#pragma once

#include <string>
#include <string_view>
#include <vector>
#include <map>
#include <memory>
#include <algorithm>
#include <optional>
#include <iostream>
#include <cctype>

// -----------------------------------------------------------------------------
// Modern C++ HTML/CSS Parser
// Inspired by lightweight GitHub parsers (TinyHTMLParser, etc.)
// Uses C++20/23 features: string_view, optional, structured bindings.
// -----------------------------------------------------------------------------

namespace html {

    struct Node;
    using NodePtr = std::shared_ptr<Node>;

    enum class NodeType { ELEMENT, TEXT, COMMENT, DOCTYPE };

    struct Node {
        NodeType type;
        std::string tagName; // Uppercase
        std::string textContent;
        std::vector<std::pair<std::string, std::string>> attributes;
        std::vector<NodePtr> children;
        NodePtr parent;

        static NodePtr make_elem(std::string_view tag) {
            auto n = std::make_shared<Node>();
            n->type = NodeType::ELEMENT;
            n->tagName = std::string(tag);
            // toupper
            std::transform(n->tagName.begin(), n->tagName.end(), n->tagName.begin(), ::toupper);
            return n;
        }

        static NodePtr make_text(std::string_view text) {
            auto n = std::make_shared<Node>();
            n->type = NodeType::TEXT;
            n->textContent = std::string(text);
            return n;
        }
        
        std::optional<std::string> get_attr(const std::string& key) {
            for(auto& [k,v] : attributes) if(k == key) return v;
            return std::nullopt;
        }
    };

    class Parser {
        std::string_view src;
        size_t pos = 0;

        void skip_whitespace() {
            while (pos < src.size() && std::isspace(src[pos])) pos++;
        }

        char peek() { return (pos < src.size()) ? src[pos] : 0; }
        
        bool match(std::string_view s) {
            if (src.substr(pos).starts_with(s)) {
                pos += s.size();
                return true;
            }
            return false;
        }
        
        std::string parse_ident() {
            size_t start = pos;
            while (pos < src.size() && (std::isalnum(src[pos]) || src[pos] == '-' || src[pos] == '_' || src[pos] == ':')) pos++;
            return std::string(src.substr(start, pos - start));
        }

    public:
        Parser(std::string_view s) : src(s) {}

        NodePtr parse() {
            auto root = Node::make_elem("BODY"); // Default container
            std::vector<NodePtr> stack = { root };

            while (pos < src.size()) {
                size_t lt = src.find('<', pos);
                if (lt == std::string_view::npos) break;

                // Capture Text
                if (lt > pos) {
                    std::string_view text = src.substr(pos, lt - pos);
                    // Trim
                    size_t first = text.find_first_not_of(" \n\r\t");
                    if (first != std::string_view::npos) {
                        size_t last = text.find_last_not_of(" \n\r\t");
                        text = text.substr(first, last - first + 1);
                        stack.back()->children.push_back(Node::make_text(text));
                    }
                }
                pos = lt;

                // Tag handling
                if (match("<!--")) {
                    size_t end = src.find("-->", pos);
                    if (end == std::string_view::npos) pos = src.size();
                    else pos = end + 3;
                    continue;
                }
                if (match("<!")) { // DOCTYPE etc
                    size_t end = src.find('>', pos);
                    if (end != std::string_view::npos) pos = end + 1;
                    continue;
                }
                if (match("</")) { // Close tag
                    size_t gt = src.find('>', pos);
                    if (gt != std::string_view::npos) {
                        // std::string_view tag = src.substr(pos, gt - pos); 
                        if (stack.size() > 1) stack.pop_back(); // Primitive close
                        pos = gt + 1;
                    }
                    continue;
                }

                if (match("<")) { // Open tag
                    size_t name_start = pos;
                    while(pos < src.size() && !std::isspace(src[pos]) && src[pos] != '>' && src[pos] != '/') pos++;
                    std::string tagName = std::string(src.substr(name_start, pos - name_start));
                    
                    auto elem = Node::make_elem(tagName);
                    
                    // Attrs
                    while (pos < src.size()) {
                        skip_whitespace();
                        if (peek() == '>' || peek() == '/') break;
                        
                        size_t key_start = pos;
                        while(pos < src.size() && !std::isspace(src[pos]) && src[pos] != '=' && src[pos] != '>' && src[pos] != '/') pos++;
                        std::string key = std::string(src.substr(key_start, pos - key_start));
                        std::string val = "";
                        
                        skip_whitespace();
                        if (match("=")) {
                            skip_whitespace();
                            char quote = peek();
                            if (quote == '"' || quote == '\'') {
                                pos++;
                                size_t val_start = pos;
                                while(pos < src.size() && src[pos] != quote) pos++;
                                val = std::string(src.substr(val_start, pos - val_start));
                                if(pos < src.size()) pos++; // skip quote
                            } else {
                                size_t val_start = pos;
                                while(pos < src.size() && !std::isspace(src[pos]) && src[pos] != '>') pos++;
                                val = std::string(src.substr(val_start, pos - val_start));
                            }
                        }
                        elem->attributes.push_back({key, val});
                    }
                    
                    stack.back()->children.push_back(elem);
                    
                    bool self_closing = match("/>");
                    if (!self_closing) match(">");
                    
                    // Void Handling
                    std::string t = elem->tagName;
                    bool is_void = (t=="IMG"||t=="BR"||t=="META"||t=="LINK"||t=="HR"||t=="INPUT"||t=="AREA"||t=="BASE"||t=="COL"||t=="EMBED"||t=="PARAM"||t=="SOURCE"||t=="TRACK"||t=="WBR"||t=="PATH"||t=="CIRCLE"||t=="RECT"||t=="LINE"||t=="POLYLINE"||t=="POLYGON");
                    
                    if (!self_closing && !is_void) {
                        // Special: SCRIPT/STYLE raw text
                        if (elem->tagName == "SCRIPT" || elem->tagName == "STYLE") {
                            std::string close = "</" + tagName; // Case insensitive match needed really
                            // Find close tag
                            size_t end = std::string_view::npos;
                            // Naive case insensitive search
                            std::string s_lower = std::string(src.substr(pos));
                            std::transform(s_lower.begin(), s_lower.end(), s_lower.begin(), ::toupper);
                            std::string t_upper = "</" + tagName + ">";
                            std::transform(t_upper.begin(), t_upper.end(), t_upper.begin(), ::toupper);
                            
                            // Slow but safe?
                            // Actually just scan for </
                            size_t raw_end = pos;
                            while(true) {
                                size_t next_lt = src.find("</", raw_end);
                                if(next_lt == std::string_view::npos) { raw_end = src.size(); break; }
                                // Check if it matches
                                std::string_view potential = src.substr(next_lt + 2, tagName.size());
                                if(potential.size() == tagName.size()) {
                                    bool match = true;
                                    for(size_t i=0;i<tagName.size();++i) if(toupper(potential[i]) != toupper(tagName[i])) match=false;
                                    if(match && src[next_lt+2+tagName.size()] == '>') {
                                        // Found it
                                        // Add Content
                                        elem->children.push_back(Node::make_text(src.substr(pos, next_lt - pos)));
                                        pos = next_lt + 2 + tagName.size() + 1; // skip </TAG>
                                        break;
                                    }
                                }
                                raw_end = next_lt + 1;
                            }
                        } else {
                            stack.push_back(elem);
                        }
                    }
                }
            }
            return root;
        }
    };
}

namespace css {
    struct CSSRule {
        std::string selector;
        std::map<std::string, std::string> declarations;
    };
    
    class Parser {
        std::string_view src;
        size_t pos = 0;
    public:
         Parser(std::string_view s) : src(s) {}
         
         std::vector<CSSRule> parse() {
             std::vector<CSSRule> rules;
             while(pos < src.size()) {
                 // Selector
                 size_t brace = src.find('{', pos);
                 if(brace == std::string_view::npos) break;
                 
                 CSSRule rule;
                 std::string_view sel = src.substr(pos, brace - pos);
                 // trim sel
                 size_t first = sel.find_first_not_of(" \n\r\t");
                 if(first != std::string_view::npos) rule.selector = std::string(sel.substr(first, sel.find_last_not_of(" \n\r\t") - first + 1));
                 else rule.selector = "unknown";
                 
                 pos = brace + 1;
                 
                 // Decls
                 while(pos < src.size() && src[pos] != '}') {
                     size_t colon = src.find(':', pos);
                     size_t semi = src.find(';', pos);
                     size_t close = src.find('}', pos);
                     
                     if (close < colon || close < semi) { // End of rule
                         pos = close; break;
                     }
                     if (colon == std::string_view::npos) { pos=close; break; }
                     
                     std::string key = std::string(src.substr(pos, colon - pos));
                     // trim key
                     
                     size_t end_val = (semi != std::string_view::npos && semi < close) ? semi : close;
                     std::string val = std::string(src.substr(colon + 1, end_val - (colon + 1)));
                     
                     // clean key/val
                     auto trim = [](std::string& s) {
                         s.erase(0, s.find_first_not_of(" \n\r\t"));
                         s.erase(s.find_last_not_of(" \n\r\t")+1);
                     };
                     trim(key); trim(val);
                     rule.declarations[key] = val;
                     
                     pos = (semi != std::string_view::npos && semi < close) ? semi + 1 : close;
                 }
                 if(pos < src.size() && src[pos] == '}') pos++;
                 rules.push_back(rule);
             }
             return rules;
         }
         
         static std::map<std::string, std::string> parse_inline(std::string_view style) {
             Parser p(style); // Reuse logic? Inline has no selector/braces.
             // Manual inline parse
             std::map<std::string, std::string> decls;
             size_t i = 0;
             while(i < style.size()) {
                 size_t colon = style.find(':', i);
                 if(colon == std::string_view::npos) break;
                 size_t semi = style.find(';', colon);
                 if(semi == std::string_view::npos) semi = style.size();
                 
                 std::string k = std::string(style.substr(i, colon - i));
                 std::string v = std::string(style.substr(colon+1, semi - (colon+1)));
                  auto trim = [](std::string& s) {
                     if(s.empty()) return;
                     auto f = s.find_first_not_of(" \n\r\t"); if(f==std::string::npos) { s=""; return;}
                     s.erase(0, f); s.erase(s.find_last_not_of(" \n\r\t")+1);
                 };
                 trim(k); trim(v);
                 decls[k] = v;
                 i = semi + 1;
             }
             return decls;
         }
    };
}
