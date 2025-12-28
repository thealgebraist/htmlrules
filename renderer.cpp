#include <iostream>
#include <vector>
#include <string>
#include <map>
#include <memory>
#include <expected>
#include <optional>
#include <format>
#include <algorithm>
#include <fstream>
#include <sstream>

/**
 * ------------------------------------------------------------------------
 * C++23 HTML/CSS RENDERER
 * Following the formal semantics defined in Agda.
 * ------------------------------------------------------------------------
 */

// Basic Geometry
struct Px { int n; };
struct Rect { Px x, y, w, h; };

// HTML DOM
enum class Tag { DIV, SPAN, IMG, P, H1, H2, TEXT_NODE };

struct Attr {
    std::string name;
    std::string value;
};

struct Node {
    Tag tag;
    std::string text_content;
    std::vector<Attr> attrs;
    std::vector<std::shared_ptr<Node>> children;

    static std::shared_ptr<Node> make_text(std::string s) {
        auto n = std::make_shared<Node>();
        n->tag = Tag::TEXT_NODE;
        n->text_content = s;
        return n;
    }

    static std::shared_ptr<Node> make_elem(Tag t, std::vector<Attr> as = {}) {
        auto n = std::make_shared<Node>();
        n->tag = t;
        n->attrs = as;
        return n;
    }
};

// CSS / Computed Style
enum class DisplayType { BLOCK, INLINE, NONE };

struct SideValues { Px top, right, bottom, left; };

struct Style {
    DisplayType disp;
    Px computedW;
    Px computedH;
    SideValues margin;
    SideValues padding;
    std::string bgColor;
    std::string fgColor;
    int fontSize;
};

// Box Tree
struct Box {
    std::shared_ptr<Node> node;
    Rect rect;
    Style style;
    std::vector<std::shared_ptr<Box>> kids;
};

// Draw Commands
struct DrawCmd {
    enum Type { BOX, IMAGE, TEXT } type;
    Rect rect;
    std::string payload; // Color, src, or text
};

/**
 * ------------------------------------------------------------------------
 * FSM STATE: ComputeStyle
 * ------------------------------------------------------------------------
 */
Style compute_style(std::optional<Style> parent, const Node& n) {
    Style s{DisplayType::BLOCK, {0}, {0}, {{0}, {0}, {0}, {0}}, {{0}, {0}, {0}, {0}}, "transparent", "black", 16};
    
    // Inheritance
    if (parent) {
        s.fgColor = parent->fgColor;
        s.fontSize = parent->fontSize;
    }

    // Default display types
    if (n.tag == Tag::SPAN || n.tag == Tag::TEXT_NODE || n.tag == Tag::IMG) {
        s.disp = DisplayType::INLINE;
    }

    // Extract properties from attributes (simulating CSS matching for classes)
    for (const auto& attr : n.attrs) {
        if (attr.name == "width") {
            try { s.computedW.n = std::stoi(attr.value); } catch (...) {}
        } else if (attr.name == "height") {
            try { s.computedH.n = std::stoi(attr.value); } catch (...) {}
        } else if (attr.name == "display") {
            if (attr.value == "none") s.disp = DisplayType::NONE;
            else if (attr.value == "inline") s.disp = DisplayType::INLINE;
            else s.disp = DisplayType::BLOCK;
        } else if (attr.name == "margin") {
            try { 
                int v = std::stoi(attr.value);
                s.margin = {{v}, {v}, {v}, {v}};
            } catch (...) {}
        } else if (attr.name == "padding") {
            try { 
                int v = std::stoi(attr.value);
                s.padding = {{v}, {v}, {v}, {v}};
            } catch (...) {}
        } else if (attr.name == "background") {
            s.bgColor = attr.value;
        } else if (attr.name == "color") {
            s.fgColor = attr.value;
        } else if (attr.name == "font-size") {
            try { s.fontSize = std::stoi(attr.value); } catch (...) {}
        }
    }
    return s;
}

/**
 * ------------------------------------------------------------------------
 * FSM STATE: Layout Phase (Recursive)
 * ------------------------------------------------------------------------
 */
std::shared_ptr<Box> layout_node(std::optional<Style> parent, Px x, Px y, Px availW, std::shared_ptr<Node> n);

std::pair<std::vector<std::shared_ptr<Box>>, Px> layout_children(std::optional<Style> parent, Px x, Px y, Px w, const std::vector<std::shared_ptr<Node>>& nodes) {
    /** FSM STATE: LayoutChildren */
    std::vector<std::shared_ptr<Box>> boxes;
    Px currentY = y;

    for (const auto& node : nodes) {
        auto b = layout_node(parent, x, currentY, w, node);
        boxes.push_back(b);
        /** FSM STATE: AccumulateHeight (Update Y) */
        Style s = b->style;
        currentY.n += b->rect.h.n + s.margin.top.n + s.margin.bottom.n;
    }
    return {boxes, currentY};
}

std::shared_ptr<Box> layout_node(std::optional<Style> parent, Px x, Px y, Px availW, std::shared_ptr<Node> n) {
    /** FSM STATE: ComputeStyle (with inheritance) */
    Style s = compute_style(parent, *n);
    
    Px bx = { x.n + s.margin.left.n };
    Px by = { y.n + s.margin.top.n };

    Px cx = { bx.n + s.padding.left.n };
    Px cy = { by.n + s.padding.top.n };

    /** FSM STATE: ResolveWidth */
    Px contentAvailW = (s.computedW.n > 0) ? s.computedW : 
        Px{ std::max(0, availW.n - s.margin.left.n - s.margin.right.n - s.padding.left.n - s.padding.right.n) };

    /** FSM STATE: LayoutChildren (Recursion) */
    auto [childBoxes, maxY] = layout_children(s, cx, cy, contentAvailW, n->children);

    /** FSM STATE: ResolveHeight */
    Px contentH = {0};
    if (s.computedH.n > 0) {
        contentH = s.computedH;
    } else {
        if (n->tag == Tag::TEXT_NODE) contentH.n = 20;
        else contentH.n = std::max(0, maxY.n - cy.n);
    }

    Px actualBbW = { contentAvailW.n + s.padding.left.n + s.padding.right.n };
    Px actualBbH = { contentH.n + s.padding.top.n + s.padding.bottom.n };

    /** FSM STATE: BoxConstruction */
    auto b = std::make_shared<Box>();
    b->node = n;
    b->rect = {bx, by, actualBbW, actualBbH};
    b->style = s;
    b->kids = childBoxes;
    return b;
}

/**
 * ------------------------------------------------------------------------
 * FSM STATE: Paint Phase
 * Implements optimized paint with accumulator
 * ------------------------------------------------------------------------
 */
void paint_box(std::shared_ptr<Box> b, std::vector<DrawCmd>& acc) {
    /** FSM STATE: GenerateCmds */
    if (b->style.disp == DisplayType::NONE) return;

    // Draw background/border (Using fgColor for border to show inheritance)
    acc.push_back({DrawCmd::BOX, b->rect, b->style.fgColor});

    if (b->node->tag == Tag::TEXT_NODE) {
        acc.push_back({DrawCmd::TEXT, b->rect, b->node->text_content});
    } else if (b->node->tag == Tag::IMG) {
        acc.push_back({DrawCmd::IMAGE, b->rect, "image"});
    }

    /** FSM STATE: PaintChildren */
    for (const auto& kid : b->kids) {
        paint_box(kid, acc);
    }
}

/**
 * ------------------------------------------------------------------------
 * SVG GENERATION
 * ------------------------------------------------------------------------
 */
std::string to_svg(const std::vector<DrawCmd>& cmds, int w, int h) {
    std::string svg = std::format("<svg width=\"{}\" height=\"{}\" xmlns=\"http://www.w3.org/2000/svg\">\n", w, h);
    svg += "<rect width=\"100%\" height=\"100%\" fill=\"black\" />\n";

    for (const auto& cmd : cmds) {
        if (cmd.type == DrawCmd::BOX) {
            svg += std::format("<rect x=\"{}\" y=\"{}\" width=\"{}\" height=\"{}\" style=\"fill:none;stroke:{};stroke-width:1;stroke-opacity:0.5\" />\n",
                               cmd.rect.x.n, cmd.rect.y.n, cmd.rect.w.n, cmd.rect.h.n, cmd.payload);
        } else if (cmd.type == DrawCmd::TEXT) {
            // Sanitize XML
            std::string text = cmd.payload;
            std::string safe;
            for(char c : text) {
                if(c == '<') safe += "&lt;";
                else if(c == '>') safe += "&gt;";
                else if(c == '&') safe += "&amp;";
                else if(c == '"') safe += "&quot;";
                else safe += c;
            }
            svg += std::format("<text x=\"{}\" y=\"{}\" font-family=\"monospace\" font-size=\"12\" fill=\"white\" fill-opacity=\"0.5\">{}</text>\n",
                               cmd.rect.x.n + 5, cmd.rect.y.n + 15, safe);
        }
    }
    svg += "</svg>";
    return svg;
}

/**
 * ------------------------------------------------------------------------
 * MINIMAL HTML PARSER
 * ------------------------------------------------------------------------
 */
Tag map_tag(std::string name) {
    std::transform(name.begin(), name.end(), name.begin(), ::tolower);
    if (name == "div" || name == "table" || name == "tr" || name == "td" || name == "body") return Tag::DIV;
    if (name == "span" || name == "a" || name == "b" || name == "i") return Tag::SPAN;
    if (name == "p") return Tag::P;
    if (name == "h1") return Tag::H1;
    if (name == "h2") return Tag::H2;
    if (name == "img") return Tag::IMG;
    return Tag::DIV;
}

std::shared_ptr<Node> parse_simple_html(std::string html) {
    auto root = Node::make_elem(Tag::DIV);
    std::vector<std::shared_ptr<Node>> stack = {root};

    size_t i = 0;
    while (i < html.length()) {
        if (html[i] == '<') {
            if (i + 1 < html.length() && html[i + 1] == '/') {
                // End Tag
                size_t end = html.find('>', i);
                if (stack.size() > 1) stack.pop_back();
                i = (end == std::string::npos) ? html.length() : end + 1;
            } else {
                // Start Tag
                size_t end = html.find('>', i);
                if (end == std::string::npos) break;
                std::string content = html.substr(i + 1, end - i - 1);
                
                std::stringstream ss(content);
                std::string tagName;
                ss >> tagName;

                auto n = Node::make_elem(map_tag(tagName));
                
                // Parse attrs
                std::string attrPart;
                while (ss >> attrPart) {
                    size_t eq = attrPart.find('=');
                    if (eq != std::string::npos) {
                        std::string key = attrPart.substr(0, eq);
                        std::string val = attrPart.substr(eq + 1);
                        if (!val.empty() && (val[0] == '"' || val[0] == '	')) val = val.substr(1);
                        if (!val.empty() && (val.back() == '"' || val.back() == '	')) val.pop_back();
                        n->attrs.push_back({key, val});
                    }
                }

                stack.back()->children.push_back(n);
                
                // Void tags check
                bool selfClosing = (!content.empty() && content.back() == '/');
                if (!selfClosing && tagName != "img" && tagName != "br" && tagName != "hr" && tagName != "meta" && tagName != "link") {
                    stack.push_back(n);
                }
                i = end + 1;
            }
        } else {
            // Text
            size_t next = html.find('<', i);
            std::string text = html.substr(i, (next == std::string::npos) ? next : next - i);
            // Trim
            text.erase(0, text.find_first_not_of(" 	\n\r"));
            text.erase(text.find_last_not_of(" 	\n\r") + 1);
            if (!text.empty()) {
                stack.back()->children.push_back(Node::make_text(text));
            }
            i = (next == std::string::npos) ? html.length() : next;
        }
    }
    return root;
}

int main(int argc, char** argv) {
    if (argc < 2) {
        std::cerr << "Usage: " << argv[0] << " <input.html>\n";
        return 1;
    }

    std::ifstream file(argv[1]);
    if (!file) {
        std::cerr << "Could not open file\n";
        return 1;
    }

    std::stringstream buffer;
    buffer << file.rdbuf();
    std::string html = buffer.str();

    auto dom = parse_simple_html(html);
    auto box_tree = layout_node(std::nullopt, {0}, {0}, {800}, dom);
    
    std::vector<DrawCmd> cmds;
    paint_box(box_tree, cmds);

    std::cout << to_svg(cmds, 800, 600) << std::endl;

    return 0;
}
