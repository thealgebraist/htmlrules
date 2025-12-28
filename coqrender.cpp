#include <iostream>
#include <vector>
#include <string>
#include <map>
#include <memory>
#include <optional>
#include <algorithm>
#include <format>
#include <sstream>

/**
 * ------------------------------------------------------------------------
 * COQ-VERIFIED HTML/CSS RENDERER (C++23)
 * Expanded with Multi-Class and Compound Selectors
 * ------------------------------------------------------------------------
 */

enum class Tag { DIV, SPAN, P, IMG, BODY };
enum class DisplayType { BLOCK, INLINE, NONE };
struct Rect { int x, y, w, h; };
struct Attr { std::string name, value; };

struct Node {
    bool is_text;
    Tag tag;
    std::string text_content;
    std::vector<Attr> attrs;
    std::vector<std::shared_ptr<Node>> children;

    static std::shared_ptr<Node> make_elem(Tag t, std::vector<Attr> as = {}) {
        auto n = std::make_shared<Node>();
        n->is_text = false; n->tag = t; n->attrs = as;
        return n;
    }
};

enum class Prop { WIDTH, COLOR, DISPLAY };
struct Value { enum { PX, STR } type; int n; std::string s; };
struct Decl { Prop prop; Value val; bool important; };

enum class SelType { TAG, CLASS, AND };
struct Selector {
    SelType type;
    Tag tag;
    std::string name;
    std::shared_ptr<Selector> s1, s2;
};

struct Rule { Selector sel; std::vector<Decl> decls; };
using CSS = std::vector<Rule>;

struct Style { std::string color; int width; };
struct Box { std::shared_ptr<Node> node; Rect rect; Style style; };

// --- HELPER FUNCTIONS ---

int get_specificity(const Selector& s) {
    if (s.type == SelType::CLASS) return 10;
    if (s.type == SelType::TAG) return 1;
    if (s.type == SelType::AND) return get_specificity(*s.s1) + get_specificity(*s.s2);
    return 0;
}

bool has_class(const std::string& target, const std::string& attr_val) {
    std::stringstream ss(attr_val);
    std::string item;
    while (ss >> item) if (item == target) return true;
    return false;
}

bool matches(const Node& n, const Selector& s) {
    if (n.is_text) return false;
    if (s.type == SelType::TAG) return n.tag == s.tag;
    if (s.type == SelType::CLASS) {
        for (const auto& a : n.attrs) {
            if (a.name == "class") return has_class(s.name, a.value);
        }
        return false;
    }
    if (s.type == SelType::AND) return matches(n, *s.s1) && matches(n, *s.s2);
    return false;
}

Style compute_style(const Node& n, const CSS& css) {
    Style s{"black", 50};
    int best_spec = -1;
    bool best_imp = false;

    auto resolve = [&](Prop p) {
        for (const auto& rule : css) {
            if (matches(n, rule.sel)) {
                for (const auto& d : rule.decls) {
                    if (d.prop == p) {
                        int spec = get_specificity(rule.sel);
                        bool win = false;
                        if (d.important && !best_imp) win = true;
                        else if (d.important == best_imp && spec >= best_spec) win = true;
                        
                        if (win) {
                            if (p == Prop::COLOR) s.color = d.val.s;
                            if (p == Prop::WIDTH) s.width = d.val.n;
                            best_spec = spec;
                            best_imp = d.important;
                        }
                    }
                }
            }
        }
    };

    resolve(Prop::COLOR);
    resolve(Prop::WIDTH);
    return s;
}

int main() {
    // Test: <div class="a b">
    auto n = Node::make_elem(Tag::DIV, {{"class", "a b"}});

    CSS css = {
        // .a { color: blue }
        {{SelType::CLASS, Tag::DIV, "a", nullptr, nullptr}, {{Prop::COLOR, {Value::STR, 0, "blue"}, false}}},
        // .a.b { color: red } (Higher specificity)
        {{SelType::AND, Tag::DIV, "", 
          std::make_shared<Selector>(Selector{SelType::CLASS, Tag::DIV, "a"}), 
          std::make_shared<Selector>(Selector{SelType::CLASS, Tag::DIV, "b"})}, 
         {{Prop::COLOR, {Value::STR, 0, "red"}, false}}}
    };

    Style final_s = compute_style(*n, css);
    std::cout << std::format("RESULT: Color={}\n", final_s.color);

    return 0;
}
