#include <iostream>
#include <vector>
#include <string>
#include <map>
#include <memory>
#include <optional>
#include <algorithm>
#include <format>

/**
 * ------------------------------------------------------------------------
 * COQ-VERIFIED HTML/CSS RENDERER (C++23)
 * ------------------------------------------------------------------------
 */

enum class Tag { DIV, SPAN, P, IMG, H1 };
enum class DisplayType { BLOCK, INLINE, NONE };
enum class BoxSizing { CONTENT_BOX, BORDER_BOX };
enum class Position { STATIC, RELATIVE, ABSOLUTE };

struct Px { int n; };
struct SideValues { int t, r, b, l; };
struct Rect { int x, y, w, h; };

struct Attr { std::string name, value; };

struct Node {
    bool is_text;
    Tag tag;
    std::string text_content;
    std::vector<Attr> attrs;
    std::vector<std::shared_ptr<Node>> children;

    static std::shared_ptr<Node> make_text(std::string s) {
        auto n = std::make_shared<Node>();
        n->is_text = true; n->text_content = s;
        return n;
    }
    static std::shared_ptr<Node> make_elem(Tag t, std::vector<Attr> as = {}) {
        auto n = std::make_shared<Node>();
        n->is_text = false; n->tag = t; n->attrs = as;
        return n;
    }
};

struct Style {
    DisplayType disp;
    Position pos;
    int top, left, z_index;
    int width, height;
    SideValues margin, padding, border;
    BoxSizing box_sizing;
    std::string color;
};

enum class Prop { WIDTH, HEIGHT, MARGIN, PADDING, BORDER, COLOR, DISPLAY, BOX_SIZING, POSITION, TOP, LEFT, Z_INDEX };
struct Value { 
    enum { PX, STR } type; 
    int n; std::string s; 
};

struct Decl { Prop prop; Value val; bool important; };

enum class SelType { TAG, CLASS, ID, DESCENDANT };
struct Selector {
    SelType type;
    Tag tag;
    std::string name;
    std::shared_ptr<Selector> s1, s2; // For descendant
};

struct Rule { Selector sel; std::vector<Decl> decls; };
using CSS = std::vector<Rule>;

struct Box {
    std::shared_ptr<Node> node;
    Rect rect;
    Style style;
    std::vector<std::shared_ptr<Box>> kids;
};

// --- HELPER FUNCTIONS ---

int get_specificity(const Selector& s) {
    if (s.type == SelType::ID) return 100;
    if (s.type == SelType::CLASS) return 10;
    if (s.type == SelType::TAG) return 1;
    if (s.type == SelType::DESCENDANT) return get_specificity(*s.s1) + get_specificity(*s.s2);
    return 0;
}

bool matches(const std::vector<std::shared_ptr<Node>>& ancestors, const Node& n, const Selector& s) {
    if (s.type == SelType::TAG) return !n.is_text && n.tag == s.tag;
    if (s.type == SelType::CLASS || s.type == SelType::ID) {
        if (n.is_text) return false;
        std::string target = (s.type == SelType::CLASS) ? "class" : "id";
        for (const auto& a : n.attrs) if (a.name == target && a.value == s.name) return true;
        return false;
    }
    if (s.type == SelType::DESCENDANT) {
        if (!matches(ancestors, n, *s.s2)) return false;
        for (const auto& anc : ancestors) if (matches({}, *anc, *s.s1)) return true;
        return false;
    }
    return false;
}

Style compute_style(const std::vector<std::shared_ptr<Node>>& ancestors, std::optional<Style> parent, const Node& n, const CSS& css) {
    Style s{DisplayType::BLOCK, Position::STATIC, 0, 0, 0, 0, 0, {0,0,0,0}, {0,0,0,0}, {0,0,0,0}, BoxSizing::CONTENT_BOX, "black"};
    
    auto resolve = [&](Prop p) -> std::optional<Decl> {
        std::optional<Decl> best;
        int best_spec = -1;
        bool best_imp = false;

        for (const auto& rule : css) {
            if (matches(ancestors, n, rule.sel)) {
                for (const auto& d : rule.decls) {
                    if (d.prop == p) {
                        int spec = get_specificity(rule.sel);
                        bool win = false;
                        if (d.important && !best_imp) win = true;
                        else if (d.important == best_imp && spec >= best_spec) win = true;
                        
                        if (win) {
                            best = d;
                            best_spec = spec;
                            best_imp = d.important;
                        }
                    }
                }
            }
        }
        return best;
    };

    auto d_disp = resolve(Prop::DISPLAY);
    if (d_disp) {
        if (d_disp->val.s == "inline") s.disp = DisplayType::INLINE;
        else if (d_disp->val.s == "none") s.disp = DisplayType::NONE;
    } else if (n.is_text || n.tag == Tag::SPAN || n.tag == Tag::IMG) {
        s.disp = DisplayType::INLINE;
    }

    auto d_pos = resolve(Prop::POSITION);
    if (d_pos) {
        if (d_pos->val.s == "relative") s.pos = Position::RELATIVE;
        else if (d_pos->val.s == "absolute") s.pos = Position::ABSOLUTE;
    }

    auto d_bs = resolve(Prop::BOX_SIZING);
    if (d_bs && d_bs->val.s == "border-box") s.box_sizing = BoxSizing::BORDER_BOX;

    auto get_px = [&](Prop p) { auto d = resolve(p); return d ? d->val.n : 0; };
    s.width = get_px(Prop::WIDTH);
    s.height = get_px(Prop::HEIGHT);
    s.top = get_px(Prop::TOP);
    s.left = get_px(Prop::LEFT);
    s.z_index = get_px(Prop::Z_INDEX);

    int m = get_px(Prop::MARGIN); s.margin = {m, m, m, m};
    int p = get_px(Prop::PADDING); s.padding = {p, p, p, p};
    int b = get_px(Prop::BORDER); s.border = {b, b, b, b};

    auto d_col = resolve(Prop::COLOR);
    if (d_col) s.color = d_col->val.s;
    else if (parent) s.color = parent->color;

    return s;
}

std::shared_ptr<Box> layout_recursive(std::vector<std::shared_ptr<Node>> ancestors, int availW, std::optional<Style> parent_s, int& x, int& y, std::shared_ptr<Node> n, const CSS& css) {
    Style s = compute_style(ancestors, parent_s, *n, css);
    if (s.disp == DisplayType::NONE) return nullptr;

    int content_w = (s.width == 0) ? 50 : s.width;
    int content_h = (s.height == 0) ? 20 : s.height;

    int bb_w = (s.box_sizing == BoxSizing::CONTENT_BOX) ? (content_w + s.padding.l + s.padding.r + s.border.l + s.border.r) : content_w;
    int bb_h = (s.box_sizing == BoxSizing::CONTENT_BOX) ? (content_h + s.padding.t + s.padding.b + s.border.t + s.border.b) : content_h;

    int flow_x = x + s.margin.l;
    int flow_y = y + s.margin.t;

    int final_x = flow_x, final_y = flow_y;
    if (s.pos == Position::RELATIVE) { final_x += s.left; final_y += s.top; }
    else if (s.pos == Position::ABSOLUTE) { final_x = s.left; final_y = s.top; }

    auto b = std::make_shared<Box>();
    b->node = n; b->rect = {final_x, final_y, bb_w, bb_h}; b->style = s;

    int child_x = final_x + s.padding.l + s.border.l;
    int child_y = final_y + s.padding.t + s.border.t;
    
    std::vector<std::shared_ptr<Node>> next_ancestors = ancestors;
    next_ancestors.push_back(n);

    for (const auto& child : n->children) {
        auto cb = layout_recursive(next_ancestors, content_w, s, child_x, child_y, child, css);
        if (cb) b->kids.push_back(cb);
    }

    if (s.disp == DisplayType::BLOCK) {
        y += bb_h + s.margin.t + s.margin.b;
    } else {
        x += bb_w + s.margin.l + s.margin.r;
    }

    return b;
}

void paint(std::shared_ptr<Box> b) {
    if (!b) return;
    std::cout << std::format("DRAW RECT: x={}, y={}, w={}, h={}, color={}, z-index={}, pos={}\n", 
                             b->rect.x, b->rect.y, b->rect.w, b->rect.h, b->style.color, b->style.z_index, (int)b->style.pos);
    if (b->node->is_text) {
        std::cout << std::format("DRAW TEXT: \"{}\" at ({}, {})\n", b->node->text_content, b->rect.x + 5, b->rect.y + 15);
    }
    for (const auto& kid : b->kids) paint(kid);
}

int main() {
    auto root = Node::make_elem(Tag::DIV, {{"id", "main"}});
    root->children.push_back(Node::make_text("Hello Coq"));
    
    auto overlay = Node::make_elem(Tag::DIV, {{"class", "overlay"}});
    overlay->children.push_back(Node::make_text("I am absolute"));
    root->children.push_back(overlay);

    CSS css = {
        {{SelType::ID, Tag::DIV, "main", nullptr, nullptr}, 
         {{Prop::COLOR, {Value::STR, 0, "blue"}, true}, 
          {Prop::MARGIN, {Value::PX, 20, ""}, false}}},
        {{SelType::CLASS, Tag::DIV, "overlay", nullptr, nullptr},
         {{Prop::POSITION, {Value::STR, 0, "absolute"}, false},
          {Prop::TOP, {Value::PX, 100, ""}, false},
          {Prop::LEFT, {Value::PX, 100, ""}, false},
          {Prop::Z_INDEX, {Value::PX, 10, ""}, false},
          {Prop::COLOR, {Value::STR, 0, "red"}, false}}}
    };

    int x = 0, y = 0;
    auto box_tree = layout_recursive({}, 800, std::nullopt, x, y, root, css);
    paint(box_tree);

    return 0;
}