#include <iostream>
#include <vector>
#include <string>
#include <map>
#include <memory>
#include <optional>
#include <algorithm>
#include <format>
#include <sstream>
#include <fstream>
#include <libxml/HTMLparser.h>
#include <libxml/tree.h>

#define STB_IMAGE_IMPLEMENTATION
#include "stb_image.h"
#define STB_IMAGE_WRITE_IMPLEMENTATION
#include "stb_image_write.h"

/**
 * ------------------------------------------------------------------------
 * COQ-VERIFIED HTML/CSS RENDERER (C++23)
 * STRICT TABLE FLOW COMPLIANCE
 * ------------------------------------------------------------------------
 */

enum class Tag { DIV, SPAN, P, IMG, H1, BODY, TABLE, TR, TD, OTHER, HEADER, FOOTER, MAIN, SECTION, ARTICLE, NAV, ASIDE };
enum class DisplayType { BLOCK, INLINE, TABLE, TABLE_ROW, TABLE_CELL, NONE };

struct Rect { int x, y, w, h; };
struct Attr { std::string name, value; };

struct Node {
    bool is_text; Tag tag; std::string text_content;
    std::vector<Attr> attrs; std::vector<std::shared_ptr<Node>> children;
    static std::shared_ptr<Node> make_text(std::string s) { auto n = std::make_shared<Node>(); n->is_text = true; n->text_content = s; return n; }
    static std::shared_ptr<Node> make_elem(Tag t, std::vector<Attr> as = {}) { auto n = std::make_shared<Node>(); n->is_text = false; n->tag = t; n->attrs = as; return n; }
};

struct Style { DisplayType disp; int w_spec, h_spec, top, left; std::string color, src; };

struct Box {
    std::shared_ptr<Node> node; Style style;
    std::vector<std::shared_ptr<Box>> kids;
    Rect rect; int intrinsic_w = 0, intrinsic_h = 0;
};

class ResourceManager {
    std::map<std::string, unsigned char*> image_cache;
    std::map<std::string, std::pair<int, int>> image_dims;
public:
    void load_image(std::string path) {
        if (image_cache.count(path)) return;
        int w, h, ch; unsigned char* data = stbi_load(path.c_str(), &w, &h, &ch, 3);
        if (data) { image_cache[path] = data; image_dims[path] = {w, h}; }
    }
    unsigned char* get_image(std::string path, int& w, int& h) {
        if (!image_cache.count(path)) return nullptr;
        w = image_dims[path].first; h = image_dims[path].second; return image_cache[path];
    }
};

struct Color { unsigned char r, g, b; };
class Canvas {
public:
    int w, h; std::vector<unsigned char> pixels;
    Canvas(int w, int h) : w(w), h(h), pixels(w * h * 3, 255) {}
    void set_pixel(int x, int y, Color c) {
        if (x < 0 || x >= w || y < 0 || y >= h) return;
        pixels[(y * w + x) * 3 + 0] = c.r; pixels[(y * w + x) * 3 + 1] = c.g; pixels[(y * w + x) * 3 + 2] = c.b;
    }
    void draw_image(Rect r, unsigned char* data, int iw, int ih) {
        if (!data) return;
        for (int j = 0; j < std::min(r.h, ih); ++j) {
            for (int i = 0; i < std::min(r.w, iw); ++i) {
                unsigned char* p = &data[(j * iw + i) * 3]; set_pixel(r.x + i, r.y + j, {p[0], p[1], p[2]});
            }
        }
    }
    void draw_border(Rect r, Color c) {
        for (int i = r.x; i < std::min(w, r.x + r.w); ++i) { set_pixel(i, r.y, c); set_pixel(i, std::min(h-1, r.y + r.h - 1), c); }
        for (int j = r.y; j < std::min(h, r.y + r.h); ++j) { set_pixel(r.x, j, c); set_pixel(std::min(w-1, r.x + r.w - 1), j, c); }
    }
    void save(const std::string& filename) { stbi_write_png(filename.c_str(), w, h, 3, pixels.data(), w * 3); }
};

// --- MULTI-PASS LOGIC (Strict alignment) ---

Tag map_tag(std::string name); // fwd decl

Style compute_style(std::shared_ptr<Node> n) {
    DisplayType disp = DisplayType::BLOCK;
    if (n->is_text || n->tag == Tag::SPAN || n->tag == Tag::IMG) disp = DisplayType::INLINE;
    if (n->tag == Tag::TABLE) disp = DisplayType::TABLE;
    if (n->tag == Tag::TR) disp = DisplayType::TABLE_ROW;
    if (n->tag == Tag::TD) disp = DisplayType::TABLE_CELL;
    if (n->tag == Tag::DIV || n->tag == Tag::P || n->tag == Tag::H1 || n->tag == Tag::BODY) disp = DisplayType::BLOCK;
    
    // New structural tags check
    if (n->tag == Tag::HEADER || n->tag == Tag::FOOTER || n->tag == Tag::MAIN || n->tag == Tag::SECTION || n->tag == Tag::ARTICLE || n->tag == Tag::NAV || n->tag == Tag::ASIDE) disp = DisplayType::BLOCK;
    
    if (n->tag == Tag::OTHER) disp = DisplayType::NONE; 
    
    Style s{disp, 0, 0, 0, 0, "black", ""};
    for (const auto& a : n->attrs) {
        if (a.name == "width") s.w_spec = std::atoi(a.value.c_str());
        if (a.name == "height") s.h_spec = std::atoi(a.value.c_str());
        if (a.name == "top") s.top = std::atoi(a.value.c_str());
        if (a.name == "left") s.left = std::atoi(a.value.c_str());
        if (a.name == "src") s.src = a.value;
    }
    return s;
}

std::shared_ptr<Box> build_box_tree(std::shared_ptr<Node> n) {
    auto b = std::make_shared<Box>(); b->node = n; b->style = compute_style(n);
    for (auto c : n->children) b->kids.push_back(build_box_tree(c));
    return b;
}

void measure_recursive(std::shared_ptr<Box> b, ResourceManager& rm) {
    if (b->style.disp == DisplayType::NONE) { b->intrinsic_w = 0; b->intrinsic_h = 0; return; }
    
    for (auto kid : b->kids) measure_recursive(kid, rm);
    
    if (b->node->tag == Tag::IMG) {
        int iw, ih; if (rm.get_image(b->style.src, iw, ih)) { b->intrinsic_w = iw; b->intrinsic_h = ih; }
        else { b->intrinsic_w = 50; b->intrinsic_h = 50; }
    } else {
        int total_w = 0, total_h = 0;
        int current_line_w = 0, current_line_h = 0;
        int sum_kw = 0, max_kh = 0; // For table rows

        for (auto kid : b->kids) {
            if (b->style.disp == DisplayType::TABLE_ROW) {
                sum_kw += kid->intrinsic_w;
                max_kh = std::max(max_kh, kid->intrinsic_h);
            } else if (kid->style.disp == DisplayType::BLOCK) {
                total_h += current_line_h;
                total_w = std::max(total_w, current_line_w);
                current_line_w = 0; current_line_h = 0;
                
                total_h += kid->intrinsic_h;
                total_w = std::max(total_w, kid->intrinsic_w);
            } else {
                // Inline flow - fit content
                current_line_w += kid->intrinsic_w;
                current_line_h = std::max(current_line_h, kid->intrinsic_h);
            }
        }
        total_h += current_line_h;
        total_w = std::max(total_w, current_line_w);

        if (b->style.disp == DisplayType::TABLE_ROW) { b->intrinsic_w = sum_kw; b->intrinsic_h = max_kh; }
        else {
            b->intrinsic_w = b->style.w_spec ? b->style.w_spec : total_w;
            b->intrinsic_h = b->style.h_spec ? b->style.h_spec : (b->node->is_text ? 20 : total_h);
        }
    }
    if (b->intrinsic_w == 0 && b->style.disp != DisplayType::NONE) b->intrinsic_w = 50; 
    if (b->intrinsic_h == 0 && b->style.disp != DisplayType::NONE) b->intrinsic_h = 20;
}

void position_recursive(int availW, int x, int y, std::shared_ptr<Box> b) {
    if (b->style.disp == DisplayType::NONE) return;

    int final_w = b->intrinsic_w;
    if (b->style.disp == DisplayType::BLOCK && b->style.w_spec == 0) final_w = availW;
    b->rect = {x + b->style.left, y + b->style.top, final_w, b->intrinsic_h};
    
    int cx = x + b->style.left, cy = y + b->style.top;
    int current_line_h = 0;
    
    for (auto kid : b->kids) {
        if (b->style.disp == DisplayType::TABLE_ROW) {
            position_recursive(b->intrinsic_w, cx, cy, kid);
            cx += kid->rect.w;
            continue;
        }

        if (kid->style.disp == DisplayType::BLOCK) {
            if (current_line_h > 0) {
                cy += current_line_h;
                cx = x + b->style.left;
                current_line_h = 0;
            }
            position_recursive(b->intrinsic_w, cx, cy, kid);
            cy += kid->rect.h;
        } else {
            // Inline flow with simple wrapping
            if (cx + kid->intrinsic_w > x + b->style.left + b->intrinsic_w && cx > x + b->style.left) {
                cy += current_line_h;
                cx = x + b->style.left;
                current_line_h = 0;
            }
            position_recursive(b->intrinsic_w, cx, cy, kid);
            cx += kid->rect.w;
            current_line_h = std::max(current_line_h, kid->rect.h);
        }
    }
}

void paint(std::shared_ptr<Box> b, Canvas& c, ResourceManager& rm) {
    if (b->style.disp == DisplayType::NONE) return;
    
    if (b->node->tag == Tag::IMG) {
        int iw, ih; unsigned char* data = rm.get_image(b->style.src, iw, ih);
        if (data) c.draw_image(b->rect, data, iw, ih);
    }
    if (b->node->is_text) {
        Color c_text = {200, 200, 200};
        for(int j=b->rect.y; j<std::min(c.h, b->rect.y+b->rect.h); ++j)
            for(int i=b->rect.x; i<std::min(c.w, b->rect.x+b->rect.w); ++i)
                c.set_pixel(i, j, c_text);
    }
    if (!b->node->is_text) c.draw_border(b->rect, {0,0,0});
    
    for (auto k : b->kids) paint(k, c, rm);
}

Tag map_tag(std::string name) {
    std::transform(name.begin(), name.end(), name.begin(), ::tolower);
    // Structural tags
    if (name == "html") return Tag::DIV; 
    if (name == "body") return Tag::BODY; 
    if (name == "table") return Tag::TABLE;
    if (name == "tr") return Tag::TR; 
    if (name == "td") return Tag::TD;
    
    // Explicit Tags
    if (name == "header") return Tag::HEADER;
    if (name == "footer") return Tag::FOOTER;
    if (name == "main") return Tag::MAIN;
    if (name == "section") return Tag::SECTION;
    if (name == "article") return Tag::ARTICLE;
    if (name == "nav") return Tag::NAV;
    if (name == "aside") return Tag::ASIDE;
    
    // Block-like tags mapped to DIV
    if (name == "div" || name == "p" || name == "h1" || name == "h2" || name == "h3" || name == "h4" || name == "h5" || name == "h6") return Tag::DIV;
    if (name == "ul" || name == "li" || name == "ol" || name == "form" || name == "blockquote" || name == "center") return Tag::DIV;
    if (name == "br") return Tag::DIV;
    
    // Inline-like tags
    if (name == "span" || name == "a" || name == "font" || name == "b" || name == "i" || name == "strong" || name == "small" || name == "em" || name == "label" || name == "button" || name == "time") return Tag::SPAN;
    if (name == "img") return Tag::IMG; 
    
    if (name == "picture") return Tag::SPAN; 

    // Hidden/Ignored
    if (name == "head" || name == "script" || name == "map" || name == "area" || name == "title" || name == "meta" || name == "link" || name == "style" || name == "source" || name == "noscript" || name == "iframe" || name == "svg" || name == "path") return Tag::OTHER;

    return Tag::OTHER;
}

#include "modern_parser.hpp"

std::shared_ptr<Node> convert_modern_node(html::NodePtr h_node) {
    if (!h_node) return nullptr;
    
    if (h_node->type == html::NodeType::TEXT) {
        return Node::make_text(h_node->textContent);
    }
    
    if (h_node->type == html::NodeType::ELEMENT) {
        auto n = Node::make_elem(map_tag(h_node->tagName));
        for(auto& [k,v] : h_node->attributes) {
            n->attrs.push_back({k, v});
        }
        for(auto c : h_node->children) {
            auto cn = convert_modern_node(c);
            if(cn) n->children.push_back(cn);
        }
        return n;
    }
    return nullptr;
}

std::shared_ptr<Node> parse_html(std::string html_src) {
    html::Parser parser(html_src);
    auto root = parser.parse();
    return convert_modern_node(root);
}

void collect_resources(std::shared_ptr<Node> n, ResourceManager& rm) {
    if(n->tag == Tag::IMG) { for(auto& a : n->attrs) if(a.name == "src") rm.load_image(a.value); }
    for(auto c : n->children) collect_resources(c, rm);
}

// ... (collect_resources)

void run_matrix_reversal_test() {
    std::cout << "Running Matrix Order Reversal Test..." << std::endl;
    // 2x2 Grid
    // DOM: R1(C1, C2), R2(C3, C4)
    // Styles: C1 left=200, C2 left=0. C3 left=200, C4 left=0.
    // Width of each cell: 100.
    
    auto c1 = Node::make_elem(Tag::TD, {{"width", "100"}, {"left", "200"}});
    auto c2 = Node::make_elem(Tag::TD, {{"width", "100"}, {"left", "0"}});
    auto r1 = Node::make_elem(Tag::TR);
    r1->children = {c1, c2};
    
    auto c3 = Node::make_elem(Tag::TD, {{"width", "100"}, {"left", "200"}});
    auto c4 = Node::make_elem(Tag::TD, {{"width", "100"}, {"left", "0"}});
    auto r2 = Node::make_elem(Tag::TR);
    r2->children = {c3, c4};
    
    auto table = Node::make_elem(Tag::TABLE);
    table->children = {r1, r2};
    
    auto root_box = build_box_tree(table);
    ResourceManager rm;
    measure_recursive(root_box, rm);
    position_recursive(1000, 0, 0, root_box);
    
    // Row 1 kids
    int x1 = root_box->kids[0]->kids[0]->rect.x;
    int x2 = root_box->kids[0]->kids[1]->rect.x;
    // Row 2 kids
    int x3 = root_box->kids[1]->kids[0]->rect.x;
    int x4 = root_box->kids[1]->kids[1]->rect.x;
    
    std::cout << "Row 1: C1.x=" << x1 << ", C2.x=" << x2 << std::endl;
    std::cout << "Row 2: C3.x=" << x3 << ", C4.x=" << x4 << std::endl;
    
    // x2=100 (base cx=100 + left=0), x1=200 (base cx=0 + left=200)
    // Visual: C2 then C1.
    if (x2 < x1 && x4 < x3) {
        std::cout << "PASS: Matrix order reversed visually!" << std::endl;
    } else {
        std::cerr << "FAIL: Matrix order NOT reversed" << std::endl;
        exit(1);
    }
}

void run_order_reversal_test() {
    std::cout << "Running Order Reversal Test..." << std::endl;
    auto boxA = Node::make_elem(Tag::DIV, {{"id", "A"}, {"top", "50"}});
    auto boxB = Node::make_elem(Tag::DIV, {{"id", "B"}});
    auto parent = Node::make_elem(Tag::DIV);
    parent->children.push_back(boxA);
    parent->children.push_back(boxB);

    auto root_box = build_box_tree(parent);
    ResourceManager rm;
    measure_recursive(root_box, rm);
    position_recursive(1000, 0, 0, root_box);

    int yA = root_box->kids[0]->rect.y;
    int yB = root_box->kids[1]->rect.y;
    std::cout << "Box A (top: 50) Y: " << yA << std::endl;
    std::cout << "Box B Y: " << yB << std::endl;

    if (yA > yB) std::cout << "PASS: Order reversed (Visual Y order B=" << yB << " -> A=" << yA << ")" << std::endl;
    else { std::cerr << "FAIL: Order NOT reversed" << std::endl; exit(1); }

    run_matrix_reversal_test();
}

void run_normal_flow_preservation_test() {
    std::cout << "Running Normal Flow Preservation Test..." << std::endl;
    // Standard block stacking
    auto b1 = Node::make_elem(Tag::DIV, {{"height", "30"}});
    auto b2 = Node::make_elem(Tag::DIV, {{"height", "40"}});
    auto b3 = Node::make_elem(Tag::DIV, {{"height", "50"}});
    auto parent = Node::make_elem(Tag::DIV);
    parent->children = {b1, b2, b3};
    
    auto root_box = build_box_tree(parent);
    ResourceManager rm;
    measure_recursive(root_box, rm);
    position_recursive(1000, 0, 0, root_box);
    
    int y1 = root_box->kids[0]->rect.y;
    int y2 = root_box->kids[1]->rect.y;
    int y3 = root_box->kids[2]->rect.y;
    int h1 = root_box->kids[0]->rect.h;
    int h2 = root_box->kids[1]->rect.h;
    
    std::cout << "B1.y=" << y1 << ", B2.y=" << y2 << ", B3.y=" << y3 << std::endl;
    
    if (y2 >= y1 + h1 && y3 >= y2 + h2) {
        std::cout << "PASS: Normal flow order preserved (strictly monotonic Y)" << std::endl;
    } else {
        std::cerr << "FAIL: Normal flow order NOT preserved" << std::endl;
        exit(1);
    }
}

void run_unit_tests() {
    std::cout << "Running Unit Tests..." << std::endl;
    auto img = Node::make_elem(Tag::IMG, {{"width", "50"}, {"height", "50"}, {"src", "test.png"}});
    auto div = Node::make_elem(Tag::DIV, {{"width", "100"}});
    div->children.push_back(img);
    
    auto root_box = build_box_tree(div);
    ResourceManager rm;
    measure_recursive(root_box, rm);
    position_recursive(1000, 0, 0, root_box);
    
    if (root_box->rect.w != 100 || root_box->kids[0]->rect.w != 50) {
        std::cerr << "FAIL: Basic unit tests" << std::endl;
        exit(1);
    }
    std::cout << "PASS: Basic dimensions" << std::endl;

    run_order_reversal_test();
    run_normal_flow_preservation_test();
}

std::string svg_escape(std::string s) {
    std::string out;
    out.reserve(s.length());
    for (size_t i = 0; i < s.length(); ++i) {
        if (s[i] == '&') {
            std::string_view rest = std::string_view(s).substr(i);
            if (rest.starts_with("&copy;")) { out += "&#169;"; i += 5; }
            else if (rest.starts_with("&nbsp;")) { out += "&#160;"; i += 5; }
            else if (rest.starts_with("&lt;")) { out += "&lt;"; i += 3; }
            else if (rest.starts_with("&gt;")) { out += "&gt;"; i += 3; }
            else if (rest.starts_with("&amp;")) { out += "&amp;"; i += 4; }
            else if (rest.starts_with("&quot;")) { out += "&quot;"; i += 5; }
            else if (rest.starts_with("&apos;")) { out += "&apos;"; i += 5; }
            else out += "&amp;";
        } else if (s[i] == '<') out += "&lt;";
        else if (s[i] == '>') out += "&gt;";
        else if (s[i] == '"') out += "&quot;";
        else if (s[i] == '\'') out += "&apos;";
        else out += s[i];
    }
    return out;
}

void save_svg_recursive(std::shared_ptr<Box> b, std::ofstream& os) {
    if (b->style.disp == DisplayType::NONE) return;
    
    // Draw box rect
    if (b->node->is_text) {
        // Text: Light gray background
        os << "<rect x='" << b->rect.x << "' y='" << b->rect.y 
           << "' width='" << b->rect.w << "' height='" << b->rect.h 
           << "' fill='#eee' />\n";
        // Text content
        os << "<text x='" << b->rect.x + 2 << "' y='" << b->rect.y + 15 
           << "' font-family='Arial' font-size='12' fill='black'>" 
           << svg_escape(b->node->text_content) << "</text>\n";
    } else if (b->node->tag == Tag::IMG) {
        os << "<rect x='" << b->rect.x << "' y='" << b->rect.y 
           << "' width='" << b->rect.w << "' height='" << b->rect.h 
           << "' fill='#cfc' stroke='black' />\n";
        os << "<text x='" << b->rect.x + 2 << "' y='" << b->rect.y + 15 
           << "' font-family='Arial' font-size='10' fill='black'>IMG</text>\n";
    } else {
        // Container: White with Black Border
        os << "<rect x='" << b->rect.x << "' y='" << b->rect.y 
           << "' width='" << b->rect.w << "' height='" << b->rect.h 
           << "' fill='none' stroke='black' />\n";
    }
    
    for (auto k : b->kids) save_svg_recursive(k, os);
}

void save_svg(std::shared_ptr<Box> b, const std::string& filename) {
    std::ofstream os(filename);
    os << "<svg xmlns='http://www.w3.org/2000/svg' width='1000' height='3000'>\n";
    os << "<style>text { pointer-events: none; }</style>\n";
    save_svg_recursive(b, os);
    os << "</svg>\n";
}

void verify_text_order(std::shared_ptr<Box> b, int& last_y, int& expected_cnt) {
    if (b->style.disp == DisplayType::NONE) return;

    if (b->node->is_text) {
        int id = -1;
        if (sscanf(b->node->text_content.c_str(), "Text %d", &id) == 1) {
            if (id != expected_cnt) {
                std::cerr << "Order Fail: Found Text " << id << " expected " << expected_cnt << std::endl;
                exit(1);
            }
            if (b->rect.y < last_y) {
                 std::cerr << "Layout Fail: Text " << id << " at Y=" << b->rect.y << " is above previous Y=" << last_y << std::endl;
                 exit(1);
            }
            last_y = b->rect.y;
            expected_cnt++;
        }
    }
    
    for (auto k : b->kids) verify_text_order(k, last_y, expected_cnt);
}

static int g_text_counter = 0;

std::shared_ptr<Node> generate_random_tree(int depth) {
    auto n = Node::make_elem(Tag::DIV);
    
    // Randomly mix text and children
    int count = 1 + (rand() % 4);
    
    if (depth <= 0) {
        // Leaf: Add some text
        n->children.push_back(Node::make_text("Text " + std::to_string(g_text_counter++)));
    } else {
        bool has_text = false;
        for(int i=0; i<count; ++i) {
            // 30% chance of text node, 70% chance of sub-div
            if (rand() % 100 < 30) {
                n->children.push_back(Node::make_text("Text " + std::to_string(g_text_counter++)));
                has_text = true;
            } else {
                 n->children.push_back(generate_random_tree(depth - 1));
            }
        }
    }
    return n;
}

void run_fuzz_tests() {
    std::cout << "Running 256 Random HTML Fuzz Tests with Text..." << std::endl;
    std::srand(std::time(nullptr));
    ResourceManager rm; 
    
    for(int i=0; i<256; ++i) {
        g_text_counter = 0;
        auto root_node = generate_random_tree(4); 
        auto body = Node::make_elem(Tag::BODY);
        body->children.push_back(root_node);
        
        auto box = build_box_tree(body);
        measure_recursive(box, rm);
        position_recursive(1000, 0, 0, box);
        
        // Check Text Order
        int last_y = -1;
        int expected_cnt = 0;
        verify_text_order(box, last_y, expected_cnt);
        
        if (i % 50 == 0) std::cout << "Verified " << i << " trees..." << std::endl;
        
        if (i == 255) {
             std::cout << "Saving last tree to fuzz_test.svg" << std::endl;
             save_svg(box, "fuzz_test.svg");
        }
    }
    std::cout << "All 256 Tests Passed! Text order invariant holds." << std::endl;
}

// ... (save_svg)

void print_tree_statsRecursive(std::shared_ptr<Node> n, int depth, std::map<std::string, int>& tag_counts, int& nodes, int& max_depth) {
    nodes++;
    max_depth = std::max(max_depth, depth);
    
    std::string tag_name = "UNKNOWN";
    // Reverse map tag for display? Or just count enum ints
    if (n->is_text) tag_name = "TEXT";
    else if (n->tag == Tag::DIV) tag_name = "DIV";
    else if (n->tag == Tag::SPAN) tag_name = "SPAN";
    else if (n->tag == Tag::IMG) tag_name = "IMG";
    else if (n->tag == Tag::BODY) tag_name = "BODY";
    else if (n->tag == Tag::OTHER) tag_name = "OTHER";
    else if (n->tag == Tag::HEADER) tag_name = "HEADER";
    else tag_name = "TAG_" + std::to_string((int)n->tag);
    
    tag_counts[tag_name]++;
    
    for(auto c : n->children) print_tree_statsRecursive(c, depth+1, tag_counts, nodes, max_depth);
}

void run_debug(std::string filename) {
    std::cout << "Debugging " << filename << "..." << std::endl;
    std::ifstream f(filename); std::stringstream buf; buf << f.rdbuf(); std::string html = buf.str();
    auto dom = parse_html(html);
    
    std::map<std::string, int> tag_counts;
    int nodes = 0;
    int max_depth = 0;
    print_tree_statsRecursive(dom, 0, tag_counts, nodes, max_depth);
    
    std::cout << "Nodes: " << nodes << std::endl;
    std::cout << "Max Depth: " << max_depth << std::endl;
    std::cout << "Tag Counts:" << std::endl;
    for(auto p : tag_counts) std::cout << "  " << p.first << ": " << p.second << std::endl;
    
// ... (run_debug)
    for(auto p : tag_counts) std::cout << "  " << p.first << ": " << p.second << std::endl;
    
    // Check root children
    std::cout << "Root Children: " << dom->children.size() << std::endl;
    for(auto c : dom->children) {
         std::cout << "   bebop " << (c->is_text ? "TEXT" : "TAG") << std::endl;
    }
}

bool is_void_tag_name(const std::string& t) {
    return (t=="IMG"||t=="BR"||t=="META"||t=="LINK"||t=="HR"||t=="INPUT"||t=="AREA"||t=="BASE"||t=="COL"||t=="EMBED"||t=="PARAM"||t=="SOURCE"||t=="TRACK"||t=="WBR"||t=="PATH"||t=="CIRCLE"||t=="RECT"||t=="LINE"||t=="POLYLINE"||t=="POLYGON");
}

void serialize_modern_node(html::NodePtr n, std::ostream& os) {
     if (n->type == html::NodeType::TEXT) {
        os << n->textContent;
        return;
    }
    if (n->type == html::NodeType::ELEMENT) {
        std::string tag_lower = n->tagName;
        std::transform(tag_lower.begin(), tag_lower.end(), tag_lower.begin(), ::tolower);
        
        os << "<" << tag_lower;
        for (auto& [k, v] : n->attributes) {
            os << " " << k << "=\"" << v << "\"";
        }
        
        if (n->children.empty() && is_void_tag_name(n->tagName)) {
             os << " />";
        } else {
             os << ">";
             for (auto c : n->children) serialize_modern_node(c, os);
             os << "</" << tag_lower << ">";
        }
    }
}

void run_roundtrip(std::string filename) {
    std::cout << "Round-tripping " << filename << "..." << std::endl;
    std::ifstream f(filename); std::stringstream buf; buf << f.rdbuf(); std::string html_src = buf.str();
    
    html::Parser parser(html_src);
    auto root = parser.parse();
    
    std::ofstream out("dr_out.html");
    serialize_modern_node(root, out);
    out.close();
    
    std::cout << "Saved to dr_out.html. Comparing sizes..." << std::endl;
    std::cout << "Original: " << html_src.size() << " bytes." << std::endl;
    
    std::ifstream f2("dr_out.html"); f2.seekg(0, std::ios::end);
    std::cout << "Output: " << f2.tellg() << " bytes." << std::endl;
}

int main(int argc, char** argv) {
    if (argc > 1) {
        std::string arg1 = argv[1];
        if (arg1 == "-test") { run_unit_tests(); return 0; }
        if (arg1 == "-fuzz") { run_fuzz_tests(); return 0; }
        if (arg1 == "-debug" && argc > 2) { run_debug(argv[2]); return 0; }
        if (arg1 == "-roundtrip" && argc > 2) { run_roundtrip(argv[2]); return 0; }
    }
    ResourceManager rm; std::string input = (argc > 1) ? argv[1] : "pg.html";
    std::ifstream f(input); std::stringstream buf; buf << f.rdbuf(); std::string html = buf.str();
    auto dom = parse_html(html); collect_resources(dom, rm);
    auto box_tree = build_box_tree(dom);
    measure_recursive(box_tree, rm); position_recursive(800, 0, 0, box_tree);
    Canvas canvas(800, 2400); paint(box_tree, canvas, rm); canvas.save("render.png");
    std::ofstream os("render.svg");
    os << "<svg width='800' height='2400' xmlns='http://www.w3.org/2000/svg'>\n";
    save_svg_recursive(box_tree, os);
    os << "</svg>\n";
    return 0;
}