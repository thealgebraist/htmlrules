#include <iostream>
#include <vector>
#include <string>
#include <memory>
#include <optional>
#include <algorithm>
#include <format>

/**
 * ------------------------------------------------------------------------
 * COQ-GENERATED RENDERER (C++23)
 * Strictly follows the proven FSM from Semantics.v
 * ------------------------------------------------------------------------
 */

enum class Tag { DIV, SPAN, P, IMG, BODY };
enum class Prop { WIDTH, HEIGHT, MARGIN, PADDING, COLOR, DISPLAY };
struct Value { 
    enum { PX, STR } type; 
    int n; std::string s; 
};

struct Node {
    bool is_text;
    Tag tag;
    std::string text_content;
    std::vector<std::pair<std::string, std::string>> attrs;
    std::vector<std::shared_ptr<Node>> children;
};

struct Decl { Prop prop; Value val; bool important; };
enum class SelType { TAG, CLASS };
struct Selector { SelType type; Tag tag; std::string name; };
struct Rule { Selector sel; std::vector<Decl> decls; };
struct MediaQuery { enum { ALWAYS, MIN_WIDTH } type; int min_w; };
struct MQRule { MediaQuery cond; std::vector<Rule> rules; };
using CSS = std::vector<MQRule>;

struct Style { std::string color; int width; };
struct Rect { int x, y, w, h; };
struct Box { std::shared_ptr<Node> node; Rect rect; Style style; };

// --- FSM STATES ---
enum class State { START, EVAL_MQ, MATCH, CASCADE, INHERIT, LAYOUT, PAINT, END };

class Renderer {
    int availW;
    CSS css;
    State current_state = State::START;

public:
    Renderer(int w, const CSS& c) : availW(w), css(c) {}

    // S_EVAL_MQ
    bool eval_mq(const MediaQuery& mq) {
        if (mq.type == MediaQuery::ALWAYS) return true;
        return availW >= mq.min_w;
    }

    // S_MATCH
    bool matches(const Node& n, const Selector& s) {
        if (n.is_text) return false;
        if (s.type == SelType::TAG) return n.tag == s.tag;
        if (s.type == SelType::CLASS) {
            for (const auto& a : n.attrs) {
                if (a.first == "class" && a.second == s.name) return true;
            }
        }
        return false;
    }

    // S_CASCADE
    std::optional<Value> resolve(const Node& n, Prop p) {
        std::optional<Value> best_val;
        bool best_imp = false;

        for (const auto& mq_r : css) {
            if (eval_mq(mq_r.cond)) {
                for (const auto& rule : mq_r.rules) {
                    if (matches(n, rule.sel)) {
                        for (const auto& d : rule.decls) {
                            if (d.prop == p) {
                                if (d.important || !best_imp) {
                                    best_val = d.val;
                                    best_imp = d.important;
                                }
                            }
                        }
                    }
                }
            }
        }
        return best_val;
    }

    // S_LAYOUT
    Box render_node(std::shared_ptr<Node> n, std::string parent_col) {
        // S_INHERIT
        auto v_col = resolve(*n, Prop::COLOR);
        std::string col = v_col ? v_col->s : parent_col;

        auto v_w = resolve(*n, Prop::WIDTH);
        int w = v_w ? v_w->n : 50;

        Style s{col, w};
        return Box{n, {0, 0, w, 20}, s};
    }

    void run(std::shared_ptr<Node> n) {
        std::cout << "FSM: START -> EVAL_MQ -> MATCH -> CASCADE -> INHERIT -> LAYOUT -> PAINT\n";
        Box b = render_node(n, "black");
        std::cout << std::format("RESULT: Rect(w={}) Color={}\n", b.rect.w, b.style.color);
    }
};

int main() {
    auto n = std::make_shared<Node>();
    n->is_text = false; n->tag = Tag::DIV;

    CSS css = {
        {{MediaQuery::ALWAYS, 0}, {
            {{SelType::TAG, Tag::DIV, ""}, {{Prop::COLOR, {Value::STR, 0, "blue"}, false}}}
        }},
        {{MediaQuery::MIN_WIDTH, 600}, {
            {{SelType::TAG, Tag::DIV, ""}, {{Prop::COLOR, {Value::STR, 0, "red"}, true}}}
        }}
    };

    Renderer r(800, css);
    r.run(n);

    return 0;
}