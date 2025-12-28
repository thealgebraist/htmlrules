import urllib.request
import html.parser
import sys
import re

# Agda AST Helpers
def escape_str(s):
    return s.replace('\\', '\\\\').replace('"', '\\"').replace('\n', ' ')

def parse_inline_style(style_str):
    """
    Simple regex-based parser for inline styles.
    Extracts width, height, background-color.
    Returns a dict of normalized attributes.
    """
    attrs = {}
    if not style_str:
        return attrs
    
    # Regex for key: value;
    # handles px, % (ignores them for now as our model expects numbers or handles them simply)
    # We want to extract numeric values for width/height if possible.
    
    # Width
    w_match = re.search(r'\bwidth\s*:\s*([\d\.]+)px', style_str)
    if w_match:
        attrs['width'] = w_match.group(1).split('.')[0] # Integer only
    
    # Height
    h_match = re.search(r'\bheight\s*:\s*([\d\.]+)px', style_str)
    if h_match:
        attrs['height'] = h_match.group(1).split('.')[0]

    # Background
    bg_match = re.search(r'\bbackground(-color)?\s*:\s*([^;]+)', style_str)
    if bg_match:
        attrs['background'] = bg_match.group(2).strip()
        
    return attrs

class AgdaNode:
    def to_agda(self, indent=0):
        pass

class Element(AgdaNode):
    def __init__(self, tag, attrs, children):
        self.tag = tag
        self.attrs = attrs
        self.children = children
    
    def to_agda(self, indent=0):
        sp = " " * indent
        # Format attributes
        if not self.attrs:
            attr_str = "[]"
        else:
            attr_str = "(" + " ∷ ".join(self.attrs) + " ∷ [])"
            
        # Format children
        if not self.children:
            kids_str = "[]"
        else:
            # Recursive formatting
            kids = []
            for c in self.children:
                kids.append(c.to_agda(indent + 2))
            
            # Join with newline and cons
            # We want:
            # (
            #   child1 ∷
            #   child2 ∷
            #   []
            # )
            kids_inner = (" \n" + sp + "  ∷ ").join(kids)
            kids_str = f"({kids_inner} \n{sp}  ∷ [])"
            
        return f"(elem {self.tag} {attr_str} {kids_str})"

class TextNode(AgdaNode):
    def __init__(self, text):
        self.text = text
    
    def to_agda(self, indent=0):
        return f'(mkT "{self.text}")'

class SiteParser(html.parser.HTMLParser):
    def __init__(self):
        super().__init__()
        # Stack of (Tag, Attrs, ChildrenList)
        # ChildrenList now contains AgdaNode objects
        self.root_children = []
        self.stack = []
        self.current_children = self.root_children
        self.text_buffer = []

    def flush_text(self):
        if self.text_buffer:
            txt = "".join(self.text_buffer).strip()
            if txt:
                safe_txt = escape_str(txt)
                if len(safe_txt) > 50: 
                    safe_txt = safe_txt[:47] + "..."
                self.current_children.append(TextNode(safe_txt))
            self.text_buffer = []

    def map_tag(self, tag):
        t = tag.lower()
        if t in ['h1', 'h2', 'p', 'div', 'span', 'img']:
            return t
        if t in ['table', 'tr', 'td', 'body', 'center', 'tbody', 'header', 'footer', 'nav', 'section', 'article', 'aside', 'main']:
            return 'div'
        if t in ['font', 'b', 'i', 'u', 'a', 'strong', 'em', 'small']:
            return 'span'
        return None 

    def handle_starttag(self, tag, attrs):
        self.flush_text()
        agda_tag = self.map_tag(tag)
        if agda_tag is None:
            return

        attr_dict = dict(attrs)
        agda_attrs = []
        for k in ['width', 'height', 'color', 'background', 'bgcolor']:
            val = attr_dict.get(k)
            if val:
                prop = 'background' if k == 'bgcolor' else k
                clean_val = val.replace('px', '').replace('%', '')
                if clean_val.isdigit():
                    agda_attrs.append(f'(mkAttr "{prop}" "{clean_val}")')

        style_attrs = parse_inline_style(attr_dict.get('style', ''))
        for k, v in style_attrs.items():
             agda_attrs.append(f'(mkAttr "{k}" "{v}")')

        # Push new context
        new_children = []
        self.stack.append((agda_tag, agda_attrs, self.current_children))
        self.current_children = new_children

    def handle_endtag(self, tag):
        self.flush_text()
        agda_tag = self.map_tag(tag)
        if agda_tag is None:
            return

        if not self.stack:
            return

        tag_name, attrs, parent_children = self.stack.pop()
        
        node = Element(tag_name, attrs, self.current_children)
        
        self.current_children = parent_children
        self.current_children.append(node)

    def handle_data(self, data):
        self.text_buffer.append(data)

    def get_agda_code(self):
        self.flush_text()
        while self.stack:
            tag_name, attrs, parent_children = self.stack.pop()
            node = Element(tag_name, attrs, self.current_children)
            self.current_children = parent_children
            self.current_children.append(node)

        # Create a root div wrapping everything
        root = Element('div', [], self.root_children)
        return root.to_agda(0)

def main():
    if len(sys.argv) < 4:
        print("Usage: python3 parse_site.py <url> <ModuleName> <Output.agda>")
        sys.exit(1)

    url = sys.argv[1]
    module_name = sys.argv[2]
    output_file = sys.argv[3]

    print(f"Fetching {url}...")
    headers = {'User-Agent': 'Mozilla/5.0'} # Some sites block default python UA
    req = urllib.request.Request(url, headers=headers)
    
    try:
        with urllib.request.urlopen(req) as response:
            html_content = response.read().decode('utf-8', errors='ignore')
    except Exception as e:
        print(f"Error fetching: {e}")
        # Generate dummy file to prevent pipeline failure
        with open(output_file, 'w') as f:
            f.write(f"module {module_name} where\nopen import CSS.Rendering\npgNodeFull = text \"Error\"\n")
        return

    # Clean up scripts/styles before parsing to avoid noise
    # Simple regex removal
    html_content = re.sub(r'<script.*?>.*?</script>', '', html_content, flags=re.DOTALL)
    html_content = re.sub(r'<style.*?>.*?</style>', '', html_content, flags=re.DOTALL)

    parser = SiteParser()
    parser.feed(html_content)
    
    # Helper to get the root expr
    # We need to handle the case where stack might have leftovers or multiple roots
    parser.flush_text()
    
    # Close any open tags loosely
    while parser.stack:
        tag_name, attrs, parent_children = parser.stack.pop()
        
        # Current children are objects now
        node = Element(tag_name, attrs, parser.current_children)
        
        parser.current_children = parent_children
        parser.current_children.append(node)

    # Root should now contain AgdaNode objects
    # We want to wrap them in a root div
    if not parser.root_children:
        agda_expr = "elem div [] []"
    else:
        root_div = Element('div', [], parser.root_children)
        agda_expr = root_div.to_agda(0)

    file_content = f"""module {module_name} where

open import CSS.Rendering hiding (t; rule'; d_w; d_h; d_bg; d_c; ex1; ex2; ex3; ex4; ex5; ex6; ex7; ex8; ex9; ex10; ex11; ex12; ex13; ex14; ex15; ex16)
open import Data.List hiding (span)
open import Data.String
open import Data.Nat
open import Data.Nat.Show using (show)

-- Helpers
mkT : String → Node
mkT s = text s

mkAttr : String → String → Attr
mkAttr n v = attr n v

pgNodeFull : Node
pgNodeFull = {agda_expr}
"""
    
    with open(output_file, 'w') as f:
        f.write(file_content)
    print(f"Generated {output_file}")

if __name__ == "__main__":
    main()
