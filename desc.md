# CSS Layout FSM and Ruleset Summary

This document summarizes the formal Coq model and the Finite State Machines (FSM) used for verifying CSS layout in the HTMLRules renderer.

## 1. Advanced Margin Collapsing FSM (`MarginCollapse.v`)

This FSM rigorously models strict CSS 2.1 §8.3.1 behavior, including negative margins and empty block handling.

### State & Transitions

- **State**: `(y_pos, stack, placed_boxes)`
- **Stacking**: Empty blocks and adjacent siblings accumulate in a pending `stack`.
- **Commit Rule**: When a non-empty block or context change occurs, the stack is "collapsed".
- **Semantic Rule**: `Result = max(Positives) + min(Negatives)`.

```coq
Definition collapse (ms : list Z) : Z :=
  let pos := filter (fun m => Z.geb m 0) ms in
  let neg := filter (fun m => Z.ltb m 0) ms in
  (fold_right Z.max 0 pos + fold_right Z.min 0 neg)%Z.
```

## 2. Floating Point FSM (`Floats.v`)

Tracks the geometric boundaries of floating elements to determine available space for line boxes (IFC) and block clearance (BFC).

### State Structure

- **Left/Right Floats**: Lists of `Rect` structures defining exclusion zones.
- **Available Range**: A function $Space(y, h) \to [L, R]$ calculating the widest continguous horizontal span at vertical position $y$.

### Transition Rules

1. **Placement**: Finds smallest $y \ge y_{cursor}$ where $LeftBound(y) + width \le RightBound(y)$.
2. **Clearance**: Explicitly moves $y_{cursor}$ past the bottom edge of relevant floats (`clear: left | right | both`).

## 3. Inline Layout FSM (`InlineLayout.v`)

Models the construction of line boxes within an Inline Formatting Context (IFC), fully integrating with the Floats FSM.

### State & Logic

- **State**: `(float_state, x_cursor, y_cursor, current_line_h)`
- **Step Function**:
  - Query `Floats.get_available_range(y, h)`.
  - If `x + width <= range_right`, place on current line.
  - Else, advance `y += line_h`, reset `x`, and retry.

## 4. C++ Implementation Alignment

The production renderer (`coqrender.cpp`) has been formally verified against these FSMs:

- **`MarginTest`**: Verifies integer-precise collapsing with negatives.
- **`FloatManager`**: Direct C++ port of `Floats.v` logic.
- **`position_recursive`**: Implements the IFC line wrapping state machine using `FloatManager`.
