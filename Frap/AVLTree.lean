inductive Tree (α : Type u) where -- Binary tree
  | empty : Tree α
  | tree (l : Tree α) (k : Nat) (v : α) (r : Tree α) : Tree α

namespace Tree

def ex_tree : Tree String :=
  tree (tree empty 2 "two" empty) 4 "four" (tree empty 5 "five"
                                                (tree empty 6 "six" empty))

def height {α : Type u} (t : Tree α) : Nat :=
  match t with
  | empty => 0
  | tree l _ _ r => 1 + max (height l) (height r)

example : height ex_tree = 3 := by
  rfl

def is_balance {α : Type u} (t : Tree α) : Bool :=
  match t with
  | empty => true
  | tree l _ _ r =>
      let hl := height l;
      let hr := height r;
      if hr <= hl
      then hl <= hr + 1
      else hr <= hl + 1

example : is_balance ex_tree := by
  rfl

def is_balance' {α : Type u} (t : Tree α) : Prop :=
  match t with
  | empty => True
  | tree l _ _ r =>
    (height l ≤ height r + 1) -- hl ≤ hr + 1
    ∨
    (height r ≤ height l + 1) -- hr ≤ hl + 1

example : is_balance' ex_tree := by
  unfold is_balance'
  unfold ex_tree
  split
  . simp
  . simp [*] at *
    rename_i h; obtain ⟨l,_,_,r⟩ := h
    rw [← l, ← r]
    simp [height]

def balance_all {α : Type u} (t : Tree α) : Bool := -- do like ForallTree
  match t with
  | empty => true
  | tree l _ _ r => balance_all l ∧ balance_all r ∧ is_balance t

example : balance_all ex_tree := by
  rfl

def balance_all' {α : Type u} (t : Tree α) : Prop :=
  match t with
  | empty => True
  | tree l _ _ r => balance_all' l ∧ balance_all' r ∧ is_balance' t

example : balance_all' ex_tree := by
  constructor <;> constructor <;> constructor
  <;> constructor <;> constructor <;> constructor
  <;> constructor <;> constructor; constructor

def is_balance'' {α : Type u} (l : Tree α) (r : Tree α) : Prop :=
  (height l ≤ height r + 1) -- hl ≤ hr + 1
  ∨
  (height r ≤ height l + 1) -- hr ≤ hl + 1

inductive ForallTree' {α : Type u} (p : Tree α → Tree α → Prop) : Tree α → Prop where
  | empty : ForallTree' p empty
  | tree : ∀ l k v r,
      p l r → ForallTree' p l → ForallTree' p r
      → ForallTree' p (tree l k v r)

inductive balance_all'' {α : Type u} : Tree α → Prop where
  | empty : balance_all'' empty
  | tree : ∀ l k v r,
    ForallTree' is_balance'' l
    → ForallTree' is_balance'' r
    → balance_all'' (tree l k v r)

inductive ForallTree {α : Type u} (p : Nat → α → Prop) : Tree α → Prop where
  | empty : ForallTree p empty
  | tree : ∀ l k v r,
      p k v → ForallTree p l → ForallTree p r
      → ForallTree p (tree l k v r)

inductive BST {α : Type u} : Tree α → Prop where
  | empty : BST empty
  | tree : ∀ l k v r,
      ForallTree (fun x _ => x < k) l
      → ForallTree (fun x _ => x > k) r
      → BST l
      → BST r
      → BST (tree l k v r)

example : BST ex_tree := by
  constructor <;> constructor <;> constructor <;> constructor <;> simp

def AVLTree {α : Type u} (t : Tree α) : Prop :=
  BST t ∧ balance_all' t

example : AVLTree ex_tree := by
  constructor
  . constructor <;> constructor <;> constructor <;> constructor <;> simp
  . constructor <;> constructor <;> constructor
    <;> constructor <;> constructor <;> constructor
    <;> constructor <;> constructor; constructor

/-
  Single rotation from left in RR case

            z                             y
           / \                           / \
          a   y     left rotate(z)      z   c
             / \       ====>           / \
            b   c                     a   b
-/
def single_left_rotate {α : Type u} (t : Tree α) : Tree α :=
  match t with
  | empty => empty
  | tree a z vz (tree b y vy c)
      => tree (tree a z vz b) y vy c
  | _ => t

/-
  Single rotation from right in LL case

            z                             y
           / \                           / \
          y   c     right rotate(z)     a   z
         / \            ====>              / \
        a   b                             b   c
-/
def single_right_rotate {α : Type u} (t : Tree α) : Tree α :=
  match t with
  | empty => empty
  | tree (tree a y vy b) z vz c
      => tree a y vy (tree b z vz c)
  | _ => t

/-
  Double rotation from left in LR case

        z                            z                              x
       / \                          / \                           /   \
      y   d     left rotate(y)     x   d     right rotate(z)     y     z
     / \           ====>          / \            ====>          / \   / \
    a   x                        y   c                         a   b c   d
       / \                      / \
      b   c                    a   b
-/
def double_rotate_left {α : Type u} (t : Tree α) : Tree α :=
  match t with
  | empty => empty
  | tree (tree a y vy (tree b x vx c)) z vz d
      => tree (tree a y vy b) x vx (tree c z vz d)
  | _ => t

/-
  Double rotation from right in RL case

        z                             z                             x
       / \                           / \                          /   \
      a   y     right rotate(y)     a   x     left rotate(z)     z     y
         / \        ====>              / \       ====>          / \   / \
        x   d                         b   y                    a   b c   d
       / \                               / \
      b   c                             c   d
-/
def double_rotate_right {α : Type u} (t : Tree α) : Tree α :=
  match t with
  | empty => empty
  | tree a z vz (tree (tree b x vx c) y vy d)
      => tree (tree a z vz b) x vx (tree c y vy d)
  | _ => t

theorem ForallTree_lt_trans {α : Type u} (a : Nat) (b : Nat) (t : Tree α)
    : a < b → ForallTree (fun x _ ↦ b < x) t → ForallTree (fun x _ ↦ a < x) t := by
  intro hab hbt
  induction hbt with
  | empty => constructor
  | tree l k v r hbk _ _ ihla ihra =>
    apply ForallTree.tree
    . apply Nat.lt_trans
      apply hab
      exact hbk
    . assumption
    . assumption

theorem SRL_BST {α : Type u} (t : Tree α)
    : BST t → BST (single_left_rotate t) := by
  sorry

theorem SRR_BST {α : Type u} (t : Tree α)
    : BST t → BST (single_right_rotate t) := by
  intro bst
  induction bst with
  | empty => apply BST.empty
  | tree l' k' v' r' ihl ihr bstL bstR ihL ihR =>
    unfold single_right_rotate
    split
    . apply BST.empty
    . simp [*] at *
      rename_i h; obtain ⟨hl', hk', _, hr'⟩ := h
      simp [*] at *
      apply BST.tree
      . cases bstL; assumption -- subtree a < y
      . apply ForallTree.tree -- subtree z > y
        . cases ihl; assumption
        . cases bstL; assumption -- subtree b > y
        . cases ihl; -- subtree c > y
          rename_i hyz _; simp
          apply ForallTree_lt_trans
          . apply hyz
          . assumption
      . cases bstL; assumption
      . cases bstL; cases ihl; apply BST.tree
        . assumption -- subtree b < z
        . apply ihr -- subtree c > z
        . assumption
        . apply bstR
    . apply BST.tree <;> assumption -- cases dont right rotate

theorem DRL_BST {α : Type u} (t : Tree α)
    : BST t → BST (double_rotate_left t) := by
  sorry

theorem DRR_BST {α : Type u} (t : Tree α)
    : BST t → BST (double_rotate_right t) := by
  sorry

def lookup {α : Type u} (d : α) (x : Nat) (t : Tree α) : α :=
  match t with
  | empty => d
  | tree l k v r =>
      if x < k then lookup d x l
      else if x > k then lookup d x r
      else v

def left_heavy {α : Type u} (t : Tree α) : Bool :=
  match t with
  | empty => false
  | tree l _ _ r => height l > height r + 1

def right_heavy {α : Type u} (t : Tree α) : Bool :=
  match t with
  | empty => false
  | tree l _ _ r => height r > height l + 1

def is_LR_case {α : Type u} (t : Tree α) : Bool :=
  match t with
  | tree (tree ll _ _ lr) _ _ _ => height ll < height lr
  | _ => false

def is_RL_case {α : Type u} (t : Tree α) : Bool :=
  match t with
  | tree _ _ _ (tree rl _ _ rr) => height rr < height rl
  | _ => false

def insert {α : Type u} (x : Nat) (v : α) (t : Tree α) : Tree α := -- make rebalance function
  match t with
  | empty => tree empty x v empty
  | tree l k v' r =>
      if x < k then
        let t' := (tree (insert x v l) k v' r);
        if left_heavy t'
        then
          if is_LR_case t'
          then double_rotate_left t'  -- LR case
          else single_right_rotate t'  -- LL case
        else t'  -- current node is balanced
      else if x > k then
        let t' := (tree l k v' (insert x v r));
        if right_heavy t'
        then
          if is_RL_case t'
          then double_rotate_right t'  -- RL case
          else single_left_rotate t'  -- RR case
        else t'  -- current node is balanced
      else tree l x v r  -- update value

theorem avl_insert_of_avl {α : Type u} (k : Nat) (v : α) (t : Tree α)
    : AVLTree t → AVLTree (insert k v t) := by
  sorry
