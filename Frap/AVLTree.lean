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

def is_balanced {α : Type u} (l : Tree α) (r : Tree α) : Prop :=
  height l ≤ height r + 1 ∨ height r ≤ height l + 1

-- inductive ForallTree' {α : Type u} (p : Tree α → Tree α → Prop) : Tree α → Prop where
--   | empty : ForallTree' p empty
--   | tree : ∀ l k v r,
--       p l r → ForallTree' p l → ForallTree' p r
--       → ForallTree' p (tree l k v r)

-- inductive balanced_all {α : Type u} : Tree α → Prop where
--   | empty : balanced_all empty
--   | tree : ∀ l k v r,
--     is_balance'' l r
--     → ForallTree' is_balance'' l
--     → ForallTree' is_balance'' r
--     → balanced_all (tree l k v r)

-- example : balanced_all ex_tree := by
--   repeat (constructor <;> repeat constructor)

inductive balanced_tree {α : Type u} : Tree α → Prop where
  | empty : balanced_tree empty
  | tree : ∀ l k v r,
    is_balanced l r
    → balanced_tree l
    → balanced_tree r
    → balanced_tree (tree l k v r)

example : balanced_tree ex_tree := by
  repeat (constructor <;> repeat constructor)

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
  repeat (constructor <;> repeat constructor)

def AVLTree {α : Type u} (t : Tree α) : Prop :=
  BST t ∧ balanced_tree t

example : AVLTree ex_tree := by
  repeat (constructor <;> repeat constructor)

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
-- def double_rotate_left {α : Type u} (t : Tree α) : Tree α :=
--   match t with
--   | empty => empty
--   | tree (tree a y vy (tree b x vx c)) z vz d
--       => tree (tree a y vy b) x vx (tree c z vz d)
--   | _ => t

def double_rotate_left {α : Type u} (t : Tree α) : Tree α :=
  match t with
  | empty => empty
  | tree (tree a y vy (tree b x vx c)) z vz d
      => single_right_rotate (tree (single_left_rotate (tree a y vy (tree b x vx c))) z vz d)
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
-- def double_rotate_right {α : Type u} (t : Tree α) : Tree α :=
--   match t with
--   | empty => empty
--   | tree a z vz (tree (tree b x vx c) y vy d)
--       => tree (tree a z vz b) x vx (tree c y vy d)
--   | _ => t

def double_rotate_right {α : Type u} (t : Tree α) : Tree α :=
  match t with
  | empty => empty
  | tree a z vz (tree (tree b x vx c) y vy d)
      => single_left_rotate (tree a z vz (single_right_rotate (tree (tree b x vx c) y vy d)))
  | _ => t

def rebalance {α : Type u} (l : Tree α) (k : Nat) (v : α) (r : Tree α) : Tree α :=
    let hl := height l;
    let hr := height r;
    if hl + 1 < hr -- Heavy right
    then
      match r with
      | empty => r -- impossible
      | tree l' _ _ r' =>
        let hrl := height l';
        let hrr := height r';
        if hrl < hrr then single_right_rotate (tree l k v r) -- RR case
        else if hrl > hrr then double_rotate_right (tree l k v r) -- RL case
        else r -- impossible
    else if hr + 1 < hl -- Heavy left
    then
      match l with
      | empty => l -- impossible
      | tree l' _ _ r' =>
        let hll := height l';
        let hlr := height r';
        if hlr < hll then single_left_rotate (tree l k v r) -- LL case
        else if hlr > hll then double_rotate_left (tree l k v r) -- LR case
        else l -- impossible
    else tree l k v r

def insert {α : Type u} (x : Nat) (v : α) (t : Tree α) : Tree α :=
  match t with
  | empty => tree empty x v empty
  | tree l k v' r =>
    if x < k then rebalance (insert x v l) k v' r
    else if x > k then rebalance l k v' (insert x v r)
    else tree l x v r  -- update value

----------------------------- proof insert preserved BST -----------------------------

theorem ForallTree_lt {α : Type u} (t : Tree α) k k'
    : k < k' → ForallTree (fun x _ ↦ x < k) t → ForallTree (fun x _ ↦ x < k') t := by
  intro hkk' hkt
  induction hkt with
  | empty => apply ForallTree.empty
  | tree l k v r hltk _ _ ihlk' ihrk' =>
    apply ForallTree.tree
    . apply Nat.lt_trans
      apply hltk
      exact hkk'
    . apply ihlk'
    . apply ihrk'

theorem ForallTree_gt {α : Type u} (t : Tree α) k k'
    : k > k' → ForallTree (fun x _ ↦ x > k) t → ForallTree (fun x _ ↦ x > k') t := by
  intro hkk' hkt
  induction hkt with
  | empty => apply ForallTree.empty
  | tree l k v r hgtk _ _ ihlk' ihrk' =>
    apply ForallTree.tree
    . apply Nat.lt_trans
      apply hkk'
      exact hgtk
    . apply ihlk'
    . apply ihrk'

theorem SRL_BST {α : Type u} (t : Tree α)
    : BST t → BST (single_left_rotate t) := by
  intro bst
  induction bst with
  | empty => apply BST.empty
  | tree l' k' v' r' ihl ihr bstL bstR ihL ihR =>
    unfold single_left_rotate
    split
    . apply BST.empty
    . simp [*] at *
      rename_i h; obtain ⟨hl', hk', _, hr'⟩ := h
      simp [*] at *
      apply BST.tree
      . apply ForallTree.tree -- subtree a < y
        . cases ihr; assumption -- z < y
        . cases ihr; apply ForallTree_lt_swap_trans <;> assumption
        . cases bstR; assumption -- subtree b < y
      . cases bstR; assumption -- subtree c > y
      . cases ihr; apply BST.tree
        . apply ihl
        . simp; rename_i btt _ _; apply btt -- subtree b < z
        . apply bstL
        . cases bstR; rename_i bt _ _ _; apply bt
      . cases bstR; rename_i ct _; apply ct -- subtree c > y
    . apply BST.tree <;> assumption -- cases don't left rotate

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
          apply ForallTree_gt
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
  intro bst
  induction bst with
  | empty => apply BST.empty
  | tree l' k' v' r' ihl ihr bstL bstR ihL ihR =>
    unfold double_rotate_left
    split
    . apply BST.empty -- empty cases
    . apply SRR_BST -- cases rotate DRL
      simp [*] at *
      rename_i h; obtain ⟨hl', hk', _, hr'⟩ := h
      simp [*] at *
      apply BST.tree
      . cases ihl
        rename_i hzx; cases hzx
        apply ForallTree.tree
        . assumption
        . apply ForallTree.tree
          . assumption
          . assumption
          . assumption
        . assumption
      . apply ihr
      . apply SRL_BST; apply bstL
      . apply bstR
    . apply BST.tree <;> assumption -- cases dont rotate

theorem DRR_BST {α : Type u} (t : Tree α)
    : BST t → BST (double_rotate_right t) := by
  intro bst
  induction bst with
  | empty => apply BST.empty
  | tree l' k' v' r' ihl ihr bstL bstR ihL ihR =>
    unfold double_rotate_right
    split
    . apply BST.empty -- empty cases
    . apply SRL_BST -- cases rotate DRR
      simp [*] at *
      rename_i h; obtain ⟨hl', hk', _, hr'⟩ := h
      simp [*] at *
      apply BST.tree
      . apply ihl
      . cases ihr
        rename_i hzx _ _; cases hzx
        apply ForallTree.tree
        . assumption
        . assumption
        . apply ForallTree.tree
          . assumption
          . assumption
          . assumption
      . apply bstL
      . apply SRR_BST; apply bstR
    . apply BST.tree <;> assumption -- cases dont rotate

theorem rebalance_BST {α : Type u} (l : Tree α) k vk (r : Tree α)
    : ForallTree (fun x _ => x < k) l
      -> ForallTree (fun x _ => x > k) r
      -> BST l
      -> BST r
      -> BST (rebalance l k vk r) := by
  intro hlk hkr hbl hbr
  unfold rebalance
  simp
  split
  . split
    . constructor
    . split
      . apply SRR_BST
        constructor <;> assumption
      . split
        . apply DRR_BST
          constructor <;> assumption
        . assumption
  . split
    . split
      . constructor
      . split
        . apply SRL_BST
          constructor <;> assumption
        . split
          . apply DRL_BST
            constructor <;> assumption
          . assumption
    . constructor <;> assumption

theorem single_left_rotateP {α : Type u} (P : Nat → α → Prop) (l : Tree α) k vk (r : Tree α)
    : ForallTree P l
      → ForallTree P r
      → P k vk
      → ForallTree P (single_left_rotate (tree l k vk r)) := by
  intro hpl hpr hpk
  unfold single_left_rotate
  split
  . constructor
  . simp [*] at *
    simp [*] at *
    cases hpr
    constructor
    . assumption
    . constructor <;> assumption
    . assumption
  . constructor <;> assumption

theorem single_right_rotateP {α : Type u} (P : Nat → α → Prop) (l : Tree α) k vk (r : Tree α)
    : ForallTree P l
      → ForallTree P r
      → P k vk
      → ForallTree P (single_right_rotate (tree l k vk r)) := by
  intro hpl hpr hpk
  unfold single_right_rotate
  split
  . constructor
  . simp [*] at *
    simp [*] at *
    cases hpl
    constructor
    . assumption
    . assumption
    . constructor <;> assumption
  . constructor <;> assumption

theorem double_left_rotateP {α : Type u} (P : Nat → α → Prop) (l : Tree α) k vk (r : Tree α)
    : ForallTree P l
      → ForallTree P r
      → P k vk
      → ForallTree P (double_rotate_left (tree l k vk r)) := by
  intro hpl hpr hpk
  unfold double_rotate_left
  split
  . constructor
  . simp [*] at *
    simp [*] at *
    cases hpl
    apply single_right_rotateP
    . apply single_left_rotateP <;> assumption
    . assumption
    . assumption
  . constructor <;> assumption

theorem double_right_rotateP {α : Type u} (P : Nat → α → Prop) (l : Tree α) k vk (r : Tree α)
    : ForallTree P l
      → ForallTree P r
      → P k vk
      → ForallTree P (double_rotate_right (tree l k vk r)) := by
  intro hpl hpr hpk
  unfold double_rotate_right
  split
  . constructor
  . simp [*] at *
    simp [*] at *
    cases hpr
    apply single_left_rotateP
    . assumption
    . apply single_right_rotateP <;> assumption
    . assumption
  . constructor <;> assumption

theorem rebalanceP {α : Type u} (P : Nat → α → Prop) (l : Tree α) k vk (r : Tree α)
    : ForallTree P l
      → ForallTree P r
      → P k vk
      → ForallTree P (rebalance l k vk r) := by
  intro hpl hpr hpk
  unfold rebalance
  simp
  split
  . split
    . constructor
    . split
      . apply single_right_rotateP <;> assumption
      . split
        . apply double_right_rotateP <;> assumption
        . assumption
  . split
    . split
      . constructor
      . split
        . apply single_left_rotateP <;> assumption
        . split
          . apply double_left_rotateP <;> assumption
          . assumption
    . constructor <;> assumption

theorem insertP {α : Type u} (P : Nat → α → Prop) (t : Tree α) k vk
    : ForallTree P t → P k vk → ForallTree P (insert k vk t) := by
  intro hpt hpk
  induction t with
  | empty => constructor <;> assumption
  | tree _ _ _ _ ihl ihr =>
    cases hpt
    unfold insert
    split
    . apply rebalanceP <;> simp [*] at *
    . split
      . apply rebalanceP <;> simp [*] at *
      . constructor <;> assumption

theorem insert_BST {α : Type u} (k : Nat) (v : α) (t : Tree α)
    : BST t → BST (insert k v t) := by
  intro bst
  induction t with
  | empty => (repeat constructor) <;> assumption
  | tree l' k' v' r' ihl ihr =>
    cases bst
    unfold insert
    simp
    split
    . apply rebalance_BST <;> simp [*] at *
      apply insertP <;> assumption
    . split
      . apply rebalance_BST <;> simp [*] at *
        apply insertP <;> assumption
      . have heq : k = k' := by
          simp at *
          apply Nat.le_antisymm
          . assumption
          . assumption
        constructor <;> simp [*] at *

----------------------------- proof insert preserved balanced_tree -----------------------------

theorem SRR_balanced_tree {α : Type u} (l l' r': Tree α) k v v'
    : height l + 1 < height (tree l' k' v' r')
      → height l' < height r'
      → balanced_tree l
      → balanced_tree (tree l' k' v' r')
      → balanced_tree (single_right_rotate (tree l k v (tree l' k' v' r'))) := by
  intro heavy_left _hLL hbl hbr
  unfold single_right_rotate
  split
  . constructor
  . simp [*] at *
    simp [*] at *
    cases hbl
    . constructor
      . simp [height, is_balanced] at *
        left
        omega
      . assumption
      . constructor
        . simp [height, is_balanced] at *
          left
          omega
        . assumption
        . assumption
  . constructor
    . unfold is_balanced
      left
      omega
    . assumption
    . assumption

theorem SRL_balanced_tree {α : Type u} (r l' r': Tree α) k v v'
    : height r + 1 < height (tree l' k' v' r')
      → height r' < height l'
      → balanced_tree (tree l' k' v' r')
      → balanced_tree r
      → balanced_tree (single_left_rotate (tree (tree l' k' v' r') k v r)) := by
  intro heavy_right _hRR hbl hbr
  unfold single_left_rotate
  split
  . constructor
  . simp [*] at *
    simp [*] at *
    cases hbr
    . constructor
      . simp [height, is_balanced] at *
        right
        omega
      . constructor
        . simp [height, is_balanced] at *
          right
          omega
        . assumption
        . assumption
      . assumption
  . constructor
    . unfold is_balanced
      right
      omega
    . assumption
    . assumption

theorem DRL_balanced_tree {α : Type u} (r l' r': Tree α) k v v'
    : height r + 1 < height (tree l' k' v' r')
      → height r' > height l'
      → balanced_tree (tree l' k' v' r')
      → balanced_tree r
      → balanced_tree (double_rotate_left (tree (tree l' k' v' r') k v r)) := by
  intro heavy_right _hRR hbl hbr
  unfold double_rotate_left
  split
  . constructor
  . simp [single_left_rotate, single_right_rotate] at *
    simp [*] at *
    cases hbl
    constructor
    . unfold is_balanced
      omega
    . rename_i h _; cases h
      constructor
      . unfold is_balanced
        omega
      . assumption
      . assumption
    . rename_i h _; cases h
      constructor
      . unfold is_balanced
        omega
      . assumption
      . assumption
  . constructor
    . unfold is_balanced
      right
      omega
    . assumption
    . assumption

theorem DRR_balanced_tree {α : Type u} (l l' r': Tree α) k v v'
    : height l + 1 < height (tree l' k' v' r')
      → height l' > height r'
      → balanced_tree l
      → balanced_tree (tree l' k' v' r')
      → balanced_tree (double_rotate_right (tree l k v (tree l' k' v' r'))) := by
  intro heavy_left _hLL hbl hbr
  unfold double_rotate_right
  split
  . constructor
  . simp [single_right_rotate, single_left_rotate] at *
    simp [*] at *
    cases hbr
    . constructor
      . unfold is_balanced
        omega
      . rename_i h _ _; cases h
        constructor
        . unfold is_balanced
          omega
        . assumption
        . assumption
      . rename_i h _ _; cases h
        constructor
        . unfold is_balanced
          omega
        . assumption
        . assumption
  . constructor
    . unfold is_balanced
      left
      omega
    . assumption
    . assumption

theorem rebalance_balanced_tree {α : Type u} (l : Tree α) k vk (r : Tree α)
    : balanced_tree l
      -> balanced_tree r
      -> balanced_tree (rebalance l k vk r) := by
  intro hbl hbr
  unfold rebalance
  simp
  split
  . split
    . constructor
    . split
      . apply SRR_balanced_tree <;> assumption
      . split
        . apply DRR_balanced_tree <;> assumption
        . assumption
  . split
    . split
      . constructor
      . split
        . apply SRL_balanced_tree <;> assumption
        . split
          . apply DRL_balanced_tree <;> assumption
          . assumption
    . constructor
      . simp at *
        unfold is_balanced
        left; assumption
      . assumption
      . assumption

theorem insert_balanced_tree {α : Type u} (k : Nat) (v : α) (t : Tree α)
    : balanced_tree t → balanced_tree (insert k v t) := by
  intro blt
  induction t with
  | empty => (repeat constructor) <;> assumption
  | tree l' k' v' r' ihl ihr =>
    cases blt
    unfold insert
    split
    . simp [*] at *
      apply rebalance_balanced_tree <;> assumption
    . split
      . simp [*] at *
        apply rebalance_balanced_tree <;> assumption
      . constructor <;> assumption

----------------------------- proof insert preserved AVL -----------------------------

theorem insert_AVL {α : Type u} (k : Nat) (v : α) (t : Tree α)
    : AVLTree t → AVLTree (insert k v t) := by
  intro avl
  cases avl
  constructor
  . apply insert_BST; assumption
  . apply insert_balanced_tree; assumption

----------------------------- delete definition -----------------------------

def findmin_node {α : Type u} (t : Tree α) : Tree α := -- assume BST
  match t with
  | empty => empty
  | tree empty k v r => tree empty k v r
  | tree l _ _ _ => findmin_node l

def delete_min {α : Type u} (t : Tree α) : Option (Nat × α × Tree α) :=
  match t with
  | empty => none
  | tree l k v r =>
    match delete_min l with
    | none => some (k, v, r)
    | some (k', v', l') => (k', v', rebalance l' k v r)

def delete {α : Type u} (x : Nat) (t : Tree α) : Tree α :=
  match t with
  | empty => empty -- not found
  | tree l k v r =>
    if x < k then rebalance (delete x l) k v r
    else if x > k then rebalance l k v (delete x r)
    else -- found delete node
      match l, r with
      | empty, empty => empty -- no children nodes
      | _, empty => l
      | empty, _ => r
      | _, tree l' k' v' r' =>
        match findmin_node l' with
        | empty => rebalance l k' v' r'
        | tree _ nextK nextV _ => rebalance l nextK nextV (delete nextK r)

def delete' {α : Type u} (x : Nat) (t : Tree α) : Tree α :=
  match t with
  | empty => empty -- not found
  | tree l k v r =>
    if x < k then rebalance (delete' x l) k v r
    else if x > k then rebalance l k v (delete' x r)
    else -- found delete node
      match l, r with
      | empty, empty => empty -- no children nodes
      | _, empty => l
      | empty, _ => r
      | _, r' =>
        match delete_min r' with
        | none => l
        | some (nextK, nextV, t) => rebalance l nextK nextV t

----------------------------- proof delete preserved BST -----------------------------

theorem delete_min_gt {α : Type u} (k k': Nat) (v': α) (t t' : Tree α)
    : ForallTree (fun x _ ↦ k < x) t
      → delete_min t = some (k', v', t')
      → k < k' := by
  intro hft hdt
  induction t generalizing k k' v' t' with
  | empty => cases hdt
  | tree l'' k'' v'' r'' ihl ihr =>
    apply ihl <;> try assumption
    . cases hft; assumption
    . simp [delete_min] at hdt
      sorry

theorem delete_min_BST {α : Type u} (k : Nat) (v : α) (t t' : Tree α)
    : BST t
      → delete_min t = some (k, v, t')
      → BST t' := by
  sorry

theorem delete_min_BST_min_node {α : Type u} (k : Nat) (v : α) (t t' : Tree α)
    : BST t
      → delete_min t = some (k, v, t')
      → ForallTree (fun x _ => x > k) t' := by
  sorry

theorem delete_minP {α : Type u} (P : Nat → α → Prop) (k : Nat) (v : α) (t t' : Tree α)
    : ForallTree P t
      → delete_min t = some (k, v, t')
      → ForallTree P t' := by
  intro hpt hdt
  induction t generalizing k v t' with
  | empty => cases hdt
  | tree l'' k'' v'' r'' ihl ihr =>
    apply ihl <;> try assumption
    . cases hpt; assumption
    . sorry
    --  rw [← hdt]
    --   simp [delete_min]
    --   split
    --   . sorry
    --   . rename_i h
    --     rw [h]
    --     congr

theorem delete_nodeP {α : Type u} (P : Nat → α → Prop) (k : Nat) (v : α) (t t' : Tree α)
    : ForallTree P t
      → delete_min t = some (k, v, t')
      → P k v := by
  sorry

theorem deleteP' {α : Type u} (P : Nat → α → Prop) (t : Tree α) k
    : ForallTree P t → ForallTree P (delete' k t) := by
  intro hpt
  induction t with
  | empty => constructor <;> assumption
  | tree l' k' v' r' ihl ihr =>
    cases hpt
    unfold delete'
    split
    . apply rebalanceP <;> simp [*] at *
    . split
      . apply rebalanceP <;> simp [*] at *
      . split
        . assumption
        . assumption
        . assumption
        . split
          . assumption
          . apply rebalanceP
            . assumption
            . apply delete_minP
              . rename_i forallr' _ _ _ _ _ _ _ _ _ _ _ _; apply forallr'
              . rename_i hdelmin; apply hdelmin
            . apply delete_nodeP
              . rename_i forallr' _ _ _ _ _ _ _ _ _ _ _ _; apply forallr'
              . rename_i hdelmin; apply hdelmin

theorem delete_BST' {α : Type u} (k : Nat) (t : Tree α)
    : BST t → BST (delete' k t) := by
  intro bst
  induction t with
  | empty => constructor
  | tree l' k' v' r' ihl ihr =>
    cases bst
    simp [*] at *
    unfold delete'
    split
    . apply rebalance_BST <;> try simp [*] at *
      apply deleteP'; assumption
    . split
      . apply rebalance_BST <;> try simp [*] at *
        apply deleteP'; assumption
      . split
        . apply BST.empty
        . assumption
        . assumption
        . split
          . assumption
          . apply rebalance_BST
            . apply ForallTree_lt
              . apply delete_min_gt <;> assumption
              . assumption
            . apply delete_min_BST_min_node
              . rename_i bstr' _ _ _ _ _ _ _ _ _ _ _ _ _; apply bstr'
              . rename_i hdelmin; apply hdelmin
            . assumption
            . apply delete_min_BST
              . rename_i bstr' _ _ _ _ _ _ _ _ _ _ _ _ _; apply bstr'
              . rename_i hdelmin; apply hdelmin

theorem findmin_node_gt {α : Type u} (t : Tree α) l k v r k'
    : BST t
      → ForallTree (fun x _ => k' < x) t
      → findmin_node t = tree l k v r
      → k' < k := by
  intro bst hl' hmin
  induction t with
  | empty => cases hmin -- contra
  | tree l' k'' v' r' ihl _ =>
    apply ihl
    . cases bst
      assumption
    . cases hl'
      assumption
    . rw [← hmin, findmin_node]
      sorry

theorem deleteP {α : Type u} (P : Nat → α → Prop) (t : Tree α) k
    : ForallTree P t → ForallTree P (delete k t) := by
  intro hpt
  induction t with
  | empty => constructor <;> assumption
  | tree _ _ _ _ ihl ihr =>
    cases hpt
    unfold delete
    split
    . apply rebalanceP <;> simp [*] at *
    . split
      . apply rebalanceP <;> simp [*] at *
      . split <;> try assumption
        . split
          . rename_i h _ _; cases h
            apply rebalanceP <;> simp [*] at *
          . apply rebalanceP
            . assumption
            . sorry
            . sorry

theorem delete_BST {α : Type u} (k : Nat) (t : Tree α)
    : BST t → BST (delete k t) := by
  intro bst
  induction t with
  | empty => constructor
  | tree l' k' v' r' ihl ihr =>
    cases bst
    simp [*] at *
    unfold delete
    split
    . apply rebalance_BST <;> try simp [*] at *
      apply deleteP; assumption
    . split
      . apply rebalance_BST <;> try simp [*] at *
        apply deleteP; assumption
      . split
        . apply BST.empty
        . assumption
        . assumption
        . split
          . rename_i hbst hforall _ _ -- case : | empty => rebalance l k' v' r'
            cases hbst
            cases hforall
            apply rebalance_BST
            . apply ForallTree_lt
              . assumption
              . assumption
            . assumption
            . assumption
            . assumption
          . rename_i hbst hforall _ _ _ _ _ _ -- cases : | tree _ nextK nextV _ => rebalance l nextK nextV (delete nextK r)
            cases hbst
            cases hforall
            rename_i hfindmin hbstl _ _ _ _ _ _
            -- cases hbstl
            apply rebalance_BST
            . apply ForallTree_lt
              . apply findmin_node_gt
                . apply hbstl
                . assumption
                . apply hfindmin
              . assumption
            . sorry
            . sorry
            . sorry

----------------------------- proof delete preserved balanced_tree -----------------------------

theorem delete_balance {α : Type u} (k : Nat) (t : Tree α)
    : balanced_tree t → balanced_tree (delete k t) := by
  sorry

----------------------------- proof delete preserved AVL -----------------------------

theorem delete_AVL {α : Type u} (k : Nat) (v : α) (t : Tree α)
    : AVLTree t → AVLTree (delete k t) := by
  intro avl
  cases avl
  constructor
  . apply delete_BST; assumption
  . apply delete_balance; assumption

----------------------------- proof lookup preserved AVL -----------------------------

def lookup {α : Type u} (d : α) (x : Nat) (t : Tree α) : α :=
  match t with
  | empty => d
  | tree l k v r =>
      if x < k then lookup d x l
      else if x > k then lookup d x r
      else v

theorem lookup_empty {α : Type u} (d : α) (k : Nat)
    : lookup d k empty = d := by
  rfl

theorem rebalance_lookup {α : Type u} (d : α) k k' (v : α) l r
    : BST l → BST r
      → ForallTree (fun x _ => x < k) l → ForallTree (fun x _ => k < x) r
      → lookup d k' (rebalance l k v r) =
          if k' < k then lookup d k' l
          else if k' > k then lookup d k' r
          else v := by
  sorry

theorem lookup_insert_eq {α : Type u} (d : α) t k v
    : AVLTree t → lookup d k (insert k v t) = v := by
  intro avl
  obtain ⟨bst, hbt⟩ := avl
  induction t with
  | empty => simp [insert, lookup]
  | tree l' k' v' r' ihl ihr =>
    cases bst
    unfold insert
    split
    . rw [rebalance_lookup] <;> try assumption
      . split
        . apply ihl
          . assumption
          . cases hbt
            assumption
        . apply ihl
          . assumption
          . cases hbt
            assumption
      . apply insert_BST; assumption
      . apply insertP <;> assumption
    . split
      . rw [rebalance_lookup] <;> try assumption
        . split
          . exfalso
            rename Not (LT.lt k k') => hnlt
            apply hnlt
            assumption
          . apply ihr;
            . assumption
            . cases hbt
              assumption
        . apply insert_BST; assumption
        . apply insertP <;> assumption
      . simp [lookup]

theorem lookup_ins_neq {α : Type u} (d : α) t k v
    : AVLTree t → k ≠ k' → lookup d k' (insert k v t) = lookup d k' t := by
  intro avl knk
  obtain ⟨bst, hbt⟩ := avl
  induction t with
  | empty =>
    simp [insert, lookup]
    intros
    exfalso
    apply knk
    omega
  | tree l'' k'' v'' r'' ihl ihr =>
    cases bst
    unfold insert
    split
    . rw [rebalance_lookup] <;> try assumption
      . split
        . simp [lookup]
          . split
            . apply ihl
              . assumption
              . cases hbt
                assumption
            . exfalso
              rename Not (LT.lt k' k'') => hnlt
              apply hnlt; assumption
        . split
          . simp [lookup]
            . split
              . exfalso
                rename Not (LT.lt k' k'') => hnlt
                apply hnlt; assumption
              . rfl
          . have heq : k' = k'' := by
              simp at *
              apply Nat.le_antisymm
              . assumption
              . assumption
            rw [heq]; simp [lookup]
      . apply insert_BST; assumption
      . apply insertP <;> assumption
    . split
      . rw [rebalance_lookup] <;> try assumption
        . split
          . simp [lookup]
            . split
              . rfl
              . exfalso
                rename Not (LT.lt k' k'') => hnlt
                apply hnlt; assumption
          . split
            . simp [lookup]
              . split
                . exfalso
                  rename Not (LT.lt k' k'') => hnlt
                  apply hnlt; assumption
                . apply ihr
                  . assumption
                  . cases hbt
                    assumption
            . have heq : k' = k'' := by
                simp at *
                apply Nat.le_antisymm
                . assumption
                . assumption
              rw [heq]; simp [lookup]
        . apply insert_BST; assumption
        . apply insertP <;> assumption
      . simp [lookup]
        repeat' split <;> try (exfalso; omega)
        . rfl
        . rfl
