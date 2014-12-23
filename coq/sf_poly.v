Require Export sf_lists.

Inductive boollist : Type :=
| bool_nil : boollist
| bool_cons : bool -> boollist -> boollist.