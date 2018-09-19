Require Import StructPoly.ListLike.

Instance ListIsList : ListLike list :=
  {
    ll_nil := @nil;
    ll_cons := @cons;

    list_like_rec := @list_rec;
    list_like_rect := @list_rect;
    list_like_ind := @list_ind
  }.
Proof.
  all:trivial.
Defined.