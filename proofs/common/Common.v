Require Export Pfv.Lib.Common.
Require Export Pfv.Lib.Lib.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Import ListNotations.

Local Open Scope hmap_scope.

Section HMapHelper.
  Context `{sz_ops}.
  Context `{vid_ops}.

  Definition hsimple (i: vid_t) (v: hmap) : hmap :=
    if is_empty v then HMapEmpty else HMapStr [(i, v)].

End HMapHelper.
