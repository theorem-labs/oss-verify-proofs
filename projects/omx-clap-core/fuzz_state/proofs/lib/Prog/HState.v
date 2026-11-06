From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Import ListNotations.
Local Open Scope Z_scope.

Definition zs (bs : list byte) : list Z := map (fun b => bv_unsigned b) bs.

Definition bz (xs : list Z) : list byte := map (fun z => Z_to_bv 8 z) xs.

Definition b64_alloc_bound (n : Z) : Z := n / 4 * 3 + 3.

Definition in_window (sp k a : Z) : Prop := sp - k <= a < sp.


Definition opt_ok {T : Type} (o : option T) : bool := match o with Some _ => true | None => false end.