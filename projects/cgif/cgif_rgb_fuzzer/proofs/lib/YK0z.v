(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Local Open Scope Z_scope.
Fixpoint udec_aux (v : Z) (fuel : nat) : list byte :=
match fuel with
| O => []
| S f => if v =? 0 then []
else udec_aux (v / 10) f ++ [Z_to_bv 8 (48 + v mod 10)]
end.
Definition udec (v : Z) : list byte :=
if v =? 0 then [Z_to_bv 8 48] else udec_aux v 24.








