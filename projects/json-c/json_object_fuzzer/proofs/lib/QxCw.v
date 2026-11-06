(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith Bool List Lia.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC QKJh Q6sh Q9dL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Bool.Bool Stdlib.Lists.List Stdlib.micromega.Lia.
Import stdpp.gmap.
Import QCiC.Mq0 QKJh Q6sh.Mq1 Q9dL.Mq0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope aprog_scope.

Fixpoint decode_u32s (n : nat) (data : list Z) : list Z :=
match n with
| O => []
| S n' =>
match data with
| b0 :: b1 :: b2 :: b3 :: rest => (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3) :: decode_u32s n' rest
| _ => []
end
end.

Section Main.
Context {ptr : Type}.
Variable TAB : ftables.
Variable fuel : nat.

#[local] Notation FM := (@FM ptr).

Definition llvm_fuzzer_test_one_input (data : list Z) : FM Z :=
let size := zlength data in
let str_len := size / 4 in

aassert (str_len <=? 2147483647) ;;;
let cps := decode_u32s (Z.to_nat str_len) data in
t <- acalloc str_len 4 ;;
match t with
| None => aret 0
| Some tp =>
aupd (set_types (zrepeat 0 str_len)) ;;;
b <- acalloc str_len 4 ;;
match b with
| None => aret 0
| Some bp =>
aupd (set_btypes (zrepeat 0 str_len)) ;;;
l <- acalloc str_len 1 ;;
match l with
| None => aret 0
| Some lp =>
aupd (set_levels (zrepeat 0 str_len)) ;;;
get_bidi_types TAB fuel cps str_len ;;;
get_bracket_types TAB fuel cps str_len ;;;
'(level, par_type) <- par_embedding_levels fuel str_len TY_ON ;;
afree tp ;;;
afree bp ;;;
afree lp ;;;
aret 0
end
end
end.

End Main.

Definition fuzz_one {ptr : Type} (TAB : ftables) (fuel : nat) (data : list Z) : aprog ptr Z :=
apbind (llvm_fuzzer_test_one_input TAB fuel data (@fst_init ptr)) (fun r => ARet (fst r)).
End Mq0.

From Stdlib Require Import ZArith Lia Bool.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKyU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKyU. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9dL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9dL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

