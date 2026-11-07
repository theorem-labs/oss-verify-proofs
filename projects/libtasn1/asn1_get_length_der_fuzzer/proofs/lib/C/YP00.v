(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Trevor Hansen, 2026-11: module names. *)
From Stdlib Require Import ZArith List Lia Bool String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YK0z.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Fixpoint udigits_aux (v : Z) (fuel : nat) : list Z :=
match fuel with
| O => []
| S f => if v =? 0 then []
else udigits_aux (v / 10) f ++ [48 + v mod 10]
end.
Definition dec_fuel : nat := 24%nat.
Definition udecZ (v : Z) : list Z :=
if v =? 0 then [48] else udigits_aux v dec_fuel.
Definition sdecZ (v : Z) : list Z :=
if v <? 0 then 45 :: udecZ (- v) else udecZ v.
Definition to_bytes (l : list Z) : list byte := map (Z_to_bv 8) l.
Example sdecZ_ex0 : sdecZ 0 = [48].                 Proof. reflexivity. Qed.
Example sdecZ_ex1 : sdecZ 7 = [55].                 Proof. reflexivity. Qed.
Example sdecZ_ex2 : sdecZ (-3) = [45; 51].          Proof. reflexivity. Qed.
Example sdecZ_ex3 : sdecZ 1024 = [49; 48; 50; 52].  Proof. reflexivity. Qed.
Example sdecZ_ex4 : sdecZ (-12) = [45; 49; 50].     Proof. reflexivity. Qed.
Example udecZ_ex5 : udecZ 67108864 = [54;55;49;48;56;56;54;52]. Proof. reflexivity. Qed.

















Definition strZ (s : string) : list Z :=
map (fun a => Z.of_N (N_of_ascii a)) (list_ascii_of_string s).
Definition strB (s : string) : list byte := to_bytes (strZ s).
Definition nl : list byte := to_bytes [10].
