(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


Definition cid_code (s : Z) : Z :=
  let v0 := (Z.shiftr s 1) in
  let v1 := (Z.lor s v0) in
  let v2 := (Z.shiftr v1 2) in
  let v3 := (Z.lor v1 v2) in
  let v4 := (Z.shiftr v3 4) in
  let v5 := (Z.lor v3 v4) in
  let v6 := (Z.shiftr v5 8) in
  let v7 := (Z.lor v5 v6) in
  let v8 := (Z.shiftr v7 16) in
  let v9 := (Z.lor v7 v8) in
  let v10 := (Z.shiftr v9 32) in
  let v11 := (Z.lor v9 v10) in
  let v12 := (Z.lxor v11 18446744073709551615) in
  let v13 := (Z.shiftr v12 1) in
  let v14 := (Z.land v13 6148914691236517205) in
  let v15 := (Z.sub v12 v14) in
  let v16 := (Z.modulo v15 18446744073709551616) in
  let v17 := (Z.shiftr v16 2) in
  let v18 := (Z.land v16 3689348814741910323) in
  let v19 := (Z.land v17 3689348814741910323) in
  let v20 := (Z.add v18 v19) in
  let v21 := (Z.modulo v20 18446744073709551616) in
  let v22 := (Z.shiftr v21 4) in
  let v23 := (Z.add v20 v22) in
  let v24 := (Z.modulo v23 18446744073709551616) in
  let v25 := (Z.land v24 1085102592571150095) in
  let v26 := (Z.mul v25 72340172838076673) in
  let v27 := (Z.modulo v26 18446744073709551616) in
  let v28 := (Z.shiftr v27 56) in
  let v29 := (Z.sub 62 v28) in
  let v30 := (bv_swrap 32%N v29) in
  let v31 := (Z.modulo v30 18446744073709551616) in
  (Z.add (Z.add (Z.lor (Z.lxor (Z.modulo (Z.shiftl v28 1) 18446744073709551616) 126) (Z.land (Z.shiftr s (Z.modulo v31 64)) 1)) (Z.b2z (Z.ltb 0 (Z.land s (Z.lxor (Z.modulo (bv_swrap 32%N (Z.shiftl 18446744073709551615 (Z.modulo v31 32))) 18446744073709551616) 18446744073709551615))))) (-2)).

(* [comment removed for export] *)
Fixpoint zchk (f g : Z -> Z) (step : Z) (k : nat) (s : Z) : bool :=
  match k with O => true | S k' => (f s =? g s) && zchk f g step k' (s + step) end.
Lemma zchk_sound : forall f g step k s, zchk f g step k s = true -> forall i, 0 <= i < Z.of_nat k -> f (s + step * i) = g (s + step * i).
Proof.
  intros f g step. induction k as [|k IH]; intros s H i Hi; [lia|]. cbn [zchk] in H. apply andb_prop in H as [H1 H2].
  destruct (Z.eq_dec i 0) as [->|NZ].
  - rewrite Z.mul_0_r, Z.add_0_r. apply Z.eqb_eq. exact H1.
  - replace (s + step * i) with (s + step + step * (i - 1)) by lia. apply (IH _ H2). lia.
Qed.

(* [comment removed for export] *)
Lemma cid_chk_ok : zchk cid_code classid 8 (Z.to_nat 8128) 520 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma cid_code_ok : forall s, 513 <= s <= 65536 -> s mod 8 = 0 -> cid_code s = classid s.
Proof.
  intros s Hs Hm. replace s with (520 + 8 * ((s - 520) / 8)) by (Z.div_mod_to_equations; lia).
  apply (zchk_sound _ _ _ _ _ cid_chk_ok). Z.div_mod_to_equations; lia.
Qed.
(* [comment removed for export] *)
Definition cls_lo (s : Z) : Z := if (1 <=? classid s) && (classid s <=? 30) then 1 else 0.
Lemma cls_chk_ok : zchk cls_lo (fun _ => 1) 1 (Z.to_nat 65536) 1 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma classid_range : forall s, 1 <= s <= 65536 -> 1 <= classid s <= 30.
Proof.
  intros s Hs. pose proof (zchk_sound _ _ _ _ _ cls_chk_ok (s - 1) ltac:(lia)) as E. cbn beta in E.
  replace (1 + 1 * (s - 1)) with s in E by lia. unfold cls_lo in E.
  destruct (Z.leb_spec0 1 (classid s)); destruct (Z.leb_spec0 (classid s) 30); cbn in E; lia.
Qed.


End CeilWrap.
