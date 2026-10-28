(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanAcct.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX DrvKitA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DrvEntry_b Ba0Drv_defs_b Ba0DrvRead_b Ba0DrvG_defs_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.
Open Scope Z_scope.

Section FPX_1. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Definition STOPS_HA : list Z := 0xa7c2c :: 0xa7dd4 :: STOPSA.
Definition runHA (scr : scripts) (ss : sym_state) := sym_exec ASEGS FUELA true STOPS_HA scr ss [].

(* [comment removed for export] *)
Definition kn_hdrA : list kentry :=
  [KWord (SA (EVar 48) 0) 1 (EVar 71); KWord (SA (EVar 48) 1) 1 (EVar 72); KRange (EVar 71) 0 255; KRange (EVar 72) 0 255].
Definition knGLA : list kentry := kn_hdrA ++ knGA 6 67108863.

(* [comment removed for export] *)
Definition scr_fallA : scripts := SCR [false] [] [].
Definition rHa := Eval vm_compute in runHA scr_fallA (SS 0x12a8dc srGLA [] knGLA 73).
Definition srHa : list expr := Eval vm_compute in s_regs (fst (fst rHa)).
Definition cfglen_xA : expr := Eval vm_compute in nth 18 srHa (ELit 0).
Definition sx8_xA : expr := Eval vm_compute in nth 21 srHa (ELit 0).
Definition srHb0 : list expr := Eval vm_compute in map (esub sx8_xA (EVar 74)) (map (esub cfglen_xA (EVar 73)) srHa).
Definition PXA : expr := EAlu ALU_ADD (EVar 48) (EVar 73).
Definition kn_bmA : list kentry :=
  [KRange (EVar 73) 0 32767;
   KWord (SA PXA 2) 1 (EVar 75); KWord (SA PXA 3) 1 (EVar 76); KWord (SA PXA 4) 1 (EVar 77); KWord (SA PXA 5) 1 (EVar 78);
   KRange (EVar 75) 0 255; KRange (EVar 76) 0 255; KRange (EVar 77) 0 255; KRange (EVar 78) 0 255].
Definition knHb0 : list kentry := kn_bmA ++ kn_after rHa knGLA.
Definition rHb := Eval vm_compute in runHA scr0 (SS 0xa7c2c srHb0 [] knHb0 79).
Definition srHb : list expr := Eval vm_compute in s_regs (fst (fst rHb)).
Definition plen_xA : expr := Eval vm_compute in nth 13 srHb (ELit 0).

(* [comment removed for export] *)
Definition srT0A : list expr := Eval vm_compute in map (esub plen_xA (EVar 79)) srHb.
Definition kn_tgtA : list kentry :=
  [KRange (EVar 73) 0 32767; KRange (EVar 79) 0 67108857; KWord (SA (EVar 48) 2) 1 (EVar 80); KRange (EVar 80) 0 255].
Definition knT0A : list kentry := kn_tgtA ++ knGLA.

Definition summH (r : sym_state * list sidecond * scripts) := (s_pc (fst (fst r)), snd (fst r), s_next (fst (fst r)), s_log (fst (fst r))).
Lemma hdr_itinerary_okA :
  (s_pc (fst (fst rHa)), snd (fst rHa), s_log (fst (fst rHa))) = (0xa7c2c, [SCBr false BC_LTU (EVar 70) (EAlu ALU_ADD cfglen_xA (ELit 6))], [])
  /\ kn_after rHa knGLA = knGLA
  /\ (s_pc (fst (fst rHb)), snd (fst rHb), s_log (fst (fst rHb))) = (0xa7dd4, [], [])
  /\ kn_after rHb knHb0 = knHb0.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma knT0A_sub : ksubl_b (kn_tgtA ++ knHb0) knT0A = true.
Proof. vm_compute. reflexivity. Qed.
Lemma knHb0_eq : knHb0 = kn_bmA ++ knGLA.
Proof. vm_compute. reflexivity. Qed.
End FPX_1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPX_2. Context {fx : PropExec.FPState}.

Definition cfgFA (v71 v72 : word) : word :=
  edenot (Env (fun n => match n with 71%nat => v71 | 72%nat => v72 | _ => Z_to_bv 64 0 end) (blobs_ev [])) cfglen_xA.
Lemma cfglen_x_cfgFA : forall vals bl,
  edenot (Env (vals_ev vals) (blobs_ev bl)) cfglen_xA = cfgFA (vals_ev vals 71) (vals_ev vals 72).
Proof. intros. reflexivity. Qed.

Definition zseqA (n : nat) : list Z := map Z.of_nat (seq 0 n).
Lemma in_zseqA : forall n z, In z (zseqA n) <-> 0 <= z < Z.of_nat n.
Proof.
  intros n z. unfold zseqA. rewrite in_map_iff. split.
  - intros (k & <- & Hk). apply in_seq in Hk. lia.
  - intros Hz. exists (Z.to_nat z). split; [lia|]. apply in_seq. lia.
Qed.
Definition cfgGA (v72 : word) : word :=
  alu64 ALU_SRL (mul_div M_MUL (Z_to_bv 64 144115188075855872) (ext_val true 0 1 v72)) (Z_to_bv 64 49).
Definition cfgHA (v71 : word) : word := ext_val false 0 1 v71.
Lemma cfgF_splitA v71 v72 : cfgFA v71 v72 = bv_or (cfgGA v72) (cfgHA v71).
Proof. reflexivity. Qed.
Lemma cfgG_tabA : forallb (fun b1 => Z.eqb (bv_unsigned (cfgGA (Z_to_bv 64 b1))) (256 * (b1 mod 128))) (zseqA 256) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cfgH_tabA : forallb (fun b0 => Z.eqb (bv_unsigned (cfgHA (Z_to_bv 64 b0))) b0) (zseqA 256) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lor_tabA : forallb (fun a => forallb (fun b => Z.eqb (Z.lor (256 * a) b) (256 * a + b)) (zseqA 256)) (zseqA 128) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma cfgF_valA : forall b0 b1, 0 <= b0 < 256 -> 0 <= b1 < 256 ->
  cfgFA (Z_to_bv 64 b0) (Z_to_bv 64 b1) = Z_to_bv 64 ((b0 + 256 * b1) mod 32768).
Proof.
  intros b0 b1 H0 H1.
  pose proof cfgG_tabA as TG. rewrite forallb_forall in TG. specialize (TG b1 (proj2 (in_zseqA 256 b1) ltac:(cbn; lia))). apply Z.eqb_eq in TG.
  pose proof cfgH_tabA as TH. rewrite forallb_forall in TH. specialize (TH b0 (proj2 (in_zseqA 256 b0) ltac:(cbn; lia))). apply Z.eqb_eq in TH.
  pose proof (Z.mod_pos_bound b1 128 ltac:(lia)) as HM.
  pose proof lor_tabA as TL. rewrite forallb_forall in TL. specialize (TL (b1 mod 128) (proj2 (in_zseqA 128 (b1 mod 128)) ltac:(cbn; lia))).
  rewrite forallb_forall in TL. specialize (TL b0 (proj2 (in_zseqA 256 b0) ltac:(cbn; lia))). apply Z.eqb_eq in TL.
  apply bv_eq. rewrite cfgF_splitA, stdpp.bitvector.definitions.bv_or_unsigned, TG, TH, TL. symmetry.
  assert (E : (b0 + 256 * b1) mod 32768 = 256 * (b1 mod 128) + b0).
  { pose proof (Z.div_mod b1 128 ltac:(lia)) as D.
    symmetry. apply (Zmod_unique (b0 + 256 * b1) 32768 (b1 / 128)); lia. }
  rewrite E. apply u_small. lia.
Qed.

Definition sx8FA (v72 : word) : word := ext_val true 0 1 v72.
Lemma sx8_x_sx8FA : forall vals bl, edenot (Env (vals_ev vals) (blobs_ev bl)) sx8_xA = sx8FA (vals_ev vals 72).
Proof. intros. reflexivity. Qed.

Lemma plen_x_eqA : plen_xA = EAlu ALU_ADD (EAlu ALU_ADD (EVar 70) (EMd M_MUL (ELit (-1)) (EVar 73))) (ELit (-6)).
Proof. reflexivity. Qed.
Lemma mod_of_decompC : forall a b q r, 0 < b -> 0 <= r < b -> a = b * q + r -> a mod b = r.
Proof. intros a b q r Hb Hr He. symmetry. apply (Zmod_unique a b q r); lia. Qed.
Lemma add_negmulA : forall a c : Z, 0 <= c <= a -> a < 2 ^ 64 ->
  alu64 ALU_ADD (Z_to_bv 64 a) (mul_div M_MUL (Z_to_bv 64 (-1)) (Z_to_bv 64 c)) = Z_to_bv 64 (a - c).
Proof.
  intros a c H1 H2. apply bv_eq. rewrite alu_add. unfold v_add. rewrite u_mul64.
  rewrite !Z_to_bv_unsigned. change (bv_modulus 64) with (2 ^ 64).
  rewrite (bv_wrap_small 64 a) by (change (bv_modulus 64) with (2 ^ 64); lia).
  rewrite (bv_wrap_small 64 c) by (change (bv_modulus 64) with (2 ^ 64); lia).
  rewrite (bv_wrap_small 64 (a - c)) by (change (bv_modulus 64) with (2 ^ 64); lia).
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
  destruct (Z.eq_dec c 0) as [->|Hnz].
  - rewrite Z.mul_0_r. change ((0) mod 2 ^ 64) with 0. rewrite Z.add_0_r, Z.sub_0_r. apply Z.mod_small. lia.
  - rewrite (mod_of_decompC ((2 ^ 64 - 1) * c) (2 ^ 64) (c - 1) (2 ^ 64 - c)) by lia.
    rewrite (mod_of_decompC (a + (2 ^ 64 - c)) (2 ^ 64) 1 (a - c)) by lia. reflexivity.
Qed.
Lemma add_neglitA : forall a k : Z, k <= 0 -> 0 <= a + k -> a < 2 ^ 64 ->
  alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 k) = Z_to_bv 64 (a + k).
Proof.
  intros a k H0 H1 H2. apply bv_eq. rewrite alu_add. unfold v_add.
  rewrite !Z_to_bv_unsigned. change (bv_modulus 64) with (2 ^ 64).
  rewrite (bv_wrap_small 64 a) by (change (bv_modulus 64) with (2 ^ 64); lia).
  rewrite (bv_wrap_small 64 (a + k)) by (change (bv_modulus 64) with (2 ^ 64); lia).
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  destruct (Z.eq_dec k 0) as [->|Hnz].
  - change ((0) mod 2 ^ 64) with 0. rewrite !Z.add_0_r. apply Z.mod_small. lia.
  - rewrite (mod_of_decompC k (2 ^ 64) (-1) (2 ^ 64 + k)) by lia.
    rewrite (mod_of_decompC (a + (2 ^ 64 + k)) (2 ^ 64) 1 (a + k)) by lia. reflexivity.
Qed.
Lemma plen_valA : forall (Lz Cc : Z) vals bl,
  0 <= Cc -> 6 + Cc <= Lz < 2 ^ 32 ->
  vals_ev vals 70 = Z_to_bv 64 Lz -> vals_ev vals 73 = Z_to_bv 64 Cc ->
  edenot (Env (vals_ev vals) (blobs_ev bl)) plen_xA = Z_to_bv 64 (Lz - 6 - Cc).
Proof.
  intros Lz Cc vals bl HC HL P70 P73. rewrite plen_x_eqA. cbn [edenot ev]. rewrite P70, P73.
  rewrite add_negmulA by lia. rewrite add_neglitA by lia. f_equal. lia.
Qed.

End FPX_2.
