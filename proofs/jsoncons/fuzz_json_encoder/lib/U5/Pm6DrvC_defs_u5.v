(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import RunEnv
  PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6MainEntry_u5 Pm6LibStdioCall_u5.
  From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import HeapIface DrvKit. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6Drv_defs_u5 Pm6DrvG_defs_u5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.

Section FPX_1. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Definition STOPS_H : list Z := (0x3a298 :: 0x3a440 :: STOPS)%Z.
Definition runH (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS_H scr ss [].
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition knGS : list kentry := knG 0 5.
Definition rHs := Eval vm_compute in run scr0 (SS 0xbeff4 srGL [] knGS 71).
Definition srHs : list expr := Eval vm_compute in s_regs (fst (fst rHs)).
Definition knHs : list kentry := Eval vm_compute in kn_after rHs knGS.
(* [comment removed for export] *)
Definition scS : stdio_res := Eval vm_compute in the_sc (stdio_call 71 srHs knHs).
Definition srIs0 : list expr := Eval vm_compute in sc_sr scS.
Definition knIs0 : list kentry := Eval vm_compute in sc_kn scS.
Definition rIs := Eval vm_compute in run scr0 (SS (sc_ret scS) srIs0 [] knIs0 103).
Definition srIs : list expr := Eval vm_compute in s_regs (fst (fst rIs)).
Definition knIs : list kentry := Eval vm_compute in kn_after rIs knIs0.
(* [comment removed for export] *)
Definition srJs0 : list expr := Eval vm_compute in sr_after_call_j srIs (map ridx c_kept) 103.
Definition knJs0 : list kentry := Eval vm_compute in keep_alloc MSO [] [] knIs.
Definition rJs := Eval vm_compute in run scr0 (SS 0x3a36c srJs0 [] knJs0 135).
Definition srJs : list expr := Eval vm_compute in s_regs (fst (fst rJs)).
Definition knJs : list kentry := Eval vm_compute in kn_after rJs knJs0.

(* [comment removed for export] *)
Definition kn_hdr : list kentry :=
  [KWord (SA (EVar 48) 0) 1 (EVar 71); KWord (SA (EVar 48) 1) 1 (EVar 72); KRange (EVar 71) 0 255; KRange (EVar 72) 0 255].
Definition knGL : list kentry := kn_hdr ++ knG 6 67108863.

(* [comment removed for export] *)
Definition scr_taken : scripts := SCR [true] [] [].
Definition rHo := Eval vm_compute in runH scr_taken (SS 0xbeff4 srGL [] knGL 73).
Definition srHo : list expr := Eval vm_compute in s_regs (fst (fst rHo)).
Definition knHo : list kentry := Eval vm_compute in kn_after rHo knGL.
Definition scO : stdio_res := Eval vm_compute in the_sc (stdio_call 73 srHo knHo).
Definition srIo0 : list expr := Eval vm_compute in sc_sr scO.
Definition knIo0 : list kentry := Eval vm_compute in sc_kn scO.
Definition rIo := Eval vm_compute in run scr0 (SS (sc_ret scO) srIo0 [] knIo0 105).
Definition srIo : list expr := Eval vm_compute in s_regs (fst (fst rIo)).
Definition knIo : list kentry := Eval vm_compute in kn_after rIo knIo0.
Definition srJo0 : list expr := Eval vm_compute in sr_after_call_j srIo (map ridx c_kept) 105.
Definition knJo0 : list kentry := Eval vm_compute in keep_alloc MSO [] [] knIo.
Definition rJo := Eval vm_compute in run scr0 (SS 0x3a36c srJo0 [] knJo0 137).
Definition srJo : list expr := Eval vm_compute in s_regs (fst (fst rJo)).
Definition knJo : list kentry := Eval vm_compute in kn_after rJo knJo0.

(* [comment removed for export] *)
Definition scr_fall : scripts := SCR [false] [] [].
Definition rHa := Eval vm_compute in runH scr_fall (SS 0xbeff4 srGL [] knGL 73).
Definition srHa : list expr := Eval vm_compute in s_regs (fst (fst rHa)).
(* [comment removed for export] *)
Definition cfglen_x : expr := Eval vm_compute in nth 18 srHa (ELit 0).
Definition sx8_x : expr := Eval vm_compute in nth 21 srHa (ELit 0).
(* [comment removed for export] *)
Definition srHb0 : list expr := Eval vm_compute in map (esub sx8_x (EVar 74)) (map (esub cfglen_x (EVar 73)) srHa).
(* [comment removed for export] *)
Definition PX : expr := EAlu ALU_ADD (EVar 48) (EVar 73).
Definition kn_bm : list kentry :=
  [KRange (EVar 73) 0 32767;
   KWord (SA PX 2) 1 (EVar 75); KWord (SA PX 3) 1 (EVar 76); KWord (SA PX 4) 1 (EVar 77); KWord (SA PX 5) 1 (EVar 78);
   KRange (EVar 75) 0 255; KRange (EVar 76) 0 255; KRange (EVar 77) 0 255; KRange (EVar 78) 0 255].
Definition knHb0 : list kentry := kn_bm ++ knGL.
Definition rHb := Eval vm_compute in runH scr0 (SS 0x3a298 srHb0 [] knHb0 79).
Definition srHb : list expr := Eval vm_compute in s_regs (fst (fst rHb)).
(* [comment removed for export] *)
Definition plen_x : expr := Eval vm_compute in nth 13 srHb (ELit 0).

(* [comment removed for export] *)
Definition srT0 : list expr := Eval vm_compute in map (esub plen_x (EVar 79)) srHb.
Definition kn_tgt : list kentry :=
  [KRange (EVar 73) 0 32767; KRange (EVar 79) 0 67108857; KWord (SA (EVar 48) 2) 1 (EVar 80); KRange (EVar 80) 0 255].
Definition knT0 : list kentry := kn_tgt ++ knGL.

(* [comment removed for export] *)
Lemma hdr_itinerary_ok :
  (s_pc (fst (fst rHs)), snd (fst rHs)) = (0xb2bb8%Z, [])
  /\ stdio_call 71 srHs knHs = Some scS /\ (sc_ret scS, sc_f scS, sc_fd scS) = (0xb3450%Z, 0xcb338%Z, 2%Z)
  /\ (s_pc (fst (fst rIs)), snd (fst rIs), s_log (fst (fst rIs))) = (0xaf7b8%Z, [], [])
  /\ (s_pc (fst (fst rJs)), snd (fst rJs), s_log (fst (fst rJs))) = (0xad914%Z, [], [])
  /\ (s_pc (fst (fst rHo)), snd (fst rHo)) = (0xb2bb8%Z, [SCBr true BC_LTU (EVar 70) (EAlu ALU_ADD cfglen_x (ELit 6))])
  /\ stdio_call 73 srHo knHo = Some scO /\ (sc_ret scO, sc_f scO, sc_fd scO) = (0xb3450%Z, 0xcb338%Z, 2%Z)
  /\ (s_pc (fst (fst rIo)), snd (fst rIo), s_log (fst (fst rIo))) = (0xaf7b8%Z, [], [])
  /\ (s_pc (fst (fst rJo)), snd (fst rJo), s_log (fst (fst rJo))) = (0xad914%Z, [], [])
  /\ (s_pc (fst (fst rHa)), snd (fst rHa), s_log (fst (fst rHa))) = (0x3a298%Z, [SCBr false BC_LTU (EVar 70) (EAlu ALU_ADD cfglen_x (ELit 6))], [])
  /\ kn_after rHa knGL = knGL
  /\ (s_pc (fst (fst rHb)), snd (fst rHb), s_log (fst (fst rHb))) = (0x3a440%Z, [], [])
  /\ kn_after rHb knHb0 = knHb0.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma knT0_sub : ksubl_b (kn_tgt ++ knHb0) knT0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma knGL_sub_Hb0 : ksubl_b knHb0 knGL = true.
Proof. vm_compute. reflexivity. Qed.

End FPX_1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPX_2. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Definition cfgF (v71 v72 : word) : word :=
  edenot (Env (fun n => match n with 71%nat => v71 | 72%nat => v72 | _ => Z_to_bv 64 0 end) (blobs_ev [])) cfglen_x.

Lemma cfglen_x_cfgF : forall vals bl,
  edenot (Env (vals_ev vals) (blobs_ev bl)) cfglen_x = cfgF (vals_ev vals 71) (vals_ev vals 72).
Proof. intros. reflexivity. Qed.

Definition zseq (n : nat) : list Z := map Z.of_nat (seq 0 n).

Lemma in_zseq : forall n z, In z (zseq n) <-> (0 <= z < Z.of_nat n)%Z.
Proof.
  intros n z. unfold zseq. rewrite in_map_iff. split.
  - intros (k & <- & Hk). apply in_seq in Hk. lia.
  - intros Hz. exists (Z.to_nat z). split; [lia|]. apply in_seq. lia.
Qed.

(* [comment removed for export] *)
Definition cfgG (v72 : word) : word :=
  alu64 ALU_SRL (mul_div M_MUL (Z_to_bv 64 144115188075855872) (ext_val true 0 1 v72)) (Z_to_bv 64 49).
Definition cfgH (v71 : word) : word := ext_val false 0 1 v71.
Lemma cfgF_split v71 v72 : cfgF v71 v72 = bv_or (cfgG v72) (cfgH v71).
Proof. reflexivity. Qed.
Lemma cfgG_tab : forallb (fun b1 => Z.eqb (bv_unsigned (cfgG (Z_to_bv 64 b1))) (256 * (b1 mod 128))) (zseq 256) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cfgH_tab : forallb (fun b0 => Z.eqb (bv_unsigned (cfgH (Z_to_bv 64 b0))) b0) (zseq 256) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lor_tab : forallb (fun a => forallb (fun b => Z.eqb (Z.lor (256 * a) b) (256 * a + b)) (zseq 256)) (zseq 128) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma cfgF_val : forall b0 b1, (0 <= b0 < 256)%Z -> (0 <= b1 < 256)%Z ->
  cfgF (Z_to_bv 64 b0) (Z_to_bv 64 b1) = Z_to_bv 64 ((b0 + 256 * b1) mod 32768).
Proof.
  intros b0 b1 H0 H1.
  pose proof cfgG_tab as TG. rewrite forallb_forall in TG. specialize (TG b1 (proj2 (in_zseq 256 b1) ltac:(cbn; lia))). apply Z.eqb_eq in TG.
  pose proof cfgH_tab as TH. rewrite forallb_forall in TH. specialize (TH b0 (proj2 (in_zseq 256 b0) ltac:(cbn; lia))). apply Z.eqb_eq in TH.
  pose proof (Z.mod_pos_bound b1 128 ltac:(lia)) as HM.
  pose proof lor_tab as TL. rewrite forallb_forall in TL. specialize (TL (b1 mod 128)%Z (proj2 (in_zseq 128 (b1 mod 128)%Z) ltac:(cbn; lia))).
  rewrite forallb_forall in TL. specialize (TL b0 (proj2 (in_zseq 256 b0) ltac:(cbn; lia))). apply Z.eqb_eq in TL.
  apply bv_eq. rewrite cfgF_split, stdpp.bitvector.definitions.bv_or_unsigned, TG, TH, TL. symmetry.
  assert (E : ((b0 + 256 * b1) mod 32768 = 256 * (b1 mod 128) + b0)%Z).
  { pose proof (Z.div_mod b1 128 ltac:(lia)) as D.
    symmetry. apply (Zmod_unique (b0 + 256 * b1) 32768 (b1 / 128)); lia. }
  rewrite E. apply u_small. lia.
Qed.

(* [comment removed for export] *)
Definition sx8F (v72 : word) : word := ext_val true 0 1 v72.
Lemma sx8_x_sx8F : forall vals bl, edenot (Env (vals_ev vals) (blobs_ev bl)) sx8_x = sx8F (vals_ev vals 72).
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma plen_x_eq : plen_x = EAlu ALU_ADD (EAlu ALU_ADD (EVar 70) (EMd M_MUL (ELit (-1)) (EVar 73))) (ELit (-6)).
Proof. reflexivity. Qed.

Lemma mod_of_decomp' : forall a b q r, (0 < b)%Z -> (0 <= r < b)%Z -> (a = b * q + r)%Z -> (a mod b = r)%Z.
Proof. intros a b q r Hb Hr He. symmetry. apply (Zmod_unique a b q r); lia. Qed.
Lemma add_negmul : forall a c : Z, (0 <= c <= a)%Z -> (a < 2 ^ 64)%Z ->
  alu64 ALU_ADD (Z_to_bv 64 a) (mul_div M_MUL (Z_to_bv 64 (-1)) (Z_to_bv 64 c)) = Z_to_bv 64 (a - c).
Proof.
  intros a c H1 H2. apply bv_eq. rewrite alu_add. unfold v_add. rewrite u_mul64.
  rewrite !Z_to_bv_unsigned. change (bv_modulus 64) with (2 ^ 64)%Z.
  rewrite (bv_wrap_small 64 a) by (change (bv_modulus 64) with (2 ^ 64)%Z; lia).
  rewrite (bv_wrap_small 64 c) by (change (bv_modulus 64) with (2 ^ 64)%Z; lia).
  rewrite (bv_wrap_small 64 (a - c)) by (change (bv_modulus 64) with (2 ^ 64)%Z; lia).
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
  replace ((-1) mod 2 ^ 64)%Z with (2 ^ 64 - 1)%Z by reflexivity.
  destruct (Z.eq_dec c 0) as [->|Hnz].
  - rewrite Z.mul_0_r. change ((0) mod 2 ^ 64)%Z with 0%Z. rewrite Z.add_0_r, Z.sub_0_r. apply Z.mod_small. lia.
  - rewrite (mod_of_decomp' ((2 ^ 64 - 1) * c) (2 ^ 64) (c - 1) (2 ^ 64 - c)) by lia.
    rewrite (mod_of_decomp' (a + (2 ^ 64 - c)) (2 ^ 64) 1 (a - c)) by lia. reflexivity.
Qed.
Lemma add_neglit : forall a k : Z, (k <= 0)%Z -> (0 <= a + k)%Z -> (a < 2 ^ 64)%Z ->
  alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 k) = Z_to_bv 64 (a + k).
Proof.
  intros a k H0 H1 H2. apply bv_eq. rewrite alu_add. unfold v_add.
  rewrite !Z_to_bv_unsigned. change (bv_modulus 64) with (2 ^ 64)%Z.
  rewrite (bv_wrap_small 64 a) by (change (bv_modulus 64) with (2 ^ 64)%Z; lia).
  rewrite (bv_wrap_small 64 (a + k)) by (change (bv_modulus 64) with (2 ^ 64)%Z; lia).
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
  destruct (Z.eq_dec k 0) as [->|Hnz].
  - change ((0) mod 2 ^ 64)%Z with 0%Z. rewrite !Z.add_0_r. apply Z.mod_small. lia.
  - rewrite (mod_of_decomp' k (2 ^ 64) (-1) (2 ^ 64 + k)) by lia.
    rewrite (mod_of_decomp' (a + (2 ^ 64 + k)) (2 ^ 64) 1 (a + k)) by lia. reflexivity.
Qed.
Lemma plen_val : forall (Lz C : Z) vals bl,
  (0 <= C)%Z -> (6 + C <= Lz < 2 ^ 32)%Z ->
  vals_ev vals 70 = Z_to_bv 64 Lz -> vals_ev vals 73 = Z_to_bv 64 C ->
  edenot (Env (vals_ev vals) (blobs_ev bl)) plen_x = Z_to_bv 64 (Lz - 6 - C).
Proof.
  intros Lz C vals bl HC HL P70 P73. rewrite plen_x_eq. cbn [edenot ev]. rewrite P70, P73.
  rewrite add_negmul by lia. rewrite add_neglit by lia. f_equal. lia.
Qed.

End FPX_2.
