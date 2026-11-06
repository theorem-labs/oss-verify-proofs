(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsRtAtomic.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.
Export OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.LibAtomic.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPGen1.
Context {fx : FPState}.

(* [comment removed for export] *)
Lemma step_amo_w : forall segs regs pc mem rom w op aq rl rd rs1 rs2 bs v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Amo op AW aq rl rd rs1 rs2, 4%Z) ->
  (bv_unsigned (getr regs rs1) mod 4 = 0)%Z ->
  rdn segs mem (getr regs rs1) 4%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.store_ok segs mem (getr regs rs1) 4%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_lw v)) (v_addi pc 4)
                  (wbytes mem (getr regs rs1)
                     (Z_to_le_bytes 4 (bv_unsigned (amo_val op (low32 v) (low32 (getr regs rs2)))))) rom).
Proof using.
  intros segs regs pc mem rom w op aq rl rd rs1 rs2 bs v Hfetch Hecall Hdecode Hal Hread Hv Hok.
  atomic_pipeline Hfetch Hecall Hdecode.
  change (if is_x0 rs1 then Z_to_bv 64 0 else reg_get regs rs1) with (getr regs rs1).
  change (if is_x0 rs2 then Z_to_bv 64 0 else reg_get regs rs2) with (getr regs rs2).
  rewrite Hal. change (negb (0 =? 0)%Z) with false. cbv beta iota.
  rewrite ov_rdn, Hread. cbv beta iota.
  rewrite Hok. cbv beta iota.
  rewrite (le_word_v _ _ Hv), write_to_mem_wbytes, b_lw_val, b_npc4.
  (lazymatch goal with |- ?G => let G' := eval unfold regupd, low32 in G in change_no_check G' end). destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_amo_d : forall segs regs pc mem rom w op aq rl rd rs1 rs2 bs v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Amo op AD aq rl rd rs1 rs2, 4%Z) ->
  (bv_unsigned (getr regs rs1) mod 8 = 0)%Z ->
  rdn segs mem (getr regs rs1) 8%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.store_ok segs mem (getr regs rs1) 8%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd v) (v_addi pc 4)
                  (wbytes mem (getr regs rs1)
                     (Z_to_le_bytes 8 (bv_unsigned (amo_val op v (getr regs rs2))))) rom).
Proof using.
  intros segs regs pc mem rom w op aq rl rd rs1 rs2 bs v Hfetch Hecall Hdecode Hal Hread Hv Hok.
  assert (Hz : bv_extract 0 64 v = v).
  { apply bv_eq. rewrite bv_extract_unsigned, Z.shiftr_0_r. apply bv_wrap_bv_unsigned. }
  atomic_pipeline Hfetch Hecall Hdecode.
  change (if is_x0 rs1 then Z_to_bv 64 0 else reg_get regs rs1) with (getr regs rs1).
  change (if is_x0 rs2 then Z_to_bv 64 0 else reg_get regs rs2) with (getr regs rs2).
  rewrite Hal. change (negb (0 =? 0)%Z) with false. cbv beta iota.
  rewrite ov_rdn, Hread. cbv beta iota.
  rewrite Hok. cbv beta iota.
  rewrite (le_word_v _ _ Hv), Hz, write_to_mem_wbytes, b_npc4.
  (lazymatch goal with |- ?G => let G' := eval unfold regupd in G in change_no_check G' end). destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma Z_to_le_bytes_mod32 : forall a b,
  bv_wrap 32 a = bv_wrap 32 b -> Z_to_le_bytes 4 a = Z_to_le_bytes 4 b.
Proof using.
  intros a b H. rewrite <- (Z_to_le_bytes_wrap 4 32 a) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia).
  rewrite <- (Z_to_le_bytes_wrap 4 32 b) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia). rewrite H. reflexivity.
Qed.

Lemma amo_add_w_bytes : forall v s : word,
  Z_to_le_bytes 4 (bv_unsigned (amo_val AMO_ADD (low32 v) (low32 s))) = word_to_le_bytes 4 (v_add v s).
Proof using.
  intros v s. (lazymatch goal with |- ?G => let G' := eval cbn [amo_val] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold word_to_le_bytes, low32, v_add in G in change_no_check G' end).
  apply Z_to_le_bytes_mod32.
  rewrite bv_add_unsigned, !bv_extract_unsigned, !Z.shiftr_0_r, Z_to_bv_unsigned.
  rewrite bv_wrap_idemp, bv_wrap_add_idemp, (bv_wrap_bv_wrap 32 64) by lia. reflexivity.
Qed.


Lemma amo_add_d_bytes : forall v s : word,
  Z_to_le_bytes 8 (bv_unsigned (amo_val AMO_ADD v s)) = word_to_le_bytes 8 (v_add v s).
Proof using.
  intros v s. (lazymatch goal with |- ?G => let G' := eval cbn [amo_val] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold word_to_le_bytes, v_add in G in change_no_check G' end).
  rewrite bv_add_unsigned, Z_to_bv_unsigned. reflexivity.
Qed.


Lemma step_amoadd_w : forall segs regs pc mem rom w aq rl rd rs1 rs2 bs v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Amo AMO_ADD AW aq rl rd rs1 rs2, 4%Z) ->
  (bv_unsigned (getr regs rs1) mod 4 = 0)%Z ->
  rdn segs mem (getr regs rs1) 4%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.store_ok segs mem (getr regs rs1) 4%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_lw v)) (v_addi pc 4)
                  (wbytes mem (getr regs rs1) (word_to_le_bytes 4 (v_add v (getr regs rs2)))) rom).
Proof using.
  intros segs regs pc mem rom w aq rl rd rs1 rs2 bs v Hf He Hd Hal Hread Hv Hok.
  rewrite (step_amo_w segs regs pc mem rom w AMO_ADD aq rl rd rs1 rs2 bs v Hf He Hd Hal Hread Hv Hok).
  rewrite amo_add_w_bytes. reflexivity.
Qed.


Lemma step_amoadd_d : forall segs regs pc mem rom w aq rl rd rs1 rs2 bs v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Amo AMO_ADD AD aq rl rd rs1 rs2, 4%Z) ->
  (bv_unsigned (getr regs rs1) mod 8 = 0)%Z ->
  rdn segs mem (getr regs rs1) 8%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.store_ok segs mem (getr regs rs1) 8%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd v) (v_addi pc 4)
                  (wbytes mem (getr regs rs1) (word_to_le_bytes 8 (v_add v (getr regs rs2)))) rom).
Proof using.
  intros segs regs pc mem rom w aq rl rd rs1 rs2 bs v Hf He Hd Hal Hread Hv Hok.
  rewrite (step_amo_d segs regs pc mem rom w AMO_ADD aq rl rd rs1 rs2 bs v Hf He Hd Hal Hread Hv Hok).
  rewrite amo_add_d_bytes. reflexivity.
Qed.

End FPGen1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPGen2.
Context {fx : FPState}.

Lemma c_eq_zero : c_eq (Z_to_bv 64 0) (Z_to_bv 64 0) = true.
Proof using. reflexivity. Qed.

(* [comment removed for export] *)
Lemma cas_d_run : forall segs regs (p0 p1 p2 p3 p4 : word) mem rom w0 w1 w2 w3 aq0 rl0 aq2 rl2
    (rd ra rt rn b1 b2 : reg) c (imm1 imm3 : bv 13) bs v,
  fetch_word segs p0 = Some w0 -> is_ecall w0 = false -> decode_any w0 = Some (Lr AD aq0 rl0 rd ra, 4%Z) ->
  fetch_word segs p1 = Some w1 -> is_ecall w1 = false -> decode_any w1 = Some (Branch c b1 b2 imm1, 4%Z) ->
  fetch_word segs p2 = Some w2 -> is_ecall w2 = false -> decode_any w2 = Some (Sc AD aq2 rl2 rt ra rn, 4%Z) ->
  fetch_word segs p3 = Some w3 -> is_ecall w3 = false -> decode_any w3 = Some (Branch BC_NE rt 0 imm3, 4%Z) ->
  v_addi p0 4 = p1 -> v_addi p1 4 = p2 -> v_addi p2 4 = p3 -> v_addi p3 4 = p4 ->
  rd <> 0 -> rt <> 0 -> ra <> rd ->
  (bv_unsigned (getr regs ra) mod 8 = 0)%Z ->
  rdn segs mem (getr regs ra) 8%nat = Some bs -> bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.store_ok segs mem (getr regs ra) 8%nat = true ->
  branch_taken c (getr (regupd regs rd v) b1) (getr (regupd regs rd v) b2) = false ->
  msteps segs (mkst regs p0 mem rom)
    (mkst (regupd (regupd regs rd v) rt (Z_to_bv 64 0)) p4
          (wbytes mem (getr regs ra) (word_to_le_bytes 8 (getr (regupd regs rd v) rn))) rom).
Proof using.
  intros segs regs p0 p1 p2 p3 p4 mem rom w0 w1 w2 w3 aq0 rl0 aq2 rl2 rd ra rt rn b1 b2 c imm1 imm3 bs v
         Hf0 He0 Hd0 Hf1 He1 Hd1 Hf2 He2 Hd2 Hf3 He3 Hd3 P1 P2 P3 P4 Hrd Hrt Hra Hal Hread Hv Hok Hcmp.
  pose proof (getr_other regs rd v ra Hra) as Ha.
  eapply mst_step; [reflexivity | eapply step_lr_d; [exact Hf0 | exact He0 | exact Hd0 | exact Hal | exact Hread | exact Hv] | ].
  rewrite (bv_eqb_neq rd 0 Hrd), P1.
  eapply mst_step; [reflexivity | eapply step_branch_ft_r; [exact Hf1 | exact He1 | exact Hd1 | exact Hcmp] | ].
  rewrite P2.
  eapply mst_step; [reflexivity | eapply step_sc_d_ok;
    [exact Hf2 | exact He2 | exact Hd2 | rewrite Ha; exact Hal | rewrite Ha; reflexivity | rewrite Ha; exact Hok] | ].
  rewrite (bv_eqb_neq rt 0 Hrt), P3, Ha.
  eapply mst_step; [reflexivity | eapply step_bne_ft; [exact Hf3 | exact He3 | exact Hd3 | ] | ].
  { rewrite (getr_same _ rt _ Hrt). (lazymatch goal with |- ?G => let G' := eval unfold getr in G in change_no_check G' end). rewrite bv_eqb_refl. apply c_eq_zero. }
  rewrite P4. wd_refl.
Qed.

(* [comment removed for export] *)
Lemma cas_w_run : forall segs regs (p0 p1 p2 p3 p4 : word) mem rom w0 w1 w2 w3 aq0 rl0 aq2 rl2
    (rd ra rt rn b1 b2 : reg) c (imm1 imm3 : bv 13) bs v,
  fetch_word segs p0 = Some w0 -> is_ecall w0 = false -> decode_any w0 = Some (Lr AW aq0 rl0 rd ra, 4%Z) ->
  fetch_word segs p1 = Some w1 -> is_ecall w1 = false -> decode_any w1 = Some (Branch c b1 b2 imm1, 4%Z) ->
  fetch_word segs p2 = Some w2 -> is_ecall w2 = false -> decode_any w2 = Some (Sc AW aq2 rl2 rt ra rn, 4%Z) ->
  fetch_word segs p3 = Some w3 -> is_ecall w3 = false -> decode_any w3 = Some (Branch BC_NE rt 0 imm3, 4%Z) ->
  v_addi p0 4 = p1 -> v_addi p1 4 = p2 -> v_addi p2 4 = p3 -> v_addi p3 4 = p4 ->
  rd <> 0 -> rt <> 0 -> ra <> rd ->
  (bv_unsigned (getr regs ra) mod 4 = 0)%Z ->
  rdn segs mem (getr regs ra) 4%nat = Some bs -> bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.store_ok segs mem (getr regs ra) 4%nat = true ->
  branch_taken c (getr (regupd regs rd (v_lw v)) b1) (getr (regupd regs rd (v_lw v)) b2) = false ->
  msteps segs (mkst regs p0 mem rom)
    (mkst (regupd (regupd regs rd (v_lw v)) rt (Z_to_bv 64 0)) p4
          (wbytes mem (getr regs ra) (word_to_le_bytes 4 (getr (regupd regs rd (v_lw v)) rn))) rom).
Proof using.
  intros segs regs p0 p1 p2 p3 p4 mem rom w0 w1 w2 w3 aq0 rl0 aq2 rl2 rd ra rt rn b1 b2 c imm1 imm3 bs v
         Hf0 He0 Hd0 Hf1 He1 Hd1 Hf2 He2 Hd2 Hf3 He3 Hd3 P1 P2 P3 P4 Hrd Hrt Hra Hal Hread Hv Hok Hcmp.
  pose proof (getr_other regs rd (v_lw v) ra Hra) as Ha.
  eapply mst_step; [reflexivity | eapply step_lr_w; [exact Hf0 | exact He0 | exact Hd0 | exact Hal | exact Hread | exact Hv] | ].
  rewrite (bv_eqb_neq rd 0 Hrd), P1.
  eapply mst_step; [reflexivity | eapply step_branch_ft_r; [exact Hf1 | exact He1 | exact Hd1 | exact Hcmp] | ].
  rewrite P2.
  eapply mst_step; [reflexivity | eapply step_sc_w_ok;
    [exact Hf2 | exact He2 | exact Hd2 | rewrite Ha; exact Hal | rewrite Ha; reflexivity | rewrite Ha; exact Hok] | ].
  rewrite (bv_eqb_neq rt 0 Hrt), P3, Ha.
  eapply mst_step; [reflexivity | eapply step_bne_ft; [exact Hf3 | exact He3 | exact Hd3 | ] | ].
  { rewrite (getr_same _ rt _ Hrt). (lazymatch goal with |- ?G => let G' := eval unfold getr in G in change_no_check G' end). rewrite bv_eqb_refl. apply c_eq_zero. }
  rewrite P4. wd_refl.
Qed.
End FPGen2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition xchg_merge (old new mask : word) : word := v_xor old (v_and (v_xor old new) mask).

(* [comment removed for export] *)
Section Bytes.
Lemma testbit_v_lw_low : forall (v : word) p, (0 <= p < 32)%Z ->
  Z.testbit (bv_unsigned (v_lw v)) p = Z.testbit (bv_unsigned v) p.
Proof using.
  intros v p Hp. (lazymatch goal with |- ?G => let G' := eval unfold v_lw in G in change_no_check G' end). rewrite Z_to_bv_unsigned, bv_wrap_spec_low by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia).
  rewrite bv_swrap_spec by lia. change (Z.of_N 32 - 1)%Z with 31%Z.
  destruct (Z.lt_ge_cases p 31) as [Hl|Hg].
  - rewrite (bool_decide_eq_true_2 _ Hl). reflexivity.
  - rewrite bool_decide_eq_false_2 by lia. replace p with 31%Z by lia. reflexivity.
Qed.

Lemma testbit_le_cons_low : forall (b : byte) bs p, (0 <= p < 8)%Z ->
  Z.testbit (bytes_le_to_Z (b :: bs)) p = Z.testbit (bv_unsigned b) p.
Proof using.
  intros b bs p Hp. (lazymatch goal with |- ?G => let G' := eval cbn [bytes_le_to_Z] in G in change_no_check G' end). rewrite Z.lor_spec, Z.shiftl_spec_low by lia. apply orb_false_r.
Qed.

Lemma testbit_le_cons_high : forall (b : byte) bs p, (8 <= p)%Z ->
  Z.testbit (bytes_le_to_Z (b :: bs)) p = Z.testbit (bytes_le_to_Z bs) (p - 8).
Proof using.
  intros b bs p Hp. (lazymatch goal with |- ?G => let G' := eval cbn [bytes_le_to_Z] in G in change_no_check G' end). rewrite Z.lor_spec, Z.shiftl_spec_high by lia.
  rewrite (Z_testbit_high 8 (bv_unsigned b) p); [reflexivity | lia | apply u8_range | lia].
Qed.

Lemma byte_eq_bits : forall z (c : byte),
  (forall j, (0 <= j < 8)%Z -> Z.testbit z j = Z.testbit (bv_unsigned c) j) -> Z_to_bv 8 z = c.
Proof using.
  intros z c H. apply bv_eq. rewrite Z_to_bv_unsigned. apply Z.bits_inj'. intros n Hn.
  destruct (Z.lt_ge_cases n 8) as [Hl|Hg].
  - rewrite bv_wrap_spec_low by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia). apply H; lia.
  - rewrite bv_wrap_spec_high by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia). symmetry.
    apply (Z_testbit_high 8); [lia | apply u8_range | lia].
Qed.

Lemma testbit_255_shl : forall k p, (0 <= k)%Z -> (0 <= p)%Z ->
  Z.testbit (255 * 2 ^ k) p = ((k <=? p) && (p <? k + 8))%Z.
Proof using.
  intros k p Hk Hp. change 255%Z with (Z.ones 8).
  destruct (Z.lt_ge_cases p k) as [Hl|Hg].
  - rewrite Z.mul_pow2_bits_low by lia. symmetry. apply andb_false_intro1. apply Z.leb_gt. lia.
  - rewrite Z.mul_pow2_bits by lia.
    destruct (Z.lt_ge_cases (p - k) 8) as [H8|H8].
    + rewrite Z.ones_spec_low by lia. symmetry. apply andb_true_intro. split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia].
    + rewrite Z.ones_spec_high by lia. symmetry. apply andb_false_intro2. apply Z.ltb_ge. lia.
Qed.

Lemma testbit_shl_val : forall b k p, (0 <= k)%Z -> (0 <= p)%Z ->
  Z.testbit (b * 2 ^ k) p = if (k <=? p)%Z then Z.testbit b (p - k) else false.
Proof using.
  intros b k p Hk Hp. destruct (Z.lt_ge_cases p k) as [Hl|Hg].
  - rewrite Z.mul_pow2_bits_low by lia. rewrite (proj2 (Z.leb_gt _ _) Hl). reflexivity.
  - rewrite Z.mul_pow2_bits by lia. rewrite (proj2 (Z.leb_le _ _) Hg). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma xchg_merge_bit_in : forall (v new mask : word) K b p,
  (0 <= K)%Z -> (K + 8 <= 32)%Z ->
  bv_unsigned mask = (255 * 2 ^ K)%Z -> bv_unsigned new = (b * 2 ^ K)%Z ->
  (K <= p < K + 8)%Z ->
  Z.testbit (bv_unsigned (xchg_merge (v_lw v) new mask)) p = Z.testbit b (p - K).
Proof using.
  intros v new mask K b p HK HK8 HM HN Hp.
  (lazymatch goal with |- ?G => let G' := eval unfold xchg_merge, v_xor, v_and in G in change_no_check G' end). rewrite !Z_to_bv_unsigned.
  rewrite bv_wrap_spec_low, Z.lxor_spec, bv_wrap_spec_low, Z.land_spec, bv_wrap_spec_low, Z.lxor_spec by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia).
  rewrite HM, HN, testbit_255_shl, testbit_shl_val by lia.
  replace (K <=? p)%Z with true by (symmetry; apply Z.leb_le; lia).
  replace (p <? K + 8)%Z with true by (symmetry; apply Z.ltb_lt; lia). (lazymatch goal with |- ?G => let G' := eval cbn [andb] in G in change_no_check G' end).
  rewrite andb_true_r. destruct (Z.testbit (bv_unsigned (v_lw v)) p), (Z.testbit b (p - K)); reflexivity.
Qed.

Lemma xchg_merge_bit_out : forall (v new mask : word) K b p,
  (0 <= K)%Z -> (K + 8 <= 32)%Z ->
  bv_unsigned mask = (255 * 2 ^ K)%Z -> bv_unsigned new = (b * 2 ^ K)%Z ->
  (0 <= p < 32)%Z -> (p < K \/ K + 8 <= p)%Z ->
  Z.testbit (bv_unsigned (xchg_merge (v_lw v) new mask)) p = Z.testbit (bv_unsigned v) p.
Proof using.
  intros v new mask K b p HK HK8 HM HN Hp Hout.
  (lazymatch goal with |- ?G => let G' := eval unfold xchg_merge, v_xor, v_and in G in change_no_check G' end). rewrite !Z_to_bv_unsigned.
  rewrite bv_wrap_spec_low, Z.lxor_spec, bv_wrap_spec_low, Z.land_spec, bv_wrap_spec_low, Z.lxor_spec by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia).
  rewrite HM, testbit_255_shl by lia.
  replace ((K <=? p) && (p <? K + 8))%Z with false.
  2:{ symmetry. destruct Hout as [Hl|Hg]; [apply andb_false_intro1; apply Z.leb_gt; lia | apply andb_false_intro2; apply Z.ltb_ge; lia]. }
  rewrite andb_false_r, Bool.xorb_false_r. apply testbit_v_lw_low. lia.
Qed.

(* [comment removed for export] *)
Lemma xchg_merge_bytes : forall (b0 b1 b2 b3 : byte) (v new mask : word) (k : nat) (b : Z),
  bytes_le_to_Z [b0; b1; b2; b3] = bv_unsigned v ->
  (k < 4)%nat -> (0 <= b < 256)%Z ->
  bv_unsigned mask = (255 * 2 ^ (8 * Z.of_nat k))%Z ->
  bv_unsigned new = (b * 2 ^ (8 * Z.of_nat k))%Z ->
  word_to_le_bytes 4 (xchg_merge (v_lw v) new mask)
  = firstn k [b0; b1; b2; b3] ++ Z_to_bv 8 b :: skipn (S k) [b0; b1; b2; b3].
Proof using.
  intros b0 b1 b2 b3 v new mask k b Hv Hk Hb HM HN.
  assert (HIN := fun p => xchg_merge_bit_in v new mask (8 * Z.of_nat k) b p ltac:(lia) ltac:(lia) HM HN).
  assert (HOUT := fun p => xchg_merge_bit_out v new mask (8 * Z.of_nat k) b p ltac:(lia) ltac:(lia) HM HN).
  (lazymatch goal with |- ?G => let G' := eval unfold word_to_le_bytes in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [Z_to_le_bytes] in G in change_no_check G' end).
  destruct k as [|[|[|[|k]]]]; [ | | | | lia]; cbn [firstn skipn app Z.of_nat Z.mul Pos.mul Pos.of_succ_nat Pos.succ] in *;
  repeat match goal with |- (_ :: _ = _ :: _) => f_equal end; try reflexivity;
  apply byte_eq_bits; intros j Hj; rewrite ?Z.shiftr_spec by lia;
  first [ rewrite HIN by lia; rewrite Z_to_bv_unsigned, bv_wrap_spec_low by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia); f_equal; lia
        | rewrite HOUT by lia; rewrite <- Hv;
          repeat (rewrite testbit_le_cons_high by lia); rewrite testbit_le_cons_low by lia; f_equal; lia ].
Qed.

(* [comment removed for export] *)
Lemma and_mask_byte : forall (bs : list byte) (v mask : word) (k : nat),
  length bs = 4%nat -> bytes_le_to_Z bs = bv_unsigned v -> (k < 4)%nat ->
  bv_unsigned mask = (255 * 2 ^ (8 * Z.of_nat k))%Z ->
  v_and (v_lw v) mask = Z_to_bv 64 (bv_unsigned (nth k bs (Z_to_bv 8 0)) * 2 ^ (8 * Z.of_nat k)).
Proof using.
  intros bs v mask k Hlen Hv Hk HM.
  destruct bs as [|b0 [|b1 [|b2 [|b3 [|]]]]]; try discriminate.
  apply bv_eq. (lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end). rewrite !Z_to_bv_unsigned. apply Z.bits_inj'. intros p Hp.
  destruct (Z.lt_ge_cases p 64) as [Hl|Hg];
    [ rewrite !bv_wrap_spec_low by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) | rewrite !bv_wrap_spec_high by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia); reflexivity ].
  rewrite Z.land_spec, HM, testbit_255_shl, testbit_shl_val by lia.
  destruct (Z.lt_ge_cases p (8 * Z.of_nat k)) as [H1|H1].
  { replace (8 * Z.of_nat k <=? p)%Z with false by (symmetry; apply Z.leb_gt; lia). apply andb_false_r. }
  replace (8 * Z.of_nat k <=? p)%Z with true by (symmetry; apply Z.leb_le; lia).
  destruct (Z.lt_ge_cases p (8 * Z.of_nat k + 8)) as [H2|H2].
  2:{ replace (p <? 8 * Z.of_nat k + 8)%Z with false by (symmetry; apply Z.ltb_ge; lia).
      rewrite andb_false_r. symmetry. apply (Z_testbit_high 8); [lia | apply u8_range | lia]. }
  replace (p <? 8 * Z.of_nat k + 8)%Z with true by (symmetry; apply Z.ltb_lt; lia).
  rewrite andb_true_r, testbit_v_lw_low, <- Hv by lia.
  destruct k as [|[|[|[|k]]]]; [ | | | | lia]; cbn [nth Z.of_nat Z.mul Pos.mul Pos.of_succ_nat Pos.succ] in *;
  repeat (rewrite testbit_le_cons_high by lia); rewrite testbit_le_cons_low by lia; f_equal; lia.
Qed.
End Bytes.

Section FPGen3.
Context {fx : FPState}.

(* [comment removed for export] *)
Lemma tset_tset_same' {A} : forall (p : positive) (x y : A) t, tset p x (tset p y t) = tset p x t.
Proof using.
  induction p as [p IH|p IH|]; intros x y [|l o r]; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); try reflexivity; rewrite IH; reflexivity.
Qed.
Lemma regupd_collapse : forall regs (r : reg) x v, regupd (regupd regs r x) r v = regupd regs r v.
Proof using. intros regs r x v. (lazymatch goal with |- ?G => let G' := eval unfold regupd, bvmap_set in G in change_no_check G' end). apply tset_tset_same'. Qed.

(* [comment removed for export] *)
Lemma xchgm_run : forall segs regs (p0 p1 p2 p3 p4 p5 p6 p7 : word) mem rom w0 w1 w2 w3 w4 w5 w6
    aq0 rl0 aq5 rl5 (rd ra rt rn rm : reg) (imm6 : bv 13) bs v,
  fetch_word segs p0 = Some w0 -> is_ecall w0 = false -> decode_any w0 = Some (Lr AW aq0 rl0 rd ra, 4%Z) ->
  fetch_word segs p1 = Some w1 -> is_ecall w1 = false -> decode_any w1 = Some (OpImm ALU_ADD rt rn 0, 4%Z) ->
  fetch_word segs p2 = Some w2 -> is_ecall w2 = false -> decode_any w2 = Some (Op ALU_XOR rt rd rt, 4%Z) ->
  fetch_word segs p3 = Some w3 -> is_ecall w3 = false -> decode_any w3 = Some (Op ALU_AND rt rt rm, 4%Z) ->
  fetch_word segs p4 = Some w4 -> is_ecall w4 = false -> decode_any w4 = Some (Op ALU_XOR rt rd rt, 4%Z) ->
  fetch_word segs p5 = Some w5 -> is_ecall w5 = false -> decode_any w5 = Some (Sc AW aq5 rl5 rt ra rt, 4%Z) ->
  fetch_word segs p6 = Some w6 -> is_ecall w6 = false -> decode_any w6 = Some (Branch BC_NE rt 0 imm6, 4%Z) ->
  v_addi p0 4 = p1 -> v_addi p1 4 = p2 -> v_addi p2 4 = p3 -> v_addi p3 4 = p4 ->
  v_addi p4 4 = p5 -> v_addi p5 4 = p6 -> v_addi p6 4 = p7 ->
  rd <> 0 -> rt <> 0 -> rt <> rd -> ra <> rd -> ra <> rt -> rn <> rd -> rm <> rd -> rm <> rt ->
  (bv_unsigned (getr regs ra) mod 4 = 0)%Z ->
  rdn segs mem (getr regs ra) 4%nat = Some bs -> bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.store_ok segs mem (getr regs ra) 4%nat = true ->
  msteps segs (mkst regs p0 mem rom)
    (mkst (regupd (regupd regs rd (v_lw v)) rt (Z_to_bv 64 0)) p7
          (wbytes mem (getr regs ra)
             (word_to_le_bytes 4 (xchg_merge (v_lw v) (getr regs rn) (getr regs rm)))) rom).
Proof using.
  intros segs regs p0 p1 p2 p3 p4 p5 p6 p7 mem rom w0 w1 w2 w3 w4 w5 w6 aq0 rl0 aq5 rl5 rd ra rt rn rm imm6 bs v
         Hf0 He0 Hd0 Hf1 He1 Hd1 Hf2 He2 Hd2 Hf3 He3 Hd3 Hf4 He4 Hd4 Hf5 He5 Hd5 Hf6 He6 Hd6
         P1 P2 P3 P4 P5 P6 P7 Hrd Hrt Htd Had Hat Hnd Hmd Hmt Hal Hread Hv Hok.
  eapply mst_step; [reflexivity | eapply step_lr_w; [exact Hf0 | exact He0 | exact Hd0 | exact Hal | exact Hread | exact Hv] | ].
  rewrite (bv_eqb_neq rd 0 Hrd), P1.
  eapply mst_step; [reflexivity | eapply step_opimm_r; [exact Hf1 | exact He1 | exact Hd1] | ].
  rewrite (bv_eqb_neq rt 0 Hrt), P2, alu_addi, (getr_other _ rd _ rn Hnd).
  change (bv_signed (0 : bv 12)) with 0%Z. rewrite v_addi_0.
  eapply mst_step; [reflexivity | eapply step_op_r; [exact Hf2 | exact He2 | exact Hd2] | ].
  rewrite (bv_eqb_neq rt 0 Hrt), P3, alu_xor, (getr_other _ rt _ rd (not_eq_sym Htd)), (getr_same _ rd _ Hrd),
          (getr_same _ rt _ Hrt), regupd_collapse.
  eapply mst_step; [reflexivity | eapply step_op_r; [exact Hf3 | exact He3 | exact Hd3] | ].
  rewrite (bv_eqb_neq rt 0 Hrt), P4, alu_and, (getr_same _ rt _ Hrt), (getr_other _ rt _ rm Hmt),
          (getr_other _ rd _ rm Hmd), regupd_collapse.
  eapply mst_step; [reflexivity | eapply step_op_r; [exact Hf4 | exact He4 | exact Hd4] | ].
  rewrite (bv_eqb_neq rt 0 Hrt), P5, alu_xor, (getr_other _ rt _ rd (not_eq_sym Htd)), (getr_same _ rd _ Hrd),
          (getr_same _ rt _ Hrt), regupd_collapse.
  eapply mst_step; [reflexivity | eapply step_sc_w_ok; [exact Hf5 | exact He5 | exact Hd5 | | | ] | ];
    [ rewrite (getr_other _ rt _ ra Hat), (getr_other _ rd _ ra Had); first [exact Hal | reflexivity | exact Hok] .. | ].
  rewrite (bv_eqb_neq rt 0 Hrt), P6, (getr_other _ rt _ ra Hat), (getr_other _ rd _ ra Had),
          (getr_same _ rt _ Hrt), regupd_collapse.
  eapply mst_step; [reflexivity | eapply step_bne_ft; [exact Hf6 | exact He6 | exact Hd6 | ] | ].
  { rewrite (getr_same _ rt _ Hrt). (lazymatch goal with |- ?G => let G' := eval unfold getr in G in change_no_check G' end). rewrite bv_eqb_refl. apply c_eq_zero. }
  rewrite P7. wd_refl.
Qed.

(* [comment removed for export] *)
Lemma casm_run : forall segs regs (p0 p1 p2 p3 p4 p5 p6 p7 p8 : word) mem rom w0 w1 w2 w3 w4 w5 w6 w7
    aq0 rl0 aq6 rl6 (rd ra rt rn rm re : reg) (imm2 imm7 : bv 13) bs v,
  fetch_word segs p0 = Some w0 -> is_ecall w0 = false -> decode_any w0 = Some (Lr AW aq0 rl0 rd ra, 4%Z) ->
  fetch_word segs p1 = Some w1 -> is_ecall w1 = false -> decode_any w1 = Some (Op ALU_AND rt rd rm, 4%Z) ->
  fetch_word segs p2 = Some w2 -> is_ecall w2 = false -> decode_any w2 = Some (Branch BC_NE rt re imm2, 4%Z) ->
  fetch_word segs p3 = Some w3 -> is_ecall w3 = false -> decode_any w3 = Some (Op ALU_XOR rt rd rn, 4%Z) ->
  fetch_word segs p4 = Some w4 -> is_ecall w4 = false -> decode_any w4 = Some (Op ALU_AND rt rt rm, 4%Z) ->
  fetch_word segs p5 = Some w5 -> is_ecall w5 = false -> decode_any w5 = Some (Op ALU_XOR rt rd rt, 4%Z) ->
  fetch_word segs p6 = Some w6 -> is_ecall w6 = false -> decode_any w6 = Some (Sc AW aq6 rl6 rt ra rt, 4%Z) ->
  fetch_word segs p7 = Some w7 -> is_ecall w7 = false -> decode_any w7 = Some (Branch BC_NE rt 0 imm7, 4%Z) ->
  v_addi p0 4 = p1 -> v_addi p1 4 = p2 -> v_addi p2 4 = p3 -> v_addi p3 4 = p4 ->
  v_addi p4 4 = p5 -> v_addi p5 4 = p6 -> v_addi p6 4 = p7 -> v_addi p7 4 = p8 ->
  rd <> 0 -> rt <> 0 -> rt <> rd -> ra <> rd -> ra <> rt -> rn <> rd -> rn <> rt -> rm <> rd -> rm <> rt ->
  re <> rd -> re <> rt ->
  (bv_unsigned (getr regs ra) mod 4 = 0)%Z ->
  rdn segs mem (getr regs ra) 4%nat = Some bs -> bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.store_ok segs mem (getr regs ra) 4%nat = true ->
  v_and (v_lw v) (getr regs rm) = getr regs re ->
  msteps segs (mkst regs p0 mem rom)
    (mkst (regupd (regupd regs rd (v_lw v)) rt (Z_to_bv 64 0)) p8
          (wbytes mem (getr regs ra)
             (word_to_le_bytes 4 (xchg_merge (v_lw v) (getr regs rn) (getr regs rm)))) rom).
Proof using.
  intros segs regs p0 p1 p2 p3 p4 p5 p6 p7 p8 mem rom w0 w1 w2 w3 w4 w5 w6 w7 aq0 rl0 aq6 rl6 rd ra rt rn rm re imm2 imm7 bs v
         Hf0 He0 Hd0 Hf1 He1 Hd1 Hf2 He2 Hd2 Hf3 He3 Hd3 Hf4 He4 Hd4 Hf5 He5 Hd5 Hf6 He6 Hd6 Hf7 He7 Hd7
         P1 P2 P3 P4 P5 P6 P7 P8 Hrd Hrt Htd Had Hat Hnd Hnt Hmd Hmt Hed Het Hal Hread Hv Hok Hexp.
  eapply mst_step; [reflexivity | eapply step_lr_w; [exact Hf0 | exact He0 | exact Hd0 | exact Hal | exact Hread | exact Hv] | ].
  rewrite (bv_eqb_neq rd 0 Hrd), P1.
  eapply mst_step; [reflexivity | eapply step_op_r; [exact Hf1 | exact He1 | exact Hd1] | ].
  rewrite (bv_eqb_neq rt 0 Hrt), P2, alu_and, (getr_same _ rd _ Hrd), (getr_other _ rd _ rm Hmd), Hexp.
  eapply mst_step; [reflexivity | eapply step_bne_ft_r; [exact Hf2 | exact He2 | exact Hd2 | ] | ].
  { rewrite (getr_same _ rt _ Hrt), (getr_other _ rt _ re Het), (getr_other _ rd _ re Hed).
    (lazymatch goal with |- ?G => let G' := eval unfold c_eq in G in change_no_check G' end). apply Z.eqb_refl. }
  rewrite P3.
  eapply mst_step; [reflexivity | eapply step_op_r; [exact Hf3 | exact He3 | exact Hd3] | ].
  rewrite (bv_eqb_neq rt 0 Hrt), P4, alu_xor, (getr_other _ rt _ rd (not_eq_sym Htd)), (getr_same _ rd _ Hrd),
          (getr_other _ rt _ rn Hnt), (getr_other _ rd _ rn Hnd), regupd_collapse.
  eapply mst_step; [reflexivity | eapply step_op_r; [exact Hf4 | exact He4 | exact Hd4] | ].
  rewrite (bv_eqb_neq rt 0 Hrt), P5, alu_and, (getr_same _ rt _ Hrt), (getr_other _ rt _ rm Hmt),
          (getr_other _ rd _ rm Hmd), regupd_collapse.
  eapply mst_step; [reflexivity | eapply step_op_r; [exact Hf5 | exact He5 | exact Hd5] | ].
  rewrite (bv_eqb_neq rt 0 Hrt), P6, alu_xor, (getr_other _ rt _ rd (not_eq_sym Htd)), (getr_same _ rd _ Hrd),
          (getr_same _ rt _ Hrt), regupd_collapse.
  eapply mst_step; [reflexivity | eapply step_sc_w_ok; [exact Hf6 | exact He6 | exact Hd6 | | | ] | ];
    [ rewrite (getr_other _ rt _ ra Hat), (getr_other _ rd _ ra Had); first [exact Hal | reflexivity | exact Hok] .. | ].
  rewrite (bv_eqb_neq rt 0 Hrt), P7, (getr_other _ rt _ ra Hat), (getr_other _ rd _ ra Had),
          (getr_same _ rt _ Hrt), regupd_collapse.
  eapply mst_step; [reflexivity | eapply step_bne_ft; [exact Hf7 | exact He7 | exact Hd7 | ] | ].
  { rewrite (getr_same _ rt _ Hrt). (lazymatch goal with |- ?G => let G' := eval unfold getr in G in change_no_check G' end). rewrite bv_eqb_refl. apply c_eq_zero. }
  rewrite P8. wd_refl.
Qed.

(* [comment removed for export] *)
Lemma xchg_byte_run : forall segs regs (p0 p1 p2 p3 p4 p5 p6 p7 : word) mem rom w0 w1 w2 w3 w4 w5 w6
    aq0 rl0 aq5 rl5 (rd ra rt rn rm : reg) (imm6 : bv 13) bs v (k : nat) (b : Z),
  fetch_word segs p0 = Some w0 -> is_ecall w0 = false -> decode_any w0 = Some (Lr AW aq0 rl0 rd ra, 4%Z) ->
  fetch_word segs p1 = Some w1 -> is_ecall w1 = false -> decode_any w1 = Some (OpImm ALU_ADD rt rn 0, 4%Z) ->
  fetch_word segs p2 = Some w2 -> is_ecall w2 = false -> decode_any w2 = Some (Op ALU_XOR rt rd rt, 4%Z) ->
  fetch_word segs p3 = Some w3 -> is_ecall w3 = false -> decode_any w3 = Some (Op ALU_AND rt rt rm, 4%Z) ->
  fetch_word segs p4 = Some w4 -> is_ecall w4 = false -> decode_any w4 = Some (Op ALU_XOR rt rd rt, 4%Z) ->
  fetch_word segs p5 = Some w5 -> is_ecall w5 = false -> decode_any w5 = Some (Sc AW aq5 rl5 rt ra rt, 4%Z) ->
  fetch_word segs p6 = Some w6 -> is_ecall w6 = false -> decode_any w6 = Some (Branch BC_NE rt 0 imm6, 4%Z) ->
  v_addi p0 4 = p1 -> v_addi p1 4 = p2 -> v_addi p2 4 = p3 -> v_addi p3 4 = p4 ->
  v_addi p4 4 = p5 -> v_addi p5 4 = p6 -> v_addi p6 4 = p7 ->
  rd <> 0 -> rt <> 0 -> rt <> rd -> ra <> rd -> ra <> rt -> rn <> rd -> rm <> rd -> rm <> rt ->
  (bv_unsigned (getr regs ra) mod 4 = 0)%Z ->
  rdn segs mem (getr regs ra) 4%nat = Some bs -> bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.store_ok segs mem (getr regs ra) 4%nat = true ->
  (k < 4)%nat -> (0 <= b < 256)%Z ->
  bv_unsigned (getr regs rm) = (255 * 2 ^ (8 * Z.of_nat k))%Z ->
  bv_unsigned (getr regs rn) = (b * 2 ^ (8 * Z.of_nat k))%Z ->
  msteps segs (mkst regs p0 mem rom)
    (mkst (regupd (regupd regs rd (v_lw v)) rt (Z_to_bv 64 0)) p7
          (wbytes mem (getr regs ra) (firstn k bs ++ Z_to_bv 8 b :: skipn (S k) bs)) rom).
Proof using.
  intros segs regs p0 p1 p2 p3 p4 p5 p6 p7 mem rom w0 w1 w2 w3 w4 w5 w6 aq0 rl0 aq5 rl5 rd ra rt rn rm imm6 bs v k b
         Hf0 He0 Hd0 Hf1 He1 Hd1 Hf2 He2 Hd2 Hf3 He3 Hd3 Hf4 He4 Hd4 Hf5 He5 Hd5 Hf6 He6 Hd6
         P1 P2 P3 P4 P5 P6 P7 Hrd Hrt Htd Had Hat Hnd Hmd Hmt Hal Hread Hv Hok Hk Hb HM HN.
  pose proof (rdn_length _ _ _ _ _ Hread) as Hlen.
  destruct bs as [|b0 [|b1 [|b2 [|b3 [|]]]]]; try discriminate.
  rewrite <- (xchg_merge_bytes b0 b1 b2 b3 v (getr regs rn) (getr regs rm) k b Hv Hk Hb HM HN).
  eapply (xchgm_run segs regs p0 p1 p2 p3 p4 p5 p6 p7); eassumption.
Qed.

(* [comment removed for export] *)
Lemma cas_byte_run : forall segs regs (p0 p1 p2 p3 p4 p5 p6 p7 p8 : word) mem rom w0 w1 w2 w3 w4 w5 w6 w7
    aq0 rl0 aq6 rl6 (rd ra rt rn rm re : reg) (imm2 imm7 : bv 13) bs v (k : nat) (b : Z),
  fetch_word segs p0 = Some w0 -> is_ecall w0 = false -> decode_any w0 = Some (Lr AW aq0 rl0 rd ra, 4%Z) ->
  fetch_word segs p1 = Some w1 -> is_ecall w1 = false -> decode_any w1 = Some (Op ALU_AND rt rd rm, 4%Z) ->
  fetch_word segs p2 = Some w2 -> is_ecall w2 = false -> decode_any w2 = Some (Branch BC_NE rt re imm2, 4%Z) ->
  fetch_word segs p3 = Some w3 -> is_ecall w3 = false -> decode_any w3 = Some (Op ALU_XOR rt rd rn, 4%Z) ->
  fetch_word segs p4 = Some w4 -> is_ecall w4 = false -> decode_any w4 = Some (Op ALU_AND rt rt rm, 4%Z) ->
  fetch_word segs p5 = Some w5 -> is_ecall w5 = false -> decode_any w5 = Some (Op ALU_XOR rt rd rt, 4%Z) ->
  fetch_word segs p6 = Some w6 -> is_ecall w6 = false -> decode_any w6 = Some (Sc AW aq6 rl6 rt ra rt, 4%Z) ->
  fetch_word segs p7 = Some w7 -> is_ecall w7 = false -> decode_any w7 = Some (Branch BC_NE rt 0 imm7, 4%Z) ->
  v_addi p0 4 = p1 -> v_addi p1 4 = p2 -> v_addi p2 4 = p3 -> v_addi p3 4 = p4 ->
  v_addi p4 4 = p5 -> v_addi p5 4 = p6 -> v_addi p6 4 = p7 -> v_addi p7 4 = p8 ->
  rd <> 0 -> rt <> 0 -> rt <> rd -> ra <> rd -> ra <> rt -> rn <> rd -> rn <> rt -> rm <> rd -> rm <> rt ->
  re <> rd -> re <> rt ->
  (bv_unsigned (getr regs ra) mod 4 = 0)%Z ->
  rdn segs mem (getr regs ra) 4%nat = Some bs -> bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.store_ok segs mem (getr regs ra) 4%nat = true ->
  (k < 4)%nat -> (0 <= b < 256)%Z ->
  bv_unsigned (getr regs rm) = (255 * 2 ^ (8 * Z.of_nat k))%Z ->
  bv_unsigned (getr regs rn) = (b * 2 ^ (8 * Z.of_nat k))%Z ->
  getr regs re = Z_to_bv 64 (bv_unsigned (nth k bs (Z_to_bv 8 0)) * 2 ^ (8 * Z.of_nat k)) ->
  msteps segs (mkst regs p0 mem rom)
    (mkst (regupd (regupd regs rd (v_lw v)) rt (Z_to_bv 64 0)) p8
          (wbytes mem (getr regs ra) (firstn k bs ++ Z_to_bv 8 b :: skipn (S k) bs)) rom).
Proof using.
  intros segs regs p0 p1 p2 p3 p4 p5 p6 p7 p8 mem rom w0 w1 w2 w3 w4 w5 w6 w7 aq0 rl0 aq6 rl6 rd ra rt rn rm re imm2 imm7
         bs v k b
         Hf0 He0 Hd0 Hf1 He1 Hd1 Hf2 He2 Hd2 Hf3 He3 Hd3 Hf4 He4 Hd4 Hf5 He5 Hd5 Hf6 He6 Hd6 Hf7 He7 Hd7
         P1 P2 P3 P4 P5 P6 P7 P8 Hrd Hrt Htd Had Hat Hnd Hnt Hmd Hmt Hed Het Hal Hread Hv Hok Hk Hb HM HN HE.
  pose proof (rdn_length _ _ _ _ _ Hread) as Hlen.
  pose proof (and_mask_byte bs v (getr regs rm) k Hlen Hv Hk HM) as Hexp. rewrite <- HE in Hexp.
  destruct bs as [|b0 [|b1 [|b2 [|b3 [|]]]]]; try discriminate.
  rewrite <- (xchg_merge_bytes b0 b1 b2 b3 v (getr regs rn) (getr regs rm) k b Hv Hk Hb HM HN).
  eapply (casm_run segs regs p0 p1 p2 p3 p4 p5 p6 p7 p8); eassumption.
Qed.
End FPGen3.
End AsRtAtomic.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupAux.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Export OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Export WalkLetEv.   (* [comment removed for export] *)
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma reg_neq_of_eqb : forall a b : reg, bv_eqb a b = false -> a <> b.
Proof. intros a b H E. subst b. rewrite bv_eqb_refl in H. discriminate H. Qed.

Ltac getr_proof X r :=
  lazymatch X with
  | regupd ?Y ?rd ?v =>
      match tt with
      | _ => let chk := match tt with _ => constr_eq rd r end in
             uconstr:(getr_same Y r v (reg_neq_of_eqb r (0%bv) (@eq_refl bool false)))
      | _ => let p := getr_proof Y r in
             uconstr:(eq_trans (getr_other Y rd v r (reg_neq_of_eqb r rd (@eq_refl bool false))) p)
      end
  | _ => uconstr:(@eq_refl word (getr X r))
  end.

(* [comment removed for export] *)
Ltac noncert_clear_all := repeat match goal with H : _ |- _ => clear H end.
(* [comment removed for export] *)
Ltac noncert_goal_has_var := wd_goal_has_var.
Ltac lia ::=
  tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
  else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker]
             | Zify.zify; xlia zchecker ].
Ltac nia ::=
  tryif noncert_goal_has_var then (Zify.zify; xnia zchecker)
  else first [ solve [noncert_clear_all; Zify.zify; xnia zchecker]
             | Zify.zify; xnia zchecker ].

(* [comment removed for export] *)
Ltac gres_walk C r acc :=
  lazymatch C with
  | regupd ?R0 ?rd ?v =>
      match tt with
      | _ => let chk := match tt with _ => constr_eq rd r end in
             constr:(pair (pair (cons (RLP rd v) acc) R0) (Some v))
      | _ => let b := rl_eqb r rd in
             lazymatch b with
             | false => gres_walk R0 r constr:(cons (RLP rd v) acc)
             end
      end
  | _ => constr:(pair (pair acc C) (@None word))
  end.
Ltac gres_lin X r :=
  let res := gres_walk X r constr:(@nil rlp) in
  lazymatch res with
  | pair (pair ?acc ?R0) (Some ?w) =>
      change (getr X r) with (getr (rl_build acc R0) r);
      rewrite (rl_some r acc R0 w (@eq_refl bool false) (@eq_refl (option word) (Some w)))
  | pair (pair ?acc ?R0) None =>
      change (getr X r) with (getr (rl_build acc R0) r);
      rewrite (rl_none r acc R0 (@eq_refl bool false) (@eq_refl (option word) None))
  end.
Ltac gres_getr_old X r := let p := getr_proof X r in let p' := constr:(p) in rewrite p'.

(* [comment removed for export] *)
Ltac gres :=
  repeat match goal with
         | |- context [getr ?X ?r] =>
             first [ lazymatch X with regupd _ _ _ => idtac end;
                     first [ wd_gres_l2 X r | gres_lin X r | gres_getr_old X r ]
                   | wd_isletR X; wd_gres_l2 X r ]
         end;
  match goal with |- context [getr _ 0] => rewrite ?getr_zero | _ => idtac end.

(* [comment removed for export] *)
Fixpoint gres_keys_in (acc : list rlp) (L : list reg) : bool :=
  match acc with
  | nil => true
  | cons (RLP r _) t => existsb (fun y => bv_eqb r y) L && gres_keys_in t L
  end.

Lemma gres_frame_notin : forall (x : reg) (L : list reg) acc R,
  ~ In x L -> gres_keys_in acc L = true -> getr (rl_build acc R) x = getr R x.
Proof.
  intros x L acc; induction acc as [|[r v] t IH]; intros R Hx Hk; cbn [rl_build gres_keys_in] in *; [reflexivity|].
  apply andb_prop in Hk as [Hr Ht]. rewrite (IH _ Hx Ht).
  apply getr_other. intros E; subst x. apply Hx.
  apply existsb_exists in Hr as [y [Hy Eb]]. apply rl_bv_eqb_true_eq in Eb. subst y. exact Hy.
Qed.

Ltac gres_frame_walk C R acc :=
  match tt with
  | _ => let _ := match goal with _ => constr_eq C R end in constr:(acc)
  | _ => lazymatch C with regupd ?C0 ?rd ?v => gres_frame_walk C0 R constr:(cons (RLP rd v) acc) end
  | _ => let _ := match goal with _ => wd_isletR C end in let B := eval unfold C in C in gres_frame_walk B R acc   (* [comment removed for export] *)
  end.
Ltac gres_frame Hx :=
  lazymatch type of Hx with
  | ~ In ?x ?L =>
      lazymatch goal with
      | |- getr ?X x = getr ?R x =>
          let acc := gres_frame_walk X R constr:(@nil rlp) in
          change (getr X x) with (getr (rl_build acc R) x);
          exact (gres_frame_notin x L acc R Hx (@eq_refl bool true))
      end
  end.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPGen1.
Context {fx : FPState}.


Fixpoint code_at (segs : list Segment) (base : word) (off : Z) (ws : list (bv 32)) : Prop :=
  match ws with
  | [] => True
  | w :: ws' => fetch_word segs (at_ base off) = Some w /\ code_at segs base (off + 4)%Z ws'
  end.

(* [comment removed for export] *)
Fixpoint code_at_b (segs : list Segment) (base : word) (off : Z) (ws : list (bv 32)) : bool :=
  match ws with
  | [] => true
  | w :: ws' =>
      match fetch_word segs (at_ base off) with
      | Some w' => Z.eqb (bv_unsigned w') (bv_unsigned w) && code_at_b segs base (off + 4)%Z ws'
      | None => false
      end
  end.

Lemma code_at_b_sound : forall segs base ws off,
  code_at_b segs base off ws = true -> code_at segs base off ws.
Proof using.
  intros segs base ws; induction ws as [|w ws IH]; intros off H; [exact I|].
  cbn [code_at_b] in H. fold code_at_b in H.
  destruct (fetch_word segs (at_ base off)) as [w'|] eqn:E; [|discriminate].
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply bv_eq in H1. subst w'.
  split; [exact E | apply IH; exact H2].
Qed.
End FPGen1.


Ltac code_at_vm := apply code_at_b_sound; vm_compute; reflexivity.

(* [comment removed for export] *)
Ltac code_at_vm_split :=
  (lazymatch goal with |- ?G => let G' := eval cbn [code_at Z.add Pos.add Pos.succ] in G in change_no_check G' end);
  repeat split;
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Section FPGen2.
Context {fx : FPState}.

Lemma code_at_get : forall segs base off ws (i : nat) w,
  code_at segs base off ws -> nth_error ws i = Some w ->
  fetch_word segs (at_ base (off + 4 * Z.of_nat i)%Z) = Some w.
Proof using.
  intros segs base off ws i; revert off ws; induction i as [|i IH]; intros off ws w HC Hn.
  - destruct ws as [|w0 ws']; [discriminate|]. cbn in Hn. injection Hn as ->.
    destruct HC as [HF _]. replace (off + 4 * Z.of_nat 0)%Z with off by lia. exact HF.
  - destruct ws as [|w0 ws']; [discriminate|]. cbn in Hn. destruct HC as [_ HC'].
    replace (off + 4 * Z.of_nat (S i))%Z with ((off + 4) + 4 * Z.of_nat i)%Z by lia.
    exact (IH _ _ _ HC' Hn).
Qed.

(* [comment removed for export] *)
Lemma at_add_0_r : forall (b : word) d, at_ b (d + 0) = at_ b d.
Proof using. intros b d. rewrite Z.add_0_r. reflexivity. Qed.

(* [comment removed for export] *)
End FPGen2.

Ltac zlit_at :=
  repeat match goal with
  | |- context [at_ ?b (?x + ?y)%Z] =>
      is_Z_lit x; is_Z_lit y;
      let z := eval cbv in (x + y)%Z in change (at_ b (x + y)%Z) with (at_ b z)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac rwH :=
  repeat match goal with
         | H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
         end.

(* [comment removed for export] *)
Ltac fold_at_vars :=
  repeat match goal with
         | |- context [v_addi ?b ?e] => is_var b; change (v_addi b e) with (at_ b e)
         end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac unfold_btgt_nc :=
  let G := match goal with |- ?G => G end in
  let G' := eval unfold btgt in G in
  tryif constr_eq G G' then idtac else change G'.
(* [comment removed for export] *)
Ltac vn :=
  gres; rwH; imm_norm; unfold_btgt_nc;
  rewrite ?at_addi; rewrite ?v_addi_0, ?v_add_0_r, ?v_add_0_l;
  fold_at_vars; rewrite ?at_addi; zlit_at; rewrite ?at_add_0_r; vals_lit; wd_setR.
(* [comment removed for export] *)
Ltac gres_old :=
  repeat match goal with
         | |- context [getr ?X ?r] =>
             lazymatch X with regupd _ _ _ => idtac end;
             first [ gres_lin X r | gres_getr_old X r ]
         end;
  match goal with |- context [getr _ 0] => rewrite ?getr_zero | _ => idtac end.
Ltac vn_old :=
  gres_old; rwH; imm_norm; unfold_btgt_nc;
  rewrite ?at_addi; rewrite ?v_addi_0, ?v_add_0_r, ?v_add_0_l;
  fold_at_vars; rewrite ?at_addi; zlit_at; rewrite ?at_add_0_r; vals_lit.
Ltac vn_core :=
  gres; rwH; imm_norm; unfold_btgt_nc;
  rewrite ?at_addi; rewrite ?v_addi_0, ?v_add_0_r, ?v_add_0_l;
  fold_at_vars; rewrite ?at_addi; zlit_at; rewrite ?at_add_0_r; vals_lit.
Ltac vn_dual :=
  let G0 := match goal with |- ?G => G end in
  let G0x := wd_zx G0 in
  vn_core; wd_setR;
  let G1 := match goal with |- ?G => G end in
  let G1x := wd_zx G1 in
  assert_succeeds (
    let H := fresh "wdDual" in
    assert (H : G0x); [ vn_old; lazymatch goal with |- ?G => tryif constr_eq G G1x then idtac else fail 100 "wd_dual: MISMATCH" end | ]).
Ltac pcn := vn.

(* [comment removed for export] *)
Ltac an F D :=
  lazymatch type of D with
  | decode_any _ = Some (Jal _ _, _) => stepj F D; vn
  | _ => stepi F D; vn
  end.

(* [comment removed for export] *)
Ltac av F D v tac := stepiv F D v ltac:(gres; rwH; imm_norm; tac); vn.

(* [comment removed for export] *)
Ltac ab_tk F D tac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Branch BC_EQ _ _ _, _)  => eapply step_beq_tk
    | decode_any _ = Some (Branch BC_NE _ _ _, _)  => eapply step_bne_tk
    | decode_any _ = Some (Branch BC_LT _ _ _, _)  => eapply step_blt_tk
    | decode_any _ = Some (Branch BC_GE _ _ _, _)  => eapply step_bge_tk
    | decode_any _ = Some (Branch BC_LTU _ _ _, _) => eapply step_bltu_tk
    | decode_any _ = Some (Branch BC_GEU _ _ _, _) => eapply step_bgeu_tk
    end;
    [ exact F | reflexivity | exact D | gres; rwH; imm_norm; tac ]
  | step_simpl; vn ].

Ltac ab_ft F D tac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Branch BC_EQ _ _ _, _)  => eapply step_beq_ft
    | decode_any _ = Some (Branch BC_NE _ _ _, _)  => eapply step_bne_ft
    | decode_any _ = Some (Branch BC_LT _ _ _, _)  => eapply step_blt_ft
    | decode_any _ = Some (Branch BC_GE _ _ _, _)  => eapply step_bge_ft
    | decode_any _ = Some (Branch BC_LTU _ _ _, _) => eapply step_bltu_ft
    | decode_any _ = Some (Branch BC_GEU _ _ _, _) => eapply step_bgeu_ft
    end;
    [ exact F | reflexivity | exact D | gres; rwH; imm_norm; tac ]
  | step_simpl; vn ].

(* [comment removed for export] *)
Ltac aret F D k :=
  stepjr F D k ltac:(gres; rwH; reflexivity);
  imm_norm;
  try lazymatch goal with
      | Hk : ret_ok k |- _ => rewrite (Hk : v_jalr k 0 = k)
      end.

(* [comment removed for export] *)
Ltac condz :=
  rwH; (lazymatch goal with |- ?G => let G' := eval unfold at_, c_eq, c_ltu, bv_eqb, bv_ltu in G in change_no_check G' end); imm_norm; unorm;
  first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; wd_ulia.

(* [comment removed for export] *)
Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try reflexivity; try (f_equal; lia).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPGen3.
Context {fx : FPState}.


Lemma v_add_at : forall (a : word) z, (0 <= z < 2 ^ 64)%Z -> v_add a (Z_to_bv 64 z) = at_ a z.
Proof using. intros a z Hz. (lazymatch goal with |- ?G => let G' := eval unfold v_add, at_ in G in change_no_check G' end). rewrite (u_Z2bv z) by lia. reflexivity. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record cpyH (segs : list Segment) (mem0 : word -> option byte) (dst src : word) (n : Z) (bs : list byte) : Prop := CPYH {
  cHn : (0 <= n)%Z;
  cHlen : length bs = Z.to_nat n;
  cHsrc : rdn segs mem0 src (length bs) = Some bs;
  cHdst : store_ok segs mem0 dst (length bs) = true;
  cHdisj : (bv_unsigned dst + n <= bv_unsigned src \/ bv_unsigned src + n <= bv_unsigned dst)%Z;
  cHnws : (bv_unsigned src + n < 2 ^ 64)%Z;
  cHnwd : (bv_unsigned dst + n < 2 ^ 64)%Z }.

Section MEMK.
  Variable segs : list Segment.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable bs : list byte.
  Hypothesis HOK : cpyH segs mem0 dst src n bs.

  Let Hn := cHn _ _ _ _ _ _ HOK.
  Let Hlen := cHlen _ _ _ _ _ _ HOK.
  Let Hsrc := cHsrc _ _ _ _ _ _ HOK.
  Let Hdst := cHdst _ _ _ _ _ _ HOK.
  Let Hdisj := cHdisj _ _ _ _ _ _ HOK.
  Let Hnws := cHnws _ _ _ _ _ _ HOK.
  Let Hnwd := cHnwd _ _ _ _ _ _ HOK.

  (* [comment removed for export] *)
  Definition memk (k : Z) : word -> option byte := wbytes mem0 dst (firstn (Z.to_nat k) bs).
  (* [comment removed for export] *)
  Definition b_ (j : Z) : byte := nth (Z.to_nat j) bs (Z_to_bv 8 0).


  Lemma memk_n : memk n = wbytes mem0 dst bs.
  Proof using Hlen HOK src segs. (lazymatch goal with |- ?G => let G' := eval unfold memk in G in change_no_check G' end). rewrite <- Hlen, firstn_all. reflexivity. Qed.

  Lemma rd_src1 : forall k j,
      (0 <= k <= n)%Z -> (0 <= j)%Z -> (j + 1 <= n)%Z ->
      rdn segs (memk k) (at_ src j) 1 = Some [b_ j].
  Proof using Hnwd Hnws Hdisj Hsrc Hlen HOK.
    intros k j Hk Hj H1. (lazymatch goal with |- ?G => let G' := eval unfold memk, b_ in G in change_no_check G' end).
    pose proof (u64_range src). pose proof (u64_range dst).
    rewrite rdn_wbytes_out.
    - replace (at_ src j) with (at_ src (Z.of_nat (Z.to_nat j))) by (f_equal; lia).
      rewrite (rdn_sub segs mem0 (length bs) src bs (Z.to_nat j) 1 Hsrc) by (rewrite Hlen; lia).
      rewrite sub_nth by (rewrite Hlen; lia). reflexivity.
    - rewrite length_firstn, Hlen, at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia.
    - rewrite at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia.
    - rewrite length_firstn, Hlen. lia.
  Qed.

  Lemma wr_dst : forall k j m,
      (0 <= j)%Z -> (j + Z.of_nat m <= n)%Z ->
      store_ok segs (memk k) (at_ dst j) m = true.
  Proof using Hnwd Hnws Hdst Hlen Hn HOK src.
    intros k j m Hj Hm. (lazymatch goal with |- ?G => let G' := eval unfold memk in G in change_no_check G' end).
    apply (store_ok_at segs mem0 dst (length bs)); try assumption; rewrite ?Hlen; lia.
  Qed.

  Lemma memk_extend1 : forall k,
      (0 <= k)%Z -> (k + 1 <= n)%Z ->
      wbytes (memk k) (at_ dst k) [b_ k] = memk (k + 1).
  Proof using Hlen HOK src segs.
    intros k Hk H1. (lazymatch goal with |- ?G => let G' := eval unfold memk, b_ in G in change_no_check G' end).
    replace (at_ dst k) with (at_ dst (Z.of_nat (Z.to_nat k))) by (f_equal; lia).
    rewrite <- sub_nth by (rewrite Hlen; lia).
    rewrite wbytes_extend' by (rewrite Hlen; lia). f_equal. f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mc_lbu : forall regs pc rom w rd rs (imm : bv 12) k j0 j,
    fetch_word segs pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) ->
    getr regs rs = at_ src j0 -> (j0 + bv_signed imm = j)%Z ->
    (0 <= k <= n)%Z -> (0 <= j)%Z -> (j + 1 <= n)%Z ->
    RiscvSemantics.step segs (mkst regs pc (memk k) rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 (bv_unsigned (b_ j)))) (v_addi pc 4) (memk k) rom).
  Proof using Hnwd Hnws Hdisj Hsrc Hlen HOK.
    intros regs pc rom w rd rs imm k j0 j Hf He Hd Hrs Hj Hk Hj0 Hj1.
    eapply step_lbu; [exact Hf | exact He | exact Hd |].
    rewrite Hrs, at_addi, Hj. apply rd_src1; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mc_sb : forall regs pc rom w rs1 rs2 (imm : bv 12) k k0 (v : word),
    fetch_word segs pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
    getr regs rs1 = at_ dst k0 -> (k0 + bv_signed imm = k)%Z ->
    getr regs rs2 = v -> Z_to_bv 8 (bv_unsigned v) = b_ k ->
    (0 <= k)%Z -> (k + 1 <= n)%Z ->
    RiscvSemantics.step segs (mkst regs pc (memk k) rom) =
    MachineOk (mkst regs (v_addi pc 4) (memk (k + 1)) rom).
  Proof using Hnwd Hnws Hdst Hlen Hn HOK src.
    intros regs pc rom w rs1 rs2 imm k k0 v Hf He Hd Hrs1 Hk Hrs2 Hb Hk0 Hk1.
    rewrite <- (memk_extend1 k) by lia.
    eapply MmapSim.step_sb_at; [exact Hf | exact He | exact Hd | | exact Hrs2 | exact Hb |].
    - rewrite Hrs1, at_addi, Hk. reflexivity.
    - apply wr_dst; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia.
  Qed.

End MEMK.

Lemma sb_val_b : forall bs j, Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (bv_unsigned (b_ bs j)))) = b_ bs j.
Proof using.
  intros bs j. pose proof (u8_range (b_ bs j)). rewrite u_Z2bv by lia. apply Z_to_bv_bv_unsigned.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section MSETK.
  Variable segs : list Segment.
  Variable mem0 : word -> option byte.
  Variable s : word.
  Variable n : Z.
  Variable b : byte.
  Hypothesis Hn : (0 <= n)%Z.
  Hypothesis Hnw : (bv_unsigned s + n < 2 ^ 64)%Z.
  Hypothesis Hok : store_ok segs mem0 s (Z.to_nat n) = true.

  Definition msetk (k : Z) : word -> option byte := wbytes mem0 s (repeat b (Z.to_nat k)).


  Lemma wr_s : forall k j m,
      (0 <= j)%Z -> (j + Z.of_nat m <= n)%Z ->
      store_ok segs (msetk k) (at_ s j) m = true.
  Proof using Hok Hnw Hn.
    intros k j m Hj Hm. (lazymatch goal with |- ?G => let G' := eval unfold msetk in G in change_no_check G' end).
    apply (store_ok_at segs mem0 s (Z.to_nat n)); try assumption; lia.
  Qed.

  Lemma msetk_extend : forall k m,
      (0 <= k)%Z ->
      wbytes (msetk k) (at_ s k) (repeat b m) = msetk (k + Z.of_nat m).
  Proof using.
    intros k m Hk. (lazymatch goal with |- ?G => let G' := eval unfold msetk in G in change_no_check G' end).
    replace (Z.to_nat (k + Z.of_nat m)) with (Z.to_nat k + m)%nat by lia.
    rewrite repeat_app, wbytes_app, repeat_length. f_equal. f_equal. lia.
  Qed.

  Lemma msetk_extend1 : forall k, (0 <= k)%Z -> wbytes (msetk k) (at_ s k) [b] = msetk (k + 1).
  Proof using. intros k Hk. apply (msetk_extend k 1). exact Hk. Qed.
End MSETK.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land_shl_disjoint : forall a b k, (0 <= a)%Z -> (0 <= k)%Z -> (0 <= b < 2 ^ k)%Z ->
  Z.land (a * 2 ^ k) b = 0%Z.
Proof using.
  intros a b k Ha Hk Hb. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i k) as [Hl|Hh].
  - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - rewrite (Z_testbit_high k b i) by lia. apply Bool.andb_false_r.
Qed.

Lemma lor_shl_disjoint : forall a b k, (0 <= a)%Z -> (0 <= k)%Z -> (0 <= b < 2 ^ k)%Z ->
  Z.lor (a * 2 ^ k) b = (a * 2 ^ k + b)%Z.
Proof using.
  intros a b k Ha Hk Hb.
  rewrite <- Z.lxor_lor by (apply land_shl_disjoint; lia).
  symmetry. apply Z.add_nocarry_lxor. apply land_shl_disjoint; lia.
Qed.

Lemma v_slli_mul : forall (x : word) k, (0 <= k)%Z -> v_slli x k = Z_to_bv 64 (bv_unsigned x * 2 ^ k).
Proof using. intros x k Hk. (lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end). rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.

Lemma v_or_shl : forall (x : word) a k, (0 <= a)%Z -> (0 <= k)%Z -> (a * 2 ^ k < 2 ^ 64)%Z ->
  (bv_unsigned x < 2 ^ k)%Z ->
  v_or (Z_to_bv 64 (a * 2 ^ k)) x = Z_to_bv 64 (a * 2 ^ k + bv_unsigned x).
Proof using.
  intros x a k Ha Hk Hak Hx. pose proof (u64_range x). (lazymatch goal with |- ?G => let G' := eval unfold v_or in G in change_no_check G' end).
  pose proof (Z.pow_nonneg 2 k ltac:(lia)).
  rewrite u_Z2bv by nia. rewrite lor_shl_disjoint by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition M8 : Z := 72340172838076673.

Lemma M8_digit : forall c k, (0 <= c < 256)%Z ->
  (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7)%Z ->
  (Z.shiftr (c * M8) (8 * k) mod 256 = c)%Z.
Proof using.
  intros c k Hc Hk. (lazymatch goal with |- ?G => let G' := eval unfold M8 in G in change_no_check G' end). rewrite Z.shiftr_div_pow2 by lia.
  assert (G : forall Mhi Mlo B, (0 < B)%Z -> (Mhi * B + Mlo = 72340172838076673)%Z -> (0 <= Mlo)%Z ->
             (255 * Mlo < B)%Z -> (Mhi mod 256 = 1)%Z ->
             (c * 72340172838076673 / B mod 256 = c)%Z).
  { intros Mhi Mlo B HB HM Hlo Hlt Hm1.
    replace (c * 72340172838076673)%Z with (c * Mhi * B + c * Mlo)%Z by nia.
    rewrite Z.div_add_l by lia. rewrite (Z.div_small (c * Mlo) B) by nia.
    rewrite Z.add_0_r, <- Zmult_mod_idemp_r, Hm1, Z.mul_1_r. apply Z.mod_small. lia. }
  destruct Hk as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]].
  - apply (G 72340172838076673 0 1)%Z; reflexivity || lia.
  - apply (G 282578800148737 1 (2^8))%Z; try reflexivity; lia.
  - apply (G 1103823438081 257 (2^16))%Z; try reflexivity; lia.
  - apply (G 4311810305 65793 (2^24))%Z; try reflexivity; lia.
  - apply (G 16843009 16843009 (2^32))%Z; try reflexivity; lia.
  - apply (G 65793 4311810305 (2^40))%Z; try reflexivity; lia.
  - apply (G 257 1103823438081 (2^48))%Z; try reflexivity; lia.
  - apply (G 1 282578800148737 (2^56))%Z; try reflexivity; lia.
Qed.

Lemma byte_eq_mod : forall x y, (x mod 256 = y mod 256)%Z -> Z_to_bv 8 x = Z_to_bv 8 y.
Proof using. intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. exact H. Qed.

(* [comment removed for export] *)
Lemma rep8_bytes : forall c, (0 <= c < 256)%Z ->
  word_to_le_bytes 8 (Z_to_bv 64 (c * M8)) = repeat (Z_to_bv 8 c) 8.
Proof using.
  intros c Hc. (lazymatch goal with |- ?G => let G' := eval unfold word_to_le_bytes in G in change_no_check G' end). rewrite u_Z2bv by ((lazymatch goal with |- ?G => let G' := eval unfold M8 in G in change_no_check G' end); lia).
  (lazymatch goal with |- ?G => let G' := eval cbn [Z_to_le_bytes repeat] in G in change_no_check G' end). rewrite !Z.shiftr_shiftr by lia. (lazymatch goal with |- ?G => let G' := eval cbn [Z.add Pos.add Pos.succ] in G in change_no_check G' end).
  pose proof (M8_digit c) as D.
  repeat match goal with
  | |- (_ :: _) = (_ :: _) => f_equal
  | |- Z_to_bv 8 _ = Z_to_bv 8 _ => apply byte_eq_mod; rewrite (Z.mod_small c 256) by lia
  | |- [] = [] => reflexivity
  end.
  - rewrite <- (D 0%Z) at 2 by lia. rewrite Z.shiftr_0_r || ((lazymatch goal with |- ?G => let G' := eval cbn [Z.mul] in G in change_no_check G' end); rewrite Z.shiftr_0_r). reflexivity.
  - apply (D 1%Z); lia.
  - apply (D 2%Z); lia.
  - apply (D 3%Z); lia.
  - apply (D 4%Z); lia.
  - apply (D 5%Z); lia.
  - apply (D 6%Z); lia.
  - apply (D 7%Z); lia.
Qed.


(* [comment removed for export] *)
Lemma step_or_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_OR rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_or (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof using.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_or segs regs pc mem rom w rd rs1 rs2 Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

(* [comment removed for export] *)
End FPGen3.

Ltac av_or F D vv tac :=
  chain_step;
  [ reflexivity
  | eapply step_or_at with (v := vv); [ exact F | reflexivity | exact D | reflexivity | gres; rwH; imm_norm; tac ]
  | step_simpl ]; vn.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPGen4.
Context {fx : FPState}.

Definition align15 (n : Z) (s : word) : Z := Z.land (Z.lor n (bv_unsigned s)) 15.

Lemma land15_range : forall x, (0 <= x)%Z -> (0 <= Z.land x 15 < 16)%Z.
Proof using.
  intros x Hx. change 15%Z with (Z.ones 4). rewrite Z.land_ones by lia.
  apply Z.mod_pos_bound. lia.
Qed.

Lemma align15_range : forall n s, (0 <= n)%Z -> (0 <= align15 n s < 16)%Z.
Proof using.
  intros n s Hn. (lazymatch goal with |- ?G => let G' := eval unfold align15 in G in change_no_check G' end). apply land15_range. apply Z.lor_nonneg. pose proof (u64_range s). lia.
Qed.

Lemma u_align15 : forall n (s : word), (0 <= n < 2 ^ 64)%Z ->
  bv_unsigned (v_andi (v_or (Z_to_bv 64 n) s) 15) = align15 n s.
Proof using.
  intros n s Hn. pose proof (u64_range s) as Hs.
  pose proof (Z_lor_range n (bv_unsigned s) Hn Hs) as Hl.
  (lazymatch goal with |- ?G => let G' := eval unfold v_andi, v_or, align15 in G in change_no_check G' end). rewrite (u_Z2bv n) by lia.
  rewrite (u_Z2bv (Z.lor n (bv_unsigned s))) by lia.
  change (bv_wrap 64 15) with 15%Z.
  pose proof (land15_range (Z.lor n (bv_unsigned s)) ltac:(lia)).
  apply u_Z2bv; lia.
Qed.

Lemma align15_n16 : forall n s, (0 <= n)%Z -> align15 n s = 0%Z -> (n mod 16 = 0)%Z.
Proof using.
  intros n s Hn H. unfold align15 in H. pose proof (u64_range s).
  rewrite Z.land_lor_distr_l in H. apply Z.lor_eq_0_iff in H as [H _].
  change 15%Z with (Z.ones 4) in H. rewrite Z.land_ones in H by lia. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma step_fence_rt : forall segs regs pc mem rom w fm pred succ rd rs1,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fence fm pred succ rd rs1, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst regs (v_addi pc 4) mem rom).
Proof using.
  intros segs regs pc mem rom w fm pred succ rd rs1 Hfetch Hecall Hdecode.
  step_pipeline Hfetch Hecall Hdecode.
  rewrite b_npc4. reflexivity.
Qed.

(* [comment removed for export] *)
End FPGen4.

Ltac afence F D :=
  chain_step; [ reflexivity | eapply step_fence_rt; [exact F | reflexivity | exact D] | step_simpl ]; vn.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPGen5.
Context {fx : FPState}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land_7 : forall a, (0 <= a)%Z -> Z.land a 7 = (a mod 8)%Z.
Proof using. intros a Ha. change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma v_andi_7_aligned : forall x : word, (bv_unsigned x mod 8 = 0)%Z -> v_andi x 7 = Z_to_bv 64 0.
Proof using.
  intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold v_andi in G in change_no_check G' end). change (bv_wrap 64 7) with 7%Z.
  pose proof (u64_range x). rewrite land_7 by lia. rewrite Hx. reflexivity.
Qed.

Lemma v_srli_3 : forall x : word, v_srli x 3 = Z_to_bv 64 (bv_unsigned x / 8).
Proof using. intros x. (lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end). rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma u_v_lb_nz : forall b : byte, bv_unsigned b <> 0%Z -> bv_unsigned (v_lb b) <> 0%Z.
Proof using.
  intros b Hb. (lazymatch goal with |- ?G => let G' := eval unfold v_lb, bv_signed, bv_swrap, bv_wrap in G in change_no_check G' end). pose proof (u8_range b) as Hr.
  change (bv_half_modulus 8) with 128%Z. change (bv_modulus 8) with 256%Z.
  rewrite Z_to_bv_unsigned. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end). change (bv_modulus 64) with (2 ^ 64)%Z.
  destruct (Z.lt_ge_cases (bv_unsigned b) 128) as [L|G].
  - rewrite (Z.mod_small (bv_unsigned b + 128) 256) by lia.
    rewrite Z.mod_small by lia. lia.
  - replace ((bv_unsigned b + 128) mod 256)%Z with (bv_unsigned b + 128 - 256)%Z.
    2:{ rewrite <- (Z.mod_add _ (-1) 256) by lia. symmetry. rewrite Z.mod_small; lia. }
    rewrite <- (Z.mod_add _ 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma bv_signed_small64 : forall z, (0 <= z < 2 ^ 63)%Z -> bv_signed (Z_to_bv 64 z) = z.
Proof using.
  intros z Hz. (lazymatch goal with |- ?G => let G' := eval unfold bv_signed, bv_swrap, bv_wrap in G in change_no_check G' end). rewrite Z_to_bv_unsigned. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end).
  change (bv_half_modulus 64) with (2 ^ 63)%Z. change (bv_modulus 64) with (2 ^ 64)%Z.
  rewrite (Z.mod_small z) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma v_lb_small : forall b : byte, (bv_unsigned b < 128)%Z -> v_lb b = Z_to_bv 64 (bv_unsigned b).
Proof using.
  intros b Hb. pose proof (u8_range b). (lazymatch goal with |- ?G => let G' := eval unfold v_lb, bv_signed, bv_swrap, bv_wrap in G in change_no_check G' end).
  change (bv_half_modulus 8) with 128%Z. change (bv_modulus 8) with 256%Z.
  rewrite Z.mod_small by lia. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma c_lts_smallZ : forall x y, (0 <= x < 2 ^ 63)%Z -> (0 <= y < 2 ^ 63)%Z ->
  c_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = Z.ltb x y.
Proof using. intros x y Hx Hy. (lazymatch goal with |- ?G => let G' := eval unfold c_lts, bv_lts in G in change_no_check G' end). rewrite !bv_signed_small64 by lia. reflexivity. Qed.

(* [comment removed for export] *)
End FPGen5.

Ltac condzs :=
  rwH; rewrite ?c_lts_smallZ by lia; (lazymatch goal with |- ?G => let G' := eval unfold at_, c_eq, c_ltu, bv_eqb, bv_ltu in G in change_no_check G' end); imm_norm; unorm;
  first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; wd_ulia.

(* [comment removed for export] *)
Section FPGen6.
Context {fx : FPState}.

Lemma ret_ok_at : forall (b : word) d,
  (bv_unsigned b mod 2 = 0)%Z -> (d mod 2 = 0)%Z -> (0 <= bv_unsigned b + d < 2 ^ 64)%Z -> ret_ok (at_ b d).
Proof using.
  intros b d Hb Hd Hr. apply ret_ok_even. rewrite at_u by lia.
  rewrite Z.add_mod, Hb, Hd by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma v_not_word : forall x : word, v_xori x (-1) = Z_to_bv 64 (2 ^ 64 - 1 - bv_unsigned x).
Proof using.
  intros x. (lazymatch goal with |- ?G => let G' := eval unfold v_xori in G in change_no_check G' end). pose proof (u64_range x) as Hx. f_equal.
  change (bv_wrap 64 (-1)) with (Z.ones 64).
  rewrite <- Z.ldiff_ones_l_low; [| lia |].
  - rewrite Z.ldiff_land, <- Z.sub_land_same_l, Z.land_comm, Z.land_ones, Z.mod_small by lia.
    rewrite Z.ones_equiv. lia.
  - destruct (Z.eq_dec (bv_unsigned x) 0) as [->|Hnz]; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|].
    apply Z.log2_lt_pow2; lia.
Qed.



(* [comment removed for export] *)
End FPGen6.

Ltac reg_in_dec :=
  (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); first [ tauto | right; reg_in_dec ].

(* [comment removed for export] *)
Ltac notin :=
  let H := fresh "Hin" in intros H; cbn [In] in H;
  repeat (destruct H as [H|H]; [discriminate H|]); destruct H.

(* [comment removed for export] *)
Ltac incl_lists :=
  let i := fresh "i" in let H := fresh "Hi" in intros i H; cbn [In] in H;
  repeat (destruct H as [<-|H]; [solve [in_list] |]); destruct H.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac rd8_side :=
  wd_lenlit; rewrite ?length_N_to_le_bytes, ?repeat_length; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Nat.add Nat.mul] in G in change_no_check G' end);
  (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia.
Ltac wd_not_hit := lazymatch goal with |- rdn _ (wbytes _ ?a _) ?b _ = _ => tryif constr_eq a b then fail else idtac | _ => idtac end.
Ltac rd8_chain :=
  repeat (wd_not_hit; rewrite wd_rdn_wbytes_out3; [ | rd8_side ]);
  apply rdn_wbytes_hit8; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPGen7.
Context {fx : FPState}.


Lemma regs_agree_upd_keep : forall (C : regset) regs regs' (r : reg) v,
  regs_agree C regs regs' -> getr regs r = v -> r <> 0 -> regs_agree C regs (regupd regs' r v).
Proof using.
  intros C regs regs' r v AG Hv Hnz x Hx.
  destruct (decide (x = r)) as [->|Hne].
  - rewrite getr_same by exact Hnz. symmetry. exact Hv.
  - rewrite getr_other by exact Hne. apply AG, Hx.
Qed.

(* [comment removed for export] *)
Lemma regs_agree_strengthen : forall (l l' : list reg) regs regs',
  regs_agree (fun r => In r l') regs regs' ->
  (forall r, In r l' -> ~ In r l -> getr regs' r = getr regs r) ->
  regs_agree (fun r => In r l) regs regs'.
Proof using.
  intros l l' regs regs' AG E r Hr.
  destruct (In_dec (fun x y : reg => decide (x = y)) r l') as [Hin|Hnin].
  - apply E; assumption.
  - apply AG, Hnin.
Qed.

(* [comment removed for export] *)
End FPGen7.

Ltac ra_solve :=
  repeat (first [ apply regs_agree_upd; [solve [in_list] |]
                | apply regs_agree_upd_keep;
                  [ | first [reflexivity | rwH; rewrite ?at_0; reflexivity | symmetry; assumption]
                    | let X := fresh in intros X; discriminate X ] ]);
  first [apply regs_agree_refl | assumption].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPGen8.
Context {fx : FPState}.


Fixpoint code_ato (segs : list Segment) (base : word) (off : Z) (ws : list (option (bv 32))) : Prop :=
  match ws with
  | [] => True
  | Some w :: ws' => fetch_word segs (at_ base off) = Some w /\ code_ato segs base (off + 4)%Z ws'
  | None :: ws' => code_ato segs base (off + 4)%Z ws'
  end.

Fixpoint code_ato_b (segs : list Segment) (base : word) (off : Z) (ws : list (option (bv 32))) : bool :=
  match ws with
  | [] => true
  | Some w :: ws' =>
      match fetch_word segs (at_ base off) with
      | Some w' => Z.eqb (bv_unsigned w') (bv_unsigned w) && code_ato_b segs base (off + 4)%Z ws'
      | None => false
      end
  | None :: ws' => code_ato_b segs base (off + 4)%Z ws'
  end.

Lemma code_ato_b_sound : forall segs base ws off,
  code_ato_b segs base off ws = true -> code_ato segs base off ws.
Proof using.
  intros segs base ws; induction ws as [|[w|] ws IH]; intros off H; [exact I| |].
  - cbn [code_ato_b] in H. fold code_ato_b in H.
    destruct (fetch_word segs (at_ base off)) as [w'|] eqn:E; [|discriminate].
    apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply bv_eq in H1. subst w'.
    split; [exact E | apply IH; exact H2].
  - cbn [code_ato_b] in H. fold code_ato_b in H. (lazymatch goal with |- ?G => let G' := eval cbn [code_ato] in G in change_no_check G' end). apply IH. exact H.
Qed.
End FPGen8.


Ltac code_ato_vm := apply code_ato_b_sound; vm_compute; reflexivity.

(* [comment removed for export] *)
Section FPGen9.
Context {fx : FPState}.

Lemma code_ato_get : forall segs base off ws (i : nat) w,
  code_ato segs base off ws -> nth_error ws i = Some (Some w) ->
  fetch_word segs (at_ base (off + 4 * Z.of_nat i)%Z) = Some w.
Proof using.
  intros segs base off ws i; revert off ws; induction i as [|i IH]; intros off ws w HC Hn.
  - destruct ws as [|[w0|] ws']; [discriminate| |discriminate]. cbn in Hn. injection Hn as ->.
    destruct HC as [HF _]. replace (off + 4 * Z.of_nat 0)%Z with off by lia. exact HF.
  - destruct ws as [|[w0|] ws']; [discriminate| |].
    + cbn in Hn. destruct HC as [_ HC'].
      replace (off + 4 * Z.of_nat (S i))%Z with ((off + 4) + 4 * Z.of_nat i)%Z by lia.
      exact (IH _ _ _ HC' Hn).
    + cbn in Hn. cbn [code_ato] in HC.
      replace (off + 4 * Z.of_nat (S i))%Z with ((off + 4) + 4 * Z.of_nat i)%Z by lia.
      exact (IH _ _ _ HC Hn).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition gload (segs : list Segment) (base : word) (off : Z) (rd : reg) (g : Z) : Prop :=
  forall regs mem rom (v : word),
    rdn segs mem (Z_to_bv 64 g) 8 = Some (word_to_le_bytes 8 v) ->
    msteps segs (mkst regs (at_ base off) mem rom)
                (mkst (regupd regs rd v) (at_ base (off + 8)) mem rom).

(* [comment removed for export] *)
Definition gload2 (segs : list Segment) (base : word) (off : Z) (r1 rd : reg) (g : Z) : Prop :=
  exists x : word, forall regs mem rom (v : word),
    rdn segs mem (Z_to_bv 64 g) 8 = Some (word_to_le_bytes 8 v) ->
      msteps segs (mkst regs (at_ base off) mem rom)
                  (mkst (regupd (regupd regs r1 x) rd v) (at_ base (off + 8)) mem rom).

(* [comment removed for export] *)
Definition gloadb (segs : list Segment) (base : word) (off : Z) (rd : reg) (g : Z) : Prop :=
  forall regs mem rom (b : byte),
    rdn segs mem (Z_to_bv 64 g) 1 = Some [b] ->
    msteps segs (mkst regs (at_ base off) mem rom)
                (mkst (regupd regs rd (v_lb b)) (at_ base (off + 8)) mem rom).


(* [comment removed for export] *)
Lemma tset_tset_same {A} : forall (p : positive) (x y : A) t, tset p x (tset p y t) = tset p x t.
Proof using.
  induction p as [p IH|p IH|]; intros x y [|l o r]; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); try reflexivity; rewrite IH; reflexivity.
Qed.

Lemma regupd_regupd_same : forall regs (r : reg) x v, regupd (regupd regs r x) r v = regupd regs r v.
Proof using. intros regs r x v. (lazymatch goal with |- ?G => let G' := eval unfold regupd, bvmap_set in G in change_no_check G' end). apply tset_tset_same. Qed.

(* [comment removed for export] *)
End FPGen9.

Ltac lit_pc :=
  lazymatch goal with
  | |- msteps _ (mkst _ ?p _ _) _ => wlit_replace p
  end.
Ltac lit_pc_post :=
  lazymatch goal with
  | |- msteps _ _ (mkst _ ?p _ _) => wlit_replace p
  end.
Ltac lit_pc_step :=
  lazymatch goal with
  | |- RiscvSemantics.step _ (mkst _ ?p _ _) = _ => wlit_replace p
  end.
(* [comment removed for export] *)
Ltac rdn_lit_exact H :=
  first [ exact H
        | lazymatch goal with
          | |- rdn _ _ ?a _ = _ =>
              lazymatch type of H with
              | rdn _ _ ?b _ = _ => replace a with b by (apply bv_eq; vm_compute; reflexivity); exact H
              end
          end ].

(* [comment removed for export] *)
Ltac close_refl :=
  reduce_bv_eqb_ifs; rewrite ?regupd_regupd_same;
  lazymatch goal with
  | |- msteps _ (mkst ?r1 ?p1 ?m ?rom) (mkst ?r2 ?p2 ?m ?rom) =>
      replace p1 with p2 by (apply bv_eq; vm_compute; reflexivity); wd_refl
  end.

Ltac gload_tac Fa Da Fl Dl :=
  let regs := fresh "regs" in let mem := fresh "mem" in let rom := fresh "rom" in
  let v := fresh "v" in let Hrd := fresh "Hrd" in
  try (let x := fresh "x" in eexists);            (* [comment removed for export] *)
  intros regs mem rom v Hrd;
  lit_pc;
  (chain_step; [ reflexivity | eapply step_auipc; [exact Fa | reflexivity | exact Da] | step_simpl ]);
  gres; imm_norm; vals_lit;
  (chain_step;
   [ reflexivity
   | first [ eapply step_ld with (bs := word_to_le_bytes 8 v) (v := v);
             [exact Fl | reflexivity | exact Dl | | apply bytes_le_to_Z_8]
           | eapply step_lb; [exact Fl | reflexivity | exact Dl | ] ];
     gres; imm_norm; (lazymatch goal with |- ?G => let G' := eval unfold v_auipc, v_addi in G in change_no_check G' end); vals_lit; rdn_lit_exact Hrd
   | step_simpl ]);
  close_refl.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPGen10.
Context {fx : FPState}.

Definition gaddr2 (segs : list Segment) (base : word) (off : Z) (r1 rd : reg) (v : word) : Prop :=
  exists x : word, forall regs mem rom,
    msteps segs (mkst regs (at_ base off) mem rom)
                (mkst (regupd (regupd regs r1 x) rd v) (at_ base (off + 8)) mem rom).

(* [comment removed for export] *)
Definition gjump (segs : list Segment) (base : word) (off : Z) (tgt : word) : Prop :=
  forall regs mem rom,
    msteps segs (mkst regs (at_ base off) mem rom) (mkst regs tgt mem rom).

(* [comment removed for export] *)
Definition gauipc_ld (segs : list Segment) (base : word) (off1 off2 : Z) (rt rd : reg) (g : Z) : Prop :=
  exists x : word,
    (forall regs mem rom,
        msteps segs (mkst regs (at_ base off1) mem rom) (mkst (regupd regs rt x) (at_ base (off1 + 4)) mem rom))
    /\ (forall regs mem rom (v : word),
           getr regs rt = x ->
           rdn segs mem (Z_to_bv 64 g) 8 = Some (word_to_le_bytes 8 v) ->
           msteps segs (mkst regs (at_ base off2) mem rom) (mkst (regupd regs rd v) (at_ base (off2 + 4)) mem rom)).

Lemma mst_eq : forall segs s1 s2, s1 = s2 -> msteps segs s1 s2.
Proof using. intros segs s1 s2 ->. apply mst_refl. Qed.

(* [comment removed for export] *)
End FPGen10.

Ltac close_eq :=
  reduce_bv_eqb_ifs;
  apply mst_eq;
  lazymatch goal with
  | |- mkst ?r1 ?p1 ?m ?rom = mkst ?r2 ?p2 ?m ?rom =>
      replace p1 with p2 by (apply bv_eq; vm_compute; reflexivity);
      replace r1 with r2; [reflexivity|];
      repeat (first [reflexivity | apply bv_eq; vm_compute; reflexivity | f_equal])
  end.

Ltac gaddr2_tac Fa Da Fb Db :=
  let regs := fresh "regs" in let mem := fresh "mem" in let rom := fresh "rom" in
  eexists; intros regs mem rom;
  lit_pc;
  (chain_step; [ reflexivity | eapply step_auipc; [exact Fa | reflexivity | exact Da] | step_simpl ]);
  gres; imm_norm; vals_lit;
  (chain_step; [ reflexivity | eapply step_addi; [exact Fb | reflexivity | exact Db] | step_simpl ]);
  gres; imm_norm; (lazymatch goal with |- ?G => let G' := eval unfold v_auipc, v_addi in G in change_no_check G' end); vals_lit;
  close_eq.

Ltac gjump_tac Fa Da :=
  let regs := fresh "regs" in let mem := fresh "mem" in let rom := fresh "rom" in
  intros regs mem rom;
  lit_pc;
  (chain_step; [ reflexivity | eapply step_jal_x0; [exact Fa | reflexivity | exact Da] | step_simpl ]);
  gres; imm_norm; vals_lit;
  close_eq.

Ltac gauipc_ld_tac Fa Da Fl Dl :=
  let regs := fresh "regs" in let mem := fresh "mem" in let rom := fresh "rom" in
  let v := fresh "v" in let Hx := fresh "Hx" in let Hrd := fresh "Hrd" in
  eexists; split;
  [ intros regs mem rom; lit_pc;
    (chain_step; [ reflexivity | eapply step_auipc; [exact Fa | reflexivity | exact Da] | step_simpl ]);
    gres; imm_norm; (lazymatch goal with |- ?G => let G' := eval unfold v_auipc in G in change_no_check G' end); vals_lit; close_eq
  | intros regs mem rom v Hx Hrd; lit_pc;
    (chain_step;
     [ reflexivity
     | eapply step_ld with (bs := word_to_le_bytes 8 v) (v := v);
       [exact Fl | reflexivity | exact Dl | rewrite Hx; imm_norm; (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); vals_lit; rdn_lit_exact Hrd | apply bytes_le_to_Z_8]
     | step_simpl ]);
    gres; close_eq ].

(* [comment removed for export] *)
Section FPGen11.
Context {fx : FPState}.

Lemma v_lw_small : forall z, (0 <= z < 2 ^ 31)%Z -> v_lw (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof using.
  intros z Hz. (lazymatch goal with |- ?G => let G' := eval unfold v_lw in G in change_no_check G' end). f_equal. rewrite Z_to_bv_unsigned. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap, bv_swrap, bv_wrap in G in change_no_check G' end).
  change (bv_modulus 64) with (2 ^ 64)%Z. change (bv_half_modulus 32) with (2 ^ 31)%Z. change (bv_modulus 32) with (2 ^ 32)%Z.
  rewrite (Z.mod_small z) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma bytes4_small : forall z, (0 <= z < 2 ^ 32)%Z ->
  bytes_le_to_Z (word_to_le_bytes 4 (Z_to_bv 64 z)) = bv_unsigned (Z_to_bv 64 z).
Proof using. intros z Hz. apply bytes_le_to_Z_4_small. rewrite Z_to_bv_unsigned. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end). change (bv_modulus 64) with (2 ^ 64)%Z. rewrite Z.mod_small; lia. Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition hid_off (H : word -> bool) (lo n : Z) : Prop :=
  forall x : word, (lo <= bv_unsigned x < lo + n)%Z -> H x = false.

Lemma hid_off_sub : forall H lo n lo' n',
  hid_off H lo n -> (lo <= lo')%Z -> (lo' + n' <= lo + n)%Z -> hid_off H lo' n'.
Proof using. intros H lo n lo' n' Hh H1 H2 x Hx. apply Hh. lia. Qed.

Lemma hid_off_nil : forall H lo n, (n <= 0)%Z -> hid_off H lo n.
Proof using. intros H lo n Hn x Hx. lia. Qed.

(* [comment removed for export] *)
Lemma hid_off_range_avoids : forall H (a : word) (n : nat),
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  hid_off H (bv_unsigned a) (Z.of_nat n) -> range_avoids H a n.
Proof using.
  intros H a n Hnw Hh k Hk. apply Hh. (lazymatch goal with |- ?G => let G' := eval unfold woff in G in change_no_check G' end). pose proof (u64_range a).
  rewrite Z_to_bv_unsigned. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end). change (bv_modulus 64) with (2 ^ 64)%Z.
  rewrite Z.mod_small; lia.
Qed.


(* [comment removed for export] *)
Lemma rdn_mrestrict : forall segs H m (a : word) n,
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  hid_off H (bv_unsigned a) (Z.of_nat n) ->
  rdn segs (mrestrict H m) a n = rdn segs m a n.
Proof using.
  intros segs H m a n Hnw Hh. apply rdn_mrestrict_eq. apply hid_off_range_avoids; assumption.
Qed.

(* [comment removed for export] *)
Lemma store_ok_mrestrict : forall segs H m (a : word) n,
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  hid_off H (bv_unsigned a) (Z.of_nat n) ->
  store_ok segs (mrestrict H m) a n = store_ok segs m a n.
Proof using.
  intros segs H m a n Hnw Hh. apply store_ok_mrestrict_eq. apply hid_off_range_avoids; assumption.
Qed.

(* [comment removed for export] *)
Lemma wbytes_mrestrict : forall H bs m (a : word),
  (bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  hid_off H (bv_unsigned a) (Z.of_nat (length bs)) ->
  wbytes (mrestrict H m) a bs = mrestrict H (wbytes m a bs).
Proof using.
  intros H bs; induction bs as [|b rest IH]; intros m a Hnw Hh; [reflexivity|].
  cbn [wbytes length] in *. pose proof (u64_range a) as Ha.
  assert (Hha : H a = false) by (apply Hh; lia).
  assert (E : (fun x : word => if bv_eqb x a then Some b else mrestrict H m x)
              = mrestrict H (fun x : word => if bv_eqb x a then Some b else m x)).
  { apply functional_extensionality. intros x. (lazymatch goal with |- ?G => let G' := eval unfold mrestrict in G in change_no_check G' end).
    destruct (bv_eqb x a) eqn:Ex; [|reflexivity].
    unfold bv_eqb in Ex. apply Z.eqb_eq in Ex. apply bv_eq in Ex. subst x. rewrite Hha. reflexivity. }
  rewrite E. destruct rest as [|b' rest'].
  - reflexivity.
  - assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; cbn [length] in Hnw; lia).
    apply IH; [rewrite Hu1; lia|]. intros x Hx. apply Hh. rewrite Hu1 in Hx. lia.
Qed.

Lemma wbytes_mrestrict_at : forall H bs m (d : word) n,
  length bs = Z.to_nat n -> (0 <= n)%Z -> (bv_unsigned d + n <= 2 ^ 64)%Z ->
  hid_off H (bv_unsigned d) n ->
  wbytes (mrestrict H m) d bs = mrestrict H (wbytes m d bs).
Proof using.
  intros H bs m d n Hlen Hn Hnw Hh. apply wbytes_mrestrict; rewrite Hlen; [lia|].
  intros x Hx. apply Hh. lia.
Qed.
End FPGen11.


Section FPGenX.
Context {fx : FPState}.

End FPGenX.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
