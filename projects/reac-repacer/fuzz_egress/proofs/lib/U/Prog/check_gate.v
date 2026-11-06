From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib Require Import EgressFrame.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Prog Require Import
  reac_frame_clean_len_c rp_frame_channels_c rp_slot_width_c want_width_c check_gate_c.
Import ListNotations.
Open Scope Z_scope.

(* The library's frame law and the harness's agree on every length the harness passes. *)
Lemma cg_width_table :
  forallb (fun k => Z.eqb (rp_frame_channels_model (50 + Z.of_nat k)) (w_width_model (50 + Z.of_nat k))) (seq 0 1551) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma cg_width_eq : forall n, 50 <= n <= 1600 -> rp_frame_channels_model n = w_width_model n.
Proof.
  intros n Hn. pose proof cg_width_table as T. rewrite forallb_forall in T.
  specialize (T (Z.to_nat (n - 50))). rewrite Z2Nat.id in T by lia. replace (50 + (n - 50)) with n in T by lia.
  apply Z.eqb_eq, T. apply in_seq. lia.
Qed.

Lemma cg_small : forall n, 0 <= n < 124 -> w_width_model n = -1.
Proof.
  intros n Hn. unfold w_width_model.
  rewrite (proj2 (Z.leb_gt 124 n)) by lia. rewrite (proj2 (Z.leb_gt 126 n)) by lia. rewrite !andb_false_r. reflexivity.
Qed.

Lemma cg_swrap : forall n, 0 <= n <= 1600 -> bv_swrap 64 n = n.
Proof. intros n Hn. apply bv_swrap_small. change (bv_half_modulus 64) with (2^63). lia. Qed.

Lemma cg_models : forall n bs slot, 0 <= n <= 1600 -> length bs = Z.to_nat n ->
  rp_slot_width_model n bs slot = want_width_model n bs slot.
Proof.
  intros n bs slot Hn HL. unfold rp_slot_width_model, want_width_model, frame_is_audio, slot_byte.
  destruct (Z.ltb_spec n 50) as [Hs|Hs].
  - rewrite cg_small by lia. reflexivity.
  - rewrite (nth_indep bs (Z_to_bv 8 0) (Z_to_bv 8 1)) by lia.
    rewrite (nth_indep bs (Z_to_bv 8 0) (Z_to_bv 8 1) (n := 17%nat)) by lia.
    rewrite cg_swrap, cg_width_eq by lia.
    destruct (bv_unsigned (nth 16 bs (Z_to_bv 8 1)) =? 0); destruct (bv_unsigned (nth 17 bs (Z_to_bv 8 1)) =? 0);
      cbn [negb orb andb]; rewrite ?orb_false_r, ?orb_true_r; cbn [orb]; reflexivity.
Qed.

Lemma cg_signed : forall z, -2^31 <= z < 2^31 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. unfold bv_signed. rewrite Z_to_bv_unsigned.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 64) with (2^63). change (bv_modulus 64) with (2^64).
  rewrite Zplus_mod_idemp_l. rewrite Z.mod_small by lia. lia.
Qed.

Theorem check_gate_holds : rp_slot_width_contract -> want_width_contract -> check_gate_contract.
Proof.
  intros SW WW. unfold check_gate_contract, CHECK_GATE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs slot lo
    HI ST HLO Ha0 HB HL HN DF -> Hs.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. change (bv_modulus 64) with (2^64) in Ra1.
  assert (HL' : Z.of_nat (length bs) = bv_unsigned a1) by (rewrite HL; lia).
  assert (Hlo0 : 0 <= lo) by (destruct ST as [H _]; exact H).
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  do 10 step.
  eapply evt_cut; [eapply (SW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bs lo) |].
  all: rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by lia.
  { assumption. }
  { exact ST. }
  { lia. }
  { intros H50. split; [lia|]. split; [lia|]. split; [exact HB|]. rewrite HL'. lia. }
  intros ms' (a1' & a2' & a3' & m1 & -> & MU1 & WM1 & MI1 & ST1).
  replace (ret_pc (Z_to_bv 64 0x13074)) with (Z_to_bv 64 0x13074) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  clear ST HI. rename ST1 into ST. rename MI1 into HI.
  transport_after_call rsegs m0 m1 MU1 WM1.
  do 5 step.
  eapply evt_cut; [eapply (WW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bs slot) |].
  { exact HB. }
  { exact HL. }
  { reflexivity. }
  { exact Hs. }
  intros ms' (b1 & b2 & b3 & b4 & b5 & b6 & ->).
  replace (ret_pc (Z_to_bv 64 0x13088)) with (Z_to_bv 64 0x13088) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  rewrite cg_signed by lia. rewrite cg_models by lia.
  step. rewrite bv_eqb_refl. cbn [negb].
  do 7 step.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact HI|]. exact ST.
Qed.
