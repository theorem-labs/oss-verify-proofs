From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import StdioModel mseek_c.
Import ListNotations.
Open Scope Z_scope.

Lemma ro_c8 : forall m A v, bytes_at rsegs m A (le8 v) -> ro_cells rsegs m A [C8 v].
Proof. intros m A v H. split; [exact (conj I I)|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H. Qed.

Lemma signed_lit64 : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_signed. apply bv_swrap_small.
  unfold bv_half_modulus, bv_modulus. cbn. lia.
Qed.

Theorem mseek_holds : mseek_contract.
Proof.
  unfold mseek_contract, MSEEK_FN, MSEEK_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo b n
    fl rpos rend md q r pv nx buf HM Hr Hq Hn A1 A2 [HGOT [g HGD]] MI ST LO HLO HOH.
  destruct HM as (pad0 & pad1 & pad2 & ung & HC & Lung & Lbuf & Hh0 & Hh16).
  subst a1 a2.
  unfold mfile_cells in HC.
  unfold A_GOT_GUARD, A_GUARD, A_OFL_HEAD, A_MCLOSE, A_MREAD, A_MWRITE, A_MSEEK, wz in *.
  apply ro_c8 in HGOT. apply ro_c8 in HGD.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word a0) as Ra0. unfold inr64 in Ra0.
  assert (GD : bv_unsigned a0 + 240 <= (symaddr Symbols.Ubsan.s___stack_chk_guard) \/ (symaddr Symbols.Ubsan.s___sysinfo) <= bv_unsigned a0 + 232) by (Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (bv_unsigned a0 + 232, bv_unsigned a0 + 240)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  carve_frame 48%nat ST.
  step. step. step. step. step. step. step. step. step.
  if_false.
  step. step. step. step. step. step. step. step. step. step. step.
  rewrite (unsigned_lit q) by lia.
  assert (C1 : bv_lts (Z_to_bv 64 (- r)) (Z_to_bv 64 (0 - q)) = false)
    by (unfold bv_lts; rewrite !signed_lit64 by lia; apply Z.ltb_ge; lia).
  step. rewrite C1; cbv iota.
  step. step.
  rewrite (unsigned_lit q), (unsigned_lit n) by lia.
  assert (C2 : negb (bv_lts (Z_to_bv 64 (n - q)) (Z_to_bv 64 (- r))) = true)
    by (unfold bv_lts; rewrite !signed_lit64 by lia; apply Bool.negb_true_iff, Z.ltb_ge; lia).
  step. rewrite C2; cbv iota.
  step. step. step. step. step. step. if_false.
  step. step. step.
  release_frame FR ST (bv_unsigned sp).
  step.
  apply evt_done. unfold mseek_post, MSEEK_K.
  do 16 eexists. split; [reflexivity|].
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
  - unfold wz. f_equal; lia.
  - replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia. exact MU.
  - exact WM.
  - exact MI.
  - exact ST.
  - unfold mfile_raw, mfile_cells, wz. exists pad0, pad1, pad2, ung.
    refine (conj _ (conj Lung (conj Lbuf (conj Hh0 Hh16)))).
    replace (q - r) with (q + - r) by lia. exact HC.
Qed.
