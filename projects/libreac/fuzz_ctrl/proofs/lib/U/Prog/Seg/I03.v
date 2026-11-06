(* Segment I03 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan, libreac v1.9.0): [0x13a28, 0x13a60], U13a28 -> U13a64
   (#54 not taken: record_sum_closes returned 1 since IR's record sums to 0 (REPLY C1.5); T24, T25 on blk = Φ + 18
   (s8; v1.8 s7) not taken by HBR; the address check #55 (Φ[36] << 8 | Φ[37] = addr_r);
   reac_identity_ingest (0x163ec) (sp+76 = id, v1.8 sp+154; addr_r, Φ + 38, pll_r)). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcParse RcReply RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcFrag RcLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInv reac_identity_ingest_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.Seg Require Import Tac_slot Tac_u4 Tac_u5.
Import ListNotations.
Open Scope Z_scope.

(* 0x13a48-0x13a4c: (Φ[36] << 8) | Φ[37]. *)
Lemma i03_addr_eq : forall b36 b37 : byte,
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb b36)) 8))) (bv_unsigned (zxb b37))) =
  zx16 (Z_to_bv 64 (bv_unsigned b36 * 256 + bv_unsigned b37)).
Proof.
  intros b36 b37. pose proof (RcLib.byte_range b36) as R6. pose proof (RcLib.byte_range b37) as R7.
  unfold zxb, zx16.
  rewrite (MState.unsigned_lit (bv_unsigned b36)) by lia.
  rewrite (MState.unsigned_lit (bv_unsigned b37)) by lia.
  replace (Z.shiftl (bv_unsigned b36) 8) with (bv_unsigned b36 * 256)
    by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
  rewrite (MState.unsigned_lit (bv_unsigned b36 * 256)) by lia.
  rewrite (MState.unsigned_lit (bv_unsigned b36 * 256 + bv_unsigned b37)) by lia.
  rewrite u5_lor8 by lia. f_equal. rewrite Z.mod_small by lia. lia.
Qed.

Lemma i03_evt : reac_identity_ingest_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi : Z) (g idb : list byte),
    sp = Z_to_bv 64 spv -> s8 = Z_to_bv 64 (phi + 18) -> a0 = Z_to_bv 64 1 ->
    1 <= r_pll g <= 10 -> 4096 <= phi -> phi + 50 <= spv -> spv mod 16 = 0 -> spv + 1936 <= 2 ^ 64 ->
    length g = 50%nat -> bytes_at rsegs m phi g ->
    ov_read_bytes rsegs m (wa (spv + 1750)) 2 = Some (le2 (Z_to_bv 64 (r_addr g))) ->
    ov_read_bytes rsegs m (wa (spv + 1736)) 8 = Some (le8 (Z_to_bv 64 (phi + 38))) ->
    ov_read_bytes rsegs m (wa (spv + 1728)) 8 = Some (le8 (Z_to_bv 64 (r_pll g))) ->
    rw_cells rsegs m (spv + 76) [CB 38 idb] ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x13a64) sp gp tp t0' t1' t2' s0 s1
                       (Z_to_bv 64 (fst (ING idb (r_addr g) (r_pl g))))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13a64) fc None m' (seg_rom rsegs) /\
         munch [(spv + 76, spv + 114)] m m' /\ wmono rsegs m m' /\
         rw_cells rsegs m' (spv + 76) [CB 38 (snd (ING idb (r_addr g) (r_pl g)))])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13a28) fc None m (seg_rom rsegs)).
Proof.
  intros ING ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi g idb Hsp Hs8 Ha0 Hpll Hphi Hpb H16 Hhi Hg HB HRA R1736 R1728 Hid.
  subst sp s8 a0.
  pose proof (u5_raddr_range g) as Hra.
  pose proof (u5_byte_read m phi g 36 HB ltac:(lia)) as HR36.
  pose proof (u5_byte_read m phi g 37 HB ltac:(lia)) as HR37.
  change (Z.of_nat 36) with 36 in HR36. change (Z.of_nat 37) with 37 in HR37.
  step. u5_br false.
  step. step. u5_br false.
  step. step. u5_br false.
  step. step. step. step. step.
  step.
  rewrite i03_addr_eq.
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false by (symmetry; apply negb_false_iff; unfold bv_eqb; apply Z.eqb_eq; reflexivity)
  end; cbv iota.
  step. step. step. step.
  eapply evt_cut.
  { eapply ING with (id := spv + 76) (ad := r_addr g) (p := phi + 38) (len := r_pll g) (idb := idb)
      (pb := r_pl g);
      [ first [reflexivity | u5_weq] | apply u5_zx16; exact Hra | reflexivity | reflexivity
      | lia | lia | lia | lia | | | | ].
    - intros _. split; [lia | exact Hid].
    - unfold r_pl, RcFrag.bsl. rewrite length_firstn, length_skipn, Hg. lia.
    - intros _ _. unfold r_pl.
      exact (u5_ba_bsl m phi g 38 (r_pll g) HB ltac:(lia) ltac:(lia) ltac:(rewrite Hg; lia)).
    - intros _ _ _. left. lia. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m' & E & MUc & WMc & _ & _ & Hrw).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x13a64)) with (Z_to_bv 64 0x13a64)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  assert (Hnr : ingest_refused (spv + 76) (phi + 38) (r_pll g) = false).
  { unfold ingest_refused.
    rewrite (proj2 (Z.eqb_neq (spv + 76) 0)), (proj2 (Z.eqb_neq (r_pll g) 0)), (proj2 (Z.eqb_neq (phi + 38) 0))
      by lia.
    reflexivity. }
  unfold ingest_ret. rewrite Hnr.
  apply evt_done. exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', m'.
  replace (spv + 76 + 38) with (spv + 114) in MUc by lia.
  split; [reflexivity|]. split; [exact MUc|]. split; [exact WMc|]. exact (Hrw Hnr).
Qed.

Section I03.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis ING : reac_identity_ingest_contract.
Hypothesis INGOK : reac_identity_ingest_id_ok_kept.

Lemma seg_I03 : forall j : nat, Hat B APIf ra (Inv_U13a64_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_U13a28_at B APIf ra empty) j.
Proof.
  intros j H g c (phi & L & A & regs & mem & md & -> & HFR & HP & HFB & HIFS & Hir & HRPS & H10).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  pose proof (u4_phi_bnd B APIf ra empty g phi _ L A regs mem md HFR HP) as Hbnd.
  pose proof HFB as ((HLK & (HS24 & H21 & H22) & H23 & Hphi & H18) & (H25 & H19 & H27 & H20 & (H24 & _ & _))).
  destruct (u5_ir_facts _ _ Hir) as (H50 & Hbig & Hsok & Hpll & _).
  destruct (ir_true _ _ Hir) as (_ & _ & _ & _ & _ & _ & _ & _ & Hrec).
  destruct (proj1 HRPS Hir) as (Ra & Rb & Rc).
  pose proof HIFS as ((HI & Hok) & HG & HS).
  pose proof (u4_phi_g _ _ _ _ (u5_norm mem phi _ HMI Hphi) H50) as HGg.
  unfold IDB in HI.
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME, spk in *.
  destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 76) 38 ST ltac:(lia) ltac:(lia)) as (jk & Hjk).
  pose proof (u5_rw_ba _ _ _ _ _ Hjk (u5_norm mem _ _ HMI HI) (u4_tID_len _ _)) as Hid.
  assert (HRA : ov_read_bytes rsegs (normalize rsegs mem) (wa (g_S g - 1936 + 1750)) 2 =
                Some (le2 (Z_to_bv 64 (r_addr (t_g (g_in g) j))))).
  { pose proof (u5_ovr _ _ _ (u5_norm mem _ _ HMI Ra)) as X. rewrite u5_raddr in X.
    rewrite length_le2 in X. exact X. }
  eapply (u4_mid B APIf ra empty FF g _ L A regs mem md _ [(g_S g - 1936 + 76, g_S g - 1936 + 114)]);
    [exact HFR | exact HP | u4_fp_tac | | |].
  - rewrite sl_mkR_of.
    apply (i03_evt ING) with (spv := g_S g - 1936) (phi := phi) (g := t_g (g_in g) j) (idb := t_ID (g_in g) j);
      [exact Hsp | | | exact Hpll | lia | lia | exact H16 | lia | apply u4_tg_len | exact HGg | exact HRA
      | exact (u5_q64_read _ _ _ (u5_q64_norm mem _ _ HMI Rb))
      | exact (u5_q64_read _ _ _ (u5_q64_norm mem _ _ HMI Rc)) | exact Hid].
    + unfold rg in H24. rewrite H24, Hbig. reflexivity.
    + unfold rg in H10. rewrite H10, u5_irrec, Hrec. reflexivity.
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & MU & WM & _).
    do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    split; [reflexivity|]. split; reflexivity.
  - intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & _ & _ & Hrw).
    injection HE; intros; subst.
    assert (HKP : SKP regs regs') by (repeat split; rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    apply H. exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    split; [split; [|split; [|split]]|split].
    + apply (u4_FB_keep g j phi regs regs' mem m' _ HFB HKP MU'); u4_dj.
    + unfold t_ir in Hir. split.
      * unfold IDB, t_IDr, rp_id. rewrite Hir.
        apply (proj2 (bytes_at_rel rsegs _ _ _ _ Hrel)). exact (sl_rw_bytes _ _ _ _ Hrw).
      * unfold t_IDr, rp_id. rewrite Hir. exact (INGOK _ _ _ (u4_tID_len _ _) Hok).
    + exact (u4_FGb_keep g _ mem m' _ (u4_tFG_len _ _) HG MU' ltac:(u4_dj)).
    + exact (u4_FSj_keep g j mem m' _ HS MU' ltac:(u4_dj)).
    + exact Hir.
    + unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
Qed.

End I03.
