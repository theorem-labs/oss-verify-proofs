(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/U/Prog/LLVMFuzzerTestOneInput_early_cg.v, with its module paths and numbers changed; 365 of its 420 lines of code are new or changed and 31 lines of the source are left out. *)
(* The crash-free twin of LLVMFuzzerTestOneInput.v: the same walk of fuzz_lock.ubsan's LLVMFuzzerTestOneInput
   (0x12bbc) with SRcf B in place of SR (ms_segs B), as libreac/fuzz_decode's released
   lib/U/Prog/check_round_trip_cg.v (25e3d17bdb50) does for its harness function. The machine walks of lt_segs.v
   are the same; only the composition changes, so that no call of the two harness functions is cut. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require Import Contract Img0 SlotAgree AgreeLift.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Spec Require Import LockSpec.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog Require Import check_no_overread_c check_lookup_c check_no_overread_ccf check_lookup_ccf lt_cf_c
  LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr lt_segs lt_glue lt_glue_cf.
Import ListNotations.
Open Scope Z_scope.

Section C.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= YM05.alloc_ceiling.
Hypothesis SINK : lf_sink_env B.
Hypothesis CNO : forall fx' : YK11.FPState, @check_no_overread_contract_cf fx' rc B API.
Hypothesis CL : forall fx' : YK11.FPState, @check_lookup_contract_cf fx' rc B API.

(* the harness returned: its post is the frame invariant and the return register *)
Lemma llvm_finish_cf : forall (fx' : YK11.FPState) stk empty L0 A0 regs0 mem0 md0 ra p n r L A regs mem md b j,
  llvm_binds B API ->
  lib_pre B API stk empty L0 A0 regs0 mem0 md0 ra p n -> sink_none B mem0 md0 ->
  YK0s.ret_ok (Z_to_bv 64 ra) -> frm_zero (@fp_csr fx') ->
  lf_fr B API stk (spZ regs0) L0 A0 mem0 md0 L A mem md ->
  YK11.getr regs 10 = Z_to_bv 64 r -> regs_preserved regs0 regs -> res_ok_slots A b ->
  SRcf B (mkCfg (@YK11.mkst fx' regs (ret_pc (YK11.getr regs0 1)) mem (YK11.seg_rom rsegs)) md)
    (llvm_post B API r stk L0 A0 regs0 mem0 md0 ra p n b j).
Proof.
  intros fx' stk empty L0 A0 regs0 mem0 md0 ra p n r L A regs mem md b j BI Hpre Hsn Hra Hfrm FR G10 RP Hres.
  destruct BI as (SEGS & _ & _ & _ & _ & _).
  pose proof Hpre as (_ & _ & _ & _ & Hra1 & _).
  apply (SRcf_ret B).
  destruct (lf_post B API SINK stk empty L0 A0 regs0 mem0 md0 ra p n r L A regs mem md Hpre Hsn FR G10 RP)
    as (Hpost & Hsn' & Hpay & MI2).
  exists fx', L, A, regs, mem, md.
  split; [rewrite SEGS, Hra1, (lf_ret_pc _ Hra); reflexivity|].
  split; [exact Hfrm|]. split; [exact Hpost|]. split; [exact Hsn'|].
  split; [exact Hres|]. split; [exact Hpay|]. split; [exact MI2 | exact I].
Qed.


Lemma llvm_early_cf : forall j stk empty L A regs mem md ra p n pl b,
  llvm_binds B API -> LLVM_K <= stk -> YK0s.ret_ok (Z_to_bv 64 ra) ->
  lib_pre B API stk empty L A regs mem md ra p n -> sink_none B mem md ->
  res_ok_slots A b -> ro_agree rsegs mem -> frm_zero fp_csr ->
  n = Z.of_nat (length pl) -> (n < 2 \/ 2 ^ 26 <= n) ->
  SRcf B (mkCfg (YK11.mkst regs (Z_to_bv 64 LLVM_ENTRY) mem (seg_rom (ms_segs B))) md)
    (llvm_post B API (lock_ret pl) stk L A regs mem md ra p n b j).
Proof.
  intros j stk empty L A regs mem md ra p n pl b BI Hk Hra Hpre Hsn Hres Hro Hfrm Hn HC.
  destruct BI as (SEGS & _ & _ & HGG & _ & AX).
  pose proof Hpre as (HM & HW & HB & HID & Hra1 & Hal & Hceil & H63 & Hstw & Htp & Herr & Hp & Hn1 & Hpl & Hrod).
  pose proof (lf_fr_init B API stk empty L A regs mem md ra p n Hpre Hro) as FR0.
  unfold LLVM_K, LLVM_FRAME, CL_STACK, CL_FRAME, ALLOC_STACK in Hk.
  pose proof YM05.alloc_ceiling_value as Hac. pose proof lf_ceiling as Hrt.
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  assert (Esp : spZ regs = bv_unsigned (reg_get regs 2)) by reflexivity.
  assert (E11 : YK11.getr regs 11 = reg_get regs 11) by reflexivity.
  assert (E1 : YK11.getr regs 1 = reg_get regs 1) by reflexivity.
  pose proof (bv_unsigned_in_range _ (reg_get regs 2)) as Rsp. unfold bv_modulus in Rsp.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  assert (HN64 : 0 <= n < 2 ^ 64).
  { rewrite Hn. pose proof (Zle_0_nat (length pl)). split; [lia|].
    destruct Hpl as [[-> _]|[Hn0 (q & Hq & _)]]; [lia|].
    destruct (mr_blocks B _ (aa_laws API) L A mem md q n 0 HM Hq ltac:(lia)) as (_ & H1 & H2 & _). lia. }
  rewrite SEGS.
  eapply (llvm_run_norm_cf B SEGS fx regs (Z_to_bv 64 LLVM_ENTRY) mem md); [exact Hh | exact Hl | exact Hro | | |].
  - unfold Regs6ss.mkR_of, LLVM_ENTRY.
    assert (E10 : reg_get regs 10 = Z_to_bv 64 p) by exact Hp.
    assert (E11' : reg_get regs 11 = Z_to_bv 64 n) by exact Hn1.
    rewrite E10, E11'.
    apply (lt_early (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4)
             (reg_get regs 8) (reg_get regs 9) (reg_get regs 18) (reg_get regs 19)
             (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24)
             (reg_get regs 25) (reg_get regs 26) (reg_get regs 27)
             (reg_get regs 28) (reg_get regs 29) (reg_get regs 30) (reg_get regs 31)
             (@fp_regs fx) (@fp_csr fx) (normalize rsegs mem) p n (spZ regs - stk) pl).
    all: try exact HC. all: try (symmetry; exact Hn). all: try apply mem_inv_normalize. all: try lia.
    apply lf_stk; [lia | lia |].
    intros a Ha. unfold writable_at.
    assert (Hni : ~ in_img B a) by (intros Hi; pose proof (lf_in_img_top B a SEGS Hi); lia).
    rewrite (wview_rel_rw rsegs mem (normalize rsegs mem) _ (mem_rel_normalize rsegs mem Hro)
               (lf_ro_addr_out B a SEGS Hni ltac:(lia))).
    pose proof (Hstw a Ha) as HWa. unfold writable_at in HWa. rewrite SEGS in HWa. exact HWa.
  - intros ms (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & u3' & u4' & u5' & u6' & m'' & -> & _). do 5 eexists. reflexivity.
  - intros R F pc' fc m0' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & u3' & u4' & u5' & u6' & m'' & HE & MU & WM) regs' m' Hx Hrel Hsame.
    injection HE as ER EF EP EC EM. subst R F pc' fc m0'.
    apply (SRcf_ret B).
    assert (MU' : munch [(bv_unsigned (reg_get regs 2) - 64, bv_unsigned (reg_get regs 2))] mem m')
      by exact (munch_rel rsegs _ mem (normalize rsegs mem) m' m'' (mem_rel_normalize rsegs mem Hro) Hrel Hsame MU).
    assert (WM' : wmono rsegs mem m')
      by exact (wmono_rel rsegs mem (normalize rsegs mem) m' m'' (mem_rel_normalize rsegs mem Hro) Hrel Hsame WM).
    assert (Hro' : ro_agree rsegs m') by exact (ro_agree_same rsegs mem m' Hro Hsame).
    assert (FR1 : lf_fr B API stk (spZ regs) L A mem md L A m' md).
    { eapply (lf_fr_evt B API SEGS AX HGG); [exact FR0 | lia | lia | exact MU' | exact WM' | exact Hro' |].
      intros x Hx0 NO. left.
      destruct (Z_le_dec (spZ regs - 64) x); destruct (Z_lt_dec x (spZ regs)); try lia;
        exfalso; apply NO; cbn [Frame.outside]; (split; [lia | exact I]). }
    assert (G10 : YK11.getr regs' 10 = Z_to_bv 64 (lock_ret pl)).
    { rewrite (lf_getr_eqv _ _ _ Hx). rewrite (lock_ret_early n pl ltac:(symmetry; exact Hn) HC).
      reflexivity. }
    assert (RP : regs_preserved regs regs').
    { intros r Hr. rewrite (lf_getr_eqv _ _ _ Hx). unfold callee_saved in Hr.
      assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
                    r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      repeat (destruct Hr' as [-> | Hr']; [reflexivity|]). subst. reflexivity. }
    destruct (lf_post B API SINK stk empty L A regs mem md ra p n (lock_ret pl) L A regs' m' md Hpre Hsn FR1 G10 RP)
      as (Hpost & Hsn' & Hpay & MI2).
    exists (mkFP fp_regs fp_csr), L, A, regs', m', md.
    split; [rewrite SEGS, <- E1, Hra1, (lf_ret_pc _ Hra); reflexivity|].
    split; [exact Hfrm|]. split; [exact Hpost|]. split; [exact Hsn'|].
    split; [exact Hres|]. split; [exact Hpay|]. split; [exact MI2 | exact I].
Qed.

Theorem LLVMFuzzerTestOneInput_holds_cf : LLVMFuzzerTestOneInput_sr_contract_cf B API.
Proof.
  intros BI j Hj ra empty stk Hk Hra L A regs mem md p n pl b Hpre Hn Hpl Hsn Hsp Hres Hroom Hro Hrelro HGI Hfrm.
  destruct (Z_lt_le_dec n 2) as [H2|H2]; [ | destruct (Z_le_gt_dec (2 ^ 26) n) as [H26|H26] ].
  1,2: exact (llvm_early_cf j stk empty L A regs mem md ra p n pl b BI Hk Hra Hpre Hsn Hres Hro Hfrm Hn
                ltac:(lia)).
  (* the size is in range: the harness reads the name and calls check_no_overread and check_lookup *)
  pose proof BI as (SEGS & HMAL & HFRE & HGG & HG & AX).
  pose proof Hpre as (HM & HW & HB & HID & Hra1 & Hal & Hceil & H63 & Hstw & Htp & Herr & Hp & Hn1 & Hpl0 & Hrod).
  pose proof (lf_fr_init B API stk empty L A regs mem md ra p n Hpre Hro) as FR0.
  unfold LLVM_K, LLVM_FRAME, CL_STACK, CL_FRAME, ALLOC_STACK in Hk.
  pose proof YM05.alloc_ceiling_value as Hac. pose proof lf_ceiling as Hrt.
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  assert (Esp : spZ regs = bv_unsigned (reg_get regs 2)) by reflexivity.
  pose proof (bv_unsigned_in_range _ (reg_get regs 2)) as Rsp. unfold bv_modulus in Rsp.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  assert (HPB : In (p, n) (blocks L A) /\ 4096 <= p /\ p + n <= YM05.alloc_ceiling).
  { destruct Hpl0 as [[-> Hn0]|[Hn0 (q & Hq & Hqp)]]; [lia|].
    pose proof (mr_blocks_range B _ (aa_laws API) L A mem md q n HM Hq) as (R1 & R2). rewrite Hqp in R1, R2.
    split; [apply blocks_In; exists q; split; [exact Hqp | exact Hq]|]. lia. }
  destruct HPB as (HPin & HP4 & HPc).
  assert (BLm : bytes_at rsegs (normalize rsegs mem) p pl).
  { apply bytes_at_normalize; [exact Hro|]. apply (blk_bytes_at B); [exact SEGS | lia | lia | exact Hpl]. }
  assert (E10 : reg_get regs 10 = Z_to_bv 64 p) by exact Hp.
  assert (E11 : reg_get regs 11 = Z_to_bv 64 n) by exact Hn1.
  assert (E1 : YK11.getr regs 1 = reg_get regs 1) by reflexivity.
  rewrite SEGS.
  eapply (g_run_cf B API SEGS AX HGG stk (spZ regs) L A mem md fx regs (Z_to_bv 64 LLVM_ENTRY) mem md L A);
    [ exact FR0 | lia | lia | | | ].
  - unfold Regs6ss.mkR_of, LLVM_ENTRY. rewrite E10, E11.
    apply (lt_entry (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4)
             (reg_get regs 8) (reg_get regs 9) (reg_get regs 18) (reg_get regs 19)
             (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24)
             (reg_get regs 25) (reg_get regs 26) (reg_get regs 27)
             (reg_get regs 28) (reg_get regs 29) (reg_get regs 30) (reg_get regs 31)
             (@fp_regs fx) (@fp_csr fx) (normalize rsegs mem) p n (spZ regs - stk) pl).
    all: try exact BLm. all: try (symmetry; exact Hn). all: try apply mem_inv_normalize. all: try lia.
    apply lf_stk; [lia | lia |].
    intros a Ha. unfold writable_at.
    assert (Hni : ~ in_img B a) by (intros Hi; pose proof (lf_in_img_top B a SEGS Hi); lia).
    rewrite (wview_rel_rw rsegs mem (normalize rsegs mem) _ (mem_rel_normalize rsegs mem Hro)
               (lf_ro_addr_out B a SEGS Hni ltac:(lia))).
    pose proof (Hstw a Ha) as HWa. unfold writable_at in HWa. rewrite SEGS in HWa. exact HWa.
  - intros ms Hms. destruct Hms as [Hret|Hcall].
    + destruct Hret as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & u3' & u4' & u5' & u6' & m'' & -> & MU & WM).
      exists (mkR (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) t0' t1' t2'
                (reg_get regs 8) (reg_get regs 9) (Z_to_bv 64 (lock_ret pl)) a1' a2' a3' a4' a5' a6' a7'
                (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22)
                (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27)
                u3' u4' u5' u6'),
             (@fp_regs fx), (ret_pc (reg_get regs 1)), (@fp_csr fx), m'',
             [(bv_unsigned (reg_get regs 2) - 64, bv_unsigned (reg_get regs 2))].
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
      intros x Hx NO. left. cbn [Frame.outside] in NO. lia.
    + destruct Hcall as (t0' & t1' & t2' & a4' & a5' & a6' & a7' & m'' & SL & rate & -> & Hr & Hkk & Hkn & R0 &
        HLP & BPP & EXP & BLP & FRP & MU & WM).
      do 6 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
      intros x Hx NO. left. cbn [Frame.outside] in NO. lia.
  - intros R F pc' fc m0' HQ regs1 m1 Hx Hrel FR1.
    destruct HQ as [Hret|Hcall].
    + (* the harness returned without calling: a0 = lock_ret pl *)
      destruct Hret as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & u3' & u4' & u5' & u6' & m'' & HE & MU & WM).
      injection HE as ER EF EP EC EM. subst R F pc' fc m0'.
      assert (G10 : YK11.getr regs1 10 = Z_to_bv 64 (lock_ret pl))
        by (rewrite (lf_getr_eqv _ _ _ Hx); reflexivity).
      assert (RP : regs_preserved regs regs1).
      { intros r Hcs. rewrite (lf_getr_eqv _ _ _ Hx). unfold callee_saved in Hcs.
        assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
                      r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[-> | ->]]]]]]]]]]]]]].
        all: reflexivity. }
      rewrite <- E1.
      exact (llvm_finish_cf (mkFP (@fp_regs fx) (@fp_csr fx)) stk empty L A regs mem md ra p n (lock_ret pl)
               L A regs1 m1 md b j BI Hpre Hsn Hra Hfrm FR1 G10 RP Hres).
    + (* the call of check_no_overread *)
      destruct Hcall as (t0' & t1' & t2' & a4' & a5' & a6' & a7' & m'' & SL & rate & HE & Hr & Hkk & Hkn & R0 &
        HLP & BPP & EXP & BLP & FRP & MU & WM).
      injection HE as ER EF EP EC EM. subst R F pc' fc m0'.
      set (kk := bv_unsigned (nth 1 pl (Z_to_bv 8 0)) mod 16) in *.
      set (Pb := lt_port pl (Z.to_nat kk)) in *.
      assert (LPb : Z.of_nat (length Pb) = kk) by (unfold Pb; rewrite lt_port_length; lia).
      assert (G1 : YK11.getr regs1 1 = Z_to_bv 64 0x12cec) by (rewrite (lf_getr_eqv _ _ _ Hx); reflexivity).
      assert (G2 : YK11.getr regs1 2 = Z_to_bv 64 (spZ regs - 64)) by (rewrite (lf_getr_eqv _ _ _ Hx); reflexivity).
      assert (G4 : YK11.getr regs1 4 = Z_to_bv 64 (ms_tp B))
        by (rewrite (lf_getr_eqv _ _ _ Hx); cbn [reg_get]; exact Htp).
      assert (G10 : YK11.getr regs1 10 = Z_to_bv 64 (p + 2 + kk)) by (rewrite (lf_getr_eqv _ _ _ Hx); reflexivity).
      assert (G11 : YK11.getr regs1 11 = Z_to_bv 64 (n - 2 - kk)) by (rewrite (lf_getr_eqv _ _ _ Hx); reflexivity).
      assert (G12 : YK11.getr regs1 12 = Z_to_bv 64 (spZ regs - 56)) by (rewrite (lf_getr_eqv _ _ _ Hx); reflexivity).
      assert (G13 : YK11.getr regs1 13 = Z_to_bv 64 rate) by (rewrite (lf_getr_eqv _ _ _ Hx); reflexivity).
      assert (Hsp1 : spZ regs1 = spZ regs - 64)
        by (unfold spZ at 1; rewrite G2; apply MState.unsigned_lit; lia).
      assert (BP1 : bytes_at rsegs m1 (spZ regs - 56) (Pb ++ Z_to_bv 8 0 :: SL))
        by exact (proj2 (bytes_at_rel rsegs m1 m'' _ _ Hrel) BPP).
      assert (BL1 : bytes_at rsegs m1 p pl) by exact (proj2 (bytes_at_rel rsegs m1 m'' _ _ Hrel) BLP).
      assert (FRC1 : rw_cells rsegs m1 (spZ regs - 40)
                [Cells.C8 (reg_get regs 19); Cells.C8 (reg_get regs 18); Cells.C8 (reg_get regs 9);
                 Cells.C8 (reg_get regs 8); Cells.C8 (reg_get regs 1)])
        by exact (lf_rw_cells_rel m1 m'' _ _ Hrel FRP).
      pose proof FR1 as (HM1 & HW1 & HB1 & HID1 & Hmd1 & Hhigh1 & Himg1 & Hblk1 & Hbyt1 & Hstw1 & Herr1 & Hgd1 & MI1).
      assert (PRE1 : call_pre_k B (aa_MR API) CNO_STACK L A regs1 m1 md).
      { apply (g_pre B API stk (spZ regs) L A mem md L A m1 md regs1 CNO_STACK FR1).
        - rewrite G1. apply ret_ok_even. reflexivity.
        - rewrite Hsp1. replace (spZ regs - 64) with (spZ regs + (-4) * 16) by lia.
          rewrite Z.mod_add by lia. exact Hal.
        - rewrite Hsp1. unfold CNO_STACK, CNO_FRAME, ALLOC_STACK. lia.
        - lia.
        - unfold CNO_STACK, CNO_FRAME, ALLOC_STACK. lia.
        - lia.
        - lia.
        - exact G4. }
      assert (TSPL : pl = firstn (2 + Z.to_nat kk) pl ++ skipn (2 + Z.to_nat kk) pl)
        by (rewrite firstn_skipn; reflexivity).
      assert (LTF : length (firstn (2 + Z.to_nat kk) pl) = (2 + Z.to_nat kk)%nat)
        by (rewrite length_firstn; lia).
      assert (BT1 : bytes_at rsegs m1 (p + 2 + kk) (skipn (2 + Z.to_nat kk) pl)).
      { rewrite TSPL in BL1. apply bytes_at_app in BL1 as [_ BL1]. rewrite LTF in BL1.
        replace (p + Z.of_nat (2 + Z.to_nat kk)) with (p + 2 + kk) in BL1 by lia. exact BL1. }
      assert (HL16 : Z.of_nat (length (Pb ++ Z_to_bv 8 0 :: SL)) = 16) by (rewrite HLP; reflexivity).
      (* check_no_overread, 0x12d2c *)
      rewrite <- SEGS.
      eapply (g_check_cf B API SEGS AX ERRNO_LOW stk (spZ regs) L A mem md regs1 m1 md L A CNO_STACK b
                CHECK_NO_OVERREAD);
        [ exact FR1 | lia | lia | rewrite Hsp1; unfold CNO_STACK, CNO_FRAME, ALLOC_STACK; lia
        | lia | unfold CNO_STACK, CNO_FRAME, ALLOC_STACK; lia | | ].
      { apply (CNO (mkFP (@fp_regs fx) (@fp_csr fx)) L A regs1 m1 md (p + 2 + kk) (n - 2 - kk)
                 (spZ regs - 56) rate (skipn (2 + Z.to_nat kk) pl) Pb SL b).
        all: first
          [ exact SEGS | exact PRE1 | exact G10 | exact G11 | exact G12 | exact G13
          | exact HLP | exact Hfrm | exact Hres | exact Hr
          | (rewrite length_skipn; lia)
          | (exists p, n; split; [exact (Hblk1 p n HPin) | lia])
          | (apply (bytes_at_blk B); [exact SEGS | exact BT1])
          | (apply (bytes_at_blk B); [exact SEGS | exact BP1])
          | (apply notin_zero; exact EXP)
          | exact MI1 | (rewrite SEGS; exact MI1) | (rewrite <- SEGS; exact MI1)
          | (destruct Hroom as (HR1 & HR2 & HR3); unfold llvm_room_cf in *; repeat split; lia)
          | (rewrite Hsp1; lia)
          | (Z.div_mod_to_equations; lia)
          | lia ]. }
      intros fx2 L2 A2 regs2 mem2 md2 Hfrm2 FR2 RP2 Eb2 Hres2 Habove2 Hkept2.
      (* 0x12cec-0x12d00: the call of check_lookup *)
      rewrite SEGS, G1.
      assert (G2b : YK11.getr regs2 2 = Z_to_bv 64 (spZ regs - 64)).
      { change (YK11.getr regs2 2) with (YK11.getr regs2 (Z_to_bv 5 2)).
        rewrite (RP2 2 ltac:(unfold callee_saved; lia)). exact G2. }
      assert (G4b : YK11.getr regs2 4 = Z_to_bv 64 (ms_tp B)).
      { change (YK11.getr regs2 4) with (YK11.getr regs2 (Z_to_bv 5 4)).
        rewrite (RP2 4 ltac:(unfold callee_saved; lia)). exact G4. }
      assert (Hsp2 : spZ regs2 = spZ regs - 64)
        by (unfold spZ at 1; rewrite G2b; apply MState.unsigned_lit; lia).
      assert (BP2 : bytes_at rsegs mem2 (spZ regs - 56) (Pb ++ Z_to_bv 8 0 :: SL)).
      { apply (lt_bytes_frame m1); [exact BP1|]. intros a Ha. rewrite HL16 in Ha.
        rewrite <- SEGS. exact (proj1 (Habove2 a ltac:(lia))). }
      assert (BL2 : bytes_at rsegs mem2 p pl).
      { apply (lt_bytes_frame m1); [exact BL1|]. intros a Ha.
        rewrite <- SEGS. replace a with (p + (a - p)) by lia.
        exact (Hkept2 p n (a - p) HPin (fun H => H) ltac:(lia)). }
      assert (FRC2 : rw_cells rsegs mem2 (spZ regs - 40)
                [Cells.C8 (reg_get regs 19); Cells.C8 (reg_get regs 18); Cells.C8 (reg_get regs 9);
                 Cells.C8 (reg_get regs 8); Cells.C8 (reg_get regs 1)]).
      { apply (lt_cells_frame m1); [exact FRC1|]. intros a Ha.
        cbn [cells_size csize Nat.add] in Ha. rewrite <- SEGS. apply Habove2. rewrite Hsp1. lia. }
      pose proof FR2 as (HM2 & HW2 & HB2 & HID2 & Hmd2 & Hhigh2 & Himg2 & Hblk2 & Hbyt2 & Hstw2 & Herr2 & Hgd2 & MI2).
      assert (R2a : reg_get regs2 2 = Z_to_bv 64 (spZ regs - 64)) by exact G2b.
      assert (R2b : reg_get regs2 8 = Z_to_bv 64 kk).
      { change (reg_get regs2 8) with (YK11.getr regs2 (Z_to_bv 5 8)).
        rewrite (RP2 8 ltac:(unfold callee_saved; lia)). rewrite (lf_getr_eqv _ _ _ Hx). reflexivity. }
      assert (R2c : reg_get regs2 9 = Z_to_bv 64 rate).
      { change (reg_get regs2 9) with (YK11.getr regs2 (Z_to_bv 5 9)).
        rewrite (RP2 9 ltac:(unfold callee_saved; lia)). rewrite (lf_getr_eqv _ _ _ Hx). reflexivity. }
      assert (R2d : reg_get regs2 18 = Z_to_bv 64 (p + 2 + kk)).
      { change (reg_get regs2 18) with (YK11.getr regs2 (Z_to_bv 5 18)).
        rewrite (RP2 18 ltac:(unfold callee_saved; lia)). rewrite (lf_getr_eqv _ _ _ Hx). reflexivity. }
      assert (R2e : reg_get regs2 19 = Z_to_bv 64 (n - 2 - kk)).
      { change (reg_get regs2 19) with (YK11.getr regs2 (Z_to_bv 5 19)).
        rewrite (RP2 19 ltac:(unfold callee_saved; lia)). rewrite (lf_getr_eqv _ _ _ Hx). reflexivity. }
      eapply (g_run_cf B API SEGS AX HGG stk (spZ regs) L A mem md fx2 regs2 (Z_to_bv 64 0x12cec) mem2 md2 L2 A2);
        [ exact FR2 | lia | lia | | | ].
      { unfold Regs6ss.mkR_of. rewrite R2a, R2b, R2c, R2d, R2e. apply lt_mid. }
      { intros ms (t0'' & t1'' & t2'' & a5'' & a6'' & a7'' & ->).
        do 5 eexists. exists (@nil ivl).
        split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
        intros x Hx0 NO. exfalso. apply NO. exact I. }
      intros R3 F3 pc3 fc3 m3' HQ3 regs3 m3 Hx3 Hrel3 FR3.
      destruct HQ3 as (t0'' & t1'' & t2'' & a5'' & a6'' & a7'' & HE3).
      injection HE3 as ER3 EF3 EP3 EC3 EM3. subst R3 F3 pc3 fc3 m3'.
      (* check_lookup, 0x12e34 *)
      assert (G31 : YK11.getr regs3 1 = Z_to_bv 64 0x12d04) by (rewrite (lf_getr_eqv _ _ _ Hx3); reflexivity).
      assert (G32 : YK11.getr regs3 2 = Z_to_bv 64 (spZ regs - 64)) by (rewrite (lf_getr_eqv _ _ _ Hx3); reflexivity).
      assert (G34 : YK11.getr regs3 4 = Z_to_bv 64 (ms_tp B))
        by (rewrite (lf_getr_eqv _ _ _ Hx3); cbn [reg_get]; exact G4b).
      assert (G310 : YK11.getr regs3 10 = Z_to_bv 64 (p + 2 + kk)) by (rewrite (lf_getr_eqv _ _ _ Hx3); reflexivity).
      assert (G311 : YK11.getr regs3 11 = Z_to_bv 64 (n - 2 - kk)) by (rewrite (lf_getr_eqv _ _ _ Hx3); reflexivity).
      assert (G312 : YK11.getr regs3 12 = Z_to_bv 64 (spZ regs - 56)) by (rewrite (lf_getr_eqv _ _ _ Hx3); reflexivity).
      assert (G313 : YK11.getr regs3 13 = Z_to_bv 64 kk) by (rewrite (lf_getr_eqv _ _ _ Hx3); reflexivity).
      assert (G314 : YK11.getr regs3 14 = Z_to_bv 64 rate) by (rewrite (lf_getr_eqv _ _ _ Hx3); reflexivity).
      assert (Hsp3 : spZ regs3 = spZ regs - 64)
        by (unfold spZ at 1; rewrite G32; apply MState.unsigned_lit; lia).
      pose proof FR3 as (HM3 & HW3 & HB3 & HID3 & Hmd3 & Hhigh3 & Himg3 & Hblk3 & Hbyt3 & Hstw3 & Herr3 & Hgd3 & MI3).
      assert (BP3 : bytes_at rsegs m3 (spZ regs - 56) (Pb ++ Z_to_bv 8 0 :: SL)).
      { apply (proj2 (bytes_at_rel rsegs m3 (normalize rsegs mem2) _ _ Hrel3)).
        apply bytes_at_normalize; [first [exact MI2 | rewrite SEGS; exact MI2 | rewrite <- SEGS; exact MI2] | exact BP2]. }
      assert (BL3 : bytes_at rsegs m3 p pl).
      { apply (proj2 (bytes_at_rel rsegs m3 (normalize rsegs mem2) _ _ Hrel3)).
        apply bytes_at_normalize; [first [exact MI2 | rewrite SEGS; exact MI2 | rewrite <- SEGS; exact MI2] | exact BL2]. }
      assert (FRC3 : rw_cells rsegs m3 (spZ regs - 40)
                [Cells.C8 (reg_get regs 19); Cells.C8 (reg_get regs 18); Cells.C8 (reg_get regs 9);
                 Cells.C8 (reg_get regs 8); Cells.C8 (reg_get regs 1)]).
      { apply (lf_rw_cells_rel m3 (normalize rsegs mem2) _ _ Hrel3).
        eapply (lf_rw_cells_norm B).
        - exact SEGS.
        - first [exact MI2 | rewrite SEGS; exact MI2 | rewrite <- SEGS; exact MI2].
        - intros i Hi Hin. pose proof (lf_in_img_top B _ SEGS Hin).
          cbn [cells_size csize Nat.add] in Hi. lia.
        - exact FRC2. }
      assert (BT3 : bytes_at rsegs m3 (p + 2 + kk) (skipn (2 + Z.to_nat kk) pl)).
      { rewrite TSPL in BL3. apply bytes_at_app in BL3 as [_ BL3]. rewrite LTF in BL3.
        replace (p + Z.of_nat (2 + Z.to_nat kk)) with (p + 2 + kk) in BL3 by lia. exact BL3. }
      assert (PRE3 : call_pre_k B (aa_MR API) CL_STACK L2 A2 regs3 m3 md2).
      { apply (g_pre B API stk (spZ regs) L A mem md L2 A2 m3 md2 regs3 CL_STACK FR3).
        - rewrite G31. apply ret_ok_even. reflexivity.
        - rewrite Hsp3. replace (spZ regs - 64) with (spZ regs + (-4) * 16) by lia.
          rewrite Z.mod_add by lia. exact Hal.
        - rewrite Hsp3. unfold CL_STACK, CL_FRAME, ALLOC_STACK. lia.
        - lia.
        - unfold CL_STACK, CL_FRAME, ALLOC_STACK. lia.
        - lia.
        - lia.
        - exact G34. }
      rewrite <- SEGS.
      eapply (g_check_cf B API SEGS AX ERRNO_LOW stk (spZ regs) L A mem md regs3 m3 md2 L2 A2 CL_STACK b
                CHECK_LOOKUP);
        [ exact FR3 | lia | lia | rewrite Hsp3; unfold CL_STACK, CL_FRAME, ALLOC_STACK; lia
        | lia | unfold CL_STACK, CL_FRAME, ALLOC_STACK; lia | | ].
      { apply (CL (mkFP (@fp_regs fx2) (@fp_csr fx2)) L2 A2 regs3 m3 md2 (p + 2 + kk) (n - 2 - kk)
                 (spZ regs - 56) kk rate (skipn (2 + Z.to_nat kk) pl) Pb SL b).
        all: first
          [ exact SEGS | exact PRE3 | exact G310 | exact G311 | exact G312 | exact G313 | exact G314
          | exact HLP | exact Hfrm2 | exact Hfrm | exact Hres2 | exact Hr | exact LPb
          | (rewrite length_skipn; lia)
          | (exists p, n; split; [exact (Hblk3 p n HPin) | lia])
          | (apply (bytes_at_blk B); [exact SEGS | exact BT3])
          | (apply (bytes_at_blk B); [exact SEGS | exact BP3])
          | (apply notin_zero; exact EXP)
          | exact MI3 | (rewrite SEGS; exact MI3) | (rewrite <- SEGS; exact MI3)
          | (destruct Hroom as (HR1 & HR2 & HR3') ; unfold llvm_room_cf in *; repeat split; lia)
          | (rewrite Hsp3; lia)
          | (Z.div_mod_to_equations; lia)
          | lia ]. }
      intros fx4 L4 A4 regs4 mem4 md4 Hfrm4 FR4 RP4 Eb4 Hres4 Habove4 Hkept4.
      (* 0x12d04: the harness returns 0 *)
      rewrite SEGS, G31.
      pose proof FR4 as (HM4 & HW4 & HB4 & HID4 & Hmd4 & Hhigh4 & Himg4 & Hblk4 & Hbyt4 & Hstw4 & Herr4 & Hgd4
        & MI4).
      assert (R4a : reg_get regs4 2 = Z_to_bv 64 (spZ regs - 64)).
      { change (reg_get regs4 2) with (YK11.getr regs4 (Z_to_bv 5 2)).
        rewrite (RP4 2 ltac:(unfold callee_saved; lia)). exact G32. }
      assert (FRC4 : rw_cells rsegs mem4 (spZ regs - 40)
                [Cells.C8 (reg_get regs 19); Cells.C8 (reg_get regs 18); Cells.C8 (reg_get regs 9);
                 Cells.C8 (reg_get regs 8); Cells.C8 (reg_get regs 1)]).
      { apply (lt_cells_frame m3); [exact FRC3|]. intros a Ha.
        cbn [cells_size csize Nat.add] in Ha. rewrite <- SEGS. apply Habove4. rewrite Hsp3. lia. }
      eapply (g_run_cf B API SEGS AX HGG stk (spZ regs) L A mem md fx4 regs4 (Z_to_bv 64 0x12d04) mem4 md4 L4 A4);
        [ exact FR4 | lia | lia | | | ].
      { unfold Regs6ss.mkR_of. rewrite R4a.
        eapply (lt_exit (reg_get regs 1) (reg_get regs 2) _ _ (reg_get regs 8) (reg_get regs 9)
                  (reg_get regs 18) (reg_get regs 19)).
        all: first
          [ exact R0
          | ( eapply (lf_rw_cells_norm B);
              [ exact SEGS
              | first [exact MI4 | rewrite SEGS; exact MI4 | rewrite <- SEGS; exact MI4]
              | intros i Hi Hin; pose proof (lf_in_img_top B _ SEGS Hin);
                cbn [cells_size csize Nat.add] in Hi; lia
              | exact FRC4 ])
          | apply munch_refl | apply wmono_refl
          | (symmetry; exact Hn)
          | lia ]. }
      { intros ms (t0z & t1z & t2z & a1z & a2z & a3z & a4z & a5z & a6z & a7z & u3z & u4z & u5z & u6z & mz & -> &
          MUz & WMz).
        do 5 eexists. exists [(bv_unsigned (reg_get regs 2) - 64, bv_unsigned (reg_get regs 2))].
        split; [reflexivity|]. split; [exact MUz|]. split; [exact WMz|].
        intros x Hx0 NO. left. cbn [Frame.outside] in NO. lia. }
      intros R5 F5 pc5 fc5 m5' HQ5 regs5 m5 Hx5 Hrel5 FR5.
      destruct HQ5 as (t0z & t1z & t2z & a1z & a2z & a3z & a4z & a5z & a6z & a7z & u3z & u4z & u5z & u6z & mz & HE5 &
        MUz & WMz).
      injection HE5 as ER5 EF5 EP5 EC5 EM5. subst R5 F5 pc5 fc5 m5'.
      assert (G510 : YK11.getr regs5 10 = Z_to_bv 64 (lock_ret pl)).
      { rewrite (lf_getr_eqv _ _ _ Hx5). rewrite R0. reflexivity. }
      assert (RP5 : regs_preserved regs regs5).
      { intros r Hcs. unfold callee_saved in Hcs.
        assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
                      r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[-> | ->]]]]]]]]]]]]]].
        all: rewrite (lf_getr_eqv _ _ _ Hx5).
        all: first
          [ reflexivity
          | lazymatch goal with |- YK11.getr _ (Z_to_bv 5 ?k) = _ =>
              etransitivity; [ exact (RP4 k ltac:(unfold callee_saved; lia)) | ];
              rewrite (lf_getr_eqv _ _ _ Hx3);
              etransitivity; [ exact (RP2 k ltac:(unfold callee_saved; lia)) | ];
              rewrite (lf_getr_eqv _ _ _ Hx); reflexivity
            end ]. }
      rewrite <- E1.
      exact (llvm_finish_cf (mkFP (@fp_regs fx4) (@fp_csr fx4)) stk empty L A regs mem md ra p n (lock_ret pl)
               L4 A4 regs5 m5 md4 b j BI Hpre Hsn Hra Hfrm4 FR5 G510 RP5 Hres4).
Qed.

End C.
