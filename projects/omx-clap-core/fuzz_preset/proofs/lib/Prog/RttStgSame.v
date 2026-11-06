From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Contract KindBGlue Img0 FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import
Ledger PjStruct ReaderRes tx_put_c TxRet WriterSpec WriterValue PjWriteHyp round_trip_text_c RttDefs same_c
fuzz_alloc_ran_out_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import RttGlue RttModel RttBase RttB_Cmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require RttRunsB strtod_c.
Import ListNotations.
Local Open Scope Z_scope.

(* round_trip_text of the #102 plain twin c8f4d6b8, stage stg_same_st (RttBase.v) at 0x14eb4, fuzz_free's return:
   RttRunsB.rtt_seg5: the second out_of_memory() test (fuzz_preset.c of #102 :694-695) reads g_own_ran_out and calls
   fuzz_alloc_ran_out; both bytes are 0 here (the entry bytes, kept by every call so far: rtt_fl_inv), so neither bnez
   is taken; rc = 0 (s4); same(doc, &back) is nonzero; on to 0x14edc = stg_end_st with s2 = 1. *)
Section S.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Hypothesis HSEG : ms_segs B = rsegs.
Hypothesis FA : forall fx' : YK11.FPState, @frame_allocator rc fx' B API.
Hypothesis SAME : same_contract.
Hypothesis FRO : fuzz_alloc_ran_out_contract.
Hypothesis NEXT : stg_end_st B API F.
#[local] Set Default Proof Using "All".

Let AX : AllocExtra B (aa_MR API) := rtt_AX B API HSEG FA.
Let FG : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a :=
  rtt_FG B API HSEG FA.

Theorem stg_same_holds : stg_same_st B API F.
Proof.
  unfold stg_same_st.
  intros L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ro oo fx1 L A regs mem md Lam peak Db s2v s3v.
  cbv zeta. intros ENT FL Ero Eoo INV RG NODEb NEWb DbL LSZb NLb.
  subst ro oo.
  pose proof ENT as (REN & INIT0 & LED0 & CNT0 & RES0 & G10d & G11p & G12c & PR & NODE0 & DSUB & DOC0 & DOCS & WF &
    DEP & WLEN & COPY & ROOM).
  pose proof REN as (SEGB & TPB & ERRB & GOTB & GUARDB & PRE0 & SP47 & GT & FRM0 & RD0).
  pose proof PRE0 as (MR0 & WF0 & BD0 & RA0 & SP16 & SPC & SP63 & WIN0 & TP0 & ERRW0 & AUX0).
  pose proof INV as (RS & Z0 & INIT & RD & FRM & FREG & LED & PK & PERM & NODE & RES & _).
  pose proof RS as (MRc & WFc & BDc & _ & PSc & _ & _ & _ & _ & WRc).
  pose proof RG as (R2 & R8 & R9 & R18 & R19 & R20 & R21 & R3 & R4 & R22).
  destruct (rtt_fl_inv B API F HSEG FA L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D 0 0 fx1 L A mem md
    _ _ _ _ _ ENT INV FL) as (_ & _ & BRO & BOO).
  set (p := negb (pretty =? 0)) in *.
  pose proof alloc_ceiling_val as HCV.
  assert (HRK : RTT_K = 13808) by (vm_compute; reflexivity).
  assert (HPK : PJ_PARSE_K = 13648) by (vm_compute; reflexivity).
  assert (HERR : errno_addr B = strtod_c.STRTOD_ERRNO) by exact ERRB. unfold strtod_c.STRTOD_ERRNO in HERR.
  assert (HSK : 0 <= same_k t <= 2640) by (unfold same_k, SAME_FS; lia).
  assert (DL : forall bk, In bk D -> In bk Lam).
  { intros bk Hb. apply (lb_perm_in _ _ _ bk PERM). right. exact (DSUB bk Hb). }
  destruct (kb_md B API L A mem md MRc) as (Hh & Hz).
  assert (RA : ro_agree (ms_segs B) mem) by exact (proj1 RD).
  assert (MREL : mem_rel (ms_segs B) mem (normalize (ms_segs B) mem)) by exact (mem_rel_normalize _ mem RA).
  assert (NB : forall a bs, Mem.bytes_at (ms_segs B) mem a bs -> Mem.bytes_at rsegs (normalize rsegs mem) a bs).
  { intros a bs Hb. rewrite <- HSEG. exact (proj1 (bytes_at_rel _ _ _ a bs MREL) Hb). }
  assert (NDn : pj_node rsegs (normalize rsegs mem) (lin Lam) doc t D).
  { rewrite <- HSEG. apply (lb_node_norm B API HSEG FA L A mem md Lam peak _ _ doc t D MRc LED DL RA); [lia | exact NODE]. }
  assert (NBn : pj_node rsegs (normalize rsegs mem) (lin Lam) (spZ regs0 - 112) t Db).
  { rewrite <- HSEG. apply (lb_node_norm B API HSEG FA L A mem md Lam peak _ _ (spZ regs0 - 112) t Db MRc LED DbL RA);
      [lia | exact NODEb]. }
  assert (STKn : Frame.stk rsegs (normalize rsegs mem) (spZ regs0 - 112 - same_k t) (spZ regs0 - 112)).
  { rewrite <- HSEG.
    assert (HWw : forall a, spZ regs0 - 112 - same_k t <= a < spZ regs0 - 112 -> writable_at (ms_segs B) mem a)
      by (intros a Ha; apply WRc; unfold rwin; left; lia).
    exact (proj2 (lb_stk_win B API HSEG FA mem (spZ regs0 - 112 - same_k t) (spZ regs0 - 112) ltac:(lia) ltac:(lia) HWw)). }
  assert (OUTd : forall z, pj_foot doc D z -> Frame.outside [(spZ regs0 - 112 - same_k t, spZ regs0 - 112)] z).
  { intros z Hf. destruct (lb_foot B API HSEG FA L A mem md Lam peak _ _ doc D z MRc LED DL Hf) as [H|H];
      apply outside_one; lia. }
  assert (OUTb : forall z, pj_foot (spZ regs0 - 112) Db z ->
      Frame.outside [(spZ regs0 - 112 - same_k t, spZ regs0 - 112)] z).
  { intros z Hf. destruct (lb_foot B API HSEG FA L A mem md Lam peak _ _ (spZ regs0 - 112) Db z MRc LED DbL Hf) as [H|H];
      apply outside_one; lia. }
  pose proof (lb_node_top _ _ _ _ _ _ NODE0) as DOCT.
  pose proof (lb_node_top _ _ _ _ _ _ NODEb) as BACKT.
  eapply (lb_run B API HSEG FA fx1 regs (Z_to_bv 64 0x14eb4) mem md _ _ Hh Hz RA).
  { unfold rmk. rewrite R2, R20, R21.
    apply (RttRunsB.rtt_seg5 SAME FRO (getr regs 1) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
      (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
      (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 22) (getr regs 23)
      (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30)
      (getr regs 31) (@fp_regs fx1) (@fp_csr fx1) (normalize rsegs mem) (spZ regs0 - 112) doc
      (spZ regs0 - 112 - same_k t) (lin Lam) t D Db);
      [lia | lia | rewrite R9; exact G10d | apply NB; exact BOO | apply NB; exact BRO | exact NDn | exact NBn |
       apply mem_inv_normalize | exact STKn | lia | exact OUTd | exact OUTb]. }
  { intros ms' (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
      _ & _ & _ & _ & _ & _ & E).
    eexists _, _, _. exact E. }
  intros R pc' m0 mem1 regs1 HQ HREL HROS HGr.
  destruct HQ as (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
    MU & WM & MI & STK' & ND' & NB' & E).
  lb_inj E R pc' m0.
  rewrite <- HSEG in MU, WM, ND', NB'.
  pose proof (munch_rel _ _ mem _ mem1 m' MREL HREL HROS MU) as MU1.
  pose proof (wmono_rel _ mem _ mem1 m' MREL HREL HROS WM) as WM1.
  pose proof (ro_agree_same _ mem mem1 RA HROS) as RA1.
  pose proof (pj_node_unnormalize B API HSEG AX FG mem1 m' (lin Lam) (spZ regs0 - 112) t Db HREL NB') as NB1.
  pose proof (@lb_inv_munch fx rc B API HSEG FA F L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D fx1 L A
    mem md Db Lam peak (cnt0 + wcalls t p + Z.of_nat (PjRoundTrip.tcalls t)) (rtt_bf F b0 cnt0 t p)
    mem1 [(spZ regs0 - 112 - same_k t, spZ regs0 - 112)] PJ_PARSE_K ENT INV MU1 WM1 RA1 ltac:(lia) ltac:(lia)
    ltac:(intros lo hi x [Ew|[]] Hx; injection Ew as <- <-; lia)) as INV1.
  apply (NEXT L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D 0 0 fx1 L A regs1 mem1 md Lam peak
    Db (Z_to_bv 64 1) s3v (Z_to_bv 64 0) (Z_to_bv 64 0x34e24) ENT FL eq_refl eq_refl INV1).
  - split; [rewrite HGr; reflexivity|].
    split; [rewrite HGr; exact R8|].
    split; [rewrite HGr; exact R9|].
    split; [rewrite HGr; reflexivity|].
    split; [rewrite HGr; exact R19|].
    split; [rewrite HGr; reflexivity|].
    split; [rewrite HGr; reflexivity|].
    split; [rewrite HGr; exact R3|].
    split; [rewrite HGr; exact R4|].
    intros r Hr. rewrite HGr, <- (R22 r Hr).
    assert (Hr' : r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hr' as [->|[->|[->|[->|[->| ->]]]]]; reflexivity.
  - exact NB1.
  - exact NEWb.
  - exact DbL.
  - exact LSZb.
  - exact NLb.
Qed.

End S.
