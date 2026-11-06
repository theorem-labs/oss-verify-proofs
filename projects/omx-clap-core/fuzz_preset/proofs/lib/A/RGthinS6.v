(* Modified by Theorem Labs, 2026-10-29: relocated from proofs/plugin-hostd/fuzz_reply/lib/A/RGthinS6.v (hub 66a127cb11e, blob 4492b7e5dbf7) to omx-clap-core/fuzz_preset's asan image A by a Theorem Labs lane's internal file alreloc.py (frozen-c4338d099cfb8025), module paths and every image numeral moved by symbol + offset; QA's bound ASAN_CEIL + 16 <= a -> ASAN_CEIL <= a after RTlaws.rl_stack's change; record, the internal file A5.md. *)
(* fuzz_preset.asan image A: the thin segment S6 (RGtop.seg_npost): Allocate's return into asan_realloc (its NULL-input
   call) -> realloc's return with a0 = the result, over the machine runs RGthinM2.m6a (a block) and RGthinM2.m6b (NULL:
   errno = ENOMEM through SetErrnoToENOMEM).  Ported from cgif_rgb's YF68.v:104 c_null and the asan_realloc
   epilogue of YF78, relocated to fuzz_reply's image. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import AllocG DeallocG ReallocG RGtop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import RGthinK RGthinM RGthinM2 RGthinS.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YP03.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section b.
Variable B : asyms.
Variable U : list Z -> astate -> Prop.
Variable ARX : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variable nmax lmax : Z.
Variable lpost : astate -> Prop.
Variable rU : list Z -> astate -> Prop.
Variable RSTACK : Z.
Variable rpreA : astate -> Z -> Prop.
Hypothesis LAWS : RTlaws B ARX AOX.
Hypothesis HTP : as_tp B = RT_TP.

Theorem rt_seg_npost : seg_npost tfibsegs B U ARX AOX rpre nmax lmax lpost rU RSTACK rpreA RT_PC0 RT_INST RT_OOM Knr.
Proof.
unfold seg_npost.
intros HTIE ly S W regs mem md n ch S1 W1 so bp regsA memA mdA q ly2 S2 W2 regs2 mem2 md2 ENT HKn APR APO A02 LP2 OOM HQB.
(* errno's address: the tie (seg_npost's premise) with the image's tp. *)
assert (HERR : as_errno B = RT_ERRNO) by (rewrite HTIE, HTP; unfold RT_TP, RT_ERRNO; lia).
unfold rnentry, realloc_pre in ENT.
destruct ENT as ((ARX0 & Hra & Hsp16 & Hlo & Hbot & Hhi & HWIN & Hgp & Htp & HCH) & RP & HA0 & HA1 & HN & HL & HU).
unfold Knr in HKn. destruct HKn as (KSP & K1ra & KK & KF & KW).
pose proof (proj1 APR) as ARX1.
unfold alloc_post in APO. destruct APO as (ARX2 & LLE & WLE & PRS & SIO & FR2 & FR2w & PR2).
set (sp0 := spZ regs) in *. set (qa := sptr_addr B ly2 q) in *.
destruct LLE as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof (fun a => rl_stack _ _ _ LAWS ly S1 W1 memA mdA a ARX1) as STK1.
pose proof (fun a => rl_stack _ _ _ LAWS ly2 S2 W2 mem2 md2 a ARX2) as STK2.
pose proof (proj2 (rl_stack _ _ _ LAWS ly S W mem md (ly_stk_lo ly) ARX0 ltac:(unfold ASTACK in Hlo; lia))) as SLO.
pose proof (rl_stkhi _ _ _ LAWS ly S W mem md ARX0) as SHI. unfold kHighMemEnd in SHI.
pose proof (proj1 ASAN_CEIL_range) as CR. unfold ASTACK in Hlo, HWIN.
assert (QA : forall a, ASAN_CEIL <= a -> ~ (q <> PNull /\ qa <= a < qa + req_size n)).
{ intros a Ha [Hne Hin]. destruct (rl_blk _ _ _ LAWS ly2 S2 W2 mem2 md2 q n ARX2 (HQB Hne)) as (_ & X2 & _).
  fold qa in X2. lia. }
assert (RAA : raZ regsA = RT_RA_NA) by (unfold raZ; rewrite K1ra; unfold w64; apply YP03.unsigned_lit_small; unfold RT_RA_NA; lia).
assert (STKV : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> ~ (sp0 - 2160 - 4096 <= a < sp0 - 2160) ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W1) memA a).
{ intros a Ha Hn. apply FR2.
  - lia.
  - exact (proj1 (STK1 a Ha)).
  - exact (proj1 (STK2 a ltac:(rewrite Eslo, Eshi; exact Ha))).
  - unfold ascratch. rewrite HERR. intros [X|X]; [rewrite KSP in X; unfold AFSTACK_G in X; lia | unfold RT_ERRNO in X; lia].
  - apply QA. lia. }
assert (XF : forall a v, ly_stk_lo ly <= a -> a + 8 <= ly_stk_hi ly -> sp0 - 2160 <= a ->
  val_mem tfibsegs (mrestrict (w_H W1) memA) a 8 v -> val_mem tfibsegs (mrestrict (w_H W2) mem2) a 8 v).
{ intros a v H1 H2 H3 V. apply (val_mem_xfer (w_H W1) (w_H W2) memA mem2 a 8 v); [|exact V]. intros k Hk. apply STKV; lia. }
assert (PW2 : forall a, sp0 - 16384 <= a < sp0 -> apresent (w_H W2) mem2 a).
{ intros a Ha. destruct (Z_le_gt_dec (sp0 - 2160) a) as [L|L]; [|destruct (Z_le_gt_dec (sp0 - 2160 - 4096) a) as [L2|L2]].
  - apply vis_apresent_hi; [unfold TFIB_IMG_END; lia|]. rewrite STKV by lia. apply apresent_vis. apply KW. unfold ASTACK. fold sp0. lia.
  - apply PR2. rewrite KSP. unfold AFSTACK_G. lia.
  - apply vis_apresent_hi; [unfold TFIB_IMG_END; lia|]. rewrite STKV by lia. apply apresent_vis. apply KW. unfold ASTACK. fold sp0. lia. }
destruct KF as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
assert (SP2 : spZ regs2 = sp0 - 2160)
  by (unfold spZ; rewrite (ap_get regsA regs2 2 2%bv PRS ltac:(unfold acallee_saved; lia) eq_refl); exact KSP).
assert (AFR : afr_ok W2 mem2 (sp0 - 2160)) by (unfold afr_ok; apply XF; [lia | lia | lia | eapply val_mem_addr; [exact F0 | lia]]).
assert (IFR : ifr_ok W2 mem2 (sp0 - 2160 + 2096) (raZ regs) (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9))
  (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19)) (bv_unsigned (getr regs 20)) (bv_unsigned (getr regs 21))
  (bv_unsigned (getr regs 22)))
  by (unfold ifr_ok; repeat split; (apply XF; [lia | lia | lia | eapply val_mem_addr; [eassumption | lia]])).
assert (RNG : Forall (fun v => 0 <= v < 2 ^ 64) [0; 0; 0; 0; 0; raZ regs; bv_unsigned (getr regs 8); bv_unsigned (getr regs 9);
  bv_unsigned (getr regs 18); bv_unsigned (getr regs 19); bv_unsigned (getr regs 20); bv_unsigned (getr regs 21);
  bv_unsigned (getr regs 22)])
  by (repeat (apply Forall_cons; [first [lia | apply u64_range]|]); apply Forall_nil).
assert (HRET : YK0s.ret_ok (w64 (raZ regs))) by (unfold raZ; rewrite w64_unsigned; exact Hra).
rewrite RAA. unfold cfg_at at 1.
destruct (rg_null_dec q) as [EQ|HQ].
- (* q = PNull: a0 = 0, errno := ENOMEM *)
  assert (A0 : getr regs2 10 = w64 0)
    by (rewrite A02; change qa with (sptr_addr B ly2 q); rewrite EQ; cbn [sptr_addr sptr_exp aeval]; reflexivity).
  eapply SRr_mono.
  { apply (m6b W2 md2 regs2 mem2 (sp0 - 2160) (raZ regs) (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9))
      (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19)) (bv_unsigned (getr regs 20)) (bv_unsigned (getr regs 21))
      (bv_unsigned (getr regs 22))).
    - exact SP2.
    - lia.
    - lia.
    - exact A0.
    - rewrite (ap_get regsA regs2 4 4%bv PRS ltac:(unfold acallee_saved; lia) eq_refl), (KK 4%bv ltac:(cbn; tauto)), Htp, HTP. reflexivity.
    - exact RNG.
    - exact AFR.
    - exact IFR.
    - intros a Ha. apply PW2. lia.
    - exact HRET. }
  intros W' c' _ POST. destruct POST as (EW & regs' & mem' & mat & Ec & (MR1 & MR2 & MR3 & MR4) & G2 & G1 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G10 & GK).
  subst W' c'.
  exists regs', mem', (with_vm_backing (m_vm_lazy md2) mat md2).
  split; [unfold cfg_at; reflexivity|].
  split.
  { apply ap_mk. cs_cases.
    - rewrite G2. assert (E : sp0 - 2160 + 2160 = bv_unsigned (getr regs 2)) by (subst sp0; unfold spZ; lia).
      rewrite E, w64_unsigned. reflexivity.
    - rewrite (GK 3%bv ltac:(cbn; tauto)), (ap_get regsA regs2 3 3%bv PRS ltac:(unfold acallee_saved; lia) eq_refl). exact (KK 3%bv ltac:(cbn; tauto)).
    - rewrite (GK 4%bv ltac:(cbn; tauto)), (ap_get regsA regs2 4 4%bv PRS ltac:(unfold acallee_saved; lia) eq_refl). exact (KK 4%bv ltac:(cbn; tauto)).
    - rewrite G8, w64_unsigned. reflexivity.
    - rewrite G9, w64_unsigned. reflexivity.
    - rewrite G18, w64_unsigned. reflexivity.
    - rewrite G19, w64_unsigned. reflexivity.
    - rewrite G20, w64_unsigned. reflexivity.
    - rewrite G21, w64_unsigned. reflexivity.
    - rewrite G22, w64_unsigned. reflexivity.
    - rewrite (GK 23%bv ltac:(cbn; tauto)), (ap_get regsA regs2 23 23%bv PRS ltac:(unfold acallee_saved; lia) eq_refl). exact (KK 23%bv ltac:(cbn; tauto)).
    - rewrite (GK 24%bv ltac:(cbn; tauto)), (ap_get regsA regs2 24 24%bv PRS ltac:(unfold acallee_saved; lia) eq_refl). exact (KK 24%bv ltac:(cbn; tauto)).
    - rewrite (GK 25%bv ltac:(cbn; tauto)), (ap_get regsA regs2 25 25%bv PRS ltac:(unfold acallee_saved; lia) eq_refl). exact (KK 25%bv ltac:(cbn; tauto)).
    - rewrite (GK 26%bv ltac:(cbn; tauto)), (ap_get regsA regs2 26 26%bv PRS ltac:(unfold acallee_saved; lia) eq_refl). exact (KK 26%bv ltac:(cbn; tauto)).
    - rewrite (GK 27%bv ltac:(cbn; tauto)), (ap_get regsA regs2 27 27%bv PRS ltac:(unfold acallee_saved; lia) eq_refl). exact (KK 27%bv ltac:(cbn; tauto)). }
  split. { rewrite G10. change qa with (sptr_addr B ly2 q). rewrite EQ. cbn [sptr_addr sptr_exp aeval]. reflexivity. }
  split.
  { apply (rl_write _ _ _ LAWS ly2 S2 W2 mem2 md2 mem' _ ARX2).
    - intros x Hst Her _. apply MR1; [|exact Her]. rewrite Eslo, Eshi in Hst. intros Hin. apply Hst. lia.
    - intros a Ha Hv. exact (MR4 a Ha Hv).
    - apply sbm_wvb. }
  split; [apply same_io_wvb|].
  split.
  { unfold rkeep. split.
    - intros a Ha Hs. apply aview_same. apply MR1.
      + intros Hin. apply Hs. unfold ascratch. left. fold sp0. unfold ASTACK.
        rewrite YP03.unsigned_lit_small in Hin by lia. lia.
      + intros Hin. apply Hs. unfold ascratch. right. rewrite HERR.
        rewrite YP03.unsigned_lit_small in Hin by lia. lia.
    - intros x Hs. apply MR1.
      + intros Hin. apply Hs. unfold ascratch. left. fold sp0. unfold ASTACK. lia.
      + intros Hin. apply Hs. unfold ascratch. right. rewrite HERR. lia. }
  split.
  { unfold rwin. intros a Ha. fold sp0 in Ha. unfold ASTACK in Ha.
    destruct (Z_le_gt_dec (sp0 - 2176) a) as [L|L]; [destruct (Z_lt_ge_dec a (sp0 - 2160)) as [L2|L2]|].
    - apply MR3. lia.
    - apply (apresent_same (w_H W2) mem2 mem' a); [apply MR1; [rewrite YP03.unsigned_lit_small by lia; lia
        | rewrite YP03.unsigned_lit_small by lia; unfold RT_ERRNO; lia] | apply PW2; lia].
    - apply (apresent_same (w_H W2) mem2 mem' a); [apply MR1; [rewrite YP03.unsigned_lit_small by lia; lia
        | rewrite YP03.unsigned_lit_small by lia; unfold RT_ERRNO; lia] | apply PW2; lia]. }
  intros _. split; [rewrite HERR; exact MR2|].
  apply (val_mem_raw (w_H W2) mem2 mem' RT_OOM 1 1); [|exact (OOM EQ)].
  intros k Hk. apply MR1; rewrite YP03.unsigned_lit_small by (unfold RT_OOM; lia); unfold RT_OOM, RT_ERRNO in *; lia.
- (* q is a block: a0 = its address, no errno write *)
  destruct (rl_blk _ _ _ LAWS ly2 S2 W2 mem2 md2 q n ARX2 (HQB HQ)) as (Q1 & Q2 & _). fold qa in Q1, Q2.
  eapply SRr_mono.
  { apply (m6a W2 md2 regs2 mem2 (sp0 - 2160) qa (raZ regs) (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9))
      (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19)) (bv_unsigned (getr regs 20)) (bv_unsigned (getr regs 21))
      (bv_unsigned (getr regs 22))).
    - exact SP2.
    - lia.
    - lia.
    - exact A02.
    - pose proof ASAN_CEIL_range as CR2. unfold req_size in Q2. destruct (Z.eqb_spec n 0); lia.
    - exact RNG.
    - exact AFR.
    - exact IFR.
    - exact HRET. }
  intros W' c' _ POST. destruct POST as (EW & regs' & mem' & mat & Ec & MEQ & G2 & G1 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G10 & GK).
  subst W' c'.
  exists regs', mem', (with_vm_backing (m_vm_lazy md2) mat md2).
  split; [unfold cfg_at; reflexivity|].
  split.
  { apply ap_mk. cs_cases.
    - rewrite G2. assert (E : sp0 - 2160 + 2160 = bv_unsigned (getr regs 2)) by (subst sp0; unfold spZ; lia).
      rewrite E, w64_unsigned. reflexivity.
    - rewrite (GK 3%bv ltac:(cbn; tauto)), (ap_get regsA regs2 3 3%bv PRS ltac:(unfold acallee_saved; lia) eq_refl). exact (KK 3%bv ltac:(cbn; tauto)).
    - rewrite (GK 4%bv ltac:(cbn; tauto)), (ap_get regsA regs2 4 4%bv PRS ltac:(unfold acallee_saved; lia) eq_refl). exact (KK 4%bv ltac:(cbn; tauto)).
    - rewrite G8, w64_unsigned. reflexivity.
    - rewrite G9, w64_unsigned. reflexivity.
    - rewrite G18, w64_unsigned. reflexivity.
    - rewrite G19, w64_unsigned. reflexivity.
    - rewrite G20, w64_unsigned. reflexivity.
    - rewrite G21, w64_unsigned. reflexivity.
    - rewrite G22, w64_unsigned. reflexivity.
    - rewrite (GK 23%bv ltac:(cbn; tauto)), (ap_get regsA regs2 23 23%bv PRS ltac:(unfold acallee_saved; lia) eq_refl). exact (KK 23%bv ltac:(cbn; tauto)).
    - rewrite (GK 24%bv ltac:(cbn; tauto)), (ap_get regsA regs2 24 24%bv PRS ltac:(unfold acallee_saved; lia) eq_refl). exact (KK 24%bv ltac:(cbn; tauto)).
    - rewrite (GK 25%bv ltac:(cbn; tauto)), (ap_get regsA regs2 25 25%bv PRS ltac:(unfold acallee_saved; lia) eq_refl). exact (KK 25%bv ltac:(cbn; tauto)).
    - rewrite (GK 26%bv ltac:(cbn; tauto)), (ap_get regsA regs2 26 26%bv PRS ltac:(unfold acallee_saved; lia) eq_refl). exact (KK 26%bv ltac:(cbn; tauto)).
    - rewrite (GK 27%bv ltac:(cbn; tauto)), (ap_get regsA regs2 27 27%bv PRS ltac:(unfold acallee_saved; lia) eq_refl). exact (KK 27%bv ltac:(cbn; tauto)). }
  split; [exact G10|].
  split.
  { apply (rl_write _ _ _ LAWS ly2 S2 W2 mem2 md2 mem' _ ARX2);
      [intros x _ _ _; apply MEQ | intros a _ Hv; rewrite (aview_pw _ mem2 mem' a MEQ); exact Hv | apply sbm_wvb]. }
  split; [apply same_io_wvb|].
  split; [unfold rkeep; split; [intros a _ _; apply aview_pw; exact MEQ | intros x _; exact (MEQ x)]|].
  split.
  { unfold rwin. intros a Ha. fold sp0 in Ha. unfold ASTACK in Ha. apply (apresent_pw _ mem2 mem' a MEQ). apply PW2. lia. }
  intros EQ. exfalso. exact (HQ EQ).
Qed.
End b.
End a.
