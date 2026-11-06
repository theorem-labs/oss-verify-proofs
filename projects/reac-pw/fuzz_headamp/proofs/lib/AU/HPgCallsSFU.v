(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address below is measured on the
   unstripped twin 1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, whose loaded sections are
   byte-equal to the pin's except .note.gnu.build-id): the CALL ADAPTERS of the image-B walk of LLVMFuzzerTestOneInput (0x80c40) at its six
   soft-float calls, in the inlined pod_nearest of segment M03 (piece value_nearest). Proves no function (kind:
   segment lemma): each lemma turns a soft-float routine's CJ contract into the step a walk lane takes at the `jal`.

   THE STATEMENTS are lib/AU/HPgM3dSFU.v's hvu_sf_ext_stmt, hvu_sf_fd_stmt, hvu_sf_sub_stmt, hvu_sf_ge_stmt and
   hvu_sf_lt_stmt (routine entries HVU_SF_EXT 0x856c0, HVU_SF_FD 0x8581c, HVU_SF_SUB 0x85940 (into __addtf3 0x85950),
   HVU_SF_GE 0x85474, HVU_SF_LT 0x853ac); hcu_sf_<routine> proves each, at every return address ret with
   4096 <= ret < 2 ^ 64 and ret mod 2 = 0. The six calls of the value piece and the lemma each takes:
     0x835cc jal __extendsftf2, ra 0x835d0                  hcu_sf_ext
     0x83600 jal __gttf2 = __getf2, ra 0x83604 (pod.h:160)   hcu_sf_ge
     0x83610 jal __floatditf, ra 0x83614                     hcu_sf_fd
     0x83624 jal __subtf3, ra 0x83628                        hcu_sf_sub
     0x83638 jal __getf2, ra 0x8363c                         hcu_sf_ge
     0x83650 jal __lttf2, ra 0x83654                         hcu_sf_lt
   Every routine's bytes are equal to image A's copy (same sizes 348, 292, 16, 1996, 188, 200).

   THE IMAGE RECORD is Section data here, as in lib/A/HPgCallsSF.v: IMG with HIMG (its segments are
   lib/AU/Img0U.v rsegs), the five symbol facts HK_EXT (key 0x200dc), HK_FD (0x7f000900), HK_SUB (0x1bc70),
   HK_GE (0x1b314), HK_LT (0x1b24c) at image B's entries, and the five contracts C_EXT, C_FD, C_SUB, C_GE, C_LT at
   IMG; lib/AU/HPgCallsSFIU.v supplies them at image B (lib/CJ/RL/I/IImgB.v, InstB.v). MTL is the meter's laws. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YK0i YK1b YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q YG05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require
PropExec MState Mem Exec Frame FP Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require CJBridge.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.Lib Require MState.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.Spec Require SoftFloat.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.Reloc Require RStep.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.G Require C_extendsftf2 C_floatditf G_subtf3 G_getf2 G_letf2.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgCalls HPgCallsSF.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgSeamNU HPgM3dSFU.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* The read agreement survives a call that keeps every byte outside a range above the image: every read-only
   byte lies in the image, below kLowMemEnd. *)
Lemma hcu_rom_view_keep : forall (W W2 : world rsegs) (memc mem2 : word -> option byte) (lo hi : Z),
kLowMemEnd <= lo -> rom_view rsegs W memc ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (lo <= x < hi) -> aview rsegs (w_H W2) mem2 x = aview rsegs (w_H W) memc x) ->
rom_view rsegs W2 mem2.
Proof.
intros W W2 memc mem2 lo hi Hlo HR Hk a Ha.
assert (Hi : in_img rsegs a) by (destruct Ha as (sg & Hin & _ & Hr); exists sg; split; [exact Hin | exact Hr]).
pose proof (hsnu_segs_low a Hi) as Hl.
pose proof asan_consts as (_ & _ & _ & _ & AC5).
rewrite Hk by lia. exact (HR a Ha).
Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

(* ======================================== the lift of one leaf call ======================================== *)
(* From hd_pre at a call with stack T (the callee uses [sp - T, sp), inside the caller's window) and the read
   agreement: a lib/Lib walk of the routine on the normalized store, which may assume the window present there
   and the two store invariants, is the routine's hd_post: the float registers all kept with a zero rounding
   mode, no write for the caller, and what the routine computes. *)
Theorem hcu_leaf_lift : forall (a T : Z) (Rr : bvmap 5 word -> Prop)
STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word),
(forall R1 R2 : bvmap 5 word, (forall r, getr R1 r = getr R2 r) -> Rr R1 -> Rr R2) ->
0 <= T ->
hd_pre rsegs B STK sp0 FP ly S W0 mem0 md0 own k T regs lyc Sc W memc mdc ->
rom_view rsegs W memc ->
(LF.stk rsegs (MN.normalize_cj rsegs (mrestrict (w_H W) memc)) (spZ regs - T) (spZ regs) ->
 LM.mem_inv rsegs (MN.normalize_cj rsegs (mrestrict (w_H W) memc)) ->
 MN.task_mem rsegs (MN.normalize_cj rsegs (mrestrict (w_H W) memc)) ->
 LEx.evt rsegs (hc_leaf_post rsegs T regs (@fp_regs fx) Rr (MN.normalize_cj rsegs (mrestrict (w_H W) memc)))
 (LMS.MS (R6.mkR_of regs) (@fp_regs fx) (Z_to_bv 64 a) (@fp_csr fx) None
  (MN.normalize_cj rsegs (mrestrict (w_H W) memc)) (LPE.seg_rom rsegs))) ->
SRr rsegs W (cfg_at rsegs a regs memc mdc)
(hd_post rsegs B MT STK sp0 FP ly S W0 mem0 md0 own k T regs lyc Sc W memc mdc
 (hd_fxk [] fx) (fun _ => False) (fun _ regs2 _ => Rr regs2)).
Proof.
intros a T Rr STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs Hext HT HPRE HRV EVF.
destruct HPRE as (HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev).
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hios & Hfrs & Hnev & Hk0 & F1 & F2 & F3 & F4
                  & Hgone & Hpres & Hstk0 & F5 & HQT).
pose proof Hstk0 as (Hsp0al & HSTK0 & Hceil & Hlolo & Hhihi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).

(* ---- the geometry of the callee's stack ---- *)
assert (Hlo_ceil : alloc_ceiling <= spZ regs - T) by lia.
assert (Hsp_hi : spZ regs <= 2 ^ 47) by lia.
assert (Hnoimg : forall x, spZ regs - T <= x < spZ regs -> ~ in_img rsegs x).
{ intros x Hx Hin. pose proof (hsnu_segs_low x Hin). lia. }

(* ---- the normalized store ---- *)
assert (HMI : LM.mem_inv rsegs (MN.normalize_cj rsegs (mrestrict (w_H W) memc)))
  by (apply (MN.mem_inv_cj_inv rsegs); apply MN.mem_inv_cj_normalize).
assert (HTM : MN.task_mem rsegs (MN.normalize_cj rsegs (mrestrict (w_H W) memc)))
  by (apply (MN.mem_inv_cj_task rsegs); apply MN.mem_inv_cj_normalize).
assert (HSTKm : LF.stk rsegs (MN.normalize_cj rsegs (mrestrict (w_H W) memc)) (spZ regs - T) (spZ regs)).
{ split; [lia|]. split; [lia|]. intros x Hx.
  destruct (Hpres x ltac:(lia)) as (HH & bb & Hbb).
  assert (Em : MN.normalize_cj rsegs (mrestrict (w_H W) memc) (LM.wa x) = Some bb).
  { unfold MN.normalize_cj. rewrite (hsnu_keep x ltac:(unfold TASK_SIZE; lia) (Hnoimg x Hx)).
    unfold mrestrict, LM.wa. rewrite HH. exact Hbb. }
  split; [unfold wview; rewrite Em; discriminate | exists bb; unfold LM.mrd; rewrite Em; reflexivity]. }
pose proof (EVF HSTKm HMI HTM) as EVW.

(* ---- lifted into SRr ---- *)
apply (hsnu_srr_of_norm_evt W a regs memc mdc _ _ HRV EVW).
intros msf can sq model' HQ Hrel Hcjs Heqv Hsm Hcl.
destruct HQ as (R' & fc' & m' & Hsq & Hpres' & Hra' & Hfrm' & Hmu & Hstk' & HRr).
subst sq.
destruct can as [cr cfr cpc csv crv cfc cm cro].
destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & Hmrel).
cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom LMS.MS] in
  E1, E2, E3, E4, E5, E6, E7, Hmrel, Hcjs, Heqv.
subst cr cfr cpc csv crv cfc cro.
destruct msf as [fr ffr fpc fsv frv ffc fm fro].
destruct Heqv as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8).
cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in
  X1, X2, X3, X4, X5, X6, X7, X8.
subst ffr fpc fsv frv ffc fm fro.

(* the write set of the call: the callee's stack *)
pose (Wr := fun x : Z => spZ regs - T <= x < spZ regs).
assert (Wdec : forall x : Z, Wr x \/ ~ Wr x) by (intros x; unfold Wr; lia).

(* every byte outside the write set is the caller's *)
assert (KEEP : forall x : word, ~ Wr (bv_unsigned x) -> cm x = mrestrict (w_H W) memc x).
{ intros x Hx. destruct (MN.cj_drop rsegs x) eqn:Dx.
  - exact (Hcjs x Dx).
  - rewrite <- (MN.mem_rel_cj_keep rsegs cm m' x Hmrel Dx).
    rewrite (Hmu x ltac:(cbn [LF.outside]; split; [exact Hx | exact I])).
    unfold MN.normalize_cj. rewrite Dx. reflexivity. }

(* every byte of the write set is present after the call *)
assert (PRESW : forall x, Wr x -> exists bb, cm (LM.wa x) = Some bb).
{ intros x Hx. unfold Wr in Hx.
  assert (Dx : MN.cj_drop rsegs (LM.wa x) = false)
    by (apply hsnu_keep; [unfold TASK_SIZE; lia | exact (Hnoimg x Hx)]).
  destruct Hstk' as (_ & _ & Hs). destruct (Hs x Hx) as (_ & bb & Hbb).
  unfold LM.mrd in Hbb. rewrite (hsnu_rom_none x ltac:(lia) (Hnoimg x Hx)) in Hbb.
  destruct (m' (LM.wa x)) as [b0|] eqn:Em'; [|discriminate Hbb].
  exists b0. rewrite <- (MN.mem_rel_cj_keep rsegs cm m' (LM.wa x) Hmrel Dx). exact Em'. }

(* the three facts the journal's execution step asks of the new store *)
assert (HA : forall x : word, ~ Wr (bv_unsigned x) ->
  mrestrict (w_H W) (munrestrict (w_H W) memc cm) x = mrestrict (w_H W) memc x).
{ intros x Hx. rewrite hsnu_mrestrict_munrestrict.
  pose proof (KEEP x Hx) as Hk. unfold mrestrict in Hk |- *.
  destruct (w_H W x); [reflexivity | exact Hk]. }
assert (HB : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) (munrestrict (w_H W) memc cm))).
{ intros x Hx. rewrite hsnu_mrestrict_munrestrict. unfold mrestrict in Hx |- *.
  destruct (w_H W x) eqn:EH; [exact Hx|].
  destruct (Wdec (bv_unsigned x)) as [Hw | Hw].
  - destruct (PRESW (bv_unsigned x) Hw) as (bb & Hbb).
    unfold LM.wa in Hbb. rewrite LMS.Z_to_bv_bv_unsigned in Hbb. rewrite Hbb. discriminate.
  - pose proof (KEEP x Hw) as Hk. unfold mrestrict in Hk. rewrite EH in Hk. rewrite Hk. exact Hx. }
assert (HC : forall x : word, w_H W x = true -> munrestrict (w_H W) memc cm x = memc x).
{ intros x Hx. unfold munrestrict. rewrite Hx. reflexivity. }
assert (HD : forall x, Wr x -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own x).
{ intros x Hx. left. unfold Wr in Hx. lia. }

red.
exists (YK11.mkFP (@fp_regs fx) fc'), lyc, Sc, fr, (munrestrict (w_H W) memc cm), model'.
split.
{ unfold unrestrict.
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom].
  rewrite (hsnu_ret_pc (reg_get regs 1)
            ltac:(change (reg_get regs 1) with (getr regs 1); exact Hra)).
  reflexivity. }
split.
{ split; [intros r _; reflexivity | exact Hfrm']. }
split.
{ exact (ajournal_exec rsegs B (AR_laws_ok rsegs B) hsnu_segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
          (munrestrict (w_H W) memc cm) model' Wr HJ HA HB HC Hsm HD). }
split.
{ intros r Hr. rewrite <- (hc_getr_xeqv R' fr X1 (Z_to_bv 5 r)). exact (Hpres' r Hr). }
split; [rewrite <- (hc_getr_xeqv R' fr X1 (Z_to_bv 5 1)); exact Hra'|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [exact (same_io_materialized mdc model' Hsm)|].
split; [apply mo_le_refl; exact MTL|].
split.
{ intros x Hx Hns _.
  apply (aview_eq_of rsegs (w_H W) memc (munrestrict (w_H W) memc cm) x).
  apply HA. rewrite LMS.unsigned_lit by exact Hx. exact Hns. }
exact (Hext R' fr (hc_getr_xeqv R' fr X1) HRr).
Qed.

(* The continuation a walk gives at a soft-float site: at ra, some fx2 with every float register kept and a zero
   rounding mode, hc_core again, the callee-saved registers, frames, blocks, I/O and meter as at the call, every
   byte outside [R - T, R) as at the call, the read agreement rom_view at the returned store (so the next call's
   premise is there), and Rr of the returned registers. *)
Definition hcu_sf_k (T ret : Z) (Rr : bvmap 5 word -> Prop) (Q : world rsegs -> config -> Prop)
STK sp0 FP ly S W0 mem0 md0 own k lyc Sc (W : world rsegs) memc mdc (regs : bvmap 5 word) (R : Z) : Prop :=
forall W2 (fx2 : YK11.FPState) ly2 S2 (regs2 : bvmap 5 word) mem2 md2,
wle W W2 -> hd_fxk [] fx fx2 ->
hc_core rsegs B STK sp0 FP ly S W0 mem0 md0 own k ly2 S2 W2 mem2 md2 regs2 R ->
aregs_preserved regs regs2 -> frames S2 = frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
same_io mdc md2 -> mo_le MT Sc S2 0 ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (R - T <= x < R) -> aview rsegs (w_H W2) mem2 x = aview rsegs (w_H W) memc x) ->
rom_view rsegs W2 mem2 ->
Rr regs2 ->
SRr rsegs W2 (mkCfg (@YK11.mkst fx2 regs2 (w64 ret) mem2 (seg_rom rsegs)) md2) Q.

(* hc_call at a leaf site: the routine's lib/Lib walk (from the bridge) and the continuation hcu_sf_k. *)
Lemma hcu_sf_call : forall (a T ret : Z) (Rr : bvmap 5 word -> Prop) (Q : world rsegs -> config -> Prop)
STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R : Z),
(forall R1 R2 : bvmap 5 word, (forall r, getr R1 r = getr R2 r) -> Rr R1 -> Rr R2) ->
0 <= T <= T_SEG_STK ->
hc_core rsegs B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R ->
getr regs 1 = w64 ret -> 4096 <= ret < 2 ^ 64 -> ret mod 2 = 0 ->
rom_view rsegs W memc ->
(LF.stk rsegs (MN.normalize_cj rsegs (mrestrict (w_H W) memc)) (spZ regs - T) (spZ regs) ->
 LM.mem_inv rsegs (MN.normalize_cj rsegs (mrestrict (w_H W) memc)) ->
 MN.task_mem rsegs (MN.normalize_cj rsegs (mrestrict (w_H W) memc)) ->
 LEx.evt rsegs (hc_leaf_post rsegs T regs (@fp_regs fx) Rr (MN.normalize_cj rsegs (mrestrict (w_H W) memc)))
 (LMS.MS (R6.mkR_of regs) (@fp_regs fx) (Z_to_bv 64 a) (@fp_csr fx) None
  (MN.normalize_cj rsegs (mrestrict (w_H W) memc)) (LPE.seg_rom rsegs))) ->
hcu_sf_k T ret Rr Q STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R ->
SRr rsegs W (cfg_at rsegs a regs memc mdc) Q.
Proof.
intros a T ret Rr Q STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R Hext HT HC Hra Hr1 Hr2 HRV EVF K.
apply (hc_call rsegs B MT a T ret (hd_fxk [] fx) (fun _ => False) (fun _ regs2 _ => Rr regs2) Q
  STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R HC Hra Hr1 Hr2 HT).
- intros HP. exact (hcu_leaf_lift a T Rr STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs Hext
    ltac:(lia) HP HRV EVF).
- intros W2 fx2 ly2 S2 regs2 mem2 md2 Hle Hfx HC2 Hpres _ Hfr Hperm Hio Hmo Hkeep HRr.
  assert (Hk' : forall x, 0 <= x < 2 ^ 64 -> ~ (R - T <= x < R) ->
    aview rsegs (w_H W2) mem2 x = aview rsegs (w_H W) memc x)
    by (intros x Hx Hs; exact (Hkeep x Hx Hs (fun H => H))).
  pose proof (hc_core_R rsegs B STK sp0 FP ly S W0 mem0 md0 own k ly2 S2 W2 mem2 md2 regs2 R HC2) as (HRc & _ & _).
  pose proof asan_consts as (AC1 & _ & _ & _ & AC5).
  apply (K W2 fx2 ly2 S2 regs2 mem2 md2 Hle Hfx HC2 Hpres Hfr Hperm Hio Hmo Hk'); [|exact HRr].
  exact (hcu_rom_view_keep W W2 memc mem2 (R - T) R ltac:(lia) HRV Hk').
Qed.

Local Ltac sf_T0 := unfold T_SEG_STK, ASTACK; lia.

(* ======================================== the five routines at image B ======================================== *)
Section sf.
Variable IMG : RStep.RImg.
Hypothesis HIMG : @RStep.img_segs IMG = rsegs.
Hypothesis HK_EXT : @RStep.sym IMG 0x200dc = HVU_SF_EXT.
Hypothesis HK_FD : @RStep.sym IMG 0x7f000900 = HVU_SF_FD.
Hypothesis HK_SUB : @RStep.sym IMG 0x1bc70 = HVU_SF_SUB.
Hypothesis HK_GE : @RStep.sym IMG 0x1b314 = HVU_SF_GE.
Hypothesis HK_LT : @RStep.sym IMG 0x1b24c = HVU_SF_LT.
Hypothesis C_EXT : @C_extendsftf2.extendsftf2_contract IMG.
Hypothesis C_FD : @C_floatditf.floatditf_contract IMG.
Hypothesis C_SUB : @G_subtf3.subtf3_contract IMG.
Hypothesis C_GE : @G_getf2.getf2_contract IMG.
Hypothesis C_LT : @G_letf2.letf2_contract IMG.

(* 0x835cc: d = __extendsftf2(f), v the 64-bit value of fa0; d in a0:a1. *)
Lemma hcu_sf_ext : @hvu_sf_ext_stmt fx rc SK B MT.
Proof.
intros ret Q STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R v HC Hra Hr1 Hr2 Hv HRV Hfrm K. subst v.
apply (hcu_sf_call HVU_SF_EXT 0 ret (hc_r2 (C_extendsftf2.f128_of_f32 (bv_unsigned (reg_get (@fp_regs fx) 10))))
  Q STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R (hc_r2_ext _) ltac:(sf_T0) HC Hra Hr1 Hr2 HRV).
- intros _ HMI HTM.
  exact (hc_br_ext IMG rsegs HVU_SF_EXT HIMG HK_EXT C_EXT regs (@fp_regs fx) (@fp_csr fx) _ Hfrm HMI HTM).
- intros W2 fx2 ly2 S2 regs2 mem2 md2 Hle Hfx HC2 Hpres Hfr Hperm Hio Hmo Hkeep Hrv (E10 & E11).
  apply (K W2 fx2 ly2 S2 regs2 mem2 md2 Hle Hfx HC2 Hpres Hfr Hperm Hio Hmo); [| exact Hrv | exact E10 | exact E11].
  intros x Hx. apply Hkeep; [exact Hx | lia].
Qed.

(* 0x83610: __floatditf(t), t = a0 = fcvt.l.s of f; the binary128 value of t in a0:a1. *)
Lemma hcu_sf_fd : @hvu_sf_fd_stmt fx rc SK B MT.
Proof.
intros ret Q STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R t HC Hra Hr1 Hr2 H10 HRV Hfrm K.
apply (hcu_sf_call HVU_SF_FD 0 ret (hc_r2 (C_floatditf.f128_of_i64 t))
  Q STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R (hc_r2_ext _) ltac:(sf_T0) HC Hra Hr1 Hr2 HRV).
- intros _ HMI HTM.
  exact (hc_br_fd IMG rsegs HVU_SF_FD HIMG HK_FD C_FD t regs (@fp_regs fx) (@fp_csr fx) _
    (hc_arg_wrap regs t H10) Hfrm HMI HTM).
- intros W2 fx2 ly2 S2 regs2 mem2 md2 Hle Hfx HC2 Hpres Hfr Hperm Hio Hmo Hkeep Hrv (E10 & E11).
  apply (K W2 fx2 ly2 S2 regs2 mem2 md2 Hle Hfx HC2 Hpres Hfr Hperm Hio Hmo); [| exact Hrv | exact E10 | exact E11].
  intros x Hx. apply Hkeep; [exact Hx | lia].
Qed.

(* 0x83624: __subtf3(a, b) (through __addtf3, whose 48-byte frame [R - 48, R) it writes); a - b in a0:a1. *)
Lemma hcu_sf_sub : @hvu_sf_sub_stmt fx rc SK B MT.
Proof.
intros ret Q STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R alo ahi blo bhi HC Hra Hr1 Hr2
  H10 H11 H12 H13 R0 R1 R2 R3 HRV Hfrm K.
apply (hcu_sf_call HVU_SF_SUB HVU_SUB_STK ret (hc_r2 (SF.f128_sub (alo + 2 ^ 64 * ahi) (blo + 2 ^ 64 * bhi)))
  Q STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R (hc_r2_ext _)
  ltac:(unfold HVU_SUB_STK; sf_T0) HC Hra Hr1 Hr2 HRV).
- intros HST HMI HTM.
  exact (hc_br_sub IMG rsegs HVU_SF_SUB HIMG HK_SUB C_SUB regs (@fp_regs fx) (@fp_csr fx)
    (MN.normalize_cj rsegs (mrestrict (w_H W) memc)) alo ahi blo bhi
    (hc_arg regs 10 alo eq_refl H10 R0) (hc_arg regs 11 ahi eq_refl H11 R1)
    (hc_arg regs 12 blo eq_refl H12 R2) (hc_arg regs 13 bhi eq_refl H13 R3) Hfrm HST HMI HTM).
- intros W2 fx2 ly2 S2 regs2 mem2 md2 Hle Hfx HC2 Hpres Hfr Hperm Hio Hmo Hkeep Hrv (E10 & E11).
  exact (K W2 fx2 ly2 S2 regs2 mem2 md2 Hle Hfx HC2 Hpres Hfr Hperm Hio Hmo Hkeep Hrv E10 E11).
Qed.

(* 0x83600 (pod.h:160, the float-cast test's __gttf2) and 0x83638: __getf2(a, b) = __gttf2(a, b); the comparison
   result (SoftFloat.f128_ge) in a0. *)
Lemma hcu_sf_ge : @hvu_sf_ge_stmt fx rc SK B MT.
Proof.
intros ret Q STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R alo ahi blo bhi HC Hra Hr1 Hr2
  H10 H11 H12 H13 R0 R1 R2 R3 HRV Hfrm K.
apply (hcu_sf_call HVU_SF_GE 0 ret (hc_r1 (SF.f128_ge (alo + 2 ^ 64 * ahi) (blo + 2 ^ 64 * bhi)))
  Q STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R (hc_r1_ext _) ltac:(sf_T0) HC Hra Hr1 Hr2 HRV).
- intros _ HMI HTM.
  exact (hc_br_ge IMG rsegs HVU_SF_GE HIMG HK_GE C_GE regs (@fp_regs fx) (@fp_csr fx) _ alo ahi blo bhi
    (hc_arg regs 10 alo eq_refl H10 R0) (hc_arg regs 11 ahi eq_refl H11 R1)
    (hc_arg regs 12 blo eq_refl H12 R2) (hc_arg regs 13 bhi eq_refl H13 R3) Hfrm HMI HTM).
- intros W2 fx2 ly2 S2 regs2 mem2 md2 Hle Hfx HC2 Hpres Hfr Hperm Hio Hmo Hkeep Hrv E10.
  apply (K W2 fx2 ly2 S2 regs2 mem2 md2 Hle Hfx HC2 Hpres Hfr Hperm Hio Hmo); [| exact Hrv | exact E10].
  intros x Hx. apply Hkeep; [exact Hx | lia].
Qed.

(* 0x83650: __lttf2(a, b) (= __letf2's code); the comparison result (SoftFloat.f128_le) in a0. *)
Lemma hcu_sf_lt : @hvu_sf_lt_stmt fx rc SK B MT.
Proof.
intros ret Q STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R alo ahi blo bhi HC Hra Hr1 Hr2
  H10 H11 H12 H13 R0 R1 R2 R3 HRV Hfrm K.
apply (hcu_sf_call HVU_SF_LT 0 ret (hc_r1 (SF.f128_le (alo + 2 ^ 64 * ahi) (blo + 2 ^ 64 * bhi)))
  Q STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R (hc_r1_ext _) ltac:(sf_T0) HC Hra Hr1 Hr2 HRV).
- intros _ HMI HTM.
  exact (hc_br_le IMG rsegs HVU_SF_LT HIMG HK_LT C_LT regs (@fp_regs fx) (@fp_csr fx) _ alo ahi blo bhi
    (hc_arg regs 10 alo eq_refl H10 R0) (hc_arg regs 11 ahi eq_refl H11 R1)
    (hc_arg regs 12 blo eq_refl H12 R2) (hc_arg regs 13 bhi eq_refl H13 R3) Hfrm HMI HTM).
- intros W2 fx2 ly2 S2 regs2 mem2 md2 Hle Hfx HC2 Hpres Hfr Hperm Hio Hmo Hkeep Hrv E10.
  apply (K W2 fx2 ly2 S2 regs2 mem2 md2 Hle Hfx HC2 Hpres Hfr Hperm Hio Hmo); [| exact Hrv | exact E10].
  intros x Hx. apply Hkeep; [exact Hx | lia].
Qed.

End sf.
End c.
End b.

Print Assumptions hcu_rom_view_keep.
Print Assumptions hcu_leaf_lift.
Print Assumptions hcu_sf_call.
Print Assumptions hcu_sf_ext.
Print Assumptions hcu_sf_fd.
Print Assumptions hcu_sf_sub.
Print Assumptions hcu_sf_ge.
Print Assumptions hcu_sf_lt.
