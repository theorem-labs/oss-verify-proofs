(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgNear.v at fa2bbbd285b; the lift is taken at reac-pw/fuzz_role's image B (fuzz_role.asan-ubsan), by the edits proofs/reac-pw/fuzz_rate/lib/AU/RtPgNearLB.v at 7e722b95884 made to fuzz_rate's image-A lift: the image is lib/AU/Img0.v, the seam lib/AU/RPgNearS.v, the contract lib/AU/RPgNearC.v (a_ / A_ names -> b_ / B_), the entry, the .got slot and the shadow-offset cell lib/AU/RPgNearImg.v's, rl_pod_nearest_A_of -> rl_pod_nearest_B_of; the proof steps are image A's. *)
(* pod_nearest(f, out) of reac-pw/fuzz_role's ASan image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0), entry RPgNearImg.B_POD_NEAREST = 0x82eb4: the
   LIFT of the machine-level contract lib/AU/RPgNearC.v pod_nearest_B_contract (the walk, in the lib/Lib library over
   the image lib/AU/Img0.v rsegs) to lib/A/RPgCSpec.v's rl_pod_nearest_specX (the form LLVMFuzzerTestOneInput's
   second middle segment calls it in). The walk itself is proved apart; here it is the theorem's premise.

   The seam is lib/AU/RPgNearS.v: the walk runs on the normalized restricted store
   `MemNorm.normalize_cj rsegs (mrestrict (w_H W) memc)`, which the contract's `rom_view` premise relates to the
   harness's store, and lands back in SRr.

   Where the walk's premises come from, at the call site:
   - the stack window [sp - 112, sp): the caller's journal keeps [sp0 - STK, sp0) present, and rl_pre puts
     [sp - 112, sp) inside it; the window lies at or above the allocator's ceiling, so no image byte and no
     read-only byte is in it and the normalization keeps every byte of it;
   - the 8 bytes at out: rl_wcell puts them either in the same caller window or in a side-stack frame the caller
     holds (AR_frames_law / AR_client_img_law give that such a frame is present, off the image and below the
     ceiling);
   - the .got slot B_GOT_SHADOW (0x9aad0) and the shadow-offset cell B_SHADOW_CELL (0xa3678): AR_const_law (LAWS)
     with the frame's two fields,
     read as 8-byte cells (val_mem) and turned into lib/Lib `bytes_at` of `le8`; both lie below TASK_SIZE, so the
     normalization keeps them;
   - the shadow byte of out: `range_addressable ... SHADOW_OFF out 8` at out + 7 gives a byte s with
     saddr_ok (out + 7) s, and out mod 8 = 0 forces s = 0; its address SHADOW_OFF + out / 8 is below
     kHighShadowEnd, hence below the stack window and below TASK_SIZE;
   - frm0 from the rl_pre float premise, and mem_inv / task_mem of the normalized store by construction.

   What the walk's post gives back: the end pc is ra (YK0s.ret_ok), the float registers outside f15 and a zero
   rounding mode (rl_fxk [15] fx), the journal extended by YCbq.ajournal_exec over the write set
   [sp - 112, sp) (and, when the answer is Some, [out, out + 8)) -- both inside awr_byte -- the callee-saved
   registers, and a0 = rl_near_rc of the answer with its 8 bytes at out. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import
YK11 YK14 YK0s YK15 YK18 YK0i YK1b YP09 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YK0o YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Nearest.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require
PropExec MState Mem Exec Frame FP Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgNearS.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require RPgNearImg RPgNearC.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Module NC := OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU.RPgNearC.
Module NI := OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU.RPgNearImg.

(* the two spellings of the return value are the same function of the model's answer *)
Lemma near_rc_same : forall o, rl_near_rc o = NC.b_near_rc o.
Proof. intros [r|]; reflexivity. Qed.

Lemma near_getr_reg : forall (regs : bvmap 5 word) (r : bv 5),
bv_eqb r (0%bv) = false -> getr regs r = reg_get regs r.
Proof. intros regs r H. unfold getr. rewrite H. reflexivity. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
Hypothesis HGOT : as_got_shadow B = NI.B_GOT_SHADOW.
Hypothesis HSC : as_shadow_cell B = NI.B_SHADOW_CELL.

Theorem rl_pod_nearest_B_of :
NC.pod_nearest_B_contract -> rl_pod_nearest_specX rsegs B MT NI.B_POD_NEAREST.
Proof using MTL LAWS HGOT HSC.
intros C.
unfold rl_pod_nearest_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs out b
       HPRE H10 Hb HF HWC Hal8 HSH HRV HFRM.
destruct HPRE as (HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev).
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hios & Hfrs & Hnev & Hk0 & F1 & F2 & F3 & F4
                  & Hgone & Hpres & Hstk0 & F5 & HQT).
pose proof Hstk0 as (Hsp0al & HSTK0 & Hceil & Hlolo & Hhihi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).

(* ---- the stack pointer the premises speak of ---- *)
assert (ESP : bv_unsigned (reg_get regs 2) = spZ regs) by reflexivity.

(* ---- the geometry of the stack window ---- *)
assert (Hlo_ceil : alloc_ceiling <= spZ regs - NC.B_NEAR_STACK).
{ unfold NC.B_NEAR_STACK. unfold T_nearest_STK in Hwlo. lia. }
assert (Hsp_hi : spZ regs <= 2 ^ 47) by lia.
assert (Hnoimg : forall a, spZ regs - NC.B_NEAR_STACK <= a < spZ regs -> ~ in_img rsegs a).
{ intros a Ha Hin. pose proof (near_segs_low a Hin). lia. }

(* ---- where the 8 bytes at out live ---- *)
assert (HOUTp : forall a, out <= a < out + 8 ->
  apresent (w_H W) memc a /\ ~ in_img rsegs a /\ 0 <= a < 2 ^ 47).
{ intros a Ha. destruct HWC as [[[Hq1 Hq2] | (cid & pos & Hin & Hcid & Hq1 & Hq2)] _].
  - split; [apply Hpres; lia|]. split; [| lia].
    intros Hi. pose proof (near_segs_low a Hi). lia.
  - assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hin).
    destruct (al_frames _ _ LAWS lyc Sc W memc mdc cid pos HAR HinC) as (_ & _ & Hfb & _).
    destruct (frames_bounds rsegs B LAWS lyc Sc W memc mdc cid pos HAR HinC)
      as (Hf0 & Hfc & _).
    split; [exact (proj1 (Hfb a ltac:(lia)))|]. split; [| lia].
    assert (Hcl : ~ in_zr a (ly_img lyc) /\ ~ in_img rsegs a).
    { apply (al_client_img _ _ LAWS lyc Sc W memc mdc a HAR).
      right. left. exists cid, pos. split; [exact HinC | lia]. }
    exact (proj2 Hcl). }

(* ---- the destination register ---- *)
assert (Eout : bv_unsigned (reg_get regs 10) = out).
{ change (reg_get regs 10) with (getr regs 10). rewrite H10. unfold w64.
  apply LMS.unsigned_lit. destruct (HOUTp out ltac:(lia)) as (_ & _ & Hr). lia. }

(* ---- the shadow byte of out is 0 ---- *)
assert (Hsa_lt : NC.B_SHADOW_OFF + out / 8 < kHighShadowEnd).
{ destruct (HOUTp out ltac:(lia)) as (_ & _ & Hor).
  pose proof (shadow_addr_bounds out ltac:(lia)) as Hsb.
  unfold shadow_addr, SHADOW_OFF in Hsb. unfold NC.B_SHADOW_OFF. lia. }
assert (Hsa_pos : 0 <= NC.B_SHADOW_OFF + out / 8).
{ destruct (HOUTp out ltac:(lia)) as (_ & _ & Hor).
  assert (0 <= out / 8) by (apply Z.div_pos; lia). unfold NC.B_SHADOW_OFF. lia. }
assert (Hsview : aview rsegs (w_H W) memc (NC.B_SHADOW_OFF + out / 8) = Some 0).
{ destruct (HSH (out + 7) ltac:(lia)) as (s & Hs & Hok).
  assert (Esa : shadow_of_addr SHADOW_OFF (out + 7) = NC.B_SHADOW_OFF + out / 8).
  { unfold shadow_of_addr, SHADOW_OFF, NC.B_SHADOW_OFF. f_equal.
    symmetry. apply Z.div_unique with (r := 7); lia. }
  rewrite Esa in Hs. rewrite Hs. f_equal.
  destruct Hok as [H0 | [H1 H2]]; [exact H0|].
  exfalso. assert ((out + 7) mod 8 = 7) by (rewrite Zplus_mod, Hal8; reflexivity). lia. }

(* ---- the normalized store ---- *)
pose proof (near_ro_agree W memc HRV) as HROA.
assert (HMI : LM.mem_inv rsegs (MN.normalize_cj rsegs (mrestrict (w_H W) memc)))
  by (apply (MN.mem_inv_cj_inv rsegs); apply MN.mem_inv_cj_normalize).
assert (HTM : MN.task_mem rsegs (MN.normalize_cj rsegs (mrestrict (w_H W) memc)))
  by (apply (MN.mem_inv_cj_task rsegs); apply MN.mem_inv_cj_normalize).

assert (HSTKm : LF.stk rsegs (MN.normalize_cj rsegs (mrestrict (w_H W) memc))
                  (spZ regs - NC.B_NEAR_STACK) (spZ regs)).
{ split; [lia|]. split; [lia|]. intros a Ha.
  destruct (Hpres a ltac:(unfold T_nearest_STK in Hwlo; unfold NC.B_NEAR_STACK in Ha; lia))
    as (HH & bb & Hbb).
  assert (Em : MN.normalize_cj rsegs (mrestrict (w_H W) memc) (LM.wa a) = Some bb).
  { unfold MN.normalize_cj. rewrite (near_keep a ltac:(unfold TASK_SIZE; lia) (Hnoimg a Ha)).
    unfold mrestrict, LM.wa. rewrite HH. exact Hbb. }
  split; [unfold wview; rewrite Em; discriminate | exists bb; unfold LM.mrd; rewrite Em; reflexivity]. }

assert (HWRm : LM.wr_at rsegs (MN.normalize_cj rsegs (mrestrict (w_H W) memc)) out 8).
{ destruct (HOUTp out ltac:(lia)) as (_ & _ & Hor0).
  split; [lia|]. split; [lia|]. intros i Hi.
  destruct (HOUTp (out + i) ltac:(lia)) as ((HH & bb & Hbb) & Hni & Hri).
  assert (Em : MN.normalize_cj rsegs (mrestrict (w_H W) memc) (LM.wa (out + i)) = Some bb).
  { unfold MN.normalize_cj. rewrite (near_keep (out + i) ltac:(unfold TASK_SIZE; lia) Hni).
    unfold mrestrict, LM.wa. rewrite HH. exact Hbb. }
  unfold wview. rewrite Em. discriminate. }

destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Hcellw & _ & Hgotw & _).
rewrite HSC in Hcellw. rewrite HGOT, HSC in Hgotw.
assert (BG : LM.bytes_at rsegs (MN.normalize_cj rsegs (mrestrict (w_H W) memc))
               NI.B_GOT_SHADOW (LM.le8 (Z_to_bv 64 NI.B_SHADOW_CELL))).
{ apply MN.bytes_at_normalize_cj_low;
    [exact HROA | rewrite LM.length_le8; unfold NI.B_GOT_SHADOW, TASK_SIZE; lia |].
  apply near_val_bytes; [unfold NI.B_SHADOW_CELL; lia | unfold NI.B_GOT_SHADOW; lia
    | unfold NI.B_GOT_SHADOW; lia |].
  apply val_mem_of_rdword. exact Hgotw. }
assert (BC : LM.bytes_at rsegs (MN.normalize_cj rsegs (mrestrict (w_H W) memc))
               NI.B_SHADOW_CELL (LM.le8 (Z_to_bv 64 NC.B_SHADOW_OFF))).
{ apply MN.bytes_at_normalize_cj_low;
    [exact HROA | rewrite LM.length_le8; unfold NI.B_SHADOW_CELL, TASK_SIZE; lia |].
  apply near_val_bytes; [unfold NC.B_SHADOW_OFF; lia | unfold NI.B_SHADOW_CELL; lia
    | unfold NI.B_SHADOW_CELL; lia |].
  apply val_mem_of_rdword. exact Hcellw. }
assert (BS : LM.bytes_at rsegs (MN.normalize_cj rsegs (mrestrict (w_H W) memc))
               (NC.B_SHADOW_OFF + out / 8) [Z_to_bv 8 0]).
{ apply MN.bytes_at_normalize_cj_low; [exact HROA | cbn [length]; unfold TASK_SIZE; lia |].
  split; [lia|]. split; [cbn [length]; lia|].
  intros i Hi. cbn [length] in Hi. assert (i = 0%nat) by lia. subst i.
  cbn [nth_error Z.of_nat]. rewrite Z.add_0_r.
  apply near_mrd_of_view; [lia | exact Hsview]. }

(* ---- the walk, at the normalized store ---- *)
pose proof (C (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 5)
              (reg_get regs 6) (reg_get regs 7) (reg_get regs 8) (reg_get regs 9) (reg_get regs 10)
              (reg_get regs 11) (reg_get regs 12) (reg_get regs 13) (reg_get regs 14) (reg_get regs 15)
              (reg_get regs 16) (reg_get regs 17) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20)
              (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25)
              (reg_get regs 26) (reg_get regs 27) (reg_get regs 28) (reg_get regs 29) (reg_get regs 30)
              (reg_get regs 31) (@fp_regs fx) (@fp_csr fx)
              (MN.normalize_cj rsegs (mrestrict (w_H W) memc)) (spZ regs - NC.B_NEAR_STACK) b
              Hb HF
              ltac:(rewrite Eout; exact HWRm)
              ltac:(rewrite Eout; exact Hal8)
              ltac:(rewrite Eout, ESP; unfold T_nearest_STK, NC.B_NEAR_STACK in *;
                    destruct HWC as [_ [Hd | Hd]]; [right; lia | left; lia])
              ltac:(rewrite ESP; exact HSTKm)
              ltac:(rewrite ESP; lia)
              ltac:(rewrite ESP; intros a Ha; apply near_rom_none; [lia | apply Hnoimg; lia])
              ltac:(unfold NI.B_SHADOW_CELL; lia)
              BG BC
              ltac:(rewrite Eout; exact BS)
              ltac:(rewrite Eout, ESP; cbn [LF.outside]; split; [lia | exact I])
              HFRM HMI HTM) as EVW.

(* ---- lifted into SRr ---- *)
apply (near_srr_of_norm_evt W NI.B_POD_NEAREST regs memc mdc _ _ HRV EVW).

(* ---- the post ---- *)
intros msf can sq model' HQ Hrel Hcjs Heqv Hsm Hcl.
destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6'
                & F' & fc' & m' & Hsq & HFk & Hfrm' & Hmem & Hwm & Hmi' & Htm' & Hstk').
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
rewrite ESP in Hstk'.

(* the write set of the call, as the caller's journal sees it *)
pose (Wr := fun a : Z =>
  (spZ regs - NC.B_NEAR_STACK <= a < spZ regs) \/
  (Nearest.nearest b Nearest.INT32_MIN Nearest.INT32_MAX <> None /\ out <= a < out + 8)).
assert (Wdec : forall a : Z, Wr a \/ ~ Wr a).
{ intros a. unfold Wr.
  assert (D1 : (spZ regs - NC.B_NEAR_STACK <= a < spZ regs)
               \/ ~ (spZ regs - NC.B_NEAR_STACK <= a < spZ regs)) by lia.
  assert (D2 : (out <= a < out + 8) \/ ~ (out <= a < out + 8)) by lia.
  destruct (Nearest.nearest b Nearest.INT32_MIN Nearest.INT32_MAX) as [rr|] eqn:Env.
  - destruct D1 as [D1|D1]; [left; left; exact D1|].
    destruct D2 as [D2|D2]; [left; right; split; [discriminate | exact D2]|].
    right. intros [Hc | (_ & Hc)]; [exact (D1 Hc) | exact (D2 Hc)].
  - destruct D1 as [D1|D1]; [left; left; exact D1|].
    right. intros [Hc | (Hc & _)]; [exact (D1 Hc) | exact (Hc eq_refl)]. }

(* what the walk left of the store, in the caller's words *)
assert (HmuW : forall x : word, ~ Wr (bv_unsigned x) ->
  m' x = MN.normalize_cj rsegs (mrestrict (w_H W) memc) x).
{ unfold NC.b_near_mem in Hmem. rewrite Eout, ESP in Hmem. revert Hmem.
  destruct (Nearest.nearest b Nearest.INT32_MIN Nearest.INT32_MAX) as [rr|] eqn:Env;
    intros Hmem.
  - intros x Hx. unfold Wr in Hx. apply (proj1 Hmem). cbn [LF.outside].
    split; [| split; [| exact I]]; intros Hc; apply Hx;
      [left; exact Hc | right; split; [congruence | exact Hc]].
  - intros x Hx. unfold Wr in Hx. apply Hmem. cbn [LF.outside].
    split; [| exact I]. intros Hc; apply Hx; left; exact Hc. }
assert (HbyA : forall a, Nearest.nearest b Nearest.INT32_MIN Nearest.INT32_MAX <> None ->
  out <= a < out + 8 -> exists bb, m' (LM.wa a) = Some bb).
{ intros a Hne Ha.
  destruct (HOUTp a Ha) as (_ & Hni & Hri).
  revert Hne. unfold NC.b_near_mem in Hmem. rewrite Eout, ESP in Hmem. revert Hmem.
  destruct (Nearest.nearest b Nearest.INT32_MIN Nearest.INT32_MAX) as [rr|];
    intros Hmem Hne; [| exfalso; apply Hne; reflexivity].
  destruct Hmem as (_ & _ & _ & Hby). rewrite LM.length_le8 in Hby.
  specialize (Hby (Z.to_nat (a - out)) ltac:(lia)).
  rewrite Z2Nat.id in Hby by lia. replace (out + (a - out)) with a in Hby by lia.
  unfold LM.mrd in Hby. rewrite (near_rom_none a ltac:(lia) Hni) in Hby.
  destruct (m' (LM.wa a)) as [b1|]; [exists b1; reflexivity |].
  destruct (nth_error (LM.le8 (Z_to_bv 64 rr)) (Z.to_nat (a - out))) as [b0|] eqn:En;
    [discriminate Hby |].
  apply nth_error_None in En. rewrite LM.length_le8 in En. lia. }

(* every byte outside the write set is the caller's *)
assert (KEEP : forall x : word, ~ Wr (bv_unsigned x) -> cm x = mrestrict (w_H W) memc x).
{ intros x Hx. destruct (MN.cj_drop rsegs x) eqn:Dx.
  - exact (Hcjs x Dx).
  - rewrite <- (MN.mem_rel_cj_keep rsegs cm m' x Hmrel Dx).
    rewrite (HmuW x Hx). unfold MN.normalize_cj. rewrite Dx. reflexivity. }

(* every byte of the write set is present after the call *)
assert (PRESW : forall a, Wr a -> exists bb, cm (LM.wa a) = Some bb).
{ intros a Ha.
  assert (Hoff : ~ in_img rsegs a /\ 0 <= a < 2 ^ 47).
  { unfold Wr in Ha. destruct Ha as [Ha | (_ & Ha)].
    - split; [apply Hnoimg; lia | lia].
    - destruct (HOUTp a Ha) as (_ & Hni & Hri). split; [exact Hni | exact Hri]. }
  destruct Hoff as (Hni & Hri).
  assert (Dx : MN.cj_drop rsegs (LM.wa a) = false)
    by (apply near_keep; [unfold TASK_SIZE; lia | exact Hni]).
  assert (Hm' : exists bb, m' (LM.wa a) = Some bb).
  { unfold Wr in Ha. destruct Ha as [Ha | (Hne & Ha)].
    - destruct Hstk' as (_ & _ & Hs).
      destruct (Hs a ltac:(lia)) as (_ & bb & Hbb).
      unfold LM.mrd in Hbb. rewrite (near_rom_none a ltac:(lia) Hni) in Hbb.
      destruct (m' (LM.wa a)) as [b0|]; [exists b0; reflexivity | discriminate Hbb].
    - exact (HbyA a Hne Ha). }
  destruct Hm' as (bb & Hbb). exists bb.
  rewrite <- (MN.mem_rel_cj_keep rsegs cm m' (LM.wa a) Hmrel Dx). exact Hbb. }

(* the three facts the journal's execution step asks of the new store *)
assert (HA : forall x : word, ~ Wr (bv_unsigned x) ->
  mrestrict (w_H W) (munrestrict (w_H W) memc cm) x = mrestrict (w_H W) memc x).
{ intros x Hx. rewrite near_mrestrict_munrestrict.
  pose proof (KEEP x Hx) as Hk. unfold mrestrict in Hk |- *.
  destruct (w_H W x); [reflexivity | exact Hk]. }
assert (HB : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) (munrestrict (w_H W) memc cm))).
{ intros x Hx. rewrite near_mrestrict_munrestrict. unfold mrestrict in Hx |- *.
  destruct (w_H W x) eqn:EH; [exact Hx|].
  destruct (Wdec (bv_unsigned x)) as [Hw | Hw].
  - destruct (PRESW (bv_unsigned x) Hw) as (bb & Hbb).
    unfold LM.wa in Hbb. rewrite LMS.Z_to_bv_bv_unsigned in Hbb. rewrite Hbb. discriminate.
  - pose proof (KEEP x Hw) as Hk. unfold mrestrict in Hk. rewrite EH in Hk. rewrite Hk. exact Hx. }
assert (HC : forall x : word, w_H W x = true -> munrestrict (w_H W) memc cm x = memc x).
{ intros x Hx. unfold munrestrict. rewrite Hx. reflexivity. }
assert (HD : forall a, Wr a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a).
{ intros a Ha. unfold Wr in Ha. destruct Ha as [Ha | (_ & Ha)].
  - left. unfold T_nearest_STK in Hwlo. unfold NC.B_NEAR_STACK in Ha. lia.
  - destruct HWC as [[[Hq1 Hq2] | (cid & pos & Hin & Hcid & Hq1 & Hq2)] _].
    + left. unfold T_nearest_STK in Hwlo. lia.
    + right. right. right. exists cid, pos. split; [exact Hin|]. left.
      unfold in_zr. cbn [fst snd]. lia. }

red.
exists (YK11.mkFP F' fc'), lyc, Sc, fr, (munrestrict (w_H W) memc cm), model'.
split.
{ unfold unrestrict.
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom].
  rewrite (near_ret_pc (reg_get regs 1)
            ltac:(change (reg_get regs 1) with (getr regs 1); exact Hra)).
  reflexivity. }
split.
{ split.
  - intros r Hr. apply HFk. intros Hk15. apply Hr. rewrite Hk15. left. reflexivity.
  - exact Hfrm'. }
split.
{ exact (ajournal_exec rsegs B LAWS near_segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
          (munrestrict (w_H W) memc cm) model' Wr HJ HA HB HC Hsm HD). }
split.
{ intros r Hr.
  assert (Hx0 : is_x0 (Z_to_bv 5 r) = false).
  { unfold acallee_saved in Hr.
    destruct Hr as [->|[->|[->|[->|[->|Hr]]]]]; [reflexivity .. |].
    assert (Hr' : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25
                  \/ r = 26 \/ r = 27) by lia.
    destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; reflexivity. }
  rewrite (near_getr_reg fr (Z_to_bv 5 r) ltac:(rewrite bv_eqb0_is_x0; exact Hx0)).
  rewrite (near_getr_reg regs (Z_to_bv 5 r) ltac:(rewrite bv_eqb0_is_x0; exact Hx0)).
  rewrite <- (X1 (Z_to_bv 5 r) Hx0).
  unfold acallee_saved in Hr.
  destruct Hr as [->|[->|[->|[->|[->|Hr]]]]]; [reflexivity .. |].
  assert (Hr' : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25
                \/ r = 26 \/ r = 27) by lia.
  destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; reflexivity. }
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [exact (same_io_materialized mdc model' Hsm)|].
split; [apply mo_le_refl; exact MTL|].
split.
{ intros a Ha Hns Hne.
  apply (aview_eq_of rsegs (w_H W) memc (munrestrict (w_H W) memc cm) a).
  apply HA. rewrite LMS.unsigned_lit by exact Ha.
  intros [Hw | Hw];
    [apply Hns; unfold T_nearest_STK; unfold NC.B_NEAR_STACK in Hw; lia | exact (Hne Hw)]. }
split.
{ rewrite (near_getr_reg fr (10%bv) ltac:(reflexivity)).
  rewrite <- (X1 (10%bv) ltac:(reflexivity)).
  unfold w64, rl_near_rc, NC.b_near_rc. reflexivity. }
destruct (Nearest.nearest b Nearest.INT32_MIN Nearest.INT32_MAX) as [r|]; [| exact I].
unfold NC.b_near_mem in Hmem. rewrite Eout, ESP in Hmem.
destruct Hmem as (_ & Hby).
assert (Hmr : forall kk, (kk < 8)%nat ->
  mbyte rsegs (mrestrict (w_H W) (munrestrict (w_H W) memc cm)) (out + Z.of_nat kk)
  = mbyte rsegs m' (out + Z.of_nat kk)).
{ intros kk Hk.
  destruct (HOUTp (out + Z.of_nat kk) ltac:(lia)) as ((HH & bb & Hbb) & Hni & Hri).
  assert (Dx : MN.cj_drop rsegs (LM.wa (out + Z.of_nat kk)) = false)
    by (apply near_keep; [unfold TASK_SIZE; lia | exact Hni]).
  assert (Ecm : mrestrict (w_H W) (munrestrict (w_H W) memc cm) (LM.wa (out + Z.of_nat kk))
                = m' (LM.wa (out + Z.of_nat kk))).
  { rewrite near_mrestrict_munrestrict. unfold mrestrict, LM.wa. rewrite HH.
    symmetry. exact (MN.mem_rel_cj_keep rsegs cm m' (LM.wa (out + Z.of_nat kk)) Hmrel Dx). }
  unfold LM.wa in Ecm. unfold mbyte. rewrite Ecm. reflexivity. }
intros kk Hk.
rewrite (Hmr kk Hk).
pose proof (near_bytes_val m' out (Z_to_bv 64 r) Hby kk Hk) as Hv.
rewrite LMS.unsigned_lit_wrap in Hv. exact Hv.
Qed.

End d.
End b.

Check rl_pod_nearest_B_of.
Print Assumptions rl_pod_nearest_B_of.
