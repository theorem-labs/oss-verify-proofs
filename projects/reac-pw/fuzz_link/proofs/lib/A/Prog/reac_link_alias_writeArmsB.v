(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img at fuzz_command's ASan image end 0x606000; ajournal no longer keeps footprint (FP) bytes in the image or at or above alloc_ceiling (fp_spares FP a also requires ~ inFP FP a, and the clause for bytes at or above alloc_ceiling outside [sp0 - STK, sp0) requires ~ inFP FP a), awr_byte (and awr_ok) take the start state's side-stack frames as a new parameter and also admit footprint writes to the program's statics as_prog_static in the image, to the caller's stack above sp0 and to those caller frames (awr_prog_or_caller), acall_kept_of_journal, region_kept_stack_sub, awr_byte_present and aj_intrin_at take the matching premises, ajournal_sub_wide composes a callee whose footprint lies in what the caller may write, awr_byte_present_prog and aj_intrin_at_prog take prog_rw for stores to the statics, AR_errno_present gives the errno cell's value from errno_rom, and astack_rd/astack_pres (stack bytes readable/present from sp to the stack top) give a frame chain for any s0 but an aligned sp + 8 (chain_pre_any, achain_any) and carry across an ajournal (astack_rd_journal, astack_pres_journal). *)
(* Modified by Theorem Labs, 2026-10: the malloc/free journal lemmas (aj_free_at, aj_free_at_io, aj_free_null_at, aj_free_null_at_io, aj_malloc_at, aj_malloc_at_io, aj_malloc_at04, aj_malloc_at04_io, aj_malloc, aj_free) no longer take In (call_trace0 ...) (as_universe B); the model laws get the trace length (call_trace_len) and the contracts the event bound. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/Reusable/YCbq.v, with its module paths and module names changed; 1154 of its 1305 lines of code are new or changed and 3194 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LinkWalkSide.v, with its module names changed; 623 of its 666 lines of code are new or changed and 1262 lines of the source are left out. *)
(* reac_link_alias_write on image A: the three refusal arms of the stretch +0x1a8 .. +0x1f0 that need no call
   (name NULL, alias NULL, empty name), for the piece `aw_mid_obl` of lib/A/Prog/reac_link_alias_writeDefs.v.
   The two calls (wrapper_strlen, fuzz_if_nametoindex), ARM 6, ARM 8, the SEND cut and the piece itself,

     aw_arms : aw_exit_obl SK B -> aw_send_obl SK B -> aw_mid_obl SK B

   are lib/A/Prog/reac_link_alias_writeArmsD.v, on the kit of lib/A/Prog/reac_link_alias_writeArmsC.v.

   The code, in the order the tests are made (listing
   (internal path) (internal record, sha256 0b8d5e317aa8)):
     +0x1a8  `beqz s6`           name = NULL               -> +0x3a4 with s5 = -22
     +0x1ac..+0x1b8 (+0x4d4)     the instrumented check of the 1-byte load of name[0]
     +0x1bc  `beqz s4`           alias = NULL              -> +0x3a4 with s5 = -22
     +0x1c0..+0x1c4 `lbu`        the name is empty         -> +0x3a4 with s5 = -22
     +0x1cc  wrapper_strlen(alias);  +0x1d4 `bgeu 255,a0`  |alias| >= 256 -> s5 = -36, +0x3a4
     +0x1e8  fuzz_if_nametoindex(name);  +0x1ec `beqz a0`  index 0 -> +0x3a0 (s5 = -19), +0x3a4
     +0x1f0  otherwise: the SEND cut.

   The engine runs at the atoms of the MID cut itself (atom r = the value of register r there, so s6 = 22 is
   the name, s7 = 23 the shadow base, s4 = 20 the alias, s5 = 21 the return code), which is what makes the
   shadow entry `mkSHE 22 0 1` and the one-byte region over atom 22 the whole memory the piece needs: between
   +0x1a8 and +0x1f0 the code reads the shadow byte of the name and name[0], and writes nothing.

   The model side (the value of `write_lib` at each refusal, and the move of the fake kernel's views to a later
   memory) is lib/A/Prog/reac_link_alias_writeArmsA.v. The three arms walk from the MID cut itself, at the atoms of its
   registers (`awE`).

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC88 LinkWalk LinkWalkPi LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import nl_talk_c reac_link_alias_write_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import fuzz_if_nametoindex_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require RtString RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import reac_link_alias_writeDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import reac_link_alias_writeArmsA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkShadow LinkWalkStrS LinkWalkCall.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
(* A machine state whose four shape fields the engine fixes is the `mkst` the run lemmas take. *)
Lemma aw_ms_eta : forall (fx : YK11.FPState) (ms : machine_state),
  ms_resv ms = None -> ms_svc_pending ms = None -> ms_fregs ms = fp_regs -> ms_fcsr ms = fp_csr ->
  ms = mkst (ms_regs ms) (ms_pc_val ms) (ms_mem ms) (ms_rom ms).
Proof. intros fx [] H1 H2 H3 H4; cbn in *; subst; reflexivity. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis LV : LinkVals.
Hypothesis TL : PALib B.

(* the shadow band the token engine checks against, as pcap uses it *)
Definition AwBspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition AwBx : sv := SOff 23 0.                  (* s7 holds the shadow base at the MID cut *)

(* ==========================================================================
   The state the engine sees at the MID cut
   ========================================================================== *)

(* The environment of the stretch: atom r is the value of register r AT THE MID CUT (the piece is a cut, not an
   entry, so its atoms are the cut's registers), and atoms 240.. are the image's objects. *)
Definition awE (ms3 : machine_state) (extra : list word) : env := Eimg (Ereg (ms_regs ms3) extra).

Lemma awE_img : forall ms3 extra, img_env VAL A_LIM (awE ms3 extra).
Proof. intros ms3 extra. apply Eimg_env. Qed.

Lemma awE_reg : forall ms3 extra n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (awE ms3 extra) n = getr (ms_regs ms3) r.
Proof.
  intros ms3 extra n r Hn. unfold awE.
  pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
  rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat (ms_regs ms3) extra n r Hn).
Qed.

Lemma awE_sv : forall ms3 extra n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  sv_denot (awE ms3 extra) (SOff n 0) = getr (ms_regs ms3) r.
Proof.
  intros ms3 extra n r Hn. cbn [sv_denot]. rewrite (awE_reg ms3 extra n r Hn), Z.add_0_r.
  apply Z_to_bv_bv_unsigned.
Qed.

(* the machine state at a cut, in the shape the run lemmas take *)
Lemma aw_mkst_at : forall (W3 : world SEGS) (ms3 : machine_state) (pc : Z),
  ms_resv ms3 = None -> ms_svc_pending ms3 = None -> ms_rom ms3 = seg_rom SEGS ->
  ms_fregs ms3 = fp_regs -> ms_fcsr ms3 = fp_csr -> ms_pc_val ms3 = w64 (BASE + pc) ->
  ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + pc)) (ms_mem ms3) (seg_rom SEGS).
Proof.
  intros W3 ms3 pc H1 H2 H3 H4 H5 H6.
  transitivity (mkst (ms_regs ms3) (ms_pc_val ms3) (ms_mem ms3) (ms_rom ms3));
    [exact (aw_ms_eta fx ms3 H1 H2 H4 H5) | rewrite H3, H6; reflexivity].
Qed.

(* The instance fact (the HSEGS convention of the library walks): link's PAImg instance has it by reflexivity. It is
   used only where a computation over the image's segments is needed, here for `LA_G_NL_writable`
   (link_ajkit.v), i.e. for the writable half of `anlk_at` at a later memory. *)
Hypothesis HSEGS : pa_segs = tfibsegs.

(* the image's symbols, for LinkWalkShadow.v's image-shadow coverage; the instance is AD2l.PcapB_syms *)
Hypothesis TB : AF0m.PcapSyms B.

(* ==========================================================================
   What a cut's `aw_base` gives, one clause at a time
   ========================================================================== *)

Definition aw_Eacc (cx : awcx) (fpos : Z) : Z -> Prop :=
  fun a => aw_E cx a \/ aside_rng (aw_lyc cx) AW_CID fpos a.

Lemma aw_base_kept : forall (cx : awcx) fpos ly3 S3 W3 ms3 md3,
  aw_base SK B cx fpos ly3 S3 W3 ms3 md3 ->
  akept SEGS B (aw_lyc cx) (aw_Sc cx) (aw_W cx) (aw_memc cx) W3 (ms_mem ms3)
    (aw_sp cx - REAC_LINK_ALIAS_WRITE_AK) (aw_sp cx) (aw_Eacc cx fpos).
Proof. intros cx fpos ly3 S3 W3 ms3 md3 H. unfold aw_base in H. cbv zeta in H. unfold aw_Eacc. tauto. Qed.

Lemma aw_base_jx : forall (cx : awcx) fpos ly3 S3 W3 ms3 md3,
  aw_base SK B cx fpos ly3 S3 W3 ms3 md3 ->
  ajournal_gx SEGS B (aw_G cx) (aw_XO cx) (aw_OUT cx) (aw_STK cx) (aw_sp0 cx) (aw_FP cx)
    (aw_ly cx) (aw_S cx) (aw_W0 cx) (aw_mem0 cx) (aw_md0 cx) ((AW_CID, fpos) :: aw_own cx)
    ly3 S3 W3 (ms_mem ms3) md3 (aw_k cx).
Proof. intros cx fpos ly3 S3 W3 ms3 md3 H. unfold aw_base in H. cbv zeta in H. tauto. Qed.

Lemma aw_base_nin : forall (cx : awcx) fpos ly3 S3 W3 ms3 md3,
  aw_base SK B cx fpos ly3 S3 W3 ms3 md3 -> ~ In (AW_CID, fpos) (frames (aw_Sc cx)).
Proof. intros cx fpos ly3 S3 W3 ms3 md3 H. unfold aw_base in H. cbv zeta in H. tauto. Qed.

Lemma aw_base_wit : forall (cx : awcx) fpos ly3 S3 W3 ms3 md3,
  aw_base SK B cx fpos ly3 S3 W3 ms3 md3 ->
  exists S1 W1 mem1 md1, AR SEGS B (aw_lyc cx) S1 W1 mem1 md1 /\
    frames S1 = (AW_CID, fpos) :: frames (aw_Sc cx).
Proof.
  intros cx fpos ly3 S3 W3 ms3 md3 H. unfold aw_base in H. cbv zeta in H.
  destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (S1 & W1 & mem1 & md1 & H1 & H2 & _) & _).
  exists S1, W1, mem1, md1. split; [exact H1 | exact H2].
Qed.

(* The position frame_alloc_3 handed out is one of its class's slots: the frame witness's AR places every frame of
   its state in its class (YG0s.v frame_facts). It is what `akb_not_side` and `fmiss_side` (LinkWalkShadow.v) ask.
   The model is reac_link_alias_writeSend.v's aws_F. *)
Lemma AW_FPOS : forall (cx : awcx) fpos ly3 S3 W3 ms3 md3,
  aw_base SK B cx fpos ly3 S3 W3 ms3 md3 -> 0 <= fpos < fs_frames AW_CID.
Proof.
  intros cx fpos ly3 S3 W3 ms3 md3 HB.
  destruct (aw_base_wit cx fpos ly3 S3 W3 ms3 md3 HB) as (S1 & W1 & mem1 & md1 & HAR & Hfr).
  assert (Hin : In (AW_CID, fpos) (frames S1)) by (rewrite Hfr; left; reflexivity).
  destruct HAR as [M _]. destruct (frame_facts B _ S1 _ _ _ M Hin) as (_ & H6 & _). exact H6.
Qed.

Lemma aw_base_shape : forall (cx : awcx) fpos ly3 S3 W3 ms3 md3,
  aw_base SK B cx fpos ly3 S3 W3 ms3 md3 ->
  ms_resv ms3 = None /\ ms_svc_pending ms3 = None /\ ms_rom ms3 = seg_rom SEGS /\
  ms_fregs ms3 = fp_regs /\ ms_fcsr ms3 = fp_csr.
Proof. intros cx fpos ly3 S3 W3 ms3 md3 H. unfold aw_base in H. cbv zeta in H. tauto. Qed.

(* ==========================================================================
   The read set, and the fake kernel's views, at the cut's memory
   ========================================================================== *)

(* a byte of the read set is not a byte of the write set (g_nl's range): the Pre separates every string it
   reads from g_nl (`apart_gnl`) *)
Lemma aw_rd_apart_gnl : forall (cx : awcx) a,
  reac_link_alias_write_apre SEGS B (aw_regs cx) (aw_m0 cx) ->
  reac_link_alias_write_ard SEGS (aw_regs cx) (aw_m0 cx) a ->
  ~ aw_E cx a.
Proof.
  intros cx a HP HA HE.
  unfold aw_E, aw_wr, reac_link_alias_write_awr in HE.
  destruct HE as (r & [<- | []] & HE). cbn [fst snd] in HE.
  assert (HNK : NK_N_SENT + 4 <= NK_SIZE) by (unfold NK_N_SENT, NK_SIZE; lia).
  destruct HP as (kbs & tab & nm & al & HN & _ & _ & _ & _ & HT & _ & _ & _ & HNM & HAL & HTS & HNS & HAS & _).
  destruct HA as [(H0 & s & HC & Ha) | [(H0 & s & HC & Ha) | (bs & tb & i & n2 & ix & p & HN' & HT' & Hi & HU & HC & Ha)]].
  - destruct nm as [s0|]; cbn in HNM; [|exact (H0 HNM)].
    destruct HNM as (_ & HC0). rewrite (aw_acstr_unique SEGS _ _ s s0 HC HC0) in Ha.
    destruct (HNS s0 eq_refl) as (_ & HG & _). unfold apart_gnl in HG. lia.
  - destruct al as [s0|]; cbn in HAL; [|exact (H0 HAL)].
    destruct HAL as (_ & HC0). rewrite (aw_acstr_unique SEGS _ _ s s0 HC HC0) in Ha.
    destruct (HAS s0 eq_refl) as (_ & HG & _). unfold apart_gnl in HG. lia.
  - rewrite <- (aw_anlk_unique SEGS _ _ kbs bs HN HN') in HT'.
    rewrite <- (aw_aiftab_unique SEGS _ _ kbs tab tb HT HT') in Hi.
    destruct (HTS i n2 ix p Hi HU) as (_ & HG & _). unfold apart_gnl in HG. lia.
Qed.

Lemma aw_rd_kept : forall (cx : awcx) fpos ly3 S3 W3 ms3 md3 a,
  aw_pre SK B cx -> aw_base SK B cx fpos ly3 S3 W3 ms3 md3 ->
  reac_link_alias_write_ard SEGS (aw_regs cx) (aw_m0 cx) a ->
  aview SEGS (w_H W3) (ms_mem ms3) a = aview SEGS (w_H (aw_W cx)) (aw_memc cx) a.
Proof.
  intros cx fpos ly3 S3 W3 ms3 md3 a HPRE HB HA.
  pose proof HPRE as (HAPRE & HRD & HP).
  pose proof (HRD a HA) as HAKB.
  pose proof (aw_base_kept cx fpos ly3 S3 W3 ms3 md3 HB) as HKEPT.
  pose proof (aw_base_nin cx fpos ly3 S3 W3 ms3 md3 HB) as HNIN.
  pose proof (aw_base_wit cx fpos ly3 S3 W3 ms3 md3 HB) as HWIT.
  assert (HJ : ajournal_gx SEGS B (aw_G cx) (aw_XO cx) (aw_OUT cx) (aw_STK cx) (aw_sp0 cx) (aw_FP cx)
     (aw_ly cx) (aw_S cx) (aw_W0 cx) (aw_mem0 cx) (aw_md0 cx) (aw_own cx)
     (aw_lyc cx) (aw_Sc cx) (aw_W cx) (aw_memc cx) (aw_mdc cx) (aw_k cx))
    by (unfold apre in HAPRE; tauto).
  eapply (akept_akb_gx SK SEGS B); [exact HJ | exact HKEPT | exact HAKB |].
  intros [HE | HS].
  - exact (aw_rd_apart_gnl cx a HP HA HE).
  - revert HS. eapply (akb_not_side SK SEGS B pa_img_range);
      [exact HJ | unfold AW_CID; lia | exact (AW_FPOS cx fpos ly3 S3 W3 ms3 md3 HB)
       | exact HNIN | exact HAKB].
Qed.

(* the AR state a journal carries at its current end *)
Lemma aw_ar_of_jx : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k,
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  AR SEGS B lyc Sc W memc mdc.
Proof.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (_ & _ & (memS & HJi & _) & _).
  destruct HJi as (HAR & _). exact HAR.
Qed.

Lemma aw_jc : forall (cx : awcx), aw_pre SK B cx ->
  ajournal_gx SEGS B (aw_G cx) (aw_XO cx) (aw_OUT cx) (aw_STK cx) (aw_sp0 cx) (aw_FP cx)
    (aw_ly cx) (aw_S cx) (aw_W0 cx) (aw_mem0 cx) (aw_md0 cx) (aw_own cx)
    (aw_lyc cx) (aw_Sc cx) (aw_W cx) (aw_memc cx) (aw_mdc cx) (aw_k cx).
Proof. intros cx (HAPRE & _ & _). unfold apre in HAPRE. tauto. Qed.

Lemma aw_base_perm : forall (cx : awcx) fpos ly3 S3 W3 ms3 md3,
  aw_base SK B cx fpos ly3 S3 W3 ms3 md3 ->
  Permutation (ablocks B ly3 S3) (ablocks B (aw_lyc cx) (aw_Sc cx)).
Proof. intros cx fpos ly3 S3 W3 ms3 md3 H. unfold aw_base in H. cbv zeta in H. tauto. Qed.

(* the exception set of the piece misses the shadow of every frame of Sc *)
Lemma aw_fmiss : forall (cx : awcx) fpos ly3 S3 W3 ms3 md3,
  aw_pre SK B cx -> aw_base SK B cx fpos ly3 S3 W3 ms3 md3 ->
  fmiss (aw_lyc cx) (aw_Sc cx) (aw_Eacc cx fpos).
Proof.
  intros cx fpos ly3 S3 W3 ms3 md3 HPRE HB.
  pose proof (aw_ar_of_jx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (aw_jc cx HPRE)) as HAR.
  unfold aw_Eacc. apply fmiss_or.
  - apply (fmiss_app SEGS B LAWS _ _ (aw_W cx) (aw_memc cx) (aw_mdc cx) _ HAR).
    intros a HE. left. unfold aw_E, aw_wr, reac_link_alias_write_awr in HE.
    destruct HE as (r & [<- | []] & HE). cbn [fst snd] in HE.
    unfold LA_G_NL, NK_N_SENT, kLowMemEnd in *. lia.
  - exact (fmiss_side SEGS B _ _ (aw_W cx) (aw_memc cx) (aw_mdc cx) AW_CID fpos HAR
             ltac:(unfold AW_CID; lia) (AW_FPOS cx fpos ly3 S3 W3 ms3 md3 HB)
             (aw_base_nin cx fpos ly3 S3 W3 ms3 md3 HB)).
Qed.

(* the shadow facts of a read-set range, from the call to the cut *)
Lemma aw_shadow_at : forall (cx : awcx) fpos ly3 S3 W3 ms3 md3 p n,
  aw_pre SK B cx -> aw_base SK B cx fpos ly3 S3 W3 ms3 md3 -> 0 < n ->
  (forall a, p <= a < p + n ->
     akb SEGS B (aw_lyc cx) (aw_Sc cx) (aw_sp cx - REAC_LINK_ALIAS_WRITE_AK) (aw_sp cx) a) ->
  range_addressable (aview SEGS (w_H (aw_W cx)) (aw_memc cx)) SHADOW_OFF p n ->
  shadow_hull_vis (aview SEGS (w_H (aw_W cx)) (aw_memc cx)) p n ->
  range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF p n /\
  shadow_hull_vis (aview SEGS (w_H W3) (ms_mem ms3)) p n.
Proof.
  intros cx fpos ly3 S3 W3 ms3 md3 p n HPRE HB Hn Hakb Hra Hhv.
  pose proof (aw_jc cx HPRE) as HJc.
  pose proof (aw_base_jx cx fpos ly3 S3 W3 ms3 md3 HB) as HJ3.
  pose proof (aw_ar_of_jx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as HAR1.
  pose proof (aw_ar_of_jx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR2.
  pose proof HJc as Rc. apply (aj_stk_row_eq SK SEGS B) in Rc.
  pose proof HJ3 as R3. apply (aj_stk_row_eq SK SEGS B) in R3.
  pose proof (aw_base_perm cx fpos ly3 S3 W3 ms3 md3 HB) as HPerm.
  apply (shadow_transport_akb SEGS B LAWS TB pa_img_range (aw_lyc cx) (aw_Sc cx) (aw_W cx) (aw_memc cx)
           (aw_mdc cx) ly3 S3 W3 (ms_mem ms3) md3
           (aw_sp cx - REAC_LINK_ALIAS_WRITE_AK) (aw_sp cx) (aw_Eacc cx fpos) p n HAR1 HAR2).
  - rewrite (proj1 R3), (proj1 Rc). reflexivity.
  - rewrite (proj2 R3), (proj2 Rc). reflexivity.
  - intros b m Hin. apply (Permutation_in (l := ablocks B (aw_lyc cx) (aw_Sc cx)));
      [apply Permutation_sym; exact HPerm | exact Hin].
  - exact (aw_base_kept cx fpos ly3 S3 W3 ms3 md3 HB).
  - exact (aw_fmiss cx fpos ly3 S3 W3 ms3 md3 HPRE HB).
  - exact Hn.
  - exact Hakb.
  - exact Hra.
  - exact Hhv.
Qed.

(* g_nl's size, as the write set and `LA_G_NL_writable` (link_ajkit.v) spell it *)
Lemma aw_nk_size : NK_SIZE = 271992.
Proof. reflexivity. Qed.

(* THE EXIT CUT'S RESULT CLAUSE for a path that leaves the fake kernel alone: the return code is `write_lib`'s
   at a refusal, and the kernel's record is the caller's, read at the later memory. *)
Lemma aw_pf_at : forall (cx : awcx) (W' : world SEGS) (m' : word -> option byte) rcv,
  reac_link_alias_write_apre SEGS B (aw_regs cx) (aw_m0 cx) ->
  (forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE ->
     aview SEGS (w_H W') m' a = aview SEGS (w_H (aw_W cx)) (aw_memc cx) a) ->
  (forall a, reac_link_alias_write_ard SEGS (aw_regs cx) (aw_m0 cx) a ->
     aview SEGS (w_H W') m' a = aview SEGS (w_H (aw_W cx)) (aw_memc cx) a) ->
  (forall kbs tab nm al,
     anlk_at SEGS (aw_m0 cx) LA_G_NL kbs -> aiftab_at SEGS (aw_m0 cx) LA_G_NL kbs tab ->
     astr_arg SEGS (aw_m0 cx) (aw_name cx) nm -> astr_arg SEGS (aw_m0 cx) (aw_alias cx) al ->
     rcv = w_rc (write_lib tab nm al (nk_sent kbs) (nk_kstate kbs)) /\
     w_reqs (write_lib tab nm al (nk_sent kbs) (nk_kstate kbs)) = nk_sent kbs /\
     w_state (write_lib tab nm al (nk_sent kbs) (nk_kstate kbs)) = nk_kstate kbs) ->
  aw_pf cx rcv W' m'.
Proof.
  intros cx W' m' rcv HP HGNL HRDK HRC.
  assert (Hmb : forall x, LA_G_NL <= x < LA_G_NL + NK_SIZE ->
            mbyte SEGS (mrestrict (w_H W') m') x = mbyte SEGS (aw_m0 cx) x).
  { intros x Hx. exact (mbyte_of_aview_eq SEGS _ _ _ _ x x (HGNL x Hx)). }
  assert (HWgen : forall (mm : word -> option byte) a, LA_G_NL <= a < LA_G_NL + NK_SIZE ->
            writable_at SEGS mm a).
  { intros mm a Ha. rewrite HSEGS. apply LA_G_NL_writable. rewrite aw_nk_size in Ha. exact Ha. }
  assert (Hwr : forall x, LA_G_NL <= x < LA_G_NL + NK_SIZE ->
            writable_at SEGS (mrestrict (w_H W') m') x) by (intros x Hx; apply HWgen; exact Hx).
  pose proof HP as (kbs0 & tab0 & nm0 & al0 & HN0 & HWF0 & HOP0 & _ & _ & HT0 & _).
  unfold aw_pf. intros kbs tab nm al HN HT HA HBl. cbv zeta.
  rewrite (aw_anlk_unique SEGS (aw_m0 cx) LA_G_NL kbs0 kbs HN0 HN) in HWF0, HOP0.
  destruct (HRC kbs tab nm al HN HT HA HBl) as (Hrc & Hreq & Hst).
  split; [exact Hrc|]. exists kbs.
  split.
  { exact (aw_anlk_move SEGS (aw_m0 cx) (mrestrict (w_H W') m') LA_G_NL kbs HN Hmb Hwr). }
  split; [exact HWF0|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split.
  { apply (aw_aiftab_move SEGS (aw_m0 cx) (mrestrict (w_H W') m') LA_G_NL kbs tab HT Hmb).
    intros i n2 ix p Hi HU HC x Hx.
    apply (mbyte_of_aview_eq SEGS _ _ _ _ x x). apply HRDK.
    right; right. exists kbs, tab, i, n2, ix, p.
    split; [exact HN|]. split; [exact HT|]. split; [exact Hi|]. split; [exact HU|].
    split; [exact HC | exact Hx]. }
  rewrite Hst, Hreq.
  split; [symmetry; exact (aw_next_kstate kbs HWF0)|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [symmetry; exact (aw_n_sent_length kbs HWF0)|].
  split; [exact HOP0|]. split; [reflexivity|]. split; [reflexivity|].
  split; [lia | intros _; reflexivity].
Qed.


(* ==========================================================================
   `aw_base` across a stretch that writes no memory (the five refusal arms between the two cuts)
   ========================================================================== *)

Lemma aw_base_step_nomem : forall (cx : awcx) fpos ly3 S3 W3 ms3 md3 ms4 md4,
  aw_base SK B cx fpos ly3 S3 W3 ms3 md3 ->
  ms_mem ms4 = ms_mem ms3 ->
  ms_resv ms4 = None -> ms_svc_pending ms4 = None -> ms_rom ms4 = seg_rom SEGS ->
  ms_fregs ms4 = fp_regs -> ms_fcsr ms4 = fp_csr ->
  m_fds md4 = m_fds md3 -> m_fs md4 = m_fs md3 ->
  ajournal_gx SEGS B (aw_G cx) (aw_XO cx) (aw_OUT cx) (aw_STK cx) (aw_sp0 cx) (aw_FP cx)
    (aw_ly cx) (aw_S cx) (aw_W0 cx) (aw_mem0 cx) (aw_md0 cx) ((AW_CID, fpos) :: aw_own cx)
    ly3 S3 W3 (ms_mem ms4) md4 (aw_k cx) ->
  getr (ms_regs ms4) 2 = getr (ms_regs ms3) 2 ->
  getr (ms_regs ms4) 9 = getr (ms_regs ms3) 9 ->
  getr (ms_regs ms4) 8 = getr (ms_regs ms3) 8 ->
  getr (ms_regs ms4) 18 = getr (ms_regs ms3) 18 ->
  getr (ms_regs ms4) 19 = getr (ms_regs ms3) 19 ->
  getr (ms_regs ms4) 24 = getr (ms_regs ms3) 24 ->
  getr (ms_regs ms4) 3 = getr (ms_regs ms3) 3 ->
  getr (ms_regs ms4) 4 = getr (ms_regs ms3) 4 ->
  getr (ms_regs ms4) 25 = getr (ms_regs ms3) 25 ->
  getr (ms_regs ms4) 26 = getr (ms_regs ms3) 26 ->
  getr (ms_regs ms4) 27 = getr (ms_regs ms3) 27 ->
  aw_base SK B cx fpos ly3 S3 W3 ms4 md4.
Proof.
  intros cx fpos ly3 S3 W3 ms3 md3 ms4 md4 HB Hmem H1 H2 H3 H4 H5 Hfd Hfs HJ
    E2 E9 E8 E18 E19 E24 E3 E4 E25 E26 E27.
  rewrite Hmem in HJ.
  unfold aw_base in HB |- *. cbv zeta in HB |- *. rewrite Hmem.
  destruct HB as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 &
                  R2 & R9 & R8 & R18 & R19 & R24 & R3 & R4 & R25 & R26 & R27 &
                  Sv1 & Sv2 & Sv3 & Pr1 & Pr2 & KP & FD & FS & RO).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact HJ|]. split; [exact B7|]. split; [exact B8|]. split; [exact B9|].
  split; [exact B10|]. split; [exact B11|]. split; [exact B12|].
  split; [rewrite E2; exact R2|]. split; [rewrite E9; exact R9|]. split; [rewrite E8; exact R8|].
  split; [rewrite E18; exact R18|]. split; [rewrite E19; exact R19|]. split; [rewrite E24; exact R24|].
  split; [rewrite E3; exact R3|]. split; [rewrite E4; exact R4|].
  split; [rewrite E25; exact R25|]. split; [rewrite E26; exact R26|]. split; [rewrite E27; exact R27|].
  split; [exact Sv1|]. split; [exact Sv2|]. split; [exact Sv3|].
  split; [exact Pr1|]. split; [exact Pr2|]. split; [exact KP|].
  split; [rewrite Hfd; exact FD|]. split; [rewrite Hfs; exact FS | exact RO].
Qed.

(* ==========================================================================
   The registers a run of this stretch keeps, read off the end state
   ========================================================================== *)

(* ==========================================================================
   ARM 1: the name is NULL (+0x1a8 `beqz s6` taken), so `write_lib` refuses with -22
   ========================================================================== *)

Lemma aw_arm_name_null : aw_exit_obl SK B ->
  forall (cx : awcx) fpos ly3 S3 W3 ms3 md3,
    aw_pre SK B cx -> aw_gi_mid SK B cx fpos ly3 S3 W3 ms3 md3 ->
    aw_name cx = 0 ->
    SRr SEGS W3 (mkCfg ms3 md3) (aw_post SK B cx).
Proof.
  intros EXIT cx fpos ly3 S3 W3 ms3 md3 HPRE HMID Hnull.
  destruct HMID as (Hpc & Hs4 & Hs5 & Hs6 & Hs7 & HGNL & HB).
  pose proof (aw_base_shape cx fpos ly3 S3 W3 ms3 md3 HB) as (Hrv & Hsv & Hrom & Hfr & Hfc).
  pose proof (aw_base_jx cx fpos ly3 S3 W3 ms3 md3 HB) as HJ3.
  pose proof HPRE as (HAPRE & HRD & HP).
  assert (HGx : gx_ok SEGS B (aw_G cx)) by (unfold apre in HAPRE; tauto).
  assert (HEI : img_env VAL A_LIM (awE ms3 [])) by apply awE_img.
  assert (Hms : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + AW_CUT_MID)) (ms_mem ms3) (seg_rom SEGS))
    by (apply (aw_mkst_at W3 ms3 AW_CUT_MID); assumption).
  assert (Hrms : restrict (w_H W3) ms3 =
     mkst (ms_regs ms3) (Z_to_bv 64 (BASE + AW_CUT_MID)) (mrestrict (w_H W3) (ms_mem ms3)) (seg_rom SEGS)).
  { rewrite Hms at 1. rewrite restrict_mkst_fx. reflexivity. }
  assert (HS : st_ok_pi SEGS VAL (awE ms3 [])
     (mkSS AW_CUT_MID (sr_set sr_atoms 22%bv (SLit 0)) [] None (mkFacts [] [] []))
     (restrict (w_H W3) ms3)).
  { apply (ast_ok_pi_set_reg_fp (awE ms3 []) (mkSS AW_CUT_MID sr_atoms [] None (mkFacts [] [] []))
             (restrict (w_H W3) ms3) 22%bv (SLit 0)).
    - rewrite Hrms.
      apply pa_entry_st_ok_full.
      + apply regs_ok_Eimg_Ereg.
      + vm_compute; reflexivity.
      + constructor.
      + exact I.
      + split; [exact I | split; exact I].
    - reflexivity.
    - cbn [ms_regs restrict mkst sv_denot]. rewrite Hs6, Hnull. reflexivity. }
  assert (SHOK : sh_ok SEGS AwBx [] (awE ms3 []) (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
  pose (RUNTO := paj_run_to_x SK B LAWS (aw_G cx) HGx (aw_XO cx) (aw_OUT cx)).
  paj_run_to_tok RUNTO HS HJ3 SHOK AwBspan AW_CUT_EXIT; [apply awr_ok_x_nil |].
  (* the run wrote nothing *)
  assert (Hmem : ms_mem ms = ms_mem ms3).
  { apply functional_extensionality. intros x. apply HF.
    cbn [ss_mem]. intros (r0 & Hin & _). destruct Hin. }
  (* the registers it kept *)
  prreg HS (2%bv : bv 5) Q2. rewrite (awE_reg ms3 [] 2%nat 2%bv eq_refl) in Q2.
  prreg HS (9%bv : bv 5) Q9. rewrite (awE_reg ms3 [] 9%nat 9%bv eq_refl) in Q9.
  prreg HS (8%bv : bv 5) Q8. rewrite (awE_reg ms3 [] 8%nat 8%bv eq_refl) in Q8.
  prreg HS (18%bv : bv 5) Q18. rewrite (awE_reg ms3 [] 18%nat 18%bv eq_refl) in Q18.
  prreg HS (19%bv : bv 5) Q19. rewrite (awE_reg ms3 [] 19%nat 19%bv eq_refl) in Q19.
  prreg HS (24%bv : bv 5) Q24. rewrite (awE_reg ms3 [] 24%nat 24%bv eq_refl) in Q24.
  prreg HS (3%bv : bv 5) Q3. rewrite (awE_reg ms3 [] 3%nat 3%bv eq_refl) in Q3.
  prreg HS (4%bv : bv 5) Q4. rewrite (awE_reg ms3 [] 4%nat 4%bv eq_refl) in Q4.
  prreg HS (25%bv : bv 5) Q25. rewrite (awE_reg ms3 [] 25%nat 25%bv eq_refl) in Q25.
  prreg HS (26%bv : bv 5) Q26. rewrite (awE_reg ms3 [] 26%nat 26%bv eq_refl) in Q26.
  prreg HS (27%bv : bv 5) Q27. rewrite (awE_reg ms3 [] 27%nat 27%bv eq_refl) in Q27.
  prreg HS (21%bv : bv 5) Q21. rewrite (awE_reg ms3 [] 21%nat 21%bv eq_refl) in Q21.
  pose proof (st_ok_pi_restrict_mkst (w_H W3) _ _ _ HS eq_refl) as Hms4.
  apply (EXIT cx fpos ly3 S3 W3 ms (with_vm_backing (m_vm_lazy md3) mat md3) HPRE).
  exists (-22).
  split.
  { rewrite Hms4 at 1. cbn [ms_pc_val mkst]. reflexivity. }
  split.
  { rewrite Q21. exact Hs5. }
  split.
  { apply (aw_base_step_nomem cx fpos ly3 S3 W3 ms3 md3 ms _ HB Hmem);
      try (rewrite Hms4 at 1; cbn [ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst]; reflexivity).
    - exact (proj1 (wvb_fds_fs (m_vm_lazy md3) mat md3)).
    - exact (proj2 (wvb_fds_fs (m_vm_lazy md3) mat md3)).
    - exact HJ3.
    - exact Q2.
    - exact Q9.
    - exact Q8.
    - exact Q18.
    - exact Q19.
    - exact Q24.
    - exact Q3.
    - exact Q4.
    - exact Q25.
    - exact Q26.
    - exact Q27. }
  apply (aw_pf_at cx W3 (ms_mem ms) (-22) HP).
  - rewrite Hmem. exact HGNL.
  - rewrite Hmem. intros a Ha. exact (aw_rd_kept cx fpos ly3 S3 W3 ms3 md3 a HPRE HB Ha).
  - intros kbs tab nm al HN HT HA HBl.
    assert (Hnm : nm = None).
    { destruct nm as [s|]; [|reflexivity]. exfalso. cbn in HA. apply (proj1 HA).
      unfold aw_name in Hnull. exact Hnull. }
    rewrite Hnm, aw_wl_name_null. cbn [w_rc w_reqs w_state].
    split; [reflexivity | split; reflexivity].
Qed.

(* ==========================================================================
   ARM 3: the name is a C string but the alias is NULL (+0x1bc `beqz s4` taken): -22 again.
   The run passes the instrumented check of name[0] (+0x1ac..+0x1b8 and its +0x4d4 tail) on the shadow entry
   `mkSHE 22 0 1`, whose `sh_ok` is the Pre's `achk` of the name carried to the cut by `aw_shadow_at`.
   ========================================================================== *)

Lemma aw_arm_alias_null : aw_exit_obl SK B ->
  forall (cx : awcx) fpos ly3 S3 W3 ms3 md3 s,
    aw_pre SK B cx -> aw_gi_mid SK B cx fpos ly3 S3 W3 ms3 md3 ->
    aw_name cx <> 0 -> acstr_at SEGS (aw_m0 cx) (aw_name cx) s ->
    aw_alias cx = 0 ->
    SRr SEGS W3 (mkCfg ms3 md3) (aw_post SK B cx).
Proof.
  intros EXIT cx fpos ly3 S3 W3 ms3 md3 s HPRE HMID Hn0 Hcs Hal0.
  destruct HMID as (Hpc & Hs4 & Hs5 & Hs6 & Hs7 & HGNL & HB).
  pose proof (aw_base_shape cx fpos ly3 S3 W3 ms3 md3 HB) as (Hrv & Hsv & Hrom & Hfr & Hfc).
  pose proof (aw_base_jx cx fpos ly3 S3 W3 ms3 md3 HB) as HJ3.
  pose proof HPRE as (HAPRE & HRD & HP).
  assert (HGx : gx_ok SEGS B (aw_G cx)) by (unfold apre in HAPRE; tauto).
  (* the name's premises, at the call *)
  pose proof HP as (kbs0 & tab0 & nm0 & al0 & HN0 & HWF0 & HOP0 & Hb1 & Hb2 & HT0 & Hgra & Hghv & Herr &
                    HNM0 & HAL0 & HTS0 & HNS0 & HAS0 & Hsl0).
  assert (Enm : nm0 = Some s)
    by (apply (aw_astr_arg_unique SEGS (aw_m0 cx) (aw_name cx)); [exact HNM0 | split; assumption]).
  destruct (HNS0 s Enm) as (_ & _ & Hlen32 & (Hmr & Hra & Hhv) & _).
  assert (Hakb : forall a, aw_name cx <= a < aw_name cx + (Z.of_nat (length s) + 1) ->
     akb SEGS B (aw_lyc cx) (aw_Sc cx) (aw_sp cx - REAC_LINK_ALIAS_WRITE_AK) (aw_sp cx) a).
  { intros a Ha. unfold aw_name in Ha. apply HRD. left. split; [exact Hn0|]. exists s.
    split; [exact Hcs | lia]. }
  destruct (aw_shadow_at cx fpos ly3 S3 W3 ms3 md3 (aw_name cx) (Z.of_nat (length s) + 1)
              HPRE HB ltac:(lia) Hakb Hra Hhv) as (Hra3 & Hhv3).
  assert (Hn1 : 0 < aw_name cx) by (destruct Hcs as ((H0 & _ & _) & _); lia).
  assert (Hn2 : aw_name cx + 1 <= 2 ^ 47 - 1)
    by (unfold aw_name; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hmr; lia).
  (* the symbolic state at the MID cut *)
  assert (HEI : img_env VAL A_LIM (awE ms3 [])) by apply awE_img.
  assert (Hms : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + AW_CUT_MID)) (ms_mem ms3) (seg_rom SEGS))
    by (apply (aw_mkst_at W3 ms3 AW_CUT_MID); assumption).
  assert (Hrms : restrict (w_H W3) ms3 =
     mkst (ms_regs ms3) (Z_to_bv 64 (BASE + AW_CUT_MID)) (mrestrict (w_H W3) (ms_mem ms3)) (seg_rom SEGS)).
  { rewrite Hms at 1. rewrite restrict_mkst_fx. reflexivity. }
  assert (EBx : U (awE ms3 []) AwBx = SHADOW_OFF).
  { unfold U, AwBx. rewrite (awE_sv ms3 [] 23%nat 23%bv eq_refl), Hs7.
    apply unsigned_lit_small. unfold SHADOW_OFF. lia. }
  assert (E22 : U (awE ms3 []) (SOff 22 0) = aw_name cx).
  { unfold U. rewrite (awE_sv ms3 [] 22%nat 22%bv eq_refl), Hs6. apply unsigned_lit_small. lia. }
  assert (HS : st_ok_pi SEGS VAL (awE ms3 [])
     (mkSS AW_CUT_MID (sr_set sr_atoms 20%bv (SLit 0)) [] None
        (mkFacts [(22%nat, mkAF 1 (2 ^ 47 - 1) 0); (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] []))
     (restrict (w_H W3) ms3)).
  { apply (ast_ok_pi_set_reg_fp (awE ms3 [])
             (mkSS AW_CUT_MID sr_atoms [] None
                (mkFacts [(22%nat, mkAF 1 (2 ^ 47 - 1) 0); (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] []))
             (restrict (w_H W3) ms3) 20%bv (SLit 0)).
    - rewrite Hrms. apply pa_entry_st_ok_full.
      + apply regs_ok_Eimg_Ereg.
      + vm_compute; reflexivity.
      + constructor.
      + exact I.
      + split; [|split; [exact I | exact I]].
        cbn [f_atoms atoms_ok]. split; [|split; [|exact I]].
        * unfold afact_ok. cbn [af_lo af_hi af_al2].
          rewrite (awE_reg ms3 [] 22%nat 22%bv eq_refl), Hs6, unsigned_lit_small by lia.
          split; [lia | split; [apply Zmod_1_r | lia]].
        * unfold afact_ok. cbn [af_lo af_hi af_al2].
          rewrite (awE_reg ms3 [] 23%nat 23%bv eq_refl), Hs7, unsigned_lit_small
            by (unfold SHADOW_OFF; lia).
          split; [lia | split; [apply Zmod_1_r | lia]].
    - reflexivity.
    - cbn [ms_regs restrict mkst sv_denot]. rewrite Hs4, Hal0. reflexivity. }
  assert (SHOK : sh_ok SEGS AwBx [mkSHE 22 0 1] (awE ms3 []) (mrestrict (w_H W3) (ms_mem ms3))).
  { constructor; [|constructor].
    unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite EBx, E22. split.
    - intros x Hx. apply Hra3. lia.
    - intros a Ha. cbn [Z.min Z.max] in Ha. unfold aw_name in Ha.
      unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hmr. unfold SHADOW_OFF. lia. }
  pose (RUNTO := paj_run_to_x SK B LAWS (aw_G cx) HGx (aw_XO cx) (aw_OUT cx)).
  paj_run_to_tok RUNTO HS HJ3 SHOK AwBspan AW_CUT_EXIT; [apply awr_ok_x_nil |].
  assert (Hmem : ms_mem ms = ms_mem ms3).
  { apply functional_extensionality. intros x. apply HF.
    cbn [ss_mem]. intros (r0 & Hin & _). destruct Hin. }
  prreg HS (2%bv : bv 5) Q2. rewrite (awE_reg ms3 [] 2%nat 2%bv eq_refl) in Q2.
  prreg HS (9%bv : bv 5) Q9. rewrite (awE_reg ms3 [] 9%nat 9%bv eq_refl) in Q9.
  prreg HS (8%bv : bv 5) Q8. rewrite (awE_reg ms3 [] 8%nat 8%bv eq_refl) in Q8.
  prreg HS (18%bv : bv 5) Q18. rewrite (awE_reg ms3 [] 18%nat 18%bv eq_refl) in Q18.
  prreg HS (19%bv : bv 5) Q19. rewrite (awE_reg ms3 [] 19%nat 19%bv eq_refl) in Q19.
  prreg HS (24%bv : bv 5) Q24. rewrite (awE_reg ms3 [] 24%nat 24%bv eq_refl) in Q24.
  prreg HS (3%bv : bv 5) Q3. rewrite (awE_reg ms3 [] 3%nat 3%bv eq_refl) in Q3.
  prreg HS (4%bv : bv 5) Q4. rewrite (awE_reg ms3 [] 4%nat 4%bv eq_refl) in Q4.
  prreg HS (25%bv : bv 5) Q25. rewrite (awE_reg ms3 [] 25%nat 25%bv eq_refl) in Q25.
  prreg HS (26%bv : bv 5) Q26. rewrite (awE_reg ms3 [] 26%nat 26%bv eq_refl) in Q26.
  prreg HS (27%bv : bv 5) Q27. rewrite (awE_reg ms3 [] 27%nat 27%bv eq_refl) in Q27.
  prreg HS (21%bv : bv 5) Q21. rewrite (awE_reg ms3 [] 21%nat 21%bv eq_refl) in Q21.
  pose proof (st_ok_pi_restrict_mkst (w_H W3) _ _ _ HS eq_refl) as Hms4.
  apply (EXIT cx fpos ly3 S3 W3 ms (with_vm_backing (m_vm_lazy md3) mat md3) HPRE).
  exists (-22).
  split.
  { rewrite Hms4 at 1. cbn [ms_pc_val mkst]. reflexivity. }
  split.
  { rewrite Q21. exact Hs5. }
  split.
  { apply (aw_base_step_nomem cx fpos ly3 S3 W3 ms3 md3 ms _ HB Hmem);
      try (rewrite Hms4 at 1; cbn [ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst]; reflexivity).
    - exact (proj1 (wvb_fds_fs (m_vm_lazy md3) mat md3)).
    - exact (proj2 (wvb_fds_fs (m_vm_lazy md3) mat md3)).
    - exact HJ3.
    - exact Q2.
    - exact Q9.
    - exact Q8.
    - exact Q18.
    - exact Q19.
    - exact Q24.
    - exact Q3.
    - exact Q4.
    - exact Q25.
    - exact Q26.
    - exact Q27.
  }
  apply (aw_pf_at cx W3 (ms_mem ms) (-22) HP).
  - rewrite Hmem. exact HGNL.
  - rewrite Hmem. intros a Ha. exact (aw_rd_kept cx fpos ly3 S3 W3 ms3 md3 a HPRE HB Ha).
  - intros kbs tab nm al HN HT HA HBl.
    assert (Hal : al = None).
    { destruct al as [a0|]; [|reflexivity]. exfalso. cbn in HBl. apply (proj1 HBl).
      unfold aw_alias in Hal0. exact Hal0. }
    rewrite Hal, aw_wl_alias_null. cbn [w_rc w_reqs w_state].
    split; [reflexivity | split; reflexivity].
Qed.


(* ==========================================================================
   ARM 4: the name is the empty string (+0x1c0 `lbu` reads its NUL, +0x1c4 `beqz` taken): -22 again.
   The one-byte region over the atom of s6 holds that NUL, so the engine reads it and decides the branch.
   ========================================================================== *)

Lemma aw_arm_name_empty : aw_exit_obl SK B ->
  forall (cx : awcx) fpos ly3 S3 W3 ms3 md3 a0,
    aw_pre SK B cx -> aw_gi_mid SK B cx fpos ly3 S3 W3 ms3 md3 ->
    aw_name cx <> 0 -> acstr_at SEGS (aw_m0 cx) (aw_name cx) [] ->
    aw_alias cx <> 0 -> acstr_at SEGS (aw_m0 cx) (aw_alias cx) a0 ->
    SRr SEGS W3 (mkCfg ms3 md3) (aw_post SK B cx).
Proof.
  intros EXIT cx fpos ly3 S3 W3 ms3 md3 a0 HPRE HMID Hn0 Hcs Ha0 Hca.
  destruct HMID as (Hpc & Hs4 & Hs5 & Hs6 & Hs7 & HGNL & HB).
  pose proof (aw_base_shape cx fpos ly3 S3 W3 ms3 md3 HB) as (Hrv & Hsv & Hrom & Hfr & Hfc).
  pose proof (aw_base_jx cx fpos ly3 S3 W3 ms3 md3 HB) as HJ3.
  pose proof HPRE as (HAPRE & HRD & HP).
  assert (HGx : gx_ok SEGS B (aw_G cx)) by (unfold apre in HAPRE; tauto).
  pose proof HP as (kbs0 & tab0 & nm0 & al0 & HN0 & HWF0 & HOP0 & Hb1 & Hb2 & HT0 & Hgra & Hghv & Herr &
                    HNM0 & HAL0 & HTS0 & HNS0 & HAS0 & Hsl0).
  assert (Enm : nm0 = Some [])
    by (apply (aw_astr_arg_unique SEGS (aw_m0 cx) (aw_name cx)); [exact HNM0 | split; assumption]).
  assert (Eal : al0 = Some a0)
    by (apply (aw_astr_arg_unique SEGS (aw_m0 cx) (aw_alias cx)); [exact HAL0 | split; assumption]).
  destruct (HNS0 [] Enm) as (_ & _ & _ & (Hmr & Hra & Hhv) & _).
  destruct (HAS0 a0 Eal) as (_ & _ & _ & Hmra & _ & _).
  assert (Hakb : forall a, aw_name cx <= a < aw_name cx + (Z.of_nat (length ([] : list byte)) + 1) ->
     akb SEGS B (aw_lyc cx) (aw_Sc cx) (aw_sp cx - REAC_LINK_ALIAS_WRITE_AK) (aw_sp cx) a).
  { intros a Ha. unfold aw_name in Ha. apply HRD. left. split; [exact Hn0|]. exists ([] : list byte).
    split; [exact Hcs | cbn [length] in *; lia]. }
  destruct (aw_shadow_at cx fpos ly3 S3 W3 ms3 md3 (aw_name cx)
              (Z.of_nat (length ([] : list byte)) + 1) HPRE HB ltac:(cbn [length]; lia) Hakb Hra Hhv)
    as (Hra3 & Hhv3).
  assert (Hn1 : 0 < aw_name cx) by (destruct Hcs as ((H0 & _ & _) & _); lia).
  assert (Hn2 : aw_name cx + 1 <= 2 ^ 47 - 1)
    by (unfold aw_name; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hmr;
        cbn [length] in Hmr; lia).
  assert (Ha1 : 0 < aw_alias cx) by (destruct Hca as ((H0 & _ & _) & _); lia).
  assert (Ha2 : aw_alias cx + 1 <= 2 ^ 47 - 1)
    by (unfold aw_alias; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hmra; lia).
  (* the name's NUL at the cut's memory *)
  assert (Hcs3 : acstr_at SEGS (mrestrict (w_H W3) (ms_mem ms3)) (aw_name cx) []).
  { apply (aw_acstr_move SEGS (aw_m0 cx) (mrestrict (w_H W3) (ms_mem ms3)) (aw_name cx) [] Hcs).
    intros x Hx. apply (mbyte_of_aview_eq SEGS _ _ _ _ x x).
    apply (aw_rd_kept cx fpos ly3 S3 W3 ms3 md3 x HPRE HB). left.
    split; [exact Hn0|]. exists ([] : list byte). split; [exact Hcs | unfold aw_name in *; cbn [length] in *; lia]. }
  pose proof (aw_abytes_head SEGS (mrestrict (w_H W3) (ms_mem ms3)) (aw_name cx) (zb 0) []
                ltac:(cbn [app] in Hcs3; exact (proj1 Hcs3))) as Hbyte.
  assert (HEI : img_env VAL A_LIM (awE ms3 [])) by apply awE_img.
  assert (Hms : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + AW_CUT_MID)) (ms_mem ms3) (seg_rom SEGS))
    by (apply (aw_mkst_at W3 ms3 AW_CUT_MID); assumption).
  assert (Hrms : restrict (w_H W3) ms3 =
     mkst (ms_regs ms3) (Z_to_bv 64 (BASE + AW_CUT_MID)) (mrestrict (w_H W3) (ms_mem ms3)) (seg_rom SEGS)).
  { rewrite Hms at 1. rewrite restrict_mkst_fx. reflexivity. }
  assert (EBx : U (awE ms3 []) AwBx = SHADOW_OFF).
  { unfold U, AwBx. rewrite (awE_sv ms3 [] 23%nat 23%bv eq_refl), Hs7.
    apply unsigned_lit_small. unfold SHADOW_OFF. lia. }
  assert (E22 : U (awE ms3 []) (SOff 22 0) = aw_name cx).
  { unfold U. rewrite (awE_sv ms3 [] 22%nat 22%bv eq_refl), Hs6. apply unsigned_lit_small. lia. }
  assert (HS : st_ok_pi SEGS VAL (awE ms3 [])
     (mkSS AW_CUT_MID sr_atoms
        [YP09.mkRegion (Some 22%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))]] None
        (mkFacts [(22%nat, mkAF 1 (2 ^ 47 - 1) 0); (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
                  (20%nat, mkAF 1 (2 ^ 47 - 1) 0)] [] []))
     (restrict (w_H W3) ms3)).
  { rewrite Hrms. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute; reflexivity.
    - constructor; [|constructor].
      unfold region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite (awE_reg ms3 [] 22%nat 22%bv eq_refl), Hs6, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor]. unfold chunk_ok.
      cbn [YP09.c_off YP09.c_val YP09.c_len]. intros i Hi.
      assert (i = 0) as -> by (cbn in Hi; lia). exists (zb 0). split.
      + cbn [cbyte byte_of_word sv_denot]. reflexivity.
      + rewrite !Z.add_0_r. exact Hbyte.
    - cbn; tauto.
    - split; [|split; [exact I | exact I]].
      cbn [f_atoms atoms_ok]. split; [|split; [|split; [|exact I]]].
      + unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite (awE_reg ms3 [] 22%nat 22%bv eq_refl), Hs6, unsigned_lit_small by lia.
        split; [lia | split; [apply Zmod_1_r | lia]].
      + unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite (awE_reg ms3 [] 23%nat 23%bv eq_refl), Hs7, unsigned_lit_small
          by (unfold SHADOW_OFF; lia).
        split; [lia | split; [apply Zmod_1_r | lia]].
      + unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite (awE_reg ms3 [] 20%nat 20%bv eq_refl), Hs4, unsigned_lit_small by lia.
        split; [lia | split; [apply Zmod_1_r | lia]]. }
  assert (SHOK : sh_ok SEGS AwBx [mkSHE 22 0 1] (awE ms3 []) (mrestrict (w_H W3) (ms_mem ms3))).
  { constructor; [|constructor].
    unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite EBx, E22. split.
    - intros x Hx. apply Hra3. cbn [length]. lia.
    - intros a Ha. cbn [Z.min Z.max] in Ha. unfold aw_name in Ha.
      unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hmr. cbn [length] in Hmr.
      unfold SHADOW_OFF. lia. }
  pose (RUNTO := paj_run_to_x SK B LAWS (aw_G cx) HGx (aw_XO cx) (aw_OUT cx)).
  paj_run_to_tok RUNTO HS HJ3 SHOK AwBspan AW_CUT_EXIT;
    [ intros a (r0 & Hin & Hw); cbn [In] in Hin; destruct Hin as [<- | []];
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; exfalso; lia |].
  assert (Hmem : ms_mem ms = ms_mem ms3).
  { apply functional_extensionality. intros x. apply HF.
    cbn [ss_mem]. intros (r0 & Hin & Hw). cbn [In] in Hin. destruct Hin as [<- | []].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw. lia. }
  prreg HS (2%bv : bv 5) Q2. rewrite (awE_reg ms3 [] 2%nat 2%bv eq_refl) in Q2.
  prreg HS (9%bv : bv 5) Q9. rewrite (awE_reg ms3 [] 9%nat 9%bv eq_refl) in Q9.
  prreg HS (8%bv : bv 5) Q8. rewrite (awE_reg ms3 [] 8%nat 8%bv eq_refl) in Q8.
  prreg HS (18%bv : bv 5) Q18. rewrite (awE_reg ms3 [] 18%nat 18%bv eq_refl) in Q18.
  prreg HS (19%bv : bv 5) Q19. rewrite (awE_reg ms3 [] 19%nat 19%bv eq_refl) in Q19.
  prreg HS (24%bv : bv 5) Q24. rewrite (awE_reg ms3 [] 24%nat 24%bv eq_refl) in Q24.
  prreg HS (3%bv : bv 5) Q3. rewrite (awE_reg ms3 [] 3%nat 3%bv eq_refl) in Q3.
  prreg HS (4%bv : bv 5) Q4. rewrite (awE_reg ms3 [] 4%nat 4%bv eq_refl) in Q4.
  prreg HS (25%bv : bv 5) Q25. rewrite (awE_reg ms3 [] 25%nat 25%bv eq_refl) in Q25.
  prreg HS (26%bv : bv 5) Q26. rewrite (awE_reg ms3 [] 26%nat 26%bv eq_refl) in Q26.
  prreg HS (27%bv : bv 5) Q27. rewrite (awE_reg ms3 [] 27%nat 27%bv eq_refl) in Q27.
  prreg HS (21%bv : bv 5) Q21. rewrite (awE_reg ms3 [] 21%nat 21%bv eq_refl) in Q21.
  pose proof (st_ok_pi_restrict_mkst (w_H W3) _ _ _ HS eq_refl) as Hms4.
  apply (EXIT cx fpos ly3 S3 W3 ms (with_vm_backing (m_vm_lazy md3) mat md3) HPRE).
  exists (-22).
  split.
  { rewrite Hms4 at 1. cbn [ms_pc_val mkst]. reflexivity. }
  split.
  { rewrite Q21. exact Hs5. }
  split.
  { apply (aw_base_step_nomem cx fpos ly3 S3 W3 ms3 md3 ms _ HB Hmem);
      try (rewrite Hms4 at 1; cbn [ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst]; reflexivity).
    - exact (proj1 (wvb_fds_fs (m_vm_lazy md3) mat md3)).
    - exact (proj2 (wvb_fds_fs (m_vm_lazy md3) mat md3)).
    - exact HJ3.
    - exact Q2.
    - exact Q9.
    - exact Q8.
    - exact Q18.
    - exact Q19.
    - exact Q24.
    - exact Q3.
    - exact Q4.
    - exact Q25.
    - exact Q26.
    - exact Q27.
  }
  apply (aw_pf_at cx W3 (ms_mem ms) (-22) HP).
  - rewrite Hmem. exact HGNL.
  - rewrite Hmem. intros a Ha. exact (aw_rd_kept cx fpos ly3 S3 W3 ms3 md3 a HPRE HB Ha).
  - intros kbs tab nm al HN HT HA HBl.
    assert (Hnm : nm = Some []).
    { apply (aw_astr_arg_unique SEGS (aw_m0 cx) (aw_name cx)); [exact HA | split; assumption]. }
    rewrite Hnm, aw_wl_name_empty. cbn [w_rc w_reqs w_state].
    split; [reflexivity | split; reflexivity].
Qed.

End b.
End a.

About aw_arm_name_null. About aw_arm_alias_null. About aw_arm_name_empty.
About aw_pf_at. About aw_rd_kept. About aw_shadow_at. About aw_base_step_nomem.
Print Assumptions aw_arm_name_null.
Print Assumptions aw_arm_alias_null.
Print Assumptions aw_arm_name_empty.

