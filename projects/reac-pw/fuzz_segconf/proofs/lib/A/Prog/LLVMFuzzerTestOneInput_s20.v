(* reac-pw/fuzz_segconf, ASan image A (fuzz_segconf.asan, pin sha256 48c5355bdacb): file group _s20, segments S11
   (0x856bc .. 0x857b8: the probe loop, the "nosuch0" pair, checks 25 and 26, calloc(cap + 1, 18)) and S12 (0x857bc ..
   0x857c8: calloc(cap + 1, 20)) of the test harness's entry function LLVMFuzzerTestOneInput (0x84d34).

   proves function LLVMFuzzerTestOneInput (reuse search: origin/main@6e24fa4d602c origin/ossv/recipes@3abc3740de97
   origin/ossv/candidates@ee89628c9971 origin/release/pau-projects-recipes@b6a0088adcb4 / the stream's proof index
   LLVMFuzzerTestOneInput + four-ref git grep; output pasted verbatim in
   the walk's shared brief; checker (fresh, read-only): CONFIRM; none: written new)

   The statements proved: lt_seg_S11_stmt and lt_seg_S12_stmt of LLVMFuzzerTestOneInput_defs.v, each at every FP
   state (lt_seg_S11, lt_seg_S12 below). S11 is cut at the inner points of the kit LLVMFuzzerTestOneInput_s20k.v
   (H i, A i, Z i, N, NZ); each piece is its own module under one Section header:
     K856bc -> H 0 | N         s20_L0   _s20e.v  (0x856bc .. 0x856fc: s10, check 25, n, the loop's registers)
     H i -> A i                s20_L1   _s20c.v  (the probe in scope, snprintf(probe, 18, "%sx", m->seg[i].name))
     A i -> Z i                s20_L2   _s20d.v  (strlen, m_find, and check_absent on a miss)
     Z i -> H (i + 1) | N      s20_L3   _s20e.v  (the probe out of scope, check 26, the latch)
     N -> NZ                   s20_L4   _s20d.v  (m_find and check_absent of "nosuch0")
     NZ -> K857bc              s20_L5   _s20f.v  (calloc(cap + 1, 18))
     K857bc -> K857cc          s20_S12  _s20f.v  (calloc(cap + 1, 20))
   This file closes the probe loop by downward induction on the turn (m->n <= 32) and composes the pieces. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI00 YC5d YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase SegPaLib SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import LLVMFuzzerTestOneInput_c SegInstA
  LLVMFuzzerTestOneInput_inst LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s10k LLVMFuzzerTestOneInput_s20k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require m_find_c check_absent_c.
(* the pieces: each proves its segment lemmas under the same Section header *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require LLVMFuzzerTestOneInput_s20c LLVMFuzzerTestOneInput_s20d
  LLVMFuzzerTestOneInput_s20e LLVMFuzzerTestOneInput_s20f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtSegCalloc RtPFSeg RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require AF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ---- the two segment statements, at every FP state ---- *)
Section top. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variables (cstk snp_lo snp_hi : Z) (snp_cr : list (Z * Z)).
Hypothesis ACALLOC4 : forall fx0 : YK11.FPState,
  @RtSegCalloc.aseg_calloc04_rule fx0 rc SK SEGS B MT (SIG SS___interceptor_trampoline_calloc) cstk.
Hypothesis HCSTK : 0 <= cstk /\ LTOI_FRAME_MAX + cstk <= STK_LLVMFuzzerTestOneInput.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  @RtPFSeg.seg_asnprintf_realizes fx0 rc SEGS B snp_lo snp_hi snp_cr (SIG SS___interceptor_trampoline_snprintf)
    gotwA guardA.
Hypothesis ASTRLEN : forall fx0 : YK11.FPState,
  @RtString.astrlen_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strlen).
Hypothesis HM_FIND : forall fx0 : YK11.FPState,
  @m_find_c.m_find_contract fx0 rc SK SEGS B (BASE + AF_m_find) STK_m_find RLO_A RHI_A.
Hypothesis HCHECK_ABSENT : forall fx0 : YK11.FPState,
  @check_absent_c.check_absent_contract fx0 rc SK SEGS B (BASE + AF_check_absent) STK_check_absent RLO_A RHI_A.
Hypothesis HSNP_LIT : forall x, In x LLVMFuzzerTestOneInput_c.LTOI_LITS ->
  snp_lo <= seg_litA_fz x /\ seg_litA_fz x + Z.of_nat (length x) + 1 <= gotwA.
Hypothesis HSNP_CR : Forall (fun r => snp_lo <= fst r /\ 0 <= snd r /\ fst r + snd r <= snp_hi) snp_cr.
Hypothesis HSNP_LO : 0 <= snp_lo.
Hypothesis HSNP_CEIL : snp_hi <= alloc_ceiling.
Hypothesis HSNP_FAKE : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> snp_hi <= ly_F ly.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis TL : PALib B.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis IMGS : s10_img.
Hypothesis BSYM : AF0m.SegBSyms B.

(* a premise of a lemma of the section above, at an FP state fx1: a hypothesis of this section (the image numbers
   by unification), a continuation in the context, or a contract given at every FP state *)
Ltac s20_close := solve [ eassumption | match goal with H : forall fx0 : YK11.FPState, _ |- _ => exact (H _) end ].

(* no turn i >= 32 of the probe loop is reached: H i asks i < m->n, and m->n <= 32 (mconf_encp) *)
Lemma s20_H_vacuous : forall i, (32 <= i)%nat -> S20A_H B MT i.
Proof.
intros i Hi fx1. unfold S20_H_stmt. intros * _ _ Hlt Hctx _. exfalso.
destruct Hctx as (_ & _ & _ & _ & [_ Hm]).
unfold sa_mconf, sa_mconfp in Hm. destruct Hm as (bs & _ & Henc).
unfold seg_spec.mconf_encp in Henc. destruct Henc as (_ & Hle & _).
unfold x_mcF in Hlt. lia.
Qed.

(* the probe loop, by downward induction on the turn: H i -> A i -> Z i -> (H (i + 1) | N) *)
Lemma s20_loop : S20A_N B MT -> forall i, S20A_H B MT i.
Proof.
intros HN.
assert (H : forall d i, (32 <= i + d)%nat -> S20A_H B MT i).
{ induction d as [|d IH]; intros i Hid.
  - apply s20_H_vacuous. lia.
  - pose proof (IH (Datatypes.S i) ltac:(lia)) as HS.
    assert (HZ : S20A_Z B MT i) by (intros fx1; eapply LLVMFuzzerTestOneInput_s20e.s20_L3; s20_close).
    assert (HA : S20A_A B MT i) by (intros fx1; eapply LLVMFuzzerTestOneInput_s20d.s20_L2; s20_close).
    intros fx1. eapply LLVMFuzzerTestOneInput_s20c.s20_L1; s20_close. }
intros i. exact (H 32%nat i ltac:(lia)).
Qed.

Theorem lt_seg_S12 : forall fx1 : YK11.FPState, lt_seg_S12_stmt (fx := fx1) B MT.
Proof. intros fx1 HK. eapply LLVMFuzzerTestOneInput_s20f.s20_S12; s20_close. Qed.

Theorem lt_seg_S11 : forall fx1 : YK11.FPState, lt_seg_S11_stmt (fx := fx1) B MT.
Proof.
intros fx1 HK.
assert (HNZ : S20A_NZ B MT) by (intros fx2; eapply LLVMFuzzerTestOneInput_s20f.s20_L5; s20_close).
assert (HN : S20A_N B MT) by (intros fx2; eapply LLVMFuzzerTestOneInput_s20d.s20_L4; s20_close).
pose proof (s20_loop HN 0%nat) as H0.
eapply LLVMFuzzerTestOneInput_s20e.s20_L0; s20_close.
Qed.
End top.
