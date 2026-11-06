(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): the assembly of
   the walk of the test harness's entry function LLVMFuzzerTestOneInput from its segment statements. Statement
   composition only: no function of the binary is proved here, and every lemma below is closed (no segment lemma
   is assumed: each is a premise).

   THE FORM: the image-B twin of lib/A/Prog/LLVMFuzzerTestOneInput_s02.v (image A's cut-statement commit
   6888a1bad128), with the same lemma names and image B's cuts (plugin-hostd/fuzz_command's lib/B/Prog/
   LLVMFuzzerTestOneInput_s02.v at origin/ossv/recipes 3abc3740de97 is its A file with B's cut names, as here):
   - lt_file_loop, the file loop (head K85110, PLAN-asanubsan-main section 1.2: at most 4 turns, nfiles =
     1 + (in[2] & 3)), by downward induction on the turn with the base case refuted by K85110's `f < nfiles` and
     lt_nfiles_range;
   - lt_mdecl_loop, the inlined m_declared loop (head K85b0c, cut K85d04 inside the turn), by downward induction on
     i with the base case refuted by K85b0c's `i < m->n` and the model's `m->n <= 32` (mconf_encp);
   - lt_assemble, the chain ENTRY .. RET from the 22 segment statements and the ret's, each at every FP state;
   - lt_adapter, LTA_ENTRY to LLVMFuzzerTestOneInput_contract at image B's instance (SegInstB's terms, the entry
     as the listing's BASE + AF_LLVMFuzzerTestOneInput): lt_base is the contract's premises but sa_frm0, in its
     order, and lt_post its post, so the proof is exact. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI00.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegPa SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import LLVMFuzzerTestOneInput_c SegInstB
  LLVMFuzzerTestOneInput_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* decode always builds as many files as its count byte asks: 1 + in[2] % 4, between 1 and 4 *)
Lemma dec_files_length : forall k i, length (SegModel.dec_files k i) = k.
Proof.
induction k as [|k IH]; intros i; cbn [SegModel.dec_files]; [reflexivity|].
destruct (SegModel.fuzz_u8 i) as [lb i1]. destruct (SegModel.fuzz_u16 i1) as [len i2].
destruct (SegModel.fuzz_take i2 len) as [p i3]. cbn [length]. rewrite IH. reflexivity.
Qed.
Lemma lt_nfiles_range : forall pl, 1 <= seg_spec.seg_nfiles pl <= 4.
Proof.
intros pl. unfold seg_spec.seg_nfiles, seg_spec.seg_files, seg_spec.seg_pay, SegModel.decode.
destruct (SegModel.fuzz_u8 (seg_spec.seg_in pl)) as [b0 i1].
destruct (SegModel.fuzz_u8 i1) as [fl i2]. destruct (SegModel.fuzz_u8 i2) as [b2 i3].
cbn [SegModel.p_files]. rewrite dec_files_length.
pose proof (Z.mod_pos_bound b2 4 ltac:(lia)) as H. rewrite Z2Nat.id by lia. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.

(* no head of a turn f >= 4 is reached, at any FP state: K85110 asks f < nfiles <= 4 *)
Lemma LT_K85110_vacuous : forall f, (4 <= f)%nat -> LTA_K85110 B MT f.
Proof.
intros f Hf fx1. unfold LT_K85110_stmt. intros * _ _ Hlt. exfalso.
pose proof (lt_nfiles_range (x_pl cx)) as H. unfold x_nf in Hlt. lia.
Qed.

(* the file loop, by downward induction on the turn (fuzz_command _s02.v:44-60): one turn is K85110 f -> K85210 f
   -> (K85338 f -> K854d4 f, on the last turn) -> K85530 f -> (K85110 (f + 1) | K855c8) *)
Lemma lt_file_loop :
  (forall fx1 : YK11.FPState, lt_seg_S04_stmt (fx := fx1) B MT) ->
  (forall fx1 : YK11.FPState, lt_seg_S05_stmt (fx := fx1) B MT) ->
  (forall fx1 : YK11.FPState, lt_seg_S06_stmt (fx := fx1) B MT) ->
  (forall fx1 : YK11.FPState, lt_seg_S07_stmt (fx := fx1) B MT) ->
  (forall fx1 : YK11.FPState, lt_seg_S08_stmt (fx := fx1) B MT) ->
  LTA_K855c8 B MT ->
  forall f, LTA_K85110 B MT f.
Proof.
intros H4 H5 H6 H7 H8 HX.
assert (H : forall d f, (4 <= f + d)%nat -> LTA_K85110 B MT f).
{ induction d as [|d IH]; intros f Hfd.
  - apply LT_K85110_vacuous. lia.
  - assert (H530 : LTA_K85530 B MT f) by (intros fx1; exact (H8 fx1 f (IH (Datatypes.S f) ltac:(lia)) HX)).
    assert (H4d4 : LTA_K854d4 B MT f) by (intros fx1; exact (H7 fx1 f H530)).
    assert (H338 : LTA_K85338 B MT f) by (intros fx1; exact (H6 fx1 f H4d4)).
    assert (H210 : LTA_K85210 B MT f) by (intros fx1; exact (H5 fx1 f H338 H530)).
    intros fx1. exact (H4 fx1 f H210). }
intros f. exact (H 4%nat f ltac:(lia)).
Qed.

(* no head of a turn i >= 32 of m_declared is reached: K85b0c asks i < m->n, and the model block holds at most 32
   segments (seg_spec.mconf_encp's second conjunct) *)
Lemma LT_K85b0c_vacuous : forall i, (32 <= i)%nat -> LTA_K85b0c B MT i.
Proof.
intros i Hi fx1. unfold LT_K85b0c_stmt. intros * _ _ Hlt. intros. exfalso.
match goal with H : lt_cm _ _ _ _ |- _ => destruct H as [_ Hm] end.
unfold sa_mconf, sa_mconfp in Hm. destruct Hm as (bs & _ & Henc).
unfold seg_spec.mconf_encp in Henc. destruct Henc as (_ & Hle & _).
unfold x_mcF in Hlt. lia.
Qed.

(* the m_declared loop, by downward induction on i: one turn is K85b0c i -> (K85d04 i ->) K85b0c (i + 1), or out
   of the loop to K85e50 *)
Lemma lt_mdecl_loop :
  (forall fx1 : YK11.FPState, lt_seg_S14_stmt (fx := fx1) B MT) ->
  (forall fx1 : YK11.FPState, lt_seg_S15_stmt (fx := fx1) B MT) ->
  LTA_K85e50 B MT ->
  forall i, LTA_K85b0c B MT i.
Proof.
intros H14 H15 HX.
assert (H : forall d i, (32 <= i + d)%nat -> LTA_K85b0c B MT i).
{ induction d as [|d IH]; intros i Hid.
  - apply LT_K85b0c_vacuous. lia.
  - pose proof (IH (Datatypes.S i) ltac:(lia)) as HN.
    assert (Hd04 : LTA_K85d04 B MT i) by (intros fx1; exact (H15 fx1 i HN HX)).
    intros fx1. exact (H14 fx1 i Hd04 HN HX). }
intros i. exact (H 32%nat i ltac:(lia)).
Qed.

(* the whole function from its segments and the ret, each given at every FP state *)
Lemma lt_assemble :
  (forall fx1 : YK11.FPState, lt_seg_S00_stmt (fx := fx1) B MT) ->
  (forall fx1 : YK11.FPState, lt_seg_S01_stmt (fx := fx1) B MT) ->
  (forall fx1 : YK11.FPState, lt_seg_S02_stmt (fx := fx1) B MT) ->
  (forall fx1 : YK11.FPState, lt_seg_S03_stmt (fx := fx1) B MT) ->
  (forall fx1 : YK11.FPState, lt_seg_S04_stmt (fx := fx1) B MT) ->
  (forall fx1 : YK11.FPState, lt_seg_S05_stmt (fx := fx1) B MT) ->
  (forall fx1 : YK11.FPState, lt_seg_S06_stmt (fx := fx1) B MT) ->
  (forall fx1 : YK11.FPState, lt_seg_S07_stmt (fx := fx1) B MT) ->
  (forall fx1 : YK11.FPState, lt_seg_S08_stmt (fx := fx1) B MT) ->
  (forall fx1 : YK11.FPState, lt_seg_S09_stmt (fx := fx1) B MT) ->
  (forall fx1 : YK11.FPState, lt_seg_S10_stmt (fx := fx1) B MT) ->
  (forall fx1 : YK11.FPState, lt_seg_S11_stmt (fx := fx1) B MT) ->
  (forall fx1 : YK11.FPState, lt_seg_S12_stmt (fx := fx1) B MT) ->
  (forall fx1 : YK11.FPState, lt_seg_S13_stmt (fx := fx1) B MT) ->
  (forall fx1 : YK11.FPState, lt_seg_S14_stmt (fx := fx1) B MT) ->
  (forall fx1 : YK11.FPState, lt_seg_S15_stmt (fx := fx1) B MT) ->
  (forall fx1 : YK11.FPState, lt_seg_S16_stmt (fx := fx1) B MT) ->
  (forall fx1 : YK11.FPState, lt_seg_S17_stmt (fx := fx1) B MT) ->
  (forall fx1 : YK11.FPState, lt_seg_S18_stmt (fx := fx1) B MT) ->
  (forall fx1 : YK11.FPState, lt_seg_S19_stmt (fx := fx1) B MT) ->
  (forall fx1 : YK11.FPState, lt_seg_S20_stmt (fx := fx1) B MT) ->
  (forall fx1 : YK11.FPState, lt_seg_S21_stmt (fx := fx1) B MT) ->
  (forall fx1 : YK11.FPState, lt_seg_RET_stmt (fx := fx1) B MT) ->
  LTA_ENTRY B MT.
Proof.
intros H00 H01 H02 H03 H04 H05 H06 H07 H08 H09 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 HR.
assert (KR : LTA_RET B MT) by (intros fx1; exact (HR fx1)).
assert (Kec8 : LTA_K85ec8 B MT) by (intros fx1; exact (H21 fx1 KR)).
assert (Keb4 : LTA_K85eb4 B MT) by (intros fx1; exact (H20 fx1 Kec8)).
assert (Keac : LTA_K85eac B MT) by (intros fx1; exact (H19 fx1 Keb4)).
assert (Kea4 : LTA_K85ea4 B MT) by (intros fx1; exact (H18 fx1 Keac)).
assert (Ke9c : LTA_K85e9c B MT) by (intros fx1; exact (H17 fx1 Kea4)).
assert (Ke50 : LTA_K85e50 B MT) by (intros fx1; exact (H16 fx1 Ke9c)).
pose proof (lt_mdecl_loop H14 H15 Ke50) as KV.
assert (K994 : LTA_K85994 B MT) by (intros fx1; exact (H13 fx1 (KV 0%nat) Ke50)).
assert (K984 : LTA_K85984 B MT) by (intros fx1; exact (H12 fx1 K994)).
assert (K868 : LTA_K85868 B MT) by (intros fx1; exact (H11 fx1 K984)).
assert (K6f4 : LTA_K856f4 B MT) by (intros fx1; exact (H10 fx1 K868)).
assert (K5c8 : LTA_K855c8 B MT) by (intros fx1; exact (H09 fx1 K6f4)).
pose proof (lt_file_loop H04 H05 H06 H07 H08 K5c8) as KF.
assert (K07c : LTA_K8507c B MT) by (intros fx1; exact (H03 fx1 (KF 0%nat))).
assert (K068 : LTA_K85068 B MT) by (intros fx1; exact (H02 fx1 K07c)).
assert (Kf4c : LTA_K84f4c B MT) by (intros fx1; exact (H01 fx1 K068)).
intros fx1. exact (H00 fx1 Kf4c).
Qed.

(* the contract at image B's instance from the walk's entry statement at the ambient FP state: lt_base is the
   contract's premises but sa_frm0, which is the entry statement's second premise; lt_post is its post *)
Lemma lt_adapter : LTA_ENTRY B MT ->
  LLVMFuzzerTestOneInput_contract SEGS B MT (BASE + AF_LLVMFuzzerTestOneInput) STK_LLVMFuzzerTestOneInput emptyA
    RLO_A RHI_A longlA mod40A catA wordsA rolesA gotwA guardA seg_litA_fz seg_litA_rc.
Proof.
intros HE. unfold LLVMFuzzerTestOneInput_contract.
intros ly S W regs mem md ch p n pl j H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15.
exact (HE fx (mkLCX ly S W regs mem md ch p n pl j 0)
  (conj H1 (conj H2 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11 (conj H12
    (conj H13 (conj H14 H15))))))))))))) H3).
Qed.

End e.
End f.
End d.
