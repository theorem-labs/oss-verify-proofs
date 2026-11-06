(* reac-pw/fuzz_segconf, ASan image A (fuzz_segconf.asan, pin sha256 48c5355bdacb): the assembly of the walk of the
   test harness's entry function LLVMFuzzerTestOneInput from its segment statements. Statement composition only:
   no function of the binary is proved here, and every lemma below is closed (no segment lemma is assumed: each is
   a premise).

   THE FORM: plugin-hostd/fuzz_command's lib/A/Prog/LLVMFuzzerTestOneInput_s02.v (origin/ossv/recipes 501c0d516c69):
   - lt_file_loop, the file loop (head K85024, the harness's structure map section 1.2: at most 4 turns, nfiles = 1 + in[2] % 4),
     by downward induction on the turn with the base case refuted by K85024's `f < nfiles` and lt_nfiles_range;
   - lt_mdecl_loop, the inlined m_declared loop (head K858f4, cut K85ac4 inside the turn), by downward induction on
     i with the base case refuted by K858f4's `i < m->n` and the model's `m->n <= 32` (mconf_encp);
   - lt_assemble, the chain ENTRY .. RET from the 22 segment statements and the ret's, each at every FP state;
   - lt_adapter, LTA_ENTRY to LLVMFuzzerTestOneInput_contract at image A's instance (SegInstA's terms, the entry
     as the listing's BASE + AF_LLVMFuzzerTestOneInput): lt_base is the contract's premises but sa_frm0, in its
     order, and lt_post its post, so the proof is exact. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import LLVMFuzzerTestOneInput_c SegInstA
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

(* no head of a turn f >= 4 is reached, at any FP state: K85024 asks f < nfiles <= 4 *)
Lemma LT_K85024_vacuous : forall f, (4 <= f)%nat -> LTA_K85024 B MT f.
Proof.
intros f Hf fx1. unfold LT_K85024_stmt. intros * _ _ Hlt. exfalso.
pose proof (lt_nfiles_range (x_pl cx)) as H. unfold x_nf in Hlt. lia.
Qed.

(* the file loop, by downward induction on the turn (fuzz_command _s02.v:44-60): one turn is K85024 f -> K850f8 f
   -> (K85208 f -> K853bc f, on the last turn) -> K85414 f -> (K85024 (f + 1) | K854a0) *)
Lemma lt_file_loop :
  (forall fx1 : YK11.FPState, lt_seg_S04_stmt (fx := fx1) B MT) ->
  (forall fx1 : YK11.FPState, lt_seg_S05_stmt (fx := fx1) B MT) ->
  (forall fx1 : YK11.FPState, lt_seg_S06_stmt (fx := fx1) B MT) ->
  (forall fx1 : YK11.FPState, lt_seg_S07_stmt (fx := fx1) B MT) ->
  (forall fx1 : YK11.FPState, lt_seg_S08_stmt (fx := fx1) B MT) ->
  LTA_K854a0 B MT ->
  forall f, LTA_K85024 B MT f.
Proof.
intros H4 H5 H6 H7 H8 HX.
assert (H : forall d f, (4 <= f + d)%nat -> LTA_K85024 B MT f).
{ induction d as [|d IH]; intros f Hfd.
  - apply LT_K85024_vacuous. lia.
  - assert (H14 : LTA_K85414 B MT f) by (intros fx1; exact (H8 fx1 f (IH (Datatypes.S f) ltac:(lia)) HX)).
    assert (H3bc : LTA_K853bc B MT f) by (intros fx1; exact (H7 fx1 f H14)).
    assert (H208 : LTA_K85208 B MT f) by (intros fx1; exact (H6 fx1 f H3bc)).
    assert (H0f8 : LTA_K850f8 B MT f) by (intros fx1; exact (H5 fx1 f H208 H14)).
    intros fx1. exact (H4 fx1 f H0f8). }
intros f. exact (H 4%nat f ltac:(lia)).
Qed.

(* no head of a turn i >= 32 of m_declared is reached: K858f4 asks i < m->n, and the model block holds at most 32
   segments (seg_spec.mconf_encp's second conjunct) *)
Lemma LT_K858f4_vacuous : forall i, (32 <= i)%nat -> LTA_K858f4 B MT i.
Proof.
intros i Hi fx1. unfold LT_K858f4_stmt. intros * _ _ Hlt. intros. exfalso.
match goal with H : lt_cm _ _ _ _ |- _ => destruct H as [_ Hm] end.
unfold sa_mconf, sa_mconfp in Hm. destruct Hm as (bs & _ & Henc).
unfold seg_spec.mconf_encp in Henc. destruct Henc as (_ & Hle & _).
unfold x_mcF in Hlt. lia.
Qed.

(* the m_declared loop, by downward induction on i: one turn is K858f4 i -> (K85ac4 i ->) K858f4 (i + 1), or out
   of the loop to K85bd0 *)
Lemma lt_mdecl_loop :
  (forall fx1 : YK11.FPState, lt_seg_S14_stmt (fx := fx1) B MT) ->
  (forall fx1 : YK11.FPState, lt_seg_S15_stmt (fx := fx1) B MT) ->
  LTA_K85bd0 B MT ->
  forall i, LTA_K858f4 B MT i.
Proof.
intros H14 H15 HX.
assert (H : forall d i, (32 <= i + d)%nat -> LTA_K858f4 B MT i).
{ induction d as [|d IH]; intros i Hid.
  - apply LT_K858f4_vacuous. lia.
  - pose proof (IH (Datatypes.S i) ltac:(lia)) as HN.
    assert (Hac4 : LTA_K85ac4 B MT i) by (intros fx1; exact (H15 fx1 i HN HX)).
    intros fx1. exact (H14 fx1 i Hac4 HN HX). }
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
assert (K44 : LTA_K85c44 B MT) by (intros fx1; exact (H21 fx1 KR)).
assert (K34 : LTA_K85c34 B MT) by (intros fx1; exact (H20 fx1 K44)).
assert (K2c : LTA_K85c2c B MT) by (intros fx1; exact (H19 fx1 K34)).
assert (K24 : LTA_K85c24 B MT) by (intros fx1; exact (H18 fx1 K2c)).
assert (K1c : LTA_K85c1c B MT) by (intros fx1; exact (H17 fx1 K24)).
assert (Kbd0 : LTA_K85bd0 B MT) by (intros fx1; exact (H16 fx1 K1c)).
pose proof (lt_mdecl_loop H14 H15 Kbd0) as KV.
assert (K7cc : LTA_K857cc B MT) by (intros fx1; exact (H13 fx1 (KV 0%nat) Kbd0)).
assert (K7bc : LTA_K857bc B MT) by (intros fx1; exact (H12 fx1 K7cc)).
assert (K6bc : LTA_K856bc B MT) by (intros fx1; exact (H11 fx1 K7bc)).
assert (K59c : LTA_K8559c B MT) by (intros fx1; exact (H10 fx1 K6bc)).
assert (K4a0 : LTA_K854a0 B MT) by (intros fx1; exact (H09 fx1 K59c)).
pose proof (lt_file_loop H04 H05 H06 H07 H08 K4a0) as KF.
assert (K98 : LTA_K84f98 B MT) by (intros fx1; exact (H03 fx1 (KF 0%nat))).
assert (K84 : LTA_K84f84 B MT) by (intros fx1; exact (H02 fx1 K98)).
assert (Keb8 : LTA_K84eb8 B MT) by (intros fx1; exact (H01 fx1 K84)).
intros fx1. exact (H00 fx1 Keb8).
Qed.

(* the contract at image A's instance from the walk's entry statement at the ambient FP state: lt_base is the
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
