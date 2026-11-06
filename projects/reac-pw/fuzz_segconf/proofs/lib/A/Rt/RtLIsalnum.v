(* Row 9 of the interceptor interface (provenance/evidence/interceptors/INTERFACE-A-interceptors.md): musl isalnum,
   called directly (no wrapper) at SegRtPC.PC_isalnum = 0x901a0, stated as RtSeg.aisalnum_realizes.
   - the walk: lib/A/Prog/isalnum.v isalnum_holds (relocated from omx-clap-core/fuzz_manifest), registers only: seven
     instructions and the return, no stack, no store byte;
   - read at the call site by RtBzLift.srr_of_canon, and its post by RtBzLift.rt_post_ro_win with a window of 0
     bytes; the donor-form post (RtBzHStr.rt_post_ro) is restated as RtDefs.art_post by art_of_rt_post_ro below;
   - the answer: the walk returns 1 or 0 as lib/A/Prog/isalnum_c.v alnum_b says, which has the body of
     RtSeg.alnum_b. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YK0i YK14 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YI00 YI04 YK06 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AB1v AF0m AF0x.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs RtBzHBase RtBzHStr RtBzLift RtBzAdapt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtSeg SegRtPC.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.isalnum_c.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.isalnum.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module ISc := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.isalnum_c.
Module ISA := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.isalnum.

(* ---- the donor-form post of a call that writes only its window, as RtDefs.art_post ---- *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

Lemma art_of_rt_post_ro : forall stk ly S (W : world tfibsegs) regs mem md (R : Z -> Prop)
  (Q : bvmap 5 word -> (word -> option byte) -> Prop) W' c',
  ecall_pre_stk tfibsegs B stk ly S W regs mem md ->
  (forall regs' mem' v, getr regs' 10 = w64 v -> R v -> Q regs' mem') ->
  rt_post_ro tfibsegs B stk ly S W regs mem md R W' c' ->
  art_post tfibsegs B stk ly S W regs mem md (fun _ => False) Q W' c'.
Proof.
  intros stk ly S W regs mem md R Q W' c' HPRE HQ
    (EW & regs' & mem' & md' & v & Ec & HAR & HKEEP & HSBM & H10 & _ & HR & HVIEW & HPRES).
  pose proof HPRE as (_ & _ & HWIN).
  split; [exact EW|]. exists regs', mem', md'.
  split; [exact Ec|]. split; [exact HAR|]. split; [exact HKEEP|]. split; [exact HSBM|].
  split; [exact (HQ regs' mem' v H10 HR)|].
  split; [intros a Ha Hs _; exact (HVIEW a Ha Hs)|].
  split; [exact HPRES|].
  intros a Ha. exact (HPRES a (HWIN a Ha)).
Qed.

End a.

(* ---- the answer ---- *)
Lemma alnum_reg : forall c,
  Z_to_bv 64 (if ISc.alnum_b c then 1 else 0) <> w64 0 <-> RtSeg.alnum_b c = true.
Proof.
  intros c. change (RtSeg.alnum_b c) with (ISc.alnum_b c).
  destruct (ISc.alnum_b c); split.
  - intros _. reflexivity.
  - intros _ E. apply (f_equal (@bv_unsigned 64)) in E. unfold w64 in E. rewrite !Z_to_bv_unsigned in E.
    vm_compute in E. discriminate.
  - intros H. exfalso. apply H. reflexivity.
  - intros H. discriminate.
Qed.

(* ---- the contract ---- *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.

Theorem seg_isalnum : RtSeg.aisalnum_realizes tfibsegs B SegRtPC.PC_isalnum.
Proof.
  unfold RtSeg.aisalnum_realizes. intros ly S W regs mem md c HPRE G10 Hc.
  set (v := if ISc.alnum_b c then 1 else 0).
  eapply srr_of_canon.
  - unfold canon_at. eapply ISA.isalnum_holds; [exact Hc | exact G10].
  - intros ms0 ms' model' (a1' & ->) Heqv Hsbm _.
    apply (art_of_rt_post_ro B ESTACK ly S W regs mem md (fun r => r = v) _ W _ HPRE).
    + intros regs' mem' r H10 Er. rewrite H10, Er. unfold v. exact (alnum_reg c).
    + eapply (rt_post_ro_win B LAWS ESTACK 0 ly S W regs mem md (fun r => r = v) _ ms' model' v
                (pre_k_of_stk B ESTACK ly S W regs mem md HPRE) ltac:(unfold ESTACK; lia) Heqv Hsbm);
        try reflexivity.
      * keep_regs.
      * unfold v. destruct (ISc.alnum_b c); lia.
      * intros a Ha. lia.
Qed.

End s.

(* ---- the closing form: AR_laws discharged by the core's law proof; isalnum reads no runtime cell, so the record
   SegBSyms B is not used ---- *)
Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis HB : SegBSyms B.

Theorem seg_isalnum_closed : RtSeg.aisalnum_realizes tfibsegs B SegRtPC.PC_isalnum.
Proof. exact (seg_isalnum B (YG0q.AR_laws_ok tfibsegs B)). Qed.

End closed.

Print Assumptions seg_isalnum_closed.
