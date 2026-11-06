(* The op loop of LLVMFuzzerTestOneInput, 0x138ac-0x142a4, bound together: given one pass (from a case entry
   to the latch, with the model's world), the machine runs the model's loop
   (TModel/TOps.v LLVMFuzzerTestOneInput_loop_m) and leaves at 0x14320 with the model's last world. The fuel is
   OPS_MAX - ops, as the model's comment says, so the induction is on it. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem TContract
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_disp LLVMFuzzerTestOneInput_lat.
Import ListNotations.
Open Scope Z_scope.

Section LOOP.
Context (data : Z) (D : list byte) (I : timg) (A : nat -> Z).

(* One pass of the loop, as the per-case files prove it: from the entry of the case the op byte selects, the
   machine reaches the latch with the world the model's op gives. *)
Definition llvm_pass (Sp lo : Z) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) : Prop :=
  forall m0 gp tp ops c cout B Bres (k k1 : nat) ms Q,
    llvm_case data D m0 gp tp (snd (fuzz_u8_m D c) mod 9) Sp lo ops c (fst (fuzz_u8_m D c)) B
      ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms ->
    LLVMFuzzerTestOneInput_op_m I B A D c k = Some (Bres, (cout, k1)) ->
    (forall ms', llvm_latch data D m0 gp tp Sp lo ops cout Bres
       ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
    evt rsegs Q ms.

Lemma llvm_loop : forall fuel Sp lo ops c (k : nat) B Bf m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms Q,
  llvm_pass Sp lo ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ->
  llvm_head data D m0 gp tp Sp lo ops c B ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms ->
  fuel = Z.to_nat (OPS_MAX - ops) ->
  LLVMFuzzerTestOneInput_loop_m fuel I B A D c k = Some (Bf, tt) ->
  (forall ms', llvm_out data D m0 gp tp Sp lo Bf ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' ->
     evt rsegs Q ms') ->
  evt rsegs Q ms.
Proof.
  intros fuel. induction fuel as [|f IH];
    intros Sp lo ops c k B Bf m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms Q HP HH HF HM HO.
  - (* no fuel: ops = OPS_MAX, which the head's invariant rules out *)
    exfalso. pose proof HH as HH2.
    destruct HH2 as (rr & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r8 & r19 & r22 &
                     t3 & t4 & t5 & t6 & m & j10 & j28 & _ & HOPS & _).
    unfold OPS_MAX in *. lia.
  - pose proof HH as HH2.
    destruct HH2 as (rr & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r8 & r19 & r22 &
                     t3 & t4 & t5 & t6 & m & j10 & j28 & _ & HOPS & HN & HC & _).
    cbn [LLVMFuzzerTestOneInput_loop_m] in HM.
    destruct (Z.eqb_spec (fi_n c) 0) as [E0|_]; [contradiction|].
    destruct (LLVMFuzzerTestOneInput_op_m I B A D c k) as [[Bres [c1 k1]]|] eqn:EOP; [|discriminate HM].
    cbv beta iota in HM.
    (* 0x138ac-0x138ec: the switch *)
    eapply llvm_dispatch; [exact HH|].
    intros ms2 HCASE.
    (* the case, by the hypothesis the per-case files discharge *)
    eapply HP; [exact HCASE | exact EOP |].
    intros ms3 HLATCH.
    (* 0x1428c-0x142a4: the latch *)
    eapply llvm_latch_go; [exact HLATCH | |].
    + (* back to the head, one pass on *)
      intros ms4 HH'.
      eapply (IH Sp lo (ops + 1) c1 k1 Bres Bf m0 gp tp);
        [exact HP | exact HH' | unfold OPS_MAX in *; lia | exact HM | exact HO].
    + (* out: the model is finished too, so its last world is this one *)
      intros ms4 HWHY HOUT.
      assert (EB : Bf = Bres).
      { destruct f as [|f'].
        - cbn [LLVMFuzzerTestOneInput_loop_m] in HM. injection HM as HM. congruence.
        - destruct HWHY as [HWHY|HWHY]; [unfold OPS_MAX in *; lia|].
          cbn [LLVMFuzzerTestOneInput_loop_m] in HM.
          assert (EN : fi_n c1 = 0).
          { rewrite <- HWHY. reflexivity. }
          rewrite EN in HM. cbn [Z.eqb] in HM. injection HM as HM. congruence. }
      apply HO. rewrite EB. exact HOUT.
Qed.

End LOOP.
