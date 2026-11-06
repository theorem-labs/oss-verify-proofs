(* The op loop of LLVMFuzzerTestOneInput, 0x138ac-0x142a4, bound together at the SR level: _loop.v llvm_loop with
   every program point an SR config (_sr.v llvm_sr_at). Four cases call receive or build_and_receive, SR contracts,
   so a pass can not be an evt run; the nine per-case lemmas give it in continuation form from the case's SR config
   to the latch's (_op08.v llvm_op0_sr / llvm_op8_sr; cases 3, 5, 6, 7 through _lift.v llvm_case_sr_of_evt). The
   switch and the latch are evt stretches, crossed with _lift.v llvm_dispatch_sr and llvm_latch_sr_go.

   The address stream. A receiving op's world is the model's at the heap frame its malloc returned (the op is taken
   at aupd A k a, h_addr_ok a), which the machine chooses; so, unlike _loop.v, the model premise is not the loop's
   result at one stream but at every stream of LLVMFuzzerTestOneInput_c.v llvm_heap_ok (the contract's
   llvm_model_ok), carried pass to pass by TOpsA.v loop_m_step_at. The exit's world is the model's loop result at
   the stream of the addresses the mallocs did return, a stream of the same class. The induction is on the fuel
   OPS_MAX - ops, as in _loop.v. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Contract Img0 AllocSlots AllocRoom MemNorm.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TCb TOps TOpsA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem TContract receive_c TSRGlue
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_sr LLVMFuzzerTestOneInput_lift.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- the model's side ---- *)

(* the class is closed under setting one index to an address a malloc may return *)
Lemma llvm_heap_ok_upd : forall A k a, LLVMFuzzerTestOneInput_c.llvm_heap_ok A -> h_addr_ok a ->
  LLVMFuzzerTestOneInput_c.llvm_heap_ok (aupd A k a).
Proof.
  intros A k a HA Ha j Hj. unfold aupd. destruct (Nat.eqb j k); [exact Ha | exact (HA j Hj)].
Qed.

Lemma llvm_heap_ok_one : LLVMFuzzerTestOneInput_c.llvm_heap_ok (fun _ => 1).
Proof. intros j _. cbv beta. lia. Qed.

(* a loop that runs from a pass with input left does that pass *)
Lemma llvm_op_some : forall f I Bw A D c k, fi_n c <> 0 ->
  (exists Bf, LLVMFuzzerTestOneInput_loop_m (S f) I Bw A D c k = Some (Bf, tt)) ->
  LLVMFuzzerTestOneInput_op_m I Bw A D c k <> None.
Proof.
  intros f I Bw A D c k Hn [Bf HL] HN. cbn [LLVMFuzzerTestOneInput_loop_m] in HL.
  destruct (Z.eqb_spec (fi_n c) 0) as [E|_]; [contradiction|].
  rewrite HN in HL. discriminate HL.
Qed.

(* The loop's result after a pass, at a stream of the class, is the loop's result from before the pass at a stream
   of the class: the same stream if the op read none of it, else that stream with index k set to the address the
   op was taken at. *)
Lemma llvm_loop_m_back : forall f I Bw As D c k a Bres cout k1 Bf A',
  fi_n c <> 0 -> h_addr_ok a ->
  LLVMFuzzerTestOneInput_op_m I Bw (aupd As k a) D c k = Some (Bres, (cout, k1)) ->
  LLVMFuzzerTestOneInput_c.llvm_heap_ok A' ->
  LLVMFuzzerTestOneInput_loop_m f I Bres A' D cout k1 = Some (Bf, tt) ->
  exists A'', LLVMFuzzerTestOneInput_c.llvm_heap_ok A'' /\
    LLVMFuzzerTestOneInput_loop_m (S f) I Bw A'' D c k = Some (Bf, tt).
Proof.
  intros f I Bw As D c k a Bres cout k1 Bf A' Hn Ha HOP HA' HL.
  destruct (op_m_k I Bw (aupd As k a) D c k Bres cout k1 HOP) as [-> | ->].
  - exists A'. split; [exact HA'|].
    cbn [LLVMFuzzerTestOneInput_loop_m].
    destruct (Z.eqb_spec (fi_n c) 0) as [E|_]; [contradiction|].
    rewrite (op_m_keep_ext I Bw (aupd As k a) A' D c k Bres cout HOP). exact HL.
  - exists (aupd A' k a). split; [exact (llvm_heap_ok_upd A' k a HA' Ha)|].
    cbn [LLVMFuzzerTestOneInput_loop_m].
    destruct (Z.eqb_spec (fi_n c) 0) as [E|_]; [contradiction|].
    rewrite (op_m_A_ext I Bw (aupd A' k a) (aupd As k a) D c k) by (rewrite !aupd_at; reflexivity).
    rewrite HOP. cbv beta iota. rewrite <- HL.
    apply loop_m_A_ext. intros i Hi. apply aupd_other. lia.
Qed.

(* The loop's result when the latch leaves after a pass (the pass counter at 0x3fe, or no input left): the world of
   that pass, at the stream with index k set to the address the op was taken at. *)
Lemma llvm_loop_m_out : forall f ops I Bw As D c k a Bres cout k1,
  S f = Z.to_nat (OPS_MAX - ops) -> fi_n c <> 0 -> h_addr_ok a -> (0x3fe < ops \/ fi_n cout = 0) ->
  LLVMFuzzerTestOneInput_op_m I Bw (aupd As k a) D c k = Some (Bres, (cout, k1)) ->
  LLVMFuzzerTestOneInput_c.llvm_heap_ok As ->
  exists A'', LLVMFuzzerTestOneInput_c.llvm_heap_ok A'' /\
    LLVMFuzzerTestOneInput_loop_m (S f) I Bw A'' D c k = Some (Bres, tt).
Proof.
  intros f ops I Bw As D c k a Bres cout k1 HF Hn Ha HW HOP HA.
  exists (aupd As k a). split; [exact (llvm_heap_ok_upd As k a HA Ha)|].
  cbn [LLVMFuzzerTestOneInput_loop_m].
  destruct (Z.eqb_spec (fi_n c) 0) as [E|_]; [contradiction|].
  rewrite HOP. cbv beta iota.
  destruct f as [|f'].
  - reflexivity.
  - destruct HW as [HW|HW]; [unfold OPS_MAX in *; lia|].
    cbn [LLVMFuzzerTestOneInput_loop_m]. rewrite HW. reflexivity.
Qed.

Section LOOPSR.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context (data : Z) (D : list byte).

(* One pass of the loop at the SR level, as the nine case lemmas give it: from the SR config of the case the op byte
   selects, the model's op not None at every address the case's malloc may return, and a continuation from the
   latch with the op's world at the address it did return, the run reaches P. *)
Definition llvm_pass_sr (gp tp : word) (Sp lo : Z) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (L0 : layout) (A0 : astate) (mem0 : word -> option byte) (md0 : Model) (b : sbound) : Prop :=
  forall ops c Bw (As : nat -> Z) (k : nat) cfg (P : config -> Prop),
    llvm_case_sr B API data D gp tp (snd (fuzz_u8_m D c) mod 9) Sp lo ops c (fst (fuzz_u8_m D c)) Bw
      ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b cfg ->
    (forall a, h_addr_ok a -> LLVMFuzzerTestOneInput_op_m timg_plain Bw (aupd As k a) D c k <> None) ->
    (forall a Bres cout k1 cfg', h_addr_ok a ->
       LLVMFuzzerTestOneInput_op_m timg_plain Bw (aupd As k a) D c k = Some (Bres, (cout, k1)) ->
       llvm_latch_sr B API data D gp tp Sp lo ops cout Bres ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
         L0 A0 mem0 md0 b cfg' ->
       SR rsegs cfg' P) ->
    SR rsegs cfg P.

(* llvm_head_sr's own facts on the pass counter and the cursor *)
Lemma llvm_head_sr_facts : forall gp tp Sp lo ops c Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b cfg,
  llvm_head_sr B API data D gp tp Sp lo ops c Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b cfg ->
  0 <= ops < OPS_MAX /\ fi_n c <> 0.
Proof.
  intros gp tp Sp lo ops c Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b cfg H.
  destruct H as (fx' & regs & mem & md & L & A & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPe).
  destruct HPe as (rr & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r8 & r19 & r22 &
                   t3 & t4 & t5 & t6 & mm & j10 & j28 & _ & HOPS & HN & _).
  split; [exact HOPS | exact HN].
Qed.

Lemma llvm_loop_sr : forall fuel gp tp Sp lo ops c (k : nat) Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    L0 A0 mem0 md0 b cfg (P : config -> Prop),
  h_binds B API ->
  llvm_pass_sr gp tp Sp lo ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b ->
  llvm_head_sr B API data D gp tp Sp lo ops c Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b cfg ->
  fuel = Z.to_nat (OPS_MAX - ops) ->
  (forall As, LLVMFuzzerTestOneInput_c.llvm_heap_ok As ->
     exists Bf, LLVMFuzzerTestOneInput_loop_m fuel timg_plain Bw As D c k = Some (Bf, tt)) ->
  (forall Bf cfg',
     (exists As, LLVMFuzzerTestOneInput_c.llvm_heap_ok As /\
        LLVMFuzzerTestOneInput_loop_m fuel timg_plain Bw As D c k = Some (Bf, tt)) ->
     llvm_out_sr B API data D gp tp Sp lo Bf ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b cfg' ->
     SR rsegs cfg' P) ->
  SR rsegs cfg P.
Proof.
  intros fuel. induction fuel as [|f IH];
    intros gp tp Sp lo ops c k Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b cfg P HB HP HH HF HM HO.
  - (* no fuel: ops = OPS_MAX, which the head's invariant rules out *)
    exfalso.
    destruct (llvm_head_sr_facts gp tp Sp lo ops c Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b cfg HH)
      as [HOPS _].
    unfold OPS_MAX in *. lia.
  - destruct (llvm_head_sr_facts gp tp Sp lo ops c Bw ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b cfg HH)
      as [HOPS HN].
    (* any stream of the class: the pass is taken at it with index k set to the malloc's address *)
    pose proof llvm_heap_ok_one as HA1.
    (* 0x138ac-0x138ec: the switch *)
    eapply (llvm_dispatch_sr B API data D); [exact HB | exact HH |].
    intros cfg2 HCASE.
    (* the case, by the hypothesis the per-case files discharge *)
    apply (HP ops c Bw (fun _ => 1) k cfg2 P HCASE).
    { intros a Ha.
      exact (llvm_op_some f _ _ _ _ _ _ HN (HM _ (llvm_heap_ok_upd (fun _ => 1) k a HA1 Ha))). }
    intros a Bres cout k1 cfg3 Ha EOP HLATCH.
    (* 0x1428c-0x142a4: the latch *)
    eapply (llvm_latch_sr_go B API data D); [exact HB | exact HLATCH | |].
    + (* back to the head, one pass on: the model premise at every stream of the class (loop_m_step_at) *)
      intros cfg4 HH'.
      apply (IH gp tp Sp lo (ops + 1) cout k1 Bres ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L0 A0 mem0 md0 b cfg4 P
               HB HP HH').
      * unfold OPS_MAX in *. lia.
      * apply (loop_m_step_at LLVMFuzzerTestOneInput_c.llvm_heap_ok f timg_plain Bw D c k a Bres cout k1).
        -- intros A' HA'. exact (llvm_heap_ok_upd A' k a HA' Ha).
        -- exact HM.
        -- exact HN.
        -- intros A' _.
           rewrite (op_m_A_ext timg_plain Bw (aupd A' k a) (aupd (fun _ => 1) k a) D c k)
             by (rewrite !aupd_at; reflexivity).
           exact EOP.
      * intros Bf cfg5 (A' & HA' & HL) HOUT. apply (HO Bf cfg5); [|exact HOUT].
        exact (llvm_loop_m_back f timg_plain Bw (fun _ => 1) D c k a Bres cout k1 Bf A' HN Ha EOP HA' HL).
    + (* out: the model is finished too, so its last world is this one *)
      intros cfg4 HW HOUT. apply (HO Bres cfg4); [|exact HOUT].
      exact (llvm_loop_m_out f ops timg_plain Bw (fun _ => 1) D c k a Bres cout k1 HF HN Ha HW EOP HA1).
Qed.

End LOOPSR.
