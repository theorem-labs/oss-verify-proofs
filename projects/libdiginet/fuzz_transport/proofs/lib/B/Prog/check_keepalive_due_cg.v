(* check_keepalive_due_cg: image B's check_keepalive_due, its footprint contract (check_keepalive_due_F_c.v)
   translated to the leaf form of the shared kit lib/B/Prog/LeafCgKit.v (SRr world walk; image B's twin of
   lib/A/Prog/LeafCgKit.v), as a STATEMENT (a Definition of a Prop), with the mechanical translation lemma
   transport_check_keepalive_due_cg_of_F.
   The premises of transport_check_keepalive_due_cg are check_keepalive_due_contract_F's premises VERBATIM, read at
   the call state (registers from regs, memory mem, footprint RNG_W W). The function has no argument, writes nothing
   outside its own 16-byte frame and returns nothing, so the post is dleaf_post with RES = None and WR = [], and the
   statement does not mention aowned: the closing file reads it at this unit's model through
   DgnTransportBCg.transport_leaf_at. X is the plain contract's model fact Bw' = Bw. The world relation after the call
   is not in X: dleaf_post keeps every byte outside the call's stack window [sp - ESTACK, sp), and the harness globals
   lie in the image, far below the stack.
   The caller is io_send (the call at 0x83254, return address 0x83258; DgnTransportBList.v PCall
   TB_check_keepalive_due). It holds the world relation at the view aview (image B's segments) (w_H W) mem; on the
   harness globals' payloads, which are image bytes (never hidden), that view is csw_view mem.
   The proof of transport_check_keepalive_due_cg_of_F takes the kit's leaf_cg_of_evtF_stmt as the Section Hypothesis
   HGLUE (proved by the B kit, as lib/A/Prog/LeafCgGlue.v and LeafCgClose.v do for image A).
   Form: lib/A/Prog/check_keepalive_due_cg.v. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA TWorldB check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_keepalive_due_c check_keepalive_due_F_c LeafCgKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require DgnTransportBSyms DgnTransportBAddr.
Import ListNotations.
Open Scope Z_scope.

(* The entry agrees with the listing layer's address of check_keepalive_due. *)
Lemma check_keepalive_due_at_sigma :
  CHECK_KEEPALIVE_DUE = DgnTransportBAddr.transportb_sigma DgnTransportBSyms.TB_check_keepalive_due.
Proof. reflexivity. Qed.

Section LeafCg.
Context {fx : YK11.FPState}.
Variable world : Type.                                                (* YA0n.v:17 *)
Variable w_H : world -> word -> bool.                                 (* YA0n.v:18 *)
Variable SRr : world -> config -> (world -> config -> Prop) -> Prop.    (* YA0n.v:34 *)
Variable alayout : Type.                                              (* YG0f.v:42 *)
Variable astate : Type.                                               (* YG00.v:153 *)
Variable AR : alayout -> astate -> world -> (word -> option byte) -> Model -> Prop.  (* YG0n.v:489 *)
Variable aview : (word -> bool) -> (word -> option byte) -> Z -> option Z.          (* YG0n.v:17 *)
Variable same_but_materialized : Model -> Model -> Prop.              (* YK04.v:538 *)
Variable ly_stk_lo ly_stk_hi : alayout -> Z.                          (* YG0f.v *)
Variable ret_ok : word -> Prop.                                       (* YK0s.v:192 *)
Variable as_gp as_tp : Z.                                             (* asyms B *)
Variable aowned : alayout -> astate -> Z -> Prop.                     (* YG0n.v:235 *)
(* The kit's definitions and facts at these names (LeafCgKit.v; argument order = the kit's Section order). *)
Let ecall_pre := @LeafCgKit.ecall_pre world w_H alayout astate AR ly_stk_lo ly_stk_hi ret_ok as_gp as_tp.
Let RNG_W := @LeafCgKit.RNG_W world w_H.
Let dleaf_post := @LeafCgKit.dleaf_post fx world w_H alayout astate AR aview same_but_materialized.
Let leaf_cg_of_evtF_stmt := @LeafCgKit.leaf_cg_of_evtF_stmt fx world w_H SRr alayout astate AR aview
  same_but_materialized ly_stk_lo ly_stk_hi ret_ok as_gp as_tp aowned.

Definition transport_check_keepalive_due_cg : Prop :=
  forall ly S (W : world) regs mem md (lo : Z) (Bw Bw' : list byte),
    ecall_pre ly S W regs mem md ->
    let RNG := RNG_W W in let m := mem in let F := fp_regs in let fc := fp_csr in
    let ra := YK11.getr regs (Z_to_bv 5 1) in let sp := YK11.getr regs (Z_to_bv 5 2) in let gp := YK11.getr regs (Z_to_bv 5 3) in let tp := YK11.getr regs (Z_to_bv 5 4) in let t0 := YK11.getr regs (Z_to_bv 5 5) in let t1 := YK11.getr regs (Z_to_bv 5 6) in let t2 := YK11.getr regs (Z_to_bv 5 7) in let s0 := YK11.getr regs (Z_to_bv 5 8) in let s1 := YK11.getr regs (Z_to_bv 5 9) in let a0 := YK11.getr regs (Z_to_bv 5 10) in let a1 := YK11.getr regs (Z_to_bv 5 11) in let a2 := YK11.getr regs (Z_to_bv 5 12) in let a3 := YK11.getr regs (Z_to_bv 5 13) in let a4 := YK11.getr regs (Z_to_bv 5 14) in let a5 := YK11.getr regs (Z_to_bv 5 15) in let a6 := YK11.getr regs (Z_to_bv 5 16) in let a7 := YK11.getr regs (Z_to_bv 5 17) in let s2 := YK11.getr regs (Z_to_bv 5 18) in let s3 := YK11.getr regs (Z_to_bv 5 19) in let s4 := YK11.getr regs (Z_to_bv 5 20) in let s5 := YK11.getr regs (Z_to_bv 5 21) in let s6 := YK11.getr regs (Z_to_bv 5 22) in let s7 := YK11.getr regs (Z_to_bv 5 23) in let s8 := YK11.getr regs (Z_to_bv 5 24) in let s9 := YK11.getr regs (Z_to_bv 5 25) in let s10 := YK11.getr regs (Z_to_bv 5 26) in let s11 := YK11.getr regs (Z_to_bv 5 27) in let t3 := YK11.getr regs (Z_to_bv 5 28) in let t4 := YK11.getr regs (Z_to_bv 5 29) in let t5 := YK11.getr regs (Z_to_bv 5 30) in let t6 := YK11.getr regs (Z_to_bv 5 31) in
    tw_at TMAP_B (csw_view m) Bw ->
    TC.check_keepalive_due_m Bw = Some (Bw', tt) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_KEEPALIVE_DUE_FRAME <= bv_unsigned sp ->
    off_stk sp CHECK_KEEPALIVE_DUE_FRAME TG.G_HARNESS_B_LO (TG.G_HARNESS_B_HI - TG.G_HARNESS_B_LO) ->
    ExecF.rng RNG (bv_unsigned sp - CHECK_KEEPALIVE_DUE_FRAME) CHECK_KEEPALIVE_DUE_FRAME ->
    ExecF.rng RNG CHECK_KEEPALIVE_DUE_STATE 4 ->
    ExecF.rng RNG CHECK_KEEPALIVE_DUE_FLY_ON 4 ->
    ExecF.rng RNG CHECK_KEEPALIVE_DUE_NOW 8 ->
    ExecF.rng RNG CHECK_KEEPALIVE_DUE_BACKOFF 8 ->
    ExecF.rng RNG CHECK_KEEPALIVE_DUE_NEXT_KA 8 ->
    SRr W (cfg_at CHECK_KEEPALIVE_DUE regs mem md)
      (dleaf_post ly S W regs mem md None [] (fun _ => Bw' = Bw)).

Definition transport_check_keepalive_due_cg_of_F_stmt : Prop :=
  check_keepalive_due_contract_F -> transport_check_keepalive_due_cg.

(* The proof applies the kit's generic translation (HGLUE) to the footprint run: check_keepalive_due_contract_F at
   RNG := RNG_W W and the call state's registers. Its post gives the rest: the window is its munch range, the
   window's bytes come from its stk (as mrd), the callee-saved registers are the mkR fields read back (only a0, a1
   and a2 change), and X is its Bw' = Bw. *)
Hypothesis HGLUE : leaf_cg_of_evtF_stmt.

Lemma transport_check_keepalive_due_cg_of_F : transport_check_keepalive_due_cg_of_F_stmt.
Proof.
  (* no unfold: it would zeta-reduce the statement's lets; intros head-reduces transport_check_keepalive_due_cg and
     keeps them as local definitions named as in check_keepalive_due_contract_F *)
  intros HF ly S W regs mem md lo Bw Bw' HPRE
    RNG m F fc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    HW HM HSTK HLO HOFF RFR RW1 RW2 RW3 RW4 RW5.
  (* the run: check_keepalive_due_contract_F, its premises in order, at the call state's registers *)
  pose proof (HF RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo Bw Bw' HW HM HSTK HLO HOFF RFR RW1 RW2 RW3 RW4 RW5) as RUN.
  refine (HGLUE ly S W regs mem md CHECK_KEEPALIVE_DUE CHECK_KEEPALIVE_DUE_FRAME _ [] None (fun _ => Bw' = Bw)
    HPRE _ _ RUN _).
  - (* the window bound *)
    unfold CHECK_KEEPALIVE_DUE_FRAME, LeafCgKit.ESTACK. lia.
  - (* WR is empty *)
    intros x Hx. unfold LeafCgKit.in_wr in Hx. inversion Hx.
  - (* the post *)
    intros ms' (a0' & a1' & a2' & m' & -> & MU & _ & STK' & EB & _).
    eexists _, m'. split; [reflexivity|].
    split; [exact MU|].
    split.
    + intros x [Hx | Hx]; [| unfold LeafCgKit.in_wr in Hx; inversion Hx].
      change (LeafCgKit.spZ regs) with (bv_unsigned sp) in Hx.
      destruct STK' as (_ & _ & STKx).
      destruct (STKx x ltac:(lia)) as (_ & b & Hb).
      exists b. exact Hb.
    + split.
      * intros k Hk. unfold LeafCgKit.acallee_saved in Hk.
        destruct Hk as [-> | [-> | [-> | [-> | [-> | Hk]]]]]; [reflexivity .. |].
        assert (E : k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27)
          by lia.
        destruct E as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; reflexivity.
      * split; [intros k Hk; discriminate Hk | exact EB].
Qed.

End LeafCg.
