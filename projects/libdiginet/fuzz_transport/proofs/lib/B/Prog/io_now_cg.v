(* io_now_cg: image B's io_now, its footprint contract (io_now_F_c.v) translated to the leaf form of the shared kit
   lib/B/Prog/LeafCgKit.v (SRr world walk; image B's twin of lib/A/Prog/LeafCgKit.v), as a STATEMENT (a Definition of
   a Prop), with the mechanical translation lemma transport_io_now_cg_of_F.
   The premises of transport_io_now_cg are io_now_contract_F's premises VERBATIM, read at the call state (registers
   from regs, memory mem, footprint RNG_W W). The function has no frame and writes nothing, so the post is dleaf_post
   with K = IO_NOW_FRAME = 0, WR = [] and RES = Some (io_now_m Bw), the plain contract's result; the statement does not
   mention aowned: the closing file reads it at this unit's model through DgnTransportBCg.transport_leaf_at.
   X is True: io_now_m is total and the plain contract states no model fact but the result. The world relation after
   the call is not in X: dleaf_post keeps every byte outside the call's stack window [sp - ESTACK, sp), and the
   harness globals lie in the image, far below the stack.
   The caller is diginet_session_poll, through the pointer g_s.io.now_us (the calls at 0x8ac5c, 0x8acfc, 0x8ad7c,
   return addresses 0x8ac60, 0x8ad00, 0x8ad80): the address it calls is TImgB.v ti_io_now timg_B, which the model's
   call of io.now_us tests the pointer against. The caller holds the world relation at the view aview (image B's
   segments) (w_H W) mem; on the harness globals' payloads, which are image bytes (never hidden), that view is
   csw_view mem.
   The proof of transport_io_now_cg_of_F takes the kit's leaf_cg_of_evtF_stmt as the Section Hypothesis HGLUE (proved
   by the B kit, as lib/A/Prog/LeafCgGlue.v and LeafCgClose.v do for image A). Form: lib/A/Prog/io_now_cg.v. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA TWorldB check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_now_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_now_F_c LeafCgKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TImg.
Import ListNotations.
Open Scope Z_scope.

(* The entry agrees with the address the model's call of io.now_us tests the session's pointer against (io_now has
   no direct call site, so the listing layer has no TB_ name for it; DgnTransportBList.v AF_io_now is its slot). *)
Lemma io_now_at_timg : IO_NOW = TImg.ti_io_now TImgB.timg_B.
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

Definition transport_io_now_cg : Prop :=
  forall ly S (W : world) regs mem md (lo : Z) (Bw : list byte),
    ecall_pre ly S W regs mem md ->
    let RNG := RNG_W W in let m := mem in let F := fp_regs in let fc := fp_csr in
    let ra := YK11.getr regs (Z_to_bv 5 1) in let sp := YK11.getr regs (Z_to_bv 5 2) in let gp := YK11.getr regs (Z_to_bv 5 3) in let tp := YK11.getr regs (Z_to_bv 5 4) in let t0 := YK11.getr regs (Z_to_bv 5 5) in let t1 := YK11.getr regs (Z_to_bv 5 6) in let t2 := YK11.getr regs (Z_to_bv 5 7) in let s0 := YK11.getr regs (Z_to_bv 5 8) in let s1 := YK11.getr regs (Z_to_bv 5 9) in let a0 := YK11.getr regs (Z_to_bv 5 10) in let a1 := YK11.getr regs (Z_to_bv 5 11) in let a2 := YK11.getr regs (Z_to_bv 5 12) in let a3 := YK11.getr regs (Z_to_bv 5 13) in let a4 := YK11.getr regs (Z_to_bv 5 14) in let a5 := YK11.getr regs (Z_to_bv 5 15) in let a6 := YK11.getr regs (Z_to_bv 5 16) in let a7 := YK11.getr regs (Z_to_bv 5 17) in let s2 := YK11.getr regs (Z_to_bv 5 18) in let s3 := YK11.getr regs (Z_to_bv 5 19) in let s4 := YK11.getr regs (Z_to_bv 5 20) in let s5 := YK11.getr regs (Z_to_bv 5 21) in let s6 := YK11.getr regs (Z_to_bv 5 22) in let s7 := YK11.getr regs (Z_to_bv 5 23) in let s8 := YK11.getr regs (Z_to_bv 5 24) in let s9 := YK11.getr regs (Z_to_bv 5 25) in let s10 := YK11.getr regs (Z_to_bv 5 26) in let s11 := YK11.getr regs (Z_to_bv 5 27) in let t3 := YK11.getr regs (Z_to_bv 5 28) in let t4 := YK11.getr regs (Z_to_bv 5 29) in let t5 := YK11.getr regs (Z_to_bv 5 30) in let t6 := YK11.getr regs (Z_to_bv 5 31) in
    tw_at TMAP_B (csw_view m) Bw ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + IO_NOW_FRAME <= bv_unsigned sp ->
    ExecF.rng RNG IO_NOW_G_NOW 8 ->
    SRr W (cfg_at IO_NOW regs mem md)
      (dleaf_post ly S W regs mem md (Some (TC.io_now_m Bw)) [] (fun _ => True)).

Definition transport_io_now_cg_of_F_stmt : Prop :=
  io_now_contract_F -> transport_io_now_cg.

(* The proof applies the kit's generic translation (HGLUE) to the footprint run: io_now_contract_F at RNG := RNG_W W
   and the call state's registers. Its post gives the rest: the window [sp - 0, sp) is empty, the callee-saved
   registers are the mkR fields read back (only a0 changes), and a0 is the result. *)
Hypothesis HGLUE : leaf_cg_of_evtF_stmt.

Lemma transport_io_now_cg_of_F : transport_io_now_cg_of_F_stmt.
Proof.
  (* no unfold: it would zeta-reduce the statement's lets; intros head-reduces transport_io_now_cg and keeps them as
     local definitions named as in io_now_contract_F *)
  intros HF ly S W regs mem md lo Bw HPRE
    RNG m F fc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    HW HSTK HLO RG.
  (* the run: io_now_contract_F, its premises in order, at the call state's registers *)
  pose proof (HF RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo Bw HW HSTK HLO RG) as RUN.
  refine (HGLUE ly S W regs mem md IO_NOW IO_NOW_FRAME _ [] (Some (TC.io_now_m Bw)) (fun _ => True)
    HPRE _ _ RUN _).
  - (* the window bound *)
    unfold IO_NOW_FRAME, LeafCgKit.ESTACK. lia.
  - (* WR is empty *)
    intros x Hx. unfold LeafCgKit.in_wr in Hx. inversion Hx.
  - (* the post *)
    intros ms' (m' & -> & MU & _ & STK' & _).
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
      * split; [intros r Hr; injection Hr as <-; reflexivity | exact I].
Qed.

End LeafCg.
