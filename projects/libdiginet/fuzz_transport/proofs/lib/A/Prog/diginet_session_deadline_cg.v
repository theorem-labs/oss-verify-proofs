(* diginet_session_deadline_cg: image A's diginet_session_deadline, its footprint contract
   (diginet_session_deadline_F_c.v) translated to the leaf form of the shared kit lib/A/Prog/LeafCgKit.v (SRr world
   walk), as a STATEMENT (a Definition of a Prop), with the mechanical translation lemma
   transport_diginet_session_deadline_cg_of_F.
   The premises of transport_diginet_session_deadline_cg are diginet_session_deadline_contract_F's premises VERBATIM,
   read at the call state (registers from regs, memory mem, footprint RNG_W W): the arguments are the premises on a0
   and a1. The function writes nothing outside its own 16-byte frame, so the post is dleaf_post with WR = [] and RES =
   Some r, the plain contract's result; the statement does not mention aowned: the closing file reads it at this
   unit's model through DgnTransportCg.transport_leaf_at.
   X is True: the plain contract states no model fact but the result. The world relation after the call is not in X:
   dleaf_post keeps every byte outside the call's stack window [sp - ESTACK, sp), and the harness globals lie in the
   image, far below the stack.
   The callers are check_inflight_settle (the call at 0x85db8, return address 0x85dbc) and diginet_session_poll (the
   call at 0x8af54, return address 0x8af58) (DgnTransportList.v PCall TS_diginet_session_deadline). Each holds the
   world relation at the view aview tfibsegs (w_H W) mem; on the harness globals' payloads, which are image bytes
   (never hidden), that view is csw_view mem. asan_cells and the two cells' addresses come from the record's constant
   cells (DgnTransportCg.v transport_cells), and the addressable premise from the zero shadow of g_s's payload: the
   record's Tfib_zero_shadow row (0x5df9c0, 0x5e4118 - 0x5df9c0) (lib/A/AF0m.v:3105), a range of as_zero_shadow B,
   read at the call state through DgnTransportCg.v decode_zshadow_at / decode_zshadow_rd (as
   diginet_session_config_default_cg.v reads g_cfg's).
   The proof of transport_diginet_session_deadline_cg_of_F takes the kit's leaf_cg_of_evtF_stmt as the Section
   Hypothesis HGLUE (proof: LeafCgGlue.v; instance: LeafCgClose.v). Form: check_state_wake_cg.v, with RES = Some r as
   fuzz_frame's diginet_mac_is_digidesign_cg.v. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA TWorldG TWorldA check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_deadline_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_deadline_F_c LeafCgKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require DgnTransportSyms DgnTransportAddr.
Import ListNotations.
Open Scope Z_scope.

(* The entry agrees with the listing layer's address of diginet_session_deadline. *)
Lemma diginet_session_deadline_at_sigma :
  DIGINET_SESSION_DEADLINE = DgnTransportAddr.transport_sigma DgnTransportSyms.TS_diginet_session_deadline.
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

Definition transport_diginet_session_deadline_cg : Prop :=
  forall ly S (W : world) regs mem md (lo now r : Z) (Bw : list byte),
    ecall_pre ly S W regs mem md ->
    let RNG := RNG_W W in let m := mem in let F := fp_regs in let fc := fp_csr in
    let ra := YK11.getr regs (Z_to_bv 5 1) in let sp := YK11.getr regs (Z_to_bv 5 2) in let gp := YK11.getr regs (Z_to_bv 5 3) in let tp := YK11.getr regs (Z_to_bv 5 4) in let t0 := YK11.getr regs (Z_to_bv 5 5) in let t1 := YK11.getr regs (Z_to_bv 5 6) in let t2 := YK11.getr regs (Z_to_bv 5 7) in let s0 := YK11.getr regs (Z_to_bv 5 8) in let s1 := YK11.getr regs (Z_to_bv 5 9) in let a0 := YK11.getr regs (Z_to_bv 5 10) in let a1 := YK11.getr regs (Z_to_bv 5 11) in let a2 := YK11.getr regs (Z_to_bv 5 12) in let a3 := YK11.getr regs (Z_to_bv 5 13) in let a4 := YK11.getr regs (Z_to_bv 5 14) in let a5 := YK11.getr regs (Z_to_bv 5 15) in let a6 := YK11.getr regs (Z_to_bv 5 16) in let a7 := YK11.getr regs (Z_to_bv 5 17) in let s2 := YK11.getr regs (Z_to_bv 5 18) in let s3 := YK11.getr regs (Z_to_bv 5 19) in let s4 := YK11.getr regs (Z_to_bv 5 20) in let s5 := YK11.getr regs (Z_to_bv 5 21) in let s6 := YK11.getr regs (Z_to_bv 5 22) in let s7 := YK11.getr regs (Z_to_bv 5 23) in let s8 := YK11.getr regs (Z_to_bv 5 24) in let s9 := YK11.getr regs (Z_to_bv 5 25) in let s10 := YK11.getr regs (Z_to_bv 5 26) in let s11 := YK11.getr regs (Z_to_bv 5 27) in let t3 := YK11.getr regs (Z_to_bv 5 28) in let t4 := YK11.getr regs (Z_to_bv 5 29) in let t5 := YK11.getr regs (Z_to_bv 5 30) in let t6 := YK11.getr regs (Z_to_bv 5 31) in
    a0 = Z_to_bv 64 DIGINET_SESSION_DEADLINE_S ->
    a1 = Z_to_bv 64 now ->
    0 <= now < 2 ^ 64 ->
    tw_at TMAP_A (csw_view m) Bw ->
    TS0.diginet_session_deadline_m Bw now = Some r ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + DIGINET_SESSION_DEADLINE_FRAME <= bv_unsigned sp ->
    off_stk sp DIGINET_SESSION_DEADLINE_FRAME TG.G_HARNESS_LO (TG.G_HARNESS_HI - TG.G_HARNESS_LO) ->
    app_mem (bv_unsigned sp - DIGINET_SESSION_DEADLINE_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    asan_cells m ->
    off_stk sp DIGINET_SESSION_DEADLINE_FRAME GOT_CELL_K 8 ->
    off_stk sp DIGINET_SESSION_DEADLINE_FRAME CELL_K 8 ->
    addressable m DIGINET_SESSION_DEADLINE_S DIGINET_SESSION_DEADLINE_SN ->
    ExecF.rng RNG (bv_unsigned sp - DIGINET_SESSION_DEADLINE_FRAME) DIGINET_SESSION_DEADLINE_FRAME ->
    ExecF.rng RNG GOT_CELL_K 8 ->
    ExecF.rng RNG CELL_K 8 ->
    ExecF.rng RNG DIGINET_SESSION_DEADLINE_S DIGINET_SESSION_DEADLINE_SN ->
    ExecF.rng RNG (shadow_addr DIGINET_SESSION_DEADLINE_S)
      (shadow_addr (DIGINET_SESSION_DEADLINE_S + DIGINET_SESSION_DEADLINE_SN - 1) -
       shadow_addr DIGINET_SESSION_DEADLINE_S + 1) ->
    SRr W (cfg_at DIGINET_SESSION_DEADLINE regs mem md)
      (dleaf_post ly S W regs mem md (Some r) [] (fun _ => True)).

Definition transport_diginet_session_deadline_cg_of_F_stmt : Prop :=
  diginet_session_deadline_contract_F -> transport_diginet_session_deadline_cg.

(* The proof applies the kit's generic translation (HGLUE) to the footprint run: diginet_session_deadline_contract_F
   at RNG := RNG_W W and the call state's registers. Its post gives the rest: the window is its munch range, the
   window's bytes come from its stk (as mrd), the callee-saved registers are the mkR fields read back (only
   caller-saved registers change), and a0 is the result r. *)
Hypothesis HGLUE : leaf_cg_of_evtF_stmt.

Lemma transport_diginet_session_deadline_cg_of_F : transport_diginet_session_deadline_cg_of_F_stmt.
Proof.
  (* no unfold: it would zeta-reduce the statement's lets; intros head-reduces transport_diginet_session_deadline_cg
     and keeps them as local definitions named as in diginet_session_deadline_contract_F *)
  intros HF ly S W regs mem md lo now r Bw HPRE
    RNG m F fc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    HA0 HA1 HNOW HW HM HSTK HLO HOFF APW1 APW2 CELLS DG DC AS RFR RGOT RCELL RS RSS.
  (* the run: diginet_session_deadline_contract_F, its premises in order, at the call state's registers *)
  pose proof (HF RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo now r Bw HA0 HA1 HNOW HW HM HSTK HLO HOFF APW1 APW2 CELLS DG DC AS RFR RGOT RCELL RS RSS) as RUN.
  refine (HGLUE ly S W regs mem md DIGINET_SESSION_DEADLINE DIGINET_SESSION_DEADLINE_FRAME _ [] (Some r)
    (fun _ => True) HPRE _ _ RUN _).
  - (* the window bound *)
    unfold DIGINET_SESSION_DEADLINE_FRAME, LeafCgKit.ESTACK. lia.
  - (* WR is empty *)
    intros x Hx. unfold LeafCgKit.in_wr in Hx. inversion Hx.
  - (* the post *)
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m' & -> & MU & _ & STK' & _).
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
      * split; [intros k Hk; injection Hk as <-; reflexivity | exact I].
Qed.

End LeafCg.
