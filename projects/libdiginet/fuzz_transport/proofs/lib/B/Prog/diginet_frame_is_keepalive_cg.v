(* Modified by Theorem Labs, 2026-10: the leaf form of proofs/libreac/fuzz_decode/lib/A/Prog/reac_frame_is_reac_cg.v (with check_braid_cg.v's register equation for an argument given as a Z value), restated for diginet_frame_is_keepalive of libdiginet/fuzz_frame's image A; module paths changed; the run is diginet_frame_is_keepalive_F_c.v's, which has no shadow_rw premise. *)
(* Modified by Theorem Labs, 2026-10: libdiginet/fuzz_frame image B's copy of this unit's image-A statement text lib/A/Prog/diginet_frame_is_keepalive_cg.v: Img0 / AsanCells / AsanKA / diginet_frame_is_keepalive_c / diginet_frame_is_keepalive_F_c / LeafCgKit are lib/B's, and the target carries image B's UBSan premise `f mod 8 = 0` (the trap 0x81f8c / 0x81f90, unimp at 0x82024) and `0 < body < 2^64` in place of image A's `0 <= body < 2^64` (the trap 0x81ff4, unimp at 0x82024), as lib/B/Prog/diginet_frame_is_keepalive_F_c.v states them, which the translation lemma passes on to the footprint contract; LeafCgKit's generic translation is unchanged. *)
(* transport_diginet_frame_is_keepalive_cg: image B's diginet_frame_is_keepalive (entry 0x8b128, frame 16), its
   footprint contract diginet_frame_is_keepalive_contract_F (diginet_frame_is_keepalive_F_c.v) translated to the leaf
   form of the shared kit lib/B/Prog/LeafCgKit.v (SRr world walk), as a STATEMENT. RELOCATED from
   libdiginet/fuzz_frame lib/B/Prog/diginet_frame_is_keepalive_cg.v (file sha256 121aef959c37; donor not released):
   names, module paths, the entry and the caller changed; added the lemma diginet_frame_is_keepalive_at_sigma (the
   entry against the listing layer, with the Require of DgnTransportBSyms and DgnTransportBAddr) as in
   check_latest_frame_cg.v.
   The premises of the target are diginet_frame_is_keepalive_F_c.v's premises VERBATIM, read at the call state
   (registers from regs, memory mem, footprint RNG_W W), after the equation a0 = f; among them image B's two UBSan
   premises f mod 8 = 0 and, in the premise of the path cmd = 0 and blen = 1, body <> 0
   (diginet_frame_is_keepalive_c.v; fuzz_frame's text states 0 < body for every path), which the translation lemma
   passes on to the footprint contract, as in fuzz_frame.
   The function writes nothing outside its frame [sp - 16, sp): WR = [] and the statement does not mention aowned
   (a read-only leaf, DgnTransportBCg.transport_leaf_at). Result: a0 = 1 when keepalive_of cmd blen bb, else 0.
   Its caller on_data calls it at 0x88d2c (return address 0x88d30; DgnTransportBList.v PCall
   TB_diginet_frame_is_keepalive) with a0 = s4 = f; on_data's own UBSan check of f (0x88b3c-0x88b80) gives
   f mod 8 = 0 there, and f's body is buf + 30, which gives body <> 0 (diginet_frame_is_keepalive_c.v).
   The kit (names, verbatim copies, the facts a proof may assume, the generic translation lemma) is the shared kit
   lib/B/Prog/LeafCgKit.v; this file re-declares the kit's Section Variables and names its definitions.
   Form: fuzz_frame's lib/B/Prog/diginet_frame_is_keepalive_cg.v (shape, Some result, register equation and
   proof). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA diginet_frame_is_keepalive_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF MState Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_frame_is_keepalive_F_c LeafCgKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require DgnTransportBSyms DgnTransportBAddr.
Import ListNotations.
Open Scope Z_scope.

(* The entry agrees with the listing layer's address of diginet_frame_is_keepalive. *)
Lemma diginet_frame_is_keepalive_at_sigma :
  DIGINET_FRAME_IS_KEEPALIVE = DgnTransportBAddr.transportb_sigma DgnTransportBSyms.TB_diginet_frame_is_keepalive.
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
Let dleaf_post_fx := @LeafCgKit.dleaf_post_fx fx world w_H alayout astate AR aview same_but_materialized.
Let bridge_evtF_stmt := @LeafCgKit.bridge_evtF_stmt world w_H SRr same_but_materialized.
Let SRr_ret_stmt := @LeafCgKit.SRr_ret_stmt world SRr.
Let AR_frame_stmt := @LeafCgKit.AR_frame_stmt world w_H alayout astate AR aview aowned.
Let AR_stack_stmt := @LeafCgKit.AR_stack_stmt world alayout astate AR ly_stk_lo ly_stk_hi aowned.
Let AR_sbm_stmt := @LeafCgKit.AR_sbm_stmt world alayout astate AR same_but_materialized.
Let aview_ext_stmt := @LeafCgKit.aview_ext_stmt aview.
Let aview_some_stmt := @LeafCgKit.aview_some_stmt aview.
Let ret_ok_stmt := @LeafCgKit.ret_ok_stmt ret_ok.
Let leaf_cg_of_evtF_stmt := @LeafCgKit.leaf_cg_of_evtF_stmt fx world w_H SRr alayout astate AR aview
  same_but_materialized ly_stk_lo ly_stk_hi ret_ok as_gp as_tp aowned.
Let leaf_cg_of_evtF_fx_stmt := @LeafCgKit.leaf_cg_of_evtF_fx_stmt fx world w_H SRr alayout astate AR aview
  same_but_materialized ly_stk_lo ly_stk_hi ret_ok as_gp as_tp aowned.

Definition transport_diginet_frame_is_keepalive_cg : Prop :=
  forall ly S (W : world) regs mem md (f cmd body lo : Z) (bb : list byte),
    ecall_pre ly S W regs mem md ->
    YK11.getr regs (Z_to_bv 5 10) = Z_to_bv 64 f ->
    let RNG := RNG_W W in let m := mem in let F := fp_regs in let fc := fp_csr in
    let ra := YK11.getr regs (Z_to_bv 5 1) in let sp := YK11.getr regs (Z_to_bv 5 2) in let gp := YK11.getr regs (Z_to_bv 5 3) in let tp := YK11.getr regs (Z_to_bv 5 4) in let t0 := YK11.getr regs (Z_to_bv 5 5) in let t1 := YK11.getr regs (Z_to_bv 5 6) in let t2 := YK11.getr regs (Z_to_bv 5 7) in let s0 := YK11.getr regs (Z_to_bv 5 8) in let s1 := YK11.getr regs (Z_to_bv 5 9) in let a0 := YK11.getr regs (Z_to_bv 5 10) in let a1 := YK11.getr regs (Z_to_bv 5 11) in let a2 := YK11.getr regs (Z_to_bv 5 12) in let a3 := YK11.getr regs (Z_to_bv 5 13) in let a4 := YK11.getr regs (Z_to_bv 5 14) in let a5 := YK11.getr regs (Z_to_bv 5 15) in let a6 := YK11.getr regs (Z_to_bv 5 16) in let a7 := YK11.getr regs (Z_to_bv 5 17) in let s2 := YK11.getr regs (Z_to_bv 5 18) in let s3 := YK11.getr regs (Z_to_bv 5 19) in let s4 := YK11.getr regs (Z_to_bv 5 20) in let s5 := YK11.getr regs (Z_to_bv 5 21) in let s6 := YK11.getr regs (Z_to_bv 5 22) in let s7 := YK11.getr regs (Z_to_bv 5 23) in let s8 := YK11.getr regs (Z_to_bv 5 24) in let s9 := YK11.getr regs (Z_to_bv 5 25) in let s10 := YK11.getr regs (Z_to_bv 5 26) in let s11 := YK11.getr regs (Z_to_bv 5 27) in let t3 := YK11.getr regs (Z_to_bv 5 28) in let t4 := YK11.getr regs (Z_to_bv 5 29) in let t5 := YK11.getr regs (Z_to_bv 5 30) in let t6 := YK11.getr regs (Z_to_bv 5 31) in
    0 < f < 2^64 ->
    (* Image B's UBSan premises: 0x8b134 `andi a1,a0,7` / 0x8b138 `bnez a1` trap (unimp at 0x8b1cc) on an f that is
       not 8-aligned, here; and 0x8b19c `beqz a0` traps (unimp at 0x8b1cc) on body = 0 before the load of bb[0], on
       the path cmd = 0 and blen = 1 only, so body <> 0 is stated under that condition, in the premise of that path's
       ranges below; 0 <= body is image A's. *)
    f mod 8 = 0 ->
    0 <= cmd < 2^8 -> 0 <= body < 2^64 ->
    bytes_at rsegs m (f + 30) [b8 cmd] ->
    bytes_at rsegs m (f + 32) (le8 (Z_to_bv 64 body) ++ le8 (Z_to_bv 64 (Z.of_nat (length bb)))) ->
    bytes_at rsegs m body bb ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + DIGINET_FRAME_IS_KEEPALIVE_FRAME <= bv_unsigned sp ->
    asan_cells m ->
    app_mem (bv_unsigned sp - DIGINET_FRAME_IS_KEEPALIVE_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    off_stk sp DIGINET_FRAME_IS_KEEPALIVE_FRAME GOT_CELL_K 8 ->
    off_stk sp DIGINET_FRAME_IS_KEEPALIVE_FRAME CELL_K 8 ->
    off_stk sp DIGINET_FRAME_IS_KEEPALIVE_FRAME (f + 30) 1 ->
    addressable m (f + 30) 1 ->
    (cmd = 0 ->
       off_stk sp DIGINET_FRAME_IS_KEEPALIVE_FRAME (f + 40) 8 /\ addressable m (f + 40) 8) ->
    (cmd = 0 -> Z.of_nat (length bb) = 1 ->
       off_stk sp DIGINET_FRAME_IS_KEEPALIVE_FRAME (f + 32) 8 /\ addressable m (f + 32) 8 /\
       off_stk sp DIGINET_FRAME_IS_KEEPALIVE_FRAME body 1 /\ addressable m body 1 /\ body <> 0) ->
    ExecF.rng RNG (bv_unsigned sp - DIGINET_FRAME_IS_KEEPALIVE_FRAME) DIGINET_FRAME_IS_KEEPALIVE_FRAME ->
    ExecF.rng RNG GOT_CELL_K 8 ->
    ExecF.rng RNG CELL_K 8 ->
    ExecF.rng RNG (f + 30) 1 ->
    ExecF.rng RNG (shadow_addr (f + 30)) 1 ->
    (cmd = 0 -> ExecF.rng RNG (f + 40) 8) ->
    (cmd = 0 -> ExecF.rng RNG (shadow_addr (f + 40)) 1) ->
    (cmd = 0 -> Z.of_nat (length bb) = 1 -> ExecF.rng RNG (f + 32) 8) ->
    (cmd = 0 -> Z.of_nat (length bb) = 1 -> ExecF.rng RNG (shadow_addr (f + 32)) 1) ->
    (cmd = 0 -> Z.of_nat (length bb) = 1 -> ExecF.rng RNG body 1) ->
    (cmd = 0 -> Z.of_nat (length bb) = 1 -> ExecF.rng RNG (shadow_addr body) 1) ->
    SRr W (cfg_at DIGINET_FRAME_IS_KEEPALIVE regs mem md)
      (dleaf_post ly S W regs mem md (Some (if keepalive_of cmd (Z.of_nat (length bb)) bb then 1 else 0))
         [] (fun _ => True)).

Definition transport_diginet_frame_is_keepalive_cg_of_F_stmt : Prop :=
  diginet_frame_is_keepalive_contract_F -> transport_diginet_frame_is_keepalive_cg.

Hypothesis HGLUE : leaf_cg_of_evtF_stmt.

(* The proof applies the kit's generic translation (HGLUE) to the footprint run: diginet_frame_is_keepalive_contract_F
   at RNG := RNG_W W, its premises in order, at the call state's registers, with a0 = Z_to_bv 64 f read back as the
   register a0. The post shape is the footprint contract's (MS (mkR ...) with munch / wmono / stk): the window is its
   munch range, the window's bytes come from its stk (as mrd), the callee-saved registers are the mkR fields read back,
   and a0 is the result. *)
Lemma transport_diginet_frame_is_keepalive_cg_of_F : transport_diginet_frame_is_keepalive_cg_of_F_stmt.
Proof.
  (* no unfold: it would zeta-reduce the statement's lets; intros head-reduces transport_diginet_frame_is_keepalive_cg
     and keeps them as local definitions named as in diginet_frame_is_keepalive_contract_F *)
  intros HF ly S W regs mem md f cmd body lo bb HPRE H10
    RNG m F fc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    HF0 HAL HCMD HBD BCMD BFB BBB STK HLO CELLS APW1 APW2 DGOT DCELL D30 A30 C40 C32
    RFR RGOT RCELL R30 RS30 R40 RS40 R32 RS32 RB RSB.
  (* the run: diginet_frame_is_keepalive_contract_F, its premises in order, at the call state's registers *)
  pose proof (HF RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    f cmd body lo bb HF0 HAL HCMD HBD BCMD BFB BBB STK HLO CELLS APW1 APW2 DGOT DCELL D30 A30 C40 C32
    RFR RGOT RCELL R30 RS30 R40 RS40 R32 RS32 RB RSB) as RUN.
  rewrite <- H10 in RUN.
  refine (HGLUE ly S W regs mem md DIGINET_FRAME_IS_KEEPALIVE DIGINET_FRAME_IS_KEEPALIVE_FRAME _ []
    (Some (if keepalive_of cmd (Z.of_nat (length bb)) bb then 1 else 0)) (fun _ => True) HPRE _ _ RUN _).
  - (* the window bound *)
    unfold DIGINET_FRAME_IS_KEEPALIVE_FRAME, ESTACK. lia.
  - (* WR is empty *)
    intros x Hx. unfold in_wr in Hx. inversion Hx.
  - (* the post *)
    intros ms' (a1' & a2' & a3' & a4' & m' & -> & MU & _ & STK').
    eexists _, m'. split; [reflexivity|].
    split; [exact MU|].
    split.
    + intros x [Hx | Hx]; [| unfold in_wr in Hx; inversion Hx].
      change (spZ regs) with (bv_unsigned sp) in Hx.
      destruct STK' as (_ & _ & STKx).
      destruct (STKx x ltac:(lia)) as (_ & b & Hb).
      exists b. exact Hb.
    + split.
      * intros r Hr. unfold acallee_saved in Hr.
        destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]]; [reflexivity .. |].
        assert (E : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
          by lia.
        destruct E as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; reflexivity.
      * split; [intros r Hr; injection Hr as <-; reflexivity | exact I].
Qed.

End LeafCg.
