(* Modified by Theorem Labs, 2026-10: diginet_sum16 of fuzz_frame.asan-ubsan, adapted from this unit's lib/A/Prog/diginet_mac_is_digidesign_cg.v: the names, the premises of diginet_sum16_F_c.v, register premises for the two Z arguments (a0 = p, a1 = length bb), the result Some (lib_sum16 bb); the translation proof is that file's, with its intros, the rewrite of the run's start state (both argument registers) and the post's existentials (t0' a1' .. a7') extended; shape donor of the premises: the UBSan image's contract lib/U/Prog/diginet_sum16_c.v. *)
(* transport_diginet_sum16_cg: image B's diginet_sum16 (entry 0x8afd8, frame 16 bytes; image A inlines the
   function), its footprint contract (diginet_sum16_F_c.v) in the leaf form of the shared kit lib/B/Prog/LeafCgKit.v
   (SRr world walk), as a STATEMENT, and the translation Lemma transport_diginet_sum16_cg_of_F.
   RELOCATED from libdiginet/fuzz_frame lib/B/Prog/diginet_sum16_cg.v (file sha256 af04cba4631e; donor not released):
   names, module paths and the entry changed; added the lemma diginet_sum16_at_sigma (the entry against the listing
   layer, with the Require of DgnTransportBSyms and DgnTransportBAddr) as in check_latest_frame_cg.v.
   The premises are diginet_sum16_contract_F's premises VERBATIM, read at the call state: the registers from regs
   (a0 = p: the premise `YK11.getr regs (Z_to_bv 5 10) = Z_to_bv 64 p`; a1 = the length of bb: the premise
   `YK11.getr regs (Z_to_bv 5 11) = Z_to_bv 64 (Z.of_nat (length bb))`), the memory mem, the footprint RNG_W W. The
   function writes only its own frame (the 8 bytes at sp - 8), so this is a read-only leaf: WR = [], no aowned in the
   statement (DgnTransportBCg.transport_leaf_at). The post is the kit's dleaf_post with the result
   Some (lib_sum16 bb).
   The callers are diginet_frame_parse (call at 0x8b54c, return address 0x8b550: p = buf + 30, n = numbytes - 16) and
   diginet_frame_build (call at 0x8b9cc, return address 0x8b9d0: p = body, n = body_len); DgnTransportBList.v PCall
   TB_diginet_sum16. p <> 0 is asked only when bb is not empty (diginet_sum16_c.v, premise choice): send_control
   passes diginet_frame_build no body (0, 0), and in mode 0 diginet_frame_build calls diginet_sum16 with p = 0, n = 0,
   which returns 0 at 0x8afe4 before it uses p.
   The kit (names, verbatim copies, the facts a proof may assume, the generic translation leaf_cg_of_evtF_stmt) is
   lib/B/Prog/LeafCgKit.v; this file re-declares the kit's Section Variables and names its definitions. The proof of
   transport_diginet_sum16_cg_of_F applies leaf_cg_of_evtF_stmt (Hypothesis HGLUE; its proof is LeafCgGlue.v) to the
   footprint run.
   Form: fuzz_frame's lib/B/Prog/diginet_sum16_cg.v, after lib/A/Prog/diginet_mac_is_digidesign_cg.v (Section,
   statement, proof with a result Some r, a Z argument read from a register, the intros that keep the statement's
   lets, the rewrite of the run's start state). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA diginet_sum16_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF MState Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_sum16_F_c LeafCgKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require DgnTransportBSyms DgnTransportBAddr.
Import ListNotations.
Open Scope Z_scope.

(* The entry agrees with the listing layer's address of diginet_sum16. *)
Lemma diginet_sum16_at_sigma :
  DIGINET_SUM16 = DgnTransportBAddr.transportb_sigma DgnTransportBSyms.TB_diginet_sum16.
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

Definition transport_diginet_sum16_cg : Prop :=
  forall ly S (W : world) regs mem md (p : Z) (bb : list byte) (lo : Z),
    ecall_pre ly S W regs mem md ->
    YK11.getr regs (Z_to_bv 5 10) = Z_to_bv 64 p ->
    YK11.getr regs (Z_to_bv 5 11) = Z_to_bv 64 (Z.of_nat (length bb)) ->
    let RNG := RNG_W W in let m := mem in let F := fp_regs in let fc := fp_csr in
    let ra := YK11.getr regs (Z_to_bv 5 1) in let sp := YK11.getr regs (Z_to_bv 5 2) in let gp := YK11.getr regs (Z_to_bv 5 3) in let tp := YK11.getr regs (Z_to_bv 5 4) in let t0 := YK11.getr regs (Z_to_bv 5 5) in let t1 := YK11.getr regs (Z_to_bv 5 6) in let t2 := YK11.getr regs (Z_to_bv 5 7) in let s0 := YK11.getr regs (Z_to_bv 5 8) in let s1 := YK11.getr regs (Z_to_bv 5 9) in let a0 := YK11.getr regs (Z_to_bv 5 10) in let a1 := YK11.getr regs (Z_to_bv 5 11) in let a2 := YK11.getr regs (Z_to_bv 5 12) in let a3 := YK11.getr regs (Z_to_bv 5 13) in let a4 := YK11.getr regs (Z_to_bv 5 14) in let a5 := YK11.getr regs (Z_to_bv 5 15) in let a6 := YK11.getr regs (Z_to_bv 5 16) in let a7 := YK11.getr regs (Z_to_bv 5 17) in let s2 := YK11.getr regs (Z_to_bv 5 18) in let s3 := YK11.getr regs (Z_to_bv 5 19) in let s4 := YK11.getr regs (Z_to_bv 5 20) in let s5 := YK11.getr regs (Z_to_bv 5 21) in let s6 := YK11.getr regs (Z_to_bv 5 22) in let s7 := YK11.getr regs (Z_to_bv 5 23) in let s8 := YK11.getr regs (Z_to_bv 5 24) in let s9 := YK11.getr regs (Z_to_bv 5 25) in let s10 := YK11.getr regs (Z_to_bv 5 26) in let s11 := YK11.getr regs (Z_to_bv 5 27) in let t3 := YK11.getr regs (Z_to_bv 5 28) in let t4 := YK11.getr regs (Z_to_bv 5 29) in let t5 := YK11.getr regs (Z_to_bv 5 30) in let t6 := YK11.getr regs (Z_to_bv 5 31) in
    (bb <> [] -> p <> 0) ->
    bytes_at rsegs m p bb ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + DIGINET_SUM16_FRAME <= bv_unsigned sp ->
    (bb <> [] -> off_stk sp DIGINET_SUM16_FRAME p (Z.of_nat (length bb))) ->
    app_mem (bv_unsigned sp - DIGINET_SUM16_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    asan_cells m ->
    off_stk sp DIGINET_SUM16_FRAME GOT_CELL_K 8 ->
    off_stk sp DIGINET_SUM16_FRAME CELL_K 8 ->
    (bb <> [] -> addressable m p (Z.of_nat (length bb))) ->
    (* the frame: ra stored at sp - 8 and loaded back *)
    ExecF.rng RNG (bv_unsigned sp - DIGINET_SUM16_FRAME) DIGINET_SUM16_FRAME ->
    (* the two asan_cells cells, read when n <> 0 *)
    (bb <> [] -> ExecF.rng RNG GOT_CELL_K 8) ->
    (bb <> [] -> ExecF.rng RNG CELL_K 8) ->
    (* the n bytes at p and their shadow bytes, read when n <> 0 *)
    (bb <> [] -> ExecF.rng RNG p (Z.of_nat (length bb))) ->
    (bb <> [] ->
       ExecF.rng RNG (shadow_addr p) (shadow_addr (p + Z.of_nat (length bb) - 1) - shadow_addr p + 1)) ->
    SRr W (cfg_at DIGINET_SUM16 regs mem md)
      (dleaf_post ly S W regs mem md (Some (lib_sum16 bb)) [] (fun _ => True)).

Definition transport_diginet_sum16_cg_of_F_stmt : Prop :=
  diginet_sum16_contract_F -> transport_diginet_sum16_cg.

(* The proof applies the kit's generic translation (HGLUE) to the footprint run: diginet_sum16_contract_F at
   RNG := RNG_W W and the call state's registers, its start state's a0 = Z_to_bv 64 p and
   a1 = Z_to_bv 64 (Z.of_nat (length bb)) rewritten to the registers by the premises on a0 and a1. The post is the
   footprint contract's post (MS (mkR ...) with munch / wmono / stk): the window is its munch range, the window's
   bytes come from its stk (as mrd), the callee-saved registers are the mkR fields read back, and a0 is the
   result. *)
Hypothesis HGLUE : leaf_cg_of_evtF_stmt.

Lemma transport_diginet_sum16_cg_of_F : transport_diginet_sum16_cg_of_F_stmt.
Proof.
  (* no unfold: it would zeta-reduce the statement's lets; intros head-reduces the statement and keeps them as local
     definitions named as in diginet_sum16_contract_F *)
  intros HF ly S W regs mem md p bb lo HPRE H10 H11
    RNG m F fc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    HP HB ST HLO DP APW1 APW2 CELLS DG DC AM RFR RGOT RCELL RP RSH.
  (* the run: diginet_sum16_contract_F, its premises in order, at the call state's registers *)
  pose proof (HF RNG ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    p bb lo HP HB ST HLO DP APW1 APW2 CELLS DG DC AM RFR RGOT RCELL RP RSH) as RUN.
  rewrite <- H10, <- H11 in RUN.
  refine (HGLUE ly S W regs mem md DIGINET_SUM16 DIGINET_SUM16_FRAME _ []
    (Some (lib_sum16 bb)) (fun _ => True) HPRE _ _ RUN _).
  - (* the window bound *)
    unfold DIGINET_SUM16_FRAME, ESTACK. lia.
  - (* WR is empty *)
    intros x Hx. unfold in_wr in Hx. inversion Hx.
  - (* the post *)
    intros ms' (t0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m' & -> & MU & _ & STK').
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
        assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
                      r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        repeat (destruct Hr' as [->|Hr']; [reflexivity|]). subst r. reflexivity.
      * split; [intros r Hr; injection Hr as <-; reflexivity|].
        exact I.
Qed.

End LeafCg.
