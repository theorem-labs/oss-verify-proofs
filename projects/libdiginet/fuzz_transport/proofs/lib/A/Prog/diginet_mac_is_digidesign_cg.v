(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_decode/lib/A/Prog/reac_frame_is_reac_cg.v stated for diginet_mac_is_digidesign on fuzz_frame.asan: the names, the premises of diginet_mac_is_digidesign_F_c.v, the register premise for the Z argument mac (as check_braid_cg.v), the module paths. *)
(* transport_diginet_mac_is_digidesign_cg: image A's diginet_mac_is_digidesign (entry 0x8b590, frame 16 bytes), its
   footprint contract (diginet_mac_is_digidesign_F_c.v) in the leaf form of the shared kit lib/A/Prog/LeafCgKit.v
   (SRr world walk), as a STATEMENT, and the translation Lemma transport_diginet_mac_is_digidesign_cg_of_F.
   RELOCATED from libdiginet/fuzz_frame lib/A/Prog/diginet_mac_is_digidesign_cg.v (file sha256 dfb0f6bc6409; donor
   not released): names, module paths and the entry changed; added the lemma diginet_mac_is_digidesign_at_sigma (the
   entry against the listing layer, with the Require of DgnTransportSyms and DgnTransportAddr) as in
   check_state_wake_cg.v. The premises are diginet_mac_is_digidesign_contract_F's premises VERBATIM, read at the call
   state: the registers from regs (a0 = mac: the premise `YK11.getr regs (Z_to_bv 5 10) = Z_to_bv 64 mac`), the
   memory mem, the footprint RNG_W W. The function writes only its own frame (the 8 bytes at sp - 8), so this is a
   read-only leaf: WR = [], no aowned in the statement (DgnTransportCg.transport_leaf_at). The post is the kit's
   dleaf_post with the result of the plain contract, Some (if oui_of l then 1 else 0).
   The caller is diginet_session_rx (the call at 0x878d0, return address 0x878d4; DgnTransportList.v PCall
   TS_diginet_mac_is_digidesign).
   The kit (names, verbatim copies, the facts a proof may assume, the generic translation leaf_cg_of_evtF_stmt) is
   lib/A/Prog/LeafCgKit.v; this file re-declares the kit's Section Variables and names its definitions. The proof of
   transport_diginet_mac_is_digidesign_cg_of_F applies leaf_cg_of_evtF_stmt (Hypothesis HGLUE; its proof is
   LeafCgGlue.v) to the footprint run.
   Form: fuzz_frame's diginet_mac_is_digidesign_cg.v. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA diginet_mac_is_digidesign_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF MState Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_mac_is_digidesign_F_c LeafCgKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require DgnTransportSyms DgnTransportAddr.
Import ListNotations.
Open Scope Z_scope.

(* The entry agrees with the listing layer's address of diginet_mac_is_digidesign. *)
Lemma diginet_mac_is_digidesign_at_sigma :
  DIGINET_MAC_IS_DIGIDESIGN = DgnTransportAddr.transport_sigma DgnTransportSyms.TS_diginet_mac_is_digidesign.
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

Definition transport_diginet_mac_is_digidesign_cg : Prop :=
  forall ly S (W : world) regs mem md (mac : Z) (l : list byte) (lo : Z),
    ecall_pre ly S W regs mem md ->
    YK11.getr regs (Z_to_bv 5 10) = Z_to_bv 64 mac ->
    let RNG := RNG_W W in let m := mem in let F := fp_regs in let fc := fp_csr in
    let ra := YK11.getr regs (Z_to_bv 5 1) in let sp := YK11.getr regs (Z_to_bv 5 2) in let gp := YK11.getr regs (Z_to_bv 5 3) in let tp := YK11.getr regs (Z_to_bv 5 4) in let t0 := YK11.getr regs (Z_to_bv 5 5) in let t1 := YK11.getr regs (Z_to_bv 5 6) in let t2 := YK11.getr regs (Z_to_bv 5 7) in let s0 := YK11.getr regs (Z_to_bv 5 8) in let s1 := YK11.getr regs (Z_to_bv 5 9) in let a0 := YK11.getr regs (Z_to_bv 5 10) in let a1 := YK11.getr regs (Z_to_bv 5 11) in let a2 := YK11.getr regs (Z_to_bv 5 12) in let a3 := YK11.getr regs (Z_to_bv 5 13) in let a4 := YK11.getr regs (Z_to_bv 5 14) in let a5 := YK11.getr regs (Z_to_bv 5 15) in let a6 := YK11.getr regs (Z_to_bv 5 16) in let a7 := YK11.getr regs (Z_to_bv 5 17) in let s2 := YK11.getr regs (Z_to_bv 5 18) in let s3 := YK11.getr regs (Z_to_bv 5 19) in let s4 := YK11.getr regs (Z_to_bv 5 20) in let s5 := YK11.getr regs (Z_to_bv 5 21) in let s6 := YK11.getr regs (Z_to_bv 5 22) in let s7 := YK11.getr regs (Z_to_bv 5 23) in let s8 := YK11.getr regs (Z_to_bv 5 24) in let s9 := YK11.getr regs (Z_to_bv 5 25) in let s10 := YK11.getr regs (Z_to_bv 5 26) in let s11 := YK11.getr regs (Z_to_bv 5 27) in let t3 := YK11.getr regs (Z_to_bv 5 28) in let t4 := YK11.getr regs (Z_to_bv 5 29) in let t5 := YK11.getr regs (Z_to_bv 5 30) in let t6 := YK11.getr regs (Z_to_bv 5 31) in
    mac <> 0 ->
    (3 <= length l)%nat ->
    bytes_at rsegs m mac l ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + DIGINET_MAC_IS_DIGIDESIGN_FRAME <= bv_unsigned sp ->
    off_stk sp DIGINET_MAC_IS_DIGIDESIGN_FRAME mac 3 ->
    app_mem (bv_unsigned sp - DIGINET_MAC_IS_DIGIDESIGN_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    asan_cells m ->
    off_stk sp DIGINET_MAC_IS_DIGIDESIGN_FRAME GOT_CELL_K 8 ->
    off_stk sp DIGINET_MAC_IS_DIGIDESIGN_FRAME CELL_K 8 ->
    addressable m mac 3 ->
    ExecF.rng RNG (bv_unsigned sp - DIGINET_MAC_IS_DIGIDESIGN_FRAME) DIGINET_MAC_IS_DIGIDESIGN_FRAME ->
    ExecF.rng RNG GOT_CELL_K 8 ->
    ExecF.rng RNG CELL_K 8 ->
    ExecF.rng RNG mac 3 ->
    ExecF.rng RNG (shadow_addr mac) (shadow_addr (mac + 3 - 1) - shadow_addr mac + 1) ->
    SRr W (cfg_at DIGINET_MAC_IS_DIGIDESIGN regs mem md)
      (dleaf_post ly S W regs mem md (Some (if oui_of l then 1 else 0)) [] (fun _ => True)).

Definition transport_diginet_mac_is_digidesign_cg_of_F_stmt : Prop :=
  diginet_mac_is_digidesign_contract_F -> transport_diginet_mac_is_digidesign_cg.

(* The proof applies the kit's generic translation (HGLUE) to the footprint run: diginet_mac_is_digidesign_contract_F
   at RNG := RNG_W W and the call state's registers, its start state's a0 = Z_to_bv 64 mac rewritten to the register
   by the premise on a0. The post is the footprint contract's post (MS (mkR ...) with munch / wmono / stk): the window
   is its munch range, the window's bytes come from its stk (as mrd), the callee-saved registers are the mkR fields
   read back, and a0 is the result. *)
Hypothesis HGLUE : leaf_cg_of_evtF_stmt.

Lemma transport_diginet_mac_is_digidesign_cg_of_F : transport_diginet_mac_is_digidesign_cg_of_F_stmt.
Proof.
  (* no unfold: it would zeta-reduce the statement's lets; intros head-reduces the statement and keeps them as local
     definitions named as in diginet_mac_is_digidesign_contract_F *)
  intros HF ly S W regs mem md mac l lo HPRE H10
    RNG m F fc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    HMAC HLEN HB ST HLO DM APW1 APW2 CELLS DG DC AM RFR RGOT RCELL RMAC RSH.
  (* the run: diginet_mac_is_digidesign_contract_F, its premises in order, at the call state's registers *)
  pose proof (HF RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    mac l lo HMAC HLEN HB ST HLO DM APW1 APW2 CELLS DG DC AM RFR RGOT RCELL RMAC RSH) as RUN.
  rewrite <- H10 in RUN.
  refine (HGLUE ly S W regs mem md DIGINET_MAC_IS_DIGIDESIGN DIGINET_MAC_IS_DIGIDESIGN_FRAME _ []
    (Some (if oui_of l then 1 else 0)) (fun _ => True) HPRE _ _ RUN _).
  - (* the window bound *)
    unfold DIGINET_MAC_IS_DIGIDESIGN_FRAME, ESTACK. lia.
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
        assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
                      r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        repeat (destruct Hr' as [->|Hr']; [reflexivity|]). subst r. reflexivity.
      * split; [intros r Hr; injection Hr as <-; reflexivity|].
        exact I.
Qed.

End LeafCg.
