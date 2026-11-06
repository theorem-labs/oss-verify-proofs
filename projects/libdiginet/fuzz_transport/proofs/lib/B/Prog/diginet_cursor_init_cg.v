(* diginet_cursor_init_cg: image B's diginet_cursor_init, its footprint contract (diginet_cursor_init_F_c.v, which has
   no shadow_rw premise) translated to the leaf form of the shared kit lib/B/Prog/LeafCgKit.v (SRr world walk).
   RELOCATED from libdiginet/fuzz_decode lib/B/Prog/diginet_cursor_init_cg.v (file sha256 225645f1389f; donor not
   released): names, module paths and the caller changed; added the lemma diginet_cursor_init_at_sigma (the entry
   against the listing layer, with the Require of DgnTransportBSyms and DgnTransportBAddr) as in
   check_latest_frame_cg.v.
   The premises of transport_diginet_cursor_init_cg are diginet_cursor_init_contract_F's premises VERBATIM, read at
   the call state (registers from regs, memory mem, footprint RNG_W W); among them image B's UBSan premise
   c mod 8 = 0 (diginet_cursor_init_c.v), which the translation lemma passes on to the footprint contract.
   The function writes a range of its caller, WR = [(c, c + 25)] (the cursor), so the statement takes aowned
   (DgnTransportBCg.v transport_leaf_wr_at) and states the kit's write premise for WR. X is the cursor's cells after
   the call (cursor_cells of lib/Prog/diginet_cursor_init_c.v). RES = None: the code does not keep a0 (a0 = c + 24 at
   the return).
   The caller is diginet_body_check (the call at 0x8c254, return address 0x8c258; DgnTransportBList.v PCall
   TB_diginet_cursor_init): c is its local cursor inside its live side-stack frame (frame + 32 of its class-2 frame,
   or of the 32-aligned area it carves on the real stack, which gives the premise c mod 8 = 0:
   diginet_cursor_init_c.v).
   The proof of transport_diginet_cursor_init_cg_of_F is in this file's Section. It applies the kit's
   leaf_cg_of_evtF_stmt (proof: LeafCgGlue.v), taken as the Section Hypothesis HGLUE.
   Form: fuzz_decode's lib/B/Prog/diginet_cursor_init_cg.v. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA diginet_cursor_init_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF MState Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_cursor_init_F_c LeafCgKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require DgnTransportBSyms DgnTransportBAddr.
Import ListNotations.
Open Scope Z_scope.

(* The entry agrees with the listing layer's address of diginet_cursor_init. *)
Lemma diginet_cursor_init_at_sigma :
  DIGINET_CURSOR_INIT = DgnTransportBAddr.transportb_sigma DgnTransportBSyms.TB_diginet_cursor_init.
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

Definition transport_diginet_cursor_init_cg : Prop :=
  forall ly S (W : world) regs mem md (c body len lo : Z),
    ecall_pre ly S W regs mem md ->
    let RNG := RNG_W W in let m := mem in let F := fp_regs in let fc := fp_csr in
    let ra := YK11.getr regs (Z_to_bv 5 1) in let sp := YK11.getr regs (Z_to_bv 5 2) in let gp := YK11.getr regs (Z_to_bv 5 3) in let tp := YK11.getr regs (Z_to_bv 5 4) in let t0 := YK11.getr regs (Z_to_bv 5 5) in let t1 := YK11.getr regs (Z_to_bv 5 6) in let t2 := YK11.getr regs (Z_to_bv 5 7) in let s0 := YK11.getr regs (Z_to_bv 5 8) in let s1 := YK11.getr regs (Z_to_bv 5 9) in let a0 := YK11.getr regs (Z_to_bv 5 10) in let a1 := YK11.getr regs (Z_to_bv 5 11) in let a2 := YK11.getr regs (Z_to_bv 5 12) in let a3 := YK11.getr regs (Z_to_bv 5 13) in let a4 := YK11.getr regs (Z_to_bv 5 14) in let a5 := YK11.getr regs (Z_to_bv 5 15) in let a6 := YK11.getr regs (Z_to_bv 5 16) in let a7 := YK11.getr regs (Z_to_bv 5 17) in let s2 := YK11.getr regs (Z_to_bv 5 18) in let s3 := YK11.getr regs (Z_to_bv 5 19) in let s4 := YK11.getr regs (Z_to_bv 5 20) in let s5 := YK11.getr regs (Z_to_bv 5 21) in let s6 := YK11.getr regs (Z_to_bv 5 22) in let s7 := YK11.getr regs (Z_to_bv 5 23) in let s8 := YK11.getr regs (Z_to_bv 5 24) in let s9 := YK11.getr regs (Z_to_bv 5 25) in let s10 := YK11.getr regs (Z_to_bv 5 26) in let s11 := YK11.getr regs (Z_to_bv 5 27) in let t3 := YK11.getr regs (Z_to_bv 5 28) in let t4 := YK11.getr regs (Z_to_bv 5 29) in let t5 := YK11.getr regs (Z_to_bv 5 30) in let t6 := YK11.getr regs (Z_to_bv 5 31) in
    a0 = Z_to_bv 64 c -> a1 = Z_to_bv 64 body -> a2 = Z_to_bv 64 len ->
    0 <= c < 2^64 -> c <> 0 -> 0 <= body < 2^64 -> 0 <= len < 2^64 ->
    (* Image B's UBSan premise: 0x8c560 `andi a3,a0,7` / 0x8c564 `bnez a3` trap (unimp at 0x8c5e8) on a c that is
       not 8-aligned. *)
    c mod 8 = 0 ->
    stk rsegs m lo (bv_unsigned sp) -> lo + DIGINET_CURSOR_INIT_FRAME <= bv_unsigned sp ->
    wr_at rsegs m c 25 ->
    off_stk sp DIGINET_CURSOR_INIT_FRAME c 25 ->
    app_mem (bv_unsigned sp - DIGINET_CURSOR_INIT_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    asan_cells m ->
    off_stk sp DIGINET_CURSOR_INIT_FRAME GOT_CELL_K 8 -> off_stk sp DIGINET_CURSOR_INIT_FRAME CELL_K 8 ->
    addressable m c 25 ->
    (* the frame: ra stored at sp - 8 and loaded back *)
    ExecF.rng RNG (bv_unsigned sp - DIGINET_CURSOR_INIT_FRAME) DIGINET_CURSOR_INIT_FRAME ->
    (* the two asan_cells cells: the GOT word and the shadow base *)
    ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    (* the 25 written bytes of the cursor *)
    ExecF.rng RNG c 25 ->
    (* the shadow bytes of the cursor, loaded before each store *)
    ExecF.rng RNG (shadow_addr c) (shadow_addr (c + 25 - 1) - shadow_addr c + 1) ->
    (* the written cursor is not allocator-owned (AR across the write: AR_frame_stmt) and not in the loaded image
       (its post bytes, read through mrd, are then overlay bytes); diginet_body_check discharges both for its local
       cursor: a byte of its live side-stack frame is never aowned, and AR's client-image law keeps it out of the
       image *)
    (forall x, in_wr [(c, c + 25)] x -> ~ aowned ly S x /\ ~ in_img x) ->
    SRr W (cfg_at DIGINET_CURSOR_INIT regs mem md)
      (dleaf_post ly S W regs mem md None [(c, c + 25)]
         (fun m2 => rw_cells rsegs m2 c (PCur.cursor_cells body (if body =? 0 then 0 else len) 0 0))).

Definition transport_diginet_cursor_init_cg_of_F_stmt : Prop :=
  diginet_cursor_init_contract_F -> transport_diginet_cursor_init_cg.

(* The proof applies the kit's generic translation (HGLUE) to the footprint run of diginet_cursor_init_contract_F at
   RNG := RNG_W W and the call state's registers. Its post gives the rest: the window and the cursor are its munch
   ranges; the window's bytes come from its stk (as mrd), the cursor's from its rw_cells; the callee-saved registers
   are the mkR fields read back; a byte of the cursor is visible because RNG_W W holds [c, c + 25). *)
Hypothesis HGLUE : leaf_cg_of_evtF_stmt.

Lemma transport_diginet_cursor_init_cg_of_F : transport_diginet_cursor_init_cg_of_F_stmt.
Proof.
  intros HF. unfold transport_diginet_cursor_init_cg.
  intros ly S W regs mem md c body len lo Hpre. cbv zeta.
  intros E0 E1 E2 Hc Hc0 Hbody Hlen Hal Hstk Hlo Hwr Hoffc Happ1 Happ2 Hcells Hoffg Hoffk Haddr
    Rstk Rg Rk Rc Rcs Hown.
  pose proof HGLUE as G. unfold leaf_cg_of_evtF_stmt, LeafCgKit.leaf_cg_of_evtF_stmt in G.
  eapply (G ly S W regs mem md DIGINET_CURSOR_INIT DIGINET_CURSOR_INIT_FRAME).
  - exact Hpre.
  - unfold DIGINET_CURSOR_INIT_FRAME, ESTACK. lia.
  - intros x Hx. pose proof (Hown x Hx) as Ho.
    unfold in_wr in Hx. apply Exists_cons in Hx.
    destruct Hx as [Hx|Hx]; [cbn [fst snd] in Hx | apply Exists_nil in Hx; destruct Hx].
    destruct Hwr as (Hw0 & Hw1 & _).
    destruct Rc as (Rc1 & Rc2 & Rc3).
    split; [lia|]. split; [|exact Ho].
    pose proof (Rc3 x 1%nat ltac:(lia) ltac:(lia)) as Hv.
    unfold RNG_W, LeafCgKit.RNG_W, range_avoids, woff in Hv. cbv beta in Hv.
    specialize (Hv 0%nat ltac:(lia)).
    assert (Ex : bv_unsigned (Z_to_bv 64 x) = x) by exact (wa_unsigned x ltac:(lia)).
    rewrite Ex in Hv. replace (x + Z.of_nat 0) with x in Hv by lia. exact Hv.
  - exact (HF (RNG_W W)
      (YK11.getr regs (Z_to_bv 5 1)) (YK11.getr regs (Z_to_bv 5 2)) (YK11.getr regs (Z_to_bv 5 3)) (YK11.getr regs (Z_to_bv 5 4))
      (YK11.getr regs (Z_to_bv 5 5)) (YK11.getr regs (Z_to_bv 5 6)) (YK11.getr regs (Z_to_bv 5 7)) (YK11.getr regs (Z_to_bv 5 8))
      (YK11.getr regs (Z_to_bv 5 9)) (YK11.getr regs (Z_to_bv 5 10)) (YK11.getr regs (Z_to_bv 5 11)) (YK11.getr regs (Z_to_bv 5 12))
      (YK11.getr regs (Z_to_bv 5 13)) (YK11.getr regs (Z_to_bv 5 14)) (YK11.getr regs (Z_to_bv 5 15)) (YK11.getr regs (Z_to_bv 5 16))
      (YK11.getr regs (Z_to_bv 5 17)) (YK11.getr regs (Z_to_bv 5 18)) (YK11.getr regs (Z_to_bv 5 19)) (YK11.getr regs (Z_to_bv 5 20))
      (YK11.getr regs (Z_to_bv 5 21)) (YK11.getr regs (Z_to_bv 5 22)) (YK11.getr regs (Z_to_bv 5 23)) (YK11.getr regs (Z_to_bv 5 24))
      (YK11.getr regs (Z_to_bv 5 25)) (YK11.getr regs (Z_to_bv 5 26)) (YK11.getr regs (Z_to_bv 5 27)) (YK11.getr regs (Z_to_bv 5 28))
      (YK11.getr regs (Z_to_bv 5 29)) (YK11.getr regs (Z_to_bv 5 30)) (YK11.getr regs (Z_to_bv 5 31))
      fp_regs fp_csr mem c body len lo E0 E1 E2 Hc Hc0 Hbody Hlen Hal Hstk Hlo Hwr Hoffc Happ1 Happ2 Hcells Hoffg Hoffk
      Haddr Rstk Rg Rk Rc Rcs).
  - intros ms' (a0' & a1' & a2' & a3' & a4' & a5' & m' & Ems & Hmu & Hwm & Hstk' & Hrw).
    pose proof Hstk' as (Hs1 & Hs2 & Hs3).
    assert (Hwin : forall x, spZ regs - DIGINET_CURSOR_INIT_FRAME <= x < spZ regs ->
      exists b, mrd rsegs m' (Z_to_bv 64 x) = Some b).
    { intros x Hx. unfold spZ in Hx.
      destruct (Hs3 x ltac:(lia)) as (Hwv & Hmrd). exact Hmrd. }
    assert (Hcs : forall r, acallee_saved r -> r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/
      r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (intros r Hr; unfold acallee_saved in Hr; lia).
    eexists. exists m'. split; [exact Ems|].
    split; [exact Hmu|].
    split; [|split; [|split; [|exact Hrw]]].
    + intros x [Hx|Hx]; [exact (Hwin x Hx)|].
      unfold in_wr in Hx. apply Exists_cons in Hx.
      destruct Hx as [Hx|Hx]; [cbn [fst snd] in Hx | apply Exists_nil in Hx; destruct Hx].
      destruct Hrw as [[Hwf Hb] _].
      match type of Hwf with cells_wf ?cs0 => set (cs := cs0) in Hwf, Hb end.
      assert (Hsz : cells_size cs = 25%nat) by reflexivity.
      pose proof (cells_bytes_length cs Hwf) as Hln. rewrite Hsz in Hln.
      destruct Hb as (Hb1 & Hb2 & Hb3).
      assert (Hi : (Z.to_nat (x - c) < length (cells_bytes cs))%nat) by (rewrite Hln; lia).
      pose proof (Hb3 _ Hi) as Hm.
      replace (c + Z.of_nat (Z.to_nat (x - c))) with x in Hm by lia.
      unfold wa in Hm.
      destruct (nth_error (cells_bytes cs) (Z.to_nat (x - c))) as [b|] eqn:En.
      * exists b. congruence.
      * apply nth_error_None in En. lia.
    + intros r Hr. destruct (Hcs r Hr) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
        reflexivity.
    + intros r Er. discriminate Er.
Qed.

End LeafCg.
