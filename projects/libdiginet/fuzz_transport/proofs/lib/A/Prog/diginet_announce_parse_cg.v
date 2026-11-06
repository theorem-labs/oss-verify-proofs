(* Modified by Theorem Labs, 2026-10: diginet_announce_parse's leaf statement and its translation lemma, in the form of
   libreac/fuzz_decode's lib/A/Prog/reac_decode_cg.v. *)
(* transport_diginet_announce_parse_cg: image A's diginet_announce_parse (fuzz_transport.asan e89be137db17, entry
   0x8c238 = transport_sigma TS_diginet_announce_parse, own frame 16 bytes), its footprint contract
   (diginet_announce_parse_F_c.v) translated to cgif_file's leaf form (SRr world walk), as a STATEMENT.
   RELOCATED from libdiginet/fuzz_frame lib/A/Prog/diginet_announce_parse_cg.v (file sha256 443c0085eb58; donor not
   released; the code is fuzz_frame's up to pc-relative words, diginet_announce_parse_c.v): the names frame_* become
   transport_*, the module paths change, and the lemma diginet_announce_parse_at_sigma (the entry against the listing
   layer, with the Require of DgnTransportSyms and DgnTransportAddr) is added as in check_state_wake_cg.v. The
   statement and the proof are fuzz_frame's otherwise.
   The premises are diginet_announce_parse_F_c.v's premises VERBATIM, read at the call state (registers from regs,
   memory mem, footprint RNG_W W). The cgif side (names, verbatim copies, the facts a proof may assume, the generic
   translation lemma) is the shared kit lib/A/Prog/LeafCgKit.v; this file re-declares the kit's Section Variables and
   names its definitions.
   The function writes the caller's 40 bytes at ap, and only when the code is 0 (ann_ok): so the written range WR is
   [(ap, ap + 40)] on code 0 and [] else, and X gives the bytes there (PAnn.ann_cells, the plain contract's cells).
   For a written byte the statement takes that it is not allocator-owned (aowned) and not in the loaded image
   (in_img): the closing file reads it at this unit's model through DgnTransportCg.v transport_leaf_wr_at. The caller
   on_announce (the call at 0x87c88, return address 0x87c8c) gives its local `a`, the 40 bytes at offset 256 of its
   own frame: a frame on the side stack for frames (__asan_stack_malloc_4 at 0x87ae8, class 4), or, when that call is
   skipped or returns 0, the frame it carves on the real stack below its sp (0x87b00 - 0x87b18). Neither is
   allocator-owned or in the loaded image, and neither is a harness global.
   transport_diginet_announce_parse_cg_of_F proves the statement from diginet_announce_parse_contract_F and the kit's
   leaf_cg_of_evtF_stmt (Section Hypothesis HGLUE; its proof is LeafCgGlue.v).
   Template: reac_decode_cg.v:20-95 (statement), :96-163 (proof). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_announce_parse_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF MState Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_announce_parse_F_c LeafCgKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require DgnTransportSyms DgnTransportAddr.
Import ListNotations.
Open Scope Z_scope.

(* The entry agrees with the listing layer's address of diginet_announce_parse. *)
Lemma diginet_announce_parse_at_sigma :
  DIGINET_ANNOUNCE_PARSE = DgnTransportAddr.transport_sigma DgnTransportSyms.TS_diginet_announce_parse.
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

Definition transport_diginet_announce_parse_cg : Prop :=
  forall ly S (W : world) regs mem md (bb aj : list byte) (f ap cmd body lo : Z),
    ecall_pre ly S W regs mem md ->
    let RNG := RNG_W W in let m := mem in let F := fp_regs in let fc := fp_csr in
    let ra := YK11.getr regs (Z_to_bv 5 1) in let sp := YK11.getr regs (Z_to_bv 5 2) in let gp := YK11.getr regs (Z_to_bv 5 3) in let tp := YK11.getr regs (Z_to_bv 5 4) in let t0 := YK11.getr regs (Z_to_bv 5 5) in let t1 := YK11.getr regs (Z_to_bv 5 6) in let t2 := YK11.getr regs (Z_to_bv 5 7) in let s0 := YK11.getr regs (Z_to_bv 5 8) in let s1 := YK11.getr regs (Z_to_bv 5 9) in let a0 := YK11.getr regs (Z_to_bv 5 10) in let a1 := YK11.getr regs (Z_to_bv 5 11) in let a2 := YK11.getr regs (Z_to_bv 5 12) in let a3 := YK11.getr regs (Z_to_bv 5 13) in let a4 := YK11.getr regs (Z_to_bv 5 14) in let a5 := YK11.getr regs (Z_to_bv 5 15) in let a6 := YK11.getr regs (Z_to_bv 5 16) in let a7 := YK11.getr regs (Z_to_bv 5 17) in let s2 := YK11.getr regs (Z_to_bv 5 18) in let s3 := YK11.getr regs (Z_to_bv 5 19) in let s4 := YK11.getr regs (Z_to_bv 5 20) in let s5 := YK11.getr regs (Z_to_bv 5 21) in let s6 := YK11.getr regs (Z_to_bv 5 22) in let s7 := YK11.getr regs (Z_to_bv 5 23) in let s8 := YK11.getr regs (Z_to_bv 5 24) in let s9 := YK11.getr regs (Z_to_bv 5 25) in let s10 := YK11.getr regs (Z_to_bv 5 26) in let s11 := YK11.getr regs (Z_to_bv 5 27) in let t3 := YK11.getr regs (Z_to_bv 5 28) in let t4 := YK11.getr regs (Z_to_bv 5 29) in let t5 := YK11.getr regs (Z_to_bv 5 30) in let t6 := YK11.getr regs (Z_to_bv 5 31) in
    a0 = Z_to_bv 64 f -> a1 = Z_to_bv 64 ap ->
    0 < f < 2^64 -> 0 < ap < 2^64 ->
    0 <= cmd < 2^8 -> 0 < body < 2^64 ->
    bytes_at rsegs m (f + 30) [b8 cmd] ->
    bytes_at rsegs m (f + 32) (le8 (Z_to_bv 64 body) ++ le8 (Z_to_bv 64 (Z.of_nat (length bb)))) ->
    bytes_at rsegs m body bb ->
    stk rsegs m lo (bv_unsigned sp) -> lo + DIGINET_ANNOUNCE_PARSE_FRAME <= bv_unsigned sp ->
    off_stk sp DIGINET_ANNOUNCE_PARSE_FRAME (f + 30) 18 ->
    (ann_ok cmd bb = true -> off_stk sp DIGINET_ANNOUNCE_PARSE_FRAME (body + 15) 18) ->
    (ann_ok cmd bb = true ->
       rw_cells rsegs m ap [CB 40 aj] /\
       (ap + 40 <= f + 30 \/ f + 48 <= ap) /\
       (ap + 40 <= body + 15 \/ body + 33 <= ap) /\
       off_stk sp DIGINET_ANNOUNCE_PARSE_FRAME ap 40) ->
    app_mem (bv_unsigned sp - DIGINET_ANNOUNCE_PARSE_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    asan_cells m ->
    off_stk sp DIGINET_ANNOUNCE_PARSE_FRAME GOT_CELL_K (MIDEND + 8 - GOT_CELL_K) ->
    addressable m (f + 30) 1 ->
    (ann_cmd cmd = true -> addressable m (f + 40) 8) ->
    (ann_ok cmd bb = true -> addressable m (f + 32) 8) ->
    (ann_ok cmd bb = true -> addressable m (body + 15) 18) ->
    (ann_ok cmd bb = true -> addressable m ap 40) ->
    (* the frame *)
    ExecF.rng RNG (bv_unsigned sp - DIGINET_ANNOUNCE_PARSE_FRAME) DIGINET_ANNOUNCE_PARSE_FRAME ->
    (* the two asan_cells cells *)
    ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    (* the byte cmd and its shadow byte *)
    ExecF.rng RNG (f + 30) 1 ->
    ExecF.rng RNG (shadow_addr (f + 30)) (shadow_addr (f + 30 + 1 - 1) - shadow_addr (f + 30) + 1) ->
    (* the length field and its shadow bytes, when cmd is e0 or e1 *)
    (ann_cmd cmd = true -> ExecF.rng RNG (f + 40) 8) ->
    (ann_cmd cmd = true ->
       ExecF.rng RNG (shadow_addr (f + 40)) (shadow_addr (f + 40 + 8 - 1) - shadow_addr (f + 40) + 1)) ->
    (* on code 0: the body field, the two strings of the body, the 40 bytes at ap, and their shadow bytes *)
    (ann_ok cmd bb = true -> ExecF.rng RNG (f + 32) 8) ->
    (ann_ok cmd bb = true ->
       ExecF.rng RNG (shadow_addr (f + 32)) (shadow_addr (f + 32 + 8 - 1) - shadow_addr (f + 32) + 1)) ->
    (ann_ok cmd bb = true -> ExecF.rng RNG (body + 15) 18) ->
    (ann_ok cmd bb = true ->
       ExecF.rng RNG (shadow_addr (body + 15)) (shadow_addr (body + 15 + 18 - 1) - shadow_addr (body + 15) + 1)) ->
    (ann_ok cmd bb = true -> ExecF.rng RNG ap 40) ->
    (ann_ok cmd bb = true ->
       ExecF.rng RNG (shadow_addr ap) (shadow_addr (ap + 40 - 1) - shadow_addr ap + 1)) ->
    (* the written caller bytes are not allocator-owned (AR across the write: AR_frame_stmt) and not in the loaded
       image (their post bytes, read through mrd, are then overlay bytes) *)
    (forall x, in_wr (if ann_ok cmd bb then [(ap, ap + 40)] else []) x -> ~ aowned ly S x /\ ~ in_img x) ->
    SRr W (cfg_at DIGINET_ANNOUNCE_PARSE regs mem md)
      (dleaf_post ly S W regs mem md (Some (ann_code cmd (Z.of_nat (length bb))))
         (if ann_ok cmd bb then [(ap, ap + 40)] else [])
         (fun m2 => ann_ok cmd bb = true -> rw_cells rsegs m2 ap (PAnn.ann_cells body bb aj))).

Definition transport_diginet_announce_parse_cg_of_F_stmt : Prop :=
  diginet_announce_parse_contract_F -> transport_diginet_announce_parse_cg.

Hypothesis HGLUE : leaf_cg_of_evtF_stmt.

(* The run is diginet_announce_parse_contract_F at RNG := RNG_W W and the call state's registers; the kit's
   leaf_cg_of_evtF_stmt turns it into the leaf form. WR's bytes are in range and visible by the footprint premise of
   [ap, ap + 40); the window's bytes come from the post's stk, WR's from its rw_cells (40 bytes); the callee-saved
   registers are the mkR fields read back. *)
Lemma transport_diginet_announce_parse_cg_of_F : transport_diginet_announce_parse_cg_of_F_stmt.
Proof.
  intros HF. unfold transport_diginet_announce_parse_cg.
  (* unfold also zeta-reduces the statement's lets, as in reac_decode_cg.v:105-107 *)
  intros ly S W regs mem md bb aj f ap cmd body lo Hpre E0 E1 Hf Hap Hcmd Hbody Hb30 Hb32 Hbb Hstk Hlo Hofff Hoffb
    Hwr Happ1 Happ2 Hcells Hoffg Had30 Had40 Had32 Hadb Hadap Rstk Rg Rc R30 R30s R40 R40s R32 R32s Rb Rbs Rap Raps
    Hown.
  pose proof HGLUE as G. unfold leaf_cg_of_evtF_stmt, LeafCgKit.leaf_cg_of_evtF_stmt in G.
  eapply (G ly S W regs mem md DIGINET_ANNOUNCE_PARSE DIGINET_ANNOUNCE_PARSE_FRAME).
  - exact Hpre.
  - unfold DIGINET_ANNOUNCE_PARSE_FRAME, ESTACK. lia.
  - intros x Hx. split; [|split; [|exact (Hown x Hx)]];
      revert Hx; destruct (ann_ok cmd bb); intros Hx; unfold in_wr in Hx;
      [ apply Exists_cons in Hx; destruct Hx as [Hx|Hx]; [cbn [fst snd] in Hx | apply Exists_nil in Hx; destruct Hx]
      | apply Exists_nil in Hx; destruct Hx
      | apply Exists_cons in Hx; destruct Hx as [Hx|Hx]; [cbn [fst snd] in Hx | apply Exists_nil in Hx; destruct Hx]
      | apply Exists_nil in Hx; destruct Hx ].
    + destruct (Rap eq_refl) as (Ra1 & Ra2 & Ra3). lia.
    + destruct (Rap eq_refl) as (Ra1 & Ra2 & Ra3).
      pose proof (Ra3 x 1%nat ltac:(lia) ltac:(lia)) as Hv.
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
      fp_regs fp_csr mem bb aj f ap cmd body lo
      E0 E1 Hf Hap Hcmd Hbody Hb30 Hb32 Hbb Hstk Hlo Hofff Hoffb Hwr Happ1 Happ2 Hcells Hoffg
      Had30 Had40 Had32 Hadb Hadap Rstk Rg Rc R30 R30s R40 R40s R32 R32s Rb Rbs Rap Raps).
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m' & Ems & Hwm & Hstk' & Hif).
    pose proof Hstk' as (Hs1 & Hs2 & Hs3).
    assert (Hwin : forall x, spZ regs - DIGINET_ANNOUNCE_PARSE_FRAME <= x < spZ regs ->
      exists b, mrd rsegs m' (Z_to_bv 64 x) = Some b).
    { intros x Hx. unfold spZ in Hx.
      destruct (Hs3 x ltac:(lia)) as (Hwv & Hmrd). exact Hmrd. }
    assert (Hcs : forall r, acallee_saved r -> r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/
      r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (intros r Hr; unfold acallee_saved in Hr; lia).
    eexists. exists m'. split; [exact Ems|].
    revert Hif. destruct (ann_ok cmd bb); intros Hif;
      (split; [|split; [|split;
        [ intros r Hr; destruct (Hcs r Hr) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
          reflexivity
        | split; [intros r Er; injection Er as Er; subst r; reflexivity|] ]]]).
    + exact (proj1 Hif).
    + intros x [Hx|Hx]; [exact (Hwin x Hx)|].
      unfold in_wr in Hx. apply Exists_cons in Hx.
      destruct Hx as [Hx|Hx]; [cbn [fst snd] in Hx | apply Exists_nil in Hx; destruct Hx].
      destruct Hif as (Hmu & Hrw). destruct Hrw as ((Hwf & Hb1 & Hb2 & Hb3) & Hwa).
      assert (Hlen : length (cells_bytes (PAnn.ann_cells body bb aj)) = 40%nat)
        by (rewrite (cells_bytes_length _ Hwf); reflexivity).
      assert (Hi : (Z.to_nat (x - ap) < length (cells_bytes (PAnn.ann_cells body bb aj)))%nat)
        by (rewrite Hlen; lia).
      pose proof (Hb3 _ Hi) as Hm.
      replace (ap + Z.of_nat (Z.to_nat (x - ap))) with x in Hm by lia.
      destruct (nth_error (cells_bytes (PAnn.ann_cells body bb aj)) (Z.to_nat (x - ap))) as [b|] eqn:En.
      * exists b. exact Hm.
      * apply nth_error_None in En. lia.
    + intros Ht. exact (proj2 Hif).
    + exact Hif.
    + intros x [Hx|Hx]; [exact (Hwin x Hx)|].
      unfold in_wr in Hx. apply Exists_nil in Hx. destruct Hx.
    + intros Ht. discriminate Ht.
Qed.

End LeafCg.
