(* rp_frame_channels_cg: fuzz_wire image A's rp_frame_channels, its footprint contract (rp_frame_channels_F_c.v) translated to cgif_file's leaf form
   (SRr world walk), as a STATEMENT, with its translation lemma, in the form of libreac/fuzz_decode's
   released lib/A/Prog/reac_frame_clean_len_cg.v (origin/ossv/recipes 98c99a85e4). The premises of the
   target are rp_frame_channels_F_c.v's premises VERBATIM, read at the call state (registers from regs, memory mem, footprint RNG_W W).
   The cgif side (names, verbatim copies, the facts a proof may assume, the generic translation lemma) is the shared
   kit lib/A/Prog/LeafCgKit.v; this file only re-declares the kit's Section Variables and names its definitions.
   wire_rp_frame_channels_cg_of_F is proved in this file's Section over the kit's leaf_cg_of_evtF_stmt (HGLUE, proved
   in LeafCgGlue.v), with K = RP_FRAME_CHANNELS_FRAME. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame ExecF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import AsanKA reac_frame_clean_len_c rp_frame_channels_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF MState Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import rp_frame_channels_F_c LeafCgKit.
Open Scope Z_scope.

Section LeafCg.
Context {fx : YK11.FPState}.
Variable world : Type.                                                (* YA0n.v:19 *)
Variable w_H : world -> word -> bool.                                 (* YA0n.v:20 *)
Variable SRr : world -> config -> (world -> config -> Prop) -> Prop.    (* YA0n.v:36 *)
Variable alayout : Type.                                              (* YG0f.v:45 *)
Variable astate : Type.                                               (* YG00.v:158 *)
Variable AR : alayout -> astate -> world -> (word -> option byte) -> Model -> Prop.  (* YG0n.v:795 *)
Variable aview : (word -> bool) -> (word -> option byte) -> Z -> option Z.          (* YG0n.v:20 *)
Variable same_but_materialized : Model -> Model -> Prop.              (* YK04.v:540 *)
Variable ly_stk_lo ly_stk_hi : alayout -> Z.                          (* YG0f.v *)
Variable ret_ok : word -> Prop.                                       (* YK0s.v:193 *)
Variable as_gp as_tp : Z.                                             (* asyms B *)
Variable aowned : alayout -> astate -> Z -> Prop.                     (* YG0n.v:419 *)
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

Definition wire_rp_frame_channels_cg : Prop :=
  forall ly S (W : world) regs mem md (lo : Z),
    ecall_pre ly S W regs mem md ->
    let RNG := RNG_W W in let m := mem in let F := fp_regs in let fc := fp_csr in
    let ra := YK11.getr regs (Z_to_bv 5 1) in let sp := YK11.getr regs (Z_to_bv 5 2) in let gp := YK11.getr regs (Z_to_bv 5 3) in let tp := YK11.getr regs (Z_to_bv 5 4) in let t0 := YK11.getr regs (Z_to_bv 5 5) in let t1 := YK11.getr regs (Z_to_bv 5 6) in let t2 := YK11.getr regs (Z_to_bv 5 7) in let s0 := YK11.getr regs (Z_to_bv 5 8) in let s1 := YK11.getr regs (Z_to_bv 5 9) in let a0 := YK11.getr regs (Z_to_bv 5 10) in let a1 := YK11.getr regs (Z_to_bv 5 11) in let a2 := YK11.getr regs (Z_to_bv 5 12) in let a3 := YK11.getr regs (Z_to_bv 5 13) in let a4 := YK11.getr regs (Z_to_bv 5 14) in let a5 := YK11.getr regs (Z_to_bv 5 15) in let a6 := YK11.getr regs (Z_to_bv 5 16) in let a7 := YK11.getr regs (Z_to_bv 5 17) in let s2 := YK11.getr regs (Z_to_bv 5 18) in let s3 := YK11.getr regs (Z_to_bv 5 19) in let s4 := YK11.getr regs (Z_to_bv 5 20) in let s5 := YK11.getr regs (Z_to_bv 5 21) in let s6 := YK11.getr regs (Z_to_bv 5 22) in let s7 := YK11.getr regs (Z_to_bv 5 23) in let s8 := YK11.getr regs (Z_to_bv 5 24) in let s9 := YK11.getr regs (Z_to_bv 5 25) in let s10 := YK11.getr regs (Z_to_bv 5 26) in let s11 := YK11.getr regs (Z_to_bv 5 27) in let t3 := YK11.getr regs (Z_to_bv 5 28) in let t4 := YK11.getr regs (Z_to_bv 5 29) in let t5 := YK11.getr regs (Z_to_bv 5 30) in let t6 := YK11.getr regs (Z_to_bv 5 31) in
    bytes_at rsegs m A_M (le8 (Z_to_bv 64 KM)) ->
    bytes_at rsegs m A_T (le8 (Z_to_bv 64 KT)) ->
    bytes_at rsegs m A_K36 (le8 (Z_to_bv 64 K36)) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + RP_FRAME_CHANNELS_FRAME <= bv_unsigned sp ->
    off_stk sp RP_FRAME_CHANNELS_FRAME A_M 8 ->
    off_stk sp RP_FRAME_CHANNELS_FRAME A_T 8 ->
    off_stk sp RP_FRAME_CHANNELS_FRAME A_K36 8 ->
    ExecF.rng RNG (bv_unsigned sp - RP_FRAME_CHANNELS_FRAME) RP_FRAME_CHANNELS_FRAME ->
    ExecF.rng RNG A_M 8 ->
    ExecF.rng RNG A_T 8 ->
    ExecF.rng RNG A_K36 8 ->
    SRr W (cfg_at RP_FRAME_CHANNELS regs mem md)
      (dleaf_post ly S W regs mem md (Some (rp_frame_channels_model (bv_signed a0))) [] (fun _ => True)).

(* The translation the close applies: the footprint contract gives the leaf statement (the kit's generic translation
   leaf_cg_of_evtF_stmt, with K = RP_FRAME_CHANNELS_FRAME, no written range and no X condition). rp_frame_channels writes
   no memory outside its frame, so a caller takes it through WireCg's wire_leaf_at. *)
Definition wire_rp_frame_channels_cg_of_F_stmt : Prop := rp_frame_channels_contract_F -> wire_rp_frame_channels_cg.

(* The proof applies the kit's generic translation (HGLUE) to the footprint walk, as fuzz_uci's rp_hot_clamp_cg.v and
   this unit's rp_fwd_class_cg.v prove theirs: the run is the footprint contract's at RNG := RNG_W W and the call
   state's registers; the window is its munch range, the window's bytes come from its stk (as mrd), the callee-saved
   registers are the mkR fields read back, and a0 is the result. *)
Hypothesis HGLUE : leaf_cg_of_evtF_stmt.

Local Abbreviation GR r k := (YK11.getr r (Z_to_bv 5 k)).

Lemma wire_rp_frame_channels_cg_of_F : wire_rp_frame_channels_cg_of_F_stmt.
Proof.
  intros HF. unfold wire_rp_frame_channels_cg.
  intros ly S W regs mem md lo HPRE. cbv zeta.
  intros HKM HKT HK36 ST HLO OM OT OK RFR RM RT RK.
  pose proof HGLUE as G. unfold leaf_cg_of_evtF_stmt, LeafCgKit.leaf_cg_of_evtF_stmt in G.
  eapply (G ly S W regs mem md RP_FRAME_CHANNELS RP_FRAME_CHANNELS_FRAME).
  - exact HPRE.
  - unfold RP_FRAME_CHANNELS_FRAME, LeafCgKit.ESTACK. lia.
  - intros x Hx. unfold LeafCgKit.in_wr in Hx. inversion Hx.
  - exact (HF (RNG_W W) (GR regs 1) (GR regs 2) (GR regs 3) (GR regs 4) (GR regs 5) (GR regs 6) (GR regs 7) (GR regs 8)
      (GR regs 9) (GR regs 10) (GR regs 11) (GR regs 12) (GR regs 13) (GR regs 14) (GR regs 15) (GR regs 16) (GR regs 17)
      (GR regs 18) (GR regs 19) (GR regs 20) (GR regs 21) (GR regs 22) (GR regs 23) (GR regs 24) (GR regs 25)
      (GR regs 26) (GR regs 27) (GR regs 28) (GR regs 29) (GR regs 30) (GR regs 31) fp_regs fp_csr mem
      lo HKM HKT HK36 ST HLO OM OT OK RFR RM RT RK).
  - intros ms' (a1' & a2' & a3' & m' & Ems & Hmu & Hwm & Hstk').
    pose proof Hstk' as (Hs1 & Hs2 & Hs3).
    eexists. exists m'. split; [exact Ems|].
    split; [exact Hmu|].
    split.
    + intros x [Hx|Hx]; [|unfold LeafCgKit.in_wr in Hx; inversion Hx].
      unfold LeafCgKit.spZ in Hx.
      destruct (Hs3 x ltac:(lia)) as (Hwv & Hmrd). exact Hmrd.
    + split.
      * intros r Hr. unfold LeafCgKit.acallee_saved in Hr.
        assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
                      r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        repeat (destruct Hr' as [->|Hr']; [reflexivity|]). subst r. reflexivity.
      * split; [intros r Er; injection Er as <-; reflexivity|].
        exact I.
Qed.

End LeafCg.
