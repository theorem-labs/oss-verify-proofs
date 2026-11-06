(* rp_slot_width_cg: image A's rp_slot_width, its footprint contract (rp_slot_width_F_c.v) translated to the leaf
   form of the shared kit lib/A/Prog/LeafCgKit.v, in the form of reac-repacer/fuzz_uci's lib/A/Prog/rp_hot_clamp_cg.v.
   The translation lemma wire_rp_slot_width_cg_of_F is proved in this file's Section over the kit's
   leaf_cg_of_evtF_stmt (HGLUE, proved in LeafCgGlue.v), as lib/A/Prog/rp_fwd_class_cg.v proves its own.

   The premises of the target are rp_slot_width_F_c.v's premises VERBATIM, read at the call state (registers from
   regs, memory mem, footprint RNG_W W). rp_slot_width writes NO memory outside its own frame (its only stores are
   `sd ra, 8(sp)` and `sd s0, 0(sp)` at 0x81558 / 0x8155c), so the write list is empty and a caller takes it through
   the kit's non-writing wrapper wire_leaf_at, not wire_leaf_wr_at.
   Its one program callee is rp_frame_channels (0x8136c); at the footprint level the chain is
   rp_frame_channels_contract_F -> rp_slot_width_contract_F (rp_slot_width_F_c.v rp_slot_width_F_holds_stmt), which is
   what the walk of this row must prove. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import AsanKA reac_frame_clean_len_c rp_frame_channels_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import rp_slot_width_F_c LeafCgKit.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_slot_width_c.
Import ListNotations.
Open Scope Z_scope.
Module PSW := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_slot_width_c.

Section LeafCg.
Context {fx : YK11.FPState}.
Variable world : Type.                                                (* YA0n.v Record world *)
Variable w_H : world -> word -> bool.                                 (* YA0n.v field w_H *)
Variable SRr : world -> config -> (world -> config -> Prop) -> Prop.    (* YA0n.v SRr *)
Variable alayout : Type.                                              (* YG0f.v *)
Variable astate : Type.                                               (* YG00.v *)
Variable AR : alayout -> astate -> world -> (word -> option byte) -> Model -> Prop.  (* YG0n.v AR *)
Variable aview : (word -> bool) -> (word -> option byte) -> Z -> option Z.          (* YG0n.v aview *)
Variable same_but_materialized : Model -> Model -> Prop.              (* YK04.v *)
Variable ly_stk_lo ly_stk_hi : alayout -> Z.                          (* YG0f.v *)
Variable ret_ok : word -> Prop.                                       (* YK0s.v *)
Variable as_gp as_tp : Z.                                             (* asyms B *)
Variable aowned : alayout -> astate -> Z -> Prop.                     (* YG0n.v aowned *)
(* The kit's definitions and facts at these names (LeafCgKit.v; argument order = the kit's Section order). *)
Let ecall_pre := @LeafCgKit.ecall_pre world w_H alayout astate AR ly_stk_lo ly_stk_hi ret_ok as_gp as_tp.
Let RNG_W := @LeafCgKit.RNG_W world w_H.
Let dleaf_post := @LeafCgKit.dleaf_post fx world w_H alayout astate AR aview same_but_materialized.
Let leaf_cg_of_evtF_stmt := @LeafCgKit.leaf_cg_of_evtF_stmt fx world w_H SRr alayout astate AR aview
  same_but_materialized ly_stk_lo ly_stk_hi ret_ok as_gp as_tp aowned.

Definition wire_rp_slot_width_cg : Prop :=
  forall ly S (W : world) regs mem md (bs : list byte) (lo : Z),
    ecall_pre ly S W regs mem md ->
    let RNG := RNG_W W in let m := mem in
    let sp := YK11.getr regs (Z_to_bv 5 2) in
    let a0 := YK11.getr regs (Z_to_bv 5 10) in
    let a1 := YK11.getr regs (Z_to_bv 5 11) in
    let a2 := YK11.getr regs (Z_to_bv 5 12) in
    bytes_at rsegs m A_M (le8 (Z_to_bv 64 KM)) ->
    bytes_at rsegs m A_T (le8 (Z_to_bv 64 KT)) ->
    bytes_at rsegs m A_K36 (le8 (Z_to_bv 64 K36)) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + RP_SLOT_WIDTH_STK <= bv_unsigned sp ->
    app_mem (bv_unsigned sp - RP_SLOT_WIDTH_STK) -> app_mem (bv_unsigned sp - 1) ->
    asan_cells m ->
    off_stk sp RP_SLOT_WIDTH_STK GOT_CELL_K 8 ->
    off_stk sp RP_SLOT_WIDTH_STK CELL_K 8 ->
    (50 <= bv_unsigned a1 ->
       (18 <= length bs)%nat /\ bytes_at rsegs m (bv_unsigned a0) bs /\
       off_stk sp RP_SLOT_WIDTH_STK (bv_unsigned a0) (Z.of_nat (length bs)) /\
       addressable m (bv_unsigned a0 + RP_SW_OFF) RP_SW_LEN) ->
    ExecF.rng RNG (bv_unsigned sp - RP_SLOT_WIDTH_STK) RP_SLOT_WIDTH_STK ->
    ExecF.rng RNG GOT_CELL_K 8 ->
    ExecF.rng RNG CELL_K 8 ->
    Forall (fun r => off_stk sp RP_SLOT_WIDTH_STK (fst r) (snd r)) WIRE_RFC_CONSTS ->
    Forall (fun r => ExecF.rng RNG (fst r) (snd r)) WIRE_RFC_CONSTS ->
    (50 <= bv_unsigned a1 -> ExecF.rng RNG (bv_unsigned a0 + RP_SW_OFF) RP_SW_LEN) ->
    (50 <= bv_unsigned a1 ->
       ExecF.rng RNG (shadow_addr (bv_unsigned a0 + RP_SW_OFF))
         (shadow_addr (bv_unsigned a0 + RP_SW_OFF + RP_SW_LEN - 1) - shadow_addr (bv_unsigned a0 + RP_SW_OFF) + 1)) ->
    SRr W (cfg_at RP_SLOT_WIDTH regs mem md)
      (dleaf_post ly S W regs mem md
         (Some (PSW.rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2))) [] (fun _ => True)).

(* The kit's generic translation (LeafCgKit.v leaf_cg_of_evtF_stmt, proved in LeafCgGlue.v) carries the footprint
   contract to the leaf form: the run is the footprint contract's at RNG := RNG_W W and the call state's registers,
   the window is its munch range, and the write list is empty. *)
Definition wire_rp_slot_width_cg_of_F_stmt : Prop := rp_slot_width_contract_F -> wire_rp_slot_width_cg.

(* The proof applies the kit's generic translation (HGLUE) to the footprint walk. The run is the footprint
   contract's at RNG := RNG_W W and the call state's registers; the window is its munch range, the window's bytes
   come from its stk (as mrd), the callee-saved registers are the mkR fields read back, and a0 is the result. *)
Hypothesis HGLUE : leaf_cg_of_evtF_stmt.

Local Abbreviation GR r k := (YK11.getr r (Z_to_bv 5 k)).

Lemma wire_rp_slot_width_cg_of_F : wire_rp_slot_width_cg_of_F_stmt.
Proof.
  intros HF. unfold wire_rp_slot_width_cg.
  intros ly S W regs mem md bs lo HPRE. cbv zeta.
  intros HKM HKT HK36 ST HLO HAPP1 HAPP2 HAC HOG HOC HB RFR RGOT RCELL HCO RCO RSW RSH.
  pose proof HGLUE as G. unfold leaf_cg_of_evtF_stmt, LeafCgKit.leaf_cg_of_evtF_stmt in G.
  eapply (G ly S W regs mem md RP_SLOT_WIDTH RP_SLOT_WIDTH_STK).
  - exact HPRE.
  - unfold RP_SLOT_WIDTH_STK, RP_SLOT_WIDTH_FRAME, RP_FRAME_CHANNELS_FRAME, LeafCgKit.ESTACK. lia.
  - intros x Hx. unfold LeafCgKit.in_wr in Hx. inversion Hx.
  - exact (HF (RNG_W W) (GR regs 1) (GR regs 2) (GR regs 3) (GR regs 4) (GR regs 5) (GR regs 6) (GR regs 7) (GR regs 8)
      (GR regs 9) (GR regs 10) (GR regs 11) (GR regs 12) (GR regs 13) (GR regs 14) (GR regs 15) (GR regs 16) (GR regs 17)
      (GR regs 18) (GR regs 19) (GR regs 20) (GR regs 21) (GR regs 22) (GR regs 23) (GR regs 24) (GR regs 25)
      (GR regs 26) (GR regs 27) (GR regs 28) (GR regs 29) (GR regs 30) (GR regs 31) fp_regs fp_csr mem
      bs lo HKM HKT HK36 ST HLO HAPP1 HAPP2 HAC HOG HOC HB RFR RGOT RCELL HCO RCO RSW RSH).
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & Ems
      & Hmu & Hwm & Hstk').
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
