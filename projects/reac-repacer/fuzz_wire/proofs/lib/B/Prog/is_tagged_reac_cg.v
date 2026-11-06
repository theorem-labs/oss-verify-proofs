(* is_tagged_reac_cg: image B's is_tagged_reac (fuzz_wire.asan-ubsan 0x8103c), its footprint contract
   (lib/B/Prog/is_tagged_reac_F_c.v is_tagged_reac_contract_F) translated to the leaf form of the shared kit
   lib/B/Prog/LeafCgKit.v (SRr world walk). Form: reac-repacer/fuzz_uci's lib/B/Prog/rp_hot_clamp_cg.v and
   libreac/fuzz_decode's released lib/B/Prog/reac_frame_is_reac_cg.v: the premises of wire_is_tagged_reac_cg are the
   premises of is_tagged_reac_contract_F VERBATIM, read at the call state (registers from regs, memory mem, footprint
   RNG_W W); the post is the kit's dleaf_post with the result is_tagged_result and no written range.
   wire_is_tagged_reac_cg_of_F is proved in this file's Section over the kit's leaf_cg_of_evtF_stmt (HGLUE, proved in
   LeafCgGlue.v); the walk's statement is the footprint contract (wire_is_tagged_reac_holds_stmt below).
   The C, the code and every offset: lib/B/Prog/is_tagged_reac_F_c.v. In short: the frame [sp - 16, sp) (+0x0; ra
   stored at +0x4, read back at +0xbc); the GOT word 0x98878 (GOT_CELL_K, holding CELL_K = 0xa07f8) and the shadow base
   at CELL_K (+0x14 .. +0x1c); the bytes at f + 12, f + 13, f + 16, f + 17 (+0x34, +0x5c, +0x80, +0xa8), each after the
   instrumented check of its shadow byte; the result 1 when they are 0x81 0x00 0x88 0x19, else 0. Image B's UBSan
   checks (unimp at +0xc8) are refuted by `bv_unsigned a0 <> 0` (+0x8) and the addressable premise of [f + 16, f + 18)
   (+0x10, +0x44, +0x68, +0x90). The shadow premises `addressable` make every instrumented check pass, so the error
   path (`jal` 0x57e5c at +0xd8, +0xe8, +0xf8, +0x104) is not reached; no premise says that it is not called.
   No call returns to this function (its only calls are those of the error path), so the file states no return
   address. It writes no byte outside its frame, so its post has no written range and the target takes no aowned
   premise: a caller reads it by lib/B/Prog/WireCg.v wire_leaf_at. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import AsanKA is_tagged_reac_F_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import LeafCgKit.
Open Scope Z_scope.

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

Definition wire_is_tagged_reac_cg : Prop :=
  forall ly S (W : world) regs mem md (bs : list byte) (lo : Z),
    ecall_pre ly S W regs mem md ->
    let RNG := RNG_W W in let m := mem in let F := fp_regs in let fc := fp_csr in
    let ra := YK11.getr regs (Z_to_bv 5 1) in let sp := YK11.getr regs (Z_to_bv 5 2) in let gp := YK11.getr regs (Z_to_bv 5 3) in let tp := YK11.getr regs (Z_to_bv 5 4) in let t0 := YK11.getr regs (Z_to_bv 5 5) in let t1 := YK11.getr regs (Z_to_bv 5 6) in let t2 := YK11.getr regs (Z_to_bv 5 7) in let s0 := YK11.getr regs (Z_to_bv 5 8) in let s1 := YK11.getr regs (Z_to_bv 5 9) in let a0 := YK11.getr regs (Z_to_bv 5 10) in let a1 := YK11.getr regs (Z_to_bv 5 11) in let a2 := YK11.getr regs (Z_to_bv 5 12) in let a3 := YK11.getr regs (Z_to_bv 5 13) in let a4 := YK11.getr regs (Z_to_bv 5 14) in let a5 := YK11.getr regs (Z_to_bv 5 15) in let a6 := YK11.getr regs (Z_to_bv 5 16) in let a7 := YK11.getr regs (Z_to_bv 5 17) in let s2 := YK11.getr regs (Z_to_bv 5 18) in let s3 := YK11.getr regs (Z_to_bv 5 19) in let s4 := YK11.getr regs (Z_to_bv 5 20) in let s5 := YK11.getr regs (Z_to_bv 5 21) in let s6 := YK11.getr regs (Z_to_bv 5 22) in let s7 := YK11.getr regs (Z_to_bv 5 23) in let s8 := YK11.getr regs (Z_to_bv 5 24) in let s9 := YK11.getr regs (Z_to_bv 5 25) in let s10 := YK11.getr regs (Z_to_bv 5 26) in let s11 := YK11.getr regs (Z_to_bv 5 27) in let t3 := YK11.getr regs (Z_to_bv 5 28) in let t4 := YK11.getr regs (Z_to_bv 5 29) in let t5 := YK11.getr regs (Z_to_bv 5 30) in let t6 := YK11.getr regs (Z_to_bv 5 31) in
    (* Image B's UBSan premise: +0x8 `beqz a0, +0xc8` traps (unimp at +0xc8) on f == NULL. *)
    bv_unsigned a0 <> 0 ->
    (18 <= length bs)%nat -> bytes_at rsegs m (bv_unsigned a0) bs ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + IS_TAGGED_REAC_FRAME <= bv_unsigned sp ->
    off_stk sp IS_TAGGED_REAC_FRAME (bv_unsigned a0) 18 ->
    app_mem (bv_unsigned sp - IS_TAGGED_REAC_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    asan_cells m ->
    off_stk sp IS_TAGGED_REAC_FRAME GOT_CELL_K 8 ->
    off_stk sp IS_TAGGED_REAC_FRAME CELL_K 8 ->
    addressable m (bv_unsigned a0 + 12) 2 ->
    addressable m (bv_unsigned a0 + 16) 2 ->
    ExecF.rng RNG (bv_unsigned sp - IS_TAGGED_REAC_FRAME) IS_TAGGED_REAC_FRAME ->
    ExecF.rng RNG GOT_CELL_K 8 ->
    ExecF.rng RNG CELL_K 8 ->
    ExecF.rng RNG (bv_unsigned a0 + 12) 2 ->
    ExecF.rng RNG (bv_unsigned a0 + 16) 2 ->
    ExecF.rng RNG (shadow_addr (bv_unsigned a0 + 12))
      (shadow_addr (bv_unsigned a0 + 13) - shadow_addr (bv_unsigned a0 + 12) + 1) ->
    ExecF.rng RNG (shadow_addr (bv_unsigned a0 + 16))
      (shadow_addr (bv_unsigned a0 + 17) - shadow_addr (bv_unsigned a0 + 16) + 1) ->
    SRr W (cfg_at IS_TAGGED_REAC regs mem md)
      (dleaf_post ly S W regs mem md (Some (is_tagged_result bs)) [] (fun _ => True)).

Definition wire_is_tagged_reac_cg_of_F_stmt : Prop := is_tagged_reac_contract_F -> wire_is_tagged_reac_cg.

(* The proof applies the kit's generic translation (HGLUE) to the footprint walk. The run is the footprint
   contract's at RNG := RNG_W W and the call state's registers; the window is its munch range, the window's bytes
   come from its stk (as mrd), the callee-saved registers are the mkR fields read back, and a0 is the result. *)
Hypothesis HGLUE : leaf_cg_of_evtF_stmt.

Local Abbreviation GR r k := (YK11.getr r (Z_to_bv 5 k)).

Lemma wire_is_tagged_reac_cg_of_F : wire_is_tagged_reac_cg_of_F_stmt.
Proof.
  intros HF. unfold wire_is_tagged_reac_cg.
  intros ly S W regs mem md bs lo HPRE. cbv zeta.
  intros HNZ HLEN HB ST HLO HOFF HAPP1 HAPP2 HAC HOG HOC HAD12 HAD16 RFR RGOT RCELL R12 R16 RS12 RS16.
  pose proof HGLUE as G. unfold leaf_cg_of_evtF_stmt, LeafCgKit.leaf_cg_of_evtF_stmt in G.
  eapply (G ly S W regs mem md IS_TAGGED_REAC IS_TAGGED_REAC_FRAME).
  - exact HPRE.
  - unfold IS_TAGGED_REAC_FRAME, LeafCgKit.ESTACK. lia.
  - intros x Hx. unfold LeafCgKit.in_wr in Hx. inversion Hx.
  - exact (HF (RNG_W W) (GR regs 1) (GR regs 2) (GR regs 3) (GR regs 4) (GR regs 5) (GR regs 6) (GR regs 7) (GR regs 8)
      (GR regs 9) (GR regs 10) (GR regs 11) (GR regs 12) (GR regs 13) (GR regs 14) (GR regs 15) (GR regs 16) (GR regs 17)
      (GR regs 18) (GR regs 19) (GR regs 20) (GR regs 21) (GR regs 22) (GR regs 23) (GR regs 24) (GR regs 25)
      (GR regs 26) (GR regs 27) (GR regs 28) (GR regs 29) (GR regs 30) (GR regs 31) fp_regs fp_csr mem
      bs lo HNZ HLEN HB ST HLO HOFF HAPP1 HAPP2 HAC HOG HOC HAD12 HAD16 RFR RGOT RCELL R12 R16 RS12 RS16).
  - intros ms' (a1' & a2' & a3' & a4' & m' & Ems & Hmu & Hwm & Hstk').
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

(* The statement the walk will prove: the footprint contract of lib/B/Prog/is_tagged_reac_F_c.v (the row of the unit's
   closing statement for this function). With HGLUE, wire_is_tagged_reac_cg_of_F turns it into wire_is_tagged_reac_cg,
   which a caller takes through lib/B/Prog/WireCg.v wire_leaf_at. It has no callee premise: no call returns to this
   function (above). *)
Definition wire_is_tagged_reac_holds_stmt : Prop := is_tagged_reac_contract_F.
