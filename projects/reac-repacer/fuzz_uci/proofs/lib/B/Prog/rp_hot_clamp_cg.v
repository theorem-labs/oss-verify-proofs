(* Modified by Theorem Labs: copied from this unit's lib/A/Prog/rp_hot_clamp_cg.v (commit ba35beec1417; itself in the form of proofs/libreac/fuzz_decode/lib/A/Prog/reac_frame_is_reac_cg.v and reac_decode_cg.v at recipes commit 88154566652a) for reac-repacer/fuzz_uci's rp_hot_clamp in image B: Img0 / AsanCells / AsanKA / rp_hot_clamp_c / rp_hot_clamp_F_c / LeafCgKit are lib/B's, and the target carries image B's two UBSan premises `bv_unsigned a0 <> 0` and `bv_unsigned a0 mod 4 = 0` (lib/B/Prog/rp_hot_clamp_F_c.v; traps 0x7fd40 and 0x7fd44 / 0x7fd48, unimp at 0x7feb4), which the translation lemma passes on to the footprint contract; LeafCgKit's generic translation is unchanged. *)
(* rp_hot_clamp_cg: image B's rp_hot_clamp, its footprint contract (rp_hot_clamp_F_c.v) translated to cgif_file's leaf
   form (SRr world walk). The premises of the target are rp_hot_clamp_F_c.v's premises VERBATIM, read at the call
   state (registers from regs, memory mem, footprint RNG_W W), and the kit's write premise for the 20 written bytes.
   The cgif side (names, verbatim copies, the facts a proof may assume, the generic translation lemma) is the shared
   kit lib/B/Prog/LeafCgKit.v; this file only re-declares the kit's Section Variables and names its definitions.
   uci_rp_hot_clamp_cg_of_F is proved in this file's Section over the kit's leaf_cg_of_evtF_stmt (HGLUE, proved in
   LeafCgGlue.v). The caller is check_clamp, which passes a struct inside its live class-1 fake frame: a byte of a live
   frame is never aowned and never in the image (lib/B/Prog/UciCg.v uci_leaf_wr_at). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog Require Import AsanKA rp_hot_clamp_c.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK11.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog Require Import rp_hot_clamp_F_c LeafCgKit.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Spec Require Import UciModel.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog Require rp_hot_clamp_c.
Import ListNotations.
Open Scope Z_scope.
Module PHC := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog.rp_hot_clamp_c.

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

(* The bytes the leaf writes, as the kit's write ranges (lo, hi): the struct [p, p + 20). *)
Definition uci_rhc_wr (p : Z) : list (Z * Z) := [(p, p + PHC.RP_HOT_SIZE)].

Definition uci_rp_hot_clamp_cg : Prop :=
  forall ly S (W : world) regs mem md (p : rp_hot) (mm lo : Z),
    ecall_pre ly S W regs mem md ->
    let RNG := RNG_W W in let m := mem in let F := fp_regs in let fc := fp_csr in
    let ra := YK11.getr regs (Z_to_bv 5 1) in let sp := YK11.getr regs (Z_to_bv 5 2) in let gp := YK11.getr regs (Z_to_bv 5 3) in let tp := YK11.getr regs (Z_to_bv 5 4) in let t0 := YK11.getr regs (Z_to_bv 5 5) in let t1 := YK11.getr regs (Z_to_bv 5 6) in let t2 := YK11.getr regs (Z_to_bv 5 7) in let s0 := YK11.getr regs (Z_to_bv 5 8) in let s1 := YK11.getr regs (Z_to_bv 5 9) in let a0 := YK11.getr regs (Z_to_bv 5 10) in let a1 := YK11.getr regs (Z_to_bv 5 11) in let a2 := YK11.getr regs (Z_to_bv 5 12) in let a3 := YK11.getr regs (Z_to_bv 5 13) in let a4 := YK11.getr regs (Z_to_bv 5 14) in let a5 := YK11.getr regs (Z_to_bv 5 15) in let a6 := YK11.getr regs (Z_to_bv 5 16) in let a7 := YK11.getr regs (Z_to_bv 5 17) in let s2 := YK11.getr regs (Z_to_bv 5 18) in let s3 := YK11.getr regs (Z_to_bv 5 19) in let s4 := YK11.getr regs (Z_to_bv 5 20) in let s5 := YK11.getr regs (Z_to_bv 5 21) in let s6 := YK11.getr regs (Z_to_bv 5 22) in let s7 := YK11.getr regs (Z_to_bv 5 23) in let s8 := YK11.getr regs (Z_to_bv 5 24) in let s9 := YK11.getr regs (Z_to_bv 5 25) in let s10 := YK11.getr regs (Z_to_bv 5 26) in let s11 := YK11.getr regs (Z_to_bv 5 27) in let t3 := YK11.getr regs (Z_to_bv 5 28) in let t4 := YK11.getr regs (Z_to_bv 5 29) in let t5 := YK11.getr regs (Z_to_bv 5 30) in let t6 := YK11.getr regs (Z_to_bv 5 31) in
    (* Image B's UBSan premises: 0x7fd40 `beq a0, zero, 0x7feb4` traps (unimp at 0x7feb4) on p == NULL, and 0x7fd44
       `andi a2, a0, 3` / 0x7fd48 `bne a2, zero, 0x7feb4` trap on a misaligned p. *)
    bv_unsigned a0 <> 0 ->
    bv_unsigned a0 mod 4 = 0 ->
    PHC.hot_int p ->
    0 <= mm <= INT_MAX ->
    bv_unsigned a1 = mm ->
    rw_cells rsegs m (bv_unsigned a0) (PHC.hot_cells p) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + RP_HOT_CLAMP_FRAME <= bv_unsigned sp ->
    off_stk sp RP_HOT_CLAMP_FRAME (bv_unsigned a0) PHC.RP_HOT_SIZE ->
    app_mem (bv_unsigned sp - RP_HOT_CLAMP_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    asan_cells m ->
    off_stk sp RP_HOT_CLAMP_FRAME GOT_CELL_K 8 ->
    off_stk sp RP_HOT_CLAMP_FRAME CELL_K 8 ->
    addressable m (bv_unsigned a0) PHC.RP_HOT_SIZE ->
    ExecF.rng RNG (bv_unsigned sp - RP_HOT_CLAMP_FRAME) RP_HOT_CLAMP_FRAME ->
    ExecF.rng RNG GOT_CELL_K 8 ->
    ExecF.rng RNG CELL_K 8 ->
    ExecF.rng RNG (bv_unsigned a0) PHC.RP_HOT_SIZE ->
    ExecF.rng RNG (shadow_addr (bv_unsigned a0))
      (shadow_addr (bv_unsigned a0 + PHC.RP_HOT_SIZE - 1) - shadow_addr (bv_unsigned a0) + 1) ->
    (* the written struct is not allocator-owned (AR across the write: AR_frame_stmt) and not in the loaded image
       (its post bytes, read through mrd, are then overlay bytes); check_clamp discharges both for its live fake
       frame (UciCg.v uci_leaf_wr_at) *)
    (forall x, in_wr (uci_rhc_wr (bv_unsigned a0)) x -> ~ aowned ly S x /\ ~ in_img x) ->
    SRr W (cfg_at RP_HOT_CLAMP regs mem md)
      (dleaf_post ly S W regs mem md None (uci_rhc_wr (bv_unsigned a0))
         (fun m2 => rw_cells rsegs m2 (bv_unsigned a0) (PHC.hot_cells (rp_hot_clamp_m p mm)))).

Definition uci_rp_hot_clamp_cg_of_F_stmt : Prop := rp_hot_clamp_contract_F -> uci_rp_hot_clamp_cg.

(* The proof applies the kit's generic translation (HGLUE) to the footprint walk. The run is the footprint
   contract's at RNG := RNG_W W and the call state's registers; the window is its munch range, the window's bytes
   come from its stk (as mrd), the struct's bytes from its rw_cells, and the callee-saved registers are the mkR fields
   read back. *)
Hypothesis HGLUE : leaf_cg_of_evtF_stmt.

Local Abbreviation GR r k := (YK11.getr r (Z_to_bv 5 k)).

Lemma uci_rp_hot_clamp_cg_of_F : uci_rp_hot_clamp_cg_of_F_stmt.
Proof.
  intros HF. unfold uci_rp_hot_clamp_cg.
  intros ly S W regs mem md p mm lo HPRE. cbv zeta.
  intros HNZ HAL HINT HMM HA1 HCELLS ST HLO HOFF HAPP1 HAPP2 HAC HOG HOC HADDR RFR RGOT RCELL RBUF RSH HOWN.
  pose proof HGLUE as G. unfold leaf_cg_of_evtF_stmt, LeafCgKit.leaf_cg_of_evtF_stmt in G.
  eapply (G ly S W regs mem md RP_HOT_CLAMP RP_HOT_CLAMP_FRAME).
  - exact HPRE.
  - unfold RP_HOT_CLAMP_FRAME, LeafCgKit.ESTACK. lia.
  - intros x Hx. split; [|split; [|exact (HOWN x Hx)]];
      unfold uci_rhc_wr, in_wr in Hx; apply Exists_cons in Hx;
      (destruct Hx as [Hx|Hx]; [cbn [fst snd] in Hx | apply Exists_nil in Hx; destruct Hx]).
    + destruct RBUF as (R1 & R2 & R3). lia.
    + destruct RBUF as (R1 & R2 & R3).
      pose proof (R3 x 1%nat ltac:(lia) ltac:(lia)) as Hv.
      unfold RNG_W, LeafCgKit.RNG_W, range_avoids, woff in Hv. cbv beta in Hv.
      specialize (Hv 0%nat ltac:(lia)).
      assert (Ex : bv_unsigned (Z_to_bv 64 x) = x) by exact (wa_unsigned x ltac:(lia)).
      rewrite Ex in Hv. replace (x + Z.of_nat 0) with x in Hv by lia. exact Hv.
  - exact (HF (RNG_W W) (GR regs 1) (GR regs 2) (GR regs 3) (GR regs 4) (GR regs 5) (GR regs 6) (GR regs 7) (GR regs 8)
      (GR regs 9) (GR regs 10) (GR regs 11) (GR regs 12) (GR regs 13) (GR regs 14) (GR regs 15) (GR regs 16) (GR regs 17)
      (GR regs 18) (GR regs 19) (GR regs 20) (GR regs 21) (GR regs 22) (GR regs 23) (GR regs 24) (GR regs 25)
      (GR regs 26) (GR regs 27) (GR regs 28) (GR regs 29) (GR regs 30) (GR regs 31) fp_regs fp_csr mem
      p mm lo HNZ HAL HINT HMM HA1 HCELLS ST HLO HOFF HAPP1 HAPP2 HAC HOG HOC HADDR RFR RGOT RCELL RBUF RSH).
  - intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & Ems
      & Hmu & Hwm & Hstk' & Hcl).
    pose proof Hstk' as (Hs1 & Hs2 & Hs3).
    assert (Hwin : forall x, spZ regs - RP_HOT_CLAMP_FRAME <= x < spZ regs -> exists b, mrd rsegs m' (Z_to_bv 64 x) = Some b).
    { intros x Hx. unfold spZ in Hx.
      destruct (Hs3 x ltac:(lia)) as (Hwv & Hmrd). exact Hmrd. }
    assert (Hcs : forall r, acallee_saved r -> r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/
      r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (intros r Hr; unfold acallee_saved in Hr; lia).
    eexists. exists m'. split; [exact Ems|].
    split; [exact Hmu|].
    split.
    + intros x [Hx|Hx]; [exact (Hwin x Hx)|].
      unfold uci_rhc_wr, in_wr in Hx. apply Exists_cons in Hx.
      destruct Hx as [Hx|Hx]; [cbn [fst snd] in Hx | apply Exists_nil in Hx; destruct Hx].
      destruct Hcl as ((Hwf & Hb1 & Hb2 & Hb3) & _).
      assert (Hlen : length (cells_bytes (PHC.hot_cells (rp_hot_clamp_m p mm))) = 20%nat)
        by (rewrite (cells_bytes_length _ Hwf); reflexivity).
      assert (Hi : (Z.to_nat (x - bv_unsigned (GR regs 10)) < length (cells_bytes (PHC.hot_cells (rp_hot_clamp_m p mm))))%nat)
        by (rewrite Hlen; unfold PHC.RP_HOT_SIZE in Hx; lia).
      pose proof (Hb3 _ Hi) as Hm.
      replace (bv_unsigned (GR regs 10) + Z.of_nat (Z.to_nat (x - bv_unsigned (GR regs 10)))) with x in Hm by lia.
      destruct (nth_error (cells_bytes (PHC.hot_cells (rp_hot_clamp_m p mm))) (Z.to_nat (x - bv_unsigned (GR regs 10))))
        as [b|] eqn:En.
      * exists b. exact Hm.
      * apply nth_error_None in En. lia.
    + split.
      * intros r Hr. destruct (Hcs r Hr) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
          reflexivity.
      * split; [intros r Er; discriminate Er|].
        exact Hcl.
Qed.

End LeafCg.
