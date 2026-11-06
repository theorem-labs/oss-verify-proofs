(* rp_meter_counter_cg: image A's rp_meter_counter (entry 0x81168), its footprint contract (rp_meter_counter_F_c.v)
   translated to cgif_file's leaf form (SRr world walk). Form: reac-repacer/fuzz_uci lib/A/Prog/rp_hot_clamp_cg.v (the
   leaf form of a leaf that writes a caller buffer, with its translation lemma), with the conditional write range of
   libreac/fuzz_decode lib/A/Prog/reac_decode_cg.v (the leaf writes the counter only when meter_ok holds) and a result
   in a0 (RES = Some ...). No released ASan statement of rp_meter_counter exists; this is written new.
   The premises of the target are rp_meter_counter_F_c.v's premises VERBATIM, read at the call state (registers from
   regs, memory mem, footprint RNG_W W), and the kit's write premise for the 2 counter bytes. The cgif side (names,
   verbatim copies, the facts a proof may assume, the generic translation lemma) is the shared kit
   lib/A/Prog/LeafCgKit.v; this file only re-declares the kit's Section Variables and names its definitions.
   wire_rp_meter_counter_cg_of_F is proved in this file's Section over the kit's leaf_cg_of_evtF_stmt (HGLUE, proved in
   LeafCgGlue.v), as the template proves its translation lemma. wire_rp_meter_counter_holds_stmt is the statement the
   walk (a later file) will prove: the footprint contract itself, since the leaf calls no other program function.
   The caller is check_meter, which passes the address of its local ctr inside its live class-0 fake frame: a byte of
   a live frame is never aowned and never in the image (lib/A/Prog/WireCg.v wire_leaf_wr_at). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import AsanKA rp_meter_counter_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import rp_meter_counter_F_c LeafCgKit.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_meter_counter_c.
Import ListNotations.
Open Scope Z_scope.
Module PMC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_meter_counter_c.

(* The statement the walk will prove (close row H_PROG_RMET_F): the footprint contract. The leaf calls only the
   refuted report sinks, so no callee contract is a premise. *)
Definition wire_rp_meter_counter_holds_stmt : Prop := rp_meter_counter_contract_F.

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
(* The kit's definitions at these names (LeafCgKit.v; argument order = the kit's Section order). *)
Let ecall_pre := @LeafCgKit.ecall_pre world w_H alayout astate AR ly_stk_lo ly_stk_hi ret_ok as_gp as_tp.
Let RNG_W := @LeafCgKit.RNG_W world w_H.
Let dleaf_post := @LeafCgKit.dleaf_post fx world w_H alayout astate AR aview same_but_materialized.
Let leaf_cg_of_evtF_stmt := @LeafCgKit.leaf_cg_of_evtF_stmt fx world w_H SRr alayout astate AR aview
  same_but_materialized ly_stk_lo ly_stk_hi ret_ok as_gp as_tp aowned.

(* The bytes the leaf writes, as the kit's write ranges (lo, hi): the 2 counter bytes [c, c + 2) when the frame is
   counted (the `sh a0, 0(a2)` at 0x81268, reached only when meter_ok holds), else none. *)
Definition wire_rmc_wr (n : Z) (bs : list byte) (c : Z) : list (Z * Z) :=
  if PMC.meter_ok n bs then [(c, c + 2)] else [].

Definition wire_rp_meter_counter_cg : Prop :=
  forall ly S (W : world) regs mem md (bs : list byte) (lo : Z),
    ecall_pre ly S W regs mem md ->
    let RNG := RNG_W W in let m := mem in let F := fp_regs in let fc := fp_csr in
    let ra := YK11.getr regs (Z_to_bv 5 1) in let sp := YK11.getr regs (Z_to_bv 5 2) in let gp := YK11.getr regs (Z_to_bv 5 3) in let tp := YK11.getr regs (Z_to_bv 5 4) in let t0 := YK11.getr regs (Z_to_bv 5 5) in let t1 := YK11.getr regs (Z_to_bv 5 6) in let t2 := YK11.getr regs (Z_to_bv 5 7) in let s0 := YK11.getr regs (Z_to_bv 5 8) in let s1 := YK11.getr regs (Z_to_bv 5 9) in let a0 := YK11.getr regs (Z_to_bv 5 10) in let a1 := YK11.getr regs (Z_to_bv 5 11) in let a2 := YK11.getr regs (Z_to_bv 5 12) in let a3 := YK11.getr regs (Z_to_bv 5 13) in let a4 := YK11.getr regs (Z_to_bv 5 14) in let a5 := YK11.getr regs (Z_to_bv 5 15) in let a6 := YK11.getr regs (Z_to_bv 5 16) in let a7 := YK11.getr regs (Z_to_bv 5 17) in let s2 := YK11.getr regs (Z_to_bv 5 18) in let s3 := YK11.getr regs (Z_to_bv 5 19) in let s4 := YK11.getr regs (Z_to_bv 5 20) in let s5 := YK11.getr regs (Z_to_bv 5 21) in let s6 := YK11.getr regs (Z_to_bv 5 22) in let s7 := YK11.getr regs (Z_to_bv 5 23) in let s8 := YK11.getr regs (Z_to_bv 5 24) in let s9 := YK11.getr regs (Z_to_bv 5 25) in let s10 := YK11.getr regs (Z_to_bv 5 26) in let s11 := YK11.getr regs (Z_to_bv 5 27) in let t3 := YK11.getr regs (Z_to_bv 5 28) in let t4 := YK11.getr regs (Z_to_bv 5 29) in let t5 := YK11.getr regs (Z_to_bv 5 30) in let t6 := YK11.getr regs (Z_to_bv 5 31) in
    (14 <= bv_unsigned a1 -> (14 <= length bs)%nat /\ bytes_at rsegs m (bv_unsigned a0) bs) ->
    (1000 <= bv_unsigned a1 -> (20 <= length bs)%nat) ->
    (PMC.meter_ok (bv_unsigned a1) bs = true -> wr_at rsegs m (bv_unsigned a2) 2) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + RP_METER_COUNTER_FRAME <= bv_unsigned sp ->
    (14 <= bv_unsigned a1 -> off_stk sp RP_METER_COUNTER_FRAME (bv_unsigned a0 + 12) 2) ->
    (1000 <= bv_unsigned a1 -> off_stk sp RP_METER_COUNTER_FRAME (bv_unsigned a0 + 12) 8) ->
    (PMC.meter_ok (bv_unsigned a1) bs = true -> off_stk sp RP_METER_COUNTER_FRAME (bv_unsigned a2) 2) ->
    app_mem (bv_unsigned sp - RP_METER_COUNTER_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    asan_cells m ->
    off_stk sp RP_METER_COUNTER_FRAME GOT_CELL_K 8 ->
    off_stk sp RP_METER_COUNTER_FRAME CELL_K 8 ->
    (14 <= bv_unsigned a1 -> addressable m (bv_unsigned a0 + 12) 2) ->
    (1000 <= bv_unsigned a1 -> addressable m (bv_unsigned a0 + 12) 8) ->
    (PMC.meter_ok (bv_unsigned a1) bs = true -> addressable m (bv_unsigned a2) 2) ->
    ExecF.rng RNG (bv_unsigned sp - RP_METER_COUNTER_FRAME) RP_METER_COUNTER_FRAME ->
    ExecF.rng RNG GOT_CELL_K 8 ->
    ExecF.rng RNG CELL_K 8 ->
    (14 <= bv_unsigned a1 -> ExecF.rng RNG (bv_unsigned a0 + 12) 2) ->
    (14 <= bv_unsigned a1 ->
       ExecF.rng RNG (shadow_addr (bv_unsigned a0 + 12))
         (shadow_addr (bv_unsigned a0 + 12 + 2 - 1) - shadow_addr (bv_unsigned a0 + 12) + 1)) ->
    (1000 <= bv_unsigned a1 -> ExecF.rng RNG (bv_unsigned a0 + 12) 8) ->
    (1000 <= bv_unsigned a1 ->
       ExecF.rng RNG (shadow_addr (bv_unsigned a0 + 12))
         (shadow_addr (bv_unsigned a0 + 12 + 8 - 1) - shadow_addr (bv_unsigned a0 + 12) + 1)) ->
    (PMC.meter_ok (bv_unsigned a1) bs = true -> ExecF.rng RNG (bv_unsigned a2) 2) ->
    (PMC.meter_ok (bv_unsigned a1) bs = true ->
       ExecF.rng RNG (shadow_addr (bv_unsigned a2))
         (shadow_addr (bv_unsigned a2 + 2 - 1) - shadow_addr (bv_unsigned a2) + 1)) ->
    (* the written counter is not allocator-owned (AR across the write: AR_frame_stmt) and not in the loaded image
       (its post bytes, read through mrd, are then overlay bytes); check_meter discharges both for its live fake
       frame (WireCg.v wire_leaf_wr_at) *)
    (forall x, in_wr (wire_rmc_wr (bv_unsigned a1) bs (bv_unsigned a2)) x -> ~ aowned ly S x /\ ~ in_img x) ->
    SRr W (cfg_at RP_METER_COUNTER regs mem md)
      (dleaf_post ly S W regs mem md (Some (if PMC.meter_ok (bv_unsigned a1) bs then 1 else 0))
         (wire_rmc_wr (bv_unsigned a1) bs (bv_unsigned a2))
         (fun m2 => PMC.meter_ok (bv_unsigned a1) bs = true ->
            bytes_at rsegs m2 (bv_unsigned a2) (le2 (Z_to_bv 64 (PMC.meter_value (bv_unsigned a1) bs))))).

Definition wire_rp_meter_counter_cg_of_F_stmt : Prop := rp_meter_counter_contract_F -> wire_rp_meter_counter_cg.

(* The proof applies the kit's generic translation (HGLUE) to the footprint walk. The run is the footprint
   contract's at RNG := RNG_W W and the call state's registers; the window is its munch range, the window's bytes
   come from its stk (as mrd), the counter's bytes from its bytes_at (when meter_ok), the result is the mkR a0 field,
   and the callee-saved registers are the mkR fields read back. *)
Hypothesis HGLUE : leaf_cg_of_evtF_stmt.

Local Abbreviation GR r k := (YK11.getr r (Z_to_bv 5 k)).

Lemma wire_rp_meter_counter_cg_of_F : wire_rp_meter_counter_cg_of_F_stmt.
Proof.
  intros HF. unfold wire_rp_meter_counter_cg.
  intros ly S W regs mem md bs lo HPRE. cbv zeta.
  intros HB1 HB2 HWR ST HLO HOF1 HOF2 HOFC HAPP1 HAPP2 HAC HOG HOC HAD1 HAD2 HADC
    RFR RGOT RCELL RB1 RS1 RB2 RS2 RC RSC HOWN.
  pose proof HGLUE as G. unfold leaf_cg_of_evtF_stmt, LeafCgKit.leaf_cg_of_evtF_stmt in G.
  eapply (G ly S W regs mem md RP_METER_COUNTER RP_METER_COUNTER_FRAME).
  - exact HPRE.
  - unfold RP_METER_COUNTER_FRAME, LeafCgKit.ESTACK. lia.
  - intros x Hx. split; [|split; [|exact (HOWN x Hx)]];
      revert Hx; unfold wire_rmc_wr; destruct (PMC.meter_ok (bv_unsigned (GR regs 11)) bs) eqn:Eok; intros Hx;
      unfold in_wr in Hx;
      [ apply Exists_cons in Hx; destruct Hx as [Hx|Hx]; [cbn [fst snd] in Hx | apply Exists_nil in Hx; destruct Hx]
      | apply Exists_nil in Hx; destruct Hx
      | apply Exists_cons in Hx; destruct Hx as [Hx|Hx]; [cbn [fst snd] in Hx | apply Exists_nil in Hx; destruct Hx]
      | apply Exists_nil in Hx; destruct Hx ].
    + destruct (RC ltac:(first [reflexivity | exact Eok])) as (R1 & R2 & R3). lia.
    + destruct (RC ltac:(first [reflexivity | exact Eok])) as (R1 & R2 & R3).
      pose proof (R3 x 1%nat ltac:(lia) ltac:(lia)) as Hv.
      unfold RNG_W, LeafCgKit.RNG_W, range_avoids, woff in Hv. cbv beta in Hv.
      specialize (Hv 0%nat ltac:(lia)).
      assert (Ex : bv_unsigned (Z_to_bv 64 x) = x) by exact (wa_unsigned x ltac:(lia)).
      rewrite Ex in Hv. replace (x + Z.of_nat 0) with x in Hv by lia. exact Hv.
  - exact (HF (RNG_W W) (GR regs 1) (GR regs 2) (GR regs 3) (GR regs 4) (GR regs 5) (GR regs 6) (GR regs 7) (GR regs 8)
      (GR regs 9) (GR regs 10) (GR regs 11) (GR regs 12) (GR regs 13) (GR regs 14) (GR regs 15) (GR regs 16) (GR regs 17)
      (GR regs 18) (GR regs 19) (GR regs 20) (GR regs 21) (GR regs 22) (GR regs 23) (GR regs 24) (GR regs 25)
      (GR regs 26) (GR regs 27) (GR regs 28) (GR regs 29) (GR regs 30) (GR regs 31) fp_regs fp_csr mem
      bs lo HB1 HB2 HWR ST HLO HOF1 HOF2 HOFC HAPP1 HAPP2 HAC HOG HOC HAD1 HAD2 HADC
      RFR RGOT RCELL RB1 RS1 RB2 RS2 RC RSC).
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & Ems & Hwm
      & Hstk' & Hif).
    pose proof Hstk' as (Hs1 & Hs2 & Hs3).
    assert (Hwin : forall x, spZ regs - RP_METER_COUNTER_FRAME <= x < spZ regs ->
      exists b, mrd rsegs m' (Z_to_bv 64 x) = Some b).
    { intros x Hx. unfold spZ in Hx.
      destruct (Hs3 x ltac:(lia)) as (Hwv & Hmrd). exact Hmrd. }
    assert (Hcs : forall r, acallee_saved r -> r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/
      r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (intros r Hr; unfold acallee_saved in Hr; lia).
    eexists. exists m'. split; [exact Ems|].
    unfold wire_rmc_wr. revert Hif.
    destruct (PMC.meter_ok (bv_unsigned (GR regs 11)) bs); intros Hif;
      (split; [|split; [|split;
        [ intros r Hr; destruct (Hcs r Hr) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
          reflexivity
        | split; [intros r Er; injection Er as Er; subst r; reflexivity|] ]]]).
    + exact (proj1 Hif).
    + intros x [Hx|Hx]; [exact (Hwin x Hx)|].
      unfold in_wr in Hx. apply Exists_cons in Hx.
      destruct Hx as [Hx|Hx]; [cbn [fst snd] in Hx | apply Exists_nil in Hx; destruct Hx].
      destruct Hif as (Hmu & Hb1 & Hb2 & Hb3).
      assert (Hlen : length (le2 (Z_to_bv 64 (PMC.meter_value (bv_unsigned (GR regs 11)) bs))) = 2%nat)
        by (unfold le2; apply length_Z_to_le_bytes).
      assert (Hi : (Z.to_nat (x - bv_unsigned (GR regs 12)) <
                    length (le2 (Z_to_bv 64 (PMC.meter_value (bv_unsigned (GR regs 11)) bs))))%nat)
        by (rewrite Hlen; lia).
      pose proof (Hb3 _ Hi) as Hm.
      replace (bv_unsigned (GR regs 12) + Z.of_nat (Z.to_nat (x - bv_unsigned (GR regs 12)))) with x in Hm by lia.
      destruct (nth_error (le2 (Z_to_bv 64 (PMC.meter_value (bv_unsigned (GR regs 11)) bs)))
                  (Z.to_nat (x - bv_unsigned (GR regs 12)))) as [b|] eqn:En.
      * exists b. exact Hm.
      * apply nth_error_None in En. lia.
    + intros _. exact (proj2 Hif).
    + exact Hif.
    + intros x [Hx|Hx]; [exact (Hwin x Hx)|].
      unfold in_wr in Hx. apply Exists_nil in Hx. destruct Hx.
    + intros Ht. discriminate Ht.
Qed.

End LeafCg.
