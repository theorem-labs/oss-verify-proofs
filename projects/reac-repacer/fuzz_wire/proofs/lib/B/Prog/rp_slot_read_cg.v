(* rp_slot_read_cg: image B's rp_slot_read, its footprint contract (rp_slot_read_F_c.v) translated to the leaf form
   of the shared kit lib/B/Prog/LeafCgKit.v, in the form of reac-repacer/fuzz_uci's lib/B/Prog/rp_hot_clamp_cg.v.
   The translation lemma wire_rp_slot_read_cg_of_F is proved in this file's Section over the kit's
   leaf_cg_of_evtF_stmt (HGLUE, proved in LeafCgGlue.v); the walk's statement rp_slot_read_F_holds_stmt is in
   rp_slot_read_F_c.v, as rp_frame_channels_F_c.v holds its own.

   The premises of the target are rp_slot_read_F_c.v's premises VERBATIM, read at the call state (registers from
   regs, memory mem, footprint RNG_W W), and the kit's write premise for the 48 bytes of v on the branch that
   writes them. rp_slot_read DOES write caller memory (`sw a2, 0(s4)` at 0x817a0 writes v[s], 12 times), so a
   caller takes it through the kit's writing wrapper wire_leaf_wr_at, which carries the aowned argument.
   Its one program callee is rp_slot_width (0x8151c); at the footprint level the chain is
   rp_slot_width_contract_F -> rp_slot_read_contract_F, which is what the walk of this row must prove.
   The caller is check_read, which passes v inside its live class-1 fake frame: a byte of a live frame is never
   aowned and never in the loaded image (lib/B/Prog/WireCg.v wire_leaf_wr_at). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import AsanKA reac_frame_clean_len_c rp_frame_channels_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import rp_slot_width_F_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import rp_slot_read_F_c LeafCgKit.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_slot_width_c rp_slot_read_c.
Import ListNotations.
Open Scope Z_scope.
Module PSW := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_slot_width_c.
Module PSR := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_slot_read_c.

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

(* The bytes the leaf writes, as the kit's write ranges (lo, hi): v[0..11], [v, v + 48), when ok, and none
   otherwise. ok is the code's own test, `0 <=? PSW.rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2)`: on a
   declined read (negative width) rp_slot_read writes nothing, so its write list there is empty. Only an empty list on
   that branch lets dleaf_post's unchanged-outside clause give check_read v still holding UNTOUCHED_SAMPLE, and it
   makes the declined branch demand nothing about v, which is why rp_slot_read_F_c.v guards its v premises by the
   same test. *)
Definition wire_rsr_wr (ok : bool) (v : Z) : list (Z * Z) := if ok then [(v, v + RP_SLOT_READ_VLEN)] else [].

Definition wire_rp_slot_read_cg : Prop :=
  forall ly S (W : world) regs mem md (bs : list byte) (lo : Z),
    ecall_pre ly S W regs mem md ->
    let RNG := RNG_W W in let m := mem in
    let sp := YK11.getr regs (Z_to_bv 5 2) in
    let a0 := YK11.getr regs (Z_to_bv 5 10) in
    let a1 := YK11.getr regs (Z_to_bv 5 11) in
    let a2 := YK11.getr regs (Z_to_bv 5 12) in
    let a3 := YK11.getr regs (Z_to_bv 5 13) in
    bytes_at rsegs m A_M (le8 (Z_to_bv 64 KM)) ->
    bytes_at rsegs m A_T (le8 (Z_to_bv 64 KT)) ->
    bytes_at rsegs m A_K36 (le8 (Z_to_bv 64 K36)) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + RP_SLOT_READ_STK <= bv_unsigned sp ->
    app_mem (bv_unsigned sp - RP_SLOT_READ_STK) -> app_mem (bv_unsigned sp - 1) ->
    asan_cells m ->
    off_stk sp RP_SLOT_READ_STK GOT_CELL_K (MIDEND + 8 - GOT_CELL_K) ->
    (RP_AUDIO_OFF <= bv_unsigned a1 ->
       bv_unsigned a1 <= Z.of_nat (length bs) /\ bytes_at rsegs m (bv_unsigned a0) bs /\
       off_stk sp RP_SLOT_READ_STK (bv_unsigned a0) (Z.of_nat (length bs)) /\
       addressable m (bv_unsigned a0) (Z.of_nat (length bs)) /\
       bv_unsigned a0 <> 0) ->
    (0 <= PSW.rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2) ->
       wr_at rsegs m (bv_unsigned a3) RP_SLOT_READ_VLEN /\
       off_stk sp RP_SLOT_READ_STK (bv_unsigned a3) RP_SLOT_READ_VLEN /\
       (bv_unsigned a3 + RP_SLOT_READ_VLEN <= bv_unsigned a0 \/
        bv_unsigned a0 + Z.of_nat (length bs) <= bv_unsigned a3) /\
       addressable m (bv_unsigned a3) RP_SLOT_READ_VLEN) ->
    (* image B's UBSan premises (rp_slot_read_F_c.v: f non-NULL in the n >= 50 block above, f + 51 and v non-NULL and
       4-byte aligned on the reading path); image A's text lacks them *)
    (0 <= PSW.rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2) ->
       bv_unsigned a0 + RP_AUDIO_OFF + 1 <= 2 ^ 64 /\ bv_unsigned a3 <> 0 /\ bv_unsigned a3 mod 4 = 0) ->
    ExecF.rng RNG (bv_unsigned sp - RP_SLOT_READ_STK) RP_SLOT_READ_STK ->
    ExecF.rng RNG GOT_CELL_K 8 ->
    ExecF.rng RNG CELL_K 8 ->
    Forall (fun r => off_stk sp RP_SLOT_READ_STK (fst r) (snd r)) WIRE_RFC_CONSTS ->
    Forall (fun r => ExecF.rng RNG (fst r) (snd r)) WIRE_RFC_CONSTS ->
    (RP_AUDIO_OFF <= bv_unsigned a1 ->
       ExecF.rng RNG (bv_unsigned a0) (Z.of_nat (length bs)) /\
       ExecF.rng RNG (shadow_addr (bv_unsigned a0))
         (shadow_addr (bv_unsigned a0 + Z.of_nat (length bs) - 1) - shadow_addr (bv_unsigned a0) + 1)) ->
    (0 <= PSW.rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2) ->
       ExecF.rng RNG (bv_unsigned a3) RP_SLOT_READ_VLEN /\
       ExecF.rng RNG (shadow_addr (bv_unsigned a3))
         (shadow_addr (bv_unsigned a3 + RP_SLOT_READ_VLEN - 1) - shadow_addr (bv_unsigned a3) + 1)) ->
    (* On the branch that writes them, the samples are not allocator-owned (AR across the write: AR_frame_stmt)
       and not in the loaded image; check_read discharges both for its live fake frame (WireCg.v
       wire_leaf_wr_at). On the declined branch the range is empty and this premise asks for nothing. *)
    (forall x, in_wr (wire_rsr_wr (0 <=? PSW.rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2)) (bv_unsigned a3)) x ->
       ~ aowned ly S x /\ ~ in_img x) ->
    SRr W (cfg_at RP_SLOT_READ regs mem md)
      (dleaf_post ly S W regs mem md
         (Some (PSR.rp_slot_read_model (bv_unsigned a1) bs (bv_signed a2)))
         (wire_rsr_wr (0 <=? PSW.rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2)) (bv_unsigned a3))
         (fun m2 => 0 <= PSW.rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2) ->
            bytes_at rsegs m2 (bv_unsigned a3)
              (PSR.rp_slot_bytes bs (PSW.rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2)) (bv_signed a2)))).

(* The kit's generic translation (LeafCgKit.v leaf_cg_of_evtF_stmt, proved in LeafCgGlue.v) carries the footprint
   contract to the leaf form: the run is the footprint contract's at RNG := RNG_W W and the call state's registers,
   the window is its munch range, and the write list is v when the width is not negative, else empty. *)
Definition wire_rp_slot_read_cg_of_F_stmt : Prop := rp_slot_read_contract_F -> wire_rp_slot_read_cg.

(* The proof applies the kit's generic translation (HGLUE) to the footprint walk. The run is the footprint
   contract's at RNG := RNG_W W and the call state's registers; the window is its munch range, the window's bytes
   come from its stk (as mrd), v's bytes from its bytes_at on the accepted branch, and the callee-saved registers are
   the mkR fields read back. *)
Hypothesis HGLUE : leaf_cg_of_evtF_stmt.

Local Abbreviation GR r k := (YK11.getr r (Z_to_bv 5 k)).

Lemma wire_rp_slot_read_cg_of_F : wire_rp_slot_read_cg_of_F_stmt.
Proof.
  intros HF. unfold wire_rp_slot_read_cg.
  intros ly S W regs mem md bs lo HPRE. cbv zeta.
  intros HKM HKT HK36 ST HLO HAPP1 HAPP2 HAC HOCS HFR HV HUB RFR RGOT RCELL HCS HCR RBS RV HOWN.
  pose proof HGLUE as G. unfold leaf_cg_of_evtF_stmt, LeafCgKit.leaf_cg_of_evtF_stmt in G.
  eapply (G ly S W regs mem md RP_SLOT_READ RP_SLOT_READ_STK).
  - exact HPRE.
  - unfold RP_SLOT_READ_STK, RP_SLOT_READ_FRAME, RP_SLOT_WIDTH_STK, RP_SLOT_WIDTH_FRAME, RP_FRAME_CHANNELS_FRAME,
      LeafCgKit.ESTACK. lia.
  - intros x Hx.
    assert (Hvx : 0 <= x < 2 ^ 64 /\ w_H W (Z_to_bv 64 x) = false).
    { revert Hx. unfold wire_rsr_wr, LeafCgKit.in_wr.
      destruct (0 <=? PSW.rp_slot_width_model (bv_unsigned (GR regs 11)) bs (bv_signed (GR regs 12))) eqn:E;
        intros Hx; [|apply Exists_nil in Hx; destruct Hx].
      apply Z.leb_le in E. destruct (RV E) as (RBUF & _).
      apply Exists_cons in Hx.
      destruct Hx as [Hx|Hx]; [cbn [fst snd] in Hx | apply Exists_nil in Hx; destruct Hx].
      destruct RBUF as (R1 & R2 & R3). split; [lia|].
      pose proof (R3 x 1%nat ltac:(lia) ltac:(lia)) as Hw.
      unfold RNG_W, LeafCgKit.RNG_W, LeafCgKit.range_avoids, LeafCgKit.woff in Hw. cbv beta in Hw.
      specialize (Hw 0%nat ltac:(lia)).
      assert (Ex : bv_unsigned (Z_to_bv 64 x) = x) by exact (wa_unsigned x ltac:(lia)).
      rewrite Ex in Hw. replace (x + Z.of_nat 0) with x in Hw by lia. exact Hw. }
    destruct Hvx as (Hvx1 & Hvx2). split; [exact Hvx1|]. split; [exact Hvx2|]. exact (HOWN x Hx).
  - exact (HF (RNG_W W) (GR regs 1) (GR regs 2) (GR regs 3) (GR regs 4) (GR regs 5) (GR regs 6) (GR regs 7) (GR regs 8)
      (GR regs 9) (GR regs 10) (GR regs 11) (GR regs 12) (GR regs 13) (GR regs 14) (GR regs 15) (GR regs 16) (GR regs 17)
      (GR regs 18) (GR regs 19) (GR regs 20) (GR regs 21) (GR regs 22) (GR regs 23) (GR regs 24) (GR regs 25)
      (GR regs 26) (GR regs 27) (GR regs 28) (GR regs 29) (GR regs 30) (GR regs 31) fp_regs fp_csr mem
      bs lo HKM HKT HK36 ST HLO HAPP1 HAPP2 HAC HOCS HFR HV HUB RFR RGOT RCELL HCS HCR RBS RV).
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & Ems
      & Hwm & Hstk' & Hif).
    pose proof Hstk' as (Hs1 & Hs2 & Hs3).
    assert (Hwin : forall x, LeafCgKit.spZ regs - RP_SLOT_READ_STK <= x < LeafCgKit.spZ regs ->
                             exists b, mrd rsegs m' (Z_to_bv 64 x) = Some b).
    { intros x Hx. unfold LeafCgKit.spZ in Hx.
      destruct (Hs3 x ltac:(lia)) as (Hwv & Hmrd). exact Hmrd. }
    assert (Hcs : forall r, LeafCgKit.acallee_saved r -> r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/
      r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
      by (intros r Hr; unfold LeafCgKit.acallee_saved in Hr; lia).
    assert (Hlen : forall n s, length (PSR.rp_slot_bytes bs n s) = 48%nat)
      by (intros n s; unfold PSR.rp_slot_bytes; cbn [seq flat_map]; rewrite !length_app, !length_le4; reflexivity).
    assert (Hbx : forall (L : list byte) A, length L = 48%nat -> bytes_at rsegs m' A L ->
                    forall x, A <= x < A + RP_SLOT_READ_VLEN -> exists b, mrd rsegs m' (Z_to_bv 64 x) = Some b).
    { intros L A HL (Hb1 & Hb2 & Hb3) x Hx.
      assert (Hi : (Z.to_nat (x - A) < length L)%nat) by (rewrite HL; unfold RP_SLOT_READ_VLEN in Hx; lia).
      pose proof (Hb3 _ Hi) as Hm.
      replace (A + Z.of_nat (Z.to_nat (x - A))) with x in Hm by lia.
      destruct (nth_error L (Z.to_nat (x - A))) as [b|] eqn:En.
      - exists b. exact Hm.
      - apply nth_error_None in En. lia. }
    eexists. exists m'. split; [exact Ems|].
    revert Hif.
    destruct (0 <=? PSW.rp_slot_width_model (bv_unsigned (GR regs 11)) bs (bv_signed (GR regs 12))) eqn:E;
      intros Hif.
    + destruct Hif as (Hmu & Hbs).
      split; [exact Hmu|].
      split.
      * intros x [Hx|Hx]; [exact (Hwin x Hx)|].
        unfold wire_rsr_wr, LeafCgKit.in_wr in Hx. apply Exists_cons in Hx.
        destruct Hx as [Hx|Hx]; [cbn [fst snd] in Hx | apply Exists_nil in Hx; destruct Hx].
        exact (Hbx _ _ (Hlen _ _) Hbs x Hx).
      * split.
        -- intros r Hr. destruct (Hcs r Hr) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
             reflexivity.
        -- split; [intros r Er; injection Er as <-; reflexivity|].
           intros _. exact Hbs.
    + split; [exact Hif|].
      split.
      * intros x [Hx|Hx]; [exact (Hwin x Hx)|].
        unfold wire_rsr_wr, LeafCgKit.in_wr in Hx. apply Exists_nil in Hx. destruct Hx.
      * split.
        -- intros r Hr. destruct (Hcs r Hr) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
             reflexivity.
        -- split; [intros r Er; injection Er as <-; reflexivity|].
           intros Hw. apply Z.leb_le in Hw. rewrite Hw in E. discriminate E.
Qed.

End LeafCg.
