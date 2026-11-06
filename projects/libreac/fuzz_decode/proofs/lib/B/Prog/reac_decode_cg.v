(* reac_decode_cg: decode image B's reac_decode, its footprint contract (reac_decode_F_nosh.v: reac_decode_F_c.v without its shadow_rw premise) translated to cgif_file's leaf form
   (SRr world walk), as a STATEMENT (a Definition of a Prop; no proof here). Port of fuzz_decode to the released
   cgif_file_fuzzer structure (the port recipe, sec. 3). The premises of the
   target are reac_decode_F_nosh.v's premises VERBATIM (= reac_decode_F_c.v's without `shadow_rw m`), read at the call state (registers from regs, memory mem, footprint RNG_W W).
   The cgif side (names, verbatim copies, the facts a proof may assume, the generic translation lemma) is the shared
   kit lib/B/Prog/LeafCgKit.v; this file only re-declares the kit's Section Variables and names its definitions.
   A proof of `dec_reac_decode_cg_of_F_stmt` goes in this file's Section, taking the kit's `_stmt` facts as Section
   Hypotheses, and applies LeafCgKit's leaf_cg_of_evtF_stmt (proof: LeafCgGlue.v). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import AsanKA reac_frame_inspect_c reac_decode_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import reac_frame_inspect_F_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import ExecF MState Frame.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import reac_decode_F_c reac_decode_F_nosh LeafCgKit.
Open Scope Z_scope.

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

Definition dec_reac_decode_cg : Prop :=
  forall ly S (W : world) regs mem md (bs : list byte) (raw mode out nch ns lo : Z),
    ecall_pre ly S W regs mem md ->
    let RNG := RNG_W W in let m := mem in let F := fp_regs in let fc := fp_csr in
    let ra := YK11.getr regs (Z_to_bv 5 1) in let sp := YK11.getr regs (Z_to_bv 5 2) in let gp := YK11.getr regs (Z_to_bv 5 3) in let tp := YK11.getr regs (Z_to_bv 5 4) in let t0 := YK11.getr regs (Z_to_bv 5 5) in let t1 := YK11.getr regs (Z_to_bv 5 6) in let t2 := YK11.getr regs (Z_to_bv 5 7) in let s0 := YK11.getr regs (Z_to_bv 5 8) in let s1 := YK11.getr regs (Z_to_bv 5 9) in let a0 := YK11.getr regs (Z_to_bv 5 10) in let a1 := YK11.getr regs (Z_to_bv 5 11) in let a2 := YK11.getr regs (Z_to_bv 5 12) in let a3 := YK11.getr regs (Z_to_bv 5 13) in let a4 := YK11.getr regs (Z_to_bv 5 14) in let a5 := YK11.getr regs (Z_to_bv 5 15) in let a6 := YK11.getr regs (Z_to_bv 5 16) in let a7 := YK11.getr regs (Z_to_bv 5 17) in let s2 := YK11.getr regs (Z_to_bv 5 18) in let s3 := YK11.getr regs (Z_to_bv 5 19) in let s4 := YK11.getr regs (Z_to_bv 5 20) in let s5 := YK11.getr regs (Z_to_bv 5 21) in let s6 := YK11.getr regs (Z_to_bv 5 22) in let s7 := YK11.getr regs (Z_to_bv 5 23) in let s8 := YK11.getr regs (Z_to_bv 5 24) in let s9 := YK11.getr regs (Z_to_bv 5 25) in let s10 := YK11.getr regs (Z_to_bv 5 26) in let s11 := YK11.getr regs (Z_to_bv 5 27) in let t3 := YK11.getr regs (Z_to_bv 5 28) in let t4 := YK11.getr regs (Z_to_bv 5 29) in let t5 := YK11.getr regs (Z_to_bv 5 30) in let t6 := YK11.getr regs (Z_to_bv 5 31) in
    a0 = Z_to_bv 64 raw -> a2 = Z_to_bv 64 mode -> a3 = Z_to_bv 64 out ->
    0 <= raw < 2^64 -> 0 <= mode < 2^64 -> 0 <= out < 2^64 ->
    (bv_unsigned a1 = 1492 -> length bs = 1492%nat /\ bytes_at rsegs m raw bs) ->
    -2^31 <= nch < 2^31 -> -2^31 <= ns < 2^31 ->
    bytes_at rsegs m (mode + 4) (le4 (Z_to_bv 64 nch) ++ le4 (Z_to_bv 64 ns)) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_DECODE_D <= bv_unsigned sp ->
    (bv_unsigned a1 = 1492 -> off_stk sp REAC_DECODE_D raw 1492) ->
    off_stk sp REAC_DECODE_D (mode + 4) 8 ->
    (decode_ok (bv_unsigned a1) bs nch ns = true ->
    wr_at rsegs m out (3 * nch * ns) /\ out + 3 * nch * ns < 2^64 /\
    (out + 3 * nch * ns <= raw \/ raw + 1492 <= out) /\
    off_stk sp REAC_DECODE_D out (3 * nch * ns)) ->
    app_mem (bv_unsigned sp - REAC_DECODE_D) -> app_mem (bv_unsigned sp - 1) ->
    asan_cells m -> off_stk sp REAC_DECODE_D GOT_CELL_K (MIDEND + 8 - GOT_CELL_K) ->
    (bv_unsigned a1 = 1492 -> addressable m raw 1492) ->
    (inspect_wf (bv_unsigned a1) bs = true -> addressable m (mode + 4) 8) ->
    (decode_ok (bv_unsigned a1) bs nch ns = true -> addressable m out (3 * nch * ns)) ->
    (bv_unsigned a1 = 1492 -> raw <> 0) ->
    (inspect_wf (bv_unsigned a1) bs = true -> mode <> 0 /\ mode mod 4 = 0) ->
    (decode_ok (bv_unsigned a1) bs nch ns = true -> out <> 0) ->
    ExecF.rng RNG (bv_unsigned sp - REAC_DECODE_D) REAC_DECODE_D ->
    ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    (bv_unsigned a1 = 1492 ->
    ExecF.rng RNG raw 1492 /\ ExecF.rng RNG (raw / 8 + ASAN_K) ((raw + 1491) / 8 - raw / 8 + 1)) ->
    (inspect_wf (bv_unsigned a1) bs = true ->
    ExecF.rng RNG (mode + 4) 8 /\
    ExecF.rng RNG ((mode + 4) / 8 + ASAN_K) ((mode + 11) / 8 - (mode + 4) / 8 + 1)) ->
    (decode_ok (bv_unsigned a1) bs nch ns = true ->
    ExecF.rng RNG out (3 * nch * ns) /\
    ExecF.rng RNG (out / 8 + ASAN_K) ((out + 3 * nch * ns - 1) / 8 - out / 8 + 1)) ->
    (* the written caller buffer is not allocator-owned (AR across the write: AR_frame_stmt) and not in the loaded
       image (its post bytes, read through mrd, are then overlay bytes); a caller discharges both from cgif's
       AR_client_img_law for a live block *)
    (forall x, in_wr (if decode_ok (bv_unsigned a1) bs nch ns then [(out, out + 3 * nch * ns)] else []) x -> ~ aowned ly S x /\ ~ in_img x) ->
    SRr W (cfg_at REAC_DECODE regs mem md)
      (dleaf_post ly S W regs mem md (Some (if decode_ok (bv_unsigned a1) bs nch ns then ns else -1)) (if decode_ok (bv_unsigned a1) bs nch ns then [(out, out + 3 * nch * ns)] else []) (fun m2 => decode_ok (bv_unsigned a1) bs nch ns = true -> bytes_at rsegs m2 out (braid_out bs nch ns))).

Definition dec_reac_decode_cg_of_F_stmt : Prop := reac_decode_contract_F_nosh -> dec_reac_decode_cg.

Hypothesis HGLUE : leaf_cg_of_evtF_stmt.

Local Abbreviation GR r k := (YK11.getr r (Z_to_bv 5 k)).

Lemma dec_reac_decode_cg_of_F : dec_reac_decode_cg_of_F_stmt.
Proof.
  intros HF. unfold dec_reac_decode_cg.
  intros ly S W regs mem md bs raw mode out nch ns lo Hpre E0 E2 E3 Hraw Hmode Hout Hbs Hnch Hns Hfld Hstk Hlo Hoffr
    Hoffm Hdec Happ1 Happ2 Hcells Hoffg Haddr Haddm Haddo Hnz1 Hnz2 Hnz3 Rstk Rg Rc Rraw Rm Ro Hown.
  pose proof HGLUE as G. unfold leaf_cg_of_evtF_stmt, LeafCgKit.leaf_cg_of_evtF_stmt in G.
  eapply (G ly S W regs mem md REAC_DECODE REAC_DECODE_D).
  - exact Hpre.
  - unfold REAC_DECODE_D, ESTACK. lia.
  - intros x Hx. split; [|split; [|exact (Hown x Hx)]];
      revert Hx; destruct (decode_ok (bv_unsigned (GR regs 11)) bs nch ns); intros Hx; unfold in_wr in Hx;
      [ apply Exists_cons in Hx; destruct Hx as [Hx|Hx]; [cbn [fst snd] in Hx | apply Exists_nil in Hx; destruct Hx]
      | apply Exists_nil in Hx; destruct Hx
      | apply Exists_cons in Hx; destruct Hx as [Hx|Hx]; [cbn [fst snd] in Hx | apply Exists_nil in Hx; destruct Hx]
      | apply Exists_nil in Hx; destruct Hx ].
    + destruct (Hdec eq_refl) as (Hwr & Hend & Hdisj & Hoff). lia.
    + destruct (Hdec eq_refl) as (Hwr & Hend & Hdisj & Hoff).
      destruct (Ro eq_refl) as ((Ro1 & Ro2 & Ro3) & Ros).
      pose proof (Ro3 x 1%nat ltac:(lia) ltac:(lia)) as Hv.
      unfold RNG_W, LeafCgKit.RNG_W, range_avoids, woff in Hv. cbv beta in Hv.
      specialize (Hv 0%nat ltac:(lia)).
      assert (Ex : bv_unsigned (Z_to_bv 64 x) = x) by exact (wa_unsigned x ltac:(lia)).
      rewrite Ex in Hv. replace (x + Z.of_nat 0) with x in Hv by lia. exact Hv.
  - exact (HF (RNG_W W) (GR regs 1) (GR regs 2) (GR regs 3) (GR regs 4) (GR regs 5) (GR regs 6) (GR regs 7) (GR regs 8)
      (GR regs 9) (GR regs 10) (GR regs 11) (GR regs 12) (GR regs 13) (GR regs 14) (GR regs 15) (GR regs 16) (GR regs 17)
      (GR regs 18) (GR regs 19) (GR regs 20) (GR regs 21) (GR regs 22) (GR regs 23) (GR regs 24) (GR regs 25)
      (GR regs 26) (GR regs 27) (GR regs 28) (GR regs 29) (GR regs 30) (GR regs 31) fp_regs fp_csr mem
      bs raw mode out nch ns lo E0 E2 E3 Hraw Hmode Hout Hbs Hnch Hns Hfld Hstk Hlo Hoffr Hoffm Hdec Happ1 Happ2 Hcells
      Hoffg Haddr Haddm Haddo Hnz1 Hnz2 Hnz3 Rstk Rg Rc Rraw Rm Ro).
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & Ems & Hwm
      & Hstk' & Hif).
    pose proof Hstk' as (Hs1 & Hs2 & Hs3).
    assert (Hwin : forall x, spZ regs - REAC_DECODE_D <= x < spZ regs -> exists b, mrd rsegs m' (Z_to_bv 64 x) = Some b).
    { intros x Hx. unfold spZ in Hx.
      destruct (Hs3 x ltac:(lia)) as (Hwv & Hmrd). exact Hmrd. }
    assert (Hcs : forall r, acallee_saved r -> r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/
      r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (intros r Hr; unfold acallee_saved in Hr; lia).
    eexists. exists m'. split; [exact Ems|].
    revert Hif. destruct (decode_ok (bv_unsigned (GR regs 11)) bs nch ns); intros Hif;
      (split; [|split; [|split;
        [ intros r Hr; destruct (Hcs r Hr) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
          reflexivity
        | split; [intros r Er; injection Er as Er; subst r; reflexivity|] ]]]).
    + exact (proj1 Hif).
    + intros x [Hx|Hx]; [exact (Hwin x Hx)|].
      unfold in_wr in Hx. apply Exists_cons in Hx.
      destruct Hx as [Hx|Hx]; [cbn [fst snd] in Hx | apply Exists_nil in Hx; destruct Hx].
      destruct Hif as (Hmu & Hbo). destruct Hbo as (Hb1 & Hb2 & Hb3).
      assert (Hlen : length (braid_out bs nch ns) = Z.to_nat (3 * nch * ns))
        by (unfold braid_out; rewrite length_map, length_map, length_seq; reflexivity).
      assert (Hi : (Z.to_nat (x - out) < length (braid_out bs nch ns))%nat) by (rewrite Hlen; lia).
      pose proof (Hb3 _ Hi) as Hm.
      replace (out + Z.of_nat (Z.to_nat (x - out))) with x in Hm by lia.
      destruct (nth_error (braid_out bs nch ns) (Z.to_nat (x - out))) as [b|] eqn:En.
      * exists b. exact Hm.
      * apply nth_error_None in En. lia.
    + intros Ht. exact (proj2 Hif).
    + exact Hif.
    + intros x [Hx|Hx]; [exact (Hwin x Hx)|].
      unfold in_wr in Hx. apply Exists_nil in Hx. destruct Hx.
    + intros Ht. discriminate Ht.
Qed.

End LeafCg.
