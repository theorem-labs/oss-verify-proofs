(* reac_decode_plain_le_cg: decode image A's reac_decode_plain_le, its footprint contract (reac_decode_plain_le_F_nosh.v: reac_decode_plain_le_F_c.v without its shadow_rw premise) translated to cgif_file's leaf form
   (SRr world walk), as a STATEMENT (a Definition of a Prop; no proof here). Port of fuzz_decode to the released
   cgif_file_fuzzer structure (the port recipe, sec. 3). The premises of the
   target are reac_decode_plain_le_F_nosh.v's premises VERBATIM (= reac_decode_plain_le_F_c.v's without `shadow_rw m`), read at the call state (registers from regs, memory mem, footprint RNG_W W).
   The cgif side (names, verbatim copies, the facts a proof may assume, the generic translation lemma) is the shared
   kit lib/A/Prog/LeafCgKit.v; this file only re-declares the kit's Section Variables and names its definitions.
   A proof of `dec_reac_decode_plain_le_cg_of_F_stmt` goes in this file's Section, taking the kit's `_stmt` facts as Section
   Hypotheses, and applies LeafCgKit's leaf_cg_of_evtF_stmt (proof: LeafCgGlue.v). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import AsanKA reac_frame_inspect_c reac_frame_inspect_F_c reac_decode_plain_le_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import ExecF MState Frame.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import reac_decode_plain_le_F_c reac_decode_plain_le_F_nosh LeafCgKit.
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

Definition dec_reac_decode_plain_le_cg : Prop :=
  forall ly S (W : world) regs mem md (bs : list byte) (raw mode out nch ns lo : Z),
    ecall_pre ly S W regs mem md ->
    let RNG := RNG_W W in let m := mem in let F := fp_regs in let fc := fp_csr in
    let ra := YK11.getr regs (Z_to_bv 5 1) in let sp := YK11.getr regs (Z_to_bv 5 2) in let gp := YK11.getr regs (Z_to_bv 5 3) in let tp := YK11.getr regs (Z_to_bv 5 4) in let t0 := YK11.getr regs (Z_to_bv 5 5) in let t1 := YK11.getr regs (Z_to_bv 5 6) in let t2 := YK11.getr regs (Z_to_bv 5 7) in let s0 := YK11.getr regs (Z_to_bv 5 8) in let s1 := YK11.getr regs (Z_to_bv 5 9) in let a0 := YK11.getr regs (Z_to_bv 5 10) in let a1 := YK11.getr regs (Z_to_bv 5 11) in let a2 := YK11.getr regs (Z_to_bv 5 12) in let a3 := YK11.getr regs (Z_to_bv 5 13) in let a4 := YK11.getr regs (Z_to_bv 5 14) in let a5 := YK11.getr regs (Z_to_bv 5 15) in let a6 := YK11.getr regs (Z_to_bv 5 16) in let a7 := YK11.getr regs (Z_to_bv 5 17) in let s2 := YK11.getr regs (Z_to_bv 5 18) in let s3 := YK11.getr regs (Z_to_bv 5 19) in let s4 := YK11.getr regs (Z_to_bv 5 20) in let s5 := YK11.getr regs (Z_to_bv 5 21) in let s6 := YK11.getr regs (Z_to_bv 5 22) in let s7 := YK11.getr regs (Z_to_bv 5 23) in let s8 := YK11.getr regs (Z_to_bv 5 24) in let s9 := YK11.getr regs (Z_to_bv 5 25) in let s10 := YK11.getr regs (Z_to_bv 5 26) in let s11 := YK11.getr regs (Z_to_bv 5 27) in let t3 := YK11.getr regs (Z_to_bv 5 28) in let t4 := YK11.getr regs (Z_to_bv 5 29) in let t5 := YK11.getr regs (Z_to_bv 5 30) in let t6 := YK11.getr regs (Z_to_bv 5 31) in
    a0 = Z_to_bv 64 raw -> a2 = Z_to_bv 64 mode -> a3 = Z_to_bv 64 out ->
    0 <= raw < 2^64 -> 0 <= mode < 2^64 -> 0 <= out < 2^64 ->
    (bv_unsigned a1 = 1492 -> length bs = 1492%nat /\ bytes_at rsegs m raw bs) ->
    -2^31 <= nch < 2^31 -> -2^31 <= ns < 2^31 ->
    bytes_at rsegs m (mode + 4) (le4 (Z_to_bv 64 nch) ++ le4 (Z_to_bv 64 ns)) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_DECODE_PLAIN_LE_D <= bv_unsigned sp ->
    (bv_unsigned a1 = 1492 -> off_stk sp REAC_DECODE_PLAIN_LE_D raw 1492) ->
    off_stk sp REAC_DECODE_PLAIN_LE_D (mode + 4) 8 ->
    (plain_ok (bv_unsigned a1) bs nch ns = true ->
    wr_at rsegs m out (3 * nch * ns) /\ out + 3 * nch * ns < 2^64 /\
    (out + 3 * nch * ns <= raw \/ raw + 1492 <= out) /\
    off_stk sp REAC_DECODE_PLAIN_LE_D out (3 * nch * ns)) ->
    app_mem (bv_unsigned sp - REAC_DECODE_PLAIN_LE_D) -> app_mem (bv_unsigned sp - 1) ->
    asan_cells m -> off_stk sp REAC_DECODE_PLAIN_LE_D GOT_CELL_K (MIDEND + 8 - GOT_CELL_K) ->
    (bv_unsigned a1 = 1492 -> addressable m raw 1492) ->
    (inspect_wf (bv_unsigned a1) bs = true -> addressable m (mode + 4) 8) ->
    (plain_ok (bv_unsigned a1) bs nch ns = true -> addressable m out (3 * nch * ns)) ->
    (* the stack window of this frame and of reac_frame_inspect's frame under it *)
    ExecF.rng RNG (bv_unsigned sp - REAC_DECODE_PLAIN_LE_D) REAC_DECODE_PLAIN_LE_D ->
    (* the two asan_cells cells, loaded before the call and by the callee *)
    ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    (* the input buffer and its shadow bytes, read by the callee and by the copy loop *)
    (bv_unsigned a1 = 1492 -> ExecF.rng RNG raw 1492) ->
    (bv_unsigned a1 = 1492 ->
    ExecF.rng RNG (shadow_addr raw) (shadow_addr (raw + 1492 - 1) - shadow_addr raw + 1)) ->
    (* the two 4-byte fields at mode + 4 and their shadow bytes *)
    (inspect_wf (bv_unsigned a1) bs = true -> ExecF.rng RNG (mode + 4) 8) ->
    (inspect_wf (bv_unsigned a1) bs = true ->
    ExecF.rng RNG (shadow_addr (mode + 4)) (shadow_addr (mode + 4 + 8 - 1) - shadow_addr (mode + 4) + 1)) ->
    (* the output buffer and its shadow bytes *)
    (plain_ok (bv_unsigned a1) bs nch ns = true -> ExecF.rng RNG out (3 * nch * ns)) ->
    (plain_ok (bv_unsigned a1) bs nch ns = true ->
    ExecF.rng RNG (shadow_addr out) (shadow_addr (out + 3 * nch * ns - 1) - shadow_addr out + 1)) ->
    (* the written caller buffer is not allocator-owned (AR across the write: AR_frame_stmt) and not in the loaded
       image (its post bytes, read through mrd, are then overlay bytes); a caller discharges both from cgif's
       AR_client_img_law for a live block *)
    (forall x, in_wr (if plain_ok (bv_unsigned a1) bs nch ns then [(out, out + 3 * nch * ns)] else []) x -> ~ aowned ly S x /\ ~ in_img x) ->
    SRr W (cfg_at REAC_DECODE_PLAIN_LE regs mem md)
      (dleaf_post ly S W regs mem md (Some (if plain_ok (bv_unsigned a1) bs nch ns then ns else -1)) (if plain_ok (bv_unsigned a1) bs nch ns then [(out, out + 3 * nch * ns)] else []) (fun m2 => plain_ok (bv_unsigned a1) bs nch ns = true -> bytes_at rsegs m2 out (plain_out bs nch ns))).

Definition dec_reac_decode_plain_le_cg_of_F_stmt : Prop := reac_decode_plain_le_contract_F_nosh -> dec_reac_decode_plain_le_cg.

Hypothesis HGLUE : leaf_cg_of_evtF_stmt.

Lemma dec_reac_decode_plain_le_cg_of_F : dec_reac_decode_plain_le_cg_of_F_stmt.
Proof.
  unfold dec_reac_decode_plain_le_cg_of_F_stmt, dec_reac_decode_plain_le_cg.
  intros HF. cbv zeta.
  intros ly S W regs mem md bs raw mode out nch ns lo Hpre Ha0 Ha2 Ha3 Hraw Hmode Hout Hbs Hnch Hns Hfld Hstk Hlo
    Hoffr Hoffm Hpo Happ1 Happ2 Hcells Hoffg Haddr Haddm Haddo Hrs Hrg Hrc Hrr Hrrs Hrm Hrms Hro Hros Hown.
  pose proof (HF (RNG_W W)
    (YK11.getr regs (Z_to_bv 5 1)) (YK11.getr regs (Z_to_bv 5 2)) (YK11.getr regs (Z_to_bv 5 3))
    (YK11.getr regs (Z_to_bv 5 4)) (YK11.getr regs (Z_to_bv 5 5)) (YK11.getr regs (Z_to_bv 5 6))
    (YK11.getr regs (Z_to_bv 5 7)) (YK11.getr regs (Z_to_bv 5 8)) (YK11.getr regs (Z_to_bv 5 9))
    (YK11.getr regs (Z_to_bv 5 10)) (YK11.getr regs (Z_to_bv 5 11)) (YK11.getr regs (Z_to_bv 5 12))
    (YK11.getr regs (Z_to_bv 5 13)) (YK11.getr regs (Z_to_bv 5 14)) (YK11.getr regs (Z_to_bv 5 15))
    (YK11.getr regs (Z_to_bv 5 16)) (YK11.getr regs (Z_to_bv 5 17)) (YK11.getr regs (Z_to_bv 5 18))
    (YK11.getr regs (Z_to_bv 5 19)) (YK11.getr regs (Z_to_bv 5 20)) (YK11.getr regs (Z_to_bv 5 21))
    (YK11.getr regs (Z_to_bv 5 22)) (YK11.getr regs (Z_to_bv 5 23)) (YK11.getr regs (Z_to_bv 5 24))
    (YK11.getr regs (Z_to_bv 5 25)) (YK11.getr regs (Z_to_bv 5 26)) (YK11.getr regs (Z_to_bv 5 27))
    (YK11.getr regs (Z_to_bv 5 28)) (YK11.getr regs (Z_to_bv 5 29)) (YK11.getr regs (Z_to_bv 5 30))
    (YK11.getr regs (Z_to_bv 5 31)) (@fp_regs fx) (@fp_csr fx) mem bs raw mode out nch ns lo
    Ha0 Ha2 Ha3 Hraw Hmode Hout Hbs Hnch Hns Hfld Hstk Hlo Hoffr Hoffm Hpo Happ1 Happ2 Hcells Hoffg
    Haddr Haddm Haddo Hrs Hrg Hrc Hrr Hrrs Hrm Hrms Hro Hros) as HE.
  eapply (HGLUE ly S W regs mem md REAC_DECODE_PLAIN_LE REAC_DECODE_PLAIN_LE_D _ _ _ _ Hpre).
  - unfold REAC_DECODE_PLAIN_LE_D, ESTACK. lia.
  - intros x Hx. pose proof (Hown x Hx) as (Hnown & Hnimg).
    revert Hx. destruct (plain_ok (bv_unsigned (YK11.getr regs (Z_to_bv 5 11))) bs nch ns) eqn:Hp; intros Hx;
      unfold in_wr in Hx; apply Exists_exists in Hx as (p & Hin & Hpx).
    + destruct Hin as [Hin|Hin]; [subst p | destruct Hin]. cbn [fst snd] in Hpx.
      destruct (Hpo eq_refl) as (Hwr & Hend & Hdisj & Hoffo).
      destruct (Hro eq_refl) as (Hro0 & Hro1 & Hrof).
      pose proof (Hrof x 1%nat ltac:(lia) ltac:(lia) 0%nat ltac:(lia)) as Hvis.
      unfold woff in Hvis.
      replace (bv_unsigned (Z_to_bv 64 x) + Z.of_nat 0) with x in Hvis by (rewrite unsigned_lit by lia; lia).
      split; [lia|]. split; [exact Hvis|]. split; [exact Hnown | exact Hnimg].
    + destruct Hin.
  - exact HE.
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & Hms & Hwm
      & Hstk' & Hpost).
    destruct Hstk' as (Hlo' & Hhi' & Hstkf).
    assert (Hwin : forall x, spZ regs - REAC_DECODE_PLAIN_LE_D <= x < spZ regs ->
      exists b, mrd rsegs m' (Z_to_bv 64 x) = Some b).
    { intros x Hx. unfold spZ in Hx. destruct (Hstkf x ltac:(lia)) as (Hwv & Hb). exact Hb. }
    revert Hms Hpost. destruct (plain_ok (bv_unsigned (YK11.getr regs (Z_to_bv 5 11))) bs nch ns) eqn:Hp;
      intros Hms Hpost.
    + destruct Hpost as (Hmu & Hby).
      do 2 eexists. split; [exact Hms|]. split; [exact Hmu|]. split.
      { intros x [Hx|Hx]; [exact (Hwin x Hx)|].
        unfold in_wr in Hx. apply Exists_exists in Hx as (p & Hin & Hpx).
        destruct Hin as [Hin|Hin]; [subst p | destruct Hin]. cbn [fst snd] in Hpx.
        destruct Hby as (Hby0 & Hbyl & Hbyf).
        assert (Hlen : length (plain_out bs nch ns) = Z.to_nat (3 * nch * ns))
          by (unfold plain_out; rewrite !length_map, length_seq; reflexivity).
        pose proof (Hbyf (Z.to_nat (x - out)) ltac:(rewrite Hlen; lia)) as Hbx.
        assert (Hsome : nth_error (plain_out bs nch ns) (Z.to_nat (x - out)) <> None)
          by (apply nth_error_Some; rewrite Hlen; lia).
        replace (out + Z.of_nat (Z.to_nat (x - out))) with x in Hbx by lia.
        revert Hbx Hsome. destruct (nth_error (plain_out bs nch ns) (Z.to_nat (x - out))) as [b|];
          intros Hbx Hsome.
        - exists b. exact Hbx.
        - exfalso. exact (Hsome eq_refl). }
      split.
      { intros r Hr. unfold acallee_saved in Hr.
        destruct Hr as [Hr|[Hr|[Hr|[Hr|[Hr|Hr]]]]].
        1-5: subst r; reflexivity.
        assert (Hr' : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
          by lia.
        destruct Hr' as [Hr'|[Hr'|[Hr'|[Hr'|[Hr'|[Hr'|[Hr'|[Hr'|[Hr'|Hr']]]]]]]]]; subst r; reflexivity. }
      split; [intros r Hr; injection Hr as Hr; subst r; reflexivity|].
      intros Hpt. exact Hby.
    + do 2 eexists. split; [exact Hms|]. split; [exact Hpost|]. split.
      { intros x [Hx|Hx]; [exact (Hwin x Hx)|].
        unfold in_wr in Hx. apply Exists_exists in Hx as (p & Hin & Hpx). destruct Hin. }
      split.
      { intros r Hr. unfold acallee_saved in Hr.
        destruct Hr as [Hr|[Hr|[Hr|[Hr|[Hr|Hr]]]]].
        1-5: subst r; reflexivity.
        assert (Hr' : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
          by lia.
        destruct Hr' as [Hr'|[Hr'|[Hr'|[Hr'|[Hr'|[Hr'|[Hr'|[Hr'|[Hr'|Hr']]]]]]]]]; subst r; reflexivity. }
      split; [intros r Hr; injection Hr as Hr; subst r; reflexivity|].
      intros Hpt. discriminate Hpt.
Qed.

End LeafCg.
