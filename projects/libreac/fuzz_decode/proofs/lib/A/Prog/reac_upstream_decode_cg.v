(* reac_upstream_decode_cg: decode image A's reac_upstream_decode, its footprint contract (reac_upstream_decode_F_c.v) translated to cgif_file's leaf form
   (SRr world walk), as a STATEMENT (a Definition of a Prop; no proof here). Port of fuzz_decode to the released
   cgif_file_fuzzer structure (the port recipe, sec. 3). The premises of the
   target are reac_upstream_decode_F_c.v's premises VERBATIM, read at the call state (registers from regs, memory mem, footprint RNG_W W).
   The cgif side (names, verbatim copies, the facts a proof may assume, the generic translation lemma) is the shared
   kit lib/A/Prog/LeafCgKit.v; this file only re-declares the kit's Section Variables and names its definitions.
   A proof of `dec_reac_upstream_decode_cg_of_F_stmt` goes in this file's Section, taking the kit's `_stmt` facts as Section
   Hypotheses, and applies LeafCgKit's leaf_cg_of_evtF_stmt (proof: LeafCgGlue.v). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import AsanKA reac_frame_inspect_c reac_decode_c reac_upstream_decode_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import ExecF MState Frame.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import reac_upstream_decode_F_c LeafCgKit.
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

Definition dec_reac_upstream_decode_cg : Prop :=
  forall ly S (W : world) regs mem md (bs : list byte) (raw out lo : Z),
    ecall_pre ly S W regs mem md ->
    let RNG := RNG_W W in let m := mem in let F := fp_regs in let fc := fp_csr in
    let ra := YK11.getr regs (Z_to_bv 5 1) in let sp := YK11.getr regs (Z_to_bv 5 2) in let gp := YK11.getr regs (Z_to_bv 5 3) in let tp := YK11.getr regs (Z_to_bv 5 4) in let t0 := YK11.getr regs (Z_to_bv 5 5) in let t1 := YK11.getr regs (Z_to_bv 5 6) in let t2 := YK11.getr regs (Z_to_bv 5 7) in let s0 := YK11.getr regs (Z_to_bv 5 8) in let s1 := YK11.getr regs (Z_to_bv 5 9) in let a0 := YK11.getr regs (Z_to_bv 5 10) in let a1 := YK11.getr regs (Z_to_bv 5 11) in let a2 := YK11.getr regs (Z_to_bv 5 12) in let a3 := YK11.getr regs (Z_to_bv 5 13) in let a4 := YK11.getr regs (Z_to_bv 5 14) in let a5 := YK11.getr regs (Z_to_bv 5 15) in let a6 := YK11.getr regs (Z_to_bv 5 16) in let a7 := YK11.getr regs (Z_to_bv 5 17) in let s2 := YK11.getr regs (Z_to_bv 5 18) in let s3 := YK11.getr regs (Z_to_bv 5 19) in let s4 := YK11.getr regs (Z_to_bv 5 20) in let s5 := YK11.getr regs (Z_to_bv 5 21) in let s6 := YK11.getr regs (Z_to_bv 5 22) in let s7 := YK11.getr regs (Z_to_bv 5 23) in let s8 := YK11.getr regs (Z_to_bv 5 24) in let s9 := YK11.getr regs (Z_to_bv 5 25) in let s10 := YK11.getr regs (Z_to_bv 5 26) in let s11 := YK11.getr regs (Z_to_bv 5 27) in let t3 := YK11.getr regs (Z_to_bv 5 28) in let t4 := YK11.getr regs (Z_to_bv 5 29) in let t5 := YK11.getr regs (Z_to_bv 5 30) in let t6 := YK11.getr regs (Z_to_bv 5 31) in
    a0 = Z_to_bv 64 raw -> a2 = Z_to_bv 64 out ->
    0 <= raw < 2^64 -> 0 <= out < 2^64 -> bv_unsigned a1 < 2^32 ->
    bytes_at rsegs m DIV36_MAGIC_AT (le8 (Z_to_bv 64 DIV36_MAGIC)) ->
    (raw <> 0 -> out <> 0 -> 0 <= up_nch (bv_unsigned a1) ->
    length bs = Z.to_nat (bv_unsigned a1) /\ bytes_at rsegs m raw bs) ->
    (up_ok raw out (bv_unsigned a1) bs = true ->
    wr_at rsegs m out (36 * up_nch (bv_unsigned a1)) /\ out + 36 * up_nch (bv_unsigned a1) < 2^64 /\
    (out + 36 * up_nch (bv_unsigned a1) <= raw \/ raw + bv_unsigned a1 <= out)) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_UPSTREAM_DECODE_D <= bv_unsigned sp ->
    (raw <> 0 -> out <> 0 -> 0 <= up_nch (bv_unsigned a1) ->
    off_stk sp REAC_UPSTREAM_DECODE_D raw (bv_unsigned a1)) ->
    (up_ok raw out (bv_unsigned a1) bs = true ->
    off_stk sp REAC_UPSTREAM_DECODE_D out (36 * up_nch (bv_unsigned a1))) ->
    off_stk sp REAC_UPSTREAM_DECODE_D DIV36_MAGIC_AT 8 ->
    app_mem (bv_unsigned sp - REAC_UPSTREAM_DECODE_D) -> app_mem (bv_unsigned sp - 1) ->
    asan_cells m ->
    off_stk sp REAC_UPSTREAM_DECODE_D GOT_CELL_K (MIDEND + 8 - GOT_CELL_K) ->
    (raw <> 0 -> out <> 0 -> 0 <= up_nch (bv_unsigned a1) -> addressable m raw (bv_unsigned a1)) ->
    (up_ok raw out (bv_unsigned a1) bs = true -> addressable m out (36 * up_nch (bv_unsigned a1))) ->
    ExecF.rng RNG (bv_unsigned sp - REAC_UPSTREAM_DECODE_D) REAC_UPSTREAM_DECODE_D ->
    ExecF.rng RNG DIV36_MAGIC_AT 8 ->
    ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    (raw <> 0 -> out <> 0 -> 0 <= up_nch (bv_unsigned a1) -> ExecF.rng RNG raw (bv_unsigned a1)) ->
    (raw <> 0 -> out <> 0 -> 0 <= up_nch (bv_unsigned a1) ->
    ExecF.rng RNG (raw / 8 + ASAN_K) ((raw + bv_unsigned a1 - 1) / 8 - raw / 8 + 1)) ->
    (up_ok raw out (bv_unsigned a1) bs = true -> ExecF.rng RNG out (36 * up_nch (bv_unsigned a1))) ->
    (up_ok raw out (bv_unsigned a1) bs = true ->
    ExecF.rng RNG (out / 8 + ASAN_K) ((out + 36 * up_nch (bv_unsigned a1) - 1) / 8 - out / 8 + 1)) ->
    (* the written caller buffer is not allocator-owned (AR across the write: AR_frame_stmt) and not in the loaded
       image (its post bytes, read through mrd, are then overlay bytes); a caller discharges both from cgif's
       AR_client_img_law for a live block *)
    (forall x, in_wr (if up_ok raw out (bv_unsigned a1) bs then [(out, out + 36 * up_nch (bv_unsigned a1))] else []) x -> ~ aowned ly S x /\ ~ in_img x) ->
    SRr W (cfg_at REAC_UPSTREAM_DECODE regs mem md)
      (dleaf_post ly S W regs mem md (Some (if up_ok raw out (bv_unsigned a1) bs then 12 else -1)) (if up_ok raw out (bv_unsigned a1) bs then [(out, out + 36 * up_nch (bv_unsigned a1))] else []) (fun m2 => up_ok raw out (bv_unsigned a1) bs = true -> bytes_at rsegs m2 out (braid_out bs (up_nch (bv_unsigned a1)) 12))).

Definition dec_reac_upstream_decode_cg_of_F_stmt : Prop := reac_upstream_decode_contract_F -> dec_reac_upstream_decode_cg.

Hypothesis HGLUE : leaf_cg_of_evtF_stmt.
(* The footprint run of reac_upstream_decode_F_c.v, read as cgif's leaf form through HGLUE (the kit's
   leaf_cg_of_evtF_stmt), at PC = REAC_UPSTREAM_DECODE and K = REAC_UPSTREAM_DECODE_D. The goals in HGLUE's order:
   ecall_pre; the frame bound; the written range's facts; the run (the contract's premises, in order); then the
   post (the return registers, munch, presence of the frame / written bytes, the callee-saved registers, a0, the
   output bytes). *)
Lemma dec_reac_upstream_decode_cg_of_F : dec_reac_upstream_decode_cg_of_F_stmt.
Proof.
  intros HF. unfold dec_reac_upstream_decode_cg.
  intros ly S W regs mem md bs raw out lo Hpre. cbv zeta.
  intros Ha0 Ha2 Hraw Hout Ha1 Hmag Hin Hwr Hstk Hlo Hoffr Hoffo Hoffm Happ1 Happ2 Hcells Hoffg Haddr Haddo
    Hr1 Hr2 Hr3 Hr4 Hr5 Hr6 Hr7 Hr8 Hnew.
  (* the run: the contract at the call state's registers and memory, RNG := RNG_W W *)
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
    (YK11.getr regs (Z_to_bv 5 31))
    fp_regs fp_csr mem bs raw out lo
    Ha0 Ha2 Hraw Hout Ha1 Hmag Hin Hwr Hstk Hlo Hoffr Hoffo Hoffm Happ1 Happ2 Hcells Hoffg Haddr Haddo
    Hr1 Hr2 Hr3 Hr4 Hr5 Hr6 Hr7 Hr8) as HRUN.
  (* the return bank keeps the caller's callee-saved registers (x2 x3 x4 x8 x9 x18..x27) *)
  assert (HKEEP : forall v5 v6 v7 v10 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 : word,
    aregs_preserved regs (mkR (YK11.getr regs (Z_to_bv 5 1)) (YK11.getr regs (Z_to_bv 5 2))
      (YK11.getr regs (Z_to_bv 5 3)) (YK11.getr regs (Z_to_bv 5 4)) v5 v6 v7
      (YK11.getr regs (Z_to_bv 5 8)) (YK11.getr regs (Z_to_bv 5 9)) v10 v11 v12 v13 v14 v15 v16 v17
      (YK11.getr regs (Z_to_bv 5 18)) (YK11.getr regs (Z_to_bv 5 19)) (YK11.getr regs (Z_to_bv 5 20))
      (YK11.getr regs (Z_to_bv 5 21)) (YK11.getr regs (Z_to_bv 5 22)) (YK11.getr regs (Z_to_bv 5 23))
      (YK11.getr regs (Z_to_bv 5 24)) (YK11.getr regs (Z_to_bv 5 25)) (YK11.getr regs (Z_to_bv 5 26))
      (YK11.getr regs (Z_to_bv 5 27)) v28 v29 v30 v31)).
  { intros v5 v6 v7 v10 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 r Hr. unfold acallee_saved in Hr.
    assert (Hrc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
      r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    repeat (destruct Hrc as [Hrc|Hrc]; [subst r; reflexivity|]). subst r. reflexivity. }
  (* destruct rewrites the up_ok test in the goal and in every premise (Hwr, Hr7, Hnew, HRUN's post) *)
  destruct (up_ok raw out (bv_unsigned (YK11.getr regs (Z_to_bv 5 11))) bs) eqn:Eok.
  - (* up_ok: the run writes [out, out + 36 * nch) and returns 12 *)
    destruct (Hwr eq_refl) as (Hwr_at & Hwr_hi & Hwr_dis).
    destruct (Hr7 eq_refl) as (Hr7_lo & Hr7_hi & Hr7_in).
    eapply (HGLUE ly S W regs mem md REAC_UPSTREAM_DECODE REAC_UPSTREAM_DECODE_D _
      [(out, out + 36 * up_nch (bv_unsigned (YK11.getr regs (Z_to_bv 5 11))))] (Some 12) _).
    + exact Hpre.
    + unfold REAC_UPSTREAM_DECODE_D, ESTACK. lia.
    + intros x Hx. pose proof Hx as Hx_wr. unfold in_wr in Hx. apply Exists_cons in Hx.
      destruct Hx as [Hx|Hx].
      * cbn [fst snd] in Hx. destruct (Hnew x Hx_wr) as (Hno_own & Hno_img).
        split; [lia|]. split; [|split; [exact Hno_own | exact Hno_img]].
        (* the byte at x is visible: RNG_W W holds the one-byte range at x (the output's ExecF.rng, Hr7) *)
        pose proof (Hr7_in x 1%nat ltac:(lia) ltac:(lia) 0%nat ltac:(lia)) as Hvis.
        unfold woff in Hvis. change (Z.of_nat 0) with 0 in Hvis.
        rewrite Z.add_0_r, Z_to_bv_bv_unsigned in Hvis. exact Hvis.
      * apply Exists_nil in Hx. destruct Hx.
    + exact HRUN.
    + intros ms' Hms'.
      destruct Hms' as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
        Hms & Hmono & Hstk' & Hpost).
      destruct Hpost as (Hmunch & Hbytes).
      subst ms'. eexists. exists m'.
      split; [reflexivity|].
      split; [exact Hmunch|].
      split.
      { intros x Hx. destruct Hx as [Hx|Hx].
        - (* the frame window: the post's stk *)
          destruct Hstk' as (Hstk_lo & Hstk_hi & Hstk_b). unfold spZ in Hx.
          destruct (Hstk_b x ltac:(lia)) as (Hwv & Hb). exact Hb.
        - (* the written buffer: the post's bytes_at *)
          unfold in_wr in Hx. apply Exists_cons in Hx. destruct Hx as [Hx|Hx].
          + cbn [fst snd] in Hx. destruct Hbytes as (Hb_lo & Hb_hi & Hb_at).
            assert (Hlen : length (braid_out bs (up_nch (bv_unsigned (YK11.getr regs (Z_to_bv 5 11)))) 12) =
              Z.to_nat (3 * up_nch (bv_unsigned (YK11.getr regs (Z_to_bv 5 11))) * 12))
              by (unfold braid_out; rewrite !length_map, length_seq; reflexivity).
            assert (Hix : (Z.to_nat (x - out) <
              length (braid_out bs (up_nch (bv_unsigned (YK11.getr regs (Z_to_bv 5 11)))) 12))%nat)
              by (rewrite Hlen; lia).
            pose proof (Hb_at (Z.to_nat (x - out)) Hix) as Hbx.
            rewrite Z2Nat.id in Hbx by lia. replace (out + (x - out)) with x in Hbx by lia.
            apply nth_error_Some in Hix.
            destruct (nth_error (braid_out bs (up_nch (bv_unsigned (YK11.getr regs (Z_to_bv 5 11)))) 12)
              (Z.to_nat (x - out))) as [b|] eqn:Enth.
            * exists b. exact Hbx.
            * exfalso. exact (Hix eq_refl).
          + apply Exists_nil in Hx. destruct Hx. }
      split; [apply HKEEP|].
      split.
      { intros r Hr. injection Hr as Hr. subst r. reflexivity. }
      intros Htrue. exact Hbytes.
  - (* not up_ok: nothing written, a0 = -1 *)
    eapply (HGLUE ly S W regs mem md REAC_UPSTREAM_DECODE REAC_UPSTREAM_DECODE_D _ [] (Some (-1)) _).
    + exact Hpre.
    + unfold REAC_UPSTREAM_DECODE_D, ESTACK. lia.
    + intros x Hx. unfold in_wr in Hx. apply Exists_nil in Hx. destruct Hx.
    + exact HRUN.
    + intros ms' Hms'.
      destruct Hms' as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
        Hms & Hmono & Hstk' & Hpost).
      subst ms'. eexists. exists m'.
      split; [reflexivity|].
      split; [exact Hpost|].
      split.
      { intros x Hx. destruct Hx as [Hx|Hx].
        - destruct Hstk' as (Hstk_lo & Hstk_hi & Hstk_b). unfold spZ in Hx.
          destruct (Hstk_b x ltac:(lia)) as (Hwv & Hb). exact Hb.
        - unfold in_wr in Hx. apply Exists_nil in Hx. destruct Hx. }
      split; [apply HKEEP|].
      split.
      { intros r Hr. injection Hr as Hr. subst r. reflexivity. }
      intros Hfalse. discriminate Hfalse.
Qed.

End LeafCg.
