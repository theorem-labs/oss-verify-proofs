(* reac_braid_encode_cg: decode image B's reac_braid_encode, its footprint contract (reac_braid_encode_F_nosh.v) translated to cgif_file's leaf form
   (SRr world walk), as a STATEMENT (a Definition of a Prop; no proof here). Port of fuzz_decode to the released
   cgif_file_fuzzer structure (the port recipe, sec. 3). The premises of the
   target are reac_braid_encode_F_nosh.v's premises VERBATIM, read at the call state (registers from regs, memory mem, footprint RNG_W W),
   with the read-only read set named REAC_BRAID_ENCODE_RO_RD.
   The cgif side (names, verbatim copies, the facts a proof may assume, the generic translation lemma) is the shared
   kit lib/B/Prog/LeafCgKit.v; this file only re-declares the kit's Section Variables and names its definitions.
   A proof of `dec_reac_braid_encode_cg_of_F_stmt` goes in this file's Section, taking the kit's `_stmt` facts as Section
   Hypotheses, and applies LeafCgKit's leaf_cg_of_evtF_fx_stmt (proof: LeafCgGlue.v). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame FP.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require Import FloatExact RcBraid.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import crt_braid_need.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import ExecF MState Frame.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import reac_braid_encode_F_nosh LeafCgKit.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require LeafCgGlue.
Open Scope Z_scope.

(* The read-only read set of reac_braid_encode in image B, as (base, size) entries: the 4 bytes of the clamp
   constant FCLAMP_HI (0x4afffffe) in the read-only data, which the `flw` at 0x81d78 loads PC-relative. It is the
   function's only load from a read-only segment (its GOT word 0x992e8 is in a writable PT_LOAD). *)
Definition REAC_BRAID_ENCODE_RO_RD : list (Z * Z) := [(0x20dcc, 4)].

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

Definition dec_reac_braid_encode_cg : Prop :=
  forall ly S (W : world) regs mem md (a N P ns : Z) (Q : Z -> Z) (V K : Z -> Z -> Z),
    ecall_pre ly S W regs mem md ->
    let RNG := RNG_W W in let m := mem in let F := fp_regs in let fc := fp_csr in
    let ra := YK11.getr regs (Z_to_bv 5 1) in let sp := YK11.getr regs (Z_to_bv 5 2) in let gp := YK11.getr regs (Z_to_bv 5 3) in let tp := YK11.getr regs (Z_to_bv 5 4) in let t0 := YK11.getr regs (Z_to_bv 5 5) in let t1 := YK11.getr regs (Z_to_bv 5 6) in let t2 := YK11.getr regs (Z_to_bv 5 7) in let s0 := YK11.getr regs (Z_to_bv 5 8) in let s1 := YK11.getr regs (Z_to_bv 5 9) in let a0 := YK11.getr regs (Z_to_bv 5 10) in let a1 := YK11.getr regs (Z_to_bv 5 11) in let a2 := YK11.getr regs (Z_to_bv 5 12) in let a3 := YK11.getr regs (Z_to_bv 5 13) in let a4 := YK11.getr regs (Z_to_bv 5 14) in let a5 := YK11.getr regs (Z_to_bv 5 15) in let a6 := YK11.getr regs (Z_to_bv 5 16) in let a7 := YK11.getr regs (Z_to_bv 5 17) in let s2 := YK11.getr regs (Z_to_bv 5 18) in let s3 := YK11.getr regs (Z_to_bv 5 19) in let s4 := YK11.getr regs (Z_to_bv 5 20) in let s5 := YK11.getr regs (Z_to_bv 5 21) in let s6 := YK11.getr regs (Z_to_bv 5 22) in let s7 := YK11.getr regs (Z_to_bv 5 23) in let s8 := YK11.getr regs (Z_to_bv 5 24) in let s9 := YK11.getr regs (Z_to_bv 5 25) in let s10 := YK11.getr regs (Z_to_bv 5 26) in let s11 := YK11.getr regs (Z_to_bv 5 27) in let t3 := YK11.getr regs (Z_to_bv 5 28) in let t4 := YK11.getr regs (Z_to_bv 5 29) in let t5 := YK11.getr regs (Z_to_bv 5 30) in let t6 := YK11.getr regs (Z_to_bv 5 31) in
    a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 N -> a2 = Z_to_bv 64 P -> a3 = Z_to_bv 64 N -> a4 = Z_to_bv 64 ns ->
    2 <= N <= 127 -> N mod 2 = 0 -> 1 <= ns <= 12 ->
    frm0 fc ->
    (forall a : word, (exists r, In r REAC_BRAID_ENCODE_RO_RD /\ fst r <= bv_unsigned a < fst r + snd r) ->
    mrd rsegs m a = seg_rom rsegs a) ->
    (forall x, (exists r, In r REAC_BRAID_ENCODE_RO_RD /\ fst r <= x < fst r + snd r) ->
    outside [(bv_unsigned sp - REAC_BRAID_ENCODE_FRAME, bv_unsigned sp)] x) ->
    stk rsegs m (bv_unsigned sp - REAC_BRAID_ENCODE_FRAME) (bv_unsigned sp) ->
    0 < a -> a + 3 * N * ns <= 2^64 -> wr_at rsegs m a (3 * N * ns) ->
    0 < P -> P mod 8 = 0 -> P + 8 * N <= 2^64 ->
    (forall ch, 0 <= ch < N -> bytes_at rsegs m (P + 8 * ch) (le8 (Z_to_bv 64 (Q ch)))) ->
    (forall ch, 0 <= ch < N -> 0 < Q ch /\ Q ch mod 4 = 0 /\ Q ch + 4 * ns <= 2^64) ->
    (forall s ch, 0 <= s < ns -> 0 <= ch < N ->
    bytes_at rsegs m (Q ch + 4 * s) (le4 (Z_to_bv 64 (V s ch))) /\ rb_sample (V s ch) (K s ch)) ->
    (a + 3 * N * ns <= P \/ P + 8 * N <= a) ->
    (forall ch, 0 <= ch < N -> a + 3 * N * ns <= Q ch \/ Q ch + 4 * ns <= a) ->
    (a + 3 * N * ns <= bv_unsigned sp - REAC_BRAID_ENCODE_FRAME \/ bv_unsigned sp <= a) ->
    (P + 8 * N <= bv_unsigned sp - REAC_BRAID_ENCODE_FRAME \/ bv_unsigned sp <= P) ->
    (forall ch, 0 <= ch < N ->
    Q ch + 4 * ns <= bv_unsigned sp - REAC_BRAID_ENCODE_FRAME \/ bv_unsigned sp <= Q ch) ->
    asan_cells m ->
    addressable m a (3 * N * ns) -> addressable m P (8 * N) ->
    (forall ch, 0 <= ch < N -> addressable m (Q ch) (4 * ns)) ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
    outside [(bv_unsigned sp - REAC_BRAID_ENCODE_FRAME, bv_unsigned sp); (a, a + 3 * N * ns)] x) ->
    rng RNG GOT_CELL_K 8 -> rng RNG CELL_K 8 -> rng RNG 0x20dcc 4 ->
    rng RNG (bv_unsigned sp - REAC_BRAID_ENCODE_FRAME) REAC_BRAID_ENCODE_FRAME ->
    rng RNG a (3 * N * ns) ->
    rng RNG (shadow_addr a / 8 * 8)
    (shadow_addr (a + 3 * N * ns - 1) / 8 * 8 + 8 - shadow_addr a / 8 * 8) ->
    rng RNG P (8 * N) ->
    rng RNG (shadow_addr P / 8 * 8) (shadow_addr (P + 8 * N - 1) / 8 * 8 + 8 - shadow_addr P / 8 * 8) ->
    (forall ch, 0 <= ch < N -> rng RNG (Q ch) (4 * ns)) ->
    (forall ch, 0 <= ch < N ->
    rng RNG (shadow_addr (Q ch) / 8 * 8)
    (shadow_addr (Q ch + 4 * ns - 1) / 8 * 8 + 8 - shadow_addr (Q ch) / 8 * 8)) ->
    (* the written caller buffer is not allocator-owned (AR across the write: AR_frame_stmt) and not in the loaded
       image (its post bytes, read through mrd, are then overlay bytes); a caller discharges both from cgif's
       AR_client_img_law for a live block *)
    (forall x, in_wr [(a, a + 3 * N * ns)] x -> ~ aowned ly S x /\ ~ in_img x) ->
    SRr W (cfg_at REAC_BRAID_ENCODE regs mem md)
      (dleaf_post_fx ly S W regs mem md [(a, a + 3 * N * ns)]
        (fun m2 => forall x : word, outside [(bv_unsigned sp - REAC_BRAID_ENCODE_FRAME, bv_unsigned sp)] (bv_unsigned x) ->
           m2 x = rb_enc mem (rb_rows a N K (Z.to_nat ns)) x)).

Definition dec_reac_braid_encode_cg_of_F_stmt : Prop := reac_braid_encode_contract_F_nosh -> dec_reac_braid_encode_cg.

Hypothesis HGLUE : leaf_cg_of_evtF_fx_stmt.

(* Proof outline of the brief (leaf-proofs-brief.md, steps 1-3): the run is reac_braid_encode_contract_F_nosh at
   RNG := RNG_W W, read at the call state; LeafCgKit's leaf_cg_of_evtF_fx_stmt turns it into the cgif leaf form with
   K = REAC_BRAID_ENCODE_FRAME, WR = [(a, a + 3 * N * ns)] and X = the rb_enc post. The post destruct follows
   reac_braid_encode_F_nosh.v's evtF post: the caller-saved results, F', m', then munch /
   wmono / stk / the rb_enc bytes. The WR visibility follows reac_decode_cg.v's (rng at the byte, RNG_W);
   the WR presence reads wr_at through wmono, then wview at a byte outside the image (~ in_img) is the overlay byte. *)
Lemma dec_reac_braid_encode_cg_of_F : dec_reac_braid_encode_cg_of_F_stmt.
Proof.
  (* no unfold: it would zeta-reduce the statement's lets; intros head-reduces dec_reac_braid_encode_cg and keeps them
     as local definitions named as in reac_braid_encode_contract_F_nosh *)
  intros HF ly S W regs mem md a N P ns Q V K HPRE
    RNG m F fc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    E0 E1 E2 E3 E4 HN HNe Hns FRM HRO HROF ST Ha HaE HW HP0 HP8m HP8 HPb HQ HV HD1 HD2 HD3 HD4 HD5
    HCE HAa HAP HAQ HWO R1g R1c R1f R2 R3 R4 R5 R6 R7 R8 HBUF.
  (* the run: reac_braid_encode_contract_F_nosh, its premises in order, at the call state's registers *)
  pose proof (HF RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m a N P ns Q V K E0 E1 E2 E3 E4 HN HNe Hns FRM HRO HROF ST Ha HaE HW HP0 HP8m HP8 HPb HQ HV HD1 HD2 HD3 HD4 HD5
    HCE HAa HAP HAQ HWO R1g R1c R1f R2 R3 R4 R5 R6 R7 R8) as RUN.
  assert (HinWR : forall x, in_wr [(a, a + 3 * N * ns)] x -> a <= x < a + 3 * N * ns).
  { intros x Hx. unfold in_wr in Hx. apply Exists_cons in Hx.
    destruct Hx as [Hx|Hx]; [exact Hx | apply Exists_nil in Hx; destruct Hx]. }
  refine (HGLUE ly S W regs mem md REAC_BRAID_ENCODE REAC_BRAID_ENCODE_FRAME _ [(a, a + 3 * N * ns)]
    (fun m2 => forall x : word, outside [(bv_unsigned sp - REAC_BRAID_ENCODE_FRAME, bv_unsigned sp)] (bv_unsigned x) ->
       m2 x = rb_enc mem (rb_rows a N K (Z.to_nat ns)) x)
    HPRE _ _ RUN _).
  - (* the window bound *)
    unfold REAC_BRAID_ENCODE_FRAME, ESTACK. lia.
  - (* the written range: in range, visible (rng at the byte, as reac_decode_cg.v), unowned and outside the image *)
    intros x Hx. pose proof (HinWR x Hx) as Hxr.
    split; [lia|]. split; [|exact (HBUF x Hx)].
    destruct R3 as (R31 & R32 & R33).
    pose proof (R33 x 1%nat ltac:(lia) ltac:(lia)) as Hv.
    unfold RNG, RNG_W, LeafCgKit.RNG_W, range_avoids, woff in Hv.
    specialize (Hv 0%nat ltac:(lia)).
    assert (Ex : bv_unsigned (Z_to_bv 64 x) = x) by exact (wa_unsigned x ltac:(lia)).
    rewrite Ex in Hv. replace (x + Z.of_nat 0) with x in Hv by lia. exact Hv.
  - (* the post *)
    intros ms' (t0' & t1' & t2' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & m'
                & -> & HF' & MU & WM & STK' & ENC).
    assert (Hcs : forall r, acallee_saved r -> r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/
      r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
      by (intros r Hr; unfold acallee_saved in Hr; lia).
    eexists _, F', m'. split; [reflexivity|].
    split; [exact HF'|].
    split; [exact MU|].
    split.
    + intros x [Hx | Hx].
      * (* the frame: stk after the run *)
        change (spZ regs) with (bv_unsigned sp) in Hx.
        destruct STK' as (STK1 & STK2 & STK3).
        destruct (STK3 x ltac:(lia)) as (Hwv & Hmrd). exact Hmrd.
      * (* the written range: writable before (wr_at), so after (wmono); outside the image, so an overlay byte *)
        pose proof (HinWR x Hx) as Hxr. destruct (HBUF x Hx) as (Hown & Himg).
        destruct HW as (HW1 & HW2 & HW3).
        pose proof (HW3 (x - a) ltac:(lia)) as Hw0.
        replace (a + (x - a)) with x in Hw0 by lia.
        pose proof (WM (wa x) Hw0) as Hw.
        change (Z_to_bv 64 x) with (wa x).
        destruct (m' (wa x)) as [b|] eqn:Em.
        -- exists b. unfold mrd. rewrite Em. reflexivity.
        -- exfalso. unfold wview in Hw. rewrite Em in Hw.
           rewrite (LeafCgGlue.find_segment_out rsegs (bv_unsigned (wa x)) 1) in Hw;
             [exact (Hw eq_refl) | lia |].
           intros sg Hin Hr. rewrite wa_unsigned in Hr by lia.
           apply Himg. exists sg. split; [exact Hin | exact Hr].
    + split.
      * intros r Hr.
        destruct (Hcs r Hr) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
          reflexivity.
      * exact ENC.
Qed.

End LeafCg.
