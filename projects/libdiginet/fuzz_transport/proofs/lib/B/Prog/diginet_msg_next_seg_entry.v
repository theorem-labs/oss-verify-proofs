(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: twin of lib/AZ/LibA/StepF.v over lib.Lib. *)
(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_decode to libdiginet/fuzz_decode image A; module paths changed *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libdiginet/fuzz_decode/lib/Lib/StepF.v to libdiginet/fuzz_codec; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/Lib/StepF.v; 416 of its 450 lines of code are new or changed and 688 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/diginet_msg_next_seg_chan.v, with its module paths changed; 284 of its 323 lines of code are new or changed and 411 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the footprint walk of diginet_cursor_init in libdiginet/fuzz_frame's image A (fuzz_frame.asan), after proofs/libreac/fuzz_decode/lib/A/Prog/reac_frame_counter_F.v (StepF's step, the frame carve, the asan shadow loads), with the four stores to the caller's cursor. *)
(* Modified by Theorem Labs, 2026-10: proof of diginet_mac_is_digidesign_contract_F (fuzz_frame.asan, image A) in the form of proofs/libreac/fuzz_decode/lib/A/Prog/reac_frame_is_reac_F_nosh.v, for three bytes and the result DgnSpec.oui_of. *)
(* Modified by Theorem Labs, 2026-10: the walk of diginet_msg_next in fuzz_frame.ubsan (0x141a0) proves its contract, and no UBSan check branch is taken. *)
(* Modified by Theorem Labs, 2026-10: the entry piece mn_entry_F of the image-A walk of diginet_msg_next (0x832d0 to the return at pos >= len or to the memset call at 0x833ec); took the shadow-byte lemmas, the frame carve and the GOT/CELL_K reads of diginet_cursor_init_F.v (frame 128, message range [mp, mp + 40)), the 1-byte check of diginet_mac_is_digidesign_F.v (as the tactic chk1, with the two exits joined) and rw_conv of the image-U walk (mn_rw_conv). *)
(* Modified by Theorem Labs, 2026-10: the epilogue (0x83710) and the dispatch (0x833f0, 0x83454, 0x83548, 0x83580) of diginet_msg_next in image A (fuzz_frame.asan) as footprint runs; took sl56, the msg_step case equations and the 1-byte check of the cursor's status byte, and the shadow granule, signed-zero, shadow-outside and mrd-across-stores lemmas, restated for the 128-byte frame and the cursor and message ranges. *)
(* Modified by Theorem Labs, 2026-10: the entry piece of the image-B walk of diginet_msg_next (fuzz_frame.asan-ubsan, 0x833b8), mn_entry_of: from the epilogue's and the dispatch's footprint statements, the run from the entry to the epilogue (pos >= len) or to the dispatch at 0x834fc; restated for the 64-byte frame, the cursor and message ranges and image B's code, with the UBSan alignment and wrap checks of image B (snez_seqz_xor, land7 of the image-U walk). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA AsanKAProof.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_msg_next_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* mn_entry_of: the run of diginet_msg_next (image B) from the entry 0x82328:
   - 0x82328 - 0x82348: sp -= 64, ra and s0 - s6 into the frame words (mn_fr);
   - 0x8234c - 0x82360: c <> 0 and mp <> 0 (the branches to 0x82798 not taken), the UBSan check c & 7 not taken;
   - 0x82364 - 0x8236c: t1 = the shadow base 0x7fff8000, read through the GOT word;
   - 0x82370 - 0x8239c: the instrumented checks of the granules of c + 16 and c + 8 (shadow byte 0), t5 = len,
     t2 = pos; 0x823a0 bgeu t2,t5: pos = len goes to 0x824c4 (a3 = 0) and the epilogue 0x82798 (mn_fin_F);
   - 0x823a4 - 0x82468 (pos < len): the instrumented check of the granule of c, t4 = body, a4 = body + pos, the three
     UBSan checks of body + pos not taken, the 1-byte check of body + pos (both exits go on at 0x823e4), the UBSan
     check mp & 7 not taken, t3 = body[pos], and the stores mp + 24 := pos, mp + 8 := 0, mp + 16 := 0, mp + 3 := 0,
     mp + 2 := 0, each after its instrumented check (the granule of mp + 24, mp + 8, mp + 16 and of mp: shadow
     byte 0); then the dispatch 0x8246c (mn_disp_F).
   Each shadow byte the code loads is read through the munch fact from the entry memory: it lies outside the frame,
   the cursor and the message, the only bytes the run writes. Every error path (a call of errpath_load8,
   errpath_store8, errpath_load1 or errpath_store1) is not reached. *)

(* ---------- shadow bytes ---------- *)

Lemma mn_signed0 : forall k : byte, bv_signed k = 0 -> k = Z_to_bv 8 0.
Proof.
  intros k H. apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 0) with 0.
  pose proof (bv_unsigned_in_range 8 k) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in H.
  change (2 ^ Z.of_N 8) with 256 in H. change (256 / 2) with 128 in H.
  Z.div_mod_to_equations. lia.
Qed.

Lemma mn_shadow_not_app : forall x, app_mem x -> ~ app_mem (shadow_addr x).
Proof.
  intros x H. unfold shadow_addr, app_mem, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *.
  Z.div_mod_to_equations. lia.
Qed.

(* The shadow byte of an application byte lies outside the frame [s - 64, s), the cursor [c, c + 25) and the
   message [mp, mp + 40). *)
Lemma mn_sh_outside : forall m s c mp x, app_mem (s - 64) -> app_mem (s - 1) ->
  addressable m c 25 -> addressable m mp 40 -> app_mem x ->
  outside [(s - 64, s); (c, c + 25); (mp, mp + 40)] (shadow_addr x).
Proof.
  intros m s c mp x A1 A2 (C0 & _ & _ & AC) (M0 & _ & _ & AM) Ax.
  pose proof (mn_shadow_not_app x Ax) as N.
  cbn [outside]. split; [|split; [|split; [|exact I]]]; intros W; apply N.
  - unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia.
  - destruct (AC (shadow_addr x - c) ltac:(lia)) as (Ay & _).
    replace (c + (shadow_addr x - c)) with (shadow_addr x) in Ay by lia. exact Ay.
  - destruct (AM (shadow_addr x - mp) ltac:(lia)) as (Ay & _).
    replace (mp + (shadow_addr x - mp)) with (shadow_addr x) in Ay by lia. exact Ay.
Qed.

(* A shadow byte read after the run's stores: the byte the entry memory holds. *)
Lemma mn_rd_sh : forall m m' s c mp x b,
  munch [(s - 64, s); (c, c + 25); (mp, mp + 40)] m m' ->
  app_mem (s - 64) -> app_mem (s - 1) -> addressable m c 25 -> addressable m mp 40 ->
  app_mem x -> mrd rsegs m (wa (shadow_addr x)) = Some b ->
  ov_read_bytes rsegs m' (Z_to_bv 64 (x / 8 + 2147450880)) 1 = Some [b].
Proof.
  intros m m' s c mp x b MU A1 A2 AC AM Ax H.
  pose proof (mn_sh_outside m s c mp x A1 A2 AC AM Ax) as O.
  change (Z_to_bv 64 (x / 8 + 2147450880)) with (wa (shadow_addr x)).
  apply rd1. unfold mrd in *. rewrite MU; [exact H|].
  rewrite wa_unsigned; [exact O|].
  unfold shadow_addr, ASAN_K, app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. Z.div_mod_to_equations. lia.
Qed.

(* The instrumented check before an access at a whose 8-byte granule lies in [q, q + n): the shadow byte is 0. *)
Lemma mn_rd_gran : forall m m' s c mp q n a,
  munch [(s - 64, s); (c, c + 25); (mp, mp + 40)] m m' ->
  app_mem (s - 64) -> app_mem (s - 1) -> addressable m c 25 -> addressable m mp 40 ->
  addressable m q n -> q <= a -> a + 8 <= q + n ->
  ov_read_bytes rsegs m' (Z_to_bv 64 (a / 8 + 2147450880)) 1 = Some [Z_to_bv 8 0].
Proof.
  intros m m' s c mp q n a MU A1 A2 AC AM (Q0 & N0 & QE & AB) H1 H2.
  assert (Hi : 0 <= 8 * (a / 8) + 7 - q < n) by (Z.div_mod_to_equations; lia).
  destruct (AB _ Hi) as (Ax & k & MK & SK).
  assert (E1 : (q + (8 * (a / 8) + 7 - q)) mod 8 = 7) by (Z.div_mod_to_equations; lia).
  assert (E2 : (q + (8 * (a / 8) + 7 - q)) / 8 = a / 8) by (Z.div_mod_to_equations; lia).
  unfold shadow_ok in SK. rewrite E1 in SK.
  assert (K0 : k = Z_to_bv 8 0) by (apply mn_signed0; lia). subst k.
  rewrite <- E2. exact (mn_rd_sh m m' s c mp _ _ MU A1 A2 AC AM Ax MK).
Qed.

(* The 1-byte check of q + i: its shadow byte k, with k = 0 or (q + i) mod 8 < k. *)
Lemma mn_rd_byte : forall m m' s c mp q n i,
  munch [(s - 64, s); (c, c + 25); (mp, mp + 40)] m m' ->
  app_mem (s - 64) -> app_mem (s - 1) -> addressable m c 25 -> addressable m mp 40 ->
  addressable m q n -> 0 <= i < n ->
  exists k, ov_read_bytes rsegs m' (Z_to_bv 64 ((q + i) / 8 + 2147450880)) 1 = Some [k] /\
            (bv_signed k = 0 \/ ((q + i) mod 8 < bv_signed k /\ bv_signed k <= 7)).
Proof.
  intros m m' s c mp q n i MU A1 A2 AC AM (Q0 & N0 & QE & AB) Hi.
  destruct (AB i Hi) as (Ax & k & MK & SK). exists k. split; [|exact SK].
  exact (mn_rd_sh m m' s c mp _ _ MU A1 A2 AC AM Ax MK).
Qed.

(* The footprint of one shadow byte of [p, p + n). *)
Lemma mn_rng_sh : forall RNG p n a,
  ExecF.rng RNG (shadow_addr p) (shadow_addr (p + n - 1) - shadow_addr p + 1) -> p <= a < p + n ->
  ExecF.rng RNG (a / 8 + 2147450880) 1.
Proof.
  intros RNG p n a H Ha. eapply rng_sub'; [exact H|]. unfold shadow_addr, ASAN_K.
  Z.div_mod_to_equations. lia.
Qed.

(* A byte the run does not write, read after its stores. *)
Lemma mn_rd_keep : forall m m' W a b, munch W m m' -> outside W a -> 0 <= a < 2^64 ->
  mrd rsegs m (wa a) = Some b -> ov_read_bytes rsegs m' (Z_to_bv 64 a) 1 = Some [b].
Proof.
  intros m m' W a b MU O Ha H. apply rd1. unfold mrd in *. rewrite MU; [exact H|].
  rewrite wa_unsigned by exact Ha. exact O.
Qed.

(* ---------- words ---------- *)

Lemma mn_srl3 : forall x, 0 <= x < 2^64 -> Z.shiftr (bv_unsigned (Z_to_bv 64 x)) 3 = x / 8.
Proof.
  intros x Hx. rewrite unsigned_lit by exact Hx. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

(* c & 7 and mp & 7, the UBSan alignment checks *)
Lemma mn_land7_0 : forall x, 0 <= x < 2^64 -> x mod 8 = 0 -> Z.land (bv_unsigned (Z_to_bv 64 x)) 7 = 0.
Proof.
  intros x Hx H8. rewrite unsigned_lit by lia. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact H8.
Qed.

(* 0x823c0 - 0x823c8: (body != 0) ^ (body + pos == 0) *)
Lemma mn_snez_seqz_xor : forall x y, 0 < x < 2^64 -> 0 < y < 2^64 ->
  Z_to_bv 64 (Z.lxor (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 x))) (bv_unsigned (v_sltiu (Z_to_bv 64 y) 1)))
  = Z_to_bv 64 1.
Proof.
  intros x y Hx Hy. unfold v_sltu, v_sltiu, c_ltu, bv_ltu. rewrite !unsigned_lit by lia. change (bv_wrap 64 1) with 1.
  replace (0 <? x) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (y <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma mn_sxb0 : sxb (Z_to_bv 8 0) = Z_to_bv 64 0.
Proof. reflexivity. Qed.

(* ---------- cells ---------- *)

(* The same bytes under other cells. *)
Lemma mn_rw_conv : forall m A cs cs', rw_cells rsegs m A cs -> cells_wf cs' ->
  cells_bytes cs' = cells_bytes cs -> rw_cells rsegs m A cs'.
Proof.
  intros m A cs cs' [[W B] V] W' EB. split; [split|].
  - exact W'.
  - rewrite EB. exact B.
  - rewrite <- (cells_bytes_length cs' W'), EB, (cells_bytes_length cs W). exact V.
Qed.

(* The message at the dispatch: the cells the five stores left, as mn_msg0. *)
Lemma mn_to_msg0 : forall m A (mj : list byte) (pos : nat) cs, length mj = 40%nat ->
  rw_cells rsegs m A cs -> cells_bytes (mn_msg0 mj pos) = cells_bytes cs -> rw_cells rsegs m A (mn_msg0 mj pos).
Proof.
  intros m A mj pos cs L H EB. eapply mn_rw_conv; [exact H| |exact EB].
  unfold mn_msg0. cbn [cells_wf cell_wf]. rewrite length_firstn, !length_skipn, L. repeat split.
Qed.

(* ---------- the two cut points ---------- *)

(* The epilogue 0x82798 (mn_fin_F) with sp and a3 given by equations. *)
Lemma mn_fin_at : mn_fin_F ->
  forall (RNG : ExecF.footprint) (sp0 ra0 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word)
    (ra xsp gp tp t0 t1 t2 y8 y9 a0 a1 a2 a3 a4 a5 a6 a7 y18 y19 y20 y21 y22 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m1 : word -> option byte)
    (c mp body : Z) (bb mj : list byte) (pos : nat) (st : Z),
  MN_FRAME <= bv_unsigned sp0 ->
  ExecF.rng RNG (bv_unsigned sp0 - MN_FRAME) MN_FRAME ->
  rw_cells rsegs m1 (bv_unsigned sp0 - MN_FRAME) (mn_fr x22 x21 x20 x19 x18 x9 x8 ra0) ->
  munch [(bv_unsigned sp0 - MN_FRAME, bv_unsigned sp0); (c, c + 25); (mp, mp + 40)] m0 m1 ->
  rw_cells rsegs m1 c (PCur.cursor_cells body (Z.of_nat (length bb)) (mr_pos (msg_step bb pos st))
                         (mr_st (msg_step bb pos st))) ->
  rw_cells rsegs m1 mp (PMsg.msg_cells body mj (msg_step bb pos st)) ->
  xsp = Z_to_bv 64 (bv_unsigned sp0 - MN_FRAME) ->
  a3 = Z_to_bv 64 (mr_code (msg_step bb pos st)) ->
  ExecF.evtF rsegs RNG
    (mn_post ra0 sp0 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc m0 c mp body bb mj pos st)
    (MS (mkR ra xsp gp tp t0 t1 t2 y8 y9 a0 a1 a2 a3 a4 a5 a6 a7 y18 y19 y20 y21 y22 x23 x24 x25 x26 x27
             t3 t4 t5 t6)
        F (Z_to_bv 64 MN_FIN) fc None m1 (seg_rom rsegs)).
Proof.
  intros HFIN. intros until st. intros HSP RFR FR MU HC HM Esp Ea3. subst xsp a3.
  eapply HFIN; eassumption.
Qed.

(* The dispatch 0x8246c (mn_disp_F) with the registers given by equations. *)
Lemma mn_disp_at : mn_disp_F ->
  forall (RNG : ExecF.footprint) (sp0 ra0 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word)
    (ra gp tp y21 y22 : word) (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
    (c mp body : Z) (bb mj : list byte) (pos : nat) (st : Z)
    (xsp v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v28 v29 v30 v31 : word),
  mn_ctx RNG sp0 ra0 x8 x9 x18 x19 x20 x21 x22 m0 m c mp body bb mj pos st (mn_msg0 mj pos) ->
  xsp = Z_to_bv 64 (bv_unsigned sp0 - MN_FRAME) ->
  v5 = Z_to_bv 64 (shadow_addr (c + 16)) -> v6 = Z_to_bv 64 ASAN_K -> v7 = Z_to_bv 64 (Z.of_nat pos) ->
  v8 = Z_to_bv 64 (shadow_addr (mp + 3)) -> v9 = Z_to_bv 64 (shadow_addr (mp + 2)) ->
  v10 = Z_to_bv 64 (c + 16) -> v11 = Z_to_bv 64 mp -> v12 = Z_to_bv 64 c -> v13 = Z_to_bv 64 (mp + 3) ->
  v14 = Z_to_bv 64 (body + Z.of_nat pos) -> v15 = Z_to_bv 64 (mp + 2) -> v16 = Z_to_bv 64 (mp + 8) ->
  v17 = Z_to_bv 64 (mp + 16) -> v18 = Z_to_bv 64 (shadow_addr (mp + 8)) ->
  v19 = Z_to_bv 64 (shadow_addr (mp + 16)) -> v20 = Z_to_bv 64 240 ->
  v28 = Z_to_bv 64 (at8 bb pos) -> v29 = Z_to_bv 64 body -> v30 = Z_to_bv 64 (Z.of_nat (length bb)) ->
  v31 = Z_to_bv 64 0 ->
  ExecF.evtF rsegs RNG
    (mn_post ra0 sp0 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc m0 c mp body bb mj pos st)
    (MS (mkR ra xsp gp tp v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 y21 y22
             x23 x24 x25 x26 x27 v28 v29 v30 v31)
        F (Z_to_bv 64 MN_DISP) fc None m (seg_rom rsegs)).
Proof.
  intros HDISP. intros until v31. intros CTX. intros. subst.
  apply HDISP. exact CTX.
Qed.

(* ---------- tactics ---------- *)

Ltac shr3 := rewrite mn_srl3 by lia.
Ltac curm := lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => mm end.
(* A branch whose condition compares words Z_to_bv 64 z with z in range. *)
Ltac br v := lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) =>
      replace cnd with v; [cbv iota | symmetry; unfold_cond; fold_lit_ux; rewrite ?unsigned_lit by lia; solve_cond_rec]
  end.

(* The 1-byte check at a branch `bnez k`: both of its exits continue at the access (pc) with the registers as they
   are, but register r, which the second exit writes (andi r, _, 7). K is that continuation. *)
Ltac cont_r K r pc :=
  lazymatch goal with |- evtF ?sg ?RN ?Q (MS ?R ?F _ ?fc ?rv ?mm ?ro) =>
    assert (K : forall v : word, evtF sg RN Q (MS (@bvmap_set 5 word (Z_to_bv 5 r) v R) F (Z_to_bv 64 pc) fc rv mm ro))
  end.
Ltac use_r K r := let v := reg_val r in exact (K v).
(* The two exits of the check: k = 0 falls through; else (a mod 8) < k, and blt goes back to the access. *)
Ltac chk_r K SK k a r :=
  destruct SK as [Ck|[Ck Ck']];
  [ rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) Ck); cbn [negb]; use_r K r
  | rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb]; step; step;
    rewrite land7, (unsigned_lit a) by lia;
    rewrite (lts_low (a mod 8) k ltac:(apply Z.mod_pos_bound; lia)), (proj2 (Z.ltb_lt _ _) Ck); cbn [negb];
    use_r K r ].

(* ---------- the entry piece ---------- *)

Theorem mn_entry_of : mn_fin_F -> mn_disp_F -> mn_entry_F.
Proof.
  intros HFIN HDISP. unfold mn_entry_F.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    c mp body bb mj pos st lo E0 E1 Hc Hmp Hc8 Hm8 Hpos Hst LJ ST HLO APS1 APS2 CELLS OFFG OFFK CC CM ADC ADM OFFC OFFM
    D1 BODY RFR RGOT RCELL RCUR RMSG RSHC RSHM RBODY.
  subst a0 a1. unfold MN_ENTRY, MN_FRAME in *.
  pose proof (u64_range sp) as Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  pose proof ADC as (C0 & _ & CE & _). pose proof ADM as (M0 & _ & ME & _).
  unfold APPMEM_END in CE, ME.
  destruct CELLS as (CK & GCK & _).
  unfold PCur.cursor_cells in CC.
  unfold off_stk, GOT_CELL_K, CELL_K in *.
  carve_frame 64%nat ST.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (c, c + 25); (mp, mp + 40)] m) as MU.
  (* 0x82328 addi sp,sp,-64; 0x8232c - 0x82348: ra, s0 .. s6 into the frame *)
  do 9 step.
  (* 0x8234c li a3,-1; 0x82350 beqz a0: c <> 0 *)
  step. step. br false.
  (* 0x82354 beqz a1: mp <> 0 *)
  step. br false.
  (* 0x82358 mv a2,a0; 0x8235c andi a0,a0,7: c mod 8 = 0; 0x82360 bnez a0: the UBSan check, not taken *)
  step. step. rewrite (mn_land7_0 c) by lia. step. br false.
  (* 0x82364 auipc a0; 0x82368 ld a0, the GOT word: CELL_K; 0x8236c ld t1,0(a0): the shadow base *)
  let mm := curm in
  assert (RDG : ov_read_bytes rsegs mm (wa 670960) 8 = Some (le8 (wa 706168)))
    by (replace (wa 670960) with (wa (670960 + 0)) by reflexivity;
        rewrite (bytes_at_read rsegs mm 670960 _ 0 8 GCK ltac:(lia)) by (rewrite length_le8; lia); reflexivity);
  assert (RDS : ov_read_bytes rsegs mm (wa 706168) 8 = Some (le8 (wa 2147450880)))
    by (replace (wa 706168) with (wa (706168 + 0)) by reflexivity;
        rewrite (bytes_at_read rsegs mm 706168 _ 0 8 CK ltac:(lia)) by (rewrite length_le8; lia); reflexivity).
  step. step. step.
  clear RDG RDS CK GCK.
  (* 0x82370 addi a0,a2,16; 0x82374 srli t0,a0,3; 0x82378 add t0,t0,t1: the shadow address of c + 16 *)
  step. step. shr3. step.
  (* 0x8237c lbu a3,0(t0): the shadow byte of the granule of c + 16 is 0; 0x82380 bnez a3: the error path, not
     reached *)
  let mm := curm in
  pose proof (mn_rd_gran m mm (bv_unsigned sp) c mp c 25 (c + 16) MU APS1 APS2 ADC ADM ADC ltac:(lia) ltac:(lia))
    as HR;
  pose proof (mn_rng_sh RNG c 25 (c + 16) RSHC ltac:(lia)) as RH.
  step. clear HR RH. step. if_false.
  (* 0x82384 addi a3,a2,8; 0x82388 srli a4,a3,3; 0x8238c add a4,a4,t1; 0x82390 lbu a4,0(a4): the shadow byte of the
     granule of c + 8 is 0; 0x82394 bnez a4: the error path, not reached *)
  step. step. shr3. step.
  let mm := curm in
  pose proof (mn_rd_gran m mm (bv_unsigned sp) c mp c 25 (c + 8) MU APS1 APS2 ADC ADM ADC ltac:(lia) ltac:(lia))
    as HR;
  pose proof (mn_rng_sh RNG c 25 (c + 8) RSHC ltac:(lia)) as RH.
  step. clear HR RH. step. if_false.
  (* 0x82398 ld t5,0(a3): len; 0x8239c ld t2,16(a2): pos; 0x823a0 bgeu t2,t5 *)
  step. step. step.
  destruct (Nat.eq_dec pos (length bb)) as [EQ|NE].
  - (* pos = len: 0x824c4 li a3,0; 0x824c8 j 0x82798, the epilogue *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) =>
      replace cnd with true; [cbv iota | symmetry; rewrite EQ; unfold bv_ltu; rewrite Z.ltb_irrefl; reflexivity]
    end.
    step. step.
    assert (RS : msg_step bb pos st = mr_plain MkEnd pos pos st 0)
      by (unfold msg_step; replace (length bb <=? pos)%nat with true by (symmetry; apply Nat.leb_le; lia);
          reflexivity).
    eapply (mn_fin_at HFIN);
      [ unfold MN_FRAME; lia | exact RFR | exact FR | exact MU | rewrite RS; exact CC | rewrite RS; exact CM
      | reflexivity | rewrite RS; reflexivity ].
  - (* pos < len *)
    assert (Hlt : (pos < length bb)%nat) by lia.
    destruct (BODY Hlt) as (B0 & BB & ADB & OFFB & D2 & D3). destruct (RBODY Hlt) as (RB & RSHB).
    clear BODY RBODY.
    pose proof ADB as (_ & _ & BE & _). unfold APPMEM_END in BE.
    br false.
    (* 0x823a4 srli a3,a2,3; 0x823a8 add a3,a3,t1; 0x823ac lbu a3,0(a3): the shadow byte of the granule of c is 0;
       0x823b0 bnez a3: the error path, not reached *)
    step. shr3. step.
    let mm := curm in
    pose proof (mn_rd_gran m mm (bv_unsigned sp) c mp c 25 c MU APS1 APS2 ADC ADM ADC ltac:(lia) ltac:(lia)) as HR;
    pose proof (mn_rng_sh RNG c 25 c RSHC ltac:(lia)) as RH.
    step. clear HR RH. step. if_false.
    (* 0x823b4 ld t4,0(a2): body; 0x823b8 add a4,t4,t2: body + pos *)
    step. step.
    (* 0x823bc bltu a4,t4: the UBSan check, not taken (body + pos does not wrap) *)
    step. br false.
    (* 0x823c0 snez a3,t4; 0x823c4 seqz a5,a4; 0x823c8 xor a3,a3,a5; 0x823cc beqz a3: the UBSan check, not taken *)
    step. step. step. rewrite (mn_snez_seqz_xor body (body + Z.of_nat pos)) by lia. step. br false.
    (* 0x823d0 beqz t4: the UBSan check, not taken (0 < body) *)
    step. br false.
    (* 0x823d4 srli a3,a4,3; 0x823d8 add a3,a3,t1; 0x823dc lb a3,0(a3): the shadow byte kb of body + pos *)
    step. shr3. step.
    let mm := curm in
    destruct (mn_rd_byte m mm (bv_unsigned sp) c mp body (Z.of_nat (length bb)) (Z.of_nat pos) MU APS1 APS2 ADC ADM
                ADB ltac:(lia)) as (kb & HR & SKb);
    pose proof (mn_rng_sh RNG body (Z.of_nat (length bb)) (body + Z.of_nat pos) RSHB ltac:(lia)) as RH.
    step. clear HR RH.
    (* 0x823e0 bnez a3: kb = 0 falls through to 0x823e4; else 0x827c8 andi a5,a4,7; 0x827cc blt a5,a3 goes back to
       0x823e4 ((body + pos) mod 8 < kb) *)
    step.
    cont_r K1 15 0x8c6c8.
    2: chk_r K1 SKb kb (body + Z.of_nat pos) 15.
    intros v1. simp_regs.
    (* 0x823e4 andi t6,a1,7: mp mod 8 = 0; 0x823e8 bnez t6: the UBSan check, not taken *)
    step. rewrite (mn_land7_0 mp) by lia. step. br false.
    (* 0x823ec addi a3,a1,24; 0x823f0 srli a5,a3,3; 0x823f4 add a5,a5,t1; 0x823f8 lbu a5,0(a5): the shadow byte of
       the granule of mp + 24 is 0; 0x823fc bnez a5: the error path, not reached *)
    step. step. shr3. step.
    let mm := curm in
    pose proof (mn_rd_gran m mm (bv_unsigned sp) c mp mp 40 (mp + 24) MU APS1 APS2 ADC ADM ADM ltac:(lia) ltac:(lia))
      as HR;
    pose proof (mn_rng_sh RNG mp 40 (mp + 24) RSHM ltac:(lia)) as RH.
    step. clear HR RH. step. if_false.
    (* 0x82400 lbu t3,0(a4): body[pos] *)
    let mm := curm in
    pose proof (mn_rd_keep m mm _ (body + Z.of_nat pos) _ MU ltac:(cbn [outside]; repeat split; lia) ltac:(lia)
                  (bytes_nth m body bb pos BB Hlt)) as HR.
    step. clear HR.
    (* 0x82404 sd t2,24(a1): mp + 24 := pos *)
    step.
    (* 0x82408 addi a6,a1,8; 0x8240c srli s2,a6,3; 0x82410 add s2,s2,t1; 0x82414 lbu a3,0(s2): the shadow byte of
       the granule of mp + 8 is 0; 0x82418 bnez a3: the error path, not reached; 0x8241c sd zero,8(a1) *)
    step. step. shr3. step.
    let mm := curm in
    pose proof (mn_rd_gran m mm (bv_unsigned sp) c mp mp 40 (mp + 8) MU APS1 APS2 ADC ADM ADM ltac:(lia) ltac:(lia))
      as HR;
    pose proof (mn_rng_sh RNG mp 40 (mp + 8) RSHM ltac:(lia)) as RH.
    step. clear HR RH. step. if_false.
    step.
    (* 0x82420 addi a7,a1,16; 0x82424 srli s3,a7,3; 0x82428 add s3,s3,t1; 0x8242c lbu a3,0(s3): the shadow byte of
       the granule of mp + 16 is 0; 0x82430 bnez a3: the error path, not reached; 0x82434 sd zero,16(a1) *)
    step. step. shr3. step.
    let mm := curm in
    pose proof (mn_rd_gran m mm (bv_unsigned sp) c mp mp 40 (mp + 16) MU APS1 APS2 ADC ADM ADM ltac:(lia) ltac:(lia))
      as HR;
    pose proof (mn_rng_sh RNG mp 40 (mp + 16) RSHM ltac:(lia)) as RH.
    step. clear HR RH. step. if_false.
    step.
    (* 0x82438 addi a3,a1,3; 0x8243c srli s0,a3,3; 0x82440 add s0,s0,t1; 0x82444 lb a5,0(s0): the shadow byte of
       mp + 3, the one of the granule of mp: 0 (mp mod 8 = 0) *)
    step. step. shr3. step.
    let mm := curm in
    pose proof (mn_rd_gran m mm (bv_unsigned sp) c mp mp 40 (mp + 3) MU APS1 APS2 ADC ADM ADM ltac:(lia) ltac:(lia))
      as HR;
    pose proof (mn_rng_sh RNG mp 40 (mp + 3) RSHM ltac:(lia)) as RH.
    step. clear HR RH. rewrite mn_sxb0.
    (* 0x82448 bnez a5: falls through; 0x8244c sb zero,3(a1): mp + 3 := 0 *)
    step. if_false.
    step.
    (* 0x82450 addi a5,a1,2; 0x82454 srli s1,a5,3; 0x82458 add s1,s1,t1; 0x8245c lb s4,0(s1): the shadow byte of
       mp + 2, the one of the granule of mp: 0 *)
    step. step. shr3. step.
    let mm := curm in
    pose proof (mn_rd_gran m mm (bv_unsigned sp) c mp mp 40 (mp + 2) MU APS1 APS2 ADC ADM ADM ltac:(lia) ltac:(lia))
      as HR;
    pose proof (mn_rng_sh RNG mp 40 (mp + 2) RSHM ltac:(lia)) as RH.
    step. clear HR RH. rewrite mn_sxb0.
    (* 0x82460 bnez s4: falls through; 0x82464 li s4,240; 0x82468 sb zero,0(a5): mp + 2 := 0 *)
    step. if_false.
    step. step.
    (* 0x8246c: the dispatch (mn_disp_F) *)
    let mm := curm in
    assert (BB' : bytes_at rsegs mm body bb)
      by (eapply bytes_at_transport; [exact BB | exact MU |
          cbn [disjoint_from]; split; [lia | split; [lia | split; [lia | exact I]]]]).
    eapply (mn_disp_at HDISP); [ | reflexivity .. ].
    unfold mn_ctx.
    refine (conj Hlt (conj Hst (conj LJ (conj Hc8 (conj Hm8 (conj B0 (conj ?[HSP] (conj APS1 (conj APS2 (conj MU
              (conj FR (conj CC (conj ?[HMSG] (conj BB' (conj ADC (conj ADM (conj ADB (conj OFFC (conj OFFM
              (conj OFFB (conj D1 (conj D2 (conj D3 (conj RFR (conj RCUR (conj RMSG (conj RB
              (conj RSHC (conj RSHM RSHB))))))))))))))))))))))))))))).
    + unfold MN_FRAME. lia.
    + apply (mn_to_msg0 _ _ mj pos _ LJ CM).
      clear - LJ.
      do 40 (destruct mj as [|? mj]; [discriminate LJ | cbn [length] in LJ; apply eq_add_S in LJ]).
      destruct mj; [|discriminate LJ].
      cbn [mn_msg0 cells_bytes cbytes app firstn skipn nth]. reflexivity.
Qed.
