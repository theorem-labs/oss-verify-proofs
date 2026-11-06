(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: twin of lib/AZ/LibA/StepF.v over lib.Lib. *)
(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_decode to libdiginet/fuzz_decode image A; module paths changed *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libdiginet/fuzz_decode/lib/Lib/StepF.v to libdiginet/fuzz_codec; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/Lib/StepF.v; 416 of its 450 lines of code are new or changed and 688 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/diginet_msg_next_seg_chan.v, with its module paths changed; 259 of its 310 lines of code are new or changed and 399 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the walk of diginet_msg_next in fuzz_frame.ubsan (0x141a0) proves its contract, and no UBSan check branch is taken. *)
(* Modified by Theorem Labs, 2026-10: the footprint walk of diginet_cursor_init in libdiginet/fuzz_frame's image A (fuzz_frame.asan), after proofs/libreac/fuzz_decode/lib/A/Prog/reac_frame_counter_F.v (StepF's step, the frame carve, the asan shadow loads), with the four stores to the caller's cursor. *)
(* Modified by Theorem Labs, 2026-10: the epilogue (0x83710) and the dispatch (0x833f0, 0x83454, 0x83548, 0x83580) of diginet_msg_next in image A (fuzz_frame.asan) as footprint runs; took sl56, the msg_step case equations and the 1-byte check of the cursor's status byte, and the shadow granule, signed-zero, shadow-outside and mrd-across-stores lemmas, restated for the 128-byte frame and the cursor and message ranges. *)
(* Modified by Theorem Labs, 2026-10: the epilogue (0x83828) and the dispatch (0x834fc) of diginet_msg_next in image B (fuzz_frame.asan-ubsan) as footprint runs, for the 64-byte frame; each shadow byte is read from the entry memory through the munch fact, the 1-byte checks of c + 24 prove the code after them once for any value of the register their second exit writes, the store of m->running follows the zero shadow byte of the granule of mp, and the context of the channel arm is rebuilt after that store. *)
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

(* mn_fin_holds: the epilogue 0x82798-0x827c0: a0 := a3, then ld ra, s0 .. s6 from the frame words at sp0 - 64 + 56 ..
   sp0 - 64 + 0, sp += 64 and ret; it stores nothing.
   mn_disp_of: from 0x8246c the code compares body[pos] (t3) with 0xf0 (s4) and goes
   - to 0x82470 when it is 0xf0 (mn_sys_F);
   - with bit 7 clear to 0x824d4: the 1-byte check of the status byte c + 24 (the shadow byte k at
     ((c + 24) >> 3) + 0x7fff8000 is 0 or (c + 24) mod 8 < k, so the code goes on at 0x824e8 from both exits),
     lbu t3 = st; st = 0: 0x8260c reads the shadow byte of the granule of c + 16 (0), stores pos + 1 at c + 16,
     a3 = -7 and the epilogue (mn_fin_F); st <> 0: the shadow byte of mp + 1 (the granule of mp, 0), m + 1 := 1,
     a7 = pos and 0x82640 (mn_chan_F);
   - with bit 7 set to 0x825d4: 0x80 .. 0xef to 0x82624 (the shadow byte of mp + 1, 0; a7 = pos + 1; m + 1 := 0;
     0x82640, mn_chan_F); 0xf1 .. 0xff to 0x825dc (the shadow byte of the granule of c + 16, the store of pos + 1 at
     c + 16, the 1-byte check of c + 24, the store of 0 at c + 24, a3 = -8 and the epilogue).
   Each shadow byte lies outside the frame [sp0 - 64, sp0), the cursor [c, c + 25) and the message [mp, mp + 40)
   (mn_sh_outside), the only bytes the run changes, so it keeps the value the entry memory m0 gives it (mn_rd_sh);
   the addressable facts of the context are stated at m0. Each access side goal is closed from an rng fact: the
   frame, the cursor, the message, and a sub-range of the shadow range of the cursor or the message. *)

(* ---------- bytes and shadow bytes ---------- *)

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

(* The shadow byte of the 8-byte granule of a, [a, a + 8) inside an addressable range, is 0: the granule's last
   byte 8 (a / 8) + 7 lies in [a, a + 8) and has address mod 8 = 7. *)
Lemma mn_granule0 : forall m p n a, addressable m p n -> p <= a -> a + 8 <= p + n ->
  mrd rsegs m (wa (shadow_addr a)) = Some (Z_to_bv 8 0).
Proof.
  intros m p n a (P0 & N0 & PE & AB) H1 H2.
  assert (Hi : 0 <= 8 * (a / 8) + 7 - p < n) by (Z.div_mod_to_equations; lia).
  destruct (AB _ Hi) as (_ & k & MK & SK).
  assert (E1 : (p + (8 * (a / 8) + 7 - p)) mod 8 = 7) by (Z.div_mod_to_equations; lia).
  assert (E2 : shadow_addr (p + (8 * (a / 8) + 7 - p)) = shadow_addr a)
    by (unfold shadow_addr; f_equal; Z.div_mod_to_equations; lia).
  rewrite E2 in MK. unfold shadow_ok in SK. rewrite E1 in SK.
  rewrite MK. f_equal. apply mn_signed0. lia.
Qed.

(* A shadow byte read in a memory m that differs from the entry memory m0 only in the three ranges: the byte m0
   holds. *)
Lemma mn_rd_sh : forall m0 m s c mp x b,
  munch [(s - 64, s); (c, c + 25); (mp, mp + 40)] m0 m ->
  app_mem (s - 64) -> app_mem (s - 1) -> addressable m0 c 25 -> addressable m0 mp 40 -> app_mem x ->
  mrd rsegs m0 (wa (shadow_addr x)) = Some b ->
  ov_read_bytes rsegs m (Z_to_bv 64 (x / 8 + ASAN_K)) 1 = Some [b].
Proof.
  intros m0 m s c mp x b MU A1 A2 AC AM Ax H.
  pose proof (mn_sh_outside m0 s c mp x A1 A2 AC AM Ax) as O.
  assert (Rx : 0 <= shadow_addr x < 2^64)
    by (clear - Ax; unfold shadow_addr, ASAN_K, app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *;
        Z.div_mod_to_equations; lia).
  change (Z_to_bv 64 (x / 8 + ASAN_K)) with (wa (shadow_addr x)).
  apply rd1. unfold mrd in *. rewrite MU; [exact H|].
  rewrite wa_unsigned; [exact O | exact Rx].
Qed.

(* The shadow byte of the granule of a, [a, a + 8) inside [p, p + n), read after the run's stores: 0. *)
Lemma mn_rd_gran : forall m0 m s c mp p n a,
  munch [(s - 64, s); (c, c + 25); (mp, mp + 40)] m0 m ->
  app_mem (s - 64) -> app_mem (s - 1) -> addressable m0 c 25 -> addressable m0 mp 40 ->
  addressable m0 p n -> p <= a -> a + 8 <= p + n ->
  ov_read_bytes rsegs m (Z_to_bv 64 (a / 8 + ASAN_K)) 1 = Some [Z_to_bv 8 0].
Proof.
  intros m0 m s c mp p n a MU A1 A2 AC AM AP H1 H2.
  pose proof AP as (_ & _ & _ & AB).
  destruct (AB (a - p) ltac:(lia)) as (Ax & _).
  replace (p + (a - p)) with a in Ax by lia.
  exact (mn_rd_sh m0 m s c mp a _ MU A1 A2 AC AM Ax (mn_granule0 m0 p n a AP H1 H2)).
Qed.

Lemma mn_shr3 : forall x, Z.shiftr x 3 = x / 8.
Proof. intros x. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma mn_zxb_b8 : forall x, 0 <= x < 256 -> zxb (b8 x) = Z_to_bv 64 x.
Proof. intros x Hx. unfold zxb. change (bv_unsigned (b8 x)) with (bz (b8 x)). rewrite bz_b8 by lia. reflexivity. Qed.

Lemma mn_zxb0 : zxb (Z_to_bv 8 0) = Z_to_bv 64 0.
Proof. apply bv_eq. reflexivity. Qed.

Lemma mn_sxb0 : sxb (Z_to_bv 8 0) = Z_to_bv 64 0.
Proof. apply bv_eq. reflexivity. Qed.

Lemma mn_at8_range : forall l i, 0 <= at8 l i < 256.
Proof. intros l i. unfold at8. apply bz_range. Qed.

(* slli a4, t3, 56; bltz a4: bit 7 of the byte *)
Lemma mn_sl56 : forall x, 0 <= x < 256 -> bv_lts (Z_to_bv 64 (Z.shiftl x 56)) (Z_to_bv 64 0) = (128 <=? x).
Proof.
  assert (G : forall x, 0 <= x < 2^8 ->
            Bool.eqb (bv_lts (Z_to_bv 64 (Z.shiftl x 56)) (Z_to_bv 64 0)) (128 <=? x) = true).
  { apply (byte_forall (fun x => Bool.eqb (bv_lts (Z_to_bv 64 (Z.shiftl x 56)) (Z_to_bv 64 0)) (128 <=? x))).
    vm_compute. reflexivity. }
  intros x Hx. apply Bool.eqb_prop, G. lia.
Qed.

(* ---------- the msg_step case equations ---------- *)

Lemma mn_rs_nostatus : forall bb pos st, (pos < length bb)%nat -> at8 bb pos < 128 -> st = 0 ->
  msg_step bb pos st = mr_plain MkNoStatus pos (S pos) st 0.
Proof.
  intros bb pos st Hlt X S0. unfold msg_step.
  replace (length bb <=? pos)%nat with false by (symmetry; apply Nat.leb_gt; lia).
  replace (at8 bb pos =? 0xf0) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (0xf0 <=? at8 bb pos) with false by (symmetry; apply Z.leb_gt; lia).
  replace (0x80 <=? at8 bb pos) with false by (symmetry; apply Z.leb_gt; lia).
  replace (st =? 0) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
Qed.

Lemma mn_rs_run : forall bb pos st, (pos < length bb)%nat -> at8 bb pos < 128 -> st <> 0 ->
  msg_step bb pos st = chan_step bb pos st st 1 pos.
Proof.
  intros bb pos st Hlt X S0. unfold msg_step.
  replace (length bb <=? pos)%nat with false by (symmetry; apply Nat.leb_gt; lia).
  replace (at8 bb pos =? 0xf0) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (0xf0 <=? at8 bb pos) with false by (symmetry; apply Z.leb_gt; lia).
  replace (0x80 <=? at8 bb pos) with false by (symmetry; apply Z.leb_gt; lia).
  replace (st =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

Lemma mn_rs_bad : forall bb pos st, (pos < length bb)%nat -> at8 bb pos <> 240 -> 240 <= at8 bb pos ->
  msg_step bb pos st = mr_plain MkBadStatus pos (S pos) 0 0.
Proof.
  intros bb pos st Hlt X1 X2. unfold msg_step.
  replace (length bb <=? pos)%nat with false by (symmetry; apply Nat.leb_gt; lia).
  replace (at8 bb pos =? 0xf0) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (0xf0 <=? at8 bb pos) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.

Lemma mn_rs_stat : forall bb pos st, (pos < length bb)%nat -> 128 <= at8 bb pos < 240 ->
  msg_step bb pos st = chan_step bb pos st (at8 bb pos) 0 (S pos).
Proof.
  intros bb pos st Hlt X. unfold msg_step.
  replace (length bb <=? pos)%nat with false by (symmetry; apply Nat.leb_gt; lia).
  replace (at8 bb pos =? 0xf0) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (0xf0 <=? at8 bb pos) with false by (symmetry; apply Z.leb_gt; lia).
  replace (0x80 <=? at8 bb pos) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.

(* ---------- the epilogue ---------- *)

Theorem mn_fin_holds : mn_fin_F.
Proof.
  unfold mn_fin_F.
  intros RNG sp0 ra0 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    ra gp tp t0 t1 t2 y8 y9 a0 a1 a2 a4 a5 a6 a7 y18 y19 y20 y21 y22 t3 t4 t5 t6
    F fc m0 m1 c mp body bb mj pos st HSP RFR FR MU HC HM.
  unfold MN_FRAME in HSP, RFR, FR |- *. unfold MN_FIN.
  unfold mn_fr in FR.
  pose proof (u64_range sp0) as Rsp.
  (* 0x82798 mv a0,a3 *)
  step.
  (* 0x8279c-0x827b8: ld ra, s0, s1, s2, s3, s4, s5, s6 from sp + 56 .. sp + 0 *)
  do 8 step.
  (* 0x827bc addi sp,sp,64: sp = sp0 *)
  step.
  replace (bv_unsigned sp0 - 64 + 64) with (bv_unsigned sp0) by lia. rewrite Z_to_bv_bv_unsigned.
  (* 0x827c0 ret *)
  step.
  apply evtF_done. unfold mn_post.
  do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact HC|exact HM].
Qed.

(* The epilogue from a path's last store: a3 = code, the cursor's position word vp and status byte b, the message
   cells of r, each the value msg_step gives. *)
Lemma mn_fin_at : forall (FIN : mn_fin_F) (RNG : ExecF.footprint)
    (sp0 ra0 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word)
    (ra gp tp t0 t1 t2 y8 y9 a0 a1 a2 a4 a5 a6 a7 y18 y19 y20 y21 y22 t3 t4 t5 t6 : word)
    (vp : word) (b : byte) (F : bvmap 5 word) (fc : bv 32) (m0 m1 : word -> option byte)
    (c mp body : Z) (bb mj : list byte) (pos : nat) (st : Z) (r : msg_res) (code : Z),
  MN_FRAME <= bv_unsigned sp0 ->
  ExecF.rng RNG (bv_unsigned sp0 - MN_FRAME) MN_FRAME ->
  rw_cells rsegs m1 (bv_unsigned sp0 - MN_FRAME) (mn_fr x22 x21 x20 x19 x18 x9 x8 ra0) ->
  munch [(bv_unsigned sp0 - MN_FRAME, bv_unsigned sp0); (c, c + 25); (mp, mp + 40)] m0 m1 ->
  rw_cells rsegs m1 c [C8 (Z_to_bv 64 body); C8 (Z_to_bv 64 (Z.of_nat (length bb))); C8 vp; C1 b] ->
  rw_cells rsegs m1 mp (PMsg.msg_cells body mj r) ->
  msg_step bb pos st = r -> code = mr_code r ->
  vp = Z_to_bv 64 (Z.of_nat (mr_pos r)) -> b = b8 (mr_st r) ->
  ExecF.evtF rsegs RNG
    (mn_post ra0 sp0 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc m0 c mp body bb mj pos st)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - MN_FRAME)) gp tp t0 t1 t2 y8 y9 a0 a1 a2 (Z_to_bv 64 code)
             a4 a5 a6 a7 y18 y19 y20 y21 y22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
        F (Z_to_bv 64 MN_FIN) fc None m1 (seg_rom rsegs)).
Proof.
  intros. subst. eapply FIN; eassumption.
Qed.

(* ---------- the dispatch ---------- *)

(* The context at the channel arm: the context of the dispatch with the memory after the store of m->running. *)
Lemma mn_ctx_store : forall RNG sp0 ra0 x8 x9 x18 x19 x20 x21 x22 m0 m m' c mp body bb mj pos st mc mc',
  mn_ctx RNG sp0 ra0 x8 x9 x18 x19 x20 x21 x22 m0 m c mp body bb mj pos st mc ->
  munch [(bv_unsigned sp0 - MN_FRAME, bv_unsigned sp0); (c, c + 25); (mp, mp + 40)] m0 m' ->
  rw_cells rsegs m' (bv_unsigned sp0 - MN_FRAME) (mn_fr x22 x21 x20 x19 x18 x9 x8 ra0) ->
  rw_cells rsegs m' c (PCur.cursor_cells body (Z.of_nat (length bb)) pos st) ->
  rw_cells rsegs m' mp mc' ->
  bytes_at rsegs m' body bb ->
  mn_ctx RNG sp0 ra0 x8 x9 x18 x19 x20 x21 x22 m0 m' c mp body bb mj pos st mc'.
Proof.
  intros RNG sp0 ra0 x8 x9 x18 x19 x20 x21 x22 m0 m m' c mp body bb mj pos st mc mc' CTX MU FR CUR MSG BB.
  destruct CTX as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & _ & _ & _ & _ & _ & H15 & H16 & H17 & H18 & H19
                   & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & H28 & H29 & H30).
  unfold mn_ctx.
  repeat (apply conj; [assumption|]). assumption.
Qed.

(* br v: the branch condition at the pc is v. *)
Local Ltac br v :=
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) =>
      replace cnd with v;
      [ cbv iota
      | symmetry; unfold_cond; rewrite ?unsigned_lit by lia; fold_lit_ux; solve_cond_rec ]
  end.

Local Ltac nsteps n := lazymatch n with O => idtac | S ?n' => step; nsteps n' end.

Local Ltac norm_tset := lazymatch goal with
  | |- context [tset ?p ?x ?R] =>
      let t := eval cbv beta iota delta [tset mkR] in (tset p x R) in change (tset p x R) with t
  end.

(* At a bnez on the shadow byte k of the address E (r is the register the andi of the check's second exit writes,
   nerr the number of instructions of that exit before its blt): prove the code after the check once, for every
   value of r; k = 0 falls through, else (E mod 8) < k and the blt goes back to the access. *)
Local Ltac mn_chk1 r E k SK nerr :=
  lazymatch goal with
  | |- ExecF.evtF ?segs ?RNG ?Q (MS ?R ?F (if _ then _ else ?N) ?fc ?rv ?mm ?ro) =>
      let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
      let J := fresh "J" in
      assert (J : forall x : word, ExecF.evtF segs RNG Q (MS (tset p x R) F N fc rv mm ro));
      [ let x := fresh "x" in intros x; norm_tset
      | let C := fresh "C" in let Cu := fresh "Cu" in
        destruct SK as [C|[C Cu]];
        [ rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]; let v := getreg r in exact (J v)
        | rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb];
          nsteps nerr;
          rewrite land7; rewrite (unsigned_lit E) by lia;
          rewrite (lts_low (E mod 8) k ltac:(apply Z.mod_pos_bound; lia)), (proj2 (Z.ltb_lt _ _) C); cbn [negb];
          let v := getreg r in exact (J v) ] ]
  end.

Theorem mn_disp_of : mn_fin_F -> mn_sys_F -> mn_chan_F -> mn_disp_F.
Proof.
  intros HFIN HSYS HCH. unfold mn_chan_F in HCH. unfold mn_disp_F.
  intros RNG sp0 ra0 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 ra gp tp y21 y22 F fc m0 m
    c mp body bb mj pos st CTX.
  pose proof CTX as (HPOS & HST & HMJ & HC8 & HM8 & HB0 & HSP & APS1 & APS2 & MU0 & FR & CUR & MSG & BB
    & ADC & ADM & ADB & OFC & OFM & OFB & D1 & D2 & D3 & RFR & RC & RM & RB & RSC & RSM & RSB).
  pose proof (mn_at8_range bb pos) as X0.
  pose proof (u64_range sp0) as Rsp.
  unfold st_ok in HST.
  pose proof ADC as (C0 & _ & CE & ABC).
  pose proof ADM as (M0 & _ & ME & _).
  pose proof ADB as (B0 & _ & BE & _).
  unfold APPMEM_END in CE, ME, BE.
  (* the shadow byte k24 of c + 24, read from the entry memory *)
  destruct (ABC 24 ltac:(lia)) as (AP24 & k24 & M24 & SK24).
  clear ABC. unfold shadow_ok in SK24.
  (* the rng facts of the shadow bytes the code reads: the granule of c + 16, c + 24, the granule of mp + 1 *)
  assert (RH16 : ExecF.rng RNG (shadow_addr (c + 16)) 1)
    by (eapply rng_sub'; [exact RSC|]; unfold shadow_addr; Z.div_mod_to_equations; lia).
  assert (RH24 : ExecF.rng RNG ((c + 24) / 8 + ASAN_K) 1)
    by (eapply rng_sub'; [exact RSC|]; unfold shadow_addr; Z.div_mod_to_equations; lia).
  assert (RHM1 : ExecF.rng RNG ((mp + 1) / 8 + ASAN_K) 1)
    by (eapply rng_sub'; [exact RSM|]; unfold shadow_addr; Z.div_mod_to_equations; lia).
  unfold MN_FRAME in HSP, APS1, APS2, MU0, FR, RFR, OFC, OFM, OFB |- *.
  unfold MN_DISP.
  unfold off_stk in OFC, OFM, OFB.
  unfold mn_fr in FR. unfold PCur.cursor_cells in CUR. unfold mn_msg0 in MSG.
  (* 0x8246c bne t3,s4 *)
  step.
  destruct (Z.eq_dec (at8 bb pos) 240) as [E240|N240].
  { (* 0x82470: body[pos] = 0xf0 *)
    br false. rewrite E240. eapply HSYS; [exact CTX | exact E240]. }
  br true.
  (* 0x824cc slli a4,t3,56; 0x824d0 bltz a4 *)
  step. rewrite (unsigned_lit (at8 bb pos)) by lia.
  step. rewrite mn_sl56 by lia.
  destruct (Z.leb_spec 128 (at8 bb pos)) as [X128|X128]; cbv iota.
  - (* 0x825d4 li a4,240; 0x825d8 bltu t3,a4 *)
    step. step.
    destruct (Z.ltb_spec (at8 bb pos) 240) as [XL|XL].
    + (* a status byte 0x80 .. 0xef: 0x82624 addi a4,a1,1; 0x82628 srli a6,a4,3; 0x8262c add a6,a6,t1 *)
      br true.
      step. step. rewrite (unsigned_lit (mp + 1)) by lia. rewrite mn_shr3. step.
      (* 0x82630 lb a6,0(a6): the shadow byte of the granule of mp, 0; 0x82634 bnez a6 *)
      pose proof (mn_rd_gran m0 m (bv_unsigned sp0) c mp mp 40 (mp + 1) MU0 APS1 APS2 ADC ADM ADM
                    ltac:(lia) ltac:(lia)) as HR.
      step. clear HR. rewrite mn_sxb0.
      step. br false.
      (* 0x82638 addi a7,t2,1; 0x8263c sb zero,0(a4): m + 1 := 0; on to 0x82640, its data from pos + 1 *)
      step. step.
      replace (Z.of_nat pos + 1) with (Z.of_nat (S pos)) by lia.
      eapply HCH with (s := at8 bb pos) (run := 0) (d := S pos);
        [ eapply mn_ctx_store; [exact CTX | exact MU0 | exact FR | exact CUR | exact MSG | exact BB]
        | lia | left; reflexivity | lia | apply mn_rs_stat; lia ].
    + (* a status byte 0xf1 .. 0xff: 0x825dc lbu a1,0(t0), the shadow byte of the granule of c + 16; 0x825e0 bnez a1 *)
      br false.
      pose proof (mn_rd_gran m0 m (bv_unsigned sp0) c mp c 25 (c + 16) MU0 APS1 APS2 ADC ADM ADC
                    ltac:(lia) ltac:(lia)) as HR.
      change (Z_to_bv 64 ((c + 16) / 8 + ASAN_K)) with (Z_to_bv 64 (shadow_addr (c + 16))) in HR.
      step. clear HR. rewrite mn_zxb0.
      step. br false.
      (* 0x825e4 addi t2,t2,1; 0x825e8 sd t2,16(a2): c + 16 := pos + 1 *)
      step. step.
      (* 0x825ec addi a0,a2,24; 0x825f0 srli a1,a0,3; 0x825f4 add a1,a1,t1 *)
      step. step. rewrite (unsigned_lit (c + 24)) by lia. rewrite mn_shr3. step.
      (* 0x825f8 lb a1,0(a1): the shadow byte k24 of c + 24, in the memory after the store *)
      lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (mn_rd_sh m0 mm (bv_unsigned sp0) c mp (c + 24) k24 MU0 APS1 APS2 ADC ADM AP24 M24) as HR
      end.
      step. clear HR.
      (* 0x825fc bnez a1; 0x82864 andi a2,a0,7; 0x82868 blt a2,a1 *)
      step. mn_chk1 12 (c + 24) k24 SK24 2%nat.
      (* 0x82600 sb zero,0(a0): c + 24 := 0; 0x82604 li a3,-8; 0x82608 j 0x82798 *)
      step. step. step.
      eapply (mn_fin_at HFIN) with (r := mr_plain MkBadStatus pos (S pos) 0 0);
        [ unfold MN_FRAME; lia | exact RFR | exact FR | exact MU0 | exact CUR | exact MSG
        | apply mn_rs_bad; lia | reflexivity | cbn [mr_pos mr_plain]; f_equal; lia | reflexivity ].
  - (* a data byte: 0x824d4 addi a4,a2,24; 0x824d8 srli a6,a4,3; 0x824dc add a6,a6,t1 *)
    step. step. rewrite (unsigned_lit (c + 24)) by lia. rewrite mn_shr3. step.
    (* 0x824e0 lb a6,0(a6): the shadow byte k24 of c + 24 *)
    pose proof (mn_rd_sh m0 m (bv_unsigned sp0) c mp (c + 24) k24 MU0 APS1 APS2 ADC ADM AP24 M24) as HR.
    step. clear HR.
    (* 0x824e4 bnez a6; 0x827f8 andi a7,a4,7; 0x827fc blt a7,a6 *)
    step. mn_chk1 17 (c + 24) k24 SK24 2%nat.
    (* 0x824e8 lbu t3,0(a4): t3 = st; 0x824ec beqz t3 *)
    step. rewrite (mn_zxb_b8 st) by lia.
    step.
    destruct (Z.eq_dec st 0) as [S0|S0].
    + (* st = 0: 0x8260c lbu a1,0(t0), the shadow byte of the granule of c + 16; 0x82610 bnez a1 *)
      br true.
      pose proof (mn_rd_gran m0 m (bv_unsigned sp0) c mp c 25 (c + 16) MU0 APS1 APS2 ADC ADM ADC
                    ltac:(lia) ltac:(lia)) as HR.
      change (Z_to_bv 64 ((c + 16) / 8 + ASAN_K)) with (Z_to_bv 64 (shadow_addr (c + 16))) in HR.
      step. clear HR. rewrite mn_zxb0.
      step. br false.
      (* 0x82614 addi t2,t2,1; 0x82618 sd t2,0(a0): c + 16 := pos + 1; 0x8261c li a3,-7; 0x82620 j 0x82798 *)
      step. step. step. step.
      eapply (mn_fin_at HFIN) with (r := mr_plain MkNoStatus pos (S pos) st 0);
        [ unfold MN_FRAME; lia | exact RFR | exact FR | exact MU0 | exact CUR | exact MSG
        | apply mn_rs_nostatus; lia | reflexivity | cbn [mr_pos mr_plain]; f_equal; lia | reflexivity ].
    + (* st <> 0: 0x824f0 addi a4,a1,1; 0x824f4 srli a6,a4,3; 0x824f8 add a6,a6,t1 *)
      br false.
      step. step. rewrite (unsigned_lit (mp + 1)) by lia. rewrite mn_shr3. step.
      (* 0x824fc lb a6,0(a6): the shadow byte of the granule of mp, 0; 0x82500 bnez a6 *)
      pose proof (mn_rd_gran m0 m (bv_unsigned sp0) c mp mp 40 (mp + 1) MU0 APS1 APS2 ADC ADM ADM
                    ltac:(lia) ltac:(lia)) as HR.
      step. clear HR. rewrite mn_sxb0.
      step. br false.
      (* 0x82504 li a6,1; 0x82508 sb a6,0(a4): m + 1 := 1; 0x8250c mv a7,t2; 0x82510 j 0x82640: the running status
         st, its data from pos *)
      step. step. step. step.
      eapply HCH with (s := st) (run := 1) (d := pos);
        [ eapply mn_ctx_store; [exact CTX | exact MU0 | exact FR | exact CUR | exact MSG | exact BB]
        | lia | right; reflexivity | lia | apply mn_rs_run; lia ].
Qed.
