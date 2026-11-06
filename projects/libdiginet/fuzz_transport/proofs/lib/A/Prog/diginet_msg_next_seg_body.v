(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: twin of lib/AZ/LibA/StepF.v over lib.Lib. *)
(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_decode to libdiginet/fuzz_decode image A; module paths changed *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libdiginet/fuzz_decode/lib/Lib/StepF.v to libdiginet/fuzz_codec; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/Lib/StepF.v; 416 of its 450 lines of code are new or changed and 688 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/diginet_msg_next_seg_chan.v; 193 of its 232 lines of code are new or changed and 411 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA AsanKAProof.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_msg_next_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* mn_fin_holds: the epilogue 0x82528-0x82560 loads ra and s0 - s11 from the frame words at sp0 - 128 + 24 ..
   sp0 - 128 + 120, adds 128 to sp and returns; it stores nothing.
   mn_body_of: from 0x82208 (the return of the memset call) the code compares body[pos] (s10) with 0xf0 and goes
   - to 0x82210 when it is 0xf0 (mn_sys_F);
   - with bit 7 clear to 0x8226c: the 1-byte check of the status byte c + 24 (the shadow byte k at
     ((c + 24) >> 3) + 0x7fff8000 is 0 or (c + 24) mod 8 < k, so the code goes on at 0x82280), lbu s10 = st; st = 0:
     0x82398 checks the shadow byte of the granule of c + 16 (0), stores pos + 1 at c + 16 (through the frame word at
     sp0 - 128 + 16), a0 = -7 and the epilogue; st <> 0: a5 = 1, a2 = pos and 0x823b8 (mn_chan_F);
   - with bit 7 set to 0x82360, a2 = pos + 1: 0xf1 .. 0xff to 0x8236c (the shadow byte of the granule of c + 16, the
     store of pos + 1 at c + 16, the 1-byte check of c + 24, the store of 0 at c + 24, a0 = -8 and the epilogue);
     0x80 .. 0xef to 0x823b4: a5 = 0 and 0x823b8 (mn_chan_F).
   Each access side goal is closed from an rng fact for the accessed range: the frame, the cursor [c, c + 25), and a
   sub-range of the cursor's shadow range for each shadow byte. The stores change only [c, c + 25); the shadow byte of
   c + 24 lies outside the frame, the cursor and the message (mn_sh_outside), so it is the same after the store at
   c + 16. *)

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

(* The shadow byte of an application byte lies outside the frame [s - 128, s), the cursor [c, c + 25) and the
   message [mp, mp + 40). *)
Lemma mn_sh_outside : forall m s c mp x, app_mem (s - 128) -> app_mem (s - 1) ->
  addressable m c 25 -> addressable m mp 40 -> app_mem x ->
  outside [(s - 128, s); (c, c + 25); (mp, mp + 40)] (shadow_addr x).
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

Lemma mn_mrd_munch : forall W m m' a b, munch W m m' -> outside W a ->
  mrd rsegs m (wa a) = Some b -> 0 <= a < 2^64 -> mrd rsegs m' (wa a) = Some b.
Proof.
  intros W m m' a b MU Ho H Ha. unfold mrd in *. rewrite MU; [exact H|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

Lemma mn_shr3 : forall x, Z.shiftr x 3 = x / 8.
Proof. intros x. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma mn_zxb_b8 : forall x, 0 <= x < 256 -> zxb (b8 x) = Z_to_bv 64 x.
Proof. intros x Hx. unfold zxb. change (bv_unsigned (b8 x)) with (bz (b8 x)). rewrite bz_b8 by lia. reflexivity. Qed.

Lemma mn_zxb0 : zxb (Z_to_bv 8 0) = Z_to_bv 64 0.
Proof. apply bv_eq. reflexivity. Qed.

Lemma mn_at8_range : forall l i, 0 <= at8 l i < 256.
Proof. intros l i. unfold at8. apply bz_range. Qed.

(* slli a0, s10, 56; bltz a0: bit 7 of the byte *)
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
    ra gp tp t0 t1 t2 y8 y9 a1 a2 a3 a4 a5 a6 a7 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 t3 t4 t5 t6
    v0 v8 v16 F fc m m1 c mp body bb mj pos st HSP RFR FR MU HC HM.
  unfold MN_FRAME in HSP, RFR, FR |- *.
  unfold mn_fr in FR.
  pose proof (u64_range sp0) as Rsp.
  (* 0x82528-0x82558: ld ra, s0 .. s11 from sp + 120 .. sp + 24 *)
  do 13 step.
  (* 0x8255c addi sp,sp,128: sp = sp0 *)
  step.
  replace (bv_unsigned sp0 - 128 + 128) with (bv_unsigned sp0) by lia. rewrite Z_to_bv_bv_unsigned.
  (* 0x82560 ret *)
  step.
  apply evtF_done. unfold mn_post.
  do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact HC|exact HM].
Qed.

(* The epilogue from a path's last store: a0 = code, the cursor's position word vp and status byte b, the message
   cells of r, each the value msg_step gives. *)
Lemma mn_fin_at : forall (RNG : ExecF.footprint) (sp0 ra0 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word)
    (ra gp tp t0 t1 t2 y8 y9 a1 a2 a3 a4 a5 a6 a7 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 t3 t4 t5 t6 : word)
    (v0 v8 v16 vp : word) (b : byte) (F : bvmap 5 word) (fc : bv 32) (m m1 : word -> option byte)
    (c mp body : Z) (bb mj : list byte) (pos : nat) (st : Z) (r : msg_res) (code : Z),
  MN_FRAME <= bv_unsigned sp0 ->
  ExecF.rng RNG (bv_unsigned sp0 - MN_FRAME) MN_FRAME ->
  rw_cells rsegs m1 (bv_unsigned sp0 - MN_FRAME)
    (mn_fr v0 v8 v16 x27 x26 x25 x24 x23 x22 x21 x20 x19 x18 x9 x8 ra0) ->
  munch [(bv_unsigned sp0 - MN_FRAME, bv_unsigned sp0); (c, c + 25); (mp, mp + 40)] m m1 ->
  rw_cells rsegs m1 c [C8 (Z_to_bv 64 body); C8 (Z_to_bv 64 (Z.of_nat (length bb))); C8 vp; C1 b] ->
  rw_cells rsegs m1 mp (PMsg.msg_cells body mj r) ->
  msg_step bb pos st = r -> code = mr_code r ->
  vp = Z_to_bv 64 (Z.of_nat (mr_pos r)) -> b = b8 (mr_st r) ->
  ExecF.evtF rsegs RNG
    (mn_post ra0 sp0 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc m c mp body bb mj pos st)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - MN_FRAME)) gp tp t0 t1 t2 y8 y9 (Z_to_bv 64 code) a1 a2 a3 a4 a5 a6 a7
             y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 t3 t4 t5 t6)
        F (Z_to_bv 64 0x8ce38) fc None m1 (seg_rom rsegs)).
Proof.
  intros. subst. eapply mn_fin_holds; eassumption.
Qed.

(* ---------- the dispatch ---------- *)

(* br v: the branch condition at the pc is v. *)
Local Ltac br v :=
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) =>
      replace cnd with v;
      [ cbv iota
      | symmetry; unfold_cond; rewrite ?unsigned_lit by lia; fold_lit_ux; solve_cond_rec ]
  end.

(* The 1-byte check of c + 24 (addi a0,s2,24; srli a1,a0,3; add a1,a1,s8; lb a1,0(a1); bnez a1; and when the
   shadow byte k is not 0: andi a2,a0,7; blt a2,a1 back to the access); R24 gives k, RH24 its rng fact. *)
Local Ltac chk24 c k SK MB :=
  step; step; rewrite (unsigned_lit (c + 24)) by lia; rewrite mn_shr3;
  step; step; step;
  destruct SK as [C|[C Cu]];
  [ rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]
  | rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb]; step; step;
    rewrite land7, (unsigned_lit (c + 24)) by lia;
    rewrite (lts_low ((c + 24) mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb] ].

Theorem mn_body_of : mn_sys_F -> mn_chan_F -> mn_body_F.
Proof.
  unfold mn_sys_F, mn_chan_F, mn_body_F. intros HSYS HCH.
  intros RNG sp0 ra0 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
    t3 t4 t5 t6 F fc m c mp body bb mj pos st CTX.
  pose proof CTX as (HPOS & HST & HMJ & HSP & APS1 & APS2 & FR & CUR & MSG & BB & ADC & ADM & ADB & OFC & OFM & OFB
    & D1 & D2 & D3 & RFR & RC & RM & RB & RSC & RSM & RSB).
  pose proof (mn_at8_range bb pos) as X0.
  assert (Hst : st = 0 \/ 128 <= st < 240) by exact HST.
  pose proof (u64_range sp0) as Rsp.
  pose proof ADC as (C0 & _ & CE & ABC).
  pose proof ADM as (M0 & _ & ME & _).
  unfold APPMEM_END in CE, ME.
  (* the shadow bytes the code reads: the granule of c + 16 (0) and the byte k24 of c + 24 *)
  pose proof (mn_granule0 m c 25 (c + 16) ADC ltac:(lia) ltac:(lia)) as M16.
  destruct (ABC 24 ltac:(lia)) as (AP24 & k24 & M24 & SK24).
  clear ABC.
  pose proof (mn_sh_outside m (bv_unsigned sp0) c mp (c + 24) APS1 APS2 ADC ADM AP24) as O24.
  assert (RH16 : ExecF.rng RNG (shadow_addr (c + 16)) 1)
    by (eapply rng_sub'; [exact RSC|]; unfold shadow_addr; Z.div_mod_to_equations; lia).
  assert (RH24 : ExecF.rng RNG ((c + 24) / 8 + ASAN_K) 1)
    by (eapply rng_sub'; [exact RSC|]; unfold shadow_addr; Z.div_mod_to_equations; lia).
  pose proof (rd1 _ _ _ M16) as R16.
  change (wa (shadow_addr (c + 16))) with (Z_to_bv 64 (shadow_addr (c + 16))) in R16.
  pose proof (Z.mod_pos_bound (c + 24) 8 ltac:(lia)) as MB24.
  unfold MN_FRAME in HSP, APS1, APS2, FR, OFC, OFM, OFB, RFR |- *.
  unfold MN_RET_MEMSET.
  unfold off_stk in OFC, OFM, OFB.
  unfold mn_fr in FR. unfold PCur.cursor_cells in CUR. unfold mn_msg0 in MSG.
  pose proof (munch_refl [(bv_unsigned sp0 - 128, bv_unsigned sp0); (c, c + 25); (mp, mp + 40)] m) as MU.
  (* 0x82208 li a0,240; 0x8220c bne s10,a0 *)
  step. step.
  destruct (Z.eq_dec (at8 bb pos) 240) as [E240|N240].
  { (* 0x82210: body[pos] = 0xf0 *)
    br false. eapply HSYS; [exact CTX | exact E240]. }
  br true.
  (* 0x82264 slli a0,s10,56; 0x82268 bltz a0 *)
  step. rewrite (unsigned_lit (at8 bb pos)) by lia.
  step. rewrite mn_sl56 by lia.
  destruct (Z.leb_spec 128 (at8 bb pos)) as [X128|X128]; cbv iota.
  - (* 0x82360 li a0,240; 0x82364 addi a2,s3,1; 0x82368 bltu s10,a0 *)
    step. step. step.
    destruct (Z.ltb_spec (at8 bb pos) 240) as [XL|XL].
    + (* 0x823b4 li a5,0: a status byte 0x80 .. 0xef, its data from pos + 1 *)
      br true. step.
      replace (Z.of_nat pos + 1) with (Z.of_nat (S pos)) by lia.
      eapply HCH; [exact CTX | lia | left; reflexivity | lia | apply mn_rs_stat; lia].
    + (* 0x8236c lbu a0,0(s7): the shadow byte of the granule of c + 16; 0x82370 bnez a0 *)
      br false.
      step. rewrite mn_zxb0. step. br false.
      (* 0x82374 sd a2,16(s2): c + 16 := pos + 1 *)
      step.
      match goal with MU' : munch _ m ?mm |- _ => rename mm into m2 end.
      pose proof (mn_mrd_munch _ m m2 _ _ MU O24 M24
        ltac:(unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia)) as M24'.
      pose proof (rd1 _ _ _ M24') as R24.
      change (wa (shadow_addr (c + 24))) with (Z_to_bv 64 ((c + 24) / 8 + ASAN_K)) in R24.
      (* 0x82378-0x82388, 0x825e4-0x825e8: the 1-byte check of c + 24 *)
      chk24 c k24 SK24 MB24.
      (* 0x8238c sb zero,0(a0): c + 24 := 0; 0x82390 li a0,-8; 0x82394 j 0x82528 *)
      all: step; step; step.
      all: eapply mn_fin_at with (r := mr_plain MkBadStatus pos (S pos) 0 0);
        [ unfold MN_FRAME; lia | exact RFR | eassumption | exact MU | eassumption | exact MSG
        | apply mn_rs_bad; lia | reflexivity | cbn [mr_pos mr_plain]; f_equal; lia | reflexivity ].
  - (* 0x8226c-0x8227c, 0x82590-0x82594: the 1-byte check of c + 24 *)
    pose proof (rd1 _ _ _ M24) as R24.
    change (wa (shadow_addr (c + 24))) with (Z_to_bv 64 ((c + 24) / 8 + ASAN_K)) in R24.
    chk24 c k24 SK24 MB24.
    (* 0x82280 lbu s10,0(a0): s10 = st; 0x82284 beqz s10 *)
    all: step; rewrite (mn_zxb_b8 st) by lia.
    all: step.
    all: destruct (Z.eq_dec st 0) as [S0|S0].
    (* st = 0: 0x82398 lbu a0,0(s7), the shadow byte of the granule of c + 16; 0x8239c bnez a0; 0x823a0 addi s3,s3,1;
       0x823a4 ld a0,16(sp) (c + 16); 0x823a8 sd s3,0(a0): c + 16 := pos + 1; 0x823ac li a0,-7; 0x823b0 j 0x82528 *)
    1, 3: br true; step; rewrite mn_zxb0; step; br false;
          step; step; step; step; step;
          eapply mn_fin_at with (r := mr_plain MkNoStatus pos (S pos) st 0);
          [ unfold MN_FRAME; lia | exact RFR | eassumption | exact MU | eassumption | exact MSG
          | apply mn_rs_nostatus; lia | reflexivity | cbn [mr_pos mr_plain]; f_equal; lia | reflexivity ].
    (* st <> 0: 0x82288 li a5,1; 0x8228c mv a2,s3; 0x82290 j 0x823b8: the running status st, its data from pos *)
    all: br false; step; step; step.
    all: eapply HCH; [exact CTX | lia | right; reflexivity | lia | apply mn_rs_run; lia].
Qed.
