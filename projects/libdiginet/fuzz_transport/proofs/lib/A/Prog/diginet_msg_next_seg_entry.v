(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: twin of lib/AZ/LibA/StepF.v over lib.Lib. *)
(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_decode to libdiginet/fuzz_decode image A; module paths changed *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libdiginet/fuzz_decode/lib/Lib/StepF.v to libdiginet/fuzz_codec; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/Lib/StepF.v; 416 of its 450 lines of code are new or changed and 688 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/diginet_msg_next_seg_chan.v; 201 of its 239 lines of code are new or changed and 412 lines of the source are left out. *)
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

(* Proof of mn_entry_F: the run of diginet_msg_next (image A) from 0x820e8 to the return (pos >= len) or to the
   memset call at 0x82204 (jal 0x51180). Each shadow byte the code loads is read through the munch fact from the entry memory:
   it lies outside the frame [sp - 128, sp) and the message [mp, mp + 40), the only bytes the run writes. *)

Lemma mn_shadow_not_app : forall x, app_mem x -> ~ app_mem (x / 8 + ASAN_K).
Proof.
  intros x H. unfold app_mem, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. Z.div_mod_to_equations. lia.
Qed.

(* The shadow byte of an application byte lies outside the frame and the message. *)
Lemma mn_sh_outside : forall m s p x, app_mem (s + -128) -> app_mem (s - 1) -> addressable m p 40 -> app_mem x ->
  outside [(s + -128, s); (p, p + 40)] (x / 8 + ASAN_K).
Proof.
  intros m s p x A1 A2 (P0 & N0 & PE & AB) Ax. pose proof (mn_shadow_not_app x Ax) as N.
  cbn [outside]. split; [|split; [|exact I]]; intros W; apply N.
  - unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia.
  - destruct (AB (x / 8 + ASAN_K - p) ltac:(lia)) as (Ay & _).
    replace (p + (x / 8 + ASAN_K - p)) with (x / 8 + ASAN_K) in Ay by lia. exact Ay.
Qed.

Lemma mn_signed0 : forall k : byte, bv_signed k = 0 -> k = Z_to_bv 8 0.
Proof.
  intros k H. apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 0) with 0.
  pose proof (bv_unsigned_in_range 8 k) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in H.
  change (2 ^ Z.of_N 8) with 256 in H. change (256 / 2) with 128 in H.
  Z.div_mod_to_equations. lia.
Qed.

(* A shadow byte read after the run's stores: the byte the entry memory holds. *)
Lemma mn_rd_sh : forall m m' s p a b x,
  munch [(s + -128, s); (p, p + 40)] m m' ->
  app_mem (s + -128) -> app_mem (s - 1) -> addressable m p 40 ->
  app_mem x -> x / 8 = a -> mrd rsegs m (wa (a + 2147450880)) = Some b ->
  ov_read_bytes rsegs m' (Z_to_bv 64 (a + 2147450880)) 1 = Some [b].
Proof.
  intros m m' s p a b x MU A1 A2 AP Ax Ea H. subst a.
  pose proof (mn_sh_outside m s p x A1 A2 AP Ax) as O. unfold ASAN_K in O.
  apply rd1. unfold mrd in *. rewrite MU; [exact H|].
  rewrite wa_unsigned; [exact O|].
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Ax. Z.div_mod_to_equations. lia.
Qed.

(* The 8-byte access at q + o (o a multiple of 8, o + 8 <= n): the shadow byte of its granule is 0. *)
Lemma mn_rd_gran : forall m m' s p q n o,
  munch [(s + -128, s); (p, p + 40)] m m' ->
  app_mem (s + -128) -> app_mem (s - 1) -> addressable m p 40 ->
  addressable m q n -> 0 <= o -> o mod 8 = 0 -> o + 8 <= n ->
  ov_read_bytes rsegs m' (Z_to_bv 64 ((q + o) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 0].
Proof.
  intros m m' s p q n o MU A1 A2 AP AQ Ho Ho8 Hn. pose proof AQ as (Q0 & N0 & QE & AB).
  pose proof (Z.mod_pos_bound q 8 ltac:(lia)) as Mq.
  destruct (AB (o + 7 - q mod 8) ltac:(lia)) as (APP & k & MK & SK).
  assert (E1 : (q + (o + 7 - q mod 8)) mod 8 = 7) by (Z.div_mod_to_equations; lia).
  assert (E2 : (q + (o + 7 - q mod 8)) / 8 = (q + o) / 8) by (Z.div_mod_to_equations; lia).
  unfold shadow_addr, shadow_ok, ASAN_K in MK, SK. rewrite E2 in MK. rewrite E1 in SK.
  assert (K0 : k = Z_to_bv 8 0) by (apply mn_signed0; lia). subst k.
  exact (mn_rd_sh m m' s p _ _ _ MU A1 A2 AP APP E2 MK).
Qed.

(* The 1-byte access at q + i: its shadow byte k, with k = 0 or (q + i) mod 8 < k. *)
Lemma mn_rd_byte : forall m m' s p q n i,
  munch [(s + -128, s); (p, p + 40)] m m' ->
  app_mem (s + -128) -> app_mem (s - 1) -> addressable m p 40 ->
  addressable m q n -> 0 <= i < n ->
  exists k, ov_read_bytes rsegs m' (Z_to_bv 64 ((q + i) / 8 + 2147450880)) 1 = Some [k] /\
            (bv_signed k = 0 \/ ((q + i) mod 8 < bv_signed k /\ bv_signed k <= 7)).
Proof.
  intros m m' s p q n i MU A1 A2 AP AQ Hi. pose proof AQ as (Q0 & N0 & QE & AB).
  destruct (AB i Hi) as (APP & k & MK & SK). exists k. split; [|exact SK].
  unfold shadow_addr, ASAN_K in MK. exact (mn_rd_sh m m' s p _ _ _ MU A1 A2 AP APP eq_refl MK).
Qed.

Lemma mn_srl3 : forall x, 0 <= x < 2^64 -> Z.shiftr (bv_unsigned (Z_to_bv 64 x)) 3 = x / 8.
Proof.
  intros x Hx. rewrite unsigned_lit by exact Hx. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

(* A byte the run does not write, read after its stores. *)
Lemma mn_rd_keep : forall m m' W a b, munch W m m' -> outside W a -> 0 <= a < 2^64 ->
  mrd rsegs m (wa a) = Some b -> ov_read_bytes rsegs m' (Z_to_bv 64 a) 1 = Some [b].
Proof.
  intros m m' W a b MU O Ha H. apply rd1. unfold mrd in *. rewrite MU; [exact H|].
  rewrite wa_unsigned by exact Ha. exact O.
Qed.

(* The same bytes under other cells. *)
Lemma mn_rw_conv : forall m A cs cs', rw_cells rsegs m A cs -> cells_wf cs' ->
  cells_bytes cs' = cells_bytes cs -> rw_cells rsegs m A cs'.
Proof.
  intros m A cs cs' [[W B] V] W' EB. split; [split|].
  - exact W'.
  - rewrite EB. exact B.
  - rewrite <- (cells_bytes_length cs' W'), EB, (cells_bytes_length cs W). exact V.
Qed.

Lemma mn_firstn_add : forall (l : list byte) n k, firstn n l ++ firstn k (skipn n l) = firstn (n + k) l.
Proof.
  intros l n; revert l; induction n as [|n IH]; intros l k; [reflexivity|].
  destruct l as [|x l]; cbn [firstn skipn app Nat.add].
  - destruct k; reflexivity.
  - f_equal. apply IH.
Qed.

(* The message at the call: the cells the three stores (m + 24, m + 3, m + 2) left, as mn_msg_pre. *)
Lemma mn_msg_conv : forall m A (mj : list byte) (v : word), length mj = 40%nat ->
  rw_cells rsegs m A [CB 2 (firstn 2 (firstn 3 (firstn 24 mj))); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
                      CB 20 (skipn 4 (firstn 24 mj)); C8 v; CB 8 (skipn 32 mj)] ->
  rw_cells rsegs m A [C1 (nth 0 mj (b8 0)); C1 (nth 1 mj (b8 0)); C1 (b8 0); C1 (b8 0);
                      CB 4 (firstn 4 (skipn 4 mj)); CB 16 (firstn 16 (skipn 8 mj)); C8 v; CB 8 (skipn 32 mj)].
Proof.
  intros m A mj v L H.
  destruct mj as [|b0 [|b1 [|b2 [|b3 r]]]]; try discriminate L.
  assert (LR : length r = 36%nat) by (cbn in L; lia).
  eapply mn_rw_conv; [exact H| |].
  - cbn [cells_wf cell_wf skipn firstn]. rewrite ?length_firstn, ?length_skipn, ?LR. repeat split.
  - cbn [cells_bytes cbytes firstn skipn nth app].
    replace (firstn 20 r) with (firstn 4 r ++ firstn 16 (skipn 4 r)) by (apply (mn_firstn_add r 4 16)).
    change (skipn 0 r) with r.
    change (skipn 0 (firstn 4 r ++ firstn 16 (skipn 4 r))) with (firstn 4 r ++ firstn 16 (skipn 4 r)).
    rewrite <- app_assoc. reflexivity.
Qed.

Ltac shr3 := rewrite mn_srl3 by lia.
Ltac curm := lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => mm end.
(* A branch whose condition compares words Z_to_bv 64 z with z in range. *)
Ltac br v := lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) =>
      replace cnd with v; [cbv iota | symmetry; unfold_cond; fold_lit_ux; rewrite ?unsigned_lit by lia; solve_cond_rec]
  end.

(* The instrumented 1-byte check at a branch `bnez k`: both of its exits continue at the access (pc) with the
   registers as they are, but a1, which the second exit writes (andi a1, _, 7). K is that continuation. *)
Ltac cont_a1 K pc :=
  lazymatch goal with |- evtF ?sg ?RN ?Q (MS ?R ?F _ ?fc ?rv ?mm ?ro) =>
    assert (K : forall v : word, evtF sg RN Q (MS (@bvmap_set 5 word (Z_to_bv 5 11) v R) F (Z_to_bv 64 pc) fc rv mm ro))
  end.
Ltac use_a1 K := let v := reg_val 11 in exact (K v).
(* The two exits of the check: k = 0 falls through; else (a mod 8) < k, and blt goes back to the access. *)
Ltac chk1 K SK k a :=
  destruct SK as [Ck|[Ck Ck']];
  [ rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) Ck); cbn [negb]; use_a1 K
  | rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb]; step; step;
    rewrite land7, (unsigned_lit a) by lia;
    rewrite (lts_low (a mod 8) k ltac:(apply Z.mod_pos_bound; lia)), (proj2 (Z.ltb_lt _ _) Ck); cbn [negb];
    use_a1 K ].

Theorem mn_entry_holds : mn_entry_F.
Proof.
  unfold mn_entry_F, MN_ENTRY, MN_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    c mp body bb mj pos st lo E0 E1 Hc Hmp Hpos Hst LJ ST HLO APS1 APS2 CELLS OFFG OFFK CC CM ADC ADM OFFC OFFM D1
    BODY RFR RGOT RCELL RCUR RMSG RSHC RSHM RBODY.
  subst a0 a1.
  pose proof (u64_range sp) as Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  pose proof ADC as (C0 & _ & CE & _). pose proof ADM as (M0 & _ & ME & _).
  unfold APPMEM_END in CE, ME.
  destruct CELLS as (CK & GCK & _).
  unfold PCur.cursor_cells in CC.
  unfold off_stk, GOT_CELL_K, CELL_K in *.
  unfold shadow_addr, ASAN_K in RSHC, RSHM.
  carve_frame 128%nat ST.
  pose proof (munch_refl [(bv_unsigned sp + -128, bv_unsigned sp); (mp, mp + 40)] m) as MU.
  (* 0x820e8 addi sp; 0x820ec .. 0x8211c: ra, s0 .. s11 into the frame *)
  do 14 step.
  (* 0x82120 mv s2, a0; 0x82124 li a0, -1; 0x82128 beqz s2: c <> 0 *)
  step. step. step. br false.
  (* 0x8212c mv s1, a1; 0x82130 beqz a1: mp <> 0 *)
  step. step. br false.
  (* 0x82134 auipc; 0x82138 ld GOT_CELL_K; 0x8213c ld CELL_K: s8 = the shadow offset *)
  let mm := curm in
  assert (RDG : ov_read_bytes rsegs mm (wa 671888) 8 = Some (le8 (wa 707064)))
    by (replace (wa 671888) with (wa (671888 + 0)) by reflexivity;
        rewrite (bytes_at_read rsegs mm 671888 _ 0 8 GCK ltac:(lia)) by (rewrite length_le8; lia); reflexivity);
  assert (RDS : ov_read_bytes rsegs mm (wa 707064) 8 = Some (le8 (wa 2147450880)))
    by (replace (wa 707064) with (wa (707064 + 0)) by reflexivity;
        rewrite (bytes_at_read rsegs mm 707064 _ 0 8 CK ltac:(lia)) by (rewrite length_le8; lia); reflexivity).
  step. step. step.
  clear RDG RDS CK GCK.
  (* 0x82140 addi a2, s2, 16; 0x82144 srli; 0x82148 add: s7 = the shadow address of c + 16 *)
  step. step. shr3. step.
  (* 0x8214c lbu; 0x82150 bnez: the shadow byte of the granule of c + 16 is 0 *)
  let mm := curm in
  pose proof (mn_rd_gran m mm (bv_unsigned sp) mp c 25 16 MU APS1 APS2 ADM ADC ltac:(lia) eq_refl ltac:(lia)) as HR;
  pose proof (rng_sub' _ _ _ ((c + 16) / 8 + 2147450880) 1 RSHC ltac:(Z.div_mod_to_equations; lia)) as RH.
  step. clear HR RH. step. if_false.
  (* 0x82154 addi a0, s2, 8; 0x82158 srli; 0x8215c add; 0x82160 lbu; 0x82164 bnez: the granule of c + 8 *)
  step. step. shr3. step.
  let mm := curm in
  pose proof (mn_rd_gran m mm (bv_unsigned sp) mp c 25 8 MU APS1 APS2 ADM ADC ltac:(lia) eq_refl ltac:(lia)) as HR;
  pose proof (rng_sub' _ _ _ ((c + 8) / 8 + 2147450880) 1 RSHC ltac:(Z.div_mod_to_equations; lia)) as RH.
  step. clear HR RH. step. if_false.
  (* 0x82168 ld s9, 0(a0): len; 0x8216c ld s3, 16(s2): pos; 0x82170 bgeu s3, s9 *)
  step. step. step.
  destruct (Nat.eq_dec pos (length bb)) as [EQ|NE].
  - (* pos = len: 0x8225c li a0, 0; 0x82260 j; 0x82528 .. 0x82560 the epilogue and ret *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) =>
      replace cnd with true; [cbv iota | symmetry; rewrite EQ; unfold bv_ltu; rewrite Z.ltb_irrefl; reflexivity]
    end.
    do 17 step.
    assert (RS : msg_step bb pos st = mr_plain MkEnd pos pos st 0)
      by (unfold msg_step; replace (length bb <=? pos)%nat with true by (symmetry; apply Nat.leb_le; lia);
          reflexivity).
    apply evtF_done. left. unfold mn_post. rewrite RS.
    cbn [mr_code mr_pos mr_st mr_plain mr_kind].
    do 15 eexists. split; [cbv delta [mkR]; reflexivity|].
    split; [eapply munch_weaken; [|exact MU]; intros x Hx; unfold MN_FRAME in Hx; cbn [outside] in *; lia|].
    split; [exact CC | exact CM].
  - (* pos < len *)
    assert (Hlt : (pos < length bb)%nat) by lia.
    destruct (BODY Hlt) as (BB & ADB & OFFB & D2 & D3). destruct (RBODY Hlt) as (RB & RSHB).
    clear BODY RBODY. unfold shadow_addr, ASAN_K in RSHB.
    pose proof (bytes_at_bound rsegs m body bb BB) as BBb.
    br false.
    (* 0x82174 srli a0, s2, 3; 0x82178 add; 0x8217c lbu; 0x82180 bnez: the granule of c *)
    step. shr3. step.
    let mm := curm in
    pose proof (mn_rd_gran m mm (bv_unsigned sp) mp c 25 0 MU APS1 APS2 ADM ADC ltac:(lia) eq_refl ltac:(lia)) as HR;
    pose proof (rng_sub' _ _ _ (c / 8 + 2147450880) 1 RSHC ltac:(Z.div_mod_to_equations; lia)) as RH.
    rewrite Z.add_0_r in HR.
    step. clear HR RH. step. if_false.
    (* 0x82184 ld s11, 0(s2): body; 0x82188 add s5, s11, s3: body + pos; 0x8218c srli; 0x82190 add *)
    step. step. step. shr3. step.
    (* 0x82194 lb a0: the shadow byte kb of body + pos; 0x82198 bnez *)
    let mm := curm in
    destruct (mn_rd_byte m mm (bv_unsigned sp) mp body (Z.of_nat (length bb)) (Z.of_nat pos) MU APS1 APS2 ADM ADB
                ltac:(lia)) as (kb & HR & SKb);
    pose proof (rng_sub' _ _ _ ((body + Z.of_nat pos) / 8 + 2147450880) 1 RSHB ltac:(Z.div_mod_to_equations; lia))
      as RH.
    step. clear HR RH. step.
    cont_a1 K1 0x8caac.
    2: chk1 K1 SKb kb (body + Z.of_nat pos).
    intros v1. simp_regs.
    (* 0x8219c addi a0, s1, 24; 0x821a0 srli; 0x821a4 add; 0x821a8 lbu; 0x821ac bnez: the granule of mp + 24 *)
    step. step. shr3. step.
    let mm := curm in
    pose proof (mn_rd_gran m mm (bv_unsigned sp) mp mp 40 24 MU APS1 APS2 ADM ADM ltac:(lia) eq_refl ltac:(lia)) as HR;
    pose proof (rng_sub' _ _ _ ((mp + 24) / 8 + 2147450880) 1 RSHM ltac:(Z.div_mod_to_equations; lia)) as RH.
    step. clear HR RH. step. if_false.
    (* 0x821b0 lbu s10, 0(s5): body[pos] *)
    let mm := curm in
    pose proof (mn_rd_keep m mm _ (body + Z.of_nat pos) _ MU ltac:(cbn [outside]; repeat split; lia) ltac:(lia)
                  (bytes_nth m body bb pos BB Hlt)) as HR.
    step. clear HR.
    (* 0x821b4 sd s3, 24(s1): m + 24 := pos *)
    step.
    (* 0x821b8 addi a0, s1, 3; 0x821bc srli; 0x821c0 add; 0x821c4 sd a1, 8(sp): the shadow address of m + 3 *)
    step. step. shr3. step. step.
    (* 0x821c8 lb a3: the shadow byte k3 of m + 3; 0x821cc bnez *)
    let mm := curm in
    destruct (mn_rd_byte m mm (bv_unsigned sp) mp mp 40 3 MU APS1 APS2 ADM ADM ltac:(lia)) as (k3 & HR & SK3);
    pose proof (rng_sub' _ _ _ ((mp + 3) / 8 + 2147450880) 1 RSHM ltac:(Z.div_mod_to_equations; lia)) as RH.
    step. clear HR RH. step.
    cont_a1 K2 0x8cae0.
    2: chk1 K2 SK3 k3 (mp + 3).
    intros v2. simp_regs.
    (* 0x821d0 sd a0, 0(sp); 0x821d4 sd a2, 16(sp); 0x821d8 sb zero, 3(s1) *)
    step. step. step.
    (* 0x821dc addi s4, s1, 2; 0x821e0 srli; 0x821e4 add: s0 = the shadow address of m + 2 *)
    step. step. shr3. step.
    (* 0x821e8 lb a0: the shadow byte k2 of m + 2; 0x821ec bnez *)
    let mm := curm in
    destruct (mn_rd_byte m mm (bv_unsigned sp) mp mp 40 2 MU APS1 APS2 ADM ADM ltac:(lia)) as (k2 & HR & SK2);
    pose proof (rng_sub' _ _ _ ((mp + 2) / 8 + 2147450880) 1 RSHM ltac:(Z.div_mod_to_equations; lia)) as RH.
    step. clear HR RH. step.
    cont_a1 K3 0x8cb00.
    2: chk1 K3 SK2 k2 (mp + 2).
    intros v3. simp_regs.
    (* 0x821f0 addi s6, s1, 8; 0x821f4 sb zero, 0(s4); 0x821f8 li a2, 16; 0x821fc mv a0, s6; 0x82200 li a1, 0;
       0x82204 jal 0x51180 (ra = 0x82208, a0 = m + 8, a1 = 0, a2 = 16) *)
    do 6 step.
    apply evtF_done. right. split; [exact Hlt|].
    unfold mn_call, MN_RET_MEMSET, MN_MEMSET, MN_FRAME.
    do 13 eexists. split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact FR|].
    apply mn_msg_conv; [exact LJ | exact CM].
Qed.
