(* Modified by Theorem Labs, 2026-10: the footprint walk of diginet_cursor_init in libdiginet/fuzz_frame's image A (fuzz_frame.asan), after proofs/libreac/fuzz_decode/lib/A/Prog/reac_frame_counter_F.v (StepF's step, the frame carve, the asan shadow loads), with the four stores to the caller's cursor. *)
(* Modified by Theorem Labs, 2026-10: libdiginet/fuzz_frame image B's copy of this unit's image-A walk lib/A/Prog/diginet_cursor_init_F.v for fuzz_frame.asan-ubsan: Img0 / AsanCells / AsanKA / AsanKAProof / the statements are lib/B's, every address is image B's (entry 0x83300; the GOT word 0x9a8e8 and the cell 0xa28b8 of asan_cells), and two steps more: the UBSan alignment check of c (0x8330c `andi a3,a0,7`, 0x83310 `bnez a3`), not taken by the premise c mod 8 = 0. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA AsanKAProof diginet_cursor_init_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_cursor_init_F_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* Proof of diginet_cursor_init_contract_F (image B, entry 0x82270). The walk steps every instruction with StepF's
   step; each access side goal is closed from an rng fact for the accessed range: the frame [sp - 16, sp), the two
   asan_cells cells, the cursor [c, c + 25), and, before each shadow load at h = (a >> 3) + ASAN_K, rng RNG h 1 (a
   sub-range of the cursor's shadow range).
   The UBSan alignment check of c (0x8227c `andi a3,a0,7`, 0x82280 `bnez a3` to the `unimp` word at 0x82304) reads
   a register only; c mod 8 = 0 makes a3 = 0, so the branch is not taken.
   The four error paths (the calls of errpath_store8 / errpath_store1) are not reached: addressable m c 25 gives
   shadow byte 0 for each of the three 8-byte granules that hold c, c + 8 and c + 16 (cinit_granule reads the
   shadow byte of the granule's last byte, which lies in [c, c + 25) and has address mod 8 = 7), and for the 1-byte
   store at c + 24 its shadow byte k is 0 or (c + 24) mod 8 < k, which is the compare at 0x82308-0x8230c.
   The stores leave the shadow bytes as they were: they lie outside the frame and the cursor (cinit_sh_outside), the
   only ranges the run changes. *)

Lemma cinit_signed0 : forall k : byte, bv_signed k = 0 -> k = Z_to_bv 8 0.
Proof.
  intros k H. apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 0) with 0.
  pose proof (bv_unsigned_in_range 8 k) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in H.
  change (2 ^ Z.of_N 8) with 256 in H. change (256 / 2) with 128 in H.
  Z.div_mod_to_equations. lia.
Qed.

Lemma cinit_shadow_not_app : forall x, app_mem x -> ~ app_mem (x / 8 + ASAN_K).
Proof.
  intros x H. unfold app_mem, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. Z.div_mod_to_equations. lia.
Qed.

(* The shadow byte of an application byte lies outside the frame [s - 16, s) and the cursor [p, p + 25). *)
Lemma cinit_sh_outside : forall m s p x, app_mem (s - 16) -> app_mem (s - 1) -> addressable m p 25 -> app_mem x ->
  outside [(s - 16, s); (p, p + 25)] (x / 8 + ASAN_K).
Proof.
  intros m s p x A1 A2 (P0 & N0 & PE & AB) Ax. pose proof (cinit_shadow_not_app x Ax) as N.
  cbn [outside]. split; [|split; [|exact I]]; intros W; apply N.
  - unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia.
  - destruct (AB (x / 8 + ASAN_K - p) ltac:(lia)) as (Ay & _).
    replace (p + (x / 8 + ASAN_K - p)) with (x / 8 + ASAN_K) in Ay by lia. exact Ay.
Qed.

(* The shadow byte of the 8-byte granule of p + 8 j (j < 3) is 0, and it lies outside the frame and the cursor. *)
Lemma cinit_granule : forall m s p j, app_mem (s - 16) -> app_mem (s - 1) -> addressable m p 25 -> 0 <= j <= 2 ->
  outside [(s - 16, s); (p, p + 25)] ((p + 8 * j) / 8 + ASAN_K) /\
  mrd rsegs m (wa ((p + 8 * j) / 8 + ASAN_K)) = Some (Z_to_bv 8 0).
Proof.
  intros m s p j A1 A2 ADR Hj. pose proof ADR as (P0 & N0 & PE & AB).
  pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as Mp.
  destruct (AB (8 * j + 7 - p mod 8) ltac:(lia)) as (APP & k & MK & SK).
  assert (E1 : (p + (8 * j + 7 - p mod 8)) mod 8 = 7) by (Z.div_mod_to_equations; lia).
  assert (E2 : (p + (8 * j + 7 - p mod 8)) / 8 = (p + 8 * j) / 8) by (Z.div_mod_to_equations; lia).
  pose proof (cinit_sh_outside m s p _ A1 A2 ADR APP) as O. rewrite E2 in O.
  split; [exact O|].
  unfold shadow_addr, shadow_ok in MK, SK. rewrite E2 in MK. rewrite E1 in SK.
  rewrite MK. f_equal. apply cinit_signed0. lia.
Qed.

Lemma cinit_mrd_munch : forall W m m' a b, munch W m m' -> outside W a ->
  mrd rsegs m (wa a) = Some b -> 0 <= a < 2^64 -> mrd rsegs m' (wa a) = Some b.
Proof.
  intros W m m' a b MU Ho H Ha. unfold mrd in *. rewrite MU; [exact H|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

Lemma cinit_zxb0 : zxb (Z_to_bv 8 0) = Z_to_bv 64 0.
Proof. apply bv_eq. reflexivity. Qed.

(* The cursor's cells from its four written pieces. *)
Lemma cinit_cells : forall m p (v0 v1 v2 : word) (b : byte),
  bytes_at rsegs m p (le8 v0) -> bytes_at rsegs m (p + 8) (le8 v1) -> bytes_at rsegs m (p + 16) (le8 v2) ->
  bytes_at rsegs m (p + 24) [b] -> wr_at rsegs m p 25 ->
  rw_cells rsegs m p [C8 v0; C8 v1; C8 v2; C1 b].
Proof.
  intros m p v0 v1 v2 b B0 B1 B2 B3 W. split; [split|].
  - cbn. repeat split.
  - cbn [cells_bytes cbytes app].
    apply bytes_at_app. split; [exact B0|]. rewrite length_le8.
    apply bytes_at_app. split; [replace (p + Z.of_nat 8) with (p + 8) by lia; exact B1|]. rewrite length_le8.
    apply bytes_at_app. split; [replace (p + Z.of_nat 8 + Z.of_nat 8) with (p + 16) by lia; exact B2|].
    rewrite length_le8. replace (p + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) with (p + 24) by lia. exact B3.
  - cbn [cells_size csize Nat.add]. change (Z.of_nat 25) with 25. exact W.
Qed.

(* The value stored at c + 8 (0x822b8-0x822c0: seqz, addi -1, and): len, or 0 when body = 0. *)
Lemma cinit_len : forall a1 a2 : word,
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltiu a1 1) + -1))) (bv_unsigned a2)) =
  Z_to_bv 64 (if bv_unsigned a1 =? 0 then 0 else bv_unsigned a2).
Proof.
  intros a1 a2. pose proof (u64_range a1) as R1. pose proof (u64_range a2) as R2.
  unfold v_sltiu. change (bv_wrap 64 1) with 1.
  destruct (Z.eqb_spec (bv_unsigned a1) 0) as [E|E].
  - rewrite E. change (0 <? 1) with true. cbv iota.
    match goal with |- context [Z.land ?x (bv_unsigned a2)] => replace x with 0 by (vm_compute; reflexivity) end.
    rewrite Z.land_0_l. reflexivity.
  - rewrite (proj2 (Z.ltb_ge (bv_unsigned a1) 1)) by lia. cbv iota.
    match goal with |- context [Z.land ?x (bv_unsigned a2)] => replace x with (Z.ones 64) by (vm_compute; reflexivity) end.
    rewrite Z.land_comm, Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

(* A store to the cursor: name its address wa E, carry the facts across it, add the bytes it wrote (B) and name the
   memory after it m'. *)
Ltac cstore E EQ B m' :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?mk ?a ?bs) ?ro) =>
      replace (write_to_mem mk a bs) with (write_to_mem mk (wa E) bs)
        by (f_equal; first [ exact EQ | exact (eq_sym EQ) ]);
      transport_chunks segs mk E bs;
      footprint_after_store segs mk E bs;
      pose proof (bytes_at_write_same segs mk E bs ltac:(lia) ltac:(simpl_sizes; lia)) as B;
      set (m' := write_to_mem mk (wa E) bs) in *; clearbody m'; try clear mk
  end.

Theorem diginet_cursor_init_holds_F : diginet_cursor_init_contract_F.
Proof.
  unfold diginet_cursor_init_contract_F, DIGINET_CURSOR_INIT, DIGINET_CURSOR_INIT_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    c body len lo E0 E1 E2 Rc Hc0 Rb Rl AL8 ST HLO WR OFFC APS1 APS2 CELLS OFFG OFFK ADR RFR RGOT RCELL RCUR RSH.
  assert (Uc : bv_unsigned a0 = c) by (subst a0; apply unsigned_lit; lia).
  assert (Ub : bv_unsigned a1 = body) by (subst a1; apply unsigned_lit; lia).
  assert (Ul : bv_unsigned a2 = len) by (subst a2; apply unsigned_lit; lia).
  clear E0 E1 E2. subst c body len.
  pose proof (u64_range sp) as Rsp. pose proof (u64_range a0) as Ra0.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  pose proof ADR as (P0 & N0 & PE & AB).
  unfold APPMEM_END in PE.
  destruct (cinit_granule m (bv_unsigned sp) (bv_unsigned a0) 0 APS1 APS2 ADR ltac:(lia)) as (O0 & MK0).
  destruct (cinit_granule m (bv_unsigned sp) (bv_unsigned a0) 1 APS1 APS2 ADR ltac:(lia)) as (O1 & MK1).
  destruct (cinit_granule m (bv_unsigned sp) (bv_unsigned a0) 2 APS1 APS2 ADR ltac:(lia)) as (O2 & MK2).
  change (8 * 0) with 0 in O0, MK0. rewrite Z.add_0_r in O0, MK0.
  change (8 * 1) with 8 in O1, MK1. change (8 * 2) with 16 in O2, MK2.
  destruct (AB 24 ltac:(lia)) as (AP3 & k3 & MK3 & SK3).
  pose proof (cinit_sh_outside m (bv_unsigned sp) (bv_unsigned a0) _ APS1 APS2 ADR AP3) as O3.
  clear AB.
  destruct CELLS as (CK & GCK & _).
  unfold off_stk, GOT_CELL_K, CELL_K, shadow_addr, shadow_ok in *. unfold ASAN_K in *.
  pose proof (Z.mod_pos_bound (bv_unsigned a0 + 24) 8 ltac:(lia)) as MB3.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 25)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  (* 0x82270 addi sp; 0x82274 sd ra: the frame *)
  step. step.
  match goal with MU' : munch _ m ?m1 |- _ => rename m1 into m0 end.
  (* 0x82278 beqz a0: c <> 0 *)
  step. if_false.
  (* 0x8227c andi a3, a0, 7; 0x82280 bnez a3 (the UBSan check of c): c mod 8 = 0, so a3 = 0 *)
  step. step.
  rewrite land7, AL8. if_false.
  (* 0x82284 auipc; 0x82288 ld GOT_CELL_K; 0x8228c ld CELL_K *)
  assert (RDG : ov_read_bytes rsegs m0 (wa 670960) 8 = Some (le8 (wa 706168))).
  { replace (wa 670960) with (wa (670960 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 670960 _ 0 8 GCK ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
  assert (RDS : ov_read_bytes rsegs m0 (wa 706168) 8 = Some (le8 (wa 2147450880))).
  { replace (wa 706168) with (wa (706168 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 706168 _ 0 8 CK ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
  step. step. step.
  clear RDG RDS CK GCK.
  (* 0x82290-0x8229c: the shadow byte of c is 0 *)
  step. gen_shr a0 g0 G0.
  step. gen_addi g0 h0 H0.
  pose proof (rng_sub' _ _ _ (bv_unsigned h0) 1 RSH ltac:(Z.div_mod_to_equations; lia)) as RH0.
  pose proof (cinit_mrd_munch _ m m0 _ _ MU O0 MK0 ltac:(Z.div_mod_to_equations; lia)) as M0.
  pose proof (rdw0 m0 h0 _ _ M0 ltac:(lia)) as R. step. clear R.
  step. if_false.
  (* 0x822a0 sd a1, 0(a0) *)
  assert (HS0 : store_ok rsegs m0 a0 8 = true).
  { pose proof (wr_at_store_ok rsegs m0 (bv_unsigned a0) 25 0 8 WR ltac:(lia) ltac:(lia)) as S.
    rewrite Z.add_0_r in S. unfold wa in S. rewrite Z_to_bv_bv_unsigned in S. exact S. }
  step. clear HS0 M0.
  cstore (bv_unsigned a0) (eq_sym (Z_to_bv_bv_unsigned a0)) B0 m1.
  (* 0x822a4-0x822b4: the shadow byte of c + 8 is 0 *)
  step. gen_addi a0 w1 U1.
  step. gen_shr w1 g1 G1. rewrite U1 in G1.
  step. gen_addi g1 h1 H1.
  pose proof (rng_sub' _ _ _ (bv_unsigned h1) 1 RSH ltac:(Z.div_mod_to_equations; lia)) as RH1.
  pose proof (cinit_mrd_munch _ m m1 _ _ MU O1 MK1 ltac:(Z.div_mod_to_equations; lia)) as M1.
  pose proof (rdw0 m1 h1 _ _ M1 ltac:(lia)) as R. step. clear R.
  step. if_false.
  (* 0x822b8-0x822c0: len, or 0 when body = 0; 0x822c4 addi a1, a0, 16 *)
  step. step. step.
  step. gen_addi a0 w2 U2.
  (* 0x822c8 sd a2, 8(a0) *)
  pose proof (wr_at_store_ok rsegs m1 (bv_unsigned a0) 25 8 8 WR ltac:(lia) ltac:(lia)) as HS1.
  step. clear HS1 M1.
  cstore (bv_unsigned a0 + 8) (eq_refl (Z_to_bv 64 (bv_unsigned a0 + 8))) B1 m2.
  (* 0x822cc-0x822d8: the shadow byte of c + 16 is 0 *)
  step. gen_shr w2 g2 G2. rewrite U2 in G2.
  step. gen_addi g2 h2 H2.
  pose proof (rng_sub' _ _ _ (bv_unsigned h2) 1 RSH ltac:(Z.div_mod_to_equations; lia)) as RH2.
  pose proof (cinit_mrd_munch _ m m2 _ _ MU O2 MK2 ltac:(Z.div_mod_to_equations; lia)) as M2.
  pose proof (rdw0 m2 h2 _ _ M2 ltac:(lia)) as R. step. clear R.
  step. if_false.
  (* 0x822dc sd zero, 16(a0) *)
  pose proof (wr_at_store_ok rsegs m2 (bv_unsigned a0) 25 16 8 WR ltac:(lia) ltac:(lia)) as HS2.
  step. clear HS2 M2.
  cstore (bv_unsigned a0 + 16) (eq_refl (Z_to_bv 64 (bv_unsigned a0 + 16))) B2 m3.
  (* 0x822e0-0x822ec: the shadow byte k3 of c + 24 *)
  step. gen_addi a0 w3 U3.
  step. gen_shr w3 g3 G3. rewrite U3 in G3.
  step. gen_addi g3 h3 H3.
  pose proof (rng_sub' _ _ _ (bv_unsigned h3) 1 RSH ltac:(Z.div_mod_to_equations; lia)) as RH3.
  pose proof (cinit_mrd_munch _ m m3 _ _ MU O3 MK3 ltac:(Z.div_mod_to_equations; lia)) as M3.
  pose proof (rdw0 m3 h3 _ _ M3 ltac:(lia)) as R. step. clear R.
  (* 0x822f0 bnez a1; when k3 <> 0, 0x82308 andi and 0x8230c blt: (c + 24) mod 8 < k3 *)
  step.
  destruct SK3 as [C3|[C3 C3']].
  1: rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C3); cbn [negb].
  2: rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k3) 0) ltac:(lia)); cbn [negb]; step; step;
     rewrite land7, U3, (lts_low ((bv_unsigned a0 + 24) mod 8) k3 MB3), (proj2 (Z.ltb_lt _ _) C3); cbn [negb].
  (* 0x822f4 sb zero, 0(a0) *)
  all: assert (HS3 : store_ok rsegs m3 w3 1 = true)
         by (rewrite <- (Z_to_bv_bv_unsigned w3), U3;
             exact (wr_at_store_ok rsegs m3 (bv_unsigned a0) 25 24 1 WR ltac:(lia) ltac:(lia))).
  all: pose proof (rng_sub' _ _ _ (bv_unsigned w3) 1 RCUR ltac:(lia)) as RW3.
  all: step.
  all: clear HS3 M3.
  all: assert (EQ3 : w3 = wa (bv_unsigned a0 + 24))
         by (unfold wa; rewrite <- U3; symmetry; apply Z_to_bv_bv_unsigned).
  all: cstore (bv_unsigned a0 + 24) EQ3 B3 m4.
  (* 0x822f8 ld ra; 0x822fc addi sp; 0x82300 ret *)
  all: step; step; step.
  all: apply evtF_done.
  all: do 7 eexists; split; [reflexivity|].
  all: split; [exact MU|].
  all: split; [exact WM|].
  all: split; [release_frame FR ST (bv_unsigned sp); exact ST|].
  (* the cursor's cells: body, len (0 when body = 0), pos 0, status 0 *)
  all: unfold PCur.cursor_cells; rewrite (Z_to_bv_bv_unsigned a1), <- cinit_len.
  all: apply cinit_cells; [exact B0 | exact B1 | exact B2 | exact B3 | exact WR].
Qed.
