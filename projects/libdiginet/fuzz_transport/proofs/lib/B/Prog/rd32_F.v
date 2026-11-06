From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA AsanKAProof rd32_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import rd32_F_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* Proof of rd32_contract_F (rd32_F_c.v; image B, entry 0x8258c, frame 16 bytes), step for step with StepF's step.
   Each access side goal is closed from an rng fact for exactly the accessed range: before the shadow byte load at
   h = ((p + i) >> 3) + ASAN_K (i = 0, 1, 2, 3) the proof adds rng RNG h 1 (a sub-range of the shadow range), and
   before the byte load at p + i it adds rng RNG (p + i) 1 (a sub-range of [p, p + 4)).
   The order of the loads: the shadow byte of p + i + 1 is loaded before the byte at p + i, and the byte at p + i is
   loaded before the test of that shadow byte (0x825c4 / 0x825c8 / 0x825cc and the same for i = 1, 2).
   Each shadow byte k is 0 or (p + i) mod 8 < k (addressable), so each error path (0x82634, 0x82640, 0x82650,
   0x82660: andi, blt) goes back to the next instruction of the main path (0x825b0, 0x825d0, 0x825f4, 0x82608) and
   no errpath_load1 call is reached.
   The two UBSan checks branch to the unimp word at 0x82630 when a0 = 2^64 - 1 (0x825b4 `beq a0,a1`, a1 = -1) or
   when p + 3 < 2 as an unsigned 64-bit value (0x825d8 `bltu a1,a2`, a1 = p + 3, a2 = 2); a0 = p, 0 <= p and
   p + 4 <= APPMEM_END (addressable) refute both.
   The value: 0x82608 `slliw` puts byte 0 at bits 24..31 and copies bit 31 into bits 32..63; 0x82610-0x82620 put
   bytes 1, 2, 3 at bits 16..23, 8..15, 0..7 and `or` the four (rd32_val).
   Template: this unit's lib/B/Prog/diginet_mac_is_digidesign_F.v (the walk form) and lib/U/Prog/rd32.v (the value
   lemma rd32_val and its two helpers). *)

(* The shadow byte of a + i, 0 <= i < n, lies in the shadow range of the bytes [a, a + n). *)
Lemma rd32_shadow_byte_rng : forall RNG a n i, 0 <= i < n ->
  ExecF.rng RNG (shadow_addr a) (shadow_addr (a + n - 1) - shadow_addr a + 1) ->
  ExecF.rng RNG (shadow_addr (a + i)) 1.
Proof.
  intros RNG a n i Hi H. eapply rng_sub'; [exact H|]. unfold shadow_addr. Z.div_mod_to_equations. lia.
Qed.

(* An or of disjoint bit ranges is a sum. *)
Lemma rd32_lor_mul_add : forall a b k, 0 <= a -> 0 <= k -> 0 <= b < 2^k -> Z.lor (a * 2^k) b = a * 2^k + b.
Proof.
  intros a b k Ha Hk Hb.
  assert (L : Z.land (a * 2^k) b = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases n k) as [Hnk|Hnk].
    - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    - rewrite <- (Z.mod_small b (2^k)) by lia. rewrite Z.mod_pow2_bits_high by lia. apply andb_false_r. }
  rewrite <- Z.lxor_lor by exact L. rewrite <- Z.add_nocarry_lxor by exact L. reflexivity.
Qed.

(* bv_swrap 32 of a 32-bit value, as a 64-bit register. *)
Lemma rd32_sw32_u : forall v, -2^31 <= v < 2^32 ->
  bv_unsigned (Z_to_bv 64 (bv_swrap 32 v)) = if v mod 2^32 <? 2^31 then v mod 2^32 else v mod 2^32 + 2^64 - 2^32.
Proof.
  intros v Hv. rewrite unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with (2^31) by reflexivity.
  replace (bv_modulus 32) with (2^32) by reflexivity.
  destruct (Z.ltb_spec (v mod 2^32) (2^31)); Z.div_mod_to_equations; lia.
Qed.

(* The value of a0 at 0x82624: the four bytes, big-endian, sign-extended from bit 31. *)
Lemma rd32_val : forall b0 b1 b2 b3 : byte,
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb b1)) 16)))
                                                  (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.shiftl (bv_unsigned (zxb b0)) 24)))))))
                     (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb b2)) 8)))
                                                     (bv_unsigned (zxb b3))))))
  = sx32 (Z_to_bv 64 (bv_unsigned b0 * 2^24 + bv_unsigned b1 * 2^16 + bv_unsigned b2 * 2^8 + bv_unsigned b3)).
Proof.
  intros b0 b1 b2 b3.
  pose proof (byte_range b0) as X0. pose proof (byte_range b1) as X1.
  pose proof (byte_range b2) as X2. pose proof (byte_range b3) as X3.
  apply bv_eq. unfold zxb, sx32. rewrite !zxb_u, !Z.shiftl_mul_pow2 by lia.
  rewrite (unsigned_lit (bv_unsigned b1 * 2^16)) by lia.
  rewrite (unsigned_lit (bv_unsigned b2 * 2^8)) by lia.
  rewrite (rd32_lor_mul_add (bv_unsigned b2) (bv_unsigned b3) 8) by lia.
  rewrite (unsigned_lit (bv_unsigned b2 * 2^8 + bv_unsigned b3)) by lia.
  rewrite (unsigned_lit (bv_unsigned b0 * 2^24 + bv_unsigned b1 * 2^16 + bv_unsigned b2 * 2^8 + bv_unsigned b3)) by lia.
  rewrite !rd32_sw32_u by lia.
  rewrite (Z.mod_small (bv_unsigned b0 * 2^24 + bv_unsigned b1 * 2^16 + bv_unsigned b2 * 2^8 + bv_unsigned b3)) by lia.
  rewrite (Z.lor_comm (bv_unsigned b1 * 2^16)).
  destruct (Z.ltb_spec (bv_unsigned b0) 128) as [H0|H0].
  - rewrite (Z.mod_small (bv_unsigned b0 * 2^24)) by lia.
    replace (bv_unsigned b0 * 2^24 <? 2^31) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (bv_unsigned b0 * 2^24 + bv_unsigned b1 * 2^16 + bv_unsigned b2 * 2^8 + bv_unsigned b3 <? 2^31)
      with true by (symmetry; apply Z.ltb_lt; lia).
    cbv iota.
    rewrite (rd32_lor_mul_add (bv_unsigned b0) (bv_unsigned b1 * 2^16) 24) by lia.
    rewrite (unsigned_lit (bv_unsigned b0 * 2^24 + bv_unsigned b1 * 2^16)) by lia.
    replace (bv_unsigned b0 * 2^24 + bv_unsigned b1 * 2^16) with ((bv_unsigned b0 * 2^8 + bv_unsigned b1) * 2^16) by ring.
    rewrite (rd32_lor_mul_add (bv_unsigned b0 * 2^8 + bv_unsigned b1) (bv_unsigned b2 * 2^8 + bv_unsigned b3) 16) by lia.
    rewrite unsigned_lit by lia. ring.
  - rewrite (Z.mod_small (bv_unsigned b0 * 2^24)) by lia.
    replace (bv_unsigned b0 * 2^24 <? 2^31) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (bv_unsigned b0 * 2^24 + bv_unsigned b1 * 2^16 + bv_unsigned b2 * 2^8 + bv_unsigned b3 <? 2^31)
      with false by (symmetry; apply Z.ltb_ge; lia).
    cbv iota.
    replace (bv_unsigned b0 * 2^24 + 2^64 - 2^32) with ((bv_unsigned b0 + 2^40 - 2^8) * 2^24) by ring.
    rewrite (rd32_lor_mul_add (bv_unsigned b0 + 2^40 - 2^8) (bv_unsigned b1 * 2^16) 24) by lia.
    rewrite (unsigned_lit ((bv_unsigned b0 + 2^40 - 2^8) * 2^24 + bv_unsigned b1 * 2^16)) by lia.
    replace ((bv_unsigned b0 + 2^40 - 2^8) * 2^24 + bv_unsigned b1 * 2^16)
      with ((bv_unsigned b0 * 2^8 + 2^48 - 2^16 + bv_unsigned b1) * 2^16) by ring.
    rewrite (rd32_lor_mul_add (bv_unsigned b0 * 2^8 + 2^48 - 2^16 + bv_unsigned b1) (bv_unsigned b2 * 2^8 + bv_unsigned b3) 16)
      by lia.
    rewrite unsigned_lit by lia. ring.
Qed.

Theorem rd32_holds_F : rd32_contract_F.
Proof.
  unfold rd32_contract_F, RD32, RD32_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p l
    lo HLEN BA ST HLO DP APS1 APS2 CELLS DG DC AM RFR RGOT RCELL RP RSH.
  pose proof BA as (BA0 & BA1 & _).
  (* the 4 bytes as mrd facts on m: the store at 0x82590 drops bytes_at for l, whose bytes past p + 4 may lie in
     the frame *)
  pose proof (bytes_nth m _ l 0 BA ltac:(lia)) as BN0.
  pose proof (bytes_nth m _ l 1 BA ltac:(lia)) as BN1.
  pose proof (bytes_nth m _ l 2 BA ltac:(lia)) as BN2.
  pose proof (bytes_nth m _ l 3 BA ltac:(lia)) as BN3.
  clear BA.
  (* the result in terms of the 4 bytes *)
  assert (BE : be32 l 0 = bv_unsigned (nth 0 l (Z_to_bv 8 0)) * 2^24 + bv_unsigned (nth 1 l (Z_to_bv 8 0)) * 2^16
                          + bv_unsigned (nth 2 l (Z_to_bv 8 0)) * 2^8 + bv_unsigned (nth 3 l (Z_to_bv 8 0)))
    by reflexivity.
  rewrite BE. clear BE.
  set (b0 := nth 0 l (Z_to_bv 8 0)) in *. clearbody b0.
  set (b1 := nth 1 l (Z_to_bv 8 0)) in *. clearbody b1.
  set (b2 := nth 2 l (Z_to_bv 8 0)) in *. clearbody b2.
  set (b3 := nth 3 l (Z_to_bv 8 0)) in *. clearbody b3.
  assert (U0 : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  set (a0 := Z_to_bv 64 p) in *. clearbody a0.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2^64) in Rsp.
  carve_frame 16%nat ST.
  (* 0x8258c addi sp; 0x82590 sd ra *)
  step. step.
  pose proof (rd32_shadow_byte_rng RNG p 4 0 ltac:(lia) RSH) as RS0.
  pose proof (rd32_shadow_byte_rng RNG p 4 1 ltac:(lia) RSH) as RS1.
  pose proof (rd32_shadow_byte_rng RNG p 4 2 ltac:(lia) RSH) as RS2.
  pose proof (rd32_shadow_byte_rng RNG p 4 3 ltac:(lia) RSH) as RS3.
  rewrite Z.add_0_r in RS0.
  clear RSH.
  destruct CELLS as (CK & GCK & _).
  destruct AM as (P0 & N0 & PE & AB).
  destruct (AB 0 ltac:(lia)) as (APP0 & k0 & MK0 & SK0).
  destruct (AB 1 ltac:(lia)) as (APP1 & k1 & MK1 & SK1).
  destruct (AB 2 ltac:(lia)) as (APP2 & k2 & MK2 & SK2).
  destruct (AB 3 ltac:(lia)) as (APP3 & k3 & MK3 & SK3).
  clear AB.
  unfold off_stk, GOT_CELL_K, CELL_K, shadow_addr, shadow_ok in *. unfold ASAN_K in *.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in APP0, APP1, APP2, APP3, APS1, APS2, PE.
  rewrite Z.add_0_r in APP0, MK0, SK0.
  match goal with MU' : munch _ m ?m1 |- _ => rename MU' into MU1; rename m1 into m0 end.
  pose proof (bytes_tp m m0 _ _ 670960 (le8 (wa 706168)) MU1 ltac:(rewrite length_le8; lia) GCK) as GOT0.
  pose proof (bytes_tp m m0 _ _ 706168 (le8 (wa 2147450880)) MU1 ltac:(rewrite length_le8; lia) CK) as SV0.
  assert (RDG : ov_read_bytes rsegs m0 (wa 670960) 8 = Some (le8 (wa 706168))).
  { replace (wa 670960) with (wa (670960 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 670960 _ 0 8 GOT0 ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
  assert (RDS : ov_read_bytes rsegs m0 (wa 706168) 8 = Some (le8 (wa 2147450880))).
  { replace (wa 706168) with (wa (706168 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 706168 _ 0 8 SV0 ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
  pose proof (mrd_tp m m0 _ _ (p / 8 + 2147450880) _ MU1
    ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) MK0) as M0.
  pose proof (mrd_tp m m0 _ _ ((p + 1) / 8 + 2147450880) _ MU1
    ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) MK1) as M1.
  pose proof (mrd_tp m m0 _ _ ((p + 2) / 8 + 2147450880) _ MU1
    ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) MK2) as M2.
  pose proof (mrd_tp m m0 _ _ ((p + 3) / 8 + 2147450880) _ MU1
    ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) MK3) as M3.
  pose proof (mrd_tp m m0 _ _ (p + Z.of_nat 0) _ MU1 ltac:(lia) ltac:(lia) BN0) as F0.
  pose proof (mrd_tp m m0 _ _ (p + Z.of_nat 1) _ MU1 ltac:(lia) ltac:(lia) BN1) as F1.
  pose proof (mrd_tp m m0 _ _ (p + Z.of_nat 2) _ MU1 ltac:(lia) ltac:(lia) BN2) as F2.
  pose proof (mrd_tp m m0 _ _ (p + Z.of_nat 3) _ MU1 ltac:(lia) ltac:(lia) BN3) as F3.
  change (Z.of_nat 0) with 0 in F0. change (Z.of_nat 1) with 1 in F1.
  change (Z.of_nat 2) with 2 in F2. change (Z.of_nat 3) with 3 in F3.
  rewrite Z.add_0_r in F0.
  pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as MB0.
  pose proof (Z.mod_pos_bound (p + 1) 8 ltac:(lia)) as MB1.
  pose proof (Z.mod_pos_bound (p + 2) 8 ltac:(lia)) as MB2.
  pose proof (Z.mod_pos_bound (p + 3) 8 ltac:(lia)) as MB3.
  (* 0x82594 auipc; 0x82598 ld a1 (GOT_CELL_K); 0x8259c ld a3 (CELL_K) *)
  step. step. step.
  (* byte 0's shadow: 0x825a0 srli a1,a0,3; 0x825a4 add a1,a1,a3; 0x825a8 lb a1 *)
  step. gen_shr a0 g0 G0.
  rewrite U0 in G0.
  step. gen_addi g0 h0 H0.
  pose proof (rng_sub' _ _ _ (bv_unsigned h0) 1 RS0 ltac:(lia)) as RH0.
  pose proof (rdw0 m0 h0 _ _ M0 ltac:(lia)) as R. step. clear R.
  (* 0x825ac bnez a1; when k0 <> 0: 0x82634 andi a2,a0,7; 0x82638 blt a2,a1 back to 0x825b0 (p mod 8 < k0) *)
  step.
  destruct SK0 as [C0|[C0 Cu0]].
  1: rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C0); cbn [negb].
  2: rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k0) 0) ltac:(lia)); cbn [negb]; step; step;
     rewrite land7, U0, (lts_low (p mod 8) k0 MB0), (proj2 (Z.ltb_lt _ _) C0); cbn [negb].
  (* UBSan check 1: 0x825b0 li a1,-1; 0x825b4 beq a0,a1 (to the unimp word at 0x82630 when a0 = 2^64 - 1) *)
  all: step; step; if_cases HU0; zify_cond HU0; rewrite ?U0 in HU0.
  all: lazymatch type of HU0 with
       | _ <> _ => clear HU0
       | _ = _ => exfalso; first [lia | Z.div_mod_to_equations; lia]
       end.
  (* byte 1's shadow: 0x825b8 addi a1,a0,1; 0x825bc srli a2,a1,3; 0x825c0 add a2,a2,a3; 0x825c4 lb a2 *)
  all: step; gen_addi a0 w1 U1.
  all: rewrite U0 in U1.
  all: step; gen_shr w1 g1 G1.
  all: rewrite U1 in G1.
  all: step; gen_addi g1 h1 H1.
  all: pose proof (rng_sub' _ _ _ (bv_unsigned h1) 1 RS1 ltac:(lia)) as RH1.
  all: pose proof (rdw0 m0 h1 _ _ M1 ltac:(lia)) as R; step; clear R.
  (* byte 0: 0x825c8 lbu a4,0(a0) *)
  all: pose proof (rng_sub' _ _ _ (bv_unsigned a0) 1 RP ltac:(lia)) as RW0.
  all: pose proof (rdw0 m0 a0 _ _ F0 ltac:(lia)) as R; step; clear R.
  (* 0x825cc bnez a2; when k1 <> 0: 0x82640 andi a5,a1,7; 0x82644 blt a5,a2 back to 0x825d0 ((p + 1) mod 8 < k1) *)
  all: step.
  all: destruct SK1 as [C1|[C1 Cu1]].
  all: lazymatch type of C1 with
       | bv_signed _ = 0 => rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C1); cbn [negb]
       | _ =>
           rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k1) 0) ltac:(lia)); cbn [negb]; step; step;
           rewrite land7, U1, (lts_low ((p + 1) mod 8) k1 MB1), (proj2 (Z.ltb_lt _ _) C1); cbn [negb]
       end.
  (* UBSan check 2: 0x825d0 addi a1,a0,3; 0x825d4 li a2,2; 0x825d8 bltu a1,a2 (to the unimp word at 0x82630 when
     p + 3 < 2) *)
  all: step; gen_addi a0 w3 U3.
  all: rewrite U0 in U3.
  all: step; step; if_cases HU1; zify_cond HU1; rewrite ?U3 in HU1.
  all: lazymatch type of HU1 with
       | _ < _ => exfalso; first [lia | Z.div_mod_to_equations; lia]
       | _ => clear HU1
       end.
  (* byte 2's shadow: 0x825dc addi a2,a0,2; 0x825e0 srli a5,a2,3; 0x825e4 add a5,a5,a3; 0x825e8 lb a6 *)
  all: step; gen_addi a0 w2 U2.
  all: rewrite U0 in U2.
  all: step; gen_shr w2 g2 G2.
  all: rewrite U2 in G2.
  all: step; gen_addi g2 h2 H2.
  all: pose proof (rng_sub' _ _ _ (bv_unsigned h2) 1 RS2 ltac:(lia)) as RH2.
  all: pose proof (rdw0 m0 h2 _ _ M2 ltac:(lia)) as R; step; clear R.
  (* byte 1: 0x825ec lbu a5,1(a0) *)
  all: pose proof (rng_sub' _ _ _ (bv_unsigned a0 + 1) 1 RP ltac:(lia)) as RW1.
  all: pose proof (rdw m0 a0 1 _ _ F1 ltac:(lia)) as R; step; clear R.
  (* 0x825f0 bnez a6; when k2 <> 0: 0x82650 andi a7,a2,7; 0x82654 blt a7,a6 back to 0x825f4 ((p + 2) mod 8 < k2) *)
  all: step.
  all: destruct SK2 as [C2|[C2 Cu2]].
  all: lazymatch type of C2 with
       | bv_signed _ = 0 => rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C2); cbn [negb]
       | _ =>
           rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k2) 0) ltac:(lia)); cbn [negb]; step; step;
           rewrite land7, U2, (lts_low ((p + 2) mod 8) k2 MB2), (proj2 (Z.ltb_lt _ _) C2); cbn [negb]
       end.
  (* byte 3's shadow: 0x825f4 srli a2,a1,3; 0x825f8 add a2,a2,a3; 0x825fc lb a2 *)
  all: step; gen_shr w3 g3 G3.
  all: rewrite U3 in G3.
  all: step; gen_addi g3 h3 H3.
  all: pose proof (rng_sub' _ _ _ (bv_unsigned h3) 1 RS3 ltac:(lia)) as RH3.
  all: pose proof (rdw0 m0 h3 _ _ M3 ltac:(lia)) as R; step; clear R.
  (* byte 2: 0x82600 lbu a0,2(a0) *)
  all: pose proof (rng_sub' _ _ _ (bv_unsigned a0 + 2) 1 RP ltac:(lia)) as RW2.
  all: pose proof (rdw m0 a0 2 _ _ F2 ltac:(lia)) as R; step; clear R.
  (* 0x82604 bnez a2; when k3 <> 0: 0x82660 andi a3,a1,7; 0x82664 blt a3,a2 back to 0x82608 ((p + 3) mod 8 < k3) *)
  all: step.
  all: destruct SK3 as [C3|[C3 Cu3]].
  all: lazymatch type of C3 with
       | bv_signed _ = 0 => rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C3); cbn [negb]
       | _ =>
           rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k3) 0) ltac:(lia)); cbn [negb]; step; step;
           rewrite land7, U3, (lts_low ((p + 3) mod 8) k3 MB3), (proj2 (Z.ltb_lt _ _) C3); cbn [negb]
       end.
  (* 0x82608 slliw a2,a4,24; 0x8260c lbu a1,0(a1) (byte 3) *)
  all: step.
  all: pose proof (rng_sub' _ _ _ (bv_unsigned w3) 1 RP ltac:(lia)) as RW3.
  all: pose proof (rdw0 m0 w3 _ _ F3 ltac:(lia)) as R; step; clear R.
  (* 0x82610 slli a5,a5,16; 0x82614 or a2,a5,a2; 0x82618 slli a0,a0,8; 0x8261c or a0,a0,a1; 0x82620 or a0,a2,a0 *)
  all: do 5 step.
  all: first [ rewrite rd32_val
             | match goal with |- evtF _ _ _ (MS ?R _ _ _ _ _ _) => idtac "rd32_val: no match in" R end; fail ].
  (* 0x82624 ld ra; 0x82628 addi sp; 0x8262c ret *)
  all: do 3 step.
  all: apply evtF_done.
  all: do 8 eexists; split; [reflexivity|]; split; [eassumption|]; split; [eassumption|].
  all: release_frame FR ST (bv_unsigned sp); exact ST.
Qed.
