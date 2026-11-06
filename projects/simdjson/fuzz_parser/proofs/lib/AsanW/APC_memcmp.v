(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import StrFun.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import ZBridge Arr Mem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require InitMem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg RtCells AMalloc_iface AU_kit AU_iface ShadowTac F_rip F_tryinit AU_steptac.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require I_printf_lib.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.
Ltac unland_all :=
  repeat match goal with |- context [Z.land ?x 18446744073709551615] =>
    change (Z.land x 18446744073709551615) with (Z.land x (Z.ones 64)); rewrite (Z.land_ones x 64) by lia end;
  change (2 ^ 64) with 18446744073709551616.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Fixpoint memcmp_res (l1 l2 : list byte) : Z :=
  match l1, l2 with
  | b1 :: r1, b2 :: r2 => if bv_unsigned b1 =? bv_unsigned b2 then memcmp_res r1 r2 else bv_unsigned b1 - bv_unsigned b2
  | _, _ => 0
  end.

Lemma land_m1_64 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551615 = x.
Proof. intros x H. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. exact H. Qed.

Lemma zxb_u : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof. intros b. unfold zxb. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. apply unsigned_lit. lia. Qed.

Lemma memcmp_res_zero_iff : forall l1 l2, length l1 = length l2 -> (memcmp_res l1 l2 = 0 <-> l1 = l2).
Proof.
  induction l1 as [|x r1 IH]; intros [|y r2] HL; cbn in HL |- *; try discriminate; [tauto|].
  injection HL as HL. destruct (Z.eqb_spec (bv_unsigned x) (bv_unsigned y)) as [E|E].
  - rewrite (IH r2 HL). apply bv_eq in E. subst y. split; [intros ->; reflexivity| intros H; injection H; auto].
  - split; [lia| intros H; injection H as -> _; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mcl_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (res : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 res) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [] m m' /\ wmono asegs m m' /\ mem_inv asegs m'.

Section Leaf.
  Variables (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Hypothesis MI : mem_inv asegs m.
  Let MU : munch [] m m := munch_refl [] m.
  Let WM : wmono asegs m m := wmono_refl asegs m.
  Notation ST pc x10 x11 x12 x13 x14 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 x14 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Lemma mcl_loop : forall (c1 c2 : list byte) (A1 A2 : Z) (x13 x14 : word),
    length c1 = length c2 -> (0 < length c1)%nat ->
    bytes_at asegs m A1 c1 -> bytes_at asegs m A2 c2 ->
    rng RNG A1 (Z.of_nat (length c1)) -> rng RNG A2 (Z.of_nat (length c1)) ->
    evtF asegs RNG (mcl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (memcmp_res c1 c2) m)
      (ST 0xfd0ec (Z_to_bv 64 A1) (Z_to_bv 64 A2) (Z_to_bv 64 (Z.of_nat (length c1))) x13 x14).
  Proof.
    induction c1 as [|x r1 IH]; intros [|y r2] A1 A2 x13 x14 HL HP B1 B2 R1 R2; cbn [length] in HL, HP; try (exfalso; lia).
    injection HL as HL.
    pose proof (bytes_at_bound asegs m A1 (x :: r1) B1) as BB1. pose proof (bytes_at_bound asegs m A2 (y :: r2) B2) as BB2.
    cbn [length] in BB1, BB2.
    pose proof (u8ro_read asegs m A1 (x :: r1) 0 x _ B1 eq_refl ltac:(lia) eq_refl) as RD1. rewrite Z.add_0_r in RD1.
    pose proof (u8ro_read asegs m A2 (y :: r2) 0 y _ B2 eq_refl ltac:(lia) eq_refl) as RD2. rewrite Z.add_0_r in RD2.
    rewrite ?unsigned_lit by lia.
    pose proof (bv_unsigned_in_range 8 x) as XR. pose proof (bv_unsigned_in_range 8 y) as YR. unfold bv_modulus in XR, YR. cbn in XR, YR.
    zstep. zstep. zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      assert (ER : memcmp_res (x :: r1) (y :: r2) = bv_unsigned x - bv_unsigned y)
        by (cbn [memcmp_res]; destruct (Z.eqb_spec (bv_unsigned x) (bv_unsigned y)); [contradiction| reflexivity]).
      rewrite ER. zstep. zstep. rewrite ?unsigned_lit by lia. finish.
    - (* [comment removed for export] *)
      assert (ER : memcmp_res (x :: r1) (y :: r2) = memcmp_res r1 r2) by (cbn [memcmp_res]; rewrite K, Z.eqb_refl; reflexivity).
      rewrite ER. zstep. zstep. zstep. zstep. if_cases K1; zify_cond K1;
        try (change 18446744073709551615 with (Z.ones 64) in K1; rewrite Z.land_ones in K1 by lia);
        try (rewrite Z.mod_small in K1 by (cbn [length] in BB1 |- *; lia)).
      + destruct r1 as [|x' r1']; [cbn [length] in K1; exfalso; lia|].
        change (x :: x' :: r1') with ([x] ++ x' :: r1') in B1. change (y :: r2) with ([y] ++ r2) in B2.
        apply bytes_at_app in B1 as [_ B1']. apply bytes_at_app in B2 as [_ B2']. cbn [length Z.of_nat Pos.of_succ_nat] in B1', B2'.
        replace (Z.of_nat (length (x :: x' :: r1')) + -1) with (Z.of_nat (length (x' :: r1'))) by (cbn [length]; lia).
        apply IH; [exact HL| cbn [length]; lia| exact B1'| exact B2'|
                   eapply rng_sub'; [exact R1| cbn [length] in *; lia] | eapply rng_sub'; [exact R2| cbn [length] in *; lia]].
      + assert (r1 = []) by (destruct r1; [reflexivity| cbn [length] in K1; exfalso; lia]). subst r1.
        destruct r2; [| cbn [length] in HL; discriminate].
        zstep. zstep. finish.
  Qed.
End Leaf.

Lemma mcl_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (b1 b2 : list byte),
  mem_inv asegs m ->
  length b1 = length b2 -> bv_unsigned a2 = Z.of_nat (length b1) ->
  bytes_at asegs m (bv_unsigned a0) b1 -> bytes_at asegs m (bv_unsigned a1) b2 ->
  rng RNG (bv_unsigned a0) (Z.of_nat (length b1)) -> rng RNG (bv_unsigned a1) (Z.of_nat (length b1)) ->
  evtF asegs RNG (mcl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (memcmp_res b1 b2) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xfd0e8) fc None m (seg_rom asegs)).
Proof.
  intros until b2. intros MI HL HN B1 B2 R1 R2.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. if_cases K; zify_cond K.
  - (* [comment removed for export] *)
    assert (b1 = []) by (destruct b1; [reflexivity| cbn [length] in HN; lia]). subst b1.
    destruct b2; [| discriminate]. zstep. zstep. finish.
  - rewrite <- (Z_to_bv_bv_unsigned a0), <- (Z_to_bv_bv_unsigned a1), <- (Z_to_bv_bv_unsigned a2), HN.
    apply mcl_loop; try assumption. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mc_pre (RNG : footprint) (sp : word) (m : word -> option byte) (lo : Z) (S1 S2 n : Z) (b1 b2 : list byte)
    (RLO1 RHI1 RLO2 RHI2 K : Z) : Prop :=
  mem_inv asegs m /\ stk asegs m lo (bv_unsigned sp) /\ lo <= bv_unsigned sp - K /\ KHIGH <= lo /\
  (rt_got m) /\ (rt_shbase m) /\ (rt_inited m) /\ (rt_layout m) /\ rt_flags m /\ rt_real_mc m /\
  length b1 = length b2 /\ n = Z.of_nat (length b1) /\ 1 <= n <= 64 /\
  bytes_at asegs m S1 b1 /\ bytes_at asegs m S2 b2 /\
  (S1 + n <= lo \/ bv_unsigned sp <= S1) /\ (S2 + n <= lo \/ bv_unsigned sp <= S2) /\
  app_blk S1 (S1 + n) /\ app_blk S2 (S2 + n) /\ unpoisoned m S1 (S1 + n) /\ unpoisoned m S2 (S2 + n) /\
  (RLO1 <= S1 /\ S1 + n <= RHI1 /\ RLO1 mod 64 = 0 /\ RHI1 mod 64 = 0 /\ 0 <= RLO1 /\ RHI1 <= KEND) /\
  (RLO2 <= S2 /\ S2 + n <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND) /\
  wr_at asegs m (shad RLO1) (shad RHI1 - shad RLO1) /\ wr_at asegs m (shad RLO2) (shad RHI2 - shad RLO2) /\
  rng_aimg RNG /\ rng RNG lo (bv_unsigned sp - lo) /\ rng RNG S1 n /\ rng RNG S2 n /\
  rng RNG (shad RLO1) (shad RHI1 - shad RLO1) /\ rng RNG (shad RLO2) (shad RHI2 - shad RLO2).

Definition mc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (res lo K : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 res) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - K, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

(* [comment removed for export] *)
Definition mc_spec (R K : Z) : Prop :=
  forall (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (b1 b2 : list byte) (RLO1 RHI1 RLO2 RHI2 : Z),
  mc_pre RNG sp m lo (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) b1 b2 RLO1 RHI1 RLO2 RHI2 K ->
  evtF asegs RNG (mc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (memcmp_res b1 b2) lo K m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 R) fc None m (seg_rom asegs)).

Section Common.
  Variables (R KR : Z).
  Hypothesis REAL : mc_spec R KR.
  Hypothesis KR0 : 0 <= KR.
  Hypothesis RR : 0 <= R < 2^64 /\ R mod 2 = 0.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (b1 b2 : list byte) (RLO1 RHI1 RLO2 RHI2 : Z).
  Notation S1 := (bv_unsigned a2).
  Notation S2 := (bv_unsigned a3).
  Notation n := (bv_unsigned a4).
  Hypothesis A1R : a1 = Z_to_bv 64 R.
  Hypothesis PRE : mc_pre RNG sp m lo S1 S2 n b1 b2 RLO1 RHI1 RLO2 RHI2 (2192 + KR).
  Notation POST := (mc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (memcmp_res b1 b2) lo (2192 + KR) m).
  Notation W := [(bv_unsigned sp - (2192 + KR), bv_unsigned sp)].

  (* [comment removed for export] *)
  Definition INV (mc : word -> option byte) : Prop :=
    rw_cells asegs mc (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk asegs mc lo (bv_unsigned sp + -104) /\ munch W m mc /\ wmono asegs m mc /\ mem_inv asegs mc
    /\ (rt_got mc) /\ (rt_shbase mc) /\ (rt_inited mc) /\ (rt_layout mc) /\ rt_real_mc mc /\ rt_flags mc
    /\ unpoisoned mc S1 (S1 + n) /\ unpoisoned mc S2 (S2 + n)
    /\ wr_at asegs mc (shad RLO1) (shad RHI1 - shad RLO1) /\ wr_at asegs mc (shad RLO2) (shad RHI2 - shad RLO2)
    /\ bytes_at asegs mc S1 b1 /\ bytes_at asegs mc S2 b2.

  (* [comment removed for export] *)
  Definition BND : Prop :=
    0 <= lo /\ lo <= bv_unsigned sp - (2192 + KR) /\ 17594333495296 <= lo /\ bv_unsigned sp < 2^64 /\ 1 <= n <= 64
    /\ 0 <= S1 /\ S1 + n + 8 <= 2^47 /\ 0 <= S2 /\ S2 + n + 8 <= 2^47
    /\ RLO1 <= S1 /\ S1 + n <= RHI1 /\ RLO1 mod 64 = 0 /\ RHI1 mod 64 = 0 /\ 0 <= RLO1 /\ RHI1 <= 2^47
    /\ RLO2 <= S2 /\ S2 + n <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= 2^47.
  Lemma BND_ok : BND.
  Proof.
    destruct PRE as (MI & ST & LO & KLO & GOT & SHB & INI & LAY & FLG & RMC & HL & HN & N64 & B1 & B2 & SEP1 & SEP2 & AP1 & AP2 & U1 & U2
                     & H1 & H2 & _).
    destruct ST as (L0 & _). unfold app_blk, KLOW, KHIGH, KEND in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold BND. lia.
  Qed.
  Ltac acc_facts B ::= pose proof BND_ok as B; unfold BND in B.

  Lemma inv_of : forall mc,
    rw_cells asegs mc (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs mc lo (bv_unsigned sp + -104) -> munch W m mc -> wmono asegs m mc -> mem_inv asegs mc -> INV mc.
  Proof.
    intros mc FR1 ST1 MU1 WM1 MI1. pose proof BND_ok as B. unfold BND in B.
    destruct PRE as (MI & ST & LO & KLO & GOT & SHB & INI & LAY & FLG & RMC & HL & HN & N64 & B1 & B2 & SEP1 & SEP2 & AP1 & AP2 & U1 & U2
                     & H1 & H2 & W1 & W2 & _).
    unfold rt_flags, rt_real_mc, AREAL_MC, AMCFLAGS in *.
    assert (SS : forall X, 0 <= X < 2^47 -> shad X < 17594333495296)
      by (intros X HX; unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
    unfold INV, rt_flags, rt_real_mc, AREAL_MC, AMCFLAGS. split; [exact FR1|]. split; [exact ST1|]. split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|].
    split; [eapply rw_cells_transport; [exact GOT| exact MU1| exact WM1| cbn [disjoint_from cells_size csize Nat.add]; lia]|].
    split; [eapply rw_cells_transport; [exact SHB| exact MU1| exact WM1| cbn [disjoint_from cells_size csize Nat.add]; lia]|].
    split; [eapply rw_cells_transport; [exact INI| exact MU1| exact WM1| cbn [disjoint_from cells_size csize Nat.add]; lia]|].
    split; [eapply rw_cells_transport; [exact LAY| exact MU1| exact WM1| cbn [disjoint_from cells_size csize Nat.add]; lia]|].
    split; [eapply rw_cells_transport; [exact RMC| exact MU1| exact WM1| cbn [disjoint_from cells_size csize Nat.add]; lia]|].
    split; [eapply rw_cells_transport; [exact FLG| exact MU1| exact WM1| cbn [disjoint_from cells_size csize Nat.add]; lia]|].
    split; [eapply unpoisoned_munch; [exact U1| exact MU1| cbn [disjoint_from]; pose proof (SS (S1 + n - 1)); pose proof (SS S1);
                                      unfold shad, ASHOFF in *; rewrite !Z.shiftr_div_pow2 in * by lia; change (2^3) with 8 in *; Z.div_mod_to_equations; lia]|].
    split; [eapply unpoisoned_munch; [exact U2| exact MU1| cbn [disjoint_from]; pose proof (SS (S2 + n - 1)); pose proof (SS S2);
                                      unfold shad, ASHOFF in *; rewrite !Z.shiftr_div_pow2 in * by lia; change (2^3) with 8 in *; Z.div_mod_to_equations; lia]|].
    split; [eapply wr_at_transport; eassumption|]. split; [eapply wr_at_transport; eassumption|].
    pose proof (bytes_at_bound asegs m S1 b1 B1). pose proof (bytes_at_bound asegs m S2 b2 B2).
    split; eapply bytes_at_transport; [exact B1| exact MU1| cbn [disjoint_from]| exact B2| exact MU1| cbn [disjoint_from]];
      rewrite <- ?HL, <- HN; destruct SEP1, SEP2; lia.
  Qed.

  (* [comment removed for export] *)
  Notation MR x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x28 x29 x30 x31 :=
    (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2192)) gp tp x5 x6 x7 sp a4 x10 x11 x12 x13 x14 x15 x16 x17 a3 ra a2 a1 s6 x23 x24 x25 s10 s11 x28 x29 x30 x31).

  (* [comment removed for export] *)
  Lemma LR : forall mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x28 x29 x30 x31, INV mc ->
    evtF asegs RNG POST (MS (MR x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x56708) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV.
    destruct IV as (FR1 & ST1 & MU1 & WM1 & MI1 & GOT1 & SHB1 & INI1 & LAY1 & RMC1 & FLG1 & U11 & U21 & W11 & W21 & B11 & B21).
    pose proof BND_ok as B. unfold BND in B.
    destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HL & HN & _ & _ & _ & SEP1 & SEP2 & AP1 & AP2 & _ & _ & H1 & H2 & _ & _ & RI & RSTK & RB1 & RB2 & RS1 & RS2).
    destruct (stk_split asegs mc lo (bv_unsigned sp + -2192) (bv_unsigned sp + -104) ST1 ltac:(lia)) as [STa STb]. clear ST1.
    rewrite A1R.
    zstep. zstep. zstep. zstep.
    replace (ret_pc (Z_to_bv 64 R)) with (Z_to_bv 64 R) by (symmetry; apply ret_pc_even; lia).
    pose proof REAL as RL. unfold mc_spec in RL.
    eapply evtF_cut.
    { eapply (RL RNG _ (Z_to_bv 64 (bv_unsigned sp + -2192))) with (lo := lo) (b1 := b1) (b2 := b2) (RLO1 := RLO1) (RHI1 := RHI1) (RLO2 := RLO2) (RHI2 := RHI2).
      rewrite ?unsigned_lit by lia. rewrite ?Z_to_bv_bv_unsigned.
      unfold mc_pre. rewrite ?unsigned_lit by lia.
      repeat match goal with |- _ /\ _ => split end;
        first [ eassumption | lia | (unfold KHIGH; lia) | (destruct SEP1; [left| right]; lia) | (destruct SEP2; [left| right]; lia)
              | (eapply rng_sub'; [exact RSTK| lia]) ]. }
    cbv beta. intros ms2 (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m2 & -> & MU2 & WM2 & MI2 & ST2).
    rewrite unsigned_lit in MU2, ST2 by lia.
    assert (MU12 : munch W m m2).
    { eapply munch_trans; [exact MU1|]. eapply munch_weaken; [| exact MU2].
      intros x Hx. cbn in Hx |- *. lia. }
    assert (WM12 : wmono asegs m m2) by (eapply wmono_trans; eassumption).
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
      by (eapply rw_cells_transport; [exact FR1| exact MU2| exact WM2| cbn [disjoint_from cells_size csize Nat.add]; lia]).
    assert (STb2 : stk asegs m2 (bv_unsigned sp + -2192) (bv_unsigned sp + -104))
      by (eapply stk_transport_disjoint; [exact STb| exact MU2| exact WM2| cbn [disjoint_from]; lia]).
    pose proof (stk_merge asegs _ _ _ _ ST2 STb2 ltac:(lia)) as ST3.
    clear MU1 WM1 MU2 WM2 FR1 STa STb STb2 ST2 GOT1 SHB1 INI1 LAY1 RMC1 FLG1 U11 U21 W11 W21 B11 B21.
    lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?r)] =>
      replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
    do 9 zstep.
    zstep. zstep.
    do 15 zstep.
    release_frame FR2 ST3 (bv_unsigned sp).
    apply evtF_done. unfold mc_post.
    do 15 eexists. split; [reflexivity|].
    replace (bv_unsigned sp - (2192 + KR)) with (bv_unsigned sp - (2192 + KR)) by lia.
    repeat match goal with |- _ /\ _ => split end; try eassumption.
  Qed.

  Ltac inv_open IV := destruct IV as (FR1 & ST1 & MU1 & WM1 & MI1 & GOT1 & SHB1 & INI1 & LAY1 & RMC1 & FLG1 & U11 & U21 & W11 & W21 & B11 & B21).

  (* [comment removed for export] *)
  Lemma LL2 : forall mc (k : nat) (c : Z) x1 x5 x6 x7 x10 x14 x15 x16 x17 x23 x24 x25 x28 x29 x30 x31,
    INV mc -> Z.to_nat (shad (S2 + n - 1) - c) = k -> shad S2 <= c < shad (S2 + n - 1) ->
    evtF asegs RNG POST (MS (MR x1 x5 x6 x7 x10 (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (S2 + n + -1) 3)) (Z_to_bv 64 0)
                                x14 x15 x16 x17 x23 x24 x25 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x56b80) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV Hk Hc. pose proof IV as IV0. inv_open IV. pose proof BND_ok as B. unfold BND in B.
    destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RS2).
    revert c x14 Hk Hc. induction k as [|k IH]; intros c x14 Hk Hc; [exfalso; lia|].
    assert (SL : shad (S2 + n - 1) = 2147450880 + Z.shiftr (S2 + n + -1) 3) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
    pose proof (unpoisoned_full_rd asegs mc S2 (S2 + n) c U21 ltac:(lia)
                  ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
    assert (AC : acc_in RNG (Z_to_bv 64 c, 1%nat))
      by (eapply rng_acc_litZ'; [exact RS2| reflexivity| reflexivity|];
          unfold shad, ASHOFF in *; rewrite !Z.shiftr_div_pow2 in * by lia; change (2^3) with 8 in *; Z.div_mod_to_equations; lia).
    assert (SB : 0 <= Z.shiftr (S2 + n + -1) 3 < 2^61) by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
    assert (SB0 : 0 <= shad S2) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K; zify_cond K.
    - rewrite ?land_m1_64 in K by lia. apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply LR; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma LE2 : forall mc x1 x5 x6 x7 x10 x14 x15 x16 x17 x23 x24 x25 x28 x29 x30 x31, INV mc ->
    evtF asegs RNG POST (MS (MR x1 x5 x6 x7 x10 (Z_to_bv 64 (2147450880 + Z.shiftr S2 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (S2 + n + -1) 3))
                                (Z_to_bv 64 (S2 + n + -1)) x14 x15 x16 x17 x23 x24 x25 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x56b64) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. pose proof IV as IV0. inv_open IV. pose proof BND_ok as B. unfold BND in B.
    destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RS2).
    destruct (unpoisoned_check_rd asegs mc S2 (S2 + n) (S2 + n + -1) 1 U21 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia))
      as (sb2 & RD2 & CK2).
    unfold shad, ASHOFF in RD2. pose proof (sval_range sb2) as SR2.
    replace (Z.shiftr (S2 + n + -1) 3 + 2147450880) with (2147450880 + Z.shiftr (S2 + n + -1) 3) in RD2 by lia.
    assert (AC : acc_in RNG (Z_to_bv 64 (2147450880 + Z.shiftr (S2 + n + -1) 3), 1%nat))
      by (eapply rng_acc_litZ'; [exact RS2| reflexivity| reflexivity|];
          unfold shad, ASHOFF in *; rewrite !Z.shiftr_div_pow2 in * by lia; change (2^3) with 8 in *; Z.div_mod_to_equations; lia).
    zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((S2 + n + -1) mod 8) (sval sb2)) by (Z.div_mod_to_equations; lia).
    zstep. if_cases K6; zify_cond K6.
    - (* [comment removed for export] *) zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LR; eassumption.
    - assert (SB2 : 0 <= Z.shiftr S2 3 < 2^61 /\ 0 <= Z.shiftr (S2 + n + -1) 3 < 2^61)
        by (rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
      rewrite ?land_m1_64 in K6 by lia.
      eapply (LL2 mc); [exact IV0 | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma LC2 : forall mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x28 x29 x30 x31, INV mc ->
    evtF asegs RNG POST (MS (MR x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 (Z_to_bv 64 (n + -65)) x28 x29 x30 x31)
                            F (Z_to_bv 64 0x566bc) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. pose proof IV as IV0. inv_open IV. pose proof BND_ok as B. unfold BND in B.
    destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RI & _ & _ & _ & _ & RS2).
    zstep. rewrite zb_lxor_ones by lia. zstep. if_cases K1; zify_cond K1. { exfalso. lia. } clear K1.
    zstep. zstep. if_cases K2; zify_cond K2.
    { exfalso. revert K2. unland_all. intros K2. Z.div_mod_to_equations. lia. }
    clear K2.
    do 11 zstep.
    assert (SB2 : 0 <= Z.shiftr S2 3 < 2^61 /\ 0 <= Z.shiftr (S2 + n + -1) 3 < 2^61)
      by (rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
    rewrite !land_m1_64 by lia. change 18446744073709551608 with (2^64 - 2^3). rewrite !land_align_down by lia. change (2^3) with 8.
    assert (NI2 : no_image asegs (shad RLO2) (shad RHI2))
      by (apply no_image_asan; unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
    destruct (shadow_probe8 asegs mc RLO2 RHI2 S2 W21 NI2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [w1 P1].
    destruct (shadow_probe8 asegs mc RLO2 RHI2 (S2 + n + -1) W21 NI2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [w2 P2].
    unfold ASHOFF in P1, P2.
    assert (AC1 : acc_in RNG (Z_to_bv 64 (2147450880 + Z.shiftr S2 3 - (2147450880 + Z.shiftr S2 3) mod 8), 8%nat))
      by (eapply rng_acc_litZ'; [exact RS2| reflexivity| reflexivity|];
          unfold shad, ASHOFF in *; rewrite !Z.shiftr_div_pow2 in * by lia; change (2^3) with 8 in *; Z.div_mod_to_equations; lia).
    assert (AC2 : acc_in RNG (Z_to_bv 64 (2147450880 + Z.shiftr (S2 + n + -1) 3 - (2147450880 + Z.shiftr (S2 + n + -1) 3) mod 8), 8%nat))
      by (eapply rng_acc_litZ'; [exact RS2| reflexivity| reflexivity|];
          unfold shad, ASHOFF in *; rewrite !Z.shiftr_div_pow2 in * by lia; change (2^3) with 8 in *; Z.div_mod_to_equations; lia).
    do 4 zstep. if_cases K5; zify_cond K5.
    - eapply LE2; eassumption.
    - eapply LR; eassumption.
  Qed.
  (* [comment removed for export] *)
  Lemma LL1 : forall mc (k : nat) (c : Z) x1 x5 x6 x7 x10 x14 x15 x16 x17 x23 x24 x28 x29 x30 x31,
    INV mc -> Z.to_nat (shad (S1 + n - 1) - c) = k -> shad S1 <= c < shad (S1 + n - 1) ->
    evtF asegs RNG POST (MS (MR x1 x5 x6 x7 x10 (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (S1 + n + -1) 3)) (Z_to_bv 64 0)
                                x14 x15 x16 x17 x23 x24 (Z_to_bv 64 (n + -65)) x28 x29 x30 x31)
                            F (Z_to_bv 64 0x56a74) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV Hk Hc. pose proof IV as IV0. inv_open IV. pose proof BND_ok as B. unfold BND in B.
    destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RS1 & _).
    revert c x14 Hk Hc. induction k as [|k IH]; intros c x14 Hk Hc; [exfalso; lia|].
    assert (SL : shad (S1 + n - 1) = 2147450880 + Z.shiftr (S1 + n + -1) 3) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
    pose proof (unpoisoned_full_rd asegs mc S1 (S1 + n) c U11 ltac:(lia)
                  ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
    assert (AC : acc_in RNG (Z_to_bv 64 c, 1%nat))
      by (eapply rng_acc_litZ'; [exact RS1| reflexivity| reflexivity|];
          unfold shad, ASHOFF in *; rewrite !Z.shiftr_div_pow2 in * by lia; change (2^3) with 8 in *; Z.div_mod_to_equations; lia).
    assert (SB : 0 <= Z.shiftr (S1 + n + -1) 3 < 2^61) by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
    assert (SB0 : 0 <= shad S1) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K; zify_cond K.
    - rewrite ?land_m1_64 in K by lia. apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply LC2; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma LE1 : forall mc x1 x5 x6 x7 x10 x14 x15 x16 x17 x23 x24 x28 x29 x30 x31, INV mc ->
    evtF asegs RNG POST (MS (MR x1 x5 x6 x7 x10 (Z_to_bv 64 (2147450880 + Z.shiftr S1 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (S1 + n + -1) 3))
                                (Z_to_bv 64 (S1 + n + -1)) x14 x15 x16 x17 x23 x24 (Z_to_bv 64 (n + -65)) x28 x29 x30 x31)
                            F (Z_to_bv 64 0x56a58) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. pose proof IV as IV0. inv_open IV. pose proof BND_ok as B. unfold BND in B.
    destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RS1 & _).
    destruct (unpoisoned_check_rd asegs mc S1 (S1 + n) (S1 + n + -1) 1 U11 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia))
      as (sb2 & RD2 & CK2).
    unfold shad, ASHOFF in RD2. pose proof (sval_range sb2) as SR2.
    replace (Z.shiftr (S1 + n + -1) 3 + 2147450880) with (2147450880 + Z.shiftr (S1 + n + -1) 3) in RD2 by lia.
    assert (AC : acc_in RNG (Z_to_bv 64 (2147450880 + Z.shiftr (S1 + n + -1) 3), 1%nat))
      by (eapply rng_acc_litZ'; [exact RS1| reflexivity| reflexivity|];
          unfold shad, ASHOFF in *; rewrite !Z.shiftr_div_pow2 in * by lia; change (2^3) with 8 in *; Z.div_mod_to_equations; lia).
    zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((S1 + n + -1) mod 8) (sval sb2)) by (Z.div_mod_to_equations; lia).
    zstep. if_cases K6; zify_cond K6.
    - (* [comment removed for export] *) zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LC2; eassumption.
    - assert (SB2 : 0 <= Z.shiftr S1 3 < 2^61 /\ 0 <= Z.shiftr (S1 + n + -1) 3 < 2^61)
        by (rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
      rewrite ?land_m1_64 in K6 by lia.
      eapply (LL1 mc); [exact IV0 | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      Z.div_mod_to_equations; lia.
  Qed.


  Lemma mcc_body :
    evtF asegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x565f8) fc None m (seg_rom asegs)).
  Proof.
    pose proof BND_ok as B. unfold BND in B.
    destruct PRE as (MI & ST & LO & KLO & GOT & SHB & INI & LAY & FLG & RMC & HL & HN & N64 & B1 & B2 & SEP1 & SEP2 & AP1 & AP2 & U1 & U2
                     & H1 & H2 & W1 & W2 & RI & RSTK & RB1 & RB2 & RS1 & RS2).
    clear SEP1 SEP2 AP1 AP2 U1 U2 B1 B2 H1 H2 W2 RB1 RB2 RS2 HL HN.
    unfold rt_flags, rt_real_mc, AREAL_MC, AMCFLAGS in FLG, RMC.
    I_printf_lib.recell FLG 0%nat 1%nat [CB 6 (repeat (Z_to_bv 8 1) 6); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)].
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold KHIGH in KLO.
    carve_frame 104%nat ST.
    steps_to 0x5666c.
    (* [comment removed for export] *)
    zstep. rewrite zb_lxor_ones by lia. zstep. if_cases K1; zify_cond K1. { exfalso. lia. } clear K1.
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    { exfalso. revert K2. unland_all. intros K2. Z.div_mod_to_equations. lia. }
    clear K2.
    do 11 zstep.
    assert (SB1 : 0 <= Z.shiftr S1 3 < 2^61 /\ 0 <= Z.shiftr (S1 + n + -1) 3 < 2^61)
      by (rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
    rewrite !land_m1_64 by lia. change 18446744073709551608 with (2^64 - 2^3). rewrite !land_align_down by lia. change (2^3) with 8.
    assert (NI1 : no_image asegs (shad RLO1) (shad RHI1))
      by (apply no_image_asan; unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
    lazymatch goal with W1' : wr_at asegs ?mc (shad RLO1) _ |- _ =>
      destruct (shadow_probe8 asegs mc RLO1 RHI1 S1 W1' NI1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [w1 P1];
      destruct (shadow_probe8 asegs mc RLO1 RHI1 (S1 + n + -1) W1' NI1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [w2 P2]
    end.
    unfold ASHOFF in P1, P2.
    assert (AC1 : acc_in RNG (Z_to_bv 64 (2147450880 + Z.shiftr S1 3 - (2147450880 + Z.shiftr S1 3) mod 8), 8%nat))
      by (eapply rng_acc_litZ'; [exact RS1| reflexivity| reflexivity|];
          unfold shad, ASHOFF in *; rewrite !Z.shiftr_div_pow2 in * by lia; change (2^3) with 8 in *; Z.div_mod_to_equations; lia).
    assert (AC2 : acc_in RNG (Z_to_bv 64 (2147450880 + Z.shiftr (S1 + n + -1) 3 - (2147450880 + Z.shiftr (S1 + n + -1) 3) mod 8), 8%nat))
      by (eapply rng_acc_litZ'; [exact RS1| reflexivity| reflexivity|];
          unfold shad, ASHOFF in *; rewrite !Z.shiftr_div_pow2 in * by lia; change (2^3) with 8 in *; Z.div_mod_to_equations; lia).
    do 4 zstep. if_cases K5; zify_cond K5.
    - eapply LE1. eapply inv_of; eassumption.
    - eapply LC2. eapply inv_of; eassumption.
  Qed.
End Common.

(* [comment removed for export] *)
Lemma mc_pre_move : forall RNG sp sp' m m' lo S1 S2 n b1 b2 RLO1 RHI1 RLO2 RHI2 K K' X Y,
  mc_pre RNG sp m lo S1 S2 n b1 b2 RLO1 RHI1 RLO2 RHI2 K ->
  munch [(X, Y)] m m' -> wmono asegs m m' -> mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp') ->
  lo <= X -> Y <= bv_unsigned sp -> bv_unsigned sp' <= bv_unsigned sp -> lo <= bv_unsigned sp' - K' ->
  mc_pre RNG sp' m' lo S1 S2 n b1 b2 RLO1 RHI1 RLO2 RHI2 K'.
Proof.
  intros until Y. intros PRE MU WM MI' ST' HX HY HS HK.
  destruct PRE as (MI & ST & LO & KLO & GOT & SHB & INI & LAY & FLG & RMC & HL & HN & N64 & B1 & B2 & SEP1 & SEP2 & AP1 & AP2 & U1 & U2
                   & H1 & H2 & W1 & W2 & RI & RSTK & RB1 & RB2 & RS1 & RS2).
  unfold rt_flags, rt_real_mc, AREAL_MC, AMCFLAGS in *. unfold KHIGH in KLO. pose proof AP1 as AP1'. pose proof AP2 as AP2'. unfold app_blk, KLOW, KHIGH, KEND in AP1', AP2'.
  destruct H1 as (H1a & H1b & H1c & H1d & H1e & H1f). destruct H2 as (H2a & H2b & H2c & H2d & H2e & H2f). unfold KEND in H1f, H2f.
  assert (SS : forall Z0, 0 <= Z0 < 2^47 -> shad Z0 < 17594333495296)
    by (intros Z0 HZ; unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
  pose proof (bv_unsigned_in_range 64 sp') as RSP'. unfold bv_modulus in RSP'. cbn in RSP'.
  unfold mc_pre, rt_flags, rt_real_mc, AREAL_MC, AMCFLAGS.
  split; [exact MI'|]. split; [exact ST'|]. split; [exact HK|]. split; [unfold KHIGH; exact KLO|].
  split; [eapply rw_cells_transport; [exact GOT| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia]|].
  split; [eapply rw_cells_transport; [exact SHB| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia]|].
  split; [eapply rw_cells_transport; [exact INI| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia]|].
  split; [eapply rw_cells_transport; [exact LAY| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia]|].
  split; [eapply rw_cells_transport; [exact FLG| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia]|].
  split; [eapply rw_cells_transport; [exact RMC| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia]|].
  split; [exact HL|]. split; [exact HN|]. split; [exact N64|].
  split; [eapply bytes_at_transport; [exact B1| exact MU| cbn [disjoint_from]; rewrite <- HN; destruct SEP1; lia]|].
  split; [eapply bytes_at_transport; [exact B2| exact MU| cbn [disjoint_from]; rewrite <- HL, <- HN; destruct SEP2; lia]|].
  split; [destruct SEP1; [left| right]; lia|]. split; [destruct SEP2; [left| right]; lia|].
  split; [exact AP1|]. split; [exact AP2|].
  split; [eapply unpoisoned_munch; [exact U1| exact MU| cbn [disjoint_from]; pose proof (SS (S1 + n - 1)); pose proof (SS S1);
                                    unfold shad, ASHOFF in *; rewrite !Z.shiftr_div_pow2 in * by lia; change (2^3) with 8 in *; Z.div_mod_to_equations; lia]|].
  split; [eapply unpoisoned_munch; [exact U2| exact MU| cbn [disjoint_from]; pose proof (SS (S2 + n - 1)); pose proof (SS S2);
                                    unfold shad, ASHOFF in *; rewrite !Z.shiftr_div_pow2 in * by lia; change (2^3) with 8 in *; Z.div_mod_to_equations; lia]|].
  split; [unfold KEND; lia|]. split; [unfold KEND; lia|].
  split; [eapply wr_at_transport; eassumption|]. split; [eapply wr_at_transport; eassumption|].
  split; [exact RI|]. split; [eapply rng_sub'; [exact RSTK| lia]|].
  split; [exact RB1|]. split; [exact RB2|]. split; [exact RS1| exact RS2].
Qed.

(* [comment removed for export] *)
Lemma mcl_mc_spec : mc_spec 0xfd0e8 0.
Proof.
  unfold mc_spec. intros until RHI2. intros PRE.
  pose proof PRE as (MI & ST & LO & KLO & GOT & SHB & INI & LAY & FLG & RMC & HL & HN & N64 & B1 & B2 & SEP1 & SEP2 & AP1 & AP2 & U1 & U2
                   & H1 & H2 & W1 & W2 & RI & RSTK & RB1 & RB2 & RS1 & RS2).
  eapply evtF_mono; [eapply mcl_spec; [exact MI| exact HL| exact HN| exact B1| exact B2| rewrite <- HN; exact RB1| rewrite <- HN; exact RB2]|].
  intros ms' (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & m' & -> & MU & WM & MI').
  unfold mc_post. do 15 eexists. split; [reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; exact I|]. split; [exact WM|]. split; [exact MI'|].
  eapply stk_transport_disjoint; [exact ST| exact MU| exact WM| exact I].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mcmp_icpt_spec : mc_spec 0x56e8c 2240.
Proof.
  unfold mc_spec. intros until RHI2. intros PRE.
  pose proof PRE as (MI & ST & LO & KLO & GOT & SHB & INI & LAY & FLG & RMC & HL & HN & N64 & B1 & B2 & SEP1 & SEP2 & AP1 & AP2 & U1 & U2
                   & H1 & H2 & W1 & W2 & RI & RSTK & RB1 & RB2 & RS1 & RS2).
  clear FLG HL HN N64 B1 B2 SEP1 SEP2 AP1 AP2 U1 U2 H1 H2 W1 W2 RB1 RB2 RS1 RS2.
  unfold rt_real_mc, AREAL_MC in RMC. unfold KHIGH in KLO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(bv_unsigned sp - 2240, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 40%nat ST.
  steps_to 0x6e9b8.
  (* [comment removed for export] *)
  destruct (stk_split asegs _ lo (bv_unsigned sp + -48) (bv_unsigned sp + -40) ST ltac:(lia)) as [STa STb]. clear ST.
  eapply evtF_cut.
  { eapply tryinit_spec with (lo := lo); rewrite ?unsigned_lit by lia;
      first [eassumption | (unfold KHIGH; lia) | lia | (eapply rng_sub'; [exact RSTK| lia])]. }
  cbv beta. intros ms1 (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m1 & -> & MU1 & WM1 & MI1 & ST1 & INI1).
  rewrite ?unsigned_lit in MU1, ST1 by lia.
  lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?r)] =>
    replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
  assert (FR1 : rw_cells asegs m1 (bv_unsigned sp + -40) [C8 (Z_to_bv 64 109776); C8 s2; C8 s1; C8 s0; C8 ra])
    by (eapply rw_cells_transport; [exact FR| exact MU1| exact WM1| cbn [disjoint_from cells_size csize Nat.add]; lia]).
  assert (RMC1 : rw_cells asegs m1 1085664 [C8 (Z_to_bv 64 1036520); C8 (Z_to_bv 64 1036312)])
    by (eapply rw_cells_transport; [exact RMC| exact MU1| exact WM1| cbn [disjoint_from cells_size csize Nat.add]; lia]).
  assert (STb1 : stk asegs m1 (bv_unsigned sp + -48) (bv_unsigned sp + -40))
    by (eapply stk_transport_disjoint; [exact STb| exact MU1| exact WM1| cbn [disjoint_from]; lia]).
  assert (MU01 : munch [(bv_unsigned sp - 2240, bv_unsigned sp)] m m1)
    by (eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU1]; intros x Hx; cbn in Hx |- *; lia]).
  assert (WM01 : wmono asegs m m1) by (eapply wmono_trans; eassumption).
  clear FR RMC STb MU1 WM1 MU WM GOT SHB INI LAY MI INI1.
  steps_to 0x565f8.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (mcc_body 0xfd0e8 0 mcl_mc_spec ltac:(lia) ltac:(lia)); [reflexivity|].
    rewrite ?unsigned_lit by lia. rewrite ?Z_to_bv_bv_unsigned.
    eapply mc_pre_move; [exact PRE| exact MU01| exact WM01| exact MI1| rewrite ?unsigned_lit by lia; exact ST1| lia| lia| rewrite ?unsigned_lit by lia; lia
                        | rewrite ?unsigned_lit by lia; lia]. }
  cbv beta. intros ms2 (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m2 & -> & MU2 & WM2 & MI2 & ST2).
  rewrite ?unsigned_lit in MU2, ST2 by lia.
  lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?r)] =>
    replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
  assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -40) [C8 (Z_to_bv 64 109776); C8 s2; C8 s1; C8 s0; C8 ra])
    by (eapply rw_cells_transport; [exact FR1| exact MU2| exact WM2| cbn [disjoint_from cells_size csize Nat.add]; lia]).
  assert (STb2 : stk asegs m2 (bv_unsigned sp + -48) (bv_unsigned sp + -40))
    by (eapply stk_transport_disjoint; [exact STb1| exact MU2| exact WM2| cbn [disjoint_from]; lia]).
  pose proof (stk_merge asegs _ _ _ _ ST2 STb2 ltac:(lia)) as ST3.
  assert (MU02 : munch [(bv_unsigned sp - 2240, bv_unsigned sp)] m m2)
    by (eapply munch_trans; [exact MU01| eapply munch_weaken; [| exact MU2]; intros x Hx; cbn in Hx |- *; lia]).
  assert (WM02 : wmono asegs m m2) by (eapply wmono_trans; eassumption).
  clear FR1 RMC1 STb1 STb2 ST1 ST2 MU01 WM01 MU2 WM2 MI1 STa.
  steps_to 0x56efc. zstep.
  release_frame FR2 ST3 (bv_unsigned sp).
  apply evtF_done. unfold mc_post.
  do 15 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end; eassumption.
Qed.

(* [comment removed for export] *)
Lemma bcmp_real_spec : mc_spec 0xfd018 2240.
Proof.
  unfold mc_spec. intros until RHI2. intros PRE.
  zstep. zstep. eapply mcmp_icpt_spec. exact PRE.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bcmp_icpt_spec : mc_spec 0x56f48 4480.
Proof.
  unfold mc_spec. intros until RHI2. intros PRE.
  pose proof PRE as (MI & ST & LO & KLO & GOT & SHB & INI & LAY & FLG & RMC & HL & HN & N64 & B1 & B2 & SEP1 & SEP2 & AP1 & AP2 & U1 & U2
                   & H1 & H2 & W1 & W2 & RI & RSTK & RB1 & RB2 & RS1 & RS2).
  clear FLG HL HN N64 B1 B2 SEP1 SEP2 AP1 AP2 U1 U2 H1 H2 W1 W2 RB1 RB2 RS1 RS2.
  unfold rt_real_mc, AREAL_MC in RMC. unfold KHIGH in KLO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(bv_unsigned sp - 4480, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 40%nat ST.
  steps_to 0x6e9b8.
  (* [comment removed for export] *)
  destruct (stk_split asegs _ lo (bv_unsigned sp + -48) (bv_unsigned sp + -40) ST ltac:(lia)) as [STa STb]. clear ST.
  eapply evtF_cut.
  { eapply tryinit_spec with (lo := lo); rewrite ?unsigned_lit by lia;
      first [eassumption | (unfold KHIGH; lia) | lia | (eapply rng_sub'; [exact RSTK| lia])]. }
  cbv beta. intros ms1 (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m1 & -> & MU1 & WM1 & MI1 & ST1 & INI1).
  rewrite ?unsigned_lit in MU1, ST1 by lia.
  lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?r)] =>
    replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
  assert (FR1 : rw_cells asegs m1 (bv_unsigned sp + -40) [C8 (Z_to_bv 64 89001); C8 s2; C8 s1; C8 s0; C8 ra])
    by (eapply rw_cells_transport; [exact FR| exact MU1| exact WM1| cbn [disjoint_from cells_size csize Nat.add]; lia]).
  assert (RMC1 : rw_cells asegs m1 1085664 [C8 (Z_to_bv 64 1036520); C8 (Z_to_bv 64 1036312)])
    by (eapply rw_cells_transport; [exact RMC| exact MU1| exact WM1| cbn [disjoint_from cells_size csize Nat.add]; lia]).
  assert (STb1 : stk asegs m1 (bv_unsigned sp + -48) (bv_unsigned sp + -40))
    by (eapply stk_transport_disjoint; [exact STb| exact MU1| exact WM1| cbn [disjoint_from]; lia]).
  assert (MU01 : munch [(bv_unsigned sp - 4480, bv_unsigned sp)] m m1)
    by (eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU1]; intros x Hx; cbn in Hx |- *; lia]).
  assert (WM01 : wmono asegs m m1) by (eapply wmono_trans; eassumption).
  clear FR RMC STb MU1 WM1 MU WM GOT SHB INI LAY MI INI1.
  steps_to 0x565f8.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (mcc_body 0xfd018 2240 bcmp_real_spec ltac:(lia) ltac:(lia)); [reflexivity|].
    rewrite ?unsigned_lit by lia. rewrite ?Z_to_bv_bv_unsigned.
    eapply mc_pre_move; [exact PRE| exact MU01| exact WM01| exact MI1| rewrite ?unsigned_lit by lia; exact ST1| lia| lia| rewrite ?unsigned_lit by lia; lia
                        | rewrite ?unsigned_lit by lia; lia]. }
  cbv beta. intros ms2 (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m2 & -> & MU2 & WM2 & MI2 & ST2).
  rewrite ?unsigned_lit in MU2, ST2 by lia.
  lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?r)] =>
    replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
  assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -40) [C8 (Z_to_bv 64 89001); C8 s2; C8 s1; C8 s0; C8 ra])
    by (eapply rw_cells_transport; [exact FR1| exact MU2| exact WM2| cbn [disjoint_from cells_size csize Nat.add]; lia]).
  assert (STb2 : stk asegs m2 (bv_unsigned sp + -48) (bv_unsigned sp + -40))
    by (eapply stk_transport_disjoint; [exact STb1| exact MU2| exact WM2| cbn [disjoint_from]; lia]).
  pose proof (stk_merge asegs _ _ _ _ ST2 STb2 ltac:(lia)) as ST3.
  assert (MU02 : munch [(bv_unsigned sp - 4480, bv_unsigned sp)] m m2)
    by (eapply munch_trans; [exact MU01| eapply munch_weaken; [| exact MU2]; intros x Hx; cbn in Hx |- *; lia]).
  assert (WM02 : wmono asegs m m2) by (eapply wmono_trans; eassumption).
  clear FR1 RMC1 STb1 STb2 ST1 ST2 MU01 WM01 MU2 WM2 MI1 STa.
  steps_to 0x56fb8. zstep.
  release_frame FR2 ST3 (bv_unsigned sp).
  apply evtF_done. unfold mc_post.
  do 15 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end; eassumption.
Qed.
End CANSEC1.
