(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ShadowTac F_memset F_rip.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.

Section CANSEC1. Context {rc : runConstT}.
Definition asan_memset_entry := 0x53ca0%Z.

Definition asan_memset_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 2208, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (bv_unsigned a0)
         [CB (Z.to_nat (bv_unsigned a2)) (repeat (Z_to_bv 8 (bv_unsigned a1 mod 256)) (Z.to_nat (bv_unsigned a2)))].

Section Proofs.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
            (junk : list byte) (RLO2 RHI2 : Z).
  Notation D := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 2208)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis GOT : rt_got m.
  Hypothesis RIC : rt_got_ric m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis INI : rt_inited m.
  Hypothesis LAY : rt_layout m.
  Hypothesis REAL : rt_real_mem m.
  Hypothesis DST : rw_cells bsegs m D [CB (Z.to_nat n) junk].
  Hypothesis SEPD : (D + n <= lo \/ bv_unsigned sp <= D)%Z.
  Hypothesis APPD : app_blk D (D + n).
  Hypothesis UDST : unpoisoned m D (D + n).
  Hypothesis NSZ : (n <= 2^40)%Z.
  Hypothesis R2 : (RLO2 <= D /\ D + n <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND)%Z.
  Hypothesis WR2 : wr_at bsegs m (shad RLO2) (shad RHI2 - shad RLO2).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RD : rng RNG D n.
  Hypothesis RSH2 : rng RNG (shad RLO2) (shad RHI2 - shad RLO2).

  Notation POST := (asan_memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 lo m).

  Definition INV (mc : word -> option byte) : Prop :=
    (exists jk, rw_cells bsegs mc (bv_unsigned sp + -2128)
                  [CB 2072 jk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ stk bsegs mc lo (bv_unsigned sp + -2128)
    /\ munch [(bv_unsigned sp + -2208, bv_unsigned sp)]%Z m mc
    /\ wmono bsegs m mc /\ mem_inv bsegs mc
    /\ rt_got mc /\ rt_got_ric mc /\ rt_shbase mc /\ rt_inited mc /\ rt_layout mc /\ rt_real_mem mc
    /\ unpoisoned mc D (D + n)
    /\ wr_at bsegs mc (shad RLO2) (shad RHI2 - shad RLO2).

  Definition BND : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2208 /\ KHIGH <= lo /\ 0 <= n < 2^64 /\ n <= 2^40
     /\ 0 <= D /\ D + n + 8 <= KEND
     /\ 2147450880 <= shad RLO2 /\ shad RLO2 <= shad D /\ shad (D + n - 1) + 1 <= shad RHI2 /\ shad RHI2 <= KHIGH
     /\ 0 <= Z.shiftr D 3 < 2^44 /\ -1 <= Z.shiftr (D + n + -1) 3 < 2^44
     /\ shad RLO2 mod 8 = 0 /\ shad RHI2 mod 8 = 0
     /\ RLO2 <= D /\ D + n <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0)%Z.

  Lemma BND_ok : BND.
  Proof.
    unfold BND. pose proof (bv_unsigned_in_range 64 a2) as Rn. unfold bv_modulus in Rn.
    destruct ST as (L0 & _). destruct APPD as [LED AD]. unfold KLOW, KHIGH, KEND in *.
    pose proof R2 as R2'. unfold sf_hide in R2'.
    rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rn.
    first [clear -Rn L0 LO KLO NSZ LED AD R2'; Z.div_mod_to_equations; nia | Z.div_mod_to_equations; nia].   (* [comment removed for export] *)
  Qed.

  Ltac acc_facts B ::= pose proof BND_ok as B; unfold BND, KHIGH, KEND in B.

  Definition BL : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2208 /\ 17594333495296 <= lo /\ 0 <= n < 2^64 /\ 0 <= D /\ D + n + 8 <= 2^47
     /\ 0 <= Z.shiftr D 3 < 2^44 /\ -1 <= Z.shiftr (D + n + -1) 3 < 2^44
     /\ 2147450880 <= shad RLO2 /\ shad RLO2 <= shad D /\ shad (D + n - 1) + 1 <= shad RHI2 /\ shad RHI2 <= 17594333495296)%Z.
  Lemma BL_ok : BL. Proof. pose proof BND_ok as B. unfold BND, KHIGH, KEND in B. unfold BL. lia. Qed.

  Ltac inv_open H :=
    let jk := fresh "jk" in
    destruct H as ((jk & FR) & ST1 & MU1 & WM1 & MI1 & GOT1 & RIC1 & SHB1 & INI1 & LAY1 & REAL1 & UD1 & WR21).

  Ltac prep IV :=
    pose proof IV as IV0; inv_open IV;
    let B := fresh "BL" in pose proof BL_ok as B; unfold BL in B;
    assert (RSTK' : rng RNG (bv_unsigned sp + -2208) 2208) by (eapply rng_sub'; [exact RSTK| lia]);
    change (?P) with (sf_hide P) in DST; change (?P) with (sf_hide P) in SEPD; change (?P) with (sf_hide P) in R2;
    change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO; change (?P) with (sf_hide P) in NSZ.

  Lemma inv_of : forall mc jk,
    rw_cells bsegs mc (bv_unsigned sp + -2128) [CB 2072 jk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk bsegs mc lo (bv_unsigned sp + -2128) ->
    munch [(bv_unsigned sp + -2208, bv_unsigned sp)]%Z m mc -> wmono bsegs m mc -> mem_inv bsegs mc ->
    rt_got mc -> rt_got_ric mc -> rt_shbase mc -> rt_inited mc -> rt_layout mc -> rt_real_mem mc ->
    INV mc.
  Proof.
    intros mc jk FR ST1 MU1 WM1 MI1 G1 G2 G3 G4 G5 G6. pose proof BND_ok as B. unfold BND, KHIGH, KEND in B.
    split; [exists jk; exact FR|]. repeat (split; [assumption|]).
    assert (SS : forall lo' hi', (0 <= lo' -> hi' + 8 <= 2^47 -> shad (hi' - 1) + 1 <= 17594333495296)%Z).
    { intros lo' hi' H1 H2. rewrite shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia. }
    split. { eapply unpoisoned_munch; [exact UDST | exact MU1 |]. cbn [disjoint_from]. pose proof (SS D (D + n)%Z). lia. }
    eapply wr_at_transport; eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma LX : forall mc x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31,
    INV mc ->
    evtF bsegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp x9 a0 a1 a2 x13 x14 x15 x16 x17
               x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x53d30) fc None mc (seg_rom bsegs)).
  Proof.
    intros until x31. intros IV. prep IV.
    assert (DST1 : rw_cells bsegs mc D [CB (Z.to_nat n) junk]).
    { unfold sf_hide in *. eapply rw_cells_transport; [exact DST | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    zstep. zstep. zstep.
    unfold sf_hide in SEPD.
    apply (munch_weaken _ [(bv_unsigned sp + -2208, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z) in MU1.
    2:{ unfold sub_fp; cbn [outside]; intros; lia. }
    clear GOT1 RIC1 SHB1 INI1 LAY1 REAL1 WR21.
    call memset_spec; [exact DST1 | exact MI1 |].
    do 10 zstep.
    release_frame FR ST1 (bv_unsigned sp). finish.
  Qed.

  (* [comment removed for export] *)
  Lemma LWL : forall mc (k : nat) (c : Z) x5 x6 x7 x9 x16 x17 x18 x19 x21 x28 x29 x30 x31,
    INV mc -> (1 <= n <= 64)%Z ->
    Z.to_nat (shad (D + n - 1) - c) = k -> (shad D <= c < shad (D + n - 1))%Z ->
    evtF bsegs RNG POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp x9 a0 a1 a2
               (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (D + n + -1) 3)) (Z_to_bv 64 0) x16 x17
               x18 x19 (Z_to_bv 64 (bv_unsigned sp + -2128)) x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x53e5c) fc None mc (seg_rom bsegs)).
  Proof.
    intros until x31. intros IV N1 Hk Hc. prep IV.
    revert c x16 Hk Hc. induction k as [|k IH]; intros c x16 Hk Hc; [exfalso; lia|].
    assert (SL : (shad (D + n - 1) = 2147450880 + Z.shiftr (D + n + -1) 3)%Z) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
    pose proof (unpoisoned_full_rd bsegs mc D (D + n) c UD1 ltac:(lia)
                  ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K; zify_cond K.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply LX; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma LWS : forall mc x5 x6 x7 x9 x16 x17 x18 x19 x21 x28 x29 x30 x31,
    INV mc -> (1 <= n <= 64)%Z ->
    evtF bsegs RNG POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp x9 a0 a1 a2
               (Z_to_bv 64 (2147450880 + Z.shiftr D 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (D + n + -1) 3))
               (Z_to_bv 64 (D + n + -1)) x16 x17
               x18 x19 (Z_to_bv 64 (bv_unsigned sp + -2128)) x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x53e40) fc None mc (seg_rom bsegs)).
  Proof.
    intros until x31. intros IV N1. prep IV.
    destruct (unpoisoned_check_rd bsegs mc D (D + n) (D + n + -1) 1 UD1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b2 & RD2 & CK2).
    unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
    zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((D + n + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LX; eassumption.
    - eapply LWL; [exact IV0 | assumption | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma LB : forall mc x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31,
    INV mc ->
    evtF bsegs RNG POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp x9 a0 a1 a2 x13 x14 x15 x16 x17
               x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x53cd8) fc None mc (seg_rom bsegs)).
  Proof.
    intros until x31. intros IV. prep IV.
    zstep. rewrite zb_lxor_ones by lia. zstep. zstep. zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      zstep. if_cases K3; zify_cond K3.
      2:{ zstep. eapply LX; exact IV0. }
      do 5 zstep.
      call_sp rip_spec;
        [ exact MI1 | exact ST1 | lia | unfold KHIGH; lia | exact GOT1 | exact SHB1 | exact LAY1 | exact APPD | exact UD1
        | pose proof BND_ok as B; unfold BND in B; lia
        | eapply rng_sub'; [exact RSTK | lia] | ].
      do 5 zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
      eapply LX; eapply inv_of; eassumption.
    - (* [comment removed for export] *)
      assert (N1 : (1 <= n <= 64)%Z) by (clear - K2 BL0; Z.div_mod_to_equations; lia).
      do 11 zstep.
      change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
      unfold sf_hide in R2.
      destruct (shadow_probe8 bsegs mc RLO2 RHI2 D WR21 ltac:(apply no_image_asan; pose proof BND_ok as B; unfold BND in B; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R2; lia)) as [w1 P1].
      destruct (shadow_probe8 bsegs mc RLO2 RHI2 (D + n + -1) WR21 ltac:(apply no_image_asan; pose proof BND_ok as B; unfold BND in B; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R2; lia)) as [w2 P2].
      unfold ASHOFF in P1, P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply LWS; eassumption.
      + eapply LX; exact IV0.
  Qed.

  Lemma asan_memset_body :
    evtF bsegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x53ca0) fc None m (seg_rom bsegs)).
  Proof.
    pose proof (munch_refl [(bv_unsigned sp + -2208, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
    pose proof BL_ok as BL0. unfold BL in BL0.
    assert (RSTK' : rng RNG (bv_unsigned sp + -2208) 2208) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (LO' : (lo <= bv_unsigned sp - 2128)%Z) by lia.
    change (?P) with (sf_hide P) in R2;
    change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO; change (?P) with (sf_hide P) in NSZ.
    change (?P) with (sf_hide P) in DST.
    pose proof ST as ST0. change (?P) with (sf_hide P) in ST. change (?P) with (sf_hide P) in WR2.
    carve_frame 2128%nat ST0.
    do 10 zstep.
    do 3 zstep. cbv beta. zsimp. zstep. if_cases K0; zify_cond K0. { exfalso. clear - K0. cbv in K0. lia. }
    eapply LB. eapply inv_of; eassumption.
  Qed.
End Proofs.

Lemma asan_memset_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (junk : list byte) (RLO2 RHI2 : Z),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2208)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_mem m ->
  rw_cells bsegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
  (bv_unsigned a0 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  app_blk (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
  unpoisoned m (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
  (bv_unsigned a2 <= 2^40)%Z ->
  (RLO2 <= bv_unsigned a0 /\ bv_unsigned a0 + bv_unsigned a2 <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND)%Z ->
  wr_at bsegs m (shad RLO2) (shad RHI2 - shad RLO2) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (bv_unsigned a0) (bv_unsigned a2) ->
  rng RNG (shad RLO2) (shad RHI2 - shad RLO2) ->
  evtF bsegs RNG (asan_memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x53ca0) fc None m (seg_rom bsegs)).
Proof. intros. eapply asan_memset_body; eassumption. Qed.
End CANSEC1.
