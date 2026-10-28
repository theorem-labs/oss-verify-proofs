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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells F_m2s F_mem_is_zero.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition rip_entry := 0x566f0%Z.

(* [comment removed for export] *)
End CANSEC1.
Ltac zify_lts K :=
  unfold bv_lts in K; rewrite ?land7_mod in K;
  rewrite !signed_lit_small64 in K by (Z.div_mod_to_equations; lia);
  zify_bool K.

(* [comment removed for export] *)
Local Ltac acc_enrich ::= rewrite ?shad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.

Section CANSEC2. Context {rc : runConstT}.
Definition rip_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp).

Section Proofs.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z).
  Notation B := (bv_unsigned a0).
  Notation n := (bv_unsigned a1).
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 80)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis GOT : rt_got m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis LAY : rt_layout m.
  Hypothesis APP : app_blk B (B + n).
  Hypothesis UNP : unpoisoned m B (B + n).
  Hypothesis NSZ : (n <= 2^40)%Z.
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RSH : rng RNG (shad B) (shad (B + n - 1) + 1 - shad B).

  Notation POST := (rip_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m).

  (* [comment removed for export] *)
  Lemma L5 : forall (m2 : word -> option byte) junk8 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x8 x9 x18 x19 x20 x21 x28 x29 x30 x31,
    rw_cells bsegs m2 (bv_unsigned sp + -64) [CB 8 junk8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk bsegs m2 lo (bv_unsigned sp + -64) ->
    munch [(bv_unsigned sp + -80, bv_unsigned sp)]%Z m m2 -> wmono bsegs m m2 -> mem_inv bsegs m2 ->
    (0 <= lo)%Z ->
    evtF bsegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 x6 x7 x8 x9
               x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x56868) fc None m2 (seg_rom bsegs)).
  Proof.
    intros until x31. intros FR ST2 MU2 WM2 MI2 LO0.
    do 11 zstep. release_frame FR ST2 (bv_unsigned sp). finish.
  Qed.

  Section AfterFrame.
    Variables (m1 : word -> option byte) (junk8 : list byte).
    Hypothesis FR : rw_cells bsegs m1 (bv_unsigned sp + -64) [CB 8 junk8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
    Hypothesis ST1 : stk bsegs m1 lo (bv_unsigned sp + -64).
    Hypothesis MU1 : munch [(bv_unsigned sp + -80, bv_unsigned sp)]%Z m m1.
    Hypothesis WM1 : wmono bsegs m m1.
    Hypothesis MI1 : mem_inv bsegs m1.
    Hypothesis GOT1 : rt_got m1.
    Hypothesis SHB1 : rt_shbase m1.
    Hypothesis LAY1 : rt_layout m1.
    Hypothesis UNP1 : unpoisoned m1 B (B + n).
    Hypothesis NZ : (n <> 0)%Z.
    Hypothesis LO0 : (0 <= lo)%Z.
    Section Core.
    Variables (AB AE : Z).
    Hypothesis RAB : (B <= AB <= B + 7 /\ AB mod 8 = 0)%Z.
    Hypothesis RAE : (B + n - 7 <= AE <= B + n /\ AE mod 8 = 0)%Z.

    (* [comment removed for export] *)
    Lemma L4 : forall x5 x11 x12 x13 x14 x15 x16 x17 x18,
      evtF bsegs RNG POST
        (MS (mkR (Z_to_bv 64 354276) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 t1 t2 a0 a1
                 (Z_to_bv 64 (shad AE)) x11 x12 x13 x14 x15 x16 x17
                 x18 (Z_to_bv 64 (shad AB)) (Z_to_bv 64 AE) (Z_to_bv 64 0xcfcf8) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x56854) fc None m1 (seg_rom bsegs)).
    Proof.
      intros. pose proof (bv_unsigned_in_range 64 a1) as Rn. pose proof APP as [LE APP']. unfold KLOW, KHIGH, KEND in APP', KLO.
      assert (SHR : (2147450880 <= shad B /\ shad B <= shad AB /\ shad AB <= shad (B + n - 1) + 1 /\ 2147450880 <= shad AE /\
                     shad AE <= shad (B + n - 1) + 1 /\ shad (B + n - 1) + 1 <= 17594333495296)%Z)
        by (rewrite !shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
      zstep. if_cases K8; zify_cond K8.
      { (* [comment removed for export] *) eapply L5; eassumption. }
      assert (ABE : (AB <= AE)%Z) by (rewrite !shad_div in K8; unfold ASHOFF in K8; Z.div_mod_to_equations; lia).
      pose proof (unpoisoned_core_zero m1 B (B + n) AB AE UNP1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ABE) as SB0.
      assert (SHD : (shad AE - shad AB <= 2^40)%Z) by (rewrite !shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
      zstep. zstep. zstep.
      call_sp mem_is_zero_spec;
        [ exact MI1 | exact ST1 | lia
        | zsimp; replace (shad AB + (shad AE - shad AB))%Z with (shad AE) by lia; exact SB0
        | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia
        | eapply rng_sub'; [exact RSTK | lia] | ].
      fold_lits. zstep. if_cases K9; zify_cond K9. { exfalso. clear - K9. cbv in K9. lia. }
      eapply L5; eassumption.
    Qed.

    (* [comment removed for export] *)
    Lemma L3 : forall x5 x12 x13 x14 x15 x16 x17,
      evtF bsegs RNG POST
        (MS (mkR (Z_to_bv 64 354276) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 t1 t2 a0 a1
                 (Z_to_bv 64 (shad AE)) (Z_to_bv 64 2147450880) x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 (n + B)) (Z_to_bv 64 (shad AB)) (Z_to_bv 64 AE) (Z_to_bv 64 0xcfcf8) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x56800) fc None m1 (seg_rom bsegs)).
    Proof.
      intros. pose proof (bv_unsigned_in_range 64 a1) as Rn. pose proof APP as [LE APP']. unfold KLOW, KHIGH, KEND in APP', KLO.
      do 3 zstep.
      destruct (unpoisoned_check_rd bsegs m1 B (B + n) (n + B - 1) 1 UNP1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b2 & RD2 & CK2).
      unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
      zstep. rewrite sxb_sval. zstep. if_cases K6; zify_cond K6.
      { apply L4. }
      zstep. zstep. if_cases K7; zify_lts K7. 2:{ exfalso. Z.div_mod_to_equations. lia. }
      apply L4.
    Qed.
    End Core.

    (* [comment removed for export] *)
    Lemma L2 : forall x5 x12 x13 x14 x15 x16 x17,
      evtF bsegs RNG POST
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 t1 t2 a0 a1
                 (Z_to_bv 64 2147450879) (Z_to_bv 64 2147450880) x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 (n + B)) s3 s4 (Z_to_bv 64 0xcfcf8) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x567c4) fc None m1 (seg_rom bsegs)).
    Proof.
      intros. pose proof (bv_unsigned_in_range 64 a1) as Rn. pose proof APP as [LE APP']. unfold KLOW, KHIGH, KEND in APP', KLO.
      zstep. if_cases K5; zify_cond K5. { exfalso; lia. }
      do 3 zstep.
      change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia.
      remember (B + 7 - (B + 7) mod 2 ^ 3)%Z as AB eqn:HAB.
      remember (n + B - (n + B) mod 2 ^ 3)%Z as AE eqn:HAE.
      assert (RAB : (B <= AB <= B + 7 /\ AB mod 8 = 0)%Z) by (subst AB; Z.div_mod_to_equations; lia).
      assert (RAE : (B + n - 7 <= AE <= B + n /\ AE mod 8 = 0)%Z) by (subst AE; Z.div_mod_to_equations; lia).
      clear HAB HAE.
      zstep. call m2s_spec; [assumption|assumption|assumption|assumption| zsimp; unfold KLOW, KHIGH, KEND; lia |]. zsimp.
      do 3 zstep. call m2s_spec; [assumption|assumption|assumption|assumption| zsimp; unfold KLOW, KHIGH, KEND; lia |]. zsimp.
      do 3 zstep.
      destruct (unpoisoned_check_rd bsegs m1 B (B + n) B 1 UNP1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b1 & RD1 & CK1).
      unfold shad, ASHOFF in RD1.
      pose proof (sval_range b1) as SR1.
      zstep. rewrite sxb_sval. zstep. if_cases K6; zify_cond K6.
      { eapply L3; eassumption. }
      (* [comment removed for export] *)
      zstep. zstep. if_cases K7; zify_lts K7. { exfalso. Z.div_mod_to_equations. lia. }
      eapply L3; eassumption.
    Qed.

    (* [comment removed for export] *)
    Lemma L1 : forall x5 x13 x14 x15 x16 x17,
      evtF bsegs RNG POST
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 t1 t2 a0 a1
                 (Z_to_bv 64 2147450879) (Z_to_bv 64 2147450880) (Z_to_bv 64 2147450879) x13 x14 x15 x16 x17
                 s2 s3 s4 (Z_to_bv 64 0xcfcf8) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x5677c) fc None m1 (seg_rom bsegs)).
    Proof.
      intros. pose proof (bv_unsigned_in_range 64 a1) as Rn. pose proof APP as [LE APP']. unfold KLOW, KHIGH, KEND in APP', KLO.
      zstep. zstep. if_cases K1; zify_cond K1.
      - apply L2.
      - do 7 zstep. fold_lits. zsimp. zstep. if_cases K2; zify_cond K2. 2:{ exfalso; lia. }
        do 6 zstep. if_cases K3; zify_cond K3. { exfalso; lia. }
        zstep. if_cases K4; zify_cond K4. { exfalso; lia. }
        apply L2.
    Qed.
  End AfterFrame.

  Lemma rip_body :
    evtF bsegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x566f0) fc None m (seg_rom bsegs)).
  Proof.
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (bv_unsigned_in_range 64 a1) as Rn.
    pose proof APP as [LE APP']. unfold KLOW, KHIGH, KEND in APP', KLO.
    assert (LO' : (lo <= bv_unsigned sp - 64)%Z) by lia.
    carve_frame 64%nat ST.
    do 8 zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
      lazymatch goal with MU1 : munch _ m m1 |- _ =>
        pose proof (unpoisoned_munch _ m m1 B (B + n) UNP MU1
                      ltac:(rewrite !shad_div; unfold ASHOFF; cbn; Z.div_mod_to_equations; lia)) as UNP1 end end.
    zstep. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *) do 11 zstep. release_frame FR ST (bv_unsigned sp). finish. }
    do 7 zstep. fold_lits. zsimp. do 2 zstep.
    zstep. if_cases K1; zify_cond K1.
    - eapply L1; eassumption.
    - do 7 zstep. fold_lits. zsimp. zstep. if_cases K2; zify_cond K2. 2:{ exfalso; lia. }
      do 6 zstep. if_cases K3; zify_cond K3. { exfalso; lia. }
      zstep. if_cases K4; zify_cond K4. { exfalso; lia. }
      eapply L1; eassumption.
  Qed.
End Proofs.

Lemma rip_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 80)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_shbase m -> rt_layout m ->
  app_blk (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a1) ->
  unpoisoned m (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a1) ->
  (bv_unsigned a1 <= 2^40)%Z ->
  rng_aimg RNG ->
  rng RNG lo (bv_unsigned sp - lo) ->
  rng RNG (shad (bv_unsigned a0)) (shad (bv_unsigned a0 + bv_unsigned a1 - 1) + 1 - shad (bv_unsigned a0)) ->
  evtF bsegs RNG (rip_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x566f0) fc None m (seg_rom bsegs)).
Proof. intros until lo. intros MI ST LO KLO GOT SHB LAY APP UNP NSZ RI RSTK RSH. eapply rip_body; eassumption. Qed.
End CANSEC2.
