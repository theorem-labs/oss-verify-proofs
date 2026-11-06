(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ZBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg RtCells ShadowTac F_rip. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_m2s_b__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ShadowTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_rip OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_tryinit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_pure. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_printf_lib__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_strnlen. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_lock__A3S. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_pure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_lib__A3S.I_printf_lib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strnlen OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_strlen.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.


Section CANSEC1. Context {rc : runConstT}.
Definition strlen_i_entry := 0x4450c%Z.
Definition STRLEN_I_DEPTH : Z := 2224.

Definition strlen_i_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S : Z) (str slack : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length str))) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2224, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp) /\ bytes_at asegs m' S (str ++ Z_to_bv 8 0 :: slack).

Section STRLEN.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (str slack : list byte) (RLO RHI : Z).
  Notation S := (bv_unsigned a0).
  Notation L0 := (Z.of_nat (length str)).
  Notation N := (Z.of_nat (length str) + 1)%Z.
  Notation full := (str ++ Z_to_bv 8 0 :: slack).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 2224)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis GOT : rt_got m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis INI : rt_inited m.
  Hypothesis LAY : rt_layout m.
  Hypothesis RSL : rt_real_strlen m.
  Hypothesis ISL : rt_isl m.
  Hypothesis STR : bytes_at asegs m S full.
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) str.
  Hypothesis PAD : ((- (S + L0 + 1)) mod 8 <= Z.of_nat (length slack))%Z.
  Hypothesis SEPB : (S + Z.of_nat (length full) <= lo \/ bv_unsigned sp <= S)%Z.
  Hypothesis APP : app_blk S (S + N).
  Hypothesis UNP : unpoisoned m S (S + N).
  Hypothesis NSZ : (N <= 2^40)%Z.
  Hypothesis R1 : (RLO <= S /\ S + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z.
  Hypothesis WR1 : wr_at asegs m (shad RLO) (shad RHI - shad RLO).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RB : rng RNG S (Z.of_nat (length full)).
  Hypothesis RSH1 : rng RNG (shad RLO) (shad RHI - shad RLO).

  Notation POST := (strlen_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S str slack lo m).
  Notation SAVES := [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Definition SINV (mc : word -> option byte) : Prop :=
    rw_cells asegs mc (bv_unsigned sp + -64) SAVES
    /\ stk asegs mc lo (bv_unsigned sp + -2144) /\ stk asegs mc (bv_unsigned sp + -2144) (bv_unsigned sp + -64)
    /\ munch [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m mc /\ wmono asegs m mc /\ mem_inv asegs mc
    /\ rt_got mc /\ rt_shbase mc /\ rt_layout mc
    /\ unpoisoned mc S (S + N) /\ wr_at asegs mc (shad RLO) (shad RHI - shad RLO) /\ bytes_at asegs mc S full.

  Definition SBND : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2224 /\ KHIGH <= lo /\ bv_unsigned sp < 2^64 /\ 1 <= N /\ N <= 2^40
     /\ 0 <= S /\ S + N + 8 <= KEND
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad S /\ shad (S + N - 1) + 1 <= shad RHI /\ shad RHI <= KHIGH
     /\ 0 <= Z.shiftr S 3 < 2^44 /\ -1 <= Z.shiftr (S + N + -1) 3 < 2^44
     /\ shad RLO mod 8 = 0 /\ shad RHI mod 8 = 0
     /\ RLO <= S /\ S + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0)%Z.
  #[using="m slack ST LO KLO APP NSZ R1"] Lemma SBND_ok : SBND.
  Proof.
    unfold SBND. destruct ST as (LOW & _). destruct APP as [LES AS]. unfold KLOW, KHIGH, KEND in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    pose proof (bv_unsigned_in_range 64 a0) as SR. unfold bv_modulus in SR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SR.
    rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF.
    Z.div_mod_to_equations. lia.
  Qed.
  Ltac acc_facts B ::= pose proof SBND_ok as B; unfold SBND, KHIGH, KEND in B.

  Definition SBL : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2224 /\ 17594333495296 <= lo /\ bv_unsigned sp < 2^64 /\ 1 <= N /\ N <= 2^40
     /\ 0 <= S /\ S + N + 8 <= 2^47
     /\ 0 <= Z.shiftr S 3 < 2^44 /\ -1 <= Z.shiftr (S + N + -1) 3 < 2^44
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad S /\ shad (S + N - 1) + 1 <= shad RHI /\ shad RHI <= 17594333495296)%Z.
  #[using="m slack ST LO KLO APP NSZ R1"] Lemma SBL_ok : SBL. Proof. pose proof SBND_ok as B. unfold SBND, KHIGH, KEND in B. unfold SBL. lia. Qed.

  Ltac sinv_open H := destruct H as (FR1 & ST1 & STM1 & MU1 & WM1 & MI1 & GOT1 & SHB1 & LAY1 & UNP1 & WR11 & STR1).
  Ltac shide_all :=
    change (?P) with (sf_hide P) in R1; change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO;
    change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST; change (?P) with (sf_hide P) in SEPB;
    change (?P) with (sf_hide P) in GOT; change (?P) with (sf_hide P) in SHB; change (?P) with (sf_hide P) in INI;
    change (?P) with (sf_hide P) in LAY; change (?P) with (sf_hide P) in UNP; change (?P) with (sf_hide P) in WR1;
    change (?P) with (sf_hide P) in RSL; change (?P) with (sf_hide P) in ISL;
    change (?P) with (sf_hide P) in STR; change (?P) with (sf_hide P) in PAD.
  Ltac sprep IV :=
    pose proof IV as IV0; sinv_open IV;
    pose proof SBL_ok as BL0; unfold SBL in BL0;
    assert (RSTK' : rng RNG (bv_unsigned sp + -2224) 2224) by (eapply rng_sub'; [exact RSTK| lia]);
    shide_all.

  #[using="ST LO KLO STR SEPB APP UNP NSZ R1 WR1"] Lemma sinv_of : forall mc,
    rw_cells asegs mc (bv_unsigned sp + -64) SAVES ->
    stk asegs mc lo (bv_unsigned sp + -2144) -> stk asegs mc (bv_unsigned sp + -2144) (bv_unsigned sp + -64) ->
    munch [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m mc -> wmono asegs m mc -> mem_inv asegs mc ->
    rt_got mc -> rt_shbase mc -> rt_layout mc -> SINV mc.
  Proof.
    intros mc FR1 ST1 STM1 MU1 WM1 MI1 G1 G2 G3. pose proof SBND_ok as B. unfold SBND, KHIGH, KEND in B.
    repeat (split; [assumption|]).
    assert (SS : (shad (S + N - 1) + 1 <= 17594333495296)%Z) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
    split. { eapply unpoisoned_munch; [exact UNP | exact MU1 |]. cbn [disjoint_from]. lia. }
    split. { eapply wr_at_transport; eassumption. }
    eapply bytes_at_transport; [exact STR | exact MU1 |]. cbn [disjoint_from]. lia.
  Qed.

  (* [comment removed for export] *)
  Definition sregs (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31 : word) :=
    mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17
        a0 (Z_to_bv 64 0x140128) (Z_to_bv 64 (bv_unsigned sp + -2136)) x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31.

  (* [comment removed for export] *)
  #[using="ST LO KLO APP NSZ R1 RSTK"] Lemma SX : forall mc x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31, SINV mc ->
    evtF asegs RNG POST (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 (Z_to_bv 64 L0) x11 x12 x13 x14 x15 x16 x17
                                 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x445c4) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. sprep IV.
    do 11 zstep.
    pose proof (stk_merge _ _ _ _ _ ST1 STM1 ltac:(lia)) as SK.
    pose proof (stk_release _ _ _ _ _ SK FR1 ltac:(lia)) as SK2. cbn [cells_size csize Nat.add] in SK2.
    replace (bv_unsigned sp + -64 + Z.of_nat 64)%Z with (bv_unsigned sp) in SK2 by lia.
    apply evtF_done. unfold strlen_i_post.
    replace (bv_unsigned sp - 2224)%Z with (bv_unsigned sp + -2224)%Z by lia.
    do 15 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="ST LO KLO APP NSZ R1 RSTK"] Lemma SOK : forall mc x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31, SINV mc ->
    evtF asegs RNG POST (MS (sregs x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 L0) x22 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x44798) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. unfold sregs. sprep IV.
    zstep. zstep. eapply SX; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="ST LO KLO APP NSZ R1 RSTK RSH1"] Lemma SL : forall mc (k : nat) (c : Z) x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31,
    SINV mc -> (1 <= N <= 64)%Z -> Z.to_nat (shad (S + N - 1) - c) = k -> (shad S <= c < shad (S + N - 1))%Z ->
    evtF asegs RNG POST (MS (sregs x1 x5 x6 x7 x9 (Z_to_bv 64 0) (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (S + N + -1) 3)) x13 x14 x15 x16 x17
                                   (Z_to_bv 64 L0) x22 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x446bc) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1 Hk Hc. unfold sregs. sprep IV.
    revert c x13 Hk Hc. induction k as [|k IH]; intros c x13 Hk Hc; [exfalso; lia|].
    assert (SLE : (shad (S + N - 1) = 2147450880 + Z.shiftr (S + N + -1) 3)%Z) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
    pose proof (unpoisoned_full_rd asegs mc S (S + N) c UNP1 ltac:(lia)
                  ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K1; zify_cond K1.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply SOK; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="ST LO KLO APP NSZ R1 RSTK RSH1"] Lemma SE : forall mc x1 x5 x6 x7 x9 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31, SINV mc -> (1 <= N <= 64)%Z ->
    evtF asegs RNG POST (MS (sregs x1 x5 x6 x7 x9 (Z_to_bv 64 L0) (Z_to_bv 64 (2147450880 + Z.shiftr S 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (S + N + -1) 3))
                                   (Z_to_bv 64 (S + N + -1)) x14 x15 x16 x17 x21 x22 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x4469c) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1. unfold sregs. sprep IV.
    destruct (unpoisoned_check_rd asegs mc S (S + N) (S + N + -1) 1 UNP1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b2 & RD2 & CK2).
    unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
    zstep. zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((S + N + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply SOK; eassumption.
    - eapply (SL mc); [exact IV0 | exact N1 | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="ST LO KLO STR SEPB APP UNP NSZ R1 WR1 RI RSTK RSH1"] Lemma SC : forall mc x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x28 x29 x30 x31, SINV mc ->
    evtF asegs RNG POST (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 (Z_to_bv 64 L0) x11 x12 x13 x14 x15 x16 x17
                                 a0 (Z_to_bv 64 0x140128) x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x44570) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. sprep IV.
    do 5 zstep.
    rewrite zb_lxor_ones by lia. if_cases K0; zify_cond K0. { exfalso. clear -K0 BL0. lia. } clear K0.
    zstep. zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      zstep. zstep. if_cases K3; zify_cond K3. 2:{ exfalso. clear -K3 BL0. lia. } clear K3.
      zstep. zstep. zstep.
      unfold sf_hide in LO.
      call_sp rip_spec;
        [ exact MI1 | exact ST1 | lia | unfold KHIGH; lia | exact GOT1 | exact SHB1 | exact LAY1
        | zsimp; exact APP | zsimp; exact UNP1
        | zsimp; pose proof SBND_ok as B9; unfold SBND in B9; lia
        | eapply rng_sub'; [exact RSTK | lia] | ].
      zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
      eapply SOK. eapply sinv_of; eassumption.
    - (* [comment removed for export] *)
      assert (N1 : (1 <= N <= 64)%Z) by (clear - K2 BL0; lia).
      do 4 zstep. replace (L0 + S)%Z with (S + N + -1)%Z by lia.
      do 6 zstep.
      change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
      unfold sf_hide in R1.
      destruct (shadow_probe8 asegs mc RLO RHI S WR11 ltac:(apply no_image_asan; pose proof SBND_ok as B9; unfold SBND in B9; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w1 P1].
      destruct (shadow_probe8 asegs mc RLO RHI (S + N + -1) WR11 ltac:(apply no_image_asan; pose proof SBND_ok as B9; unfold SBND in B9; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w2 P2].
      unfold ASHOFF in P1, P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply SE; eassumption.
      + eapply SX; eassumption.
  Qed.

  #[using="RLO RHI MI ST LO KLO GOT SHB INI LAY RSL ISL STR NONUL PAD SEPB APP UNP NSZ R1 WR1 RI RSTK RB RSH1"] Lemma strlen_i_body :
    evtF asegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x4450c) fc None m (seg_rom asegs)).
  Proof.
    pose proof (munch_refl [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof SBL_ok as BL0. unfold SBL in BL0.
    pose proof (bytes_at_bound _ _ _ _ STR) as BB.
    assert (RSTK' : rng RNG (bv_unsigned sp + -2224) 2224) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof MI as MIc. pose proof ST as ST0. pose proof GOT as GOTc. pose proof SHB as SHBc. pose proof INI as INIc.
    pose proof LAY as LAYc. pose proof RSL as RSLc. pose proof ISL as ISLc.
    assert (STRc : bytes_at asegs m S full) by exact STR.
    shide_all.
    carve_frame 64%nat ST0.
    destruct (stk_split _ _ lo (bv_unsigned sp + -2144) _ ST0 ltac:(lia)) as [ST1 STM]. clear ST0.
    do 12 zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. cbv beta. rewrite sxb_sval. change (sval (Z_to_bv 8 1)) with 1%Z. zstep. zstep. zstep. fold_lits. zstep.
    zstep. if_cases K0; zify_cond K0. { exfalso. clear -K0. cbv in K0. lia. } clear K0.
    zstep. call_sp tryinit_spec. all: iprem.
    do 5 zstep.
    assert (STRn : bytes_at asegs x13 S full).
    { unfold sf_hide in STR, SEPB, LO. eapply bytes_at_transport; [exact STR | exact MU |]. cbn [disjoint_from]. clear -SEPB LO BL0. lia. }
    unfold sf_hide in PAD.
    call strlen_spec. all: iprem.
    assert (ISL1 : rw_cells asegs x28 0x140220 [CB 3 (repeat (Z_to_bv 8 1) 3); C1 (Z_to_bv 8 1); CB 4 (repeat (Z_to_bv 8 1) 4)]).
    { pose proof ISLc as ISL'. recell ISL' 0%nat 1%nat [CB 3 (repeat (Z_to_bv 8 1) 3); C1 (Z_to_bv 8 1); CB 4 (repeat (Z_to_bv 8 1) 4)]. exact ISL'. }
    zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1. cbv in K1. lia. } clear K1.
    zstep. zstep. zstep. cbv beta. rewrite unsigned_lit8 by lia. zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2. cbv in K2. lia. } clear K2.
    eapply SC. eapply sinv_of; eassumption.
  Qed.
End STRLEN.

#[using="Type"] Lemma strlen_i_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (str slack : list byte) (RLO RHI : Z),
  let S := bv_unsigned a0 in let N := (Z.of_nat (length str) + 1)%Z in
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2224)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_strlen m -> rt_isl m ->
  bytes_at asegs m S (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  ((- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  (S + Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack)) <= lo \/ bv_unsigned sp <= S)%Z ->
  app_blk S (S + N) -> unpoisoned m S (S + N) -> (N <= 2^40)%Z ->
  (RLO <= S /\ S + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z ->
  wr_at asegs m (shad RLO) (shad RHI - shad RLO) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S (Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack))) ->
  rng RNG (shad RLO) (shad RHI - shad RLO) ->
  evtF asegs RNG (strlen_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4450c) fc None m (seg_rom asegs)).
Proof. intros. eapply strlen_i_body; eassumption. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma strlen_w_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (str slack : list byte) (RLO RHI : Z),
  let S := bv_unsigned a0 in let N := (Z.of_nat (length str) + 1)%Z in
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2224)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_strlen m -> rt_isl m ->
  bytes_at asegs m S (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  ((- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  (S + Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack)) <= lo \/ bv_unsigned sp <= S)%Z ->
  app_blk S (S + N) -> unpoisoned m S (S + N) -> (N <= 2^40)%Z ->
  (RLO <= S /\ S + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z ->
  wr_at asegs m (shad RLO) (shad RHI - shad RLO) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S (Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack))) ->
  rng RNG (shad RLO) (shad RHI - shad RLO) ->
  evtF asegs RNG (strlen_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44468) fc None m (seg_rom asegs)).
Proof.
  intros. assert (RI' : rng_aimg RNG) by assumption.
  zstep. eapply strlen_i_body; eassumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma strlen_wb_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (str slack : list byte),
  let S := bv_unsigned a0 in let N := (Z.of_nat (length str) + 1)%Z in
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2224)%Z -> (KHIGH <= lo)%Z ->
  icptenv m ->
  bytes_at asegs m S (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  ((- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  (S + Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack)) <= lo \/ bv_unsigned sp <= S)%Z ->
  sobj RNG m S (S + N) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S (Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack))) ->
  evtF asegs RNG (strlen_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44468) fc None m (seg_rom asegs)).
Proof.
  intros until slack. intros S N MI ST LO KLO ENV STR NONUL PAD SEPB (APP & UNP & NSZ & RLO & RHI & R1 & WR1 & RSH1) RI RSTK RB.
  eapply (strlen_w_spec RNG) with (RLO := RLO) (RHI := RHI); try eassumption;
    first [ exact (ie_got _ ENV) | exact (ie_shb _ ENV) | exact (ie_ini _ ENV) | exact (ie_lay _ ENV) | exact (ie_strlen _ ENV)
          | exact (ie_isl _ ENV) | (unfold N, S in NSZ; lia) ].
Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ShadowTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_rip.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_tryinit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_pure.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_lib__A3S.I_printf_lib.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strnlen.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_strlen.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.


Section CANSEC1. Context {rc : runConstT}.
Definition strlen_i_entry := 0x44574%Z.
Definition STRLEN_I_DEPTH : Z := 2224.

Definition strlen_i_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S : Z) (str slack : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length str))) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2224, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp) /\ bytes_at asegs m' S (str ++ Z_to_bv 8 0 :: slack).

Section STRLEN.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (str slack : list byte) (RLO RHI : Z).
  Notation S := (bv_unsigned a0).
  Notation L0 := (Z.of_nat (length str)).
  Notation N := (Z.of_nat (length str) + 1)%Z.
  Notation full := (str ++ Z_to_bv 8 0 :: slack).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 2224)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis GOT : rt_got m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis INI : rt_inited m.
  Hypothesis LAY : rt_layout m.
  Hypothesis RSL : rt_real_strlen m.
  Hypothesis ISL : rt_isl m.
  Hypothesis STR : bytes_at asegs m S full.
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) str.
  Hypothesis PAD : ((- (S + L0 + 1)) mod 8 <= Z.of_nat (length slack))%Z.
  Hypothesis SEPB : (S + Z.of_nat (length full) <= lo \/ bv_unsigned sp <= S)%Z.
  Hypothesis APP : app_blk S (S + N).
  Hypothesis UNP : unpoisoned m S (S + N).
  Hypothesis NSZ : (N <= 2^40)%Z.
  Hypothesis R1 : (RLO <= S /\ S + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z.
  Hypothesis WR1 : wr_at asegs m (shad RLO) (shad RHI - shad RLO).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RB : rng RNG S (Z.of_nat (length full)).
  Hypothesis RSH1 : rng RNG (shad RLO) (shad RHI - shad RLO).

  Notation POST := (strlen_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S str slack lo m).
  Notation SAVES := [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Definition SINV (mc : word -> option byte) : Prop :=
    rw_cells asegs mc (bv_unsigned sp + -64) SAVES
    /\ stk asegs mc lo (bv_unsigned sp + -2144) /\ stk asegs mc (bv_unsigned sp + -2144) (bv_unsigned sp + -64)
    /\ munch [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m mc /\ wmono asegs m mc /\ mem_inv asegs mc
    /\ rt_got mc /\ rt_shbase mc /\ rt_layout mc
    /\ unpoisoned mc S (S + N) /\ wr_at asegs mc (shad RLO) (shad RHI - shad RLO) /\ bytes_at asegs mc S full.

  Definition SBND : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2224 /\ KHIGH <= lo /\ bv_unsigned sp < 2^64 /\ 1 <= N /\ N <= 2^40
     /\ 0 <= S /\ S + N + 8 <= KEND
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad S /\ shad (S + N - 1) + 1 <= shad RHI /\ shad RHI <= KHIGH
     /\ 0 <= Z.shiftr S 3 < 2^44 /\ -1 <= Z.shiftr (S + N + -1) 3 < 2^44
     /\ shad RLO mod 8 = 0 /\ shad RHI mod 8 = 0
     /\ RLO <= S /\ S + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0)%Z.
  #[using="m slack ST LO KLO APP NSZ R1"] Lemma SBND_ok : SBND.
  Proof.
    unfold SBND. destruct ST as (LOW & _). destruct APP as [LES AS]. unfold KLOW, KHIGH, KEND in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    pose proof (bv_unsigned_in_range 64 a0) as SR. unfold bv_modulus in SR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SR.
    rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF.
    Z.div_mod_to_equations. lia.
  Qed.
  Ltac acc_facts B ::= pose proof SBND_ok as B; unfold SBND, KHIGH, KEND in B.

  Definition SBL : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2224 /\ 17594333495296 <= lo /\ bv_unsigned sp < 2^64 /\ 1 <= N /\ N <= 2^40
     /\ 0 <= S /\ S + N + 8 <= 2^47
     /\ 0 <= Z.shiftr S 3 < 2^44 /\ -1 <= Z.shiftr (S + N + -1) 3 < 2^44
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad S /\ shad (S + N - 1) + 1 <= shad RHI /\ shad RHI <= 17594333495296)%Z.
  #[using="m slack ST LO KLO APP NSZ R1"] Lemma SBL_ok : SBL. Proof. pose proof SBND_ok as B. unfold SBND, KHIGH, KEND in B. unfold SBL. lia. Qed.

  Ltac sinv_open H := destruct H as (FR1 & ST1 & STM1 & MU1 & WM1 & MI1 & GOT1 & SHB1 & LAY1 & UNP1 & WR11 & STR1).
  Ltac shide_all :=
    change (?P) with (sf_hide P) in R1; change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO;
    change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST; change (?P) with (sf_hide P) in SEPB;
    change (?P) with (sf_hide P) in GOT; change (?P) with (sf_hide P) in SHB; change (?P) with (sf_hide P) in INI;
    change (?P) with (sf_hide P) in LAY; change (?P) with (sf_hide P) in UNP; change (?P) with (sf_hide P) in WR1;
    change (?P) with (sf_hide P) in RSL; change (?P) with (sf_hide P) in ISL;
    change (?P) with (sf_hide P) in STR; change (?P) with (sf_hide P) in PAD.
  Ltac sprep IV :=
    pose proof IV as IV0; sinv_open IV;
    pose proof SBL_ok as BL0; unfold SBL in BL0;
    assert (RSTK' : rng RNG (bv_unsigned sp + -2224) 2224) by (eapply rng_sub'; [exact RSTK| lia]);
    shide_all.

  #[using="ST LO KLO STR SEPB APP UNP NSZ R1 WR1"] Lemma sinv_of : forall mc,
    rw_cells asegs mc (bv_unsigned sp + -64) SAVES ->
    stk asegs mc lo (bv_unsigned sp + -2144) -> stk asegs mc (bv_unsigned sp + -2144) (bv_unsigned sp + -64) ->
    munch [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m mc -> wmono asegs m mc -> mem_inv asegs mc ->
    rt_got mc -> rt_shbase mc -> rt_layout mc -> SINV mc.
  Proof.
    intros mc FR1 ST1 STM1 MU1 WM1 MI1 G1 G2 G3. pose proof SBND_ok as B. unfold SBND, KHIGH, KEND in B.
    repeat (split; [assumption|]).
    assert (SS : (shad (S + N - 1) + 1 <= 17594333495296)%Z) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
    split. { eapply unpoisoned_munch; [exact UNP | exact MU1 |]. cbn [disjoint_from]. lia. }
    split. { eapply wr_at_transport; eassumption. }
    eapply bytes_at_transport; [exact STR | exact MU1 |]. cbn [disjoint_from]. lia.
  Qed.

  (* [comment removed for export] *)
  Definition sregs (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31 : word) :=
    mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17
        a0 (Z_to_bv 64 0x140528) (Z_to_bv 64 (bv_unsigned sp + -2136)) x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31.

  (* [comment removed for export] *)
  #[using="ST LO KLO APP NSZ R1 RSTK"] Lemma SX : forall mc x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31, SINV mc ->
    evtF asegs RNG POST (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 (Z_to_bv 64 L0) x11 x12 x13 x14 x15 x16 x17
                                 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x4462c) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. sprep IV.
    do 11 zstep.
    pose proof (stk_merge _ _ _ _ _ ST1 STM1 ltac:(lia)) as SK.
    pose proof (stk_release _ _ _ _ _ SK FR1 ltac:(lia)) as SK2. cbn [cells_size csize Nat.add] in SK2.
    replace (bv_unsigned sp + -64 + Z.of_nat 64)%Z with (bv_unsigned sp) in SK2 by lia.
    apply evtF_done. unfold strlen_i_post.
    replace (bv_unsigned sp - 2224)%Z with (bv_unsigned sp + -2224)%Z by lia.
    do 15 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="ST LO KLO APP NSZ R1 RSTK"] Lemma SOK : forall mc x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31, SINV mc ->
    evtF asegs RNG POST (MS (sregs x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 L0) x22 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x44800) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. unfold sregs. sprep IV.
    zstep. zstep. eapply SX; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="ST LO KLO APP NSZ R1 RSTK RSH1"] Lemma SL : forall mc (k : nat) (c : Z) x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31,
    SINV mc -> (1 <= N <= 64)%Z -> Z.to_nat (shad (S + N - 1) - c) = k -> (shad S <= c < shad (S + N - 1))%Z ->
    evtF asegs RNG POST (MS (sregs x1 x5 x6 x7 x9 (Z_to_bv 64 0) (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (S + N + -1) 3)) x13 x14 x15 x16 x17
                                   (Z_to_bv 64 L0) x22 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x44724) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1 Hk Hc. unfold sregs. sprep IV.
    revert c x13 Hk Hc. induction k as [|k IH]; intros c x13 Hk Hc; [exfalso; lia|].
    assert (SLE : (shad (S + N - 1) = 2147450880 + Z.shiftr (S + N + -1) 3)%Z) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
    pose proof (unpoisoned_full_rd asegs mc S (S + N) c UNP1 ltac:(lia)
                  ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K1; zify_cond K1.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply SOK; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="ST LO KLO APP NSZ R1 RSTK RSH1"] Lemma SE : forall mc x1 x5 x6 x7 x9 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31, SINV mc -> (1 <= N <= 64)%Z ->
    evtF asegs RNG POST (MS (sregs x1 x5 x6 x7 x9 (Z_to_bv 64 L0) (Z_to_bv 64 (2147450880 + Z.shiftr S 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (S + N + -1) 3))
                                   (Z_to_bv 64 (S + N + -1)) x14 x15 x16 x17 x21 x22 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x44704) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1. unfold sregs. sprep IV.
    destruct (unpoisoned_check_rd asegs mc S (S + N) (S + N + -1) 1 UNP1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b2 & RD2 & CK2).
    unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
    zstep. zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((S + N + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply SOK; eassumption.
    - eapply (SL mc); [exact IV0 | exact N1 | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="ST LO KLO STR SEPB APP UNP NSZ R1 WR1 RI RSTK RSH1"] Lemma SC : forall mc x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x28 x29 x30 x31, SINV mc ->
    evtF asegs RNG POST (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 (Z_to_bv 64 L0) x11 x12 x13 x14 x15 x16 x17
                                 a0 (Z_to_bv 64 0x140528) x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x445d8) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. sprep IV.
    do 5 zstep.
    rewrite zb_lxor_ones by lia. if_cases K0; zify_cond K0. { exfalso. clear -K0 BL0. lia. } clear K0.
    zstep. zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      zstep. zstep. if_cases K3; zify_cond K3. 2:{ exfalso. clear -K3 BL0. lia. } clear K3.
      zstep. zstep. zstep.
      unfold sf_hide in LO.
      call_sp rip_spec;
        [ exact MI1 | exact ST1 | lia | unfold KHIGH; lia | exact GOT1 | exact SHB1 | exact LAY1
        | zsimp; exact APP | zsimp; exact UNP1
        | zsimp; pose proof SBND_ok as B9; unfold SBND in B9; lia
        | eapply rng_sub'; [exact RSTK | lia] | ].
      zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
      eapply SOK. eapply sinv_of; eassumption.
    - (* [comment removed for export] *)
      assert (N1 : (1 <= N <= 64)%Z) by (clear - K2 BL0; lia).
      do 4 zstep. replace (L0 + S)%Z with (S + N + -1)%Z by lia.
      do 6 zstep.
      change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
      unfold sf_hide in R1.
      destruct (shadow_probe8 asegs mc RLO RHI S WR11 ltac:(apply no_image_asan; pose proof SBND_ok as B9; unfold SBND in B9; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w1 P1].
      destruct (shadow_probe8 asegs mc RLO RHI (S + N + -1) WR11 ltac:(apply no_image_asan; pose proof SBND_ok as B9; unfold SBND in B9; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w2 P2].
      unfold ASHOFF in P1, P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply SE; eassumption.
      + eapply SX; eassumption.
  Qed.

  #[using="RLO RHI MI ST LO KLO GOT SHB INI LAY RSL ISL STR NONUL PAD SEPB APP UNP NSZ R1 WR1 RI RSTK RB RSH1"] Lemma strlen_i_body :
    evtF asegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x44574) fc None m (seg_rom asegs)).
  Proof.
    pose proof (munch_refl [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof SBL_ok as BL0. unfold SBL in BL0.
    pose proof (bytes_at_bound _ _ _ _ STR) as BB.
    assert (RSTK' : rng RNG (bv_unsigned sp + -2224) 2224) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof MI as MIc. pose proof ST as ST0. pose proof GOT as GOTc. pose proof SHB as SHBc. pose proof INI as INIc.
    pose proof LAY as LAYc. pose proof RSL as RSLc. pose proof ISL as ISLc.
    assert (STRc : bytes_at asegs m S full) by exact STR.
    shide_all.
    carve_frame 64%nat ST0.
    destruct (stk_split _ _ lo (bv_unsigned sp + -2144) _ ST0 ltac:(lia)) as [ST1 STM]. clear ST0.
    do 12 zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. cbv beta. rewrite sxb_sval. change (sval (Z_to_bv 8 1)) with 1%Z. zstep. zstep. zstep. fold_lits. zstep.
    zstep. if_cases K0; zify_cond K0. { exfalso. clear -K0. cbv in K0. lia. } clear K0.
    zstep. call_sp tryinit_spec. all: iprem.
    do 5 zstep.
    assert (STRn : bytes_at asegs x13 S full).
    { unfold sf_hide in STR, SEPB, LO. eapply bytes_at_transport; [exact STR | exact MU |]. cbn [disjoint_from]. clear -SEPB LO BL0. lia. }
    unfold sf_hide in PAD.
    call strlen_spec. all: iprem.
    assert (ISL1 : rw_cells asegs x28 0x140620 [CB 3 (repeat (Z_to_bv 8 1) 3); C1 (Z_to_bv 8 1); CB 4 (repeat (Z_to_bv 8 1) 4)]).
    { pose proof ISLc as ISL'. recell ISL' 0%nat 1%nat [CB 3 (repeat (Z_to_bv 8 1) 3); C1 (Z_to_bv 8 1); CB 4 (repeat (Z_to_bv 8 1) 4)]. exact ISL'. }
    zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1. cbv in K1. lia. } clear K1.
    zstep. zstep. zstep. cbv beta. rewrite unsigned_lit8 by lia. zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2. cbv in K2. lia. } clear K2.
    eapply SC. eapply sinv_of; eassumption.
  Qed.
End STRLEN.

#[using="Type"] Lemma strlen_i_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (str slack : list byte) (RLO RHI : Z),
  let S := bv_unsigned a0 in let N := (Z.of_nat (length str) + 1)%Z in
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2224)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_strlen m -> rt_isl m ->
  bytes_at asegs m S (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  ((- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  (S + Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack)) <= lo \/ bv_unsigned sp <= S)%Z ->
  app_blk S (S + N) -> unpoisoned m S (S + N) -> (N <= 2^40)%Z ->
  (RLO <= S /\ S + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z ->
  wr_at asegs m (shad RLO) (shad RHI - shad RLO) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S (Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack))) ->
  rng RNG (shad RLO) (shad RHI - shad RLO) ->
  evtF asegs RNG (strlen_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44574) fc None m (seg_rom asegs)).
Proof. intros. eapply strlen_i_body; eassumption. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma strlen_w_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (str slack : list byte) (RLO RHI : Z),
  let S := bv_unsigned a0 in let N := (Z.of_nat (length str) + 1)%Z in
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2224)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_strlen m -> rt_isl m ->
  bytes_at asegs m S (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  ((- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  (S + Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack)) <= lo \/ bv_unsigned sp <= S)%Z ->
  app_blk S (S + N) -> unpoisoned m S (S + N) -> (N <= 2^40)%Z ->
  (RLO <= S /\ S + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z ->
  wr_at asegs m (shad RLO) (shad RHI - shad RLO) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S (Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack))) ->
  rng RNG (shad RLO) (shad RHI - shad RLO) ->
  evtF asegs RNG (strlen_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x444d0) fc None m (seg_rom asegs)).
Proof.
  intros. assert (RI' : rng_aimg RNG) by assumption.
  zstep. eapply strlen_i_body; eassumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma strlen_wb_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (str slack : list byte),
  let S := bv_unsigned a0 in let N := (Z.of_nat (length str) + 1)%Z in
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2224)%Z -> (KHIGH <= lo)%Z ->
  icptenv m ->
  bytes_at asegs m S (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  ((- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  (S + Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack)) <= lo \/ bv_unsigned sp <= S)%Z ->
  sobj RNG m S (S + N) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S (Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack))) ->
  evtF asegs RNG (strlen_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x444d0) fc None m (seg_rom asegs)).
Proof.
  intros until slack. intros S N MI ST LO KLO ENV STR NONUL PAD SEPB (APP & UNP & NSZ & RLO & RHI & R1 & WR1 & RSH1) RI RSTK RB.
  eapply (strlen_w_spec RNG) with (RLO := RLO) (RHI := RHI); try eassumption;
    first [ exact (ie_got _ ENV) | exact (ie_shb _ ENV) | exact (ie_ini _ ENV) | exact (ie_lay _ ENV) | exact (ie_strlen _ ENV)
          | exact (ie_isl _ ENV) | (unfold N, S in NSZ; lia) ].
Qed.
End CANSEC1.
End TwB.
