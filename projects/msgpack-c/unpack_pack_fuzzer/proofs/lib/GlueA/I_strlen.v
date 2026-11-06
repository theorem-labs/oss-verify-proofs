(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import StrFun.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import Shadow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import ZBridge.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import StepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg RtCells ShadowTac F_rip F_tryinit I_printf_lib. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require I_fwrite. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_fwrite.I_strnlen.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import F_strlen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.

Notation rt_real_strlen m := (rw_cells asegs m 0xd32b8 [C8 (Z_to_bv 64 0xc7af0)]).

Section CANSEC3. Context {rc : runConstT}.
Definition strlen_i_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S : Z) (str slack : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length str))) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2160, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
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
  Hypothesis LO : (lo <= bv_unsigned sp - 2160)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis GOT : rt_got m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis INI : rt_inited m.
  Hypothesis LAY : rt_layout m.
  Hypothesis RSL : rt_real_strlen m.
  Hypothesis ISL : rt_isl m.
  Hypothesis BUF : bytes_at asegs m S full.
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) str.
  Hypothesis PAD : ((- (S + L0 + 1)) mod 8 <= Z.of_nat (length slack))%Z.
  Hypothesis SEPB : (S + (L0 + 1 + Z.of_nat (length slack)) <= lo \/ bv_unsigned sp <= S)%Z.
  Hypothesis SPOS : (0 < S)%Z.
  Hypothesis APP : app_blk S (S + N).
  Hypothesis UNP : unpoisoned m S (S + N).
  Hypothesis NSZ : (L0 <= 63)%Z.
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
    /\ munch [(bv_unsigned sp + -2160, bv_unsigned sp)]%Z m mc /\ wmono asegs m mc /\ mem_inv asegs mc
    /\ rt_got mc /\ rt_shbase mc /\ rt_layout mc
    /\ unpoisoned mc S (S + N) /\ wr_at asegs mc (shad RLO) (shad RHI - shad RLO) /\ bytes_at asegs mc S full.

  Definition SBND : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2160 /\ KHIGH <= lo /\ bv_unsigned sp < 2^64 /\ 1 <= N /\ N <= 64
     /\ 0 <= S /\ S + N + 8 <= KEND
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad S /\ shad (S + N - 1) + 1 <= shad RHI /\ shad RHI <= KHIGH
     /\ 0 <= Z.shiftr S 3 < 2^44 /\ -1 <= Z.shiftr (S + N + -1) 3 < 2^44
     /\ shad RLO mod 8 = 0 /\ shad RHI mod 8 = 0
     /\ RLO <= S /\ S + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0)%Z.
  Lemma full_len : Z.of_nat (length full) = (L0 + 1 + Z.of_nat (length slack))%Z.
  Proof. rewrite length_app. cbn [length]. lia. Qed.
  Lemma SBND_ok : SBND.
  Proof.
    unfold SBND. destruct ST as (LOW & _). destruct APP as [LES AS]. unfold KLOW, KHIGH, KEND in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF.
    Z.div_mod_to_equations. lia.
  Qed.
  Ltac acc_facts B ::= pose proof SBND_ok as B; unfold SBND, KHIGH, KEND in B.

  Definition SBL : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2160 /\ 17594333495296 <= lo /\ bv_unsigned sp < 2^64 /\ 1 <= N <= 64
     /\ 0 <= S /\ S + N + 8 <= 2^47
     /\ 0 <= Z.shiftr S 3 < 2^44 /\ -1 <= Z.shiftr (S + N + -1) 3 < 2^44
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad S /\ shad (S + N - 1) + 1 <= shad RHI /\ shad RHI <= 17594333495296)%Z.
  Lemma SBL_ok : SBL. Proof. pose proof SBND_ok as B. unfold SBND, KHIGH, KEND in B. unfold SBL. lia. Qed.

  Ltac sinv_open H := destruct H as (FR1 & ST1 & STM1 & MU1 & WM1 & MI1 & GOT1 & SHB1 & LAY1 & UNP1 & WR11 & BUF1).
  Ltac shide_all :=
    change (?P) with (sf_hide P) in R1; change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO;
    change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST; change (?P) with (sf_hide P) in SEPB;
    change (?P) with (sf_hide P) in GOT; change (?P) with (sf_hide P) in SHB; change (?P) with (sf_hide P) in INI;
    change (?P) with (sf_hide P) in LAY; change (?P) with (sf_hide P) in UNP; change (?P) with (sf_hide P) in WR1;
    change (?P) with (sf_hide P) in RSL; change (?P) with (sf_hide P) in ISL;
    change (?P) with (sf_hide P) in BUF; change (?P) with (sf_hide P) in NONUL; change (?P) with (sf_hide P) in PAD.
  Ltac sprep IV :=
    pose proof IV as IV0; sinv_open IV;
    pose proof SBL_ok as BL; unfold SBL in BL;
    assert (RSTK' : rng RNG (bv_unsigned sp + -2160) 2160) by (eapply rng_sub'; [exact RSTK| lia]);
    shide_all.

  Lemma sinv_of : forall mc,
    rw_cells asegs mc (bv_unsigned sp + -64) SAVES ->
    stk asegs mc lo (bv_unsigned sp + -2144) -> stk asegs mc (bv_unsigned sp + -2144) (bv_unsigned sp + -64) ->
    munch [(bv_unsigned sp + -2160, bv_unsigned sp)]%Z m mc -> wmono asegs m mc -> mem_inv asegs mc ->
    rt_got mc -> rt_shbase mc -> rt_layout mc -> SINV mc.
  Proof.
    intros mc FR1 ST1 STM1 MU1 WM1 MI1 G1 G2 G3. pose proof SBND_ok as B. unfold SBND, KHIGH, KEND in B.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB. pose proof full_len as FLN.
    repeat (split; [assumption|]).
    assert (SS : (shad (S + N - 1) + 1 <= 17594333495296)%Z) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
    split. { eapply unpoisoned_munch; [exact UNP | exact MU1 |]. cbn [disjoint_from]. lia. }
    split. { eapply wr_at_transport; eassumption. }
    eapply bytes_at_transport; [exact BUF | exact MU1 |]. cbn [disjoint_from]. lia.
  Qed.

  Lemma SX : forall mc x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31, SINV mc ->
    evtF asegs RNG POST (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 L0) x11 x12 x13 x14 x15 x16 x17
                                 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x4d61c) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. sprep IV.
    do 11 zstep.
    pose proof (stk_merge _ _ _ _ _ ST1 STM1 ltac:(lia)) as SK.
    pose proof (stk_release _ _ _ _ _ SK FR1 ltac:(lia)) as SK2. cbn [cells_size csize Nat.add] in SK2.
    replace (bv_unsigned sp + -64 + Z.of_nat 64)%Z with (bv_unsigned sp) in SK2 by lia.
    apply evtF_done. unfold strlen_i_post.
    replace (bv_unsigned sp - 2160)%Z with (bv_unsigned sp + -2160)%Z by lia.
    do 15 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; assumption.
  Qed.

  Definition sregs (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31 : word) :=
    mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17
        a0 (Z_to_bv 64 0x16b5e8) (Z_to_bv 64 (bv_unsigned sp + -2136)) x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31.

  Lemma SL : forall mc (k : nat) (c : Z) x1 x5 x6 x7 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31,
    SINV mc -> Z.to_nat (shad (S + N - 1) - c) = k -> (shad S <= c < shad (S + N - 1))%Z ->
    evtF asegs RNG POST (MS (sregs x1 x5 x6 x7 (Z_to_bv 64 N) (Z_to_bv 64 0) (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (S + N + -1) 3)) x13 x14 x15 x16 x17
                                   (Z_to_bv 64 L0) x22 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x4d714) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV Hk Hc. unfold sregs. sprep IV.
    revert c x13 Hk Hc. induction k as [|k IH]; intros c x13 Hk Hc; [exfalso; lia|].
    assert (SLE : (shad (S + N - 1) = 2147450880 + Z.shiftr (S + N + -1) 3)%Z) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
    pose proof (unpoisoned_full_rd asegs mc S (S + N) c UNP1 ltac:(lia)
                  ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K1; zify_cond K1.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      zstep. zstep. eapply SX; eassumption.
  Qed.

  Lemma SE : forall mc x1 x5 x6 x7 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31, SINV mc ->
    evtF asegs RNG POST (MS (sregs x1 x5 x6 x7 (Z_to_bv 64 N) (Z_to_bv 64 L0) (Z_to_bv 64 (2147450880 + Z.shiftr S 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (S + N + -1) 3))
                                   (Z_to_bv 64 (S + N + -1)) x14 x15 x16 x17 x21 x22 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x4d6f4) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. unfold sregs. sprep IV.
    destruct (unpoisoned_check_rd asegs mc S (S + N) (S + N + -1) 1 UNP1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b2 & RD2 & CK2).
    unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
    zstep. zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((S + N + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      zstep. zstep. eapply SX; eassumption.
    - eapply (SL mc); [exact IV0 | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      Z.div_mod_to_equations; lia.
  Qed.

  Lemma SJ : forall mc x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x28 x29 x30 x31, SINV mc ->
    evtF asegs RNG POST (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp (Z_to_bv 64 1) (Z_to_bv 64 L0) x11 x12 x13 x14 x15 x16 x17
                                 a0 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x4d5b4) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. sprep IV.
    assert (ISL1 : rw_cells asegs mc 0x16b6e0 [CB 3 (repeat (Z_to_bv 8 1) 3); C1 (Z_to_bv 8 1); CB 4 (repeat (Z_to_bv 8 1) 4)]).
    { unfold sf_hide in ISL. pose proof ISL as ISL'.
      eapply rw_cells_transport in ISL'; [| exact MU1 | exact WM1 | cbn [disjoint_from cells_size csize Nat.add]; lia].
      recell ISL' 0%nat 1%nat [CB 3 (repeat (Z_to_bv 8 1) 3); C1 (Z_to_bv 8 1); CB 4 (repeat (Z_to_bv 8 1) 4)]. exact ISL'. }
    zstep. if_cases K0; zify_cond K0. { exfalso. clear -K0. cbv in K0. lia. } clear K0.
    zstep. zstep. zstep. cbv beta. rewrite unsigned_lit8 by lia. zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1. cbv in K1. lia. } clear K1.
    zstep. zstep. rewrite zb_lxor_ones by lia. zstep. zstep. zstep. if_cases K3; zify_cond K3. { exfalso. clear -K3 BL. lia. }
    zstep. zstep. if_cases K4; zify_cond K4. { exfalso. clear -K4 NSZ. lia. }
    do 4 zstep. replace (L0 + S)%Z with (S + N + -1)%Z by lia. do 6 zstep.
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

  Lemma strlen_i_body :
    evtF asegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x4d564) fc None m (seg_rom asegs)).
  Proof.
    pose proof (munch_refl [(bv_unsigned sp + -2160, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof SBL_ok as BL0. unfold SBL in BL0.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    assert (RSTK' : rng RNG (bv_unsigned sp + -2160) 2160) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof MI as MIc. pose proof ST as ST0. pose proof GOT as GOTc. pose proof SHB as SHBc. pose proof INI as INIc.
    pose proof LAY as LAYc. pose proof RSL as RSLc.
    pose proof APP as APPc. pose proof WR1 as WR1c. pose proof R1 as R1c.
    assert (BUFc : bytes_at asegs m S full) by exact BUF.
    assert (NONULc : ~ In (Z_to_bv 8 0) str) by exact NONUL.
    assert (PADc : ((- (S + L0 + 1)) mod 8 <= Z.of_nat (length slack))%Z) by exact PAD.
    assert (RBc : rng RNG S (Z.of_nat (length full))) by exact RB.
    shide_all.
    carve_frame 64%nat ST0.
    destruct (stk_split _ _ lo (bv_unsigned sp + -2144) _ ST0 ltac:(lia)) as [ST1 STM]. clear ST0.
    do 12 zstep.

    zstep. zstep. zstep. cbv beta. rewrite sxb_sval. change (sval (Z_to_bv 8 1)) with 1%Z. zstep. zstep. zstep. fold_lits. zstep.
    zstep. if_cases K0; zify_cond K0. { exfalso. clear -K0. cbv in K0. lia. } clear K0.
    zstep. call_sp tryinit_spec. all: iprem.
    do 4 zstep. zstep.

    call strlen_spec. all: iprem.
    eapply SJ. eapply sinv_of; eassumption.
  Qed.
End STRLEN.

Lemma strlen_i_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (str slack : list byte) (RLO RHI : Z),
  let S := bv_unsigned a0 in let N := (Z.of_nat (length str) + 1)%Z in
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2160)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_strlen m -> rt_isl m ->
  bytes_at asegs m S (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  ((- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  (S + (Z.of_nat (length str) + 1 + Z.of_nat (length slack)) <= lo \/ bv_unsigned sp <= S)%Z -> (0 < S)%Z ->
  app_blk S (S + N) -> unpoisoned m S (S + N) -> (Z.of_nat (length str) <= 63)%Z ->
  (RLO <= S /\ S + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z ->
  wr_at asegs m (shad RLO) (shad RHI - shad RLO) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S (Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack))) -> rng RNG (shad RLO) (shad RHI - shad RLO) ->
  evtF asegs RNG (strlen_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4d564) fc None m (seg_rom asegs)).
Proof. intros. eapply strlen_i_body; eassumption. Qed.
End CANSEC3.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.StrFun.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ZBridge.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import RtCells.TwinB ShadowTac.TwinB F_rip.TwinB F_tryinit.TwinB I_printf_lib.TwinB.

  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_fwrite.TwinB.I_strnlen.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import F_strlen.TwinB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.

Notation rt_real_strlen m := (rw_cells bsegs m 0xd53d0 [C8 (Z_to_bv 64 0xc9c0c)]).

Section CANSEC3. Context {rc : runConstT}.
Definition strlen_i_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S : Z) (str slack : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length str))) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 2160, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp) /\ bytes_at bsegs m' S (str ++ Z_to_bv 8 0 :: slack).

Section STRLEN.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (str slack : list byte) (RLO RHI : Z).
  Notation S := (bv_unsigned a0).
  Notation L0 := (Z.of_nat (length str)).
  Notation N := (Z.of_nat (length str) + 1)%Z.
  Notation full := (str ++ Z_to_bv 8 0 :: slack).
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 2160)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis GOT : rt_got m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis INI : rt_inited m.
  Hypothesis LAY : rt_layout m.
  Hypothesis RSL : rt_real_strlen m.
  Hypothesis ISL : rt_isl m.
  Hypothesis BUF : bytes_at bsegs m S full.
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) str.
  Hypothesis PAD : ((- (S + L0 + 1)) mod 8 <= Z.of_nat (length slack))%Z.
  Hypothesis SEPB : (S + (L0 + 1 + Z.of_nat (length slack)) <= lo \/ bv_unsigned sp <= S)%Z.
  Hypothesis SPOS : (0 < S)%Z.
  Hypothesis APP : app_blk S (S + N).
  Hypothesis UNP : unpoisoned m S (S + N).
  Hypothesis NSZ : (L0 <= 63)%Z.
  Hypothesis R1 : (RLO <= S /\ S + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z.
  Hypothesis WR1 : wr_at bsegs m (shad RLO) (shad RHI - shad RLO).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RB : rng RNG S (Z.of_nat (length full)).
  Hypothesis RSH1 : rng RNG (shad RLO) (shad RHI - shad RLO).

  Notation POST := (strlen_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S str slack lo m).
  Notation SAVES := [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Definition SINV (mc : word -> option byte) : Prop :=
    rw_cells bsegs mc (bv_unsigned sp + -64) SAVES
    /\ stk bsegs mc lo (bv_unsigned sp + -2144) /\ stk bsegs mc (bv_unsigned sp + -2144) (bv_unsigned sp + -64)
    /\ munch [(bv_unsigned sp + -2160, bv_unsigned sp)]%Z m mc /\ wmono bsegs m mc /\ mem_inv bsegs mc
    /\ rt_got mc /\ rt_shbase mc /\ rt_layout mc
    /\ unpoisoned mc S (S + N) /\ wr_at bsegs mc (shad RLO) (shad RHI - shad RLO) /\ bytes_at bsegs mc S full.

  Definition SBND : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2160 /\ KHIGH <= lo /\ bv_unsigned sp < 2^64 /\ 1 <= N /\ N <= 64
     /\ 0 <= S /\ S + N + 8 <= KEND
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad S /\ shad (S + N - 1) + 1 <= shad RHI /\ shad RHI <= KHIGH
     /\ 0 <= Z.shiftr S 3 < 2^44 /\ -1 <= Z.shiftr (S + N + -1) 3 < 2^44
     /\ shad RLO mod 8 = 0 /\ shad RHI mod 8 = 0
     /\ RLO <= S /\ S + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0)%Z.
  Lemma full_len : Z.of_nat (length full) = (L0 + 1 + Z.of_nat (length slack))%Z.
  Proof. rewrite length_app. cbn [length]. lia. Qed.
  Lemma SBND_ok : SBND.
  Proof.
    unfold SBND. destruct ST as (LOW & _). destruct APP as [LES AS]. unfold KLOW, KHIGH, KEND in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF.
    Z.div_mod_to_equations. lia.
  Qed.
  Ltac acc_facts B ::= pose proof SBND_ok as B; unfold SBND, KHIGH, KEND in B.

  Definition SBL : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2160 /\ 17594333495296 <= lo /\ bv_unsigned sp < 2^64 /\ 1 <= N <= 64
     /\ 0 <= S /\ S + N + 8 <= 2^47
     /\ 0 <= Z.shiftr S 3 < 2^44 /\ -1 <= Z.shiftr (S + N + -1) 3 < 2^44
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad S /\ shad (S + N - 1) + 1 <= shad RHI /\ shad RHI <= 17594333495296)%Z.
  Lemma SBL_ok : SBL. Proof. pose proof SBND_ok as B. unfold SBND, KHIGH, KEND in B. unfold SBL. lia. Qed.

  Ltac sinv_open H := destruct H as (FR1 & ST1 & STM1 & MU1 & WM1 & MI1 & GOT1 & SHB1 & LAY1 & UNP1 & WR11 & BUF1).
  Ltac shide_all :=
    change (?P) with (sf_hide P) in R1; change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO;
    change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST; change (?P) with (sf_hide P) in SEPB;
    change (?P) with (sf_hide P) in GOT; change (?P) with (sf_hide P) in SHB; change (?P) with (sf_hide P) in INI;
    change (?P) with (sf_hide P) in LAY; change (?P) with (sf_hide P) in UNP; change (?P) with (sf_hide P) in WR1;
    change (?P) with (sf_hide P) in RSL; change (?P) with (sf_hide P) in ISL;
    change (?P) with (sf_hide P) in BUF; change (?P) with (sf_hide P) in NONUL; change (?P) with (sf_hide P) in PAD.
  Ltac sprep IV :=
    pose proof IV as IV0; sinv_open IV;
    pose proof SBL_ok as BL; unfold SBL in BL;
    assert (RSTK' : rng RNG (bv_unsigned sp + -2160) 2160) by (eapply rng_sub'; [exact RSTK| lia]);
    shide_all.

  Lemma sinv_of : forall mc,
    rw_cells bsegs mc (bv_unsigned sp + -64) SAVES ->
    stk bsegs mc lo (bv_unsigned sp + -2144) -> stk bsegs mc (bv_unsigned sp + -2144) (bv_unsigned sp + -64) ->
    munch [(bv_unsigned sp + -2160, bv_unsigned sp)]%Z m mc -> wmono bsegs m mc -> mem_inv bsegs mc ->
    rt_got mc -> rt_shbase mc -> rt_layout mc -> SINV mc.
  Proof.
    intros mc FR1 ST1 STM1 MU1 WM1 MI1 G1 G2 G3. pose proof SBND_ok as B. unfold SBND, KHIGH, KEND in B.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB. pose proof full_len as FLN.
    repeat (split; [assumption|]).
    assert (SS : (shad (S + N - 1) + 1 <= 17594333495296)%Z) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
    split. { eapply unpoisoned_munch; [exact UNP | exact MU1 |]. cbn [disjoint_from]. lia. }
    split. { eapply wr_at_transport; eassumption. }
    eapply bytes_at_transport; [exact BUF | exact MU1 |]. cbn [disjoint_from]. lia.
  Qed.

  Lemma SX : forall mc x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31, SINV mc ->
    evtF bsegs RNG POST (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 L0) x11 x12 x13 x14 x15 x16 x17
                                 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x4dfac) fc None mc (seg_rom bsegs)).
  Proof.
    intros until x31. intros IV. sprep IV.
    do 11 zstep.
    pose proof (stk_merge _ _ _ _ _ ST1 STM1 ltac:(lia)) as SK.
    pose proof (stk_release _ _ _ _ _ SK FR1 ltac:(lia)) as SK2. cbn [cells_size csize Nat.add] in SK2.
    replace (bv_unsigned sp + -64 + Z.of_nat 64)%Z with (bv_unsigned sp) in SK2 by lia.
    apply evtF_done. unfold strlen_i_post.
    replace (bv_unsigned sp - 2160)%Z with (bv_unsigned sp + -2160)%Z by lia.
    do 15 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; assumption.
  Qed.

  Definition sregs (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31 : word) :=
    mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17
        a0 (Z_to_bv 64 0x16d7a8) (Z_to_bv 64 (bv_unsigned sp + -2136)) x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31.

  Lemma SL : forall mc (k : nat) (c : Z) x1 x5 x6 x7 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31,
    SINV mc -> Z.to_nat (shad (S + N - 1) - c) = k -> (shad S <= c < shad (S + N - 1))%Z ->
    evtF bsegs RNG POST (MS (sregs x1 x5 x6 x7 (Z_to_bv 64 N) (Z_to_bv 64 0) (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (S + N + -1) 3)) x13 x14 x15 x16 x17
                                   (Z_to_bv 64 L0) x22 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x4e0a4) fc None mc (seg_rom bsegs)).
  Proof.
    intros until x31. intros IV Hk Hc. unfold sregs. sprep IV.
    revert c x13 Hk Hc. induction k as [|k IH]; intros c x13 Hk Hc; [exfalso; lia|].
    assert (SLE : (shad (S + N - 1) = 2147450880 + Z.shiftr (S + N + -1) 3)%Z) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
    pose proof (unpoisoned_full_rd bsegs mc S (S + N) c UNP1 ltac:(lia)
                  ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K1; zify_cond K1.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      zstep. zstep. eapply SX; eassumption.
  Qed.

  Lemma SE : forall mc x1 x5 x6 x7 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31, SINV mc ->
    evtF bsegs RNG POST (MS (sregs x1 x5 x6 x7 (Z_to_bv 64 N) (Z_to_bv 64 L0) (Z_to_bv 64 (2147450880 + Z.shiftr S 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (S + N + -1) 3))
                                   (Z_to_bv 64 (S + N + -1)) x14 x15 x16 x17 x21 x22 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x4e084) fc None mc (seg_rom bsegs)).
  Proof.
    intros until x31. intros IV. unfold sregs. sprep IV.
    destruct (unpoisoned_check_rd bsegs mc S (S + N) (S + N + -1) 1 UNP1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b2 & RD2 & CK2).
    unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
    zstep. zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((S + N + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      zstep. zstep. eapply SX; eassumption.
    - eapply (SL mc); [exact IV0 | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      Z.div_mod_to_equations; lia.
  Qed.

  Lemma SJ : forall mc x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x28 x29 x30 x31, SINV mc ->
    evtF bsegs RNG POST (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp (Z_to_bv 64 1) (Z_to_bv 64 L0) x11 x12 x13 x14 x15 x16 x17
                                 a0 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x4df44) fc None mc (seg_rom bsegs)).
  Proof.
    intros until x31. intros IV. sprep IV.
    assert (ISL1 : rw_cells bsegs mc 0x16d8a0 [CB 3 (repeat (Z_to_bv 8 1) 3); C1 (Z_to_bv 8 1); CB 4 (repeat (Z_to_bv 8 1) 4)]).
    { unfold sf_hide in ISL. pose proof ISL as ISL'.
      eapply rw_cells_transport in ISL'; [| exact MU1 | exact WM1 | cbn [disjoint_from cells_size csize Nat.add]; lia].
      recell ISL' 0%nat 1%nat [CB 3 (repeat (Z_to_bv 8 1) 3); C1 (Z_to_bv 8 1); CB 4 (repeat (Z_to_bv 8 1) 4)]. exact ISL'. }
    zstep. if_cases K0; zify_cond K0. { exfalso. clear -K0. cbv in K0. lia. } clear K0.
    zstep. zstep. zstep. cbv beta. rewrite unsigned_lit8 by lia. zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1. cbv in K1. lia. } clear K1.
    zstep. zstep. rewrite zb_lxor_ones by lia. zstep. zstep. zstep. if_cases K3; zify_cond K3. { exfalso. clear -K3 BL. lia. }
    zstep. zstep. if_cases K4; zify_cond K4. { exfalso. clear -K4 NSZ. lia. }
    do 4 zstep. replace (L0 + S)%Z with (S + N + -1)%Z by lia. do 6 zstep.
    change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
    unfold sf_hide in R1.
    destruct (shadow_probe8 bsegs mc RLO RHI S WR11 ltac:(apply no_image_asan; pose proof SBND_ok as B9; unfold SBND in B9; lia)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w1 P1].
    destruct (shadow_probe8 bsegs mc RLO RHI (S + N + -1) WR11 ltac:(apply no_image_asan; pose proof SBND_ok as B9; unfold SBND in B9; lia)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w2 P2].
    unfold ASHOFF in P1, P2.
    do 4 zstep. if_cases K5; zify_cond K5.
    + eapply SE; eassumption.
    + eapply SX; eassumption.
  Qed.

  Lemma strlen_i_body :
    evtF bsegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x4def4) fc None m (seg_rom bsegs)).
  Proof.
    pose proof (munch_refl [(bv_unsigned sp + -2160, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
    pose proof SBL_ok as BL0. unfold SBL in BL0.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    assert (RSTK' : rng RNG (bv_unsigned sp + -2160) 2160) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof MI as MIc. pose proof ST as ST0. pose proof GOT as GOTc. pose proof SHB as SHBc. pose proof INI as INIc.
    pose proof LAY as LAYc. pose proof RSL as RSLc.
    pose proof APP as APPc. pose proof WR1 as WR1c. pose proof R1 as R1c.
    assert (BUFc : bytes_at bsegs m S full) by exact BUF.
    assert (NONULc : ~ In (Z_to_bv 8 0) str) by exact NONUL.
    assert (PADc : ((- (S + L0 + 1)) mod 8 <= Z.of_nat (length slack))%Z) by exact PAD.
    assert (RBc : rng RNG S (Z.of_nat (length full))) by exact RB.
    shide_all.
    carve_frame 64%nat ST0.
    destruct (stk_split _ _ lo (bv_unsigned sp + -2144) _ ST0 ltac:(lia)) as [ST1 STM]. clear ST0.
    do 12 zstep.

    zstep. zstep. zstep. cbv beta. rewrite sxb_sval. change (sval (Z_to_bv 8 1)) with 1%Z. zstep. zstep. zstep. fold_lits. zstep.
    zstep. if_cases K0; zify_cond K0. { exfalso. clear -K0. cbv in K0. lia. } clear K0.
    zstep. call_sp tryinit_spec. all: iprem.
    do 4 zstep. zstep.

    call strlen_spec. all: iprem.
    eapply SJ. eapply sinv_of; eassumption.
  Qed.
End STRLEN.

Lemma strlen_i_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (str slack : list byte) (RLO RHI : Z),
  let S := bv_unsigned a0 in let N := (Z.of_nat (length str) + 1)%Z in
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2160)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_strlen m -> rt_isl m ->
  bytes_at bsegs m S (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  ((- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  (S + (Z.of_nat (length str) + 1 + Z.of_nat (length slack)) <= lo \/ bv_unsigned sp <= S)%Z -> (0 < S)%Z ->
  app_blk S (S + N) -> unpoisoned m S (S + N) -> (Z.of_nat (length str) <= 63)%Z ->
  (RLO <= S /\ S + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z ->
  wr_at bsegs m (shad RLO) (shad RHI - shad RLO) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S (Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack))) -> rng RNG (shad RLO) (shad RHI - shad RLO) ->
  evtF bsegs RNG (strlen_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4def4) fc None m (seg_rom bsegs)).
Proof. intros. eapply strlen_i_body; eassumption. Qed.
End CANSEC3.
End TwinB.
