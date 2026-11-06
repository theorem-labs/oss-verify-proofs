(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import StrFun.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg RtCells ShadowTac F_rip.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Section CANSEC1. Context {rc : runConstT}.
Definition imm_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'.

Lemma firstn1_skipn : forall (l : list byte) k d, (k < length l)%nat -> firstn 1 (skipn k l) = [nth k l d].
Proof. induction l as [|x l IH]; intros k d H; [cbn in H; lia|]. destruct k; cbn; [reflexivity|]. apply IH. cbn in H. lia. Qed.

Section IMM.
  Variables (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (src : list byte).
  Notation D := (bv_unsigned a0).
  Notation S := (bv_unsigned a1).
  Notation n := (bv_unsigned a2).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
  Hypothesis LEN : length src = Z.to_nat n.
  Hypothesis AB : (0 <= S /\ S + n <= 2^47 /\ 0 <= D /\ D + n <= 2^47 /\ n <= 2^40)%Z.
  Hypothesis RS : rng RNG S n.
  Hypothesis RD : rng RNG D n.
  Notation POST := (imm_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 m).
  Notation ST pc mm x11 x12 x13 x14 x15 x16 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 x11 x12 x13 x14 x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Lemma imm_fwd : forall (K : nat) mc (P : Z) x11 x13 x14 x15 x16,
    Z.to_nat (n - P) = K -> (0 <= P < n)%Z -> (D < S)%Z ->
    bytes_at bsegs mc (S + P) (skipn (Z.to_nat P) src) -> wr_at bsegs mc D n ->
    mem_inv bsegs mc -> munch W m mc -> wmono bsegs m mc ->
    x11 = Z_to_bv 64 (S + P) -> x13 = Z_to_bv 64 (D + P) ->
    evtF bsegs RNG POST (ST 0x78a90 mc x11 (Z_to_bv 64 (D + n)) x13 x14 x15 x16).
  Proof using LEN AB RS RD.
    induction K as [K IH] using lt_wf_ind; intros mc P x11 x13 x14 x15 x16 HK HP HDS SB DW MI MU WM -> ->.
    destruct (skipn (Z.to_nat P) src) as [|b rest] eqn:Es.
    { exfalso. assert (length (skipn (Z.to_nat P) src) = 0%nat) by (rewrite Es; reflexivity). rewrite length_skipn in H. lia. }
    assert (RB : ov_read_bytes bsegs mc (wa (S + P)) 1 = Some [b]).
    { pose proof (bytes_at_ov_read bsegs mc (S + P) (b :: rest) 0 1 SB ltac:(cbn; lia)) as R. rewrite Z.add_0_r in R. exact R. }
    assert (SB1 : bytes_at bsegs mc (S + P + 1) rest).
    { apply (bytes_at_app bsegs mc (S + P) [b] rest) in SB. destruct SB as [_ SB]. exact SB. }
    clear SB.
    assert (SOK : store_ok bsegs mc (wa (D + P)) 1 = true) by (apply (wr_at_store_ok bsegs mc D n P 1 DW); lia).
    zstep. zstep.
    store_done.
    zstep. zstep. zstep. if_cases KL; zify_cond KL.
    - (* [comment removed for export] *)
      replace (S + P + 1)%Z with (S + (P + 1))%Z by lia. replace (D + P + 1)%Z with (D + (P + 1))%Z by lia.
      eapply (IH (Z.to_nat (n - (P + 1))) ltac:(lia) _ (P + 1)%Z); try eassumption; try lia; try reflexivity.
      replace (Z.to_nat (P + 1)) with (1 + Z.to_nat P)%nat by lia. rewrite <- skipn_skipn, Es. cbn [skipn]. replace (S + (P + 1))%Z with (S + P + 1)%Z by lia. exact SB1.
    - (* [comment removed for export] *)
      zstep. zstep. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma imm_bwd : forall (J : nat) mc (K : Z) x14 x15 x16,
    Z.to_nat K = J -> (0 <= K < n)%Z -> (S < D)%Z ->
    bytes_at bsegs mc S (firstn (Z.to_nat K + 1) src) -> wr_at bsegs mc D n ->
    mem_inv bsegs mc -> munch W m mc -> wmono bsegs m mc ->
    evtF bsegs RNG POST (ST 0x78ab8 mc a1 (Z_to_bv 64 1) (Z_to_bv 64 K) x14 x15 x16).
  Proof using LEN AB RS RD.
    induction J as [J IH] using lt_wf_ind; intros mc K x14 x15 x16 HJ HK HSD SB DW MI MU WM.
    assert (EF : firstn (Z.to_nat K + 1) src = firstn (Z.to_nat K) src ++ [nth (Z.to_nat K) src (Z_to_bv 8 0)]).
    { rewrite <- (firstn_skipn (Z.to_nat K) src) at 1. rewrite firstn_app. rewrite firstn_firstn.
      rewrite length_firstn. replace (Nat.min (Z.to_nat K + 1) (Z.to_nat K)) with (Z.to_nat K) by lia.
      replace (Z.to_nat K + 1 - Nat.min (Z.to_nat K) (length src))%nat with 1%nat by lia. f_equal.
      apply firstn1_skipn. lia. }
    rewrite EF in SB. apply (bytes_at_app bsegs mc S) in SB. destruct SB as [SB0 SB1].
    rewrite length_firstn in SB1. replace (Nat.min (Z.to_nat K) (length src)) with (Z.to_nat K) in SB1 by lia.
    rewrite Z2Nat.id in SB1 by lia.
    assert (RB : ov_read_bytes bsegs mc (wa (S + K)) 1 = Some [nth (Z.to_nat K) src (Z_to_bv 8 0)]).
    { pose proof (bytes_at_ov_read bsegs mc (S + K) _ 0 1 SB1 ltac:(cbn; lia)) as R. rewrite Z.add_0_r in R. exact R. }
    clear SB1.
    assert (SOK : store_ok bsegs mc (wa (D + K)) 1 = true) by (apply (wr_at_store_ok bsegs mc D n K 1 DW); lia).
    assert (LF : length (firstn (Z.to_nat K) src) = Z.to_nat K) by (rewrite length_firstn; lia).
    remember (firstn (Z.to_nat K) src) as pre eqn:Hpre.
    zstep. zstep. zstep. zstep. zstep. zstep.
    store_done.
    zstep. if_cases KL; zify_cond KL.
    - replace (K + -1)%Z with (K - 1)%Z by lia.
      eapply (IH (Z.to_nat (K - 1)) ltac:(lia) _ (K - 1)%Z); try eassumption; try lia.
      replace (Z.to_nat (K - 1) + 1)%nat with (Z.to_nat K) by lia. rewrite <- Hpre. eassumption.
    - zstep. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma imm_body : forall x13 x14 x15 x16,
    bytes_at bsegs m S src -> wr_at bsegs m D n -> mem_inv bsegs m ->
    evtF bsegs RNG POST (ST 0x78a80 m a1 a2 x13 x14 x15 x16).
  Proof using LEN AB RS RD.
    intros x13 x14 x15 x16 SB DW MI.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl bsegs m) as WM.
    zstep. if_cases K0; zify_cond K0.
    - zstep. if_cases K1; zify_cond K1.
      + zstep. finish.
      + zstep. if_cases K2; zify_cond K2.
        * zstep. finish.
        * zstep. zstep. replace (n + -1)%Z with (n - 1)%Z by lia.
          eapply (imm_bwd (Z.to_nat (n - 1)) m (n - 1)%Z); try eassumption; try lia.
          replace (Z.to_nat (n - 1) + 1)%nat with (length src) by lia. rewrite firstn_all. exact SB.
    - zstep. if_cases K2; zify_cond K2.
      + zstep. finish.
      + zstep. zstep.
        eapply (imm_fwd (Z.to_nat (n - 0)) m 0%Z); try eassumption; try lia; try (rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned).
        cbn [skipn]. rewrite Z.add_0_r. exact SB.
  Qed.
End IMM.

Lemma imm_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (src : list byte),
  bytes_at bsegs m (bv_unsigned a1) src -> length src = Z.to_nat (bv_unsigned a2) ->
  wr_at bsegs m (bv_unsigned a0) (bv_unsigned a2) -> mem_inv bsegs m ->
  (bv_unsigned a1 + bv_unsigned a2 <= 2^47 /\ bv_unsigned a0 + bv_unsigned a2 <= 2^47 /\ bv_unsigned a2 <= 2^40)%Z ->
  rng RNG (bv_unsigned a1) (bv_unsigned a2) -> rng RNG (bv_unsigned a0) (bv_unsigned a2) ->
  evtF bsegs RNG (imm_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x78a80) fc None m (seg_rom bsegs)).
Proof.
  intros until src. intros SB LEN DW MI AB RS RD.
  eapply imm_body; try eassumption.
  pose proof (bv_unsigned_in_range 64 a0). pose proof (bv_unsigned_in_range 64 a1). pose proof (bv_unsigned_in_range 64 a2).
  unfold bv_modulus in *. cbn in *. lia.
Qed.
End CANSEC1.


(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Definition asan_memmove_entry := 0x65f28%Z.

Definition asan_memmove_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 2224, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp).

Section Proofs.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
            (src : list byte) (RLO1 RHI1 RLO2 RHI2 : Z).
  Notation D := (bv_unsigned a0).
  Notation S := (bv_unsigned a1).
  Notation n := (bv_unsigned a2).
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 2224)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis GOT : rt_got m.
  Hypothesis RIC : rt_got_ric m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis INI : rt_inited m.
  Hypothesis LAY : rt_layout m.
  Hypothesis SRC : bytes_at bsegs m S src.
  Hypothesis SRCL : length src = Z.to_nat n.
  Hypothesis DW : wr_at bsegs m D n.
  Hypothesis SEPS : (S + n <= lo \/ bv_unsigned sp <= S)%Z.
  Hypothesis SEPD : (D + n <= lo \/ bv_unsigned sp <= D)%Z.
  Hypothesis APPS : app_blk S (S + n).
  Hypothesis APPD : app_blk D (D + n).
  Hypothesis USRC : unpoisoned m S (S + n).
  Hypothesis UDST : unpoisoned m D (D + n).
  Hypothesis NSZ : (n <= 2^40)%Z.
  Hypothesis R1 : (RLO1 <= S /\ S + n <= RHI1 /\ RLO1 mod 64 = 0 /\ RHI1 mod 64 = 0 /\ 0 <= RLO1 /\ RHI1 <= KEND)%Z.
  Hypothesis R2 : (RLO2 <= D /\ D + n <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND)%Z.
  Hypothesis WR1 : wr_at bsegs m (shad RLO1) (shad RHI1 - shad RLO1).
  Hypothesis WR2 : wr_at bsegs m (shad RLO2) (shad RHI2 - shad RLO2).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RS : rng RNG S n.
  Hypothesis RD : rng RNG D n.
  Hypothesis RSH1 : rng RNG (shad RLO1) (shad RHI1 - shad RLO1).
  Hypothesis RSH2 : rng RNG (shad RLO2) (shad RHI2 - shad RLO2).

  Notation POST := (asan_memmove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 lo m).

  Definition INV (mc : word -> option byte) : Prop :=
    rw_cells bsegs mc (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk bsegs mc lo (bv_unsigned sp + -2144)
    /\ stk bsegs mc (bv_unsigned sp + -2144) (bv_unsigned sp + -64)
    /\ munch [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m mc
    /\ wmono bsegs m mc /\ mem_inv bsegs mc
    /\ rt_got mc /\ rt_got_ric mc /\ rt_shbase mc /\ rt_inited mc /\ rt_layout mc
    /\ unpoisoned mc S (S + n) /\ unpoisoned mc D (D + n)
    /\ wr_at bsegs mc (shad RLO1) (shad RHI1 - shad RLO1) /\ wr_at bsegs mc (shad RLO2) (shad RHI2 - shad RLO2)
    /\ bytes_at bsegs mc S src /\ wr_at bsegs mc D n.

  Definition BND : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2224 /\ KHIGH <= lo /\ 0 <= n < 2^64 /\ n <= 2^40
     /\ 0 <= D /\ D + n + 8 <= KEND /\ 0 <= S /\ S + n + 8 <= KEND
     /\ 2147450880 <= shad RLO2 /\ shad RLO2 <= shad D /\ shad (D + n - 1) + 1 <= shad RHI2 /\ shad RHI2 <= KHIGH
     /\ 2147450880 <= shad RLO1 /\ shad RLO1 <= shad S /\ shad (S + n - 1) + 1 <= shad RHI1 /\ shad RHI1 <= KHIGH
     /\ 0 <= Z.shiftr D 3 < 2^44 /\ -1 <= Z.shiftr (D + n + -1) 3 < 2^44
     /\ 0 <= Z.shiftr S 3 < 2^44 /\ -1 <= Z.shiftr (S + n + -1) 3 < 2^44
     /\ shad RLO2 mod 8 = 0 /\ shad RHI2 mod 8 = 0 /\ shad RLO1 mod 8 = 0 /\ shad RHI1 mod 8 = 0
     /\ RLO2 <= D /\ D + n <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0
     /\ RLO1 <= S /\ S + n <= RHI1 /\ RLO1 mod 64 = 0 /\ RHI1 mod 64 = 0)%Z.

  Lemma BND_ok : BND.
  Proof.
    unfold BND. pose proof (bv_unsigned_in_range 64 a2) as Rn. unfold bv_modulus in Rn.
    destruct ST as (L0 & _). destruct APPD as [LED AD]. destruct APPS as [LES AS]. unfold KLOW, KHIGH, KEND in *.
    pose proof R2 as R2'. pose proof R1 as R1'.
    rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rn.
    first [clear -Rn L0 LO KLO NSZ LED AD LES AS R2' R1'; Z.div_mod_to_equations; nia | Z.div_mod_to_equations; nia].
  Qed.

  Ltac acc_facts B ::= pose proof BND_ok as B; unfold BND, KHIGH, KEND in B.

  Definition BL : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2224 /\ 17594333495296 <= lo /\ 0 <= n < 2^64 /\ 0 <= D /\ D + n + 8 <= 2^47
     /\ 0 <= S /\ S + n + 8 <= 2^47
     /\ 0 <= Z.shiftr D 3 < 2^44 /\ -1 <= Z.shiftr (D + n + -1) 3 < 2^44
     /\ 0 <= Z.shiftr S 3 < 2^44 /\ -1 <= Z.shiftr (S + n + -1) 3 < 2^44
     /\ 2147450880 <= shad RLO2 /\ shad RLO2 <= shad D /\ shad (D + n - 1) + 1 <= shad RHI2 /\ shad RHI2 <= 17594333495296
     /\ 2147450880 <= shad RLO1 /\ shad RLO1 <= shad S /\ shad (S + n - 1) + 1 <= shad RHI1 /\ shad RHI1 <= 17594333495296)%Z.
  Lemma BL_ok : BL. Proof. pose proof BND_ok as B. unfold BND, KHIGH, KEND in B. unfold BL. lia. Qed.

  Ltac inv_open H :=
    destruct H as (FR & ST1 & STP & MU1 & WM1 & MI1 & GOT1 & RIC1 & SHB1 & INI1 & LAY1 & US1 & UD1 & WR11 & WR21 & SRC1 & DW1).

  Ltac prep IV :=
    pose proof IV as IV0; inv_open IV;
    let B := fresh "BL" in pose proof BL_ok as B; unfold BL in B;
    assert (RSTK' : rng RNG (bv_unsigned sp + -2224) 2224) by (eapply rng_sub'; [exact RSTK| lia]);
    change (?P) with (sf_hide P) in SEPD; change (?P) with (sf_hide P) in SEPS; change (?P) with (sf_hide P) in R2;
    change (?P) with (sf_hide P) in R1;
    change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO; change (?P) with (sf_hide P) in NSZ.

  Lemma inv_of : forall mc,
    rw_cells bsegs mc (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk bsegs mc lo (bv_unsigned sp + -2144) ->
    stk bsegs mc (bv_unsigned sp + -2144) (bv_unsigned sp + -64) ->
    munch [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m mc -> wmono bsegs m mc -> mem_inv bsegs mc ->
    rt_got mc -> rt_got_ric mc -> rt_shbase mc -> rt_inited mc -> rt_layout mc ->
    INV mc.
  Proof.
    intros mc FR ST1 STP MU1 WM1 MI1 G1 G2 G3 G4 G5. pose proof BND_ok as B. unfold BND, KHIGH, KEND in B.
    split; [exact FR|]. repeat (split; [assumption|]).
    assert (SS : forall lo' hi', (0 <= lo' -> hi' + 8 <= 2^47 -> shad (hi' - 1) + 1 <= 17594333495296)%Z).
    { intros lo' hi' H1 H2. rewrite shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia. }
    split. { eapply unpoisoned_munch; [exact USRC | exact MU1 |]. cbn [disjoint_from]. pose proof (SS S (S + n)%Z). lia. }
    split. { eapply unpoisoned_munch; [exact UDST | exact MU1 |]. cbn [disjoint_from]. pose proof (SS D (D + n)%Z). lia. }
    split; [eapply wr_at_transport; eassumption|].
    split; [eapply wr_at_transport; eassumption|].
    split.
    { eapply bytes_at_transport; [exact SRC | exact MU1 |]. cbn [disjoint_from]. rewrite SRCL. rewrite Z2Nat.id by lia.
      destruct SEPS; lia. }
    eapply wr_at_transport; eassumption.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma LX : forall mc x1 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    INV mc ->
    evtF bsegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 x8 x9 a0 a1 a2 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x66008) fc None mc (seg_rom bsegs)).
  Proof.
    intros until x31. intros IV. prep IV.
    zstep.
    unfold sf_hide in SEPD, SEPS.
    apply (munch_weaken _ [(bv_unsigned sp + -2224, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z) in MU1.
    2:{ unfold sub_fp; cbn [outside]; intros; lia. }
    clear GOT1 RIC1 SHB1 INI1 LAY1 WR11 WR21 US1 UD1.
    call imm_spec.
    all: first [exact SRC1 | exact SRCL | exact DW1 | exact MI1 | (unfold sf_hide in NSZ; lia) | idtac].
    do 11 zstep.
    pose proof (stk_merge bsegs _ _ _ _ ST1 STP ltac:(lia)) as ST1'. clear ST1 STP.
    release_frame FR ST1' (bv_unsigned sp). finish.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma LWLd : forall mc (k : nat) (c : Z) x1 x5 x6 x7 x8 x9 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    INV mc -> (1 <= n <= 64)%Z ->
    Z.to_nat (shad (D + n - 1) - c) = k -> (shad D <= c < shad (D + n - 1))%Z ->
    evtF bsegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 x8 x9 a0 a1 a2
               (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (D + n + -1) 3)) (Z_to_bv 64 0) x16 x17
               x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x66214) fc None mc (seg_rom bsegs)).
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
  Lemma LWSd : forall mc x1 x5 x6 x7 x8 x9 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    INV mc -> (1 <= n <= 64)%Z ->
    evtF bsegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 x8 x9 a0 a1 a2
               (Z_to_bv 64 (2147450880 + Z.shiftr D 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (D + n + -1) 3))
               (Z_to_bv 64 (D + n + -1)) x16 x17
               x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x661f8) fc None mc (seg_rom bsegs)).
  Proof.
    intros until x31. intros IV N1. prep IV.
    destruct (unpoisoned_check_rd bsegs mc D (D + n) (D + n + -1) 1 UD1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b2 & RD2 & CK2).
    unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
    zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((D + n + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LX; eassumption.
    - eapply LWLd; [exact IV0 | assumption | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma LBd : forall mc x1 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x20 x21 x22 x28 x29 x30 x31,
    INV mc ->
    evtF bsegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 x8 x9 a0 a1 a2 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 (n + -65)) x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x65fbc) fc None mc (seg_rom bsegs)).
  Proof.
    intros until x31. intros IV. prep IV.
    zstep. rewrite zb_lxor_ones by lia. zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
    zstep. zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      zstep. if_cases K3; zify_cond K3.
      2:{ zstep. eapply LX; exact IV0. }
      do 5 zstep.
      call_sp rip_spec.
      all: first [ exact MI1 | exact ST1 | exact GOT1 | exact SHB1 | exact LAY1 | exact APPD | exact UD1
                 | (eapply rng_sub'; [exact RSTK | lia]) | (unfold sf_hide in *; unfold KHIGH; lia)
                 | (pose proof BND_ok as B; unfold BND in B; unfold sf_hide in *; lia) | idtac ].
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
      + eapply LWSd; eassumption.
      + eapply LX; exact IV0.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma LWLs : forall mc (k : nat) (c : Z) x1 x5 x6 x7 x8 x9 x16 x17 x18 x20 x21 x22 x28 x29 x30 x31,
    INV mc -> (1 <= n <= 64)%Z ->
    Z.to_nat (shad (S + n - 1) - c) = k -> (shad S <= c < shad (S + n - 1))%Z ->
    evtF bsegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 x8 x9 a0 a1 a2
               (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (S + n + -1) 3)) (Z_to_bv 64 0) x16 x17
               x18 (Z_to_bv 64 (n + -65)) x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x66170) fc None mc (seg_rom bsegs)).
  Proof.
    intros until x31. intros IV N1 Hk Hc. prep IV.
    revert c x16 Hk Hc. induction k as [|k IH]; intros c x16 Hk Hc; [exfalso; lia|].
    assert (SL : (shad (S + n - 1) = 2147450880 + Z.shiftr (S + n + -1) 3)%Z) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
    pose proof (unpoisoned_full_rd bsegs mc S (S + n) c US1 ltac:(lia)
                  ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K; zify_cond K.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply LBd; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma LWSs : forall mc x1 x5 x6 x7 x8 x9 x16 x17 x18 x20 x21 x22 x28 x29 x30 x31,
    INV mc -> (1 <= n <= 64)%Z ->
    evtF bsegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 x8 x9 a0 a1 a2
               (Z_to_bv 64 (2147450880 + Z.shiftr S 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (S + n + -1) 3))
               (Z_to_bv 64 (S + n + -1)) x16 x17
               x18 (Z_to_bv 64 (n + -65)) x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x66154) fc None mc (seg_rom bsegs)).
  Proof.
    intros until x31. intros IV N1. prep IV.
    destruct (unpoisoned_check_rd bsegs mc S (S + n) (S + n + -1) 1 US1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b2 & RD2 & CK2).
    unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
    zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((S + n + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LBd; eassumption.
    - eapply LWLs; [exact IV0 | assumption | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma LBs : forall mc x1 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    INV mc ->
    evtF bsegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 x8 x9 a0 a1 a2 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x65f64) fc None mc (seg_rom bsegs)).
  Proof.
    intros until x31. intros IV. prep IV.
    zstep. rewrite zb_lxor_ones by lia. zstep. zstep. zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      zstep. if_cases K3; zify_cond K3.
      2:{ zstep. eapply LBd; exact IV0. }
      do 6 zstep.
      call_sp rip_spec.
      all: first [ exact MI1 | exact ST1 | exact GOT1 | exact SHB1 | exact LAY1 | exact APPS | exact US1
                 | (eapply rng_sub'; [exact RSTK | lia]) | (unfold sf_hide in *; unfold KHIGH; lia)
                 | (pose proof BND_ok as B; unfold BND in B; unfold sf_hide in *; lia) | idtac ].
      do 5 zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
      eapply LBd; eapply inv_of; eassumption.
    - (* [comment removed for export] *)
      assert (N1 : (1 <= n <= 64)%Z) by (clear - K2 BL0; Z.div_mod_to_equations; lia).
      do 11 zstep.
      change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
      unfold sf_hide in R1.
      destruct (shadow_probe8 bsegs mc RLO1 RHI1 S WR11 ltac:(apply no_image_asan; pose proof BND_ok as B; unfold BND in B; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w1 P1].
      destruct (shadow_probe8 bsegs mc RLO1 RHI1 (S + n + -1) WR11 ltac:(apply no_image_asan; pose proof BND_ok as B; unfold BND in B; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w2 P2].
      unfold ASHOFF in P1, P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply LWSs; eassumption.
      + eapply LBd; exact IV0.
  Qed.


  Lemma asan_memmove_body :
    evtF bsegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x65f28) fc None m (seg_rom bsegs)).
  Proof.
    pose proof (munch_refl [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
    pose proof BL_ok as BL0. unfold BL in BL0.
    assert (RSTK' : rng RNG (bv_unsigned sp + -2224) 2224) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (LO' : (lo <= bv_unsigned sp - 2144)%Z) by lia.
    change (?P) with (sf_hide P) in R2; change (?P) with (sf_hide P) in R1;
    change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO; change (?P) with (sf_hide P) in NSZ.
    change (?P) with (sf_hide P) in SRC. change (?P) with (sf_hide P) in DW.
    pose proof ST as ST0. change (?P) with (sf_hide P) in ST. change (?P) with (sf_hide P) in WR2. change (?P) with (sf_hide P) in WR1.
    carve_frame 64%nat ST0.
    destruct (stk_split bsegs _ lo (bv_unsigned sp + -2144) (bv_unsigned sp + -64) ST0 ltac:(lia)) as [ST0' STP]. clear ST0. rename ST0' into ST0.
    do 11 zstep.
    do 3 zstep. cbv beta. zsimp. zstep. if_cases K0; zify_cond K0. { exfalso. clear - K0. cbv in K0. lia. }
    eapply LBs. eapply inv_of; eassumption.
  Qed.
End Proofs.

Lemma asan_memmove_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (src : list byte) (RLO1 RHI1 RLO2 RHI2 : Z),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2224)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m ->
  bytes_at bsegs m (bv_unsigned a1) src -> length src = Z.to_nat (bv_unsigned a2) ->
  wr_at bsegs m (bv_unsigned a0) (bv_unsigned a2) ->
  (bv_unsigned a1 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
  (bv_unsigned a0 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  app_blk (bv_unsigned a1) (bv_unsigned a1 + bv_unsigned a2) ->
  app_blk (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
  unpoisoned m (bv_unsigned a1) (bv_unsigned a1 + bv_unsigned a2) ->
  unpoisoned m (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
  (bv_unsigned a2 <= 2^40)%Z ->
  (RLO1 <= bv_unsigned a1 /\ bv_unsigned a1 + bv_unsigned a2 <= RHI1 /\ RLO1 mod 64 = 0 /\ RHI1 mod 64 = 0 /\ 0 <= RLO1 /\ RHI1 <= KEND)%Z ->
  (RLO2 <= bv_unsigned a0 /\ bv_unsigned a0 + bv_unsigned a2 <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND)%Z ->
  wr_at bsegs m (shad RLO1) (shad RHI1 - shad RLO1) -> wr_at bsegs m (shad RLO2) (shad RHI2 - shad RLO2) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (bv_unsigned a1) (bv_unsigned a2) -> rng RNG (bv_unsigned a0) (bv_unsigned a2) ->
  rng RNG (shad RLO1) (shad RHI1 - shad RLO1) -> rng RNG (shad RLO2) (shad RHI2 - shad RLO2) ->
  evtF bsegs RNG (asan_memmove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x65f28) fc None m (seg_rom bsegs)).
Proof. intros. eapply asan_memmove_body; eassumption. Qed.
End CANSEC2.
Print Assumptions asan_memmove_spec.
