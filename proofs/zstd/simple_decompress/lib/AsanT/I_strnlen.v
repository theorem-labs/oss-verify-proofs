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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ShadowTac F_rip F_tryinit F_memchr I_printf_lib.
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
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.

Ltac iprem :=
  lazymatch goal with
  | |- evtF _ _ _ _ => idtac
  | |- mem_inv _ _ => first [assumption | eassumption]
  | |- context [bv_unsigned (Z_to_bv 64 _)] => rewrite !unsigned_lit by lia; iprem
  | |- stk _ _ _ _ => first [assumption | eassumption]
  | |- rw_cells _ _ _ _ => rewrite ?Z_to_bv_bv_unsigned; first [assumption | eassumption]
  | |- shadow_bytes _ _ _ _ => first [assumption | eassumption]
  | |- bytes_at _ _ _ _ => first [assumption | eassumption]
  | |- unpoisoned _ _ _ => first [assumption | eassumption]
  | |- memchr_ok _ _ _ _ => first [assumption | eassumption]
  | |- wr_at _ _ _ _ => first [assumption | eassumption]
  | |- app_blk _ _ => first [assumption | eassumption]
  | |- Forall _ _ => first [assumption | eassumption]
  | |- _ = Z_to_bv 64 _ => first [reflexivity | assumption | symmetry; assumption]
  | |- rng _ _ _ => first [ assumption | match goal with H : rng _ _ _ |- _ => eapply rng_sub'; [exact H | unfold KHIGH, sf_hide in *; lia] end ]
  | |- _ => unfold KHIGH, sf_hide in *; first [assumption | lia]
  end.
Ltac unland K :=
  change 18446744073709551615%Z with (Z.ones 64) in K; rewrite ?Z.land_ones in K by lia;
  change (2 ^ 64)%Z with 18446744073709551616%Z in K.

Notation rt_real_memchr m := (rw_cells bsegs m 0xc9078 [C8 (Z_to_bv 64 0xc053c)]).
Notation rt_real_strnlen m := (rw_cells bsegs m 0xc9160 [C8 (Z_to_bv 64 0xc0ec4)]).

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition hitlen (c n : Z) (buf : list byte) : Z :=
  match find_byte c (firstn (Z.to_nat n) buf) with Some j => Z.of_nat j + 1 | None => n end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition memchr_i_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S cc n : Z) (buf : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (memchr_res S cc n buf)) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 2208, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp) /\ bytes_at bsegs m' S buf.

Section MEMCHR.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (buf : list byte) (RLO RHI : Z).
  Notation S := (bv_unsigned a0).
  Notation cc := (bv_unsigned a1 mod 256)%Z.
  Notation n := (bv_unsigned a2).
  Notation N := (hitlen cc n buf).
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 2208)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis GOT : rt_got m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis INI : rt_inited m.
  Hypothesis LAY : rt_layout m.
  Hypothesis RMC : rt_real_memchr m.
  Hypothesis BUF : bytes_at bsegs m S buf.
  Hypothesis OK : memchr_ok S cc n buf.
  Hypothesis SEPB : (S + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= S)%Z.
  Hypothesis SPOS : (0 < S)%Z.
  Hypothesis APP : app_blk S (S + N).
  Hypothesis UNP : unpoisoned m S (S + N).
  Hypothesis NSZ : (N <= 2^40)%Z.
  Hypothesis R1 : (RLO <= S /\ S + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z.
  Hypothesis WR1 : wr_at bsegs m (shad RLO) (shad RHI - shad RLO).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RB : rng RNG S (Z.of_nat (length buf)).
  Hypothesis RSH1 : rng RNG (shad RLO) (shad RHI - shad RLO).

  Notation POST := (memchr_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S cc n buf lo m).
  Notation RES := (memchr_res S cc n buf).

  Definition INV (mc : word -> option byte) : Prop :=
    rw_cells bsegs mc (bv_unsigned sp + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk bsegs mc lo (bv_unsigned sp + -2128) /\ stk bsegs mc (bv_unsigned sp + -2128) (bv_unsigned sp + -56)
    /\ munch [(bv_unsigned sp + -2208, bv_unsigned sp)]%Z m mc /\ wmono bsegs m mc /\ mem_inv bsegs mc
    /\ rt_got mc /\ rt_shbase mc /\ rt_layout mc
    /\ unpoisoned mc S (S + N) /\ wr_at bsegs mc (shad RLO) (shad RHI - shad RLO) /\ bytes_at bsegs mc S buf.

  Definition BND : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2208 /\ KHIGH <= lo /\ bv_unsigned sp < 2^64 /\ 0 <= N /\ N <= 2^40 /\ 0 <= n < 2^64
     /\ 0 <= S /\ S + N + 8 <= KEND
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad S /\ shad (S + N - 1) + 1 <= shad RHI /\ shad RHI <= KHIGH
     /\ 0 <= Z.shiftr S 3 < 2^44 /\ -1 <= Z.shiftr (S + N + -1) 3 < 2^44
     /\ shad RLO mod 8 = 0 /\ shad RHI mod 8 = 0
     /\ RLO <= S /\ S + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0)%Z.
  Lemma hitlen_range : (0 <= N <= n)%Z.
  Proof.
    unfold hitlen. pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R.
    destruct (find_byte cc (firstn (Z.to_nat n) buf)) as [j|] eqn:E; [|lia].
    apply find_byte_Some in E. destruct E as [E _]. rewrite firstn_length in E. lia.
  Qed.
  Lemma BND_ok : BND.
  Proof.
    unfold BND. destruct ST as (L0 & _). destruct APP as [LES AS]. unfold KLOW, KHIGH, KEND in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    pose proof (bv_unsigned_in_range 64 a2) as NR. unfold bv_modulus in NR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in NR.
    pose proof hitlen_range as HR.
    rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF.
    Z.div_mod_to_equations. lia.
  Qed.
  Ltac acc_facts B ::= pose proof BND_ok as B; unfold BND, KHIGH, KEND in B.

  Definition BL : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2208 /\ 17594333495296 <= lo /\ bv_unsigned sp < 2^64 /\ 0 <= N <= n /\ N <= 2^40 /\ n < 2^64
     /\ 0 <= S /\ S + N + 8 <= 2^47
     /\ 0 <= Z.shiftr S 3 < 2^44 /\ -1 <= Z.shiftr (S + N + -1) 3 < 2^44
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad S /\ shad (S + N - 1) + 1 <= shad RHI /\ shad RHI <= 17594333495296)%Z.
  Lemma BL_ok : BL. Proof. pose proof BND_ok as B. unfold BND, KHIGH, KEND in B. pose proof hitlen_range. unfold BL. lia. Qed.

  Ltac inv_open H := destruct H as (FR1 & ST1 & STM1 & MU1 & WM1 & MI1 & GOT1 & SHB1 & LAY1 & UNP1 & WR11 & BUF1).
  Ltac hide_all :=
    change (?P) with (sf_hide P) in R1; change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO;
    change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST; change (?P) with (sf_hide P) in SEPB;
    change (?P) with (sf_hide P) in GOT; change (?P) with (sf_hide P) in SHB; change (?P) with (sf_hide P) in INI;
    change (?P) with (sf_hide P) in LAY; change (?P) with (sf_hide P) in UNP; change (?P) with (sf_hide P) in WR1;
    change (?P) with (sf_hide P) in RMC; change (?P) with (sf_hide P) in BUF; change (?P) with (sf_hide P) in OK.
  Ltac prep IV :=
    pose proof IV as IV0; inv_open IV;
    let B := fresh "BL" in pose proof BL_ok as B; unfold BL in B;
    assert (RSTK' : rng RNG (bv_unsigned sp + -2208) 2208) by (eapply rng_sub'; [exact RSTK| lia]);
    hide_all.

  Lemma inv_of : forall mc,
    rw_cells bsegs mc (bv_unsigned sp + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk bsegs mc lo (bv_unsigned sp + -2128) -> stk bsegs mc (bv_unsigned sp + -2128) (bv_unsigned sp + -56) ->
    munch [(bv_unsigned sp + -2208, bv_unsigned sp)]%Z m mc -> wmono bsegs m mc -> mem_inv bsegs mc ->
    rt_got mc -> rt_shbase mc -> rt_layout mc -> INV mc.
  Proof.
    intros mc FR1 ST1 STM1 MU1 WM1 MI1 G1 G2 G3. pose proof BND_ok as B. unfold BND, KHIGH, KEND in B.
    repeat (split; [assumption|]).
    assert (SS : (shad (S + N - 1) + 1 <= 17594333495296)%Z) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
    split. { eapply unpoisoned_munch; [exact UNP | exact MU1 |]. cbn [disjoint_from]. lia. }
    split. { eapply wr_at_transport; eassumption. }
    eapply bytes_at_transport; [exact BUF | exact MU1 |]. cbn [disjoint_from]. lia.
  Qed.

  (* [comment removed for export] *)
  Definition mregs (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x28 x29 x30 x31 : word) :=
    mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17
        a0 a1 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31.

  (* [comment removed for export] *)
  Lemma LX : forall mc x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31, INV mc ->
    evtF bsegs RNG POST (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp x9 (Z_to_bv 64 RES) x11 x12 x13 x14 x15 x16 x17
                                 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x459d0) fc None mc (seg_rom bsegs)).
  Proof.
    intros until x31. intros IV. prep IV.
    do 10 zstep.
    pose proof (stk_merge _ _ _ _ _ ST1 STM1 ltac:(lia)) as SK.
    pose proof (stk_release _ _ _ _ _ SK FR1 ltac:(lia)) as SK2. cbn [cells_size csize Nat.add] in SK2.
    replace (bv_unsigned sp + -56 + Z.of_nat 56)%Z with (bv_unsigned sp) in SK2 by lia.
    apply evtF_done. unfold memchr_i_post.
    replace (bv_unsigned sp - 2208)%Z with (bv_unsigned sp + -2208)%Z by lia.
    do 15 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma LL : forall mc (k : nat) (c : Z) x1 x5 x6 x7 x14 x15 x16 x17 x21 x28 x29 x30 x31,
    INV mc -> (1 <= N <= 64)%Z -> Z.to_nat (shad (S + N - 1) - c) = k -> (shad S <= c < shad (S + N - 1))%Z ->
    evtF bsegs RNG POST (MS (mregs x1 x5 x6 x7 (Z_to_bv 64 N) (Z_to_bv 64 RES) (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (S + N + -1) 3)) (Z_to_bv 64 0) x14 x15 x16 x17
                                   (Z_to_bv 64 (bv_unsigned sp + -2128)) x21 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x45ae0) fc None mc (seg_rom bsegs)).
  Proof.
    intros until x31. intros IV N1 Hk Hc. unfold mregs. prep IV.
    revert c x14 Hk Hc. induction k as [|k IH]; intros c x14 Hk Hc; [exfalso; lia|].
    assert (SL : (shad (S + N - 1) = 2147450880 + Z.shiftr (S + N + -1) 3)%Z) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
    pose proof (unpoisoned_full_rd bsegs mc S (S + N) c UNP1 ltac:(lia)
                  ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K1; zify_cond K1.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply LX; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma LE : forall mc x1 x5 x6 x7 x14 x15 x16 x17 x21 x28 x29 x30 x31, INV mc -> (1 <= N <= 64)%Z ->
    evtF bsegs RNG POST (MS (mregs x1 x5 x6 x7 (Z_to_bv 64 N) (Z_to_bv 64 RES) (Z_to_bv 64 (2147450880 + Z.shiftr S 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (S + N + -1) 3))
                                   (Z_to_bv 64 (S + N + -1)) x14 x15 x16 x17 (Z_to_bv 64 (bv_unsigned sp + -2128)) x21 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x45ac4) fc None mc (seg_rom bsegs)).
  Proof.
    intros until x31. intros IV N1. unfold mregs. prep IV.
    destruct (unpoisoned_check_rd bsegs mc S (S + N) (S + N + -1) 1 UNP1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b2 & RD2 & CK2).
    unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
    zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((S + N + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LX; eassumption.
    - eapply (LL mc); [exact IV0 | exact N1 | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma LC : forall mc x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31, INV mc ->
    x9 = Z_to_bv 64 N -> x10 = Z_to_bv 64 RES ->
    evtF bsegs RNG POST (MS (mregs x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (bv_unsigned sp + -2128)) x21 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x45988) fc None mc (seg_rom bsegs)).
  Proof.
    intros until x31. intros IV -> ->. unfold mregs. prep IV.
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      zstep. if_cases K3; zify_cond K3.
      2:{ (* [comment removed for export] *) zstep. eapply LX; eassumption. }
      assert (N1 : (64 < N)%Z) by (unland K2; clear - K2 K3 BL0; Z.div_mod_to_equations; lia).
      zstep. zstep. zstep. zstep.
      unfold sf_hide in LO.
      call_sp rip_spec;
        [ exact MI1 | exact ST1 | lia | unfold KHIGH; lia | exact GOT1 | exact SHB1 | exact LAY1
        | zsimp; exact APP | zsimp; exact UNP1
        | zsimp; pose proof BND_ok as B9; unfold BND in B9; lia
        | eapply rng_sub'; [exact RSTK | lia] | ].
      zstep. zstep. zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
      eapply LX. eapply inv_of; eassumption.
    - (* [comment removed for export] *)
      assert (N1 : (1 <= N <= 64)%Z) by (unland K2; clear - K2 BL0; Z.div_mod_to_equations; lia).
      do 11 zstep.
      change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
      unfold sf_hide in R1.
      destruct (shadow_probe8 bsegs mc RLO RHI S WR11 ltac:(apply no_image_asan; pose proof BND_ok as B9; unfold BND in B9; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w1 P1].
      destruct (shadow_probe8 bsegs mc RLO RHI (S + N + -1) WR11 ltac:(apply no_image_asan; pose proof BND_ok as B9; unfold BND in B9; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w2 P2].
      unfold ASHOFF in P1, P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply LE; eassumption.
      + eapply LX; eassumption.
  Qed.

  Lemma memchr_i_body :
    evtF bsegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x45914) fc None m (seg_rom bsegs)).
  Proof.
    pose proof (munch_refl [(bv_unsigned sp + -2208, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
    pose proof BL_ok as BL0. unfold BL in BL0.
    assert (RSTK' : rng RNG (bv_unsigned sp + -2208) 2208) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof MI as MIc. pose proof ST as ST0. pose proof GOT as GOTc. pose proof SHB as SHBc. pose proof INI as INIc.
    pose proof LAY as LAYc. pose proof RMC as RMCc.
    assert (BUFc : bytes_at bsegs m S buf) by exact BUF.
    hide_all.
    carve_frame 56%nat ST0.
    destruct (stk_split _ _ lo (bv_unsigned sp + -2128) _ ST0 ltac:(lia)) as [ST1 STM]. clear ST0.
    do 13 zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. cbv beta. rewrite sxb_sval. change (sval (Z_to_bv 8 1)) with 1%Z. zstep. zstep. zstep. fold_lits. zstep.
    zstep. if_cases K0; zify_cond K0. { exfalso. clear -K0. cbv in K0. lia. } clear K0.
    zstep. call_sp tryinit_spec. all: iprem.
    do 6 zstep. zstep.
    unfold sf_hide in OK.
    call memchr_spec. all: iprem.
    zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1. cbv in K1. lia. } clear K1.
    pose proof hitlen_range as HR.
    destruct (find_byte cc (firstn (Z.to_nat n) buf)) as [j|] eqn:FB.
    - (* [comment removed for export] *)
      assert (ER : RES = (S + Z.of_nat j)%Z) by (unfold memchr_res; rewrite FB; reflexivity).
      assert (EN : N = (Z.of_nat j + 1)%Z) by (unfold hitlen; rewrite FB; reflexivity).
      rewrite ER. zstep. if_cases K2; zify_cond K2. 2:{ exfalso. clear -K2 BL0 HR EN SPOS. lia. } clear K2.
      do 5 zstep. rewrite zb_lxor_ones by lia. zstep. if_cases K3; zify_cond K3. 2:{ exfalso. clear -K3 BL0 HR EN. lia. } clear K3.
      eapply LC; [eapply inv_of; eassumption | f_equal; lia | rewrite ER; reflexivity].
    - (* [comment removed for export] *)
      assert (ER : RES = 0%Z) by (unfold memchr_res; rewrite FB; reflexivity).
      assert (EN : N = n) by (unfold hitlen; rewrite FB; reflexivity).
      rewrite ER. zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2. cbv in K2. lia. } clear K2.
      zstep. rewrite zb_lxor_ones by lia. zstep. zstep. zstep. if_cases K3; zify_cond K3. { exfalso. clear -K3 BL0 HR EN. lia. } clear K3.
      eapply LC; [eapply inv_of; eassumption | rewrite EN; symmetry; apply Z_to_bv_bv_unsigned | rewrite ER; reflexivity].
  Qed.
End MEMCHR.

Lemma memchr_i_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (buf : list byte) (RLO RHI : Z),
  let S := bv_unsigned a0 in let cc := (bv_unsigned a1 mod 256)%Z in let n := bv_unsigned a2 in let N := hitlen cc n buf in
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2208)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_memchr m ->
  bytes_at bsegs m S buf -> memchr_ok S cc n buf ->
  (S + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= S)%Z -> (0 < S)%Z ->
  app_blk S (S + N) -> unpoisoned m S (S + N) -> (N <= 2^40)%Z ->
  (RLO <= S /\ S + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z ->
  wr_at bsegs m (shad RLO) (shad RHI - shad RLO) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S (Z.of_nat (length buf)) -> rng RNG (shad RLO) (shad RHI - shad RLO) ->
  evtF bsegs RNG (memchr_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S cc n buf lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x45914) fc None m (seg_rom bsegs)).
Proof. intros. eapply memchr_i_body; eassumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End CANSEC1.
Notation rt_isl m := (rw_cells bsegs m 0x161920 [C8 (Z_to_bv 64 72340172838076673)]).

Section CANSEC2. Context {rc : runConstT}.
Definition strnlen_i_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S n : Z) (buf : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (strnlen_res n buf)) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 4384, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp) /\ bytes_at bsegs m' S buf.

Section STRNLEN.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (buf : list byte) (RLO RHI : Z).
  Notation S := (bv_unsigned a0).
  Notation n := (bv_unsigned a1).
  Notation N := (hitlen 0 n buf).
  Notation L0 := (strnlen_res n buf).
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 4384)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis GOT : rt_got m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis INI : rt_inited m.
  Hypothesis LAY : rt_layout m.
  Hypothesis RMC : rt_real_memchr m.
  Hypothesis RSL : rt_real_strnlen m.
  Hypothesis ISL : rt_isl m.
  Hypothesis BUF : bytes_at bsegs m S buf.
  Hypothesis OK : memchr_ok S 0 n buf.
  Hypothesis SEPB : (S + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= S)%Z.
  Hypothesis SPOS : (0 < S)%Z.
  Hypothesis APP : app_blk S (S + N).
  Hypothesis UNP : unpoisoned m S (S + N).
  Hypothesis NSZ : (N <= 2^40)%Z.
  Hypothesis R1 : (RLO <= S /\ S + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z.
  Hypothesis WR1 : wr_at bsegs m (shad RLO) (shad RHI - shad RLO).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RB : rng RNG S (Z.of_nat (length buf)).
  Hypothesis RSH1 : rng RNG (shad RLO) (shad RHI - shad RLO).

  Notation POST := (strnlen_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S n buf lo m).
  Notation SAVES := [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Definition SINV (mc : word -> option byte) : Prop :=
    rw_cells bsegs mc (bv_unsigned sp + -64) SAVES
    /\ stk bsegs mc lo (bv_unsigned sp + -2144) /\ stk bsegs mc (bv_unsigned sp + -2144) (bv_unsigned sp + -64)
    /\ munch [(bv_unsigned sp + -4384, bv_unsigned sp)]%Z m mc /\ wmono bsegs m mc /\ mem_inv bsegs mc
    /\ rt_got mc /\ rt_shbase mc /\ rt_layout mc
    /\ unpoisoned mc S (S + N) /\ wr_at bsegs mc (shad RLO) (shad RHI - shad RLO) /\ bytes_at bsegs mc S buf.

  Lemma hitlen_range2 : (0 <= N <= n)%Z.
  Proof.
    unfold hitlen. pose proof (bv_unsigned_in_range 64 a1) as R. unfold bv_modulus in R.
    destruct (find_byte 0 (firstn (Z.to_nat n) buf)) as [j|] eqn:E; [|lia].
    apply find_byte_Some in E. destruct E as [E _]. rewrite firstn_length in E. lia.
  Qed.
  Lemma hitlen_strnlen : N = Z.min (L0 + 1) n.
  Proof.
    unfold hitlen, strnlen_res. pose proof (bv_unsigned_in_range 64 a1) as R. unfold bv_modulus in R.
    destruct (find_byte 0 (firstn (Z.to_nat n) buf)) as [j|] eqn:E; [|lia].
    apply find_byte_Some in E. destruct E as [E _]. rewrite firstn_length in E. lia.
  Qed.

  Definition SBND : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 4384 /\ KHIGH <= lo /\ bv_unsigned sp < 2^64 /\ 0 <= N /\ N <= 2^40 /\ 0 <= n < 2^64
     /\ 0 <= S /\ S + N + 8 <= KEND
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad S /\ shad (S + N - 1) + 1 <= shad RHI /\ shad RHI <= KHIGH
     /\ 0 <= Z.shiftr S 3 < 2^44 /\ -1 <= Z.shiftr (S + N + -1) 3 < 2^44
     /\ shad RLO mod 8 = 0 /\ shad RHI mod 8 = 0
     /\ RLO <= S /\ S + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0)%Z.
  Lemma SBND_ok : SBND.
  Proof.
    unfold SBND. destruct ST as (LOW & _). destruct APP as [LES AS]. unfold KLOW, KHIGH, KEND in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    pose proof (bv_unsigned_in_range 64 a1) as NR. unfold bv_modulus in NR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in NR.
    pose proof hitlen_range2 as HR.
    rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF.
    Z.div_mod_to_equations. lia.
  Qed.
  Ltac acc_facts B ::= pose proof SBND_ok as B; unfold SBND, KHIGH, KEND in B.

  Definition SBL : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 4384 /\ 17594333495296 <= lo /\ bv_unsigned sp < 2^64 /\ 0 <= N <= n /\ N <= 2^40 /\ n < 2^64
     /\ 0 <= S /\ S + N + 8 <= 2^47
     /\ 0 <= Z.shiftr S 3 < 2^44 /\ -1 <= Z.shiftr (S + N + -1) 3 < 2^44
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad S /\ shad (S + N - 1) + 1 <= shad RHI /\ shad RHI <= 17594333495296)%Z.
  Lemma SBL_ok : SBL. Proof. pose proof SBND_ok as B. unfold SBND, KHIGH, KEND in B. pose proof hitlen_range2. unfold SBL. lia. Qed.

  Ltac sinv_open H := destruct H as (FR1 & ST1 & STM1 & MU1 & WM1 & MI1 & GOT1 & SHB1 & LAY1 & UNP1 & WR11 & BUF1).
  Ltac shide_all :=
    change (?P) with (sf_hide P) in R1; change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO;
    change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST; change (?P) with (sf_hide P) in SEPB;
    change (?P) with (sf_hide P) in GOT; change (?P) with (sf_hide P) in SHB; change (?P) with (sf_hide P) in INI;
    change (?P) with (sf_hide P) in LAY; change (?P) with (sf_hide P) in UNP; change (?P) with (sf_hide P) in WR1;
    change (?P) with (sf_hide P) in RMC; change (?P) with (sf_hide P) in RSL; change (?P) with (sf_hide P) in ISL;
    change (?P) with (sf_hide P) in BUF; change (?P) with (sf_hide P) in OK.
  Ltac sprep IV :=
    pose proof IV as IV0; sinv_open IV;
    let B := fresh "BL" in pose proof SBL_ok as B; unfold SBL in B;
    assert (RSTK' : rng RNG (bv_unsigned sp + -4384) 4384) by (eapply rng_sub'; [exact RSTK| lia]);
    shide_all.

  Lemma sinv_of : forall mc,
    rw_cells bsegs mc (bv_unsigned sp + -64) SAVES ->
    stk bsegs mc lo (bv_unsigned sp + -2144) -> stk bsegs mc (bv_unsigned sp + -2144) (bv_unsigned sp + -64) ->
    munch [(bv_unsigned sp + -4384, bv_unsigned sp)]%Z m mc -> wmono bsegs m mc -> mem_inv bsegs mc ->
    rt_got mc -> rt_shbase mc -> rt_layout mc -> SINV mc.
  Proof.
    intros mc FR1 ST1 STM1 MU1 WM1 MI1 G1 G2 G3. pose proof SBND_ok as B. unfold SBND, KHIGH, KEND in B.
    repeat (split; [assumption|]).
    assert (SS : (shad (S + N - 1) + 1 <= 17594333495296)%Z) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
    split. { eapply unpoisoned_munch; [exact UNP | exact MU1 |]. cbn [disjoint_from]. lia. }
    split. { eapply wr_at_transport; eassumption. }
    eapply bytes_at_transport; [exact BUF | exact MU1 |]. cbn [disjoint_from]. lia.
  Qed.

  (* [comment removed for export] *)
  Definition sregs (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word) :=
    mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17
        a0 a1 (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 0x161828) x22 s7 s8 s9 s10 s11 x28 x29 x30 x31.

  (* [comment removed for export] *)
  Lemma SX : forall mc x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31, SINV mc ->
    evtF bsegs RNG POST (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 (Z_to_bv 64 L0) x11 x12 x13 x14 x15 x16 x17
                                 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x445dc) fc None mc (seg_rom bsegs)).
  Proof.
    intros until x31. intros IV. sprep IV.
    do 11 zstep.
    pose proof (stk_merge _ _ _ _ _ ST1 STM1 ltac:(lia)) as SK.
    pose proof (stk_release _ _ _ _ _ SK FR1 ltac:(lia)) as SK2. cbn [cells_size csize Nat.add] in SK2.
    replace (bv_unsigned sp + -64 + Z.of_nat 64)%Z with (bv_unsigned sp) in SK2 by lia.
    apply evtF_done. unfold strnlen_i_post.
    replace (bv_unsigned sp - 4384)%Z with (bv_unsigned sp + -4384)%Z by lia.
    do 15 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma SL : forall mc (k : nat) (c : Z) x1 x5 x6 x7 x14 x15 x16 x17 x22 x28 x29 x30 x31,
    SINV mc -> (1 <= N <= 64)%Z -> Z.to_nat (shad (S + N - 1) - c) = k -> (shad S <= c < shad (S + N - 1))%Z ->
    evtF bsegs RNG POST (MS (sregs x1 x5 x6 x7 (Z_to_bv 64 N) (Z_to_bv 64 L0) (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (S + N + -1) 3)) (Z_to_bv 64 0) x14 x15 x16 x17
                                   x22 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x446b0) fc None mc (seg_rom bsegs)).
  Proof.
    intros until x31. intros IV N1 Hk Hc. unfold sregs. sprep IV.
    revert c x14 Hk Hc. induction k as [|k IH]; intros c x14 Hk Hc; [exfalso; lia|].
    assert (SLE : (shad (S + N - 1) = 2147450880 + Z.shiftr (S + N + -1) 3)%Z) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
    pose proof (unpoisoned_full_rd bsegs mc S (S + N) c UNP1 ltac:(lia)
                  ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K1; zify_cond K1.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply SX; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma SE : forall mc x1 x5 x6 x7 x14 x15 x16 x17 x22 x28 x29 x30 x31, SINV mc -> (1 <= N <= 64)%Z ->
    evtF bsegs RNG POST (MS (sregs x1 x5 x6 x7 (Z_to_bv 64 N) (Z_to_bv 64 L0) (Z_to_bv 64 (2147450880 + Z.shiftr S 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (S + N + -1) 3))
                                   (Z_to_bv 64 (S + N + -1)) x14 x15 x16 x17 x22 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x44694) fc None mc (seg_rom bsegs)).
  Proof.
    intros until x31. intros IV N1. unfold sregs. sprep IV.
    destruct (unpoisoned_check_rd bsegs mc S (S + N) (S + N + -1) 1 UNP1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b2 & RD2 & CK2).
    unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
    zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((S + N + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply SX; eassumption.
    - eapply (SL mc); [exact IV0 | exact N1 | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma SC : forall mc x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31, SINV mc -> x9 = Z_to_bv 64 N ->
    evtF bsegs RNG POST (MS (sregs x1 x5 x6 x7 x9 (Z_to_bv 64 L0) x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x44594) fc None mc (seg_rom bsegs)).
  Proof.
    intros until x31. intros IV ->. unfold sregs. sprep IV.
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      zstep. if_cases K3; zify_cond K3.
      2:{ (* [comment removed for export] *) zstep. eapply SX; eassumption. }
      assert (N1 : (64 < N)%Z) by (unland K2; clear - K2 K3 BL0; Z.div_mod_to_equations; lia).
      zstep. zstep. zstep. zstep.
      unfold sf_hide in LO.
      call_sp rip_spec;
        [ exact MI1 | exact ST1 | lia | unfold KHIGH; lia | exact GOT1 | exact SHB1 | exact LAY1
        | zsimp; exact APP | zsimp; exact UNP1
        | zsimp; pose proof SBND_ok as B9; unfold SBND in B9; lia
        | eapply rng_sub'; [exact RSTK | lia] | ].
      zstep. zstep. zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
      eapply SX. eapply sinv_of; eassumption.
    - (* [comment removed for export] *)
      assert (N1 : (1 <= N <= 64)%Z) by (unland K2; clear - K2 BL0; Z.div_mod_to_equations; lia).
      do 11 zstep.
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

  Lemma L0_range : (0 <= L0 <= n)%Z /\ N = Z.min (L0 + 1) n.
  Proof.
    pose proof hitlen_strnlen as HS. unfold strnlen_res in *. pose proof (bv_unsigned_in_range 64 a1) as R. unfold bv_modulus in R.
    destruct (find_byte 0 (firstn (Z.to_nat n) buf)) as [j|] eqn:E; [|lia].
    apply find_byte_Some in E. destruct E as [E _]. rewrite firstn_length in E. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma SJ : forall mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31, SINV mc -> (L0 + 1 < 2^64)%Z -> x10 = Z_to_bv 64 L0 ->
    evtF bsegs RNG POST (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp (Z_to_bv 64 1) x10 x11 x12 x13 x14 x15 x16 x17
                                 a0 a1 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x44568) fc None mc (seg_rom bsegs)).
  Proof.
    intros until x31. intros IV L1 ->. pose proof L0_range as [LR HS]. sprep IV.
    assert (ISL1 : rw_cells bsegs mc 0x161920 [CB 3 (repeat (Z_to_bv 8 1) 3); C1 (Z_to_bv 8 1); CB 4 (repeat (Z_to_bv 8 1) 4)]).
    { unfold sf_hide in ISL. pose proof ISL as ISL'.
      eapply rw_cells_transport in ISL'; [| exact MU1 | exact WM1 | cbn [disjoint_from cells_size csize Nat.add]; lia].
      recell ISL' 0%nat 1%nat [CB 3 (repeat (Z_to_bv 8 1) 3); C1 (Z_to_bv 8 1); CB 4 (repeat (Z_to_bv 8 1) 4)]. exact ISL'. }
    zstep. if_cases K0; zify_cond K0. { exfalso. clear -K0. cbv in K0. lia. } clear K0.
    zstep. zstep. zstep. cbv beta. rewrite unsigned_lit8 by lia. zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1. cbv in K1. lia. } clear K1.
    zstep. zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      zstep. zstep. rewrite zb_lxor_ones by lia. zstep. zstep. zstep. if_cases K3; zify_cond K3. 2:{ exfalso. clear -K3 BL0 LR HS K2. lia. }
      assert (EN : N = n) by (clear -HS K2 LR; lia).
      eapply SC; [exact IV0 |]. rewrite EN. symmetry. apply Z_to_bv_bv_unsigned.
    - (* [comment removed for export] *)
      zstep. rewrite zb_lxor_ones by lia. zstep. zstep. zstep. if_cases K3; zify_cond K3. { exfalso. clear -K3 BL0 LR HS K2. lia. }
      eapply SC; [exact IV0 |]. f_equal. lia.
  Qed.

  Lemma strnlen_i_body :
    evtF bsegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x44518) fc None m (seg_rom bsegs)).
  Proof.
    pose proof (munch_refl [(bv_unsigned sp + -4384, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
    pose proof SBL_ok as BL0. unfold SBL in BL0. pose proof L0_range as [LR HS].
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    assert (RSTK' : rng RNG (bv_unsigned sp + -4384) 4384) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof MI as MIc. pose proof ST as ST0. pose proof GOT as GOTc. pose proof SHB as SHBc. pose proof INI as INIc.
    pose proof LAY as LAYc. pose proof RMC as RMCc. pose proof RSL as RSLc.
    pose proof APP as APPc. pose proof WR1 as WR1c. pose proof R1 as R1c.
    assert (BUFc : bytes_at bsegs m S buf) by exact BUF. assert (OKc : memchr_ok S 0 n buf) by exact OK.
    shide_all.
    carve_frame 64%nat ST0.
    destruct (stk_split _ _ lo (bv_unsigned sp + -2144) _ ST0 ltac:(lia)) as [ST1 STM]. clear ST0.
    do 13 zstep. zstep.
    call_sp tryinit_spec. all: iprem.
    do 5 zstep. zstep.
    (* [comment removed for export] *)
    match goal with H : stk bsegs _ lo (bv_unsigned sp + -2144) |- _ => carve_frame 32%nat H end.
    do 8 zstep. zstep. zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) => lazymatch goal with MU1 : munch _ m m1 |- _ =>
      assert (UNP1 : unpoisoned m1 S (S + N)) by (unfold sf_hide in UNP; eapply unpoisoned_munch; [exact UNP | exact MU1 |]; cbn [disjoint_from]; clear -BL0; lia)
    end end.
    call_sp memchr_i_spec. all: iprem.
    rewrite ?unsigned_lit in * by lia. change ((0 mod 256)%Z) with 0%Z in *.
    try rename POST into RTI9.
    (* [comment removed for export] *)
    assert (TAIL : forall mc x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 jk,
      rw_cells bsegs mc (bv_unsigned sp + -2176) [CB 8 jk; C8 (Z_to_bv 64 1); C8 sp; C8 (Z_to_bv 64 0x44568)] ->
      rw_cells bsegs mc (bv_unsigned sp + -64) SAVES ->
      stk bsegs mc lo (bv_unsigned sp + -2176) -> stk bsegs mc (bv_unsigned sp + -2144) (bv_unsigned sp + -64) ->
      munch [(bv_unsigned sp + -4384, bv_unsigned sp)]%Z m mc -> wmono bsegs m mc -> mem_inv bsegs mc ->
      rt_got mc -> rt_shbase mc -> rt_layout mc ->
      evtF bsegs RNG POST (MS (mkR (Z_to_bv 64 0xc0ee8) (Z_to_bv 64 (bv_unsigned sp + -2176)) gp tp x5 x6 x7 a1 a0
                                   (Z_to_bv 64 (memchr_res S 0 n buf)) x11 x12 x13 x14 x15 x16 x17
                                   a0 a1 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                              F (Z_to_bv 64 0xc0ee8) fc None mc (seg_rom bsegs))).
    { intros until jk. intros FRS FR9 ST2 STM9 MU9 WM9 MI9 G1 G2 G3.
      assert (IV : SINV mc).
      { pose proof (stk_release _ _ _ _ _ ST2 FRS ltac:(lia)) as ST3. cbn [cells_size csize Nat.add] in ST3.
        replace (bv_unsigned sp + -2176 + Z.of_nat 32)%Z with (bv_unsigned sp + -2144)%Z in ST3 by lia.
        eapply sinv_of; eassumption. }
      destruct (find_byte 0 (firstn (Z.to_nat n) buf)) as [j|] eqn:FB.
      - assert (ER : memchr_res S 0 n buf = (S + Z.of_nat j)%Z) by (unfold memchr_res; rewrite FB; reflexivity).
        assert (EL : L0 = Z.of_nat j) by (unfold strnlen_res; rewrite FB; reflexivity).
        pose proof (find_byte_Some _ _ _ FB) as [FJ _]. rewrite firstn_length in FJ.
        rewrite ER. zstep. if_cases K1; zify_cond K1. { exfalso. unland K1. clear -K1 BL0 LR HS EL SPOS FJ. Z.div_mod_to_equations; lia. } clear K1.
        do 6 zstep. zstep.
        eapply SJ; [exact IV | lia | f_equal; lia].
      - assert (ER : memchr_res S 0 n buf = 0%Z) by (unfold memchr_res; rewrite FB; reflexivity).
        assert (EL : L0 = n) by (unfold strnlen_res; rewrite FB; reflexivity).
        unfold sf_hide in OK. pose proof OK as OK'. unfold memchr_ok in OK'. rewrite FB in OK'.
        rewrite ER. zstep. if_cases K1; zify_cond K1. 2:{ exfalso. clear -K1. cbv in K1. lia. } clear K1.
        do 5 zstep. zstep.
        eapply SJ; [exact IV | lia | rewrite EL; symmetry; apply Z_to_bv_bv_unsigned]. }
    eapply TAIL; eassumption.
  Qed.
End STRNLEN.

Lemma strnlen_i_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (buf : list byte) (RLO RHI : Z),
  let S := bv_unsigned a0 in let n := bv_unsigned a1 in let N := hitlen 0 n buf in
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 4384)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_memchr m -> rt_real_strnlen m -> rt_isl m ->
  bytes_at bsegs m S buf -> memchr_ok S 0 n buf ->
  (S + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= S)%Z -> (0 < S)%Z ->
  app_blk S (S + N) -> unpoisoned m S (S + N) -> (N <= 2^40)%Z ->
  (RLO <= S /\ S + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z ->
  wr_at bsegs m (shad RLO) (shad RHI - shad RLO) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S (Z.of_nat (length buf)) -> rng RNG (shad RLO) (shad RHI - shad RLO) ->
  evtF bsegs RNG (strnlen_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S n buf lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44518) fc None m (seg_rom bsegs)).
Proof. intros. eapply strnlen_i_body; eassumption. Qed.

End CANSEC2.
