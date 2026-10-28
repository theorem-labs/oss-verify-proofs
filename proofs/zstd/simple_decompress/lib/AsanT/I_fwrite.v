(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun Stdio_pure.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ShadowTac F_rip F_tryinit.
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
  | |- wr_at _ _ _ _ => first [assumption | eassumption]
  | |- app_blk _ _ => first [assumption | eassumption]
  | |- Forall _ _ => first [assumption | eassumption]
  | |- _ = Z_to_bv 64 _ => first [reflexivity | assumption | symmetry; assumption]
  | |- rng _ _ _ => first [ assumption | match goal with H : rng _ _ _ |- _ => eapply rng_sub'; [exact H | unfold KHIGH, sf_hide in *; lia] end ]
  | |- _ => unfold KHIGH, sf_hide in *; first [assumption | lia]
  end.

(* [comment removed for export] *)
Notation rt_real_fwrite m := (rw_cells bsegs m 0xc9090 [C8 (Z_to_bv 64 0xbcbf0)]).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition fwrite_i_mid (ra sp gp tp s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 x14 x15 x16 x17 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x46128) (Z_to_bv 64 (bv_unsigned sp - 2128)) gp tp t0 t1 t2
                  sp a1 a0 a1 a2 a3 x14 x15 x16 x17
                  a0 a3 a2 (Z_to_bv 64 1) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xbcbf0) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 2144, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp - 2128) /\ stk bsegs m' (bv_unsigned sp - 2128) (bv_unsigned sp - 56)
    /\ rw_cells bsegs m' (bv_unsigned sp - 56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rt_inited m'.

Section FWRITE_PRE.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z).
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 2144)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis INI : rt_inited m.
  Hypothesis RFW : rt_real_fwrite m.
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).

  Lemma fwrite_i_pre :
    evtF bsegs RNG (fwrite_i_mid ra sp gp tp s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x460cc) fc None m (seg_rom bsegs)).
  Proof.
    pose proof (munch_refl [(bv_unsigned sp + -2144, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption). unfold KHIGH in KLO.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    assert (RSTK' : rng RNG (bv_unsigned sp + -2144) 2144) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof MI as MIc. pose proof ST as ST0. pose proof INI as INIc. pose proof RFW as RFWc.
    change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST; change (?P) with (sf_hide P) in INI; change (?P) with (sf_hide P) in RFW.
    carve_frame 56%nat ST0.
    destruct (stk_split _ _ lo (bv_unsigned sp + -2128) _ ST0 ltac:(lia)) as [ST1 STM]. clear ST0.
    do 14 zstep. zstep.
    call_sp tryinit_spec. all: iprem.
    do 7 zstep. zstep.
    apply evtF_done. unfold fwrite_i_mid.
    replace (bv_unsigned sp - 2128)%Z with (bv_unsigned sp + -2128)%Z by lia.
    replace (bv_unsigned sp - 56)%Z with (bv_unsigned sp + -56)%Z by lia.
    replace (bv_unsigned sp - 2144)%Z with (bv_unsigned sp + -2144)%Z by lia.
    do 12 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption.
  Qed.
End FWRITE_PRE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fwrite_i_post_post (sp gp tp s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (rav s0v s1v s2v s3v s4v s5v : word) (res lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 res) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc rav) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 2208, bv_unsigned sp - 2128)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp).

Section FWRITE_POST.
  Variables (RNG : footprint)
            (x1 sp gp tp t0 t1 t2 x9 a1 a2 a3 a4 a5 a6 a7 p x19 x20 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (rav s0v s1v s2v s3v s4v s5v : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo res size N : Z) (RLO RHI : Z).
  Notation P := (bv_unsigned p).
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis ST : stk bsegs m lo (bv_unsigned sp - 2128).
  Hypothesis STM : stk bsegs m (bv_unsigned sp - 2128) (bv_unsigned sp - 56).
  Hypothesis FR : rw_cells bsegs m (bv_unsigned sp - 56) [C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].
  Hypothesis LO : (lo <= bv_unsigned sp - 2208)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis GOT : rt_got m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis LAY : rt_layout m.
  Hypothesis X9 : x9 = Z_to_bv 64 size.
  Hypothesis HN : (res * size)%Z = N.
  Hypothesis RES : (0 <= res < 2^64 /\ 1 <= size /\ 0 <= N <= 2^40)%Z.
  Hypothesis APP : app_blk P (P + N).
  Hypothesis UNP : unpoisoned m P (P + N).
  Hypothesis R1 : (RLO <= P /\ P + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z.
  Hypothesis WR1 : wr_at bsegs m (shad RLO) (shad RHI - shad RLO).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RSH1 : rng RNG (shad RLO) (shad RHI - shad RLO).

  Notation POST := (fwrite_i_post_post sp gp tp s6 s7 s8 s9 s10 s11 F fc rav s0v s1v s2v s3v s4v s5v res lo m).

  Definition INV (mc : word -> option byte) : Prop :=
    rw_cells bsegs mc (bv_unsigned sp + -56) [C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]
    /\ stk bsegs mc lo (bv_unsigned sp + -2128) /\ stk bsegs mc (bv_unsigned sp + -2128) (bv_unsigned sp + -56)
    /\ munch [(bv_unsigned sp + -2208, bv_unsigned sp + -2128)]%Z m mc /\ wmono bsegs m mc /\ mem_inv bsegs mc
    /\ rt_got mc /\ rt_shbase mc /\ rt_layout mc
    /\ unpoisoned mc P (P + N) /\ wr_at bsegs mc (shad RLO) (shad RHI - shad RLO).

  Definition BND : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2208 /\ KHIGH <= lo /\ bv_unsigned sp < 2^64 /\ 0 <= N /\ N <= 2^40 /\ 0 <= res < 2^64
     /\ 0 <= P /\ P + N + 8 <= KEND
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad P /\ shad (P + N - 1) + 1 <= shad RHI /\ shad RHI <= KHIGH
     /\ 0 <= Z.shiftr P 3 < 2^44 /\ -1 <= Z.shiftr (P + N + -1) 3 < 2^44
     /\ shad RLO mod 8 = 0 /\ shad RHI mod 8 = 0
     /\ RLO <= P /\ P + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0)%Z.
  Lemma BND_ok : BND.
  Proof.
    unfold BND. destruct ST as (L0 & _). destruct APP as [LES AS]. unfold KLOW, KHIGH, KEND in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    pose proof (bv_unsigned_in_range 64 p) as PR. unfold bv_modulus in PR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in PR.
    rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF.
    Z.div_mod_to_equations. lia.
  Qed.
  Ltac acc_facts B ::= pose proof BND_ok as B; unfold BND, KHIGH, KEND in B.

  Definition BL : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2208 /\ 17594333495296 <= lo /\ bv_unsigned sp < 2^64 /\ 0 <= N /\ N <= 2^40 /\ 0 <= res < 2^64
     /\ 0 <= P /\ P + N + 8 <= 2^47
     /\ 0 <= Z.shiftr P 3 < 2^44 /\ -1 <= Z.shiftr (P + N + -1) 3 < 2^44
     /\ 2147450880 <= shad RLO /\ shad RLO <= shad P /\ shad (P + N - 1) + 1 <= shad RHI /\ shad RHI <= 17594333495296)%Z.
  Lemma BL_ok : BL. Proof. pose proof BND_ok as B. unfold BND, KHIGH, KEND in B. unfold BL. lia. Qed.

  Ltac inv_open H := destruct H as (FR1 & ST1 & STM1 & MU1 & WM1 & MI1 & GOT1 & SHB1 & LAY1 & UNP1 & WR11).
  Ltac prep IV :=
    pose proof IV as IV0; inv_open IV;
    let B := fresh "BL" in pose proof BL_ok as B; unfold BL in B;
    assert (RSTK' : rng RNG (bv_unsigned sp + -2208) 2208) by (eapply rng_sub'; [exact RSTK| lia]);
    change (?P) with (sf_hide P) in R1; change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO;
    change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST; change (?P) with (sf_hide P) in STM;
    change (?P) with (sf_hide P) in FR; change (?P) with (sf_hide P) in GOT; change (?P) with (sf_hide P) in SHB;
    change (?P) with (sf_hide P) in LAY; change (?P) with (sf_hide P) in UNP; change (?P) with (sf_hide P) in WR1.

  Lemma inv_of : forall mc,
    rw_cells bsegs mc (bv_unsigned sp + -56) [C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
    stk bsegs mc lo (bv_unsigned sp + -2128) -> stk bsegs mc (bv_unsigned sp + -2128) (bv_unsigned sp + -56) ->
    munch [(bv_unsigned sp + -2208, bv_unsigned sp + -2128)]%Z m mc -> wmono bsegs m mc -> mem_inv bsegs mc ->
    rt_got mc -> rt_shbase mc -> rt_layout mc -> INV mc.
  Proof.
    intros mc FR1 ST1 STM1 MU1 WM1 MI1 G1 G2 G3. pose proof BND_ok as B. unfold BND, KHIGH, KEND in B.
    repeat (split; [assumption|]).
    assert (SS : (shad (P + N - 1) + 1 <= 17594333495296)%Z) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
    split. { eapply unpoisoned_munch; [exact UNP | exact MU1 |]. cbn [disjoint_from]. lia. }
    eapply wr_at_transport; eassumption.
  Qed.

  Notation FWR pc x10 x11 x12 x13 x14 x15 mc :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2 sp (Z_to_bv 64 N) x10 x11 x12 x13 x14 x15 a6 a7
             p x19 (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 1) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mc (seg_rom bsegs)) (only parsing).

  (* [comment removed for export] *)
  Lemma LX : forall mc x1' x5 x6 x7 x9' x11 x12 x13 x14 x15 x16 x17 x20' x21' x28 x29 x30 x31, INV mc ->
    evtF bsegs RNG POST
      (MS (mkR x1' (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp x9' (Z_to_bv 64 res) x11 x12 x13 x14 x15 x16 x17
               p x19 x20' x21' s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x4618c) fc None mc (seg_rom bsegs)).
  Proof.
    intros until x31. intros IV. prep IV.
    do 10 zstep.
    pose proof (stk_merge _ _ _ _ _ ST1 STM1 ltac:(lia)) as SK.
    pose proof (stk_release _ _ _ _ _ SK FR1 ltac:(lia)) as SK2. cbn [cells_size csize Nat.add] in SK2.
    replace (bv_unsigned sp + -56 + Z.of_nat 56)%Z with (bv_unsigned sp) in SK2 by lia.
    apply evtF_done. unfold fwrite_i_post_post.
    replace (bv_unsigned sp - 2208)%Z with (bv_unsigned sp + -2208)%Z by lia.
    replace (bv_unsigned sp - 2128)%Z with (bv_unsigned sp + -2128)%Z by lia.
    do 15 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma LL : forall mc (k : nat) (c : Z) x14 x15,
    INV mc -> (1 <= N <= 64)%Z -> Z.to_nat (shad (P + N - 1) - c) = k -> (shad P <= c < shad (P + N - 1))%Z ->
    evtF bsegs RNG POST (FWR 0x46250 (Z_to_bv 64 res) (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (P + N + -1) 3)) (Z_to_bv 64 0) x14 x15 mc).
  Proof.
    intros mc k c x14 x15 IV N1 Hk Hc. prep IV.
    revert c x14 Hk Hc. induction k as [|k IH]; intros c x14 Hk Hc; [exfalso; lia|].
    assert (SL : (shad (P + N - 1) = 2147450880 + Z.shiftr (P + N + -1) 3)%Z) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
    pose proof (unpoisoned_full_rd bsegs mc P (P + N) c UNP1 ltac:(lia)
                  ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K1; zify_cond K1.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply LX; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma LE : forall mc x14 x15, INV mc -> (1 <= N <= 64)%Z ->
    evtF bsegs RNG POST (FWR 0x46234 (Z_to_bv 64 res) (Z_to_bv 64 (2147450880 + Z.shiftr P 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (P + N + -1) 3))
                             (Z_to_bv 64 (P + N + -1)) x14 x15 mc).
  Proof.
    intros mc x14 x15 IV N1. prep IV.
    destruct (unpoisoned_check_rd bsegs mc P (P + N) (P + N + -1) 1 UNP1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b2 & RD2 & CK2).
    unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
    zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((P + N + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LX; eassumption.
    - eapply (LL mc); [exact IV0 | exact N1 | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      Z.div_mod_to_equations; lia.
  Qed.

  Lemma fwrite_i_post :
    evtF bsegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2 sp x9 (Z_to_bv 64 res) a1 a2 a3 a4 a5 a6 a7
               p x19 x20 (Z_to_bv 64 1) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x46128) fc None m (seg_rom bsegs)).
  Proof.
    assert (IV : INV m).
    { pose proof ST as ST'. pose proof STM as STM'. pose proof FR as FR'.
      replace (bv_unsigned sp - 2128)%Z with (bv_unsigned sp + -2128)%Z in ST', STM' by lia.
      replace (bv_unsigned sp - 56)%Z with (bv_unsigned sp + -56)%Z in STM', FR' by lia.
      repeat (split; [assumption|]); try assumption. all: try apply munch_refl; try apply wmono_refl.
      split; [apply munch_refl|]. split; [apply wmono_refl|]. repeat (split; [assumption|]). assumption. }
    prep IV. subst x9.
    zstep. if_cases K0; zify_cond K0. { exfalso. clear -K0. cbv in K0. lia. } clear K0.
    zstep. if_cases KR; zify_cond KR.
    { (* [comment removed for export] *) eapply LX; eassumption. }
    assert (NPOS : (1 <= N)%Z) by (clear -KR RES HN BL0; nia).
    zstep. rewrite HN.
    zstep. rewrite zb_lxor_ones by lia. zstep. zstep. zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1 BL0. lia. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      assert (N1 : (64 < N)%Z).
      { change 18446744073709551615%Z with (Z.ones 64) in K2. rewrite ?Z.land_ones in K2 by lia. change (2 ^ 64)%Z with 18446744073709551616%Z in K2.
        clear - K2 BL0 NPOS. Z.div_mod_to_equations. lia. }
      zstep. if_cases K3; zify_cond K3. 2:{ exfalso. clear -K3 BL0 N1. lia. }
      zstep. zstep. zstep. zstep.
      unfold sf_hide in LO.
      call_sp rip_spec;
        [ exact MI1 | exact ST1 | lia | unfold KHIGH; lia | exact GOT1 | exact SHB1 | exact LAY1
        | zsimp; exact APP | zsimp; exact UNP1
        | zsimp; pose proof BND_ok as B9; unfold BND in B9; lia
        | eapply rng_sub'; [exact RSTK | lia] | ].
      zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
      zstep. zstep.
      eapply LX. eapply inv_of; eassumption.
    - (* [comment removed for export] *)
      assert (N1 : (1 <= N <= 64)%Z).
      { change 18446744073709551615%Z with (Z.ones 64) in K2. rewrite ?Z.land_ones in K2 by lia. change (2 ^ 64)%Z with 18446744073709551616%Z in K2.
        clear - K2 BL0 NPOS. Z.div_mod_to_equations. lia. }
      do 11 zstep.
      change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
      unfold sf_hide in R1.
      destruct (shadow_probe8 bsegs m RLO RHI P WR11 ltac:(apply no_image_asan; pose proof BND_ok as B9; unfold BND in B9; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w1 P1].
      destruct (shadow_probe8 bsegs m RLO RHI (P + N + -1) WR11 ltac:(apply no_image_asan; pose proof BND_ok as B9; unfold BND in B9; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w2 P2].
      unfold ASHOFF in P1, P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply LE; eassumption.
      + eapply LX; eassumption.
  Qed.
End FWRITE_POST.
End CANSEC1.
