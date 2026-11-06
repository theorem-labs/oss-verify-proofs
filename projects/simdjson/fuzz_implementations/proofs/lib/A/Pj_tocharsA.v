(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjPjNum SjPjDig.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.A Require Import Layout Shadow RT_iface RT_iface2 D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf
     Sj_num_akit Sj_num_amem Sj_num_aframe Sj_num_lm_kit Pj_defsA Pj_rtkA Pj_sfA_a Pj_sfA Pj_tocharsA_defs Pj_tocharsA_a Pj_tocharsA_b
     Pj_tocharsA_r Pj_tocharsA_c Pj_tocharsA_c2 Pj_tocharsA_d Pj_tocharsA_k RT_iface3 I_lkit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma wr_at_sub : forall (m : mem) A n a k, wr_at asegs m A n -> A <= a -> a + k <= A + n -> 0 <= k -> wr_at asegs m a k.
Proof.
  intros m A n a k (H0 & H1 & H) Ha Hk K0. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a + i) with (A + (a - A + i)) by lia. apply H. lia.
Qed.

Lemma u8arr_acc40 : forall (m : mem) A (bs : list byte), A mod 8 = 0 -> 0 <= A -> bytes_at asegs m (shad A) (repeat z8 5) -> acc asegs m A 40.
Proof. intros m A bs A8 A0 H. change 40 with (8 * Z.of_nat 5). exact (acc_zero_run asegs m A 5 A8 A0 H). Qed.

Section TC.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis RC2 : rt_contracts2 RT.
Variable PMc : Model -> Prop.

Section Calls.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Variables (Σ Σ1 : rts RT) (J : tcI) (fN : Z) (kN : nat) (K : config -> Prop) (m0 : mem).
Hypothesis OK : tc_ok J.
Notation q := (ti_q J). Notation spq := (ti_spq J). Notation NB := (ti_NB J). Notation f := (ti_f J). Notation Sh := (ti_S J). Notation lo := (ti_lo J).
Hypothesis EF : rt_frames RT Σ1 = (ti_f J, 1%nat) :: rt_frames RT Σ.
Hypothesis EL : rt_live RT Σ1 = rt_live RT Σ.
Hypothesis ES : rt_sp0 RT Σ1 = rt_sp0 RT Σ.
Hypothesis EC : rt_credit RT Σ1 = rt_credit RT Σ - 1.
Hypothesis INF : In (fN, kN) (rt_frames RT Σ).
Hypothesis NBF : fN <= ti_NB J /\ ti_NB J + 40 <= fN + fs_size kN - 8.
Hypothesis LOR : rt_sp0 RT Σ - STACK_WIN <= ti_lo J.
Hypothesis HK : forall (Σ' : rts RT) (e : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' (nb : list byte),
  frm0 fc' -> ART RT Σ' m' -> mem_inv asegs m' -> stk asegs m' lo q ->
  rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ -> rt_credit RT Σ - 1 <= rt_credit RT Σ' ->
  rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q [(NB, NB + 40)] m0 m' ->
  NB < e <= NB + 27 -> rw_cells asegs m' NB [CB 40 nb] ->
  aevt RT PMc Σ' K (MS (mkR (ti_ra J) (Z_to_bv 64 q) (ti_gp J) (Z_to_bv 64 TPV_A) t0' t1' t2' (ti_s0 J) (ti_s1 J) (Z_to_bv 64 e) a1' a2' a3' a4' a5' a6' a7'
                        (ti_s2 J) (ti_s3 J) (ti_s4 J) (ti_s5 J) (ti_s6 J) (ti_s7 J) (ti_s8 J) (ti_s9 J) (ti_s10 J) (ti_s11 J) t3' t4' t5' t6')
                   F' (ret_pc (ti_ra J)) fc' None m' (seg_rom asegs)).

Notation Q := (fun ms : machine_state => aevt RT PMc Σ1 K ms).
Notation BASEJ := (BASE RT Σ Σ1 J).
Notation KZ mb B := (tc_finA RT AF PMc MST Σ Σ1 J fN kN OK EF EL ES INF NBF LOR K m0 HK EC mb B).

Local Ltac ul := unfold ti_spq, ti_S, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Lemma tc_call_ok : forall mb mm shc, TINV J shc mb mm -> call_ok RT Σ1 mm (Z_to_bv 64 spq) lo.
Proof using OK ES LOR.
  intros mb mm shc TI. ti_open TI. ti_envX OK. unfold call_ok. rewrite unsigned_lit by ul. rewrite ES.
  split; [exact ST|]. split; [ul|]. split; [ul|]. split; [ul|].
  destruct Cd as [Ed|Ed]; rewrite Ed; clear - Cq16; Z.div_mod_to_equations; lia.
Qed.

Lemma nb_checked_dst : forall mb mm shc d k, BASEJ m0 mb -> TINV J shc mb mm -> NB <= d -> d + k <= NB + 40 -> 0 <= k ->
  checked_dst RT Σ1 mm (Z_to_bv 64 spq) d k.
Proof using AF OK EF INF NBF LOR ES.
  intros mb mm shc d k B TI D1 D2 K0. pose proof (inFN1 RT Σ Σ1 J fN kN EF INF) as IN2.
  pose proof (base_nbsh RT Σ Σ1 J OK m0 mb mm B ltac:(destruct TI as (_ & _ & _ & _ & _ & _ & _ & MU & _); exact MU)) as SHN.
  ti_open TI. ti_envX OK. unfold checked_dst. rewrite unsigned_lit by ul. split; [| split].
  - intros _. split.
    + apply (acc_sub asegs mm NB 40 d k); [| lia| lia]. apply (u8arr_acc40 mm NB nb Cnb8 ltac:(lia)). unfold shad, SHB. exact SHN.
    + right; left. exists fN, kN. split; [exact IN2| lia].
  - intros i Hi. right; right; right; left. exists fN, kN. split; [exact IN2| lia].
  - destruct NA as [_ W]. rewrite NL in W. apply (wr_at_sub mm NB 40 d k W); lia.
Qed.

Lemma nb_checked_src : forall mb mm shc s k, BASEJ m0 mb -> TINV J shc mb mm -> NB <= s -> s + k <= NB + 40 ->
  checked_src RT Σ1 mm (Z_to_bv 64 spq) lo s k.
Proof using AF OK EF INF NBF LOR ES.
  intros mb mm shc s k B TI S1 S2. pose proof (inFN1 RT Σ Σ1 J fN kN EF INF) as IN2.
  pose proof (base_nbsh RT Σ Σ1 J OK m0 mb mm B ltac:(destruct TI as (_ & _ & _ & _ & _ & _ & _ & MU & _); exact MU)) as SHN.
  ti_open TI. ti_envX OK. unfold checked_src. rewrite unsigned_lit by ul. split.
  - intros _. split.
    + apply (acc_sub asegs mm NB 40 s k); [| lia| lia]. apply (u8arr_acc40 mm NB nb Cnb8 ltac:(lia)). unfold shad, SHB. exact SHN.
    + right; left. exists fN, kN. split; [exact IN2| lia].
  - left. lia.
Qed.

Lemma nb_bytes : forall (mm : mem) nb (k n : nat), u8arr asegs mm NB nb -> length nb = 40%nat -> (k + n <= 40)%nat ->
  bytes_at asegs mm (NB + Z.of_nat k) (firstn n (skipn k nb)) /\ length (firstn n (skipn k nb)) = n.
Proof.
  intros mm nb k n UA L Hk. split; [apply (bytes_at_sub asegs mm NB nb k n (proj1 UA)); rewrite L; exact Hk|].
  rewrite length_firstn, length_skipn, L. lia.
Qed.

Notation BART mb mm shc B TI := (base_art RT AF Σ Σ1 J fN kN OK EF ES INF NBF LOR m0 mb mm shc B TI).
Notation BSHPN mb B := (base_shpn RT Σ Σ1 J OK m0 mb B).

Lemma tc_lay1A : forall mb e sg n, BASEJ m0 mb -> (SF_EMIN <= e <= SF_EMAX) -> (0 <= sg <= 1) -> (1 <= n <= 20) ->
  tc_l1_k J mb Q e sg n.
Proof using AF RC RC2 FDO MST OK EF EL ES EC INF NBF LOR HK.
  intros mb e sg n B HE HSG HN. unfold tc_l1_k. intros until mm. intros TI FRM E0 P15.
  pose proof (BART mb mm _ B TI) as ART1. pose proof (tc_call_ok mb mm _ TI) as COK.
  pose proof (nb_checked_dst mb mm _ (NB + sg + n) 16 B TI ltac:(lia) ltac:(lia) ltac:(lia)) as CD.
  pose proof TI as TI0. ti_open TI. ti_envX OK.
  apply evt_done.
  eapply (aevt_memsetP RT RC PMc FDO MST Σ1 K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ xF xfc mm (NB + sg + n) 16 (Z_to_bv 8 48) lo);
    [reflexivity| reflexivity| reflexivity| ul| lia| exact CD| exact ART1| exact MI| exact COK|].
  intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m3 RA3 PR3 BY3.
  rewrite unsigned_lit in RA3, PR3 by ul. pose proof RA3 as (ART3 & _ & _ & _).
  assert (TI3 : TINV J sh_poison m3 m3).
  { eapply (tinv_after_nb RT Σ Σ1 J fN kN OK EF INF NBF mb mm m3 sh_poison (NB + sg + n) 16);
      [exact TI0| reflexivity| exact RA3| exact PR3| exact BY3| rewrite repeat_length; reflexivity| lia| lia]. }
  assert (B3 : BASEJ m0 m3).
  { eapply (base_after_call RT AF Σ Σ1 J fN kN OK EF EL ES INF NBF LOR m0 mb mm m3); [exact B| exact TI0| exact ART3| exact PR3| left; lia]. }
  rewrite (ret_pc_even 0xbe368) by lia.
  apply (aevt_evt RT AF PMc MST).
  eapply (tc_l1b J OK m3 Q e sg n HE HSG HN (BSHPN m3 B3) (KZ m3 B3)); [exact TI3| exact FRM| exact E0| exact P15].
Qed.

Lemma tc_lay2A : forall mb e sg n, BASEJ m0 mb -> (SF_EMIN <= e <= SF_EMAX) -> (0 <= sg <= 1) -> (1 <= n <= 20) ->
  tc_l2_k J mb Q e sg n.
Proof using AF RC RC2 FDO MST OK EF EL ES EC INF NBF LOR HK.
  intros mb e sg n B HE HSG HN. unfold tc_l2_k. intros until mm. intros TI FRM P15.
  pose proof (BART mb mm _ B TI) as ART1. pose proof (tc_call_ok mb mm _ TI) as COK.
  pose proof (nb_checked_dst mb mm _ (NB + sg + (n + e) + 1) 16 B TI ltac:(lia) ltac:(lia) ltac:(lia)) as CD.
  pose proof (nb_checked_src mb mm _ (NB + sg + (n + e)) 16 B TI ltac:(lia) ltac:(lia)) as CS.
  pose proof TI as TI0. ti_open TI. ti_envX OK.
  destruct (nb_bytes mm nb (Z.to_nat (sg + (n + e))) 16 NA NL ltac:(lia)) as [SRC LS].
  replace (NB + Z.of_nat (Z.to_nat (sg + (n + e)))) with (NB + sg + (n + e)) in SRC by lia.
  set (bs := firstn 16 (skipn (Z.to_nat (sg + (n + e))) nb)) in *. clearbody bs.
  apply evt_done.
  eapply (aevt_memmoveP RT RC PMc FDO MST Σ1 K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ xF xfc mm (NB + sg + (n + e) + 1) (NB + sg + (n + e)) bs lo);
    [reflexivity| reflexivity| rewrite LS; reflexivity| ul| ul| rewrite LS; lia| exact SRC| rewrite LS; exact CS| rewrite LS; exact CD| exact ART1| exact MI| exact COK|].
  intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m3 RA3 PR3 BY3.
  rewrite unsigned_lit in RA3, PR3 by ul. rewrite LS in PR3. pose proof RA3 as (ART3 & _ & _ & _).
  assert (TI3 : TINV J sh_poison m3 m3).
  { eapply (tinv_after_nb RT Σ Σ1 J fN kN OK EF INF NBF mb mm m3 sh_poison (NB + sg + (n + e) + 1) 16);
      [exact TI0| reflexivity| exact RA3| exact PR3| exact BY3| rewrite LS; reflexivity| lia| lia]. }
  assert (B3 : BASEJ m0 m3).
  { eapply (base_after_call RT AF Σ Σ1 J fN kN OK EF EL ES INF NBF LOR m0 mb mm m3); [exact B| exact TI0| exact ART3| exact PR3| left; lia]. }
  rewrite (ret_pc_even 0xbe498) by lia.
  apply (aevt_evt RT AF PMc MST).
  eapply (tc_l2b J OK m3 Q e sg n HE HSG HN (BSHPN m3 B3) (KZ m3 B3)); [exact TI3| exact FRM| exact P15].
Qed.

Lemma tc_lay4A : forall mb e sg n, BASEJ m0 mb -> (SF_EMIN <= e <= SF_EMAX) -> (0 <= sg <= 1) -> (1 <= n <= 20) ->
  tc_l4_k J mb Q e sg n.
Proof using AF RC RC2 FDO MST OK EF EL ES EC INF NBF LOR HK.
  intros mb e sg n B HE HSG HN. unfold tc_l4_k. intros until mm. intros TI FRM HN2.
  pose proof (BART mb mm _ B TI) as ART1. pose proof (tc_call_ok mb mm _ TI) as COK.
  pose proof (nb_checked_dst mb mm _ (NB + sg + 2) 16 B TI ltac:(lia) ltac:(lia) ltac:(lia)) as CD.
  pose proof (nb_checked_src mb mm _ (NB + sg + 1) 16 B TI ltac:(lia) ltac:(lia)) as CS.
  pose proof TI as TI0. ti_open TI. ti_envX OK.
  destruct (nb_bytes mm nb (Z.to_nat (sg + 1)) 16 NA NL ltac:(lia)) as [SRC LS].
  replace (NB + Z.of_nat (Z.to_nat (sg + 1))) with (NB + sg + 1) in SRC by lia.
  set (bs := firstn 16 (skipn (Z.to_nat (sg + 1)) nb)) in *. clearbody bs.
  apply evt_done.
  eapply (aevt_memmoveP RT RC PMc FDO MST Σ1 K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ xF xfc mm (NB + sg + 2) (NB + sg + 1) bs lo);
    [reflexivity| reflexivity| rewrite LS; reflexivity| ul| ul| rewrite LS; lia| exact SRC| rewrite LS; exact CS| rewrite LS; exact CD| exact ART1| exact MI| exact COK|].
  intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m3 RA3 PR3 BY3.
  rewrite unsigned_lit in RA3, PR3 by ul. rewrite LS in PR3. pose proof RA3 as (ART3 & _ & _ & _).
  assert (TI3 : TINV J sh_poison m3 m3).
  { eapply (tinv_after_nb RT Σ Σ1 J fN kN OK EF INF NBF mb mm m3 sh_poison (NB + sg + 2) 16);
      [exact TI0| reflexivity| exact RA3| exact PR3| exact BY3| rewrite LS; reflexivity| lia| lia]. }
  assert (B3 : BASEJ m0 m3).
  { eapply (base_after_call RT AF Σ Σ1 J fN kN OK EF EL ES INF NBF LOR m0 mb mm m3); [exact B| exact TI0| exact ART3| exact PR3| left; lia]. }
  rewrite (ret_pc_even 0xbe534) by lia.
  apply (aevt_evt RT AF PMc MST).
  eapply (tc_l4b J OK m3 Q e sg n HE HSG HN (BSHPN m3 B3) (KZ m3 B3)); [exact TI3| exact FRM| exact HN2].
Qed.

Lemma tmp17_facts : forall mb mm shc, BASEJ m0 mb -> TINV J shc mb mm ->
  exists t17, bytes_at asegs mm (spq + 15) t17 /\ length t17 = 17%nat /\ wr_at asegs mm (spq + 15) 17
    /\ checked_src RT Σ1 mm (Z_to_bv 64 spq) lo (spq + 15) 17
    /\ checked_dst RT Σ1 mm (Z_to_bv 64 spq) (spq + 15) 17.
Proof using AF OK EF ES INF NBF LOR.
  intros mb mm shc B TI. pose proof (BART mb mm _ B TI) as ART1. ti_open TI. ti_envX OK.
  pose proof (af_sp0_range RT AF Σ1 mm ART1) as SPR. rewrite ES in SPR.
  destruct (proj1 (num_rw_cells_app asegs mm _ [_; _] _) LOC) as [_ L23]. cbn [cells_size csize Nat.add] in L23.
  destruct (proj1 (num_rw_cells_app asegs mm _ [_] _) L23) as [L2 _].
  replace (q - 128 - ti_d J + Z.of_nat 15) with (q - 128 - ti_d J + 15) in L2 by lia.
  pose proof (rw_cells_bytes_at asegs mm _ _ L2) as BY. cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY.
  assert (LT : length t17 = 17%nat) by (destruct L2 as [[Hwf _] _]; cbn in Hwf; tauto).
  destruct L2 as [_ W2]. cbn [cells_size csize Nat.add] in W2.
  assert (ACC : acc asegs mm (q - 128 - ti_d J + 15) 17).
  { apply (af_acc_stack RT AF Σ1 mm _ 17 ART1); [rewrite ES|]; ul. }
  exists t17. split; [exact BY|]. split; [exact LT|]. split; [exact W2|]. split.
  - unfold checked_src. rewrite unsigned_lit by ul. split; [| right; lia]. intros _. split; [exact ACC|].
    right; right; left. rewrite ES. ul.
  - unfold checked_dst. rewrite unsigned_lit by ul. split; [| split; [| exact W2]].
    + intros _. split; [exact ACC|]. right; right; left. rewrite ES. ul.
    + intros i Hi. left. ul.
Qed.

Lemma tc_lay3cA : forall mb e sg n, BASEJ m0 mb -> (SF_EMIN <= e <= SF_EMAX) -> (0 <= sg <= 1) -> (1 <= n <= 20) ->
  tc_l3c_k J mb Q e sg n.
Proof using AF RC RC2 FDO MST OK EF EL ES EC INF NBF LOR HK.
  intros mb e sg n B HE HSG HN. unfold tc_l3c_k. intros until mm. intros TI FRM P3.
  pose proof (BART mb mm _ B TI) as ART1. pose proof (tc_call_ok mb mm _ TI) as COK.
  pose proof (nb_checked_dst mb mm _ (NB + sg + 2 - (n + e)) 17 B TI ltac:(lia) ltac:(lia) ltac:(lia)) as CD.
  destruct (tmp17_facts mb mm _ B TI) as (t17 & SRC & LS & _ & CS & _).
  pose proof TI as TI0. ti_open TI. ti_envX OK.
  apply evt_done.
  eapply (aevt_memcpyP RT RC PMc FDO MST Σ1 K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ xF xfc mm (NB + sg + 2 - (n + e)) (q - 128 - ti_d J + 15) t17 lo);
    [reflexivity| reflexivity| rewrite LS; reflexivity| ul| ul| rewrite LS; lia| exact SRC| rewrite LS; exact CS| rewrite LS; exact CD| rewrite LS; left; lia
    | exact ART1| exact MI| exact COK|].
  intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m3 RA3 PR3 BY3.
  rewrite unsigned_lit in RA3, PR3 by ul. rewrite LS in PR3. pose proof RA3 as (ART3 & _ & _ & _).
  assert (TI3 : TINV J sh_poison m3 m3).
  { eapply (tinv_after_nb RT Σ Σ1 J fN kN OK EF INF NBF mb mm m3 sh_poison (NB + sg + 2 - (n + e)) 17);
      [exact TI0| reflexivity| exact RA3| exact PR3| exact BY3| rewrite LS; reflexivity| lia| lia]. }
  assert (B3 : BASEJ m0 m3).
  { eapply (base_after_call RT AF Σ Σ1 J fN kN OK EF EL ES INF NBF LOR m0 mb mm m3); [exact B| exact TI0| exact ART3| exact PR3| left; lia]. }
  rewrite (ret_pc_even 0xbe464) by lia.
  apply (aevt_evt RT AF PMc MST).
  eapply (tc_l3c J OK m3 Q e sg n HE HSG HN (BSHPN m3 B3) (KZ m3 B3)); [exact TI3| exact FRM| exact P3].
Qed.

Lemma tc_lay3A : forall mb e sg n, BASEJ m0 mb -> (SF_EMIN <= e <= SF_EMAX) -> (0 <= sg <= 1) -> (1 <= n <= 20) ->
  tc_l3_k J mb Q e sg n.
Proof using AF RC RC2 FDO MST OK EF EL ES EC INF NBF LOR HK.
  intros mb e sg n B HE HSG HN. unfold tc_l3_k. intros until mm. intros TI FRM P3.
  pose proof (BART mb mm _ B TI) as ART1. pose proof (tc_call_ok mb mm _ TI) as COK.
  pose proof (nb_checked_src mb mm _ (NB + sg) 17 B TI ltac:(lia) ltac:(lia)) as CS.
  destruct (tmp17_facts mb mm _ B TI) as (t17 & _ & _ & _ & _ & CD).
  pose proof TI as TI0. ti_open TI. ti_envX OK.
  destruct (nb_bytes mm nb (Z.to_nat sg) 17 NA NL ltac:(lia)) as [SRC LS].
  replace (NB + Z.of_nat (Z.to_nat sg)) with (NB + sg) in SRC by lia.
  set (bs := firstn 17 (skipn (Z.to_nat sg) nb)) in *. clearbody bs.
  apply evt_done.
  eapply (aevt_memcpyP RT RC PMc FDO MST Σ1 K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ xF xfc mm (q - 128 - ti_d J + 15) (NB + sg) bs lo);
    [reflexivity| reflexivity| rewrite LS; reflexivity| ul| ul| rewrite LS; lia| exact SRC| rewrite LS; exact CS| rewrite LS; exact CD| rewrite LS; right; lia
    | exact ART1| exact MI| exact COK|].
  intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m3 RA3 PR3 BY3.
  rewrite unsigned_lit in RA3, PR3 by ul. rewrite LS in PR3. pose proof RA3 as (ART3 & _ & _ & _).
  assert (TI3 : TINV J sh_poison m3 m3).
  { eapply (tinv_after_tmp RT Σ Σ1 J fN kN OK EF INF NBF mb mm m3 sh_poison bs); [exact TI0| reflexivity| exact RA3| exact PR3| exact BY3| exact LS]. }
  assert (B3 : BASEJ m0 m3).
  { eapply (base_after_call RT AF Σ Σ1 J fN kN OK EF EL ES INF NBF LOR m0 mb mm m3); [exact B| exact TI0| exact ART3| exact PR3| right; split; reflexivity]. }
  rewrite (ret_pc_even 0xbe3e0) by lia.
  apply (aevt_evt RT AF PMc MST).
  eapply (tc_l3b J OK m3 Q e sg n HE HSG HN (BSHPN m3 B3) (tc_lay3cA m3 e sg n B3 HE HSG HN)); [exact TI3| exact FRM| exact P3].
Qed.

Lemma tc_copyA : forall mb e sg, BASEJ m0 mb -> (SF_EMIN <= e <= SF_EMAX) -> (0 <= sg <= 1) -> tc_copy_k J mb Q e sg.
Proof using AF RC RC2 FDO MST OK EF EL ES EC INF NBF LOR HK.
  intros mb e sg B HE HSG. unfold tc_copy_k. intros until mm. intros TI FRM HN.
  pose proof (BART mb mm _ B TI) as ART1. pose proof (tc_call_ok mb mm _ TI) as COK.
  pose proof (nb_checked_dst mb mm _ (NB + sg) 16 B TI ltac:(lia) ltac:(lia) ltac:(lia)) as CD.
  pose proof (sh_zero_zc J _ ltac:(destruct TI as (_ & _ & _ & _ & SHx & _); exact SHx)) as ZC.
  pose proof (inF1 RT Σ Σ1 J EF) as IN1.
  pose proof TI as TI0. ti_open TI. ti_envX OK. pose proof (tc_f8 J OK) as F8.
  pose proof (bytes_at_sub asegs mm (f + 32) tmp (Z.to_nat (24 - n)) 16 (proj1 TA) ltac:(rewrite TL; lia)) as SRC.
  replace (f + 32 + Z.of_nat (Z.to_nat (24 - n))) with (f + 56 - n) in SRC by lia.
  assert (LS : length (firstn 16 (skipn (Z.to_nat (24 - n)) tmp)) = 16%nat) by (rewrite length_firstn, length_skipn, TL; lia).
  set (bs := firstn 16 (skipn (Z.to_nat (24 - n)) tmp)) in *. clearbody bs.
  assert (CS : checked_src RT Σ1 mm (Z_to_bv 64 spq) lo (f + 56 - n) 16).
  { unfold checked_src. rewrite unsigned_lit by ul. split; [| left; unfold ti_spq; lia]. intros _. split.
    - apply (acc_sub asegs mm (f + 32) 40); [| lia| lia]. change 40 with (8 * Z.of_nat 5). apply acc_zero_run; [clear - F8; Z.div_mod_to_equations; lia| lia|].
      unfold shad, SHB. replace ((f + 32) / 8 + 2147450880) with (f / 8 + 2147450884) by (clear - F8; Z.div_mod_to_equations; lia).
      exact (zero_run_of_CB mm _ 5 ZC).
    - right; left. exists (ti_f J), 1%nat. split; [exact IN1| rewrite fs1; lia]. }
  apply evt_done.
  eapply (aevt_memcpyP RT RC PMc FDO MST Σ1 K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ xF xfc mm (NB + sg) (f + 56 - n) bs lo);
    [reflexivity| reflexivity| rewrite LS; reflexivity| ul| ul| rewrite LS; lia| exact SRC| rewrite LS; exact CS| rewrite LS; exact CD| rewrite LS; clear - Cnbf HSG HN; lia
    | exact ART1| exact MI| exact COK|].
  intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m3 RA3 PR3 BY3.
  rewrite unsigned_lit in RA3, PR3 by ul. rewrite LS in PR3. pose proof RA3 as (ART3 & _ & _ & _).
  assert (TI3 : TINV J sh_zero m3 m3).
  { eapply (tinv_after_nb RT Σ Σ1 J fN kN OK EF INF NBF mb mm m3 sh_zero (NB + sg) 16);
      [exact TI0| reflexivity| exact RA3| exact PR3| exact BY3| rewrite LS; reflexivity| lia| lia]. }
  assert (B3 : BASEJ m0 m3).
  { eapply (base_after_call RT AF Σ Σ1 J fN kN OK EF EL ES INF NBF LOR m0 mb mm m3); [exact B| exact TI0| exact ART3| exact PR3| left; lia]. }
  rewrite (ret_pc_even 0xbe2f8) by lia.
  apply (aevt_evt RT AF PMc MST).
  eapply (tc_c0 J OK m3 Q e sg n HE HSG HN (BSHPN m3 B3) (KZ m3 B3)
            (tc_lay1A m3 e sg n B3 HE HSG HN) (tc_lay2A m3 e sg n B3 HE HSG HN) (tc_lay3A m3 e sg n B3 HE HSG HN) (tc_lay4A m3 e sg n B3 HE HSG HN));
    [exact TI3| exact FRM].
Qed.

Lemma tc_kernA : forall mb, BASEJ m0 mb -> tc_kern_k J mb Q.
Proof using AF RC RC2 FDO MST OK EF EL ES EC INF NBF LOR HK.
  intros mb B. unfold tc_kern_k. intros until mm. intros TI FRM HEX HSG.
  pose proof (BART mb mm _ B TI) as ART1.
  pose proof TI as TI0. ti_open TI. ti_envX OK.
  eapply evt_cut.
  { eapply (sf_okA RT AF Σ1); [exact ART1| exact MI| exact HEX| exact ST| lia| rewrite ES; lia| ul]. }
  cbv beta. intros ms' (m' & PO & MUk & WMk & MIk & STk & ARTk). unfold sf_postA1 in PO.
  destruct PO as (y0 & y1 & y2 & b0 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & e & -> & HE).
  rewrite (ret_pc_even 0xbe140) by lia.
  assert (TI' : TINV J sh_poison m' m') by (eapply (tinv_rebase_k J OK mb mm m' sh_poison TI0 eq_refl MUk WMk MIk STk)).
  assert (B' : BASEJ m0 m') by (exact (base_rebase_k RT AF Σ Σ1 J OK EF EL ES LOR m0 mb mm m' sh_poison B TI0 MUk ARTk)).
  eapply (tc_dig J OK m' Q e sg (BSHPN m' B') (base_shpd RT AF Σ Σ1 J fN kN OK EF ES INF NBF LOR m0 m' B') (tc_copyA m' e sg B' HE HSG));
    [exact TI'| exact FRM].
Qed.
End Calls.

Local Ltac ul0 := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, PJ_TC_STACK_A in *; lia.

Theorem tochars_okA : tochars_cpsA RT PMc.
Proof using AF RC RC2.
  unfold tochars_cpsA.
  intros Σ K NB q lo fN kN ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m junk
         FDO MST INF FLE FHI NB8 NBC NBSH ART0 MI ST LOR ROOM QT Q16 FRM FRT CR HK.
  pose proof (af_sp0_range RT AF Σ m ART0) as SPR. pose proof (af_sp0_win RT AF Σ m ART0) as SPW.
  pose proof (af_frames_range RT AF Σ m fN kN ART0 INF) as (FN0 & FN1 & _ & _).
  pose proof (af_frames_align RT AF Σ m fN kN ART0 INF) as (_ & FNLO).
  pose proof (proj2 (af_fshadow_apart RT AF Σ m fN kN ART0 INF) fN kN INF) as FNSH.
  assert (FSZ : 0 <= fs_size kN) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  unfold PJ_TC_STACK_A, RT_STACK in ROOM.

  apply (aevt_evt RT AF PMc MST).
  eapply (tc_pro ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc q lo NB m ltac:(lia) ltac:(ul0) Q16 ltac:(ul0) (fun ms => aevt RT PMc Σ K ms));
    [| exact MI| exact ST| exact (af_client_consts RT AF Σ m ART0)].
  unfold tc_call1_k. intros d xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF jl m1 Hd LOC SAVED MI1 MU1 WM1 ST1.
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 (q - 128 - d) ART0 ltac:(ul0)); [| exact WM1].
    intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. left. ul0. }
  apply evt_done.

  eapply (aevt_smalloc1 RT PMc FDO MST RC2 Σ K); [reflexivity| unfold FRAMES_MAX2, FRAMES_TOT in *; lia| lia| exact ART1| exact MI1| | intros HN; exfalso; rewrite HN in INF; exact INF|].
  { unfold call_ok. rewrite unsigned_lit by ul0. split; [exact ST1|]. split; [ul0|]. split; [ul0|]. split; [ul0|].
    destruct Hd as [-> | ->]; clear - Q16; Z.div_mod_to_equations; lia. }
  intros Σ1 f xt0' xt1' xt2' xa1' xa2' xa3' xa4' xa5' xa6' xa7' xt3' xt4' xt5' xt6' xF' m2 (ART2 & MI2 & WM2 & ST2) PR2 W1 W2 EF EL ES EC F0 F64 FTOP.
  rewrite unsigned_lit in ST2, PR2 by ul0. rewrite (ret_pc_even 0xbdfc8) by lia.
  rewrite fs1 in W1, W2, FTOP. change (128 - 8) with 120 in W1. change (128 / 8) with 16 in W2.

  assert (IN1 : In (f, 1%nat) (rt_frames RT Σ1)) by (rewrite EF; left; reflexivity).
  pose proof (af_frames_range RT AF Σ1 m2 f 1%nat ART2 IN1) as (_ & FR1 & _ & _). rewrite fs1, ES in FR1.
  pose proof (af_frames_align RT AF Σ1 m2 f 1%nat ART2 IN1) as (_ & FLO).
  pose proof (proj2 (af_fshadow_apart RT AF Σ1 m2 f 1%nat ART2 IN1) f 1%nat IN1) as FSH. rewrite fs1s, fs1 in FSH.
  pose proof (frames_sep RT AF Σ1 m2 f 1%nat (rt_frames RT Σ) NB 40 ART2 EF NB8 ltac:(lia) eq_refl ltac:(exists fN, kN; split; [exact INF| lia])) as SEP.
  cbv zeta in SEP. rewrite fs1 in SEP. change (128 / 8) with 16 in SEP. change (40 / 8) with 5 in SEP. destruct SEP as (SP1 & SP2 & SP3 & SP4).
  set (J := mkTI q d NB lo f ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (reg_get F 8)).
  assert (OK : tc_ok J).
  { subst J. constructor; cbn [ti_q ti_d ti_NB ti_lo ti_f ti_spq ti_S]; unfold ti_S; cbn [ti_f]; unfold shad, SHB in *.
    - exact Hd.
    - ul0.
    - lia.
    - ul0.
    - exact NB8.
    - ul0.
    - lia.
    - exact F64.
    - ul0.
    - lia.
    - lia.
    - assert ((f + 128) / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; [lia| ul0]). ul0.
    - lia.
    - lia.
    - lia.
    - lia.
    - assert ((NB + 40) / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; [lia| ul0]).
      pose proof (Z.div_le_mono NB (NB + 40) 8 ltac:(lia) ltac:(lia)). ul0.
    - pose proof (Z.div_le_mono fN NB 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono (NB + 48) (fN + fs_size kN) 8 ltac:(lia) ltac:(lia)).
      destruct FNSH as [HS|HS]; [left| right]; Z.div_mod_to_equations; lia.
    - exact Q16. }

  assert (IN2 : In (fN, kN) (rt_frames RT Σ)) by exact INF.
  assert (AG2 : forall P : Z -> Prop,
    (forall x, P x -> (q - 128 - d <= x < q) \/ (NB <= x < NB + 40) \/ (NB / 8 + 2147450880 <= x < NB / 8 + 2147450880 + 5)) -> agree_on P m1 m2).
  { intros P HP a Ha. apply PR2. destruct (HP _ Ha) as [H|[H|H]].
    - left. ul0.
    - right; right; right; left. exists fN, kN. split; [exact IN2| lia].
    - right; right; right; right. exists fN, kN. split; [exact IN2|].
      pose proof (Z.div_le_mono fN NB 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono (NB + 48) (fN + fs_size kN) 8 ltac:(lia) ltac:(lia)).
      unfold shad, SHB. Z.div_mod_to_equations. lia. }
  assert (AG1 : forall P : Z -> Prop, (forall x, P x -> ~ (q - 128 - d <= x < q)) -> agree_on P m m1).
  { intros P HP a Ha. apply MU1. cbn [outside]. split; [| exact I]. apply HP. exact Ha. }
  pose proof (rw_cells_agree asegs m1 m2 _ _ LOC ltac:(apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; left; destruct Hd as [Ed|Ed]; rewrite Ed in Hx |- *; cbn in Hx; lia) WM2) as LOC2.
  pose proof (rw_cells_agree asegs m1 m2 _ _ SAVED ltac:(apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; left; lia) WM2) as SAVED2.
  pose proof (rw_cells_agree asegs m m1 _ _ NBC ltac:(apply AG1; intros x Hx; cbn [cells_size csize Nat.add] in Hx; ul0) WM1) as NBC1.
  pose proof (rw_cells_agree asegs m1 m2 _ _ NBC1 ltac:(apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; right; left; lia) WM2) as NBC2.
  pose proof (bytes_at_agree asegs m m1 _ _ NBSH ltac:(apply AG1; intros x Hx; rewrite repeat_length in Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx;
                assert ((NB + 40) / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; [lia| ul0]); unfold shad, SHB in Hx; ul0)) as NBSH1.
  pose proof (bytes_at_agree asegs m1 m2 _ _ NBSH1 ltac:(apply AG2; intros x Hx; rewrite repeat_length in Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx;
                unfold shad, SHB in Hx; right; right; lia)) as NBSH2.

  destruct (wr_at_rw_CB m2 f 120 W1 ltac:(lia)) as [jf FRAME]. destruct (wr_at_rw_CB m2 _ 16 W2 ltac:(lia)) as [js SHJ].
  change (Z.to_nat 120) with 120%nat in FRAME. change (Z.to_nat 16) with 16%nat in SHJ.

  assert (B2 : BASE RT Σ Σ1 J m m2).
  { split; [exact ART2|]. split; [| exact NBSH2].
    intros a Ha Ho. cbn [outside] in Ho. rewrite (PR2 a), (MU1 a); [reflexivity| |].
    - cbn [outside]. split; [| exact I]. subst J. cbn [ti_q ti_NB] in Ha, Ho. destruct (aclient_split_c RT AF Σ m q (bv_unsigned a) ART0 Ha); ul0.
    - subst J. cbn [ti_q ti_NB] in Ha, Ho |- *. eapply aclient_mono; [exact Ha| auto| auto| lia]. }

  apply (aevt_evt RT AF PMc MST).
  eapply (tc_hdr J OK m2 (fun ms => aevt RT PMc Σ1 K ms)
            (tc_finA RT AF PMc MST Σ Σ1 J fN kN OK EF EL ES INF ltac:(subst J; cbn [ti_NB]; lia) LOR K m HK EC m2 B2)
            (tc_kernA FDO MST Σ Σ1 J fN kN K m OK EF EL ES EC INF ltac:(subst J; cbn [ti_NB]; lia) LOR HK m2 B2)
            (base_shpn RT Σ Σ1 J OK m m2 B2));
    [exact FRM| exact LOC2| exact SAVED2| exact FRAME| exact SHJ| exact NBC2| exact MI2| exact ST2].
Qed.
End TC.
