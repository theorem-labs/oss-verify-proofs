(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage1 SjStage1Out.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_stage1_kit Sj_h_arith.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_hkit2 Sj_stage1_defs Sj_stage1 Sj_stage2_iface Sj_h_layout. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_hkit3A. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_h_parsew. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_parseA Atp_pid_s1zA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section Parse0CPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis S1Z : stage1z_cps RT.

Local Ltac ul := unfold PARSE_STACK, S2A_STACK, Sj_num_iface.NUMA_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Definition parse0_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z)
         (THIS DOC IDX BUF TAPE SBUF OC IA : Z) (ws0 : list word) (tcap scap : Z)
         (vptr capv nsi nxt bufv lenv docv : word) (p12 p28 p50 : list byte),
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 THIS -> a1 = Z_to_bv 64 BUF -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 DOC -> tp = Z_to_bv 64 0x6a7e68 -> frm0 fc ->
  0 <= BUF < 2^64 ->
  4 <= Z.of_nat (length ws0) -> Z.of_nat (length ws0) < 2^40 ->
  ART RT Σ m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + PARSE_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  In (THIS, 96) (rt_live RT Σ) -> In (IDX, 4 * Z.of_nat (length ws0)) (rt_live RT Σ) ->
  THIS mod 8 = 0 -> IDX mod 8 = 0 ->
  (THIS + 96 <= IDX \/ IDX + 4 * Z.of_nat (length ws0) <= THIS) ->
  rw_cells asegs m THIS (impl16 vptr nsi p12 (Z_to_bv 64 IDX) nxt p28 capv (Z_to_bv 64 1024) (Z_to_bv 8 0) (Z_to_bv 8 0) p50
                                (Z_to_bv 64 OC) (Z_to_bv 64 IA) bufv lenv docv) ->
  u32arr asegs m IDX ws0 ->
  cps_f
    (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                 t3 t4 t5 t6 F fc e_parse m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m' (v : word),
           ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
         /\ bv_unsigned v = 13
         /\ s2a_okres TAPE SBUF tcap scap v m'
         /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
         /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (parse_X THIS IDX TAPE SBUF OC IA (Z.of_nat (length ws0)) tcap scap) m m'
         /\ (exists nsi' nxt' bufv' lenv' docv',
               rw_cells asegs m' THIS (impl16 vptr nsi' p12 (Z_to_bv 64 IDX) nxt' p28 capv (Z_to_bv 64 1024) (Z_to_bv 8 0) (Z_to_bv 8 0) p50
                                              (Z_to_bv 64 OC) (Z_to_bv 64 IA) bufv' lenv' docv'))) c
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_live RT Σ' = rt_live RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ <= rt_credit RT Σ').

Theorem parse0_ok : parse0_cps.
Proof using AF S1Z.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    THIS DOC IDX BUF TAPE SBUF OC IA ws0 tcap scap vptr capv nsi nxt bufv lenv docv p12 p28 p50
    FDO MST -> -> -> -> -> FRM BUFR ICAP ICAPH ART0 MI0 ST0 LOW LOR SPT SPA INT INI T8 I8 DTI THISC ARR.
  intros T c (Hc & FC0) Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).

  pose proof (af_live_range RT AF Σ m THIS 96 ART0 INT) as (TH0 & TH1 & _).
  pose proof (af_live_range RT AF Σ m IDX _ ART0 INI) as (IX0 & IX1 & _).
  assert (FP1 : fp_client RT Σ lo [(usp - 32, usp)]) by (constructor; [left; cbn [fst snd]; ul| constructor]).

  pose proof (pa_walk1 usp lo ra gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 s0 s1 (Z_to_bv 64 THIS) (Z_to_bv 64 BUF) (Z_to_bv 64 0) (Z_to_bv 64 DOC)
                a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ST0 ltac:(ul) ltac:(ul) ltac:(ul) MI0) as W1.
  rewrite <- ESP in W1.
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & j & -> & MU1 & WM1 & MI1 & ST1 & FR1) & Hc1'). clear Hc1.
  pose proof (art_fp_client RT AF Σ m m1 lo _ ART0 LOW FP1 MU1 WM1) as ART1.
  assert (AG1 : agree_on (fun x => x < usp - 32) m m1).
  { apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn [outside]. split; [lia| exact I]. }

  assert (THISC1 := THISC). apply (rw_cells_agree asegs m m1 _ _) in THISC1; [| eapply agree_sub; [exact AG1|]; intros x Hx; unfold impl16 in Hx; cbn [cells_size csize Nat.add] in Hx; cbv beta; ul| exact WM1].
  assert (ARR1 : u32arr asegs m1 IDX ws0) by (apply (u32arr_agree m m1 _ _ ARR); [eapply agree_sub; [exact AG1|]; intros x Hx; cbv beta in *; ul| exact WM1]).
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -32)) = usp + -32) by (apply unsigned_lit; ul).
  assert (SPA2 : (usp + -32) mod 16 = 0) by (replace (usp + -32) with (usp + (-2) * 16) by lia; rewrite Z.mod_add by lia; exact SPA).

  apply impl16_s1 in THISC1.
  set (MID := mid16 p28 capv (Z_to_bv 64 1024) (Z_to_bv 8 0) (Z_to_bv 8 0) p50 (Z_to_bv 64 OC) (Z_to_bv 64 IA)) in *.
  set (E := mkS1Env (Z_to_bv 64 0xe2cfc) (Z_to_bv 64 (usp + -32)) gp (Z_to_bv 64 0x6a7e68) (Z_to_bv 64 DOC) (Z_to_bv 64 THIS)
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo THIS BUF IDX [] (length ws0) vptr p12 MID (le8 docv) m1).
  assert (OK : env_okz E).
  { unfold E. constructor; cbn [e_bs e_lo e_sp e_THIS e_IDX e_BUF e_cap]; unfold A1_GTOP, A1_STACK; rewrite ?EU2; try reflexivity.
    all: clear - LOW LOR TH0 TH1 IX0 IX1 ICAP DTI SP0R SP0W; ul. }
  assert (LV : a1z_live RT Σ E).
  { unfold a1z_live, E. cbn [e_THIS e_IDX e_cap e_bs blen length Z.of_nat]. split; [exact INT|]. split; [exact INI|].
    split; [exact T8|]. split; [exact I8|]. unfold blen. cbn [length Z.of_nat]. clear - ICAP. lia. }
  apply (S1Z Σ PMc E t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 nsi nxt bufv lenv ws0 FDO MST OK LV);
    [.. | split; [| apply (cfrm0_of_asta RT Σ PMc (eq _) c1 Hc1'); intros ms0 <-; exact FRM] |].
  - exact LOW.
  - cbn [E e_lo e_sp]. rewrite EU2. ul.
  - cbn [E e_sp]. rewrite EU2. ul.
  - cbn [E e_sp]. rewrite EU2. exact SPA2.
  - exact ART1.
  - exact MI1.
  - cbn [E e_m0 e_lo e_sp]. rewrite EU2. exact ST1.
  - exact THISC1.
  - exact ARR1.
  - reflexivity.
  - exact FRM.
  -
    eapply ASTA_conseq; [exact Hc1'|]. intros ms <-. cbv delta [E mkR e_ra e_sp e_gp e_tp e_s0 e_s1 e_s2 e_s3 e_s4 e_s5 e_s6 e_s7 e_s8 e_s9 e_s10 e_s11 e_F e_fc e_m0 e_THIS e_BUF e_bs entry_st blen length Z.of_nat]. reflexivity.
  - intros c2 (Hc2 & FC2).
    destruct (ASTA_unpack_f RT Σ _ _ c2 Hc2 FC2) as (ms2 & (m2 & RS2 & FRM2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & RES2) & _ & Hc2'). clear Hc2.
    cbn [E e_ra e_sp e_gp e_tp e_s0 e_s1 e_s2 e_s3 e_s4 e_s5 e_s6 e_s7 e_s8 e_s9 e_s10 e_s11 e_lo e_m0 e_bs] in RS2, ST2, PRES2, RES2.
    rewrite EU2 in ST2, PRES2.
    destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
    cbn [ms_fcsr] in FRM2. rewrite (ret_pc_even 0xe2cfc) in Hc2' by lia.
    destruct RES2 as (ws' & nxt' & THISC2 & ARR2 & LWS2 & FIRSTN).
    unfold parser_cells in THISC2. cbn [E e_THIS e_IDX e_BUF e_bs e_cap e_vptr e_p12 e_mid e_docj blen length Z.of_nat] in THISC2, ARR2, LWS2.
    unfold a1_FP in PRES2. cbn [E e_THIS e_IDX e_cap] in PRES2.
    destruct (impl16_wf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ THISC) as (L12 & L28 & L50).
    apply (s1_impl16 m2 THIS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L28 L50) in THISC2.

    assert (FR2 : rw_cells asegs m2 (usp + -32) [CB 8 j; C8 s1; C8 s0; C8 ra]).
    { apply (rw_cells_agree asegs m1 m2 _ _ FR1); [| exact WM2]. apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES2).
      intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; ul|]. cbn [outside]. split; [ul|]. split; [ul| exact I]. }

    pose proof (pa_walk3 usp lo 13 j gp (Z_to_bv 64 0x6a7e68) u0 u1 u2 (Z_to_bv 64 DOC) (Z_to_bv 64 THIS) b1 b2 b3 b4 b5 b6 b7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 ra s0 s1 F2 fc2 m2 ST2 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(lia) FR2 MI2) as W3.
    lazymatch type of W3 with evt asegs _ ?X =>
      assert (W3' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W3) end.
    clear W3.
    apply (cps_realizes asegs _ _ _ c2 (asta_evt_c RT AF Σ PMc _ _ MST W3') Hc2'). clear W3'. intros c3 Hc3.
    apply Hk. split; [| apply (cfrm0_of_asta RT Σ PMc _ c3 Hc3); intros ms (m3 & _ & E3 & _); rewrite E3; exact FRM2].
    exists Σ. split; [| split; [reflexivity| split; [reflexivity| split; [reflexivity| lia]]]].
    eapply ASTA_conseq; [exact Hc3|]. intros ms (m3 & RS3 & _ & MU3 & WM3 & MI3 & ST3). exists m3, (Z_to_bv 64 13).
    split; [rewrite ESP; exact RS3|].
    split; [apply unsigned_lit; lia|].
    split; [left; rewrite unsigned_lit by lia; lia|].
    split; [split; [exact (art_fp_client RT AF Σ m2 m3 lo _ ART2 LOW FP1 MU3 WM3)| split; [exact MI3| exact ST3]]|].
    split.
    * intros a Ha Hout. unfold parse_X in Hout. cbn [outside] in Hout. destruct Hout as (HO1 & HO2 & _).
      pose proof (aclient_split_c RT AF Σ m usp (bv_unsigned a) ART0 Ha) as SPL.
      rewrite (MU3 a), (PRES2 a), (MU1 a); [reflexivity| | | |].
      -- cbn [outside]. split; [clear - SPL LOW LOR; ul| exact I].
      -- apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| lia].
      -- cbn [outside]. split; [exact HO1|]. split; [exact HO2| exact I].
      -- cbn [outside]. split; [clear - SPL LOW LOR; ul| exact I].
    * exists (Z_to_bv 64 0), nxt', (Z_to_bv 64 BUF), (Z_to_bv 64 0), docv.
      apply (rw_cells_agree asegs m2 m3 _ _ THISC2); [| exact WM3]. apply (agree_of_munch _ _ _ _ MU3).
      intros x Hx. unfold impl16 in Hx. cbn [cells_size csize Nat.add] in Hx. cbn [outside]. split; [ul| exact I].
Qed.

End Parse0CPS.
