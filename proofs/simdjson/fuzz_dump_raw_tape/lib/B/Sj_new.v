(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Str_tac.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition e_new_nt : Z := 0x10af80.
Definition e_newarr_nt : Z := 0x10afb4.
Definition e_delarr : Z := 0x10aff0.
Definition e_del : Z := 0x10afec.

Definition new_frame (s0 ra : word) (ra1 : Z) (j : list byte) : list cell := [C8 s0; C8 (Z_to_bv 64 ra1); CB 8 j; C8 ra].

Definition new_mid (usp n ra1 lo : Z) (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop := fun ms =>
  exists (m1 : mem) (j : list byte),
    ms = entry_st (Z_to_bv 64 0x167864) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 n) s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_malloc m1
    /\ munch [(usp - 32, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -32)
    /\ rw_cells bsegs m1 (usp + -32) (new_frame s0 ra ra1 j).

Lemma new_walkA : forall (usp n lo : Z) (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 32 -> usp < 2^63 -> 1 <= n < 2^63 -> mem_inv bsegs m ->
  evt bsegs (new_mid usp n 0x10af8c lo ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_new_nt m).
Proof.
  intros until m. intros ST LO SPH N MI.
  unfold entry_st, e_new_nt, e_malloc, new_mid, new_frame.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 32, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  zstep. zstep. zstep. lstep. zstep. zstep.
  zstep. zstep. zstep.
  replace (Z.b2z (n <? 1)) with 0 by (destruct (Z.ltb_spec n 1); [lia| reflexivity]). rewrite Z.add_0_r.
  apply evt_done. do 2 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST| exact FR].
Qed.

Lemma newarr_walkA : forall (usp n lo : Z) (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 32 -> usp < 2^63 -> 1 <= n < 2^63 -> mem_inv bsegs m ->
  evt bsegs (new_mid usp n 0x10afc0 lo ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_newarr_nt m).
Proof.
  intros until m. intros ST LO SPH N MI.
  unfold entry_st, e_newarr_nt, e_malloc, new_mid, new_frame.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 32, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  zstep. zstep. zstep. zstep. lstep. zstep. zstep.
  zstep. zstep. zstep.
  replace (Z.b2z (n <? 1)) with 0 by (destruct (Z.ltb_spec n 1); [lia| reflexivity]). rewrite Z.add_0_r.
  apply evt_done. do 2 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST| exact FR].
Qed.

Lemma new_walkB : forall (usp p ra1 lo : Z) (gp tp t0 t1 t2 s0x s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s0c rac : word)
    (j : list byte) F fc (m : mem),
  ra1 = 0x10af8c \/ ra1 = 0x10afc0 ->
  stk bsegs m lo (usp + -32) -> lo <= usp - 32 -> usp < 2^63 -> 0 < p < 2^64 ->
  rw_cells bsegs m (usp + -32) (new_frame s0c rac ra1 j) -> mem_inv bsegs m ->
  evt bsegs (fun ms => ret_st rac (Z_to_bv 64 usp) gp tp s0c s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) m ms /\ ms_fcsr ms = fc /\ stk bsegs m lo usp)
    (MS (mkR (Z_to_bv 64 0x167864) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 s0x s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x167864) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros RA1 ST LO SPH P FR MI.
  unfold new_frame in FR. pose proof ST as (STa & STb & _).
  destruct RA1 as [-> | ->];
    (zstep; if_cases K; zify_cond K; [| exfalso; lia];
     zstep; zstep; zstep; zstep; zstep; zstep;
     release_frame FR ST usp;
     zstep;
     apply evt_done; split; [unfold ret_st; do 16 eexists; reflexivity| split; [reflexivity| exact ST]]).
Qed.

Section NewCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis MAL : malloc_contract_f RT.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Definition new_cps (entry : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (n lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  1 <= n <= 0x20001000 -> a0 = Z_to_bv 64 n -> tp = Z_to_bv 64 0x6abde8 ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost n <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + 32 + RT_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> frm0 fc ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc entry m)))
            (malloc_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 n lo m).

Lemma new_gen : forall (entry ra1 : Z),
  ra1 = 0x10af8c \/ ra1 = 0x10afc0 ->
  (forall (usp n lo : Z) (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
     stk bsegs m lo usp -> lo <= usp - 32 -> usp < 2^63 -> 1 <= n < 2^63 -> mem_inv bsegs m ->
     evt bsegs (new_mid usp n ra1 lo ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
       (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc entry m)) ->
  new_cps entry.
Proof using AF MAL.
  intros entry ra1 RA1 WA Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n lo
    FDO MST N -> -> LV CR ART0 MI0 ST0 LOW LOR SPT SPA FRM.
  intros T c (Hc & FC0) Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (WA usp n lo ra gp (Z_to_bv 64 0x6abde8) t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                ST0 ltac:(ul) ltac:(ul) ltac:(lia) MI0) as W1.
  rewrite <- ESP in W1.
  lazymatch type of W1 with evt bsegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & j & -> & MU1 & WM1 & MI1 & ST1 & FR1) & Hc1'). clear Hc1.
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 (usp - 32) ART0 ltac:(ul)); [| exact WM1].
    intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. left. ul. }
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -32)) = usp + -32) by (apply unsigned_lit; ul).
  apply (MAL Σ PMc (Z_to_bv 64 0x167864) (Z_to_bv 64 (usp + -32)) gp (Z_to_bv 64 0x6abde8) t0 t1 t2 (Z_to_bv 64 n) s1 (Z_to_bv 64 n)
           a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 n lo FDO MST N); try reflexivity; try assumption;
    [.. | split; [exact Hc1'| apply (cfrm0_of_asta RT Σ PMc (eq _) c1 Hc1'); intros ms0 <-; exact FRM] |].
  - unfold call_ok. rewrite EU2. split; [exact ST1|]. split; [ul|]. split; [ul|]. split; [ul|].
    replace (usp + -32) with (usp + (-2) * 16) by lia. rewrite Z.mod_add by lia. exact SPA.
  - unfold unwind_ok. rewrite EU2, unsigned_lit by ul. left. ul.
  - intros c2 ((Σ1 & p & Hc2 & LV1 & FRS1 & SP1 & CR1 & P0 & P16 & PTOP) & FC2).
    destruct (ASTA_unpack_f RT Σ1 _ _ c2 Hc2 FC2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WR2 & ACC2) & FRM2 & Hc2'). clear Hc2.
    destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
    cbn [ms_fcsr] in FRM2. rewrite EU2 in ST2, PRES2.
    rewrite (ret_pc_even 0x167864) in Hc2' by lia.
    assert (FR2 : rw_cells bsegs m2 (usp + -32) (new_frame s0 ra ra1 j)).
    { apply (rw_cells_agree bsegs m1 m2 _ _ FR1); [| exact WM2]. apply (agree_of_pres _ _ _ _ _ _ PRES2).
      intros x Hx. unfold new_frame in Hx. cbn [cells_size csize Nat.add] in Hx. left. ul. }
    pose proof (new_walkB usp p ra1 lo gp (Z_to_bv 64 0x6abde8) u0 u1 u2 (Z_to_bv 64 n) s1 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  u3 u4 u5 u6 s0 ra j F2 fc2 m2 RA1 ST2 ltac:(ul) ltac:(ul) ltac:(ul) FR2 MI2) as W2.
    lazymatch type of W2 with evt bsegs _ ?X =>
      assert (W2' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W2) end.
    clear W2.
    apply (cps_realizes bsegs _ _ _ c2 (asta_evt_c RT AF Σ1 PMc _ _ MST W2') Hc2'). clear W2'. intros c3 Hc3.
    apply Hk. split; [| apply (cfrm0_of_asta RT Σ1 PMc _ c3 Hc3); intros ms (_ & E & _); rewrite E; exact FRM2].
    exists Σ1, p. split; [| repeat split; assumption].
    eapply ASTA_conseq; [exact Hc3|]. intros ms (RS3 & _ & ST3). exists m2.
    split; [rewrite ESP; exact RS3|].
    split; [split; [exact ART2| split; [exact MI2| split; [exact (wmono_trans _ _ _ _ WM1 WM2)| exact ST3]]]|].
    split; [| split; [exact WR2| exact ACC2]].
    intros a Ha. pose proof (aclient_split_c RT AF Σ m usp (bv_unsigned a) ART0 Ha) as SPL.
    rewrite (PRES2 a), (MU1 a); [reflexivity| |].
    + cbn [outside]. split; [ul| exact I].
    + apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| lia].
Qed.

Theorem new_nt_ok : new_cps e_new_nt.
Proof using AF MAL. apply (new_gen e_new_nt 0x10af8c); [left; reflexivity|]. intros. apply new_walkA; assumption. Qed.

Theorem newarr_nt_ok : new_cps e_newarr_nt.
Proof using AF MAL. apply (new_gen e_newarr_nt 0x10afc0); [right; reflexivity|]. intros. apply newarr_walkA; assumption. Qed.

End NewCPS.

Lemma delarr_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  evt bsegs (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_free m))
    (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_delarr m).
Proof. intros. unfold entry_st, e_delarr, e_free. zstep. zstep. apply evt_done. cbv delta [mkR]. reflexivity. Qed.

Lemma del_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  evt bsegs (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_free m))
    (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_del m).
Proof. intros. unfold entry_st, e_del, e_free. zstep. zstep. apply evt_done. cbv delta [mkR]. reflexivity. Qed.

Section DelCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

Definition del_cps (entry : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (p n lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  In (p, n) (rt_live RT Σ) -> a0 = Z_to_bv 64 p -> tp = Z_to_bv 64 0x6abde8 ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo -> unwind_ok ra s0 sp -> frm0 fc ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc entry m)))
            (free_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p lo m).

Definition delnull_cps (entry : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 0 -> tp = Z_to_bv 64 0x6abde8 ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo -> unwind_ok ra s0 sp -> frm0 fc ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc entry m)))
            (fun c => exists v, icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v lo 0 0 m (fun _ => True) c).

Theorem delarr_ok : free_contract_f RT -> del_cps e_delarr.
Proof using AF.
  intros FREE Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n lo
    FDO MST HIN EA ETP ART0 MI0 COK UOK FRM T c (Hc & FC0) Hk.
  assert (W : forall ms, eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_delarr m) ms ->
                evt bsegs _ ms) by (intros ms <-; apply delarr_walk).
  apply (cps_realizes bsegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W) Hc). intros c1 Hc1.
  assert (FC1 : cfrm0 c1) by (apply (cfrm0_of_asta RT Σ PMc (eq _) c1 Hc1); intros ms0 <-; exact FRM).
  exact (FREE Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n lo
           FDO MST HIN EA ETP ART0 MI0 COK UOK T c1 (conj Hc1 FC1) Hk).
Qed.

Theorem del_ok : free_contract_f RT -> del_cps e_del.
Proof using AF.
  intros FREE Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n lo
    FDO MST HIN EA ETP ART0 MI0 COK UOK FRM T c (Hc & FC0) Hk.
  assert (W : forall ms, eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_del m) ms ->
                evt bsegs _ ms) by (intros ms <-; apply del_walk).
  apply (cps_realizes bsegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W) Hc). intros c1 Hc1.
  assert (FC1 : cfrm0 c1) by (apply (cfrm0_of_asta RT Σ PMc (eq _) c1 Hc1); intros ms0 <-; exact FRM).
  exact (FREE Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n lo
           FDO MST HIN EA ETP ART0 MI0 COK UOK T c1 (conj Hc1 FC1) Hk).
Qed.

Theorem delarr_null_ok : free_null_contract_f RT -> delnull_cps e_delarr.
Proof using AF.
  intros FREE0 Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    FDO MST EA ETP ART0 MI0 COK UOK FRM T c (Hc & FC0) Hk.
  assert (W : forall ms, eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_delarr m) ms ->
                evt bsegs _ ms) by (intros ms <-; apply delarr_walk).
  apply (cps_realizes bsegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W) Hc). intros c1 Hc1.
  assert (FC1 : cfrm0 c1) by (apply (cfrm0_of_asta RT Σ PMc (eq _) c1 Hc1); intros ms0 <-; exact FRM).
  exact (FREE0 Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
           FDO MST EA ETP ART0 MI0 COK UOK T c1 (conj Hc1 FC1) Hk).
Qed.

End DelCPS.
