(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast SysStep FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma land_m32 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551584 = 32 * (x / 32).
Proof.
  intros x Hx. change 18446744073709551584 with (Z.ldiff (Z.ones 64) (Z.ones 5)).
  rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  change (2^5) with 32. lia.
Qed.

Lemma le1_lit : forall z, le1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof.
  intros z. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply Z_to_bv8_mod. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2^64). rewrite <- Znumtheory.Zmod_div_mod; [reflexivity| lia| lia| exists (2^56); reflexivity].
Qed.
Ltac sb_fix := lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) => rewrite (le1_lit z); mem_after_store
  end.
Ltac ls := lstep; try sb_fix.

Definition sh32 (b : list byte) : list cell := map (fun x => CB 1 [x]) b.

Definition fz_hdr (c0 c1 c2 : cell) (h3 : list byte) : list cell := [c0; c1; c2; CB 8 h3].
Definition fz_parser (c0 : cell) (p1 : list byte) (c8 c16 : cell) (p17 : list byte) (c20 c24 c48 c56 : cell) (p57 : list byte) (c64 : cell) : list cell :=
  [c0; CB 7 p1; c8; c16; CB 3 p17; c20; c24; c48; c56; CB 7 p57; c64].

Definition fz_locals (j0 j1 : list byte) (f : Z) (j3 j4 j5 : list byte) : list cell :=
  [CB 8 j0; CB 8 j1; C8 (Z_to_bv 64 f); CB 8 j3; CB 8 j4; CB 8 j5].

Definition e_pid : Z := 0xb7630.
Definition e_pdtor : Z := 0xb74b0.

Open Scope Z_scope.

Lemma cells_mid_update : forall (m m' : mem) A pre k old new post,
  rw_cells bsegs m A (pre ++ [CB k old] ++ post) ->
  agree_on (fun x => A <= x < A + Z.of_nat (cells_size (pre ++ [CB k old] ++ post))
                     /\ ~ (A + Z.of_nat (cells_size pre) <= x < A + Z.of_nat (cells_size pre) + Z.of_nat k)) m m' ->
  wmono bsegs m m' -> bytes_at bsegs m' (A + Z.of_nat (cells_size pre)) new -> length new = k ->
  rw_cells bsegs m' A (pre ++ [CB k new] ++ post).
Proof.
  intros m m' A pre k old new post H AG WM HB HL.
  apply Sj_stage1_kit.rw_cells_app in H. destruct H as [H1 H2]. apply Sj_stage1_kit.rw_cells_app in H2. destruct H2 as [H2 H3].
  assert (E : cells_size (pre ++ [CB k old] ++ post) = (cells_size pre + (k + cells_size post))%nat)
    by (rewrite !cells_size_app; cbn [cells_size csize]; lia).
  cbn [cells_size csize] in H3. rewrite Nat.add_0_r in H3.
  pose proof (rw_cells_bound bsegs m _ _ H1) as B1. pose proof (rw_cells_bound bsegs m _ _ H3) as B3.
  apply Sj_stage1_kit.rw_cells_app. split.
  - apply (rw_cells_agree bsegs m m' _ _ H1); [| exact WM]. eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. rewrite E. lia.
  - apply Sj_stage1_kit.rw_cells_app. split.
    + subst k. apply rw_cells_CB_intro; [exact HB|].
      assert (W : wr_at bsegs m (A + Z.of_nat (cells_size pre)) (Z.of_nat (length new))).
      { apply (rw_cells_wr_at bsegs m _ _ _ H2). cbn [cells_size csize]. lia. }
      exact (wr_at_transport bsegs m m' _ _ W WM).
    + cbn [cells_size csize]. rewrite Nat.add_0_r.
      apply (rw_cells_agree bsegs m m' _ _ H3); [| exact WM]. eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. rewrite E. lia.
Qed.

Lemma outside_of_nin : forall (W : list (Z * Z)) x, ~ in_ranges W x -> outside W x.
Proof.
  induction W as [|[l h] W IH]; intros x H; [exact I|]. cbn [outside]. split.
  - intros Hr. apply H. exists l, h. split; [left; reflexivity| exact Hr].
  - apply IH. intros (l' & h' & Hin & Hr). apply H. exists l', h'. split; [right; exact Hin| exact Hr].
Qed.

Definition parser_init (p1 p17 p57 : list byte) : list cell :=
  fz_parser (C1 (Z_to_bv 8 0)) p1 (C8 (Z_to_bv 64 0)) (C1 (Z_to_bv 8 0)) p17 (C4 (Z_to_bv 64 12)) (CB 24 (repeat z8 24))
            (C8 (Z_to_bv 64 4294967295)) (C1 (Z_to_bv 8 0)) p57 (CB 16 (repeat z8 16)).

Definition PID_STACK : Z := 0x3f000.
Definition PID_FRAMES : nat := 8.

Section FuzzCPS.
Variable RT : rt_sig.
Variable LIB : mem -> Prop.
Variable PDONE : rts RT -> mem -> Z -> list (Z * Z) -> Prop.
Hypothesis LIB_loc : fp_local LIB_FP LIB.

Definition pdtor_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (P : Z) (L0 : list (Z * Z)) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 P -> tp = Z_to_bv 64 0x6be3e8 ->
  PDONE Σ m P L0 -> ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + PID_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> unwind_ok ra s0 sp -> frm0 fc ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_pdtor m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists v m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
         /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
         /\ rt_pres_fp L0 (rt_frames RT Σ) (bv_unsigned sp) [(P, P + 80)] m m') c
       /\ rt_live RT Σ' = L0 /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

Lemma lib_fp_static : forall x, in_ranges LIB_FP x -> client_static x /\ 0x6bc060 <= x < 0x6de75c.
Proof.
  intros x (l & h & Hin & Hr). unfold LIB_FP in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hin|Hin]; [inversion Hin; subst l h; split; [apply client_static_intro; lia| lia]|]). destruct Hin.
Qed.

Lemma LIB_agree : forall m m', LIB m -> agree_on (in_ranges LIB_FP) m m' -> LIB m'.
Proof using LIB_loc. intros m m' H AG. apply (LIB_loc m m' H). intros a Ha. apply AG. exact Ha. Qed.

End FuzzCPS.
