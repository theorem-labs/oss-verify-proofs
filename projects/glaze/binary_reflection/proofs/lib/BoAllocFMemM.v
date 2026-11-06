(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRun3N. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRun3N.BoAllocFRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRun3N.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).

Section P3STK.
  Context {fx : FPState}.
  Variables (memD : word -> option byte) (S p x22 : word) (T n n8 id last cnt bsz qb : Z).
  Hypothesis GS : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47.
  Hypothesis Gp : AIMGHI + 16 <= U p /\ (PSIDE (U p) n8 /\ U p + n8 <= U S - 3584) /\ U p mod 16 = 0.
  Hypothesis GT : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584).
  Hypothesis Gn8 : 8 <= n8 /\ n8 mod 8 = 0 /\ n8 <= 2 ^ 40.
  Hypothesis Glast : 0x10007fff8000 <= last /\ last + 8192 <= U S - 3584.
  Hypothesis Gcnt : 0 <= cnt < 1021.
  Lemma TSB_P3STK : hideW ((T + 4096 <= 0x7fff8000)%Z \/ (0x10007fff8000 <= T)%Z).
  Proof using GT n8 p S. pose proof GT as X. unfold hideW in X |- *. lia. Qed.
  Lemma PSB_P3STK : hideW ((U p + n8 <= 0x7fff7000)%Z \/ (0x10007fff8000 + 16 <= U p)%Z).
  Proof using Gp S. pose proof Gp as X. unfold hideW in X |- *. lia. Qed.
  #[local] Abbreviation M13 := (fr_P3 memD S p x22 T n n8 id last cnt bsz qb).

  Lemma shlen8' : shlen (Z_to_bv 64 n8) = n8 / 8.
  Proof using Gn8 GT Gp T p S. pose proof TSB_P3STK as TSB1; unfold hideW in TSB1. pose proof PSB_P3STK as PSB1; unfold hideW in PSB1. (lazymatch goal with |- ?G => let G' := eval unfold shlen in G in change_no_check G' end). unorm. reflexivity. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma pd8' : 8 * (U p / 8) = U p /\ 8 * (n8 / 8) = n8 /\ AIMGHI / 8 <= U p / 8 /\ U p / 8 + n8 / 8 <= 2 ^ 44.
  Proof using Gcnt Gn8 GT Gp GS cnt T x22 S memD. pose proof TSB_P3STK as TSB1; unfold hideW in TSB1. pose proof PSB_P3STK as PSB1; unfold hideW in PSB1. pose proof (u64_range S). Z.div_mod_to_equations. lia. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Ltac side3 := wd_lenlit; rewrite ?length_N_to_le_bytes, ?repeat_length, ?shlen8'; rewrite ?Z2Nat.id by lia;
                (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Nat.add Nat.mul] in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold shad, at_ in G in change_no_check G' end); wd_ulia.
  Ltac rd3 := pose proof (u64_range S); pose proof (u64_range p); pose proof pd8';
              (lazymatch goal with |- ?G => let G' := eval unfold fr_P3, fr_PS, fr_c2, fr_c1, ps_frame in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end); rewrite ?at_at;
              repeat (wd_rdstep side3).

  (* [comment removed for export] *)
  Lemma fr_P3_e0 : rdn BSEGS M13 (at_ S (-2216)) 8 = Some (LE8 (Z_to_bv 64 0x50afc)).             Proof using Gcnt Glast Gn8 GT Gp GS. pose proof TSB_P3STK as TSB1; unfold hideW in TSB1. pose proof PSB_P3STK as PSB1; unfold hideW in PSB1. rd3. Qed.
  Lemma fr_P3_e1 : rdn BSEGS M13 (at_ S (-2224)) 8 = Some (LE8 (Z_to_bv 64 (0x10ab58 + 728))).    Proof using Gcnt Glast Gn8 GT Gp GS. pose proof TSB_P3STK as TSB1; unfold hideW in TSB1. pose proof PSB_P3STK as PSB1; unfold hideW in PSB1. rd3. Qed.
  Lemma fr_P3_e2 : rdn BSEGS M13 (at_ S (-2232)) 8 = Some (LE8 (at_ (Z_to_bv 64 T) 80)).         Proof using Gcnt Glast Gn8 GT Gp GS. pose proof TSB_P3STK as TSB1; unfold hideW in TSB1. pose proof PSB_P3STK as PSB1; unfold hideW in PSB1. rd3. Qed.
  Lemma fr_P3_e3 : rdn BSEGS M13 (at_ S (-2240)) 8 = Some (LE8 (Z_to_bv 64 n)).                   Proof using Gcnt Glast Gn8 GT Gp GS. pose proof TSB_P3STK as TSB1; unfold hideW in TSB1. pose proof PSB_P3STK as PSB1; unfold hideW in PSB1. rd3. Qed.
  Lemma fr_P3_e4 : rdn BSEGS M13 (at_ S (-2248)) 8 = Some (LE8 (at_ S (-2128))).                  Proof using Gcnt Glast Gn8 GT Gp GS. pose proof TSB_P3STK as TSB1; unfold hideW in TSB1. pose proof PSB_P3STK as PSB1; unfold hideW in PSB1. rd3. Qed.
  Lemma fr_P3_e5 : rdn BSEGS M13 (at_ S (-2256)) 8 = Some (LE8 (at_ (Z_to_bv 64 T) 208)).        Proof using Gcnt Glast Gn8 GT Gp GS. pose proof TSB_P3STK as TSB1; unfold hideW in TSB1. pose proof PSB_P3STK as PSB1; unfold hideW in PSB1. rd3. Qed.
  Lemma fr_P3_e6 : rdn BSEGS M13 (at_ S (-2264)) 8 = Some (LE8 (at_ p (-16))).                    Proof using Gcnt Glast Gn8 GT Gp GS. pose proof TSB_P3STK as TSB1; unfold hideW in TSB1. pose proof PSB_P3STK as PSB1; unfold hideW in PSB1. rd3. Qed.
  (* [comment removed for export] *)
  Lemma fr_P3_cb0 : rdn BSEGS M13 (at_ S (-2208)) 8 = Some (LE8 (at_ (Z_to_bv 64 T) 208)).       Proof using Gcnt Glast Gn8 GT Gp GS. pose proof TSB_P3STK as TSB1; unfold hideW in TSB1. pose proof PSB_P3STK as PSB1; unfold hideW in PSB1. rd3. Qed.
  Lemma fr_P3_cb1 : rdn BSEGS M13 (at_ S (-2200)) 8 = Some (LE8 (at_ S (-2128))).                 Proof using Gcnt Glast Gn8 GT Gp GS. pose proof TSB_P3STK as TSB1; unfold hideW in TSB1. pose proof PSB_P3STK as PSB1; unfold hideW in PSB1. rd3. Qed.
  (* [comment removed for export] *)
  Lemma fr_P3_q0 : rdn BSEGS M13 (at_ S (-2136)) 8 = Some (LE8 (Z_to_bv 64 0x6ef14)).             Proof using Gcnt Glast Gn8 GT Gp GS. pose proof TSB_P3STK as TSB1; unfold hideW in TSB1. pose proof PSB_P3STK as PSB1; unfold hideW in PSB1. rd3. Qed.
  Lemma fr_P3_q1 : rdn BSEGS M13 (at_ S (-2144)) 8 = Some (LE8 S).                                Proof using Gcnt Glast Gn8 GT Gp GS. pose proof TSB_P3STK as TSB1; unfold hideW in TSB1. pose proof PSB_P3STK as PSB1; unfold hideW in PSB1. rd3. Qed.
  Lemma fr_P3_q2 : rdn BSEGS M13 (at_ S (-2152)) 8 = Some (LE8 p).                                Proof using Gcnt Glast Gn8 GT Gp GS. pose proof TSB_P3STK as TSB1; unfold hideW in TSB1. pose proof PSB_P3STK as PSB1; unfold hideW in PSB1. rd3. Qed.
  Lemma fr_P3_q3 : rdn BSEGS M13 (at_ S (-2160)) 8 = Some (LE8 (Z_to_bv 64 0x6eea4)).             Proof using Gcnt Glast Gn8 GT Gp GS. pose proof TSB_P3STK as TSB1; unfold hideW in TSB1. pose proof PSB_P3STK as PSB1; unfold hideW in PSB1. rd3. Qed.
  Lemma fr_P3_q4 : rdn BSEGS M13 (at_ S (-2168)) 8 = Some (LE8 (Z_to_bv 64 1)).                   Proof using Gcnt Glast Gn8 GT Gp GS. pose proof TSB_P3STK as TSB1; unfold hideW in TSB1. pose proof PSB_P3STK as PSB1; unfold hideW in PSB1. rd3. Qed.
  Lemma fr_P3_q5 : rdn BSEGS M13 (at_ S (-2176)) 8 = Some (LE8 (at_ S (-2128))).                  Proof using Gcnt Glast Gn8 GT Gp GS. pose proof TSB_P3STK as TSB1; unfold hideW in TSB1. pose proof PSB_P3STK as PSB1; unfold hideW in PSB1. rd3. Qed.
  Lemma fr_P3_q6 : rdn BSEGS M13 (at_ S (-2184)) 8 = Some (LE8 (at_ S (-81))).                    Proof using Gcnt Glast Gn8 GT Gp GS. pose proof TSB_P3STK as TSB1; unfold hideW in TSB1. pose proof PSB_P3STK as PSB1; unfold hideW in PSB1. rd3. Qed.
  Lemma fr_P3_q7 : rdn BSEGS M13 (at_ S (-2192)) 8 = Some (LE8 x22).                              Proof using Gcnt Glast Gn8 GT Gp GS. pose proof TSB_P3STK as TSB1; unfold hideW in TSB1. pose proof PSB_P3STK as PSB1; unfold hideW in PSB1. rd3. Qed.
  (* [comment removed for export] *)
  Lemma fr_P3_stk : forall a : word, U S - 2128 <= U a -> M13 a = memD a.
  Proof using Gcnt Glast Gn8 GT Gp GS. pose proof TSB_P3STK as TSB1; unfold hideW in TSB1. pose proof PSB_P3STK as PSB1; unfold hideW in PSB1.
    intros a Ha. pose proof (u64_range S). pose proof (u64_range p). pose proof pd8'.
    (lazymatch goal with |- ?G => let G' := eval unfold fr_P3, fr_PS, fr_c2, fr_c1, ps_frame in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite ?at_at.
    rewrite !wbytes_outside by side3. reflexivity.
  Qed.
End P3STK.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section P3ESTK.
  Context {fx : FPState}.
  Variables (memD : word -> option byte) (S p x22 : word) (T n n8 id cnt24 k ba qb : Z) (bst bcs : list byte).
  Hypothesis GS : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47.
  Hypothesis Gp : AIMGHI + 16 <= U p /\ (PSIDE (U p) n8 /\ U p + n8 <= U S - 3584) /\ U p mod 16 = 0.
  Hypothesis GT : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584).
  Hypothesis Gn8 : 8 <= n8 /\ n8 mod 8 = 0 /\ n8 <= 2 ^ 40.
  Hypothesis Gba : 0x10007fff8000 <= ba /\ ba + 8192 <= U S - 3584.
  Lemma TSB_P3ESTK : hideW ((T + 4096 <= 0x7fff8000)%Z \/ (0x10007fff8000 <= T)%Z).
  Proof using GT n8 p S. pose proof GT as X. unfold hideW in X |- *. lia. Qed.
  Lemma PSB_P3ESTK : hideW ((U p + n8 <= 0x7fff7000)%Z \/ (0x10007fff8000 + 16 <= U p)%Z).
  Proof using Gp S. pose proof Gp as X. unfold hideW in X |- *. lia. Qed.
  #[local] Abbreviation Me := (fr_P3e memD S p x22 T n n8 id cnt24 k ba qb bst bcs).

  Lemma shlen8N' : shlen (Z_to_bv 64 n8) = n8 / 8.
  Proof using Gn8 GT Gp T p S. pose proof TSB_P3ESTK as TSB1; unfold hideW in TSB1. pose proof PSB_P3ESTK as PSB1; unfold hideW in PSB1. (lazymatch goal with |- ?G => let G' := eval unfold shlen in G in change_no_check G' end). unorm. reflexivity. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma pd8N' : 8 * (U p / 8) = U p /\ 8 * (n8 / 8) = n8 /\ AIMGHI / 8 <= U p / 8 /\ U p / 8 + n8 / 8 <= 2 ^ 44.
  Proof using Gn8 GT Gp GS T x22 S memD. pose proof TSB_P3ESTK as TSB1; unfold hideW in TSB1. pose proof PSB_P3ESTK as PSB1; unfold hideW in PSB1. pose proof (u64_range S). Z.div_mod_to_equations. lia. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Ltac sideN := wd_lenlit; rewrite ?length_N_to_le_bytes, ?repeat_length, ?shlen8N'; rewrite ?Z2Nat.id by lia;
                (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Nat.add Nat.mul] in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold shad, at_ in G in change_no_check G' end); wd_ulia.
  Ltac rdN := pose proof (u64_range S); pose proof (u64_range p); pose proof pd8N';
              (lazymatch goal with |- ?G => let G' := eval unfold fr_P3e, fr_P3f, fr_e1e, fr_e1f, fr_PS, fr_c1, ps_frame in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end); rewrite ?at_at;
              repeat (wd_rdstep sideN).

  Lemma fr_P3e_e0 : rdn BSEGS Me (at_ S (-2216)) 8 = Some (LE8 (Z_to_bv 64 0x50afc)).             Proof using Gba Gn8 GT Gp GS. pose proof TSB_P3ESTK as TSB1; unfold hideW in TSB1. pose proof PSB_P3ESTK as PSB1; unfold hideW in PSB1. rdN. Qed.
  Lemma fr_P3e_e1 : rdn BSEGS Me (at_ S (-2224)) 8 = Some (LE8 (Z_to_bv 64 (0x10ab58 + 728))).    Proof using Gba Gn8 GT Gp GS. pose proof TSB_P3ESTK as TSB1; unfold hideW in TSB1. pose proof PSB_P3ESTK as PSB1; unfold hideW in PSB1. rdN. Qed.
  Lemma fr_P3e_e2 : rdn BSEGS Me (at_ S (-2232)) 8 = Some (LE8 (at_ (Z_to_bv 64 T) 80)).         Proof using Gba Gn8 GT Gp GS. pose proof TSB_P3ESTK as TSB1; unfold hideW in TSB1. pose proof PSB_P3ESTK as PSB1; unfold hideW in PSB1. rdN. Qed.
  Lemma fr_P3e_e3 : rdn BSEGS Me (at_ S (-2240)) 8 = Some (LE8 (Z_to_bv 64 n)).                   Proof using Gba Gn8 GT Gp GS. pose proof TSB_P3ESTK as TSB1; unfold hideW in TSB1. pose proof PSB_P3ESTK as PSB1; unfold hideW in PSB1. rdN. Qed.
  Lemma fr_P3e_e4 : rdn BSEGS Me (at_ S (-2248)) 8 = Some (LE8 (at_ S (-2128))).                  Proof using Gba Gn8 GT Gp GS. pose proof TSB_P3ESTK as TSB1; unfold hideW in TSB1. pose proof PSB_P3ESTK as PSB1; unfold hideW in PSB1. rdN. Qed.
  Lemma fr_P3e_e5 : rdn BSEGS Me (at_ S (-2256)) 8 = Some (LE8 (at_ (Z_to_bv 64 T) 208)).        Proof using Gba Gn8 GT Gp GS. pose proof TSB_P3ESTK as TSB1; unfold hideW in TSB1. pose proof PSB_P3ESTK as PSB1; unfold hideW in PSB1. rdN. Qed.
  Lemma fr_P3e_e6 : rdn BSEGS Me (at_ S (-2264)) 8 = Some (LE8 (at_ p (-16))).                    Proof using Gba Gn8 GT Gp GS. pose proof TSB_P3ESTK as TSB1; unfold hideW in TSB1. pose proof PSB_P3ESTK as PSB1; unfold hideW in PSB1. rdN. Qed.
  Lemma fr_P3e_cb0 : rdn BSEGS Me (at_ S (-2208)) 8 = Some (LE8 (at_ (Z_to_bv 64 T) 208)).       Proof using Gba Gn8 GT Gp GS. pose proof TSB_P3ESTK as TSB1; unfold hideW in TSB1. pose proof PSB_P3ESTK as PSB1; unfold hideW in PSB1. rdN. Qed.
  Lemma fr_P3e_cb1 : rdn BSEGS Me (at_ S (-2200)) 8 = Some (LE8 (at_ S (-2128))).                 Proof using Gba Gn8 GT Gp GS. pose proof TSB_P3ESTK as TSB1; unfold hideW in TSB1. pose proof PSB_P3ESTK as PSB1; unfold hideW in PSB1. rdN. Qed.
  Lemma fr_P3e_q0 : rdn BSEGS Me (at_ S (-2136)) 8 = Some (LE8 (Z_to_bv 64 0x6ef14)).             Proof using Gba Gn8 GT Gp GS. pose proof TSB_P3ESTK as TSB1; unfold hideW in TSB1. pose proof PSB_P3ESTK as PSB1; unfold hideW in PSB1. rdN. Qed.
  Lemma fr_P3e_q1 : rdn BSEGS Me (at_ S (-2144)) 8 = Some (LE8 S).                                Proof using Gba Gn8 GT Gp GS. pose proof TSB_P3ESTK as TSB1; unfold hideW in TSB1. pose proof PSB_P3ESTK as PSB1; unfold hideW in PSB1. rdN. Qed.
  Lemma fr_P3e_q2 : rdn BSEGS Me (at_ S (-2152)) 8 = Some (LE8 p).                                Proof using Gba Gn8 GT Gp GS. pose proof TSB_P3ESTK as TSB1; unfold hideW in TSB1. pose proof PSB_P3ESTK as PSB1; unfold hideW in PSB1. rdN. Qed.
  Lemma fr_P3e_q3 : rdn BSEGS Me (at_ S (-2160)) 8 = Some (LE8 (Z_to_bv 64 0x6eea4)).             Proof using Gba Gn8 GT Gp GS. pose proof TSB_P3ESTK as TSB1; unfold hideW in TSB1. pose proof PSB_P3ESTK as PSB1; unfold hideW in PSB1. rdN. Qed.
  Lemma fr_P3e_q4 : rdn BSEGS Me (at_ S (-2168)) 8 = Some (LE8 (Z_to_bv 64 1)).                   Proof using Gba Gn8 GT Gp GS. pose proof TSB_P3ESTK as TSB1; unfold hideW in TSB1. pose proof PSB_P3ESTK as PSB1; unfold hideW in PSB1. rdN. Qed.
  Lemma fr_P3e_q5 : rdn BSEGS Me (at_ S (-2176)) 8 = Some (LE8 (at_ S (-2128))).                  Proof using Gba Gn8 GT Gp GS. pose proof TSB_P3ESTK as TSB1; unfold hideW in TSB1. pose proof PSB_P3ESTK as PSB1; unfold hideW in PSB1. rdN. Qed.
  Lemma fr_P3e_q6 : rdn BSEGS Me (at_ S (-2184)) 8 = Some (LE8 (at_ S (-81))).                    Proof using Gba Gn8 GT Gp GS. pose proof TSB_P3ESTK as TSB1; unfold hideW in TSB1. pose proof PSB_P3ESTK as PSB1; unfold hideW in PSB1. rdN. Qed.
  Lemma fr_P3e_q7 : rdn BSEGS Me (at_ S (-2192)) 8 = Some (LE8 x22).                              Proof using Gba Gn8 GT Gp GS. pose proof TSB_P3ESTK as TSB1; unfold hideW in TSB1. pose proof PSB_P3ESTK as PSB1; unfold hideW in PSB1. rdN. Qed.
  Lemma fr_P3e_stk : forall a : word, U S - 2128 <= U a -> Me a = memD a.
  Proof using Gba Gn8 GT Gp GS. pose proof TSB_P3ESTK as TSB1; unfold hideW in TSB1. pose proof PSB_P3ESTK as PSB1; unfold hideW in PSB1.
    intros a Ha. pose proof (u64_range S). pose proof (u64_range p). pose proof pd8N'.
    (lazymatch goal with |- ?G => let G' := eval unfold fr_P3e, fr_e1e, fr_PS, fr_c1, ps_frame in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite ?at_at.
    rewrite !wbytes_outside by sideN. reflexivity.
  Qed.

End P3ESTK.

Section P3FSTK.
  Context {fx : FPState}.
  Variables (memD : word -> option byte) (S p x22 : word) (T n n8 id cnt24 k ba qb last len : Z) (bst bcs : list byte).
  Hypothesis GS : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47.
  Hypothesis Gp : AIMGHI + 16 <= U p /\ (PSIDE (U p) n8 /\ U p + n8 <= U S - 3584) /\ U p mod 16 = 0.
  Hypothesis GT : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584).
  Hypothesis Gn8 : 8 <= n8 /\ n8 mod 8 = 0 /\ n8 <= 2 ^ 40.
  Hypothesis Gba : 0x10007fff8000 <= ba /\ ba + 8192 <= U S - 3584.
  Hypothesis Glast : 0x10007fff8000 <= last /\ last + 8192 <= U S - 3584.
  Lemma TSB_P3FSTK : hideW ((T + 4096 <= 0x7fff8000)%Z \/ (0x10007fff8000 <= T)%Z).
  Proof using GT n8 p S. pose proof GT as X. unfold hideW in X |- *. lia. Qed.
  Lemma PSB_P3FSTK : hideW ((U p + n8 <= 0x7fff7000)%Z \/ (0x10007fff8000 + 16 <= U p)%Z).
  Proof using Gp S. pose proof Gp as X. unfold hideW in X |- *. lia. Qed.
  #[local] Abbreviation Mf := (fr_P3f memD S p x22 T n n8 id cnt24 k ba qb last len bst bcs).

  Lemma shlen8F' : shlen (Z_to_bv 64 n8) = n8 / 8.
  Proof using Gn8 GT Gp T p S. pose proof TSB_P3FSTK as TSB1; unfold hideW in TSB1. pose proof PSB_P3FSTK as PSB1; unfold hideW in PSB1. (lazymatch goal with |- ?G => let G' := eval unfold shlen in G in change_no_check G' end). unorm. reflexivity. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma pd8F' : 8 * (U p / 8) = U p /\ 8 * (n8 / 8) = n8 /\ AIMGHI / 8 <= U p / 8 /\ U p / 8 + n8 / 8 <= 2 ^ 44.
  Proof using Gn8 GT Gp GS T x22 S memD. pose proof TSB_P3FSTK as TSB1; unfold hideW in TSB1. pose proof PSB_P3FSTK as PSB1; unfold hideW in PSB1. pose proof (u64_range S). Z.div_mod_to_equations. lia. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Ltac sideN := wd_lenlit; rewrite ?length_N_to_le_bytes, ?repeat_length, ?shlen8F'; rewrite ?Z2Nat.id by lia;
                (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Nat.add Nat.mul] in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold shad, at_ in G in change_no_check G' end); wd_ulia.
  Ltac rdN := pose proof (u64_range S); pose proof (u64_range p); pose proof pd8F';
              (lazymatch goal with |- ?G => let G' := eval unfold fr_P3e, fr_P3f, fr_e1e, fr_e1f, fr_PS, fr_c1, ps_frame in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end); rewrite ?at_at;
              repeat (wd_rdstep sideN).

  Lemma fr_P3f_e0 : rdn BSEGS Mf (at_ S (-2216)) 8 = Some (LE8 (Z_to_bv 64 0x50afc)).             Proof using Glast Gba Gn8 GT Gp GS. pose proof TSB_P3FSTK as TSB1; unfold hideW in TSB1. pose proof PSB_P3FSTK as PSB1; unfold hideW in PSB1. rdN. Qed.
  Lemma fr_P3f_e1 : rdn BSEGS Mf (at_ S (-2224)) 8 = Some (LE8 (Z_to_bv 64 (0x10ab58 + 728))).    Proof using Glast Gba Gn8 GT Gp GS. pose proof TSB_P3FSTK as TSB1; unfold hideW in TSB1. pose proof PSB_P3FSTK as PSB1; unfold hideW in PSB1. rdN. Qed.
  Lemma fr_P3f_e2 : rdn BSEGS Mf (at_ S (-2232)) 8 = Some (LE8 (at_ (Z_to_bv 64 T) 80)).         Proof using Glast Gba Gn8 GT Gp GS. pose proof TSB_P3FSTK as TSB1; unfold hideW in TSB1. pose proof PSB_P3FSTK as PSB1; unfold hideW in PSB1. rdN. Qed.
  Lemma fr_P3f_e3 : rdn BSEGS Mf (at_ S (-2240)) 8 = Some (LE8 (Z_to_bv 64 n)).                   Proof using Glast Gba Gn8 GT Gp GS. pose proof TSB_P3FSTK as TSB1; unfold hideW in TSB1. pose proof PSB_P3FSTK as PSB1; unfold hideW in PSB1. rdN. Qed.
  Lemma fr_P3f_e4 : rdn BSEGS Mf (at_ S (-2248)) 8 = Some (LE8 (at_ S (-2128))).                  Proof using Glast Gba Gn8 GT Gp GS. pose proof TSB_P3FSTK as TSB1; unfold hideW in TSB1. pose proof PSB_P3FSTK as PSB1; unfold hideW in PSB1. rdN. Qed.
  Lemma fr_P3f_e5 : rdn BSEGS Mf (at_ S (-2256)) 8 = Some (LE8 (at_ (Z_to_bv 64 T) 208)).        Proof using Glast Gba Gn8 GT Gp GS. pose proof TSB_P3FSTK as TSB1; unfold hideW in TSB1. pose proof PSB_P3FSTK as PSB1; unfold hideW in PSB1. rdN. Qed.
  Lemma fr_P3f_e6 : rdn BSEGS Mf (at_ S (-2264)) 8 = Some (LE8 (at_ p (-16))).                    Proof using Glast Gba Gn8 GT Gp GS. pose proof TSB_P3FSTK as TSB1; unfold hideW in TSB1. pose proof PSB_P3FSTK as PSB1; unfold hideW in PSB1. rdN. Qed.
  Lemma fr_P3f_cb0 : rdn BSEGS Mf (at_ S (-2208)) 8 = Some (LE8 (at_ (Z_to_bv 64 T) 208)).       Proof using Glast Gba Gn8 GT Gp GS. pose proof TSB_P3FSTK as TSB1; unfold hideW in TSB1. pose proof PSB_P3FSTK as PSB1; unfold hideW in PSB1. rdN. Qed.
  Lemma fr_P3f_cb1 : rdn BSEGS Mf (at_ S (-2200)) 8 = Some (LE8 (at_ S (-2128))).                 Proof using Glast Gba Gn8 GT Gp GS. pose proof TSB_P3FSTK as TSB1; unfold hideW in TSB1. pose proof PSB_P3FSTK as PSB1; unfold hideW in PSB1. rdN. Qed.
  Lemma fr_P3f_q0 : rdn BSEGS Mf (at_ S (-2136)) 8 = Some (LE8 (Z_to_bv 64 0x6ef14)).             Proof using Glast Gba Gn8 GT Gp GS. pose proof TSB_P3FSTK as TSB1; unfold hideW in TSB1. pose proof PSB_P3FSTK as PSB1; unfold hideW in PSB1. rdN. Qed.
  Lemma fr_P3f_q1 : rdn BSEGS Mf (at_ S (-2144)) 8 = Some (LE8 S).                                Proof using Glast Gba Gn8 GT Gp GS. pose proof TSB_P3FSTK as TSB1; unfold hideW in TSB1. pose proof PSB_P3FSTK as PSB1; unfold hideW in PSB1. rdN. Qed.
  Lemma fr_P3f_q2 : rdn BSEGS Mf (at_ S (-2152)) 8 = Some (LE8 p).                                Proof using Glast Gba Gn8 GT Gp GS. pose proof TSB_P3FSTK as TSB1; unfold hideW in TSB1. pose proof PSB_P3FSTK as PSB1; unfold hideW in PSB1. rdN. Qed.
  Lemma fr_P3f_q3 : rdn BSEGS Mf (at_ S (-2160)) 8 = Some (LE8 (Z_to_bv 64 0x6eea4)).             Proof using Glast Gba Gn8 GT Gp GS. pose proof TSB_P3FSTK as TSB1; unfold hideW in TSB1. pose proof PSB_P3FSTK as PSB1; unfold hideW in PSB1. rdN. Qed.
  Lemma fr_P3f_q4 : rdn BSEGS Mf (at_ S (-2168)) 8 = Some (LE8 (Z_to_bv 64 1)).                   Proof using Glast Gba Gn8 GT Gp GS. pose proof TSB_P3FSTK as TSB1; unfold hideW in TSB1. pose proof PSB_P3FSTK as PSB1; unfold hideW in PSB1. rdN. Qed.
  Lemma fr_P3f_q5 : rdn BSEGS Mf (at_ S (-2176)) 8 = Some (LE8 (at_ S (-2128))).                  Proof using Glast Gba Gn8 GT Gp GS. pose proof TSB_P3FSTK as TSB1; unfold hideW in TSB1. pose proof PSB_P3FSTK as PSB1; unfold hideW in PSB1. rdN. Qed.
  Lemma fr_P3f_q6 : rdn BSEGS Mf (at_ S (-2184)) 8 = Some (LE8 (at_ S (-81))).                    Proof using Glast Gba Gn8 GT Gp GS. pose proof TSB_P3FSTK as TSB1; unfold hideW in TSB1. pose proof PSB_P3FSTK as PSB1; unfold hideW in PSB1. rdN. Qed.
  Lemma fr_P3f_q7 : rdn BSEGS Mf (at_ S (-2192)) 8 = Some (LE8 x22).                              Proof using Glast Gba Gn8 GT Gp GS. pose proof TSB_P3FSTK as TSB1; unfold hideW in TSB1. pose proof PSB_P3FSTK as PSB1; unfold hideW in PSB1. rdN. Qed.
  Lemma fr_P3f_stk : forall a : word, U S - 2128 <= U a -> Mf a = memD a.
  Proof using Glast Gba Gn8 GT Gp GS. pose proof TSB_P3FSTK as TSB1; unfold hideW in TSB1. pose proof PSB_P3FSTK as PSB1; unfold hideW in PSB1.
    intros a Ha. pose proof (u64_range S). pose proof (u64_range p). pose proof pd8F'.
    (lazymatch goal with |- ?G => let G' := eval unfold fr_P3f, fr_e1f, fr_PS, fr_c1, ps_frame in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite ?at_at.
    rewrite !wbytes_outside by sideN. reflexivity.
  Qed.
End P3FSTK.
