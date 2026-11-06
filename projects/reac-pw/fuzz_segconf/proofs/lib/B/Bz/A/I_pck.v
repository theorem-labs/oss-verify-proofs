(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: relocated unchanged from an earlier relocation of this file for fuzz_command, for the image this tree pins (fuzz_command.asan-ubsan sha256 bbe55d24). *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/B/Bz/A/I_pck.v (donor image sha256 bbe55d24d096), with its module paths changed and its addresses moved to reac-pw/fuzz_segconf's ASan build. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A Require Import Shadow.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A Require Import R_small I_qck X_atexit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Definition cstr_at (m : mem) (s : Z) (str : list byte) : Prop :=
  bytes_at asegs m s (str ++ [z8]) /\ ~ In z8 str.

Lemma cstr_byte : forall m s str i, cstr_at m s str -> (i < length str)%nat ->
  exists b, bytes_at asegs m (s + Z.of_nat i) [b] /\ b <> z8 /\ nth_error str i = Some b.
Proof.
  intros m s str i (BY & NZ) Hi.
  destruct (nth_error str i) as [b|] eqn:E; [| apply nth_error_None in E; lia].
  exists b. split; [| split; [| reflexivity]].
  - apply (bytes_at_nth1 asegs m s (str ++ [z8]) i b BY). rewrite nth_error_app1 by exact Hi. exact E.
  - intros ->. apply NZ. eapply nth_error_In. exact E.
Qed.

Lemma cstr_nul : forall m s str, cstr_at m s str -> bytes_at asegs m (s + Z.of_nat (length str)) [z8].
Proof.
  intros m s str (BY & _). apply (bytes_at_nth1 asegs m s (str ++ [z8]) (length str) z8 BY).
  rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.

Lemma cstr_bound : forall m s str, cstr_at m s str -> 0 <= s /\ s + Z.of_nat (length str) + 1 <= 2^64.
Proof. intros m s str (BY & _). pose proof (bytes_at_bound _ _ _ _ BY) as B. rewrite length_app in B. cbn [length] in B. lia. Qed.

Lemma z8_neq : forall b : byte, b <> z8 -> bv_unsigned b <> 0.
Proof. intros b H E. apply H. apply bv_eq. rewrite E. reflexivity. Qed.

(* [comment removed for export] *)
Lemma istrlen_loop : forall (n : nat) (k : nat) (s : Z) (str : list byte)
    (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  cstr_at m s str -> (length str = k + n)%nat -> mem_inv asegs m ->
  evt asegs (fun ms' => exists a2' : word,
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 s) (Z_to_bv 64 (Z.of_nat (length str) + 1)) a2' a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x68400) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 s) (Z_to_bv 64 (Z.of_nat k)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x683f0) fc None m (seg_rom asegs)).
Proof.
  induction n as [|n IH]; intros k s str ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    CS LEN MI.
  - pose proof (cstr_bound m s str CS) as (S0 & SB).
    pose proof (cstr_nul m s str CS) as NUL. rewrite LEN, Nat.add_0_r in NUL. pose proof (ro_C1_of_bytes m _ _ NUL) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (EUs : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia).
    assert (EUk : bv_unsigned (Z_to_bv 64 (Z.of_nat k)) = Z.of_nat k) by (apply unsigned_lit; lia).
    assert (EUsk : bv_unsigned (Z_to_bv 64 (s + Z.of_nat k)) = s + Z.of_nat k) by (apply unsigned_lit; lia).
    lstep. set (p := s + Z.of_nat k) in *. do 2 lstep. lstep. if_false.
    apply evt_done. eexists. rewrite LEN, Nat.add_0_r. reflexivity.
  - pose proof (cstr_bound m s str CS) as (S0 & SB).
    destruct (cstr_byte m s str k CS ltac:(lia)) as (b & Hb & Bnz & _). pose proof (ro_C1_of_bytes m _ _ Hb) as CB0.
    pose proof (z8_neq b Bnz) as BNZ. pose proof (bv_unsigned_in_range 8 b) as BR. unfold bv_modulus in BR. change (2 ^ Z.of_N 8) with 256 in BR.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (EUs : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia).
    assert (EUk : bv_unsigned (Z_to_bv 64 (Z.of_nat k)) = Z.of_nat k) by (apply unsigned_lit; lia).
    assert (EUsk : bv_unsigned (Z_to_bv 64 (s + Z.of_nat k)) = s + Z.of_nat k) by (apply unsigned_lit; lia).
    lstep. set (p := s + Z.of_nat k) in *. do 2 lstep. lstep.
    if_cases K; zify_cond K; [ | exfalso; rewrite ?unsigned_lit in K by lia; lia ]. subst p.
    replace (Z.of_nat k + 1) with (Z.of_nat (S k)) by lia.
    apply (IH (S k) s str); [exact CS | lia | exact MI].
Qed.

Lemma internal_strlen_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (s : Z) (str : list byte),
  a0 = Z_to_bv 64 s -> cstr_at m s str -> mem_inv asegs m ->
  evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z.of_nat (length str)) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x683ec) fc None m (seg_rom asegs)).
Proof.
  intros until str. intros -> CS MI.
  pose proof (cstr_bound m s str CS) as (S0 & SB).
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lstep. change (Z_to_bv 64 0) with (Z_to_bv 64 (Z.of_nat 0)).
  eapply evt_cut; [eapply (istrlen_loop (length str) 0 s str); [exact CS | lia | exact MI] |].
  intros ms (a2' & ->).
  lstep. lstep.
  apply evt_done. unfold leaf_post. do 14 eexists. exists m.
  split; [ first [reflexivity | f_equal; f_equal; apply Z_to_bv_eqm; rewrite unsigned_lit_wrap; Z.div_mod_to_equations; lia] |].
  split; [exact MU|]. split; [exact WM| exact MI].
Qed.
