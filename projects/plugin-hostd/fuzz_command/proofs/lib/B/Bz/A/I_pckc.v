(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: fm I_pck.v lines 25-26 and 108-213, relocated onto plugin-hostd/fuzz_command.asan; fm internal_strchr 0x63ea8 -> ours 0x69a70. *)
(* Modified by Theorem Labs, 2026-10: relocated from lib/A/<same path> to fuzz_command.asan-ubsan by the image-B address relocator (the A-to-B address map, keyed by the image maps' symbol names and by code; GXA symbol keys kept), whose check table lists every changed numeral *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A Require Import Shadow.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A Require Import R_small I_qck X_atexit.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A Require Import I_pck.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Ltac brT K := if_cases K; zify_cond K; [ | exfalso; try (change (bv_unsigned z8) with 0 in K); rewrite ?unsigned_lit in K by lia; rewrite ?Z.mod_small in K by lia; lia ].
Ltac brF K := if_cases K; zify_cond K; [ exfalso; try (change (bv_unsigned z8) with 0 in K); rewrite ?unsigned_lit in K by lia; rewrite ?Z.mod_small in K by lia; lia | ].

Definition strchr_res (s c : Z) (str : list byte) : Z :=
  match find_byte c str with Some i => s + Z.of_nat i | None => 0 end.

Lemma istrchr_loop : forall (n : nat) (k : nat) (s c : Z) (str : list byte)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (b : byte),
  a0 = Z_to_bv 64 (s + Z.of_nat k) ->
  cstr_at m s str -> (length str + 1 = k + S n)%nat -> 0 < c < 256 ->
  (forall j bj, (j < k)%nat -> nth_error str j = Some bj -> bv_unsigned bj <> c) ->
  bytes_at asegs m (s + Z.of_nat k) [b] -> bv_unsigned b <> c -> mem_inv asegs m ->
  evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (strchr_res s c str) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 c) (Z_to_bv 64 (bv_unsigned b)) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x69acc) fc None m (seg_rom asegs)).
Proof.
  induction n as [|n IH]; intros k s c str ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m b
    -> CS LEN C0 HJ HB HBc MI.
  - (* [comment removed for export] *)
    pose proof (cstr_nul m s str CS) as NUL.
    assert (Ek : k = length str) by lia. subst k.
    assert (Eb : b = z8).
    { destruct HB as (_ & _ & HB1). destruct NUL as (_ & _ & HN1). specialize (HB1 0%nat ltac:(cbn; lia)). specialize (HN1 0%nat ltac:(cbn; lia)).
      cbn in HB1, HN1. rewrite HN1 in HB1. congruence. }
    subst b.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    lstep. if_true. lstep. lstep.
    assert (ER : strchr_res s c str = 0).
    { unfold strchr_res. destruct (find_byte c str) as [i|] eqn:FB; [| reflexivity].
      exfalso. destruct (find_byte_Some _ _ _ FB) as (Hi & (bi & Hbi & Ebi) & _). exact (HJ i bi Hi Hbi Ebi). }
    apply evt_done. unfold leaf_post. rewrite ER. do 14 eexists. exists m.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM| exact MI].
  - (* [comment removed for export] *)
    pose proof (cstr_bound m s str CS) as (S0 & SB).
    destruct (cstr_byte m s str k CS ltac:(lia)) as (b' & Hb' & Bnz & Hnth).
    assert (Eb : b = b').
    { destruct HB as (_ & _ & HB1). destruct Hb' as (_ & _ & HN1). specialize (HB1 0%nat ltac:(cbn; lia)). specialize (HN1 0%nat ltac:(cbn; lia)).
      cbn in HB1, HN1. rewrite HN1 in HB1. congruence. }
    subst b'.
    pose proof (z8_neq b Bnz) as BNZ. pose proof (bv_unsigned_in_range 8 b) as BR. unfold bv_modulus in BR. change (2 ^ Z.of_N 8) with 256 in BR.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (EUs : bv_unsigned (Z_to_bv 64 (s + Z.of_nat k)) = s + Z.of_nat k) by (apply unsigned_lit; lia).
    lstep. brF K1.
    destruct (Nat.eq_dec (S k) (length str)) as [Ek|Ek].
    + (* [comment removed for export] *)
      pose proof (cstr_nul m s str CS) as NUL. rewrite <- Ek in NUL. rewrite Nat2Z.inj_succ in NUL.
      replace (s + Z.succ (Z.of_nat k)) with (s + Z.of_nat k + 1) in NUL by lia.
      pose proof (ro_C1_of_bytes m _ _ NUL) as CB0.
      lstep. lstep. lstep. lstep. brT K2.
      apply (IH (S k) s c str); try assumption; try lia.
      all: try (f_equal; lia).
      all: first [ (intros j bj Hj Hbj; destruct (Nat.eq_dec j k) as [->|NE]; [rewrite Hnth in Hbj; injection Hbj as <-; exact HBc| apply (HJ j bj ltac:(lia) Hbj)])
                 | (rewrite Nat2Z.inj_succ; replace (s + Z.succ (Z.of_nat k)) with (s + Z.of_nat k + 1) by lia; exact NUL)
                 | (change (bv_unsigned z8) with 0; lia) ].
    + destruct (cstr_byte m s str (S k) CS ltac:(lia)) as (b2 & Hb2 & Bnz2 & Hnth2).
      rewrite Nat2Z.inj_succ in Hb2. replace (s + Z.succ (Z.of_nat k)) with (s + Z.of_nat k + 1) in Hb2 by lia.
      pose proof (ro_C1_of_bytes m _ _ Hb2) as CB0.
      pose proof (bv_unsigned_in_range 8 b2) as BR2. unfold bv_modulus in BR2. change (2 ^ Z.of_N 8) with 256 in BR2.
      lstep. lstep. lstep. lstep.
      destruct (Z.eq_dec (bv_unsigned b2) c) as [E2|E2].
      * (* [comment removed for export] *)
        brF K2. lstep. lstep.
        assert (FB : find_byte c str = Some (S k)).
        { apply (find_byte_charact c str (S k) b2 Hnth2 E2). intros j bj Hj Hbj.
          destruct (Nat.eq_dec j k) as [->|NE]; [rewrite Hnth in Hbj; injection Hbj as <-; exact HBc | apply (HJ j bj ltac:(lia) Hbj)]. }
        assert (ER : strchr_res s c str = s + Z.of_nat k + 1) by (unfold strchr_res; rewrite FB; lia).
        apply evt_done. unfold leaf_post. rewrite ER. do 14 eexists. exists m.
        split; [reflexivity|]. split; [exact MU|]. split; [exact WM| exact MI].
      * brT K2.
        apply (IH (S k) s c str); try assumption; try lia.
        all: try (f_equal; lia).
        all: first [ (intros j bj Hj Hbj; destruct (Nat.eq_dec j k) as [->|NE]; [rewrite Hnth in Hbj; injection Hbj as <-; exact HBc| apply (HJ j bj ltac:(lia) Hbj)])
                   | (rewrite Nat2Z.inj_succ; replace (s + Z.succ (Z.of_nat k)) with (s + Z.of_nat k + 1) by lia; exact Hb2) ].
Qed.

Lemma internal_strchr_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (s c : Z) (str : list byte),
  a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 c -> 0 < c < 256 -> cstr_at m s str -> mem_inv asegs m ->
  evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (strchr_res s c str) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x69abc) fc None m (seg_rom asegs)).
Proof.
  intros until str. intros -> -> C0 CS MI.
  pose proof (cstr_bound m s str CS) as (S0 & SB).
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUs : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia).
  assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
  assert (LC : Z.land c 255 = c) by (change 255 with (Z.ones 8); rewrite Z.land_ones by lia; apply Z.mod_small; lia).
  destruct (Nat.eq_dec (length str) 0) as [E0|E0].
  - (* [comment removed for export] *)
    pose proof (cstr_nul m s str CS) as NUL. rewrite E0 in NUL. cbn [Z.of_nat] in NUL. rewrite Z.add_0_r in NUL.
    pose proof (ro_C1_of_bytes m _ _ NUL) as CB0.
    lstep. lstep. rewrite ?LC. lstep. brT K0.
    apply (istrchr_loop 0 0 s c str); try assumption; try lia.
    all: first [ (f_equal; lia) | (intros j bj Hj; lia) | (rewrite Z.add_0_r; exact NUL) | (change (bv_unsigned z8) with 0; lia) ].
  - destruct (cstr_byte m s str 0 CS ltac:(lia)) as (b & Hb & Bnz & Hnth). rewrite Z.add_0_r in Hb.
    pose proof (ro_C1_of_bytes m _ _ Hb) as CB0.
    pose proof (bv_unsigned_in_range 8 b) as BR. unfold bv_modulus in BR. change (2 ^ Z.of_N 8) with 256 in BR.
    lstep. lstep. rewrite ?LC. lstep.
    destruct (Z.eq_dec (bv_unsigned b) c) as [E|E].
    + brF K0. lstep.
      assert (ER : strchr_res s c str = s) by (unfold strchr_res; rewrite (find_byte_charact c str 0 b Hnth E) by (intros j bj Hj; lia); lia).
      apply evt_done. unfold leaf_post. rewrite ER. do 14 eexists. exists m.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM| exact MI].
    + brT K0.
      apply (istrchr_loop (length str) 0 s c str); try assumption; try lia.
      all: first [ (f_equal; lia) | (intros j bj Hj; lia) | (rewrite Z.add_0_r; exact Hb) ].
Qed.
