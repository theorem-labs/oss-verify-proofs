(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim StoreOk Hoare RefMemcpyLib.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Pm8RegionPoisoned Pm8AsanMemcpy Pm8MemcpyIcpt.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import MState Mem Exec Frame.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Bridge Require Import BrRegs BrXfer.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJM Require Import BrCanon.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.F8 Require Import F_memcpy.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Lemma evt_of_cat_run : forall (Q : machine_state -> Prop) R F pc fc m ro regs' pc' M',
  rcanon R ->
  CatSim.msteps rsegs (MS R F pc fc None m ro) (MS regs' F pc' fc None M' ro) ->
  Q (MS (canon_regs regs') F pc' fc None M' ro) ->
  evt rsegs Q (MS R F pc fc None m ro).
Proof.
  intros Q R F pc fc m ro regs' pc' M' HR Hrun HQ.
  pose proof (msteps_canon rsegs _ _ Hrun HR) as HC. cbn [ms_regs MS] in HC. unfold rcanon in HC. rewrite <- HC in HQ.
  exists (MS regs' F pc' fc None M' ro). split; [apply cat_msteps_cj; exact Hrun | exact HQ].
Qed.

Section MC.

Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Variable F : bvmap 5 word.
Variable fc : bv 32.
Variable m : word -> option byte.
Variable bs : list byte.
Variables kS kD : Z.

Notation pd := (bv_unsigned a0).
Notation ps := (bv_unsigned a1).
Notation n := (bv_unsigned a2).
Notation s := (bv_unsigned sp).
Definition fS : Z := (Pm8RegionPoisoned.SB + bv_unsigned a1 / 8)%Z.
Definition lS : Z := (Pm8RegionPoisoned.SB + (bv_unsigned a1 + bv_unsigned a2 - 1) / 8)%Z.
Definition fD : Z := (Pm8RegionPoisoned.SB + bv_unsigned a0 / 8)%Z.
Definition lD : Z := (Pm8RegionPoisoned.SB + (bv_unsigned a0 + bv_unsigned a2 - 1) / 8)%Z.

Hypothesis Hn : (0 <= n <= 2 ^ 40)%Z.
Hypothesis HappS : Pm8AsanMemcpy.in_app8 ps n.
Hypothesis HappD : Pm8AsanMemcpy.in_app8 pd n.
Hypothesis Hs : (0x1000000 <= s - 2232)%Z /\ (s < 2 ^ 64)%Z.
Hypothesis HshS : (lS + 8 <= s - 2232)%Z.
Hypothesis HshD : (lD + 8 <= s - 2232)%Z.
Hypothesis HdjS : (0 < n -> ps + n <= s - 2232 \/ s <= ps)%Z.
Hypothesis HdjD : (0 < n -> pd + n <= s - 2232 \/ s <= pd)%Z.
Hypothesis Hover : (pd + n <= ps \/ ps + n <= pd)%Z.
Hypothesis Hok : store_ok rsegs m (Z_to_bv 64 (s - 2232)) 2232%nat = true.
Hypothesis Hdst : store_ok rsegs m (Z_to_bv 64 pd) (Z.to_nat n) = true.
Hypothesis Hsrc : rdn rsegs m (Z_to_bv 64 ps) (Z.to_nat n) = Some bs.
Hypothesis Hret : ret_ok ra.
Hypothesis HG : Pm8RegionPoisoned.rt_layout_globs m.
Hypothesis HI : Pm8AsanMemcpy.mc_icpt_globs m.
Hypothesis HZS : (0 < n)%Z -> forall x : word, (fS <= bv_unsigned x < lS)%Z -> m x = Some (Z_to_bv 8 0).
Hypothesis HLS : (0 < n)%Z -> m (Z_to_bv 64 lS) = Some (Z_to_bv 8 kS).
Hypothesis HkS : kS = 0%Z \/ ((ps + n - 1) mod 8 < kS <= 7)%Z.
Hypothesis HWS : (0 < n <= 64)%Z -> exists w0 w1, rdn rsegs m (Z_to_bv 64 (fS - fS mod 8)) 8%nat = Some w0 /\ rdn rsegs m (Z_to_bv 64 (lS - lS mod 8)) 8%nat = Some w1.
Hypothesis HZD : (0 < n)%Z -> forall x : word, (fD <= bv_unsigned x < lD)%Z -> m x = Some (Z_to_bv 8 0).
Hypothesis HLD : (0 < n)%Z -> m (Z_to_bv 64 lD) = Some (Z_to_bv 8 kD).
Hypothesis HkD : kD = 0%Z \/ ((pd + n - 1) mod 8 < kD <= 7)%Z.
Hypothesis HWD : (0 < n <= 64)%Z -> exists w0 w1, rdn rsegs m (Z_to_bv 64 (fD - fD mod 8)) 8%nat = Some w0 /\ rdn rsegs m (Z_to_bv 64 (lD - lD mod 8)) 8%nat = Some w1.

Notation R0 := (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).

Definition icpt_memcpy_raw : machine_state -> Prop :=
  fun ms' => exists regs' Mj,
    ms' = MS (canon_regs regs') F ra fc None (wbytes Mj (Z_to_bv 64 pd) bs) (seg_rom rsegs)
    /\ getr regs' 10 = Z_to_bv 64 pd /\ getr regs' 2 = sp /\ getr regs' 1 = ra /\ keeps_cs R0 regs'
    /\ (forall x : word, (bv_unsigned x < s - 2232 \/ s <= bv_unsigned x)%Z -> Mj x = m x) /\ mem_grows m Mj.

Lemma icpt_memcpy_call_raw :
  evt rsegs icpt_memcpy_raw (MS R0 F (Z_to_bv 64 0x7ee70) fc None m (seg_rom rsegs)).
Proof.
  pose (fx := mkFP F fc).
  assert (A1 : getr R0 10 = Z_to_bv 64 pd) by (cbn; symmetry; apply Z_to_bv_bv_unsigned).
  assert (A2 : getr R0 11 = Z_to_bv 64 ps) by (cbn; symmetry; apply Z_to_bv_bv_unsigned).
  assert (A3 : getr R0 12 = Z_to_bv 64 n) by (cbn; symmetry; apply Z_to_bv_bv_unsigned).
  destruct (@Pm8MemcpyIcpt.wrap_memcpy_run fx m (seg_rom rsegs) sp ra pd ps n s bs kS fS lS (fS - fS mod 8) (lS - lS mod 8)
              kD fD lD (fD - fD mod 8) (lD - lD mod 8)
              eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
              Hn HappS HappD Hs HshS HshD HdjS HdjD Hover Hok Hdst Hsrc Hret HG HI HZS HLS HkS HWS HZD HLD HkD HWD
              R0 A1 A2 A3 eq_refl eq_refl)
    as (regs' & Mj & RUN & E10 & E2 & E1 & KCS & OUT & GR).
  assert (EPC : Z_to_bv 64 0x7ee70 = (0x7ee70 : word)) by (apply bv_eq; reflexivity).
  rewrite EPC.
  change (CatSim.msteps rsegs (MS R0 F (0x7ee70 : word) fc None m (seg_rom rsegs))
                        (MS regs' F ra fc None (wbytes Mj (Z_to_bv 64 pd) bs) (seg_rom rsegs))) in RUN.
  eapply evt_of_cat_run; [apply rcanon_mkR | exact RUN | ].
  exists regs', Mj. repeat split; assumption.
Qed.
End MC.
