(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare RefMemcpyLib MemsetLib.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Pm5RegionPoisoned Pm5AsanMemset Pm5AsanMemcpy Pm5MemsetIcpt.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import MState Mem Exec Frame.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Bridge Require Import BrRegs BrXfer.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJMXB Require Import BrCanon IcptMemcpyC.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F5 Require Import F_memcpy.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section MS.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Variable F : bvmap 5 word.
Variable fc : bv 32.
Variable m : word -> option byte.
Variable kD : Z.

Notation pd := (bv_unsigned a0).
Notation n := (bv_unsigned a2).
Notation s := (bv_unsigned sp).
Definition fDs : Z := (Pm5RegionPoisoned.SB + bv_unsigned a0 / 8)%Z.
Definition lDs : Z := (Pm5RegionPoisoned.SB + (bv_unsigned a0 + bv_unsigned a2 - 1) / 8)%Z.

Hypothesis Hn : (0 <= n <= 2 ^ 40)%Z.
Hypothesis HappD : Pm5AsanMemcpy.in_app8 pd n.
Hypothesis Hs : (0x1000000 <= s - 2216)%Z /\ (s < 2 ^ 64)%Z.
Hypothesis HshD : (lDs + 8 <= s - 2216)%Z.
Hypothesis HdjD : (0 < n -> pd + n <= s - 2216 \/ s <= pd)%Z.
Hypothesis Hok : store_ok rsegs m (Z_to_bv 64 (s - 2216)) 2216%nat = true.
Hypothesis Hdst : store_ok rsegs m (Z_to_bv 64 pd) (Z.to_nat n) = true.
Hypothesis Hret : ret_ok ra.
Hypothesis HG : Pm5RegionPoisoned.rt_layout_globs m.
Hypothesis HI : Pm5AsanMemset.ms_icpt_globs m.
Hypothesis HZD : (0 < n)%Z -> forall x : word, (fDs <= bv_unsigned x < lDs)%Z -> m x = Some (Z_to_bv 8 0).
Hypothesis HLD : (0 < n)%Z -> m (Z_to_bv 64 lDs) = Some (Z_to_bv 8 kD).
Hypothesis HkD : kD = 0%Z \/ ((pd + n - 1) mod 8 < kD <= 7)%Z.
Hypothesis HWD : (0 < n <= 64)%Z -> exists w0 w1, rdn rsegs m (Z_to_bv 64 (fDs - fDs mod 8)) 8%nat = Some w0 /\ rdn rsegs m (Z_to_bv 64 (lDs - lDs mod 8)) 8%nat = Some w1.

Notation R0 := (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).

Definition icpt_memset_raw : machine_state -> Prop :=
  fun ms' => exists regs' Mj,
    ms' = MS (canon_regs regs') F ra fc None (wbytes Mj (Z_to_bv 64 pd) (repeat (cbyte a1) (Z.to_nat n))) (seg_rom rsegs)
    /\ getr regs' 10 = Z_to_bv 64 pd /\ getr regs' 2 = sp /\ getr regs' 1 = ra /\ keeps_cs R0 regs'
    /\ (forall x : word, (bv_unsigned x < s - 2216 \/ s <= bv_unsigned x)%Z -> Mj x = m x) /\ mem_grows m Mj.

Lemma icpt_memset_call_raw :
  evt rsegs icpt_memset_raw (MS R0 F (Z_to_bv 64 0x80b04) fc None m (seg_rom rsegs)).
Proof.
  pose (fx := mkFP F fc).
  assert (A1 : getr R0 10 = Z_to_bv 64 pd) by (cbn; symmetry; apply Z_to_bv_bv_unsigned).
  assert (A2 : getr R0 11 = a1) by reflexivity.
  assert (A3 : getr R0 12 = Z_to_bv 64 n) by (cbn; symmetry; apply Z_to_bv_bv_unsigned).
  destruct (@Pm5MemsetIcpt.wrap_memset_run fx m (seg_rom rsegs) sp ra a1 pd n s kD fDs lDs (fDs - fDs mod 8) (lDs - lDs mod 8)
              eq_refl eq_refl eq_refl eq_refl eq_refl
              Hn HappD Hs HshD HdjD Hok Hdst Hret HG HI HZD HLD HkD HWD
              R0 A1 A2 A3 eq_refl eq_refl)
    as (regs' & Mj & RUN & E10 & E2 & E1 & KCS & OUT & GR).
  assert (EPC : Z_to_bv 64 0x80b04 = (0x80b04 : word)) by (apply bv_eq; reflexivity).
  rewrite EPC.
  change (CatSim.msteps rsegs (MS R0 F (0x80b04 : word) fc None m (seg_rom rsegs))
                        (MS regs' F ra fc None (wbytes Mj (Z_to_bv 64 pd) (repeat (cbyte a1) (Z.to_nat n))) (seg_rom rsegs))) in RUN.
  eapply evt_of_cat_run; [apply rcanon_mkR | exact RUN | ].
  exists regs', Mj. repeat split; assumption.
Qed.
End MS.
