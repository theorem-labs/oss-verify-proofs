(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import I_lkit.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import R_small R_m2s I_consts I_qck RT_iface D_defs D_kit D_clx.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import I_memcpyw I_memsetw I_memchrw I_strnlenw I_read I_lift I_strcmp_spec I_strcmpw I_strcmpw2 I_strcmp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition e_strcmp : Z := 0x514a0.       (* [comment removed for export] *)

Section Contract.
Variable RT : rt_sig.

(* [comment removed for export] *)
Definition strcmp_icontract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (p1 p2 : Z) (b1 b2 : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 p1 -> a1 = Z_to_bv 64 p2 ->
  Z.of_nat (length b1) < 2^40 -> Z.of_nat (length b2) < 2^40 ->
  bytes_at asegs m p1 b1 -> bytes_at asegs m p2 b2 -> strcmp_ok b1 b2 ->
  checked_src RT Σ m sp lo p1 (strcmp_sz b1 b2) -> checked_src RT Σ m sp lo p2 (strcmp_sz b1 b2) ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_strcmp m)))
    (icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (strcmp_res b1 b2)) lo 0 0 m
               (fun _ => True)).

Hypothesis AF : art_facts RT.
Hypothesis RIP : rip_stmt.
Hypothesis AF_IC : forall Σ m, ART RT Σ m -> icells m /\ icells_ms m /\ icells_mc m /\ icells_sn m /\ m2s_cells m.
Hypothesis AF_SHW : forall Σ m p n, ART RT Σ m -> 0 < n -> rng_class RT Σ p n -> qc_words m p n /\ region_in_mem p n.
Hypothesis AF_SCMP : forall Σ m, ART RT Σ m -> icells_scmp m.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, kHighShadowEnd in *; lia.

Theorem strcmp_lift : strcmp_icontract.
Proof using AF RIP AF_IC AF_SHW AF_SCMP.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p1 p2 b1 b2 lo
    FDO MST -> -> L1 L2 BS1 BS2 OK CSRC1 CSRC2 ART0 MI0 CALL.
  intros T c Hc Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  destruct CALL as (ST & LOW & LOR & SPT & SPA).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  destruct (AF_IC Σ m ART0) as (_ & _ & _ & _ & M2S).
  pose proof (AF_SCMP Σ m ART0) as ISC.
  set (sz := strcmp_sz b1 b2) in *.
  assert (SZ1 : 1 <= sz) by (unfold sz, strcmp_sz, strcmp_idx; lia).
  assert (SZL : sz <= 2^40) by (destruct OK as [OK1 _]; fold sz in OK1; lia).
  destruct CSRC1 as (C1 & SEP1). destruct CSRC2 as (C2 & SEP2).
  assert (CH1 : chk_ok m p1 sz) by (apply (chk_ok_of RT AF_SHW Σ m p1 sz ART0); [lia| exact C1]).
  assert (CH2 : chk_ok m p2 sz) by (apply (chk_ok_of RT AF_SHW Σ m p2 sz ART0); [lia| exact C2]).
  assert (R1 : p1 + sz <= 2^47).
  { destruct CH1 as (_ & _ & RO). destruct (RO ltac:(lia)) as (RIM & _).
    unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIM. lia. }
  assert (R2 : p2 + sz <= 2^47).
  { destruct CH2 as (_ & _ & RO). destruct (RO ltac:(lia)) as (RIM & _).
    unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIM. lia. }
  assert (W1 : evt asegs (istrcmp_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                            (strcmp_res b1 b2) lo m)
                 (entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p1) (Z_to_bv 64 p2) a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_strcmp m)).
  { unfold entry_st, e_strcmp. rewrite ESP.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    lstep.
    apply (istrcmp_spec RIP) with (p1 := p1) (p2 := p2); try reflexivity; try assumption;
      rewrite ?(unsigned_lit usp) by ul; try ul; try assumption. }
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ c (asta_evt' RT AF Σ PMc _ _ MST W1') Hc). intros c1 Hc1. apply Hk.
  unfold icpt_post. eapply ASTA_conseq; [exact Hc1|]. intros ms PO.
  unfold istrcmp_post in PO.
  destruct PO as (u0 & u1 & u2 & b3 & b4 & b5 & b6 & b7 & b8 & b9 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI & ST').
  rewrite (unsigned_lit usp) in MU, ST' by ul.
  destruct (icpt_after RT AF Σ m m' usp lo _ 0 0 ART0 LOW ltac:(ul) ltac:(ul) MU WM) as (ART' & PRES).
  { intros x (l & h & Hin & Hx). cbn in Hin. destruct Hin as [E|[]]. injection E as <- <-. right; ul. }
  { intros i Hi. lia. }
  exists m'. split; [rewrite ESP; do 16 eexists; reflexivity|].
  split; [split; [exact ART'| split; [exact MI| split; [exact WM| exact ST']]]|].
  split; [exact PRES| exact I].
Qed.

End Contract.
