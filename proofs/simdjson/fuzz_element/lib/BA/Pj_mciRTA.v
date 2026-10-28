(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac ITree Nodes Decode SysStep ImageA RzCPS NodesA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import I_lkit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout R_small R_m2s I_consts I_qck RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import I_memchrw I_lift F_memcmp I_memcmpw I_memcmp I_lift4 Pj_mciA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_state RT_rep RT_facts RT_artfacts RT_icfacts R_isPoisoned RT_iclifts RT_cli RT_iclifts4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

#[local] Existing Instance OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A.Shadow.GWf.
Section Stub.
Hypothesis RIP : rip_stmt.

Lemma imemcmp_stub_spec : cmp_fn PJ_MEMCMP_STUB_A 2320.
Proof using RIP.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p q bp bq lo
    E0 E1 E2 LEN NZ P0 Q0 PH QH BP BQ SEPP SEPQ CP CQ M2S IC MI ST LO LOLO SPH.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold PJ_MEMCMP_STUB_A. lstep.
  exact (imemcmp_shell_spec RIP 0 ltac:(lia) cmp_fn_musl ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m p q bp bq lo E0 E1 E2 LEN NZ P0 Q0 PH QH BP BQ SEPP SEPQ CP CQ M2S IC MI ST ltac:(lia) LOLO SPH).
Qed.
End Stub.

Section LiftI.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RIP : rip_stmt.
Hypothesis AF_CMP : forall Σ m, ART RT Σ m -> icells_cmp m /\ m2s_cells m.
Hypothesis AF_SHW : forall Σ m p n, ART RT Σ m -> 0 < n -> rng_class RT Σ p n -> qc_words m p n /\ region_in_mem p n.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, kHighShadowEnd in *; lia.

Theorem memcmp_inner_lift : memcmp_inner_icontract RT.
Proof using AF RIP AF_CMP AF_SHW.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p q bp bq lo
    FDO MST -> -> -> LEN P0 Q0 NZ NB BP BQ CSP CSQ ART0 MI0 CALL.
  intros T cf Hc Hk.
  set (n := Z.of_nat (length bp)) in *.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  destruct CALL as (ST & LOW & LOR & SPT & SPA).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  destruct (AF_CMP Σ m ART0) as (ICC & M2S).
  destruct CSP as (CP & SEPP). destruct CSQ as (CQ & SEPQ).
  assert (N1 : 1 <= n) by (unfold n; lia).
  assert (CHP : chk_ok m p n) by (apply (chk_ok_of RT AF_SHW Σ m p n ART0); [lia| exact CP]).
  assert (CHQ : chk_ok m q n) by (apply (chk_ok_of RT AF_SHW Σ m q n ART0); [lia| exact CQ]).
  assert (RP : p + n <= 2^47).
  { destruct CHP as (_ & _ & RO). destruct (RO ltac:(lia)) as (RIM & _). unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIM. lia. }
  assert (RQ : q + n <= 2^47).
  { destruct CHQ as (_ & _ & RO). destruct (RO ltac:(lia)) as (RIM & _). unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIM. lia. }
  assert (W1 : evt asegs (cmp_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc bp bq 2320 lo m)
                 (entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 q) (Z_to_bv 64 n) a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc PJ_MEMCMP_STUB_A m)).
  { unfold entry_st. rewrite ESP.
    pose proof (imemcmp_stub_spec RIP) as IB. unfold cmp_fn in IB.
    apply IB with (p := p) (q := q) (bp := bp) (bq := bq) (lo := lo); try reflexivity; try assumption; rewrite ?(unsigned_lit usp) by ul; fold n; try ul; try assumption. }
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ cf (asta_evt' RT AF Σ PMc _ _ MST W1') Hc). intros c1 Hc1. apply Hk.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & PO & Hc1').
  unfold cmp_post in PO.
  destruct PO as (r & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI & ST' & HR).
  rewrite (unsigned_lit usp) in MU, ST' by ul.
  destruct (icpt_after RT AF Σ m m' usp lo _ 0 0 ART0 LOW ltac:(ul) ltac:(ul) MU WM) as (ART' & PRES).
  { intros x (l & h & Hin & Hx). cbn in Hin. destruct Hin as [E|[]]; injection E as <- <-. right; ul. }
  { intros i Hi. lia. }
  exists r. split; [exact HR|].
  unfold icpt_postF. eapply (ASTA_conseq RT); [exact Hc1'|]. intros ms <-.
  exists m'. split; [rewrite ESP; do 15 eexists; reflexivity|].
  split; [split; [exact ART'| split; [exact MI| split; [exact WM| exact ST']]]|].
  split; [exact PRES| exact I].
Qed.

End LiftI.

Theorem rta_memcmp_inner : memcmp_inner_icontract RTA.
Proof. exact (memcmp_inner_lift RTA rta_art_facts rip_proof rta_cmp rta_shw). Qed.
