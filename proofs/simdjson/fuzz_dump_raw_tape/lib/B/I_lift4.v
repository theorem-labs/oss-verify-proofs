(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac ITree Nodes Decode SysStep ImageA RzCPS NodesA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import I_lkit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout R_small R_m2s I_consts I_qck RT_iface D_defs D_kit D_clx I_memchrw I_lift F_memcmp I_memcmpw I_memcmp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Section Lift4.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RIP : rip_stmt.
Hypothesis AF_CMP : forall Σ m, ART RT Σ m -> icells_cmp m /\ m2s_cells m.
Hypothesis AF_SHW : forall Σ m p n, ART RT Σ m -> 0 < n -> rng_class RT Σ p n -> qc_words m p n /\ region_in_mem p n.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, kHighShadowEnd in *; lia.

Theorem memcmp_lift : memcmp_icontract RT.
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
  assert (W1 : evt bsegs (cmp_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc bp bq 4640 lo m)
                 (entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 q) (Z_to_bv 64 n) a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_memcmp m)).
  { unfold entry_st, e_memcmp. rewrite ESP.
    pose proof (ibcmp_spec RIP) as IB. unfold cmp_fn in IB.
    apply IB with (p := p) (q := q) (bp := bp) (bq := bq) (lo := lo); try reflexivity; try assumption; rewrite ?(unsigned_lit usp) by ul; fold n; try ul; try assumption. }
  lazymatch type of W1 with evt bsegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ cf (asta_evt' RT AF Σ PMc _ _ MST W1') Hc). intros c1 Hc1. apply Hk.
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

End Lift4.
