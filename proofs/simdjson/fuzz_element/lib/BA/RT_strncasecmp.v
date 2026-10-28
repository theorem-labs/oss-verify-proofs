(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout R_small R_m2s R_thread I_consts I_qck RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface5. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import I_memcmpw I_lift R_strncasecmp RT_state RT_rep RT_facts0 RT_facts RT_artfacts RT_icfacts R_isPoisoned RT_iclifts.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

Section Lift.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RIP : rip_stmt.
Hypothesis AF_SCA : forall Σ m, ART RT Σ m -> icells_sca m /\ m2s_cells m.
Hypothesis AF_SHW : forall Σ m p n, ART RT Σ m -> 0 < n -> rng_class RT Σ p n -> qc_words m p n /\ region_in_mem p n.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, kHighShadowEnd in *; lia.

Theorem strncasecmp_lift : strncasecmp_icontract RT.
Proof using AF RIP AF_SCA AF_SHW.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p q n bp bq lo
    FDO MST -> -> -> P0 Q0 NR BP BQ FP FQ k LP LQ CSP CSQ ART0 MI0 CALL.
  intros T cf Hc Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  destruct CALL as (ST & LOW & LOR & SPT & SPA).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  destruct (AF_SCA Σ m ART0) as (ICC & M2S).
  destruct CSP as (CP & SEPP). destruct CSQ as (CQ & SEPQ).
  assert (K0 : 0 <= k <= n) by (unfold k; lia).
  assert (CHP : chk_ok m p k) by (apply (chk_ok_of RT AF_SHW Σ m p k ART0); [lia| exact CP]).
  assert (CHQ : chk_ok m q k) by (apply (chk_ok_of RT AF_SHW Σ m q k ART0); [lia| exact CQ]).
  assert (RP : p + k <= 2^47).
  { destruct (Z.eq_dec k 0) as [->|NZ]; [lia|].
    destruct CHP as (_ & _ & RO). destruct (RO ltac:(lia)) as (RIM & _). unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIM. lia. }
  assert (RQ : q + k <= 2^47).
  { destruct (Z.eq_dec k 0) as [->|NZ]; [lia|].
    destruct CHQ as (_ & _ & RO). destruct (RO ltac:(lia)) as (RIM & _). unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIM. lia. }
  assert (W1 : evt asegs (frame_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (scase_res bp bq (Z.to_nat n))
                            [(usp - 2256, usp)] lo m)
                 (entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 q) (Z_to_bv 64 n) a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_strncasecmp m)).
  { unfold entry_st. rewrite ESP.
    pose proof (istrncasecmp_spec RIP ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 q) (Z_to_bv 64 n) a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p q n bp bq lo eq_refl eq_refl eq_refl) as SPEC.
    rewrite (unsigned_lit usp) in SPEC by ul. cbv zeta in SPEC. fold k in SPEC.
    apply SPEC; try assumption; try ul. all: left; ul. }
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ cf (asta_evt' RT AF Σ PMc _ _ MST W1') Hc). intros c1 Hc1. apply Hk.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & PO & Hc1').
  unfold frame_post in PO.
  destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI & ST').
  rewrite (unsigned_lit usp) in ST' by ul.
  destruct (icpt_after RT AF Σ m m' usp lo _ 0 0 ART0 LOW ltac:(ul) ltac:(ul) MU WM) as (ART' & PRES).
  { intros x (l & h & Hin & Hx). cbn in Hin. destruct Hin as [E|[]]; injection E as <- <-. right; ul. }
  { intros i Hi. lia. }
  unfold icpt_postF. eapply (ASTA_conseq RT); [exact Hc1'|]. intros ms <-.
  exists m'. split; [rewrite ESP; do 15 eexists; reflexivity|].
  split; [split; [exact ART'| split; [exact MI| split; [exact WM| exact ST']]]|].
  split; [exact PRES| exact I].
Qed.

Theorem strncasecmp0_lift : strncasecmp0_icontract RT.
Proof using AF RIP AF_SCA AF_SHW.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    FDO MST -> ART0 MI0 CALL.
  intros T cf Hc Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  destruct CALL as (ST & LOW & LOR & SPT & SPA).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  destruct (AF_SCA Σ m ART0) as (ICC & M2S).
  set (p := bv_unsigned a0). set (q := bv_unsigned a1).
  pose proof (bv_unsigned_in_range 64 a0) as RP. pose proof (bv_unsigned_in_range 64 a1) as RQ. unfold bv_modulus in RP, RQ. cbn [Z.pow_pos Pos.iter Z.mul Z.of_N] in RP, RQ.
  assert (EP : a0 = Z_to_bv 64 p) by (symmetry; apply Z_to_bv_bv_unsigned). assert (EQ : a1 = Z_to_bv 64 q) by (symmetry; apply Z_to_bv_bv_unsigned).
  assert (W1 : evt asegs (frame_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (scase_res [] [] (Z.to_nat 0))
                            [(usp - 2256, usp)] lo m)
                 (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 0) a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_strncasecmp m)).
  { unfold entry_st. rewrite ESP, EP, EQ.
    pose proof (istrncasecmp_spec RIP ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 q) (Z_to_bv 64 0) a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p q 0 [] [] lo eq_refl eq_refl eq_refl) as SPEC.
    rewrite (unsigned_lit usp) in SPEC by ul. cbv zeta in SPEC. cbn [scase_idx Z.to_nat Z.of_nat Z.min Z.add length] in SPEC.
    apply SPEC; try assumption; try ul; try (apply bytes_at_nil; ul); try (apply Forall_nil); try (right; right; reflexivity).
    all: apply chk_ok_zero; reflexivity. }
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ cf (asta_evt' RT AF Σ PMc _ _ MST W1') Hc). intros c1 Hc1. apply Hk.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & PO & Hc1').
  unfold frame_post in PO.
  destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI & ST').
  rewrite (unsigned_lit usp) in ST' by ul.
  destruct (icpt_after RT AF Σ m m' usp lo _ 0 0 ART0 LOW ltac:(ul) ltac:(ul) MU WM) as (ART' & PRES).
  { intros x (l & h & Hin & Hx). cbn in Hin. destruct Hin as [E|[]]; injection E as <- <-. right; ul. }
  { intros i Hi. lia. }
  unfold icpt_postF. eapply (ASTA_conseq RT); [exact Hc1'|]. intros ms <-.
  exists m'. split; [rewrite ESP; do 15 eexists; reflexivity|].
  split; [split; [exact ART'| split; [exact MI| split; [exact WM| exact ST']]]|].
  split; [exact PRES| exact I].
Qed.

End Lift.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A.Shadow.GW}.

Lemma rta_sca : forall Σ m, ART RTA Σ m -> icells_sca m /\ m2s_cells m.
Proof.
  intros Σ m HA.
  pose proof (ART_consts Σ m HA) as (_ & (_ & G2 & _) & _ & MC & _ & _ & _ & (_ & SSC & _)).
  pose proof (ART_fs Σ m HA) as (_ & _ & _ & _ & _ & _ & (_ & _ & (T1 & _)) & _).
  pose proof MC as (M1 & M2 & M3).
  split; [| exact MC].
  split; [exact (ro_of_rw _ _ _ G2)|].
  split; [exact (ro_head _ _ _ _ (ro_of_rw _ _ _ M1))|].
  split; [exact (ro_of_rw _ _ _ M2)|].
  split; [exact T1| exact SSC].
Qed.

Theorem rta_strncasecmp : strncasecmp_icontract RTA.
Proof. exact (strncasecmp_lift RTA rta_art_facts rip_proof rta_sca rta_shw). Qed.
Theorem rta_strncasecmp0 : strncasecmp0_icontract RTA.
Proof. exact (strncasecmp0_lift RTA rta_art_facts rip_proof rta_sca rta_shw). Qed.

End GWIN.
