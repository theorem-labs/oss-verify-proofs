(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac ITree Nodes Decode SysStep RzCPS NodesA. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import I_lkit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout R_small R_m2s I_consts I_qck RT_iface D_defs D_kit D_clx I_memcpyw I_memsetw I_memchrw I_strnlenw I_read I_lift I_strlenw I_strlen I_strncmpw I_lift2
     RT_state RT_rep RT_facts RT_artfacts RT_icfacts RT_iclifts RT_icfacts2 R_isPoisoned.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import I_strcpyA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRtA Require Import F_strcpyA I_strcpyw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Section Lift.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RIP : rip_stmt.
Hypothesis AF_IC : forall Σ m, ART RT Σ m -> icells m /\ icells_ms m /\ icells_mc m /\ icells_sn m /\ m2s_cells m.
Hypothesis AF_SHW : forall Σ m p n, ART RT Σ m -> 0 < n -> rng_class RT Σ p n -> qc_words m p n /\ region_in_mem p n.
Hypothesis AF_CP : forall Σ m, ART RT Σ m -> icells_cp m.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, kHighShadowEnd in *; lia.

Theorem strcpy_lift : strcpy_icontract RT.
Proof using AF RIP AF_IC AF_SHW AF_CP.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d s str slack lo
    FDO MST -> -> STR NZ L40 PAD S0 D0 SEPS CSRC CDST OV ART0 MI0 CALL.
  intros T cf Hc Hk.
  set (len := Z.of_nat (length str)) in *.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  destruct CALL as (ST & LOW & LOR & SPT & SPA).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  destruct (AF_IC Σ m ART0) as (_ & _ & _ & ICS & M2S).
  pose proof (AF_CP Σ m ART0) as ICP.
  destruct CSRC as (CS & _). destruct CDST as (CD & DCL & DWR).
  assert (CHS : chk_ok m s (len + 1)) by (apply (chk_ok_of RT AF_SHW Σ m s _ ART0); [lia| exact CS]).
  assert (CHD : chk_ok m d (len + 1)) by (apply (chk_ok_of RT AF_SHW Σ m d _ ART0); [lia| exact CD]).
  destruct (wr_at_rw_CB m d (len + 1) DWR ltac:(lia)) as (junk & DST).
  assert (EN : Z.to_nat (len + 1) = (length str + 1)%nat) by (unfold len; lia). rewrite EN in DST. clear EN.
  assert (SEPD : d + len + 1 <= lo \/ usp <= d).
  { destruct (range_side d (len + 1) lo usp); [| ul| lia| right; lia| left; lia].
    intros i Hi. destruct (aclient_split RT AF Σ m usp (d + i) ART0 (DCL i Hi)); [left; lia| right; ul]. }
  assert (RS : s + len + 1 <= 2^47).
  { destruct CHS as (_ & _ & RO). destruct (RO ltac:(lia)) as (RIM & _).
    unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIM. lia. }
  assert (RD : d + len + 1 <= 2^47).
  { destruct CHD as (_ & _ & RO). destruct (RO ltac:(lia)) as (RIM & _).
    unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIM. lia. }
  assert (W1 : evt ctasegs (iscpy_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc d str
                              [(d, d + len + 1); (bv_unsigned (Z_to_bv 64 usp) - 2224, bv_unsigned (Z_to_bv 64 usp))] lo m)
                 (entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 s) a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_strcpy m)).
  { unfold entry_st, e_strcpy. rewrite ESP.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
    lstep.
    eapply evt_mono; [apply (iscpy_spec RIP) with (s := s) (d := d) (str := str) (slack := slack) (junk := junk) (lo := lo); try reflexivity; try assumption;
                        rewrite ?(unsigned_lit usp) by ul; try ul; try assumption |].
    intros ms PO. unfold iscpy_post in PO |- *. rewrite ?(unsigned_lit usp) in PO by ul. rewrite ?(unsigned_lit usp) by ul. exact PO. }
  lazymatch type of W1 with evt ctasegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt ctasegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes ctasegs _ _ _ cf (asta_evt' RT AF Σ PMc _ _ MST W1') Hc). intros c1 Hc1. apply Hk.
  unfold icpt_post. eapply ASTA_conseq; [exact Hc1|]. intros ms PO.
  unfold iscpy_post in PO.
  destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI & ST' & DC).
  rewrite ?(unsigned_lit usp) in MU by ul. rewrite ?(unsigned_lit usp) in ST' by ul.
  destruct (icpt_after RT AF Σ m m' usp lo _ d (len + 1) ART0 LOW ltac:(ul) ltac:(ul) MU WM) as (ART' & PRES).
  { intros x (l & h & Hin & Hx). cbn in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-; [left; lia| right; ul]. }
  { intros i Hi. apply DCL. exact Hi. }
  exists m'. split; [rewrite ESP; do 16 eexists; reflexivity|].
  split; [split; [exact ART'| split; [exact MI| split; [exact WM| exact ST']]]|].
  split; [exact PRES|].
  destruct DC as [[_ DB] _]. cbn [cells_bytes cbytes] in DB. rewrite app_nil_r in DB. exact DB.
Qed.

End Lift.

(* [comment removed for export] *)
Lemma rta_cp : forall Σ m, ART RTA Σ m -> icells_cp m.
Proof.
  intros Σ m HA. split; [exact (rta_real_strcpy Σ m HA)|].
  pose proof (ART_consts Σ m HA) as (_ & _ & _ & _ & _ & _ & _ & IC). unfold icells_rep in IC.
  repeat lazymatch type of IC with _ /\ _ => let X := fresh "X" in destruct IC as [X IC] end.
  split; lazymatch goal with |- ?G => match goal with H : G |- _ => exact H end end.
Qed.

Theorem rta_strcpy : strcpy_icontract RTA.
Proof. exact (strcpy_lift RTA rta_art_facts rip_proof rta_ic rta_shw rta_cp). Qed.
