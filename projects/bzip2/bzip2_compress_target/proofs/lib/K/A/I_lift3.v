(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Tac ImageA SysStep RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Str_tac Startup_glue.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Shadow IcptSpec IcptSpec2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout R_small R_m2s R_thread I_consts I_qck I_lkit RT_iface D_defs D_kit I_lift F_memcmp I_memcmpw I_memcmp.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA SysStep RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow IcptSpec IcptSpec2.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_small.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_m2s.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_thread.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_consts.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_qck.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_lkit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_lift.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_memcmp.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_memcmpw.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_memcmp.TwinB__.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Section Lift3.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RIP : rip_stmt.
Hypothesis AF_ICC : forall Σ m, ART RT Σ m -> icells_cmp m /\ m2s_cells m.
Hypothesis AF_SHW : forall Σ m p n, ART RT Σ m -> 0 < n -> rng_class RT Σ p n -> qc_words m p n /\ region_in_mem p n.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, kHighShadowEnd in *; lia.

Theorem memcmp_lift : memcmp_icontract RT.
Proof using AF RIP AF_ICC AF_SHW.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p1 p2 b1 b2 lo
    FDO MST -> -> -> P1 P2 HL HN B1 B2 CSRC1 CSRC2 ART0 MI0 CALL.
  intros T cf Hc Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  destruct CALL as (ST & LOW & LOR & SPT & SPA).
  set (usp := bv_unsigned sp) in *. set (n := Z.of_nat (length b1)) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  destruct (AF_ICC Σ m ART0) as (ICC & M2S).
  destruct CSRC1 as (CS1 & SEP1). destruct CSRC2 as (CS2 & SEP2).
  assert (CH1 : chk_ok m p1 n) by (apply (chk_ok_of RT AF_SHW Σ m p1 n ART0); [unfold n; lia | exact CS1]).
  assert (CH2 : chk_ok m p2 n) by (apply (chk_ok_of RT AF_SHW Σ m p2 n ART0); [unfold n; lia | exact CS2]).
  assert (R1 : p1 + n <= 2^47).
  { destruct (Z.eq_dec n 0) as [E|NE]; [lia|]. destruct CH1 as (_ & _ & RO). destruct (RO ltac:(unfold n in *; lia)) as (RIM & _).
    unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIM. lia. }
  assert (R2 : p2 + n <= 2^47).
  { destruct (Z.eq_dec n 0) as [E|NE]; [lia|]. destruct CH2 as (_ & _ & RO). destruct (RO ltac:(unfold n in *; lia)) as (RIM & _).
    unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIM. lia. }
  assert (CA : cmp_args m usp lo p1 p2 b1 b2).
  { unfold cmp_args. fold n. split; [exact HL|]. split; [exact HN|]. split; [lia|]. split; [exact R1|]. split; [lia|]. split; [exact R2|].
    split; [exact B1|]. split; [exact B2|]. split; [exact SEP1|]. split; [exact SEP2|]. split; [exact CH1|]. split; [exact CH2|]. split; [exact M2S | exact ICC]. }
  assert (W1 : evt bsegs (frame_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (memcmp_res b1 b2)
                            [(bv_unsigned (Z_to_bv 64 usp) - 4560, bv_unsigned (Z_to_bv 64 usp))] lo m)
                 (entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p1) (Z_to_bv 64 p2) (Z_to_bv 64 n) a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_memcmp m)).
  { unfold entry_st, e_memcmp. rewrite ESP.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    lstep.
    pose proof (imemcmp_spec RIP) as IS. unfold cmp_stmt in IS.
    eapply evt_mono; [apply (IS ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p1 p2 lo b1 b2);
                      rewrite ?(unsigned_lit usp) by ul; try assumption; try ul|].
    intros ms' PO. rewrite (unsigned_lit usp) in PO by ul. exact PO. }
  lazymatch type of W1 with evt bsegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ cf (asta_evt' RT AF Σ PMc _ _ MST W1') Hc). intros c1 Hc1. apply Hk.
  unfold icpt_post. eapply ASTA_conseq; [exact Hc1|]. intros ms PO.
  unfold frame_post in PO.
  destruct PO as (u0 & u1 & u2 & c1' & c2' & c3' & c4' & c5' & c6' & c7' & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI & ST').
  rewrite (unsigned_lit usp) in MU, ST' by ul.
  destruct (icpt_after RT AF Σ m m' usp lo _ 0 0 ART0 LOW ltac:(ul) ltac:(ul) MU WM) as (ART' & PRES).
  { intros x (l & h & Hin & Hx). cbn in Hin. destruct Hin as [E|[]]; injection E as <- <-. right; ul. }
  { intros i Hi. lia. }
  exists m'. split; [rewrite ESP; do 16 eexists; reflexivity|].
  split; [split; [exact ART'| split; [exact MI| split; [exact WM| exact ST']]]|].
  split; [exact PRES| exact I].
Qed.

End Lift3.
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA SysStep RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout Shadow R_small R_m2s R_thread I_consts I_qck I_lkit IcptSpec IcptSpec2 RT_iface D_defs D_kit
  I_lift F_memcmp I_memcmpw I_memcmp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Section Lift3.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RIP : rip_stmt.
Hypothesis AF_ICC : forall Σ m, ART RT Σ m -> icells_cmp m /\ m2s_cells m.
Hypothesis AF_SHW : forall Σ m p n, ART RT Σ m -> 0 < n -> rng_class RT Σ p n -> qc_words m p n /\ region_in_mem p n.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, kHighShadowEnd in *; lia.

Theorem memcmp_lift : memcmp_icontract RT.
Proof using AF RIP AF_ICC AF_SHW.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p1 p2 b1 b2 lo
    FDO MST -> -> -> P1 P2 HL HN B1 B2 CSRC1 CSRC2 ART0 MI0 CALL.
  intros T cf Hc Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  destruct CALL as (ST & LOW & LOR & SPT & SPA).
  set (usp := bv_unsigned sp) in *. set (n := Z.of_nat (length b1)) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  destruct (AF_ICC Σ m ART0) as (ICC & M2S).
  destruct CSRC1 as (CS1 & SEP1). destruct CSRC2 as (CS2 & SEP2).
  assert (CH1 : chk_ok m p1 n) by (apply (chk_ok_of RT AF_SHW Σ m p1 n ART0); [unfold n; lia | exact CS1]).
  assert (CH2 : chk_ok m p2 n) by (apply (chk_ok_of RT AF_SHW Σ m p2 n ART0); [unfold n; lia | exact CS2]).
  assert (R1 : p1 + n <= 2^47).
  { destruct (Z.eq_dec n 0) as [E|NE]; [lia|]. destruct CH1 as (_ & _ & RO). destruct (RO ltac:(unfold n in *; lia)) as (RIM & _).
    unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIM. lia. }
  assert (R2 : p2 + n <= 2^47).
  { destruct (Z.eq_dec n 0) as [E|NE]; [lia|]. destruct CH2 as (_ & _ & RO). destruct (RO ltac:(unfold n in *; lia)) as (RIM & _).
    unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIM. lia. }
  assert (CA : cmp_args m usp lo p1 p2 b1 b2).
  { unfold cmp_args. fold n. split; [exact HL|]. split; [exact HN|]. split; [lia|]. split; [exact R1|]. split; [lia|]. split; [exact R2|].
    split; [exact B1|]. split; [exact B2|]. split; [exact SEP1|]. split; [exact SEP2|]. split; [exact CH1|]. split; [exact CH2|]. split; [exact M2S | exact ICC]. }
  assert (W1 : evt asegs (frame_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (memcmp_res b1 b2)
                            [(bv_unsigned (Z_to_bv 64 usp) - 4560, bv_unsigned (Z_to_bv 64 usp))] lo m)
                 (entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p1) (Z_to_bv 64 p2) (Z_to_bv 64 n) a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_memcmp m)).
  { unfold entry_st, e_memcmp. rewrite ESP.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    lstep.
    pose proof (imemcmp_spec RIP) as IS. unfold cmp_stmt in IS.
    eapply evt_mono; [apply (IS ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p1 p2 lo b1 b2);
                      rewrite ?(unsigned_lit usp) by ul; try assumption; try ul|].
    intros ms' PO. rewrite (unsigned_lit usp) in PO by ul. exact PO. }
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ cf (asta_evt' RT AF Σ PMc _ _ MST W1') Hc). intros c1 Hc1. apply Hk.
  unfold icpt_post. eapply ASTA_conseq; [exact Hc1|]. intros ms PO.
  unfold frame_post in PO.
  destruct PO as (u0 & u1 & u2 & c1' & c2' & c3' & c4' & c5' & c6' & c7' & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI & ST').
  rewrite (unsigned_lit usp) in MU, ST' by ul.
  destruct (icpt_after RT AF Σ m m' usp lo _ 0 0 ART0 LOW ltac:(ul) ltac:(ul) MU WM) as (ART' & PRES).
  { intros x (l & h & Hin & Hx). cbn in Hin. destruct Hin as [E|[]]; injection E as <- <-. right; ul. }
  { intros i Hi. lia. }
  exists m'. split; [rewrite ESP; do 16 eexists; reflexivity|].
  split; [split; [exact ART'| split; [exact MI| split; [exact WM| exact ST']]]|].
  split; [exact PRES| exact I].
Qed.

End Lift3.
