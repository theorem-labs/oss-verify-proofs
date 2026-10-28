(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzDefs BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzContracts BzContracts0 BzWalkArith DecCut S0_bzd_out S0_bzd_loop1.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem CmpArith BzCLemmas1.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDOut BzDOK BzDOKp BzDFrame. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF DecTacF.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDFrame OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import S0F_bzd_out.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import S0F_bzd_loop1.
From Stdlib Require Lia. Unset Lia Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzImg0TacF.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLia.
Local Ltac StoreFast.tlia ::= RelLia.tlia_r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.

Section BZD.
  Variable z : bzdctx.
  Hypothesis ZOK : bzdctx_ok z.
  Notation cx := (z_cx z).
  Hypothesis N1 : (1 <= b_n (z_cx z))%Z.
  Hypothesis NN0 : b_small (z_cx z) = 0%Z -> b_tt (z_cx z) <> 0%Z.
  Hypothesis NN1 : b_small (z_cx z) = 1%Z -> b_ll16 (z_cx z) <> 0%Z /\ b_ll4 (z_cx z) <> 0%Z.
  Notation S := (b_s (z_cx z)). Notation STRM := (b_strm (z_cx z)). Notation usp := (bv_unsigned (z_sp z)).
  Notation DST := (b_dst (z_cx z)). Notation dlen := (b_dlen (z_cx z)). Notation lo := (z_lo z). Notation uspi := (bv_unsigned (z_spi z)).

  Ltac zlin :=
    let CX := ident:(CX) in let IA1 := ident:(IA1) in let IA2 := ident:(IA2) in let Z' := fresh "ZOK" in pose proof ZOK as Z';
    cps_destruct Z' as (CX & USP & LO1 & LO2 & FJL & PAYL & SPI & SPI2);
    let CL := fresh "CL" in pose proof (proj1 CX) as CL; unfold ctx_lin in CL; cbv zeta in CL;
    cps_destruct CL as (LS1 & LS2 & LR1 & LR2 & LR3 & LR4 & LD1 & LD2 & LD3 & LD4 & LP1 & LP2 & _ & LSTRM & LSM & LN & LTT & LL16 & LL4);
    let CS := fresh "CS" in pose proof (proj2 (proj2 CX)) as CS; unfold ctx_sep, disj in CS; cbv zeta in CS;
    cps_destruct CS as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & IA1 & IA2 & IA3 & IA4 & IA5); unfold img_apart, IHI in IA1, IA2;
    bz_ceil; unfold DSTATE_SIZE, CEILING, STACK_TOP, IMG_HI_MAX, D14 in *;
    pose proof (word_urange (z_sp z)) as USPR; pose proof (word_urange (z_spi z)) as USPIR.
  Ltac ofmkc := cbn [o_cx o_J o_d o_s o_g1 o_s1v o_SP o_gp o_tp o_F o_fc o_KQ o_m0 fmkc] in *.
  Ltac splits := lazymatch goal with |- _ /\ _ => split; splits | |- _ => idtac end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma fmkc_ok : forall m1 J d s f dbytes rest m,
    dpureF cx (bs_of cx J s) (z_payload z) J d s -> dout_okW d -> (0 <= s_avail_out s <= dlen)%Z ->
    FDEST z m s dbytes rest ->
    foctx_ok (fmkc z m1 J d s f).
  Proof.
    intros until m. (intros DP OKW Hav; cps_intros (_ & _ & _ & Lout)).
    pose proof DP as X. unfold dpureF, jk_static, in_rel, drep in X. dvF_cbn_in X.
    cps_destruct X as (JWF & _ & En & Esm & Evb & _ & _ & _ & RbB & RbL & Rbn & Rcred & Rsnb & Rnu & Rtt & Rl16 & Rl4 & Rs2u).
    cps_destruct OKW as (Eol & Rtp & NK & Rsnb1 & Ecb & Rsb & Rr01 & Rrnd & Rcf & Eoc & Rn9).
    zlin. unfold foctx_ok, oent. ofmkc. rewrite LSTRM. rewrite Ecb, Eoc, En.
    change (2^32)%Z with 4294967296%Z in Rtt. change (2^16)%Z with 65536%Z in Rl16.
    splits; try assumption.
    all: try (rewrite <- En; exact NK).
    (* [comment removed for export] *)
    all: clear D1 D2 D3 D4 D5 D6 D7 IA1 IA2 IA3 IA4 IA5 LTT LL16 LL4 NK Rr01 Rrnd Rcf CX N1; lia.
  Qed.

  Lemma fmkc_okF : forall m1 J d s f, b_small cx = 0%Z -> foctx_okF (fmkc z m1 J d s f).
  Proof.
    intros m1 J d s f Hsm. zlin. unfold foctx_okF. ofmkc.
    pose proof (NN0 Hsm) as TNZ. destruct LTT as [X | [LTT1 LTT2]]; [exfalso; exact (TNZ X)|].
    cps_destruct (D4 TNZ) as (D4a & D4b & D4c). splits; [exact Hsm| | | exact D4a| exact D4c].
    all: clear D1 D2 D3 D5 D6 D7 IA1 IA2 IA3 IA4 IA5 LL16 LL4 CX D4a D4b D4c; lia.
  Qed.

  Lemma fmkc_okS : forall m1 J d s f, b_small cx = 1%Z -> foctx_okS (fmkc z m1 J d s f).
  Proof.
    intros m1 J d s f Hsm. zlin. unfold foctx_okS. ofmkc.
    destruct (NN1 Hsm) as [NZ16 NZ4].
    destruct LL16 as [X | [LA1 LA2]]; [exfalso; exact (NZ16 X)|]. destruct LL4 as [X | [LB1 LB2]]; [exfalso; exact (NZ4 X)|].
    cps_destruct (D5 NZ16) as (D5a & D5b & D5c). cps_destruct (D6 NZ4) as (D6a & D6b & D6c). pose proof (D7 NZ16 NZ4) as D7a.
    splits; first [exact Hsm | assumption | idtac].
    all: clear D1 D2 D3 D4 D7 IA1 IA2 IA3 IA4 IA5 LTT CX D5a D5b D5c D6a D6b D6c D7a; lia.
  Qed.

  Lemma fmkc_al : forall m1 J d s f, foctx_al (fmkc z m1 J d s f).
  Proof.
    intros m1 J d s f. unfold foctx_al. ofmkc. zlin.
    pose proof (proj1 (proj2 CX)) as AL. unfold ctx_al in AL. cps_destruct AL as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
    split; [unfold ctx_al; splits; assumption|]. first [rewrite LSTRM; exact A2 | rewrite <- LSTRM; exact A2 | lia].
  Qed.
End BZD.
End ACeilS1.
