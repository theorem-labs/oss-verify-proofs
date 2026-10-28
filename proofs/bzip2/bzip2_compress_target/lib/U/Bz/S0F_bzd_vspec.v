(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzDefs BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import S0_bzd_out.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem CmpArith BzCLemmas1.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDOut BzDOK. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF DecTacF.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0F_bzd_out.

From Stdlib Require Wf_nat.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzLemmasT BzLemmasMtf BzSepTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0F_bzd_out.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFastZ StoreFastC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NatLit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzImg0TacF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require NormFast. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLiaA SepFast RelLiaS.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
Module S0F_bzd_fnr2.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Arith.Wf_nat.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.StoreFast.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzDefs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzInv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTables OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasMtf OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_bzd_out OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzSepTac.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmas1.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_out.
 Unset Lia Cache.
Import ListNotations. Local Open Scope bv_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
   (* [comment removed for export] *)
Local Ltac mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | mem_after_store_fast ].
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
Ltac unhide_disj := repeat match goal with H : id (?A \/ ?B) |- _ => unfold id in H end.
Ltac hide_disj := repeat match goal with H : ?A \/ ?B |- _ => change (A \/ B) with (id (A \/ B)) in H end.
Local Ltac tlia ::= first [ Zify.zify; xlia zchecker
                         | sf_unhide; unhide_disj;
                           first [ zify_prune_neg; Zify.zify; xlia zchecker
                                 | zify_prune_plain; Zify.zify; xlia zchecker
                                 | Zify.zify; xlia zchecker ] ].
Local Ltac tslia ::= tslia_sep.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.NatLit.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzImg0TacF.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= RelLiaA.lia_rf.
Local Ltac BzTac.bz32 ::= NormFast.bz32_m.
Local Ltac BzTac2.bz32l ::= NormFast.bz32l_m.
Local Ltac Zify.zify_pre_hook ::= NormFast.nf_pre_natlen.
Local Ltac DecCutF.unset_Z ::= NormFast.unset_Z_subst.
Local Ltac BzSepTac.sep_tac ::= SepFast.sep_tac_u.
Local Ltac tlia ::= RelLiaS.tlia_bzd_r.
Local Ltac BzSepTac.tlia1 ::= RelLiaS.tlia1_r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.

Section FNR.
  Variable c : foctx.
  Notation cx := (o_cx c). Notation J := (o_J c). Notation d0 := (o_d c). Notation s0 := (o_s c).
  Notation S := (b_s (o_cx c)). Notation STRM := (b_strm (o_cx c)). Notation DST := (b_dst (o_cx c)). Notation dlen := (b_dlen (o_cx c)).
  Notation n := (b_n (o_cx c)). Notation TT := (b_tt (o_cx c)).
  Notation snb := (sv_nblock (d_sv (o_d c))). Notation av0 := (s_avail_out (o_s c)). Notation PP := (sv_nblock (d_sv (o_d c)) + 1)%Z.
  Notation cap := (100000 * b_n (o_cx c))%Z.
  Notation F := (o_F c). Notation fc := (o_fc c). Notation KQ := (o_KQ c). Notation m0 := (o_m0 c).
  Notation RO := (FROf c). Notation WB := (FWB c).
  Notation RR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s3 s8 t3 t4 t5 t6 :=
    (mkR ra (o_SP c) (o_gp c) (o_tp c) t0 t1 t2 (Z_to_bv 64 (b_s (o_cx c))) s1 a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 (b_s (o_cx c) + 1096)) s3 (Z_to_bv 64 (b_s (o_cx c) + 2047))
         (Z_to_bv 64 1) (Z_to_bv 64 2) (Z_to_bv 64 (-1)) s8 (Z_to_bv 64 100000) (Z_to_bv 64 (b_s (o_cx c) + 64080)) (Z_to_bv 64 10) t3 t4 t5 t6) (only parsing).
  Hypothesis OK : foctx_ok c. Hypothesis OKF : foctx_okF c.
  Hypothesis KJ : FKjoin c (FROf c).
  Hypothesis KE : FKexit c (FROf c).

  (* [comment removed for export] *)
  Notation KH1 := (K_H1 (d_tt (o_d c)) (100000 * b_n (o_cx c)) (sv_nblock (d_sv (o_d c)) + 1)).
  Notation KH2 := (K_H2 (d_tt (o_d c)) (100000 * b_n (o_cx c)) (sv_nblock (d_sv (o_d c)) + 1)).
  Notation KDR := (K_DR (d_tt (o_d c)) (100000 * b_n (o_cx c)) (sv_nblock (d_sv (o_d c)) + 1)).
  Notation KG := (ucG (d_tt (o_d c)) (100000 * b_n (o_cx c)) (sv_nblock (d_sv (o_d c)) + 1)).
  Notation CC r := (ccommit (o_d c) (o_s c) r).

  Ltac unRO H := let GOT := ident:(GOT) in cps_destruct H as (SAV & TTA & CRC & RNA & GOT & MI); unfold FGOT in GOT.
  Ltac unDS H := cps_destruct H as (HD & NBU & MID & SM).
  (* [comment removed for export] *)
  Ltac prep :=
    let JWF := ident:(JWF) in let ENT := ident:(ENT) in let OK' := fresh "OK" in pose proof OK as OK';
    cps_destruct OK' as (HS & HSTRM & HDST & Hdlen & SEP_SD & IAS & IAD & JWF & ENT);
    let OKF' := fresh "OKF" in pose proof OKF as OKF';
    cps_destruct OKF' as (HSM & HTT & SEP_ST & SEP_DT);
    cps_destruct ENT as (En & Rn & Esm & Rsnb & Rsnb1 & Rav0 & Lout0 & Eol0 & RtP0 & NK0 & Rcb0 & Roc0 & Rr01 & Rrnd & _ & Rtt & _ & _);
    cps_destruct JWF as (Lp1 & Lp2 & Lp3 & Ls1 & Ls2 & Lq1 & Lq2);
    unfold FWB in *; pose proof alloc_ceiling_range as ACR;
    pose proof (zw32_length (d_tt d0) cap ltac:(lia)) as TTL; pose proof rnums_words_length as RNL; pose proof crc_words_length as CRCL; hide_disj.

  (* [comment removed for export] *)
  Ltac cs_split cs w :=
    lazymatch cs with
    | C4 w :: ?post => constr:((@nil cell, post))
    | ?c1 :: ?cs' => let r := cs_split cs' w in lazymatch r with (?pre, ?post) => constr:((c1 :: pre, post)) end
    end.
  Ltac recell H w v :=
    lazymatch type of H with rw_cells ?sg ?mm ?A ?cs =>
      let r := cs_split cs w in
      lazymatch r with (?pre, ?post) =>
        apply (C4_recell sg mm A pre w v post) in H; [ cbn [app] in H | ]
      end
    end.
  (* [comment removed for export] *)
  Ltac ro_close := unfold FROf, FGOT; repeat match goal with |- _ /\ _ => split end; assumption.
  Ltac ojoin_close := unfold ojoin; focbn; repeat match goal with |- _ /\ _ => split end; first [lia | assumption | intros; lia | idtac].


  Notation csnb := (Z_to_bv 64 snb). Notation cpp := (Z_to_bv 64 (snb + 1)). Notation cnn := (Z_to_bv 64 (100000 * n)).
  Notation optr av := (Z_to_bv 64 (DST + (dlen - av))).

  (* [comment removed for export] *)
  Ltac dst_write av ch Edb RL :=
    let E' := ident:(E') in let R' := ident:(R') in lazymatch goal with DSTA : u8arr _ _ DST ?bs |- _ =>
      let SOK := fresh "SOK" in
      pose proof (u8arr_store_ok s0segs _ DST _ (dlen - av) _ DSTA ltac:(lia) eq_refl) as SOK;
      step; rewrite BzInv.le1_lit;
      let D := fresh "DSTB" in
      pose proof (u8arr_write s0segs _ DST _ (dlen - av) (Z_to_bv 8 ch) DSTA ltac:(lia)) as D;
      clear DSTA; store_done; try clear SOK; rename D into DSTA;
      lazymatch goal with DL : Z.of_nat (length bs) = _ |- _ =>
        let D2 := fresh "DLB" in
        pose proof DL as D2; rewrite <- (upd_length bs (Z.to_nat (dlen - av)) (Z_to_bv 8 ch)) in D2; clear DL; rename D2 into DL;
        unfold id in Edb;
        let r' := fresh "rest" in let E' := fresh "Edb" in let R' := fresh "RL" in
        cps_destruct (destc_snoc _ _ _ _ (Z.to_nat (dlen - av)) ch av Edb ltac:(rewrite length_map, length_rev; lia) RL ltac:(lia)) as (r' & E' & R');
        clear Edb RL; rename E' into Edb; rename R' into RL;
        let db := fresh "dbytes" in
        remember (upd bs (Z.to_nat (dlen - av)) (Z_to_bv 8 ch)) as db eqn:Xdb; clear Xdb;
        lazymatch type of Edb with ?x = ?y => change (id (x = y)) in Edb end
      end end.

  (* [comment removed for export] *)
  Ltac crc_step crc ch Hcrc :=
    let Hidx := fresh "Hidx" in
    pose proof (crc_idx_byte crc ch ltac:(lia) ltac:(lia)) as Hidx;
    wstep; wstep; wstep; wstep; rewrite Hcrc; wstep; wstep;
    lazymatch goal with CRC : u32arr _ ?mm 209272 crc_words |- _ =>
      let RD := fresh "RD" in
      pose proof (u32arr_read s0segs mm 209272 crc_words (Z.lxor (crc / 16777216) ch) _ _ CRC (crc_words_nth _ Hidx) ltac:(lia) eq_refl) as RD;
      wstep; clear RD end.
  Ltac cc1 := lazymatch goal with |- evt _ (o_KQ c (ccommit _ _ (1%Z, ?X))) _ =>
    change (ccommit (o_d c) (o_s c) (1%Z, X)) with (1%Z, o_d c, o_s c) end.
  Ltac fix_optr av :=
    replace (Z_to_bv 64 (DST + (dlen - av) + 1)) with (Z_to_bv 64 (DST + (dlen - (av - 1)))) by (f_equal; lia).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
End FNR.
End ACeilS1.
End S0F_bzd_fnr2.

Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_out OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_vspec.S0F_bzd_fnr2.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
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
Section ACeilS1. Context {ACEIL__ : ACeil}.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition FASTR_spec : Prop :=
    forall c : foctx, foctx_ok c -> foctx_okF c -> foctx_al c -> FKjoin c (FROf c) -> FKexit c (FROf c) ->
    forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s3 s8 t3 t4 t5 t6 : word) (m : word -> option byte) (dbytes rest : list byte),
      DSg c m (o_J c) (o_d c) (o_s c) -> DESTg c m (o_s c) dbytes rest -> FROf c m ->
      munch (FWB c) (o_m0 c) m -> wmono s0segs (o_m0 c) m ->
      d_rand (o_d c) = 1%Z ->
      evt s0segs (o_KQ c (unRLE (o_d c) (o_s c)))
          (MS (FRR c ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s3 s8 t3 t4 t5 t6) (o_F c) (Z_to_bv 64 0x15008) (o_fc c) None m (seg_rom s0segs)).

  (* [comment removed for export] *)
  Definition SMALLNR_spec : Prop :=
    forall c : foctx, foctx_ok c -> foctx_okS c -> foctx_al c -> FKjoin c (FROs c) -> FKexit c (FROs c) ->
    forall (ra t0 t1 t2 a0 a3 a4 a5 a6 a7 s1 s3 s8 t3 t4 t5 t6 : word) (m : word -> option byte) (dbytes rest : list byte),
      DSg c m (o_J c) (o_d c) (o_s c) -> DESTg c m (o_s c) dbytes rest -> FROs c m ->
      munch (FWB c) (o_m0 c) m -> wmono s0segs (o_m0 c) m ->
      d_rand (o_d c) = 0%Z ->
      evt s0segs (o_KQ c (unRLE (o_d c) (o_s c)))
          (MS (FRR c ra t0 t1 t2 a0 (Z_to_bv 64 (b_strm (o_cx c))) (Z_to_bv 64 1) a3 a4 a5 a6 a7 s1 s3 s8 t3 t4 t5 t6)
              (o_F c) (Z_to_bv 64 0x1545c) (o_fc c) None m (seg_rom s0segs)).

  (* [comment removed for export] *)
  Definition SMALLR_spec : Prop :=
    forall c : foctx, foctx_ok c -> foctx_okS c -> foctx_al c -> FKjoin c (FROs c) -> FKexit c (FROs c) ->
    forall (ra t0 t1 t2 a0 a3 a4 a5 a6 a7 s1 s3 s8 t3 t4 t5 t6 : word) (m : word -> option byte) (dbytes rest : list byte),
      DSg c m (o_J c) (o_d c) (o_s c) -> DESTg c m (o_s c) dbytes rest -> FROs c m ->
      munch (FWB c) (o_m0 c) m -> wmono s0segs (o_m0 c) m ->
      d_rand (o_d c) = 1%Z ->
      evt s0segs (o_KQ c (unRLE (o_d c) (o_s c)))
          (MS (FRR c ra t0 t1 t2 a0 (Z_to_bv 64 (b_strm (o_cx c))) (Z_to_bv 64 1) a3 a4 a5 a6 a7 s1 s3 s8 t3 t4 t5 t6)
              (o_F c) (Z_to_bv 64 0x14854) (o_fc c) None m (seg_rom s0segs)).

  (* [comment removed for export] *)
End ACeilS1.
