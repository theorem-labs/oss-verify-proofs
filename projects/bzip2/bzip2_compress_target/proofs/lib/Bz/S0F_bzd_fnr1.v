(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Wf_nat.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsS0 StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzTac BzDefs BzInv BzTables BzLemmasT BzLemmasMtf S0_bzd_out BzSepTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem CmpArith BzCLemmas1.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDOut BzDOK DecCutF DecTacF.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import S0F_bzd_out.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFastZ StoreFastC.   (* [comment removed for export] *)
Local Ltac mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | mem_after_store_fast ].
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Ltac unhide_disj := repeat match goal with H : id (?A \/ ?B) |- _ => unfold id in H end.
Ltac hide_disj := repeat match goal with H : ?A \/ ?B |- _ => change (A \/ B) with (id (A \/ B)) in H end.
Local Ltac tlia ::= first [ Zify.zify; xlia zchecker
                         | sf_unhide; unhide_disj;
                           first [ zify_prune_neg; Zify.zify; xlia zchecker
                                 | zify_prune_plain; Zify.zify; xlia zchecker
                                 | Zify.zify; xlia zchecker ] ].
Local Ltac tslia ::= tslia_sep.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzImg0TacF.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NormFast RelLiaA SasFastF RelLiaS.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
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
Local Ltac simpl_arr_sizes ::= SasFastF.sas6F_all.
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
  Notation RR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 :=
    (mkR ra (o_SP c) (o_gp c) (o_tp c) t0 t1 t2 (Z_to_bv 64 (b_s (o_cx c))) (o_s1v c) a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 (b_s (o_cx c) + 2047)) (Z_to_bv 64 (b_s (o_cx c) + 1096))
         (Z_to_bv 64 1) (Z_to_bv 64 2) (Z_to_bv 64 100000) (Z_to_bv 64 (b_s (o_cx c) + 64080)) s8 s9 (Z_to_bv 64 4) (Z_to_bv 64 10) t3 t4 t5 t6) (only parsing).
  Hypothesis OK : foctx_ok c. Hypothesis OKF : foctx_okF c.
  Hypothesis KJ : FKjoin c (FROf c).
  Hypothesis KE : FKexit c (FROf c).

  (* [comment removed for export] *)
  Notation KH1 := (K_H1 (d_tt (o_d c)) (100000 * b_n (o_cx c)) (sv_nblock (d_sv (o_d c)) + 1)).
  Notation KH2 := (K_H2 (d_tt (o_d c)) (100000 * b_n (o_cx c)) (sv_nblock (d_sv (o_d c)) + 1)).
  Notation KDR := (K_DR (d_tt (o_d c)) (100000 * b_n (o_cx c)) (sv_nblock (d_sv (o_d c)) + 1)).
  Notation KG := (ucG (d_tt (o_d c)) (100000 * b_n (o_cx c)) (sv_nblock (d_sv (o_d c)) + 1)).
  Notation CC r := (ccommit (o_d c) (o_s c) r).

  (* [comment removed for export] *)
  Definition DESTc (m : word -> option byte) (cl : cloc) (dbytes rest : list byte) : Prop :=
    u8arr s0segs m DST dbytes /\ Z.of_nat (length dbytes) = dlen /\
    dbytes = map (Z_to_bv 8) (rev (s_out s0)) ++ map (Z_to_bv 8) (rev (c_out cl)) ++ rest /\
    Z.of_nat (length rest) = c_avail cl.

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

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma fnr_ret : forall (ra t0 t1 t2 a0 t4 t5 crcw tpw : word) (m : word -> option byte) (cl : cloc) (dbytes rest : list byte),
    DSg c m J d0 s0 -> DESTc m cl dbytes rest -> RO m -> munch WB m0 m -> wmono s0segs m0 m ->
    cinv PP av0 cl -> (bv_unsigned crcw mod 4294967296 = c_crc cl)%Z -> (bv_unsigned tpw mod 4294967296 = c_tPos cl)%Z ->
    evt s0segs (KQ (CC (0%Z, cl)))
        (MS (RR ra t0 t1 t2 a0 (Z_to_bv 64 TT) (Z_to_bv 64 (DST + (dlen - c_avail cl))) crcw (Z_to_bv 64 (c_ch cl))
                (Z_to_bv 64 av0) (Z_to_bv 64 (c_avail cl)) tpw (Z_to_bv 64 (c_nused cl)) (Z_to_bv 64 3) (Z_to_bv 64 (c_len cl)) t4 t5 (Z_to_bv 64 (c_k0 cl)))
            F (Z_to_bv 64 0x15394) fc None m (seg_rom s0segs)).
  Proof.
    intros until rest. intros DSm DE ROm MU WM CI Hcrc Htp. unDS DSm. unRO ROm. cps_destruct DE as (DSTA & DL & Edb & RL). prep.
    change (id (dbytes = map (Z_to_bv 8) (rev (s_out s0)) ++ map (Z_to_bv 8) (rev (c_out cl)) ++ rest)) in Edb.
    cps_destruct CI as (Ccrc & Cch & Clen & Cnu & Ck0 & Ctp & Cav & Cout).
    unfold DSg in *. dvF_cbn_in HD. dvF_cbn_in MID. dvF_cbn_in SM.
    replace (CC (0%Z, cl)) with (0%Z, dcommit d0 cl, scommit s0 cl) by reflexivity.
    rewrite dcommit_set8, scommit_smod.
    wstep. wstep. wstep. wstep. wstep. wstep.
    if_cases K; zify_cond K.
    - wstep. wstep. wstep. step. rewrite BzInv.le1_lit. mem_after_store.
      wstep. wstep. wstep. wstep. wstep. wstep.
      try rewrite (unsigned_lit (c_ch cl)) in HD by lia.
      recell HD tpw (c_tPos cl); [| rewrite Htp; symmetry; apply Z.mod_small; lia].
      recell MID crcw (c_crc cl); [| rewrite Hcrc; symmetry; apply Z.mod_small; lia].
      eapply KJ.
      + unfold DSg. focbn. repeat match goal with |- _ /\ _ => split end; [exact_cells HD | exact_cells NBU | exact_cells MID | exact_cells SM].
      + unfold DESTg. focbn. repeat match goal with |- _ /\ _ => split end. all: match goal with |- ?g => idtac g end.
        * exact DSTA. * exact DL. * unfold id in Edb; rewrite Edb, rev_app_distr, map_app, app_assoc; reflexivity. * rewrite length_app. lia.
      + ro_close.
      + exact MU.
      + exact WM.
      + ojoin_close.
    - wstep. wstep. wstep.
      wstep. wstep. wstep. step. rewrite BzInv.le1_lit. mem_after_store.
      wstep. wstep. wstep. wstep. wstep. wstep.
      try rewrite (unsigned_lit (c_ch cl)) in HD by lia.
      recell HD tpw (c_tPos cl); [| rewrite Htp; symmetry; apply Z.mod_small; lia].
      recell MID crcw (c_crc cl); [| rewrite Hcrc; symmetry; apply Z.mod_small; lia].
      eapply KJ.
      + unfold DSg. focbn. repeat match goal with |- _ /\ _ => split end; [exact_cells HD | exact_cells NBU | exact_cells MID | exact_cells SM].
      + unfold DESTg. focbn. repeat match goal with |- _ /\ _ => split end;
          [exact DSTA | exact DL | unfold id in Edb; rewrite Edb, rev_app_distr, map_app, app_assoc; reflexivity | rewrite length_app; lia].
      + ro_close.
      + exact MU.
      + exact WM.
      + ojoin_close.
  Time Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation csnb := (Z_to_bv 64 snb). Notation cpp := (Z_to_bv 64 (snb + 1)). Notation cnn := (Z_to_bv 64 (100000 * n)).
  Notation optr av := (Z_to_bv 64 (DST + (dlen - av))).

  (* [comment removed for export] *)
  Definition PS (pc : Z) (K : nat -> cloc -> Z * cloc) (f : nat) (cl : cloc) : Prop :=
    forall (a0 s8 t3 t4 t6 crcw tpw : word) (m : word -> option byte) (dbytes rest : list byte),
      DSg c m J d0 s0 -> DESTc m cl dbytes rest -> RO m -> munch WB m0 m -> wmono s0segs m0 m ->
      cinv PP av0 cl -> (bv_unsigned crcw mod 4294967296 = c_crc cl)%Z -> (bv_unsigned tpw mod 4294967296 = c_tPos cl)%Z ->
      (PP - c_nused cl <= Z.of_nat f)%Z ->
      evt s0segs (KQ (CC (K f cl)))
        (MS (RR (Z_to_bv 64 (c_k0 cl)) csnb cpp cnn a0 (Z_to_bv 64 TT) (optr (c_avail cl)) crcw (Z_to_bv 64 (c_ch cl))
                (Z_to_bv 64 av0) (Z_to_bv 64 (c_avail cl)) tpw s8 (Z_to_bv 64 3) t3 t4 (Z_to_bv 64 (c_nused cl)) t6)
            F (Z_to_bv 64 pc) fc None m (seg_rom s0segs)).
  Definition H2S := PS 0x15254 KH2.
  Definition GS := PS 0x15288 KG.
  (* [comment removed for export] *)
  Definition QS (pc : Z) (drain : bool) (K : nat -> cloc -> Z * cloc) (f : nat) (cl : cloc) : Prop :=
    forall (ra a0 s9 t4 t5 crcw tpw : word) (m : word -> option byte) (dbytes rest : list byte),
      DSg c m J d0 s0 -> DESTc m cl dbytes rest -> RO m -> munch WB m0 m -> wmono s0segs m0 m ->
      cinv PP av0 cl -> (bv_unsigned crcw mod 4294967296 = c_crc cl)%Z -> (bv_unsigned tpw mod 4294967296 = c_tPos cl)%Z ->
      (PP - c_nused cl <= Z.of_nat f)%Z ->
      (if drain then (1 <= c_len cl)%Z /\ (1 <= c_avail cl)%Z /\ s9 = Z_to_bv 64 3 else True) ->
      evt s0segs (KQ (CC (K f cl)))
        (MS (RR ra csnb cpp cnn a0 (Z_to_bv 64 TT) (optr (c_avail cl)) crcw (Z_to_bv 64 (c_ch cl)) (Z_to_bv 64 av0)
                (Z_to_bv 64 (c_avail cl)) tpw (Z_to_bv 64 (c_nused cl)) s9 (Z_to_bv 64 (c_len cl)) t4 t5 (Z_to_bv 64 (c_k0 cl)))
            F (Z_to_bv 64 pc) fc None m (seg_rom s0segs)).
  Definition H1S := QS 0x151f0 false KH1.
  Definition DRS := QS 0x151fc true KDR.

  (* [comment removed for export] *)
  Lemma KEc : forall (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 : word) (m : word -> option byte) (out : list Z) (dbytes rest : list byte),
    DSg c m J d0 s0 -> u8arr s0segs m DST dbytes -> Z.of_nat (length dbytes) = dlen ->
    dbytes = map (Z_to_bv 8) (rev (s_out s0)) ++ map (Z_to_bv 8) (rev out) ++ rest ->
    RO m -> munch WB m0 m -> wmono s0segs m0 m ->
    evt s0segs (KQ (1%Z, d0, s0)) (MS (RR ra t0 t1 t2 (Z_to_bv 64 (-4)) a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6)
                                     F (Z_to_bv 64 0x15484) fc None m (seg_rom s0segs)).
  Proof.
    intros until rest. intros DSm DSTA DL Edb ROm MU WM.
    pose proof OK as OK'. cps_destruct OK' as (_ & _ & _ & _ & _ & _ & _ & _ & ENT). cps_destruct ENT as (_ & _ & _ & _ & _ & Rav0 & Lout0 & _ & _ & NK0 & _).
    rewrite <- (set8_id d0), <- (smod_id s0). rewrite <- (jk_set_o_id J) in DSm.
    eapply (KE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dbytes (map (Z_to_bv 8) (rev out) ++ rest));
      [exact DSm | | exact ROm | exact MU | exact WM | unfold oexit; focbn; lia].
    unfold DESTg. focbn. repeat match goal with |- _ /\ _ => split end; [exact DSTA | exact DL | exact Edb | exact Lout0].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac cc1 := lazymatch goal with |- evt _ (o_KQ c (ccommit _ _ (1%Z, ?X))) _ =>
    change (ccommit (o_d c) (o_s c) (1%Z, X)) with (1%Z, o_d c, o_s c) end.
  Ltac exitK := cc1;
    lazymatch goal with DSTA : u8arr _ _ DST _, DL : Z.of_nat (length _) = dlen, Edb : id (_ = _) |- _ =>
      unfold id in Edb;
      eapply KEc; [unfold DSg; dvF_cbn; repeat match goal with |- _ /\ _ => split end; assumption
                  | exact DSTA | exact DL | exact Edb | ro_close | assumption | assumption] end.
  (* [comment removed for export] *)
  Ltac tt_load i :=
    lazymatch goal with TTA : u32arr _ ?mm TT _ |- _ =>
      let RD := fresh "RD" in
      pose proof (zw32_read s0segs mm TT (d_tt d0) cap i _ TTA ltac:(lia) eq_refl) as RD;
      wstep; clear RD end.

  (* [comment removed for export] *)
  Ltac cinv_close := unfold cinv; ccbv; repeat match goal with |- _ /\ _ => split end; first [lia | mlia].
  Ltac tp_rel := ccbv; rewrite unsigned_lit by mlia; apply Z.mod_small; mlia.
  (* [comment removed for export] *)
  Ltac goPS IH f' crcw dbytes rest DSTA DL Edb RL MU WM Hcrc :=
    enter_with (IH f' _ eq_refl _ _ _ _ _ crcw _ _ dbytes rest);
    [ ccbv; st_eq
    | unfold DSg; dvF_cbn; repeat match goal with |- _ /\ _ => split end; assumption
    | unfold DESTc; ccbv; repeat match goal with |- _ /\ _ => split end; [exact DSTA| exact DL| exact Edb| exact RL]
    | ro_close | exact MU | exact WM
    | cinv_close | ccbv; exact Hcrc | tp_rel | ccbv; lia ].
  Ltac goQS IH f' crcw dbytes rest DSTA DL Edb RL MU WM Hcrc :=
    enter_with (IH f' _ eq_refl _ _ _ _ _ crcw _ _ dbytes rest);
    [ ccbv; st_eq
    | unfold DSg; dvF_cbn; repeat match goal with |- _ /\ _ => split end; assumption
    | unfold DESTc; ccbv; repeat match goal with |- _ /\ _ => split end; [exact DSTA| exact DL| exact Edb| exact RL]
    | ro_close | exact MU | exact WM
    | cinv_close | ccbv; exact Hcrc | tp_rel | ccbv; lia | exact I ].
  (* [comment removed for export] *)
  Ltac mif_neq a b := rewrite (proj2 (Z.eqb_neq a b)) by lia; cbn [negb].
  Ltac mif_eq a b := rewrite (proj2 (Z.eqb_eq a b)) by lia; cbn [negb].

  Lemma fnr_G : forall f,
    (forall f' cl', f = Datatypes.S f' -> H2S f' cl') -> (forall f' cl', f = Datatypes.S f' -> H1S f' cl') -> forall cl, GS f cl.
  Proof.
    intros f IH2 IH1 cl. unfold GS, PS. intros until rest. intros DSm DE ROm MU WM CI Hcrc Htp Hf.
    unDS DSm. unRO ROm. cps_destruct DE as (DSTA & DL & Edb & RL). prep.
    cps_destruct CI as (Ccrc & Cch & Clen & Cnu & Ck0 & Ctp & Cav & Cout).
    destruct cl as [crc ch len nu k0 tp out av]. cbn [c_crc c_ch c_len c_nused c_k0 c_tPos c_out c_avail] in *.
    change (id (dbytes = map (Z_to_bv 8) (rev (s_out s0)) ++ map (Z_to_bv 8) (rev out) ++ rest)) in Edb.
    unfold DSg in *. dvF_cbn_in HD. dvF_cbn_in MID. dvF_cbn_in SM.
    pose proof (word_urange tpw) as TPR.
    wstep. (* [comment removed for export] *) wstep. (* [comment removed for export] *)
    if_cases K1; zify_cond K1; rewrite ?signed_lit_small in K1 by lia.
    { (* [comment removed for export] *)
      rewrite ucG_over by (ccbv; lia). exitK. }
    wstep. if_cases K2; zify_cond K2.
    { (* [comment removed for export] *)
      rewrite ucG_done by (ccbv; lia). wstep. wstep. wstep.
      enter_with (fnr_ret _ _ _ _ _ _ _ crcw tpw _ _ dbytes rest);
        [ ccbv; st_eq
        | unfold DSg; dvF_cbn; repeat match goal with |- _ /\ _ => split end; assumption
        | unfold DESTc; ccbv; repeat match goal with |- _ /\ _ => split end; [exact DSTA| exact DL| exact Edb| exact RL]
        | ro_close | exact MU | exact WM
        | unfold cinv; ccbv; lia | ccbv; exact Hcrc | ccbv; exact Htp ]. }
    destruct f as [|f']; [exfalso; cbn [Z.of_nat] in Hf; lia|]. rewrite Nat2Z.inj_succ in Hf.
    rewrite ucG_go by (ccbv; lia).
    (* [comment removed for export] *)
    wstep. wstep. if_cases K3; zify_cond K3.
    { pose proof (sextw_ge (bv_unsigned tpw) cap (proj1 TPR) ltac:(lia) K3) as GE. change (2^32)%Z with 4294967296%Z in GE. rewrite Htp in GE.
      rewrite G1_None by (ccbv; lia). exitK. }
    destruct (sextw_lt (bv_unsigned tpw) cap (proj1 TPR) ltac:(lia) K3) as [LT XV]. change (2^32)%Z with 4294967296%Z in LT, XV. rewrite Htp in LT, XV.
    rewrite G1_Some by (ccbv; lia). ccbv.
    (* [comment removed for export] *)
    wstep. wstep. rewrite (shl32_shr30 (bv_unsigned tpw)) by lia. change (2^32)%Z with 4294967296%Z. rewrite Htp. wstep.
    tt_load tp. pose proof (Rtt tp) as Rw1. set (w1 := zget (d_tt d0) tp) in *.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep.
    rewrite (sx32_mod32 w1) by lia. rewrite (sx32_land255 w1) by lia. rewrite (land255_small k0) by lia.
    pose proof (S0_bzd_out.land255_range w1) as CH1.
    wstep. if_cases K4; zify_cond K4.
    { (* [comment removed for export] *)
      mif_neq (Z.land w1 255) k0. wstep. wstep. wstep.
      goPS IH2 f' crcw dbytes rest DSTA DL Edb RL MU WM Hcrc. }
    mif_eq (Z.land w1 255) k0.
    wstep. if_cases K5; zify_cond K5.
    2:{ (* [comment removed for export] *)
        mif_eq (nu + 1)%Z (sv_nblock (d_sv (o_d c)) + 1)%Z. wstep. wstep.
        goPS IH2 f' crcw dbytes rest DSTA DL Edb RL MU WM Hcrc. }
    mif_neq (nu + 1)%Z (sv_nblock (d_sv (o_d c)) + 1)%Z.
    (* [comment removed for export] *)
    wstep. if_cases K6; zify_cond K6.
    { rewrite G2_None by (ccbv; mlia). exitK. }
    rewrite G2_Some by (ccbv; mlia). ccbv.
    (* [comment removed for export] *)
    wstep. wstep. tt_load (w1 / 256)%Z. pose proof (Rtt (w1 / 256)%Z) as Rw2. set (w2 := zget (d_tt d0) (w1 / 256)) in *.
    rewrite (zx32_of_Z w2) by lia.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep.
    wstep. if_cases K7; zify_cond K7.
    { mif_eq (nu + 2)%Z (sv_nblock (d_sv (o_d c)) + 1)%Z.
      goQS IH1 f' crcw dbytes rest DSTA DL Edb RL MU WM Hcrc. }
    mif_neq (nu + 2)%Z (sv_nblock (d_sv (o_d c)) + 1)%Z.
    (* [comment removed for export] *)
    wstep. wstep. pose proof (S0_bzd_out.land255_range w2) as CH2.
    wstep. if_cases K8; zify_cond K8.
    { mif_neq (Z.land w2 255) k0.
      goQS IH1 f' crcw dbytes rest DSTA DL Edb RL MU WM Hcrc. }
    mif_eq (Z.land w2 255) k0.
    (* [comment removed for export] *)
    wstep. if_cases K9; zify_cond K9.
    { rewrite G3_None by (ccbv; mlia). exitK. }
    rewrite G3_Some by (ccbv; mlia). ccbv.
    wstep. wstep. tt_load (w2 / 256)%Z. pose proof (Rtt (w2 / 256)%Z) as Rw3. set (w3 := zget (d_tt d0) (w2 / 256)) in *.
    rewrite (zx32_of_Z w3) by lia.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep.
    wstep. if_cases K10; zify_cond K10.
    { mif_eq (nu + 3)%Z (sv_nblock (d_sv (o_d c)) + 1)%Z.
      goQS IH1 f' crcw dbytes rest DSTA DL Edb RL MU WM Hcrc. }
    mif_neq (nu + 3)%Z (sv_nblock (d_sv (o_d c)) + 1)%Z.
    (* [comment removed for export] *)
    wstep. wstep. pose proof (S0_bzd_out.land255_range w3) as CH3.
    wstep. if_cases K11; zify_cond K11.
    { mif_neq (Z.land w3 255) k0.
      goQS IH1 f' crcw dbytes rest DSTA DL Edb RL MU WM Hcrc. }
    mif_eq (Z.land w3 255) k0.
    (* [comment removed for export] *)
    wstep. if_cases K12; zify_cond K12.
    { rewrite G4_None by (ccbv; mlia). exitK. }
    rewrite G4_Some by (ccbv; mlia). ccbv.
    wstep. wstep. tt_load (w3 / 256)%Z. pose proof (Rtt (w3 / 256)%Z) as Rw4. set (w4 := zget (d_tt d0) (w3 / 256)) in *.
    rewrite (zx32_of_Z w4) by lia.
    (* [comment removed for export] *)
    wstep.
    wstep. if_cases K13; zify_cond K13.
    { rewrite G5_None by (ccbv; mlia). exitK. }
    rewrite G5_Some by (ccbv; mlia). ccbv.
    wstep. wstep. tt_load (w4 / 256)%Z. pose proof (Rtt (w4 / 256)%Z) as Rw5. set (w5 := zget (d_tt d0) (w4 / 256)) in *.
    (* [comment removed for export] *)
    pose proof (S0_bzd_out.land255_range w4) as CH4. pose proof (S0_bzd_out.land255_range w5) as CH5.
    wstep. wstep. wstep. wstep. wstep.
    rewrite (sx32_mod32 w5), (sx32_land255 w5) by lia.
    wstep. (* [comment removed for export] *)
    goQS IH1 f' crcw dbytes rest DSTA DL Edb RL MU WM Hcrc.
  Time Qed.
End FNR.
End ACeilS1.
