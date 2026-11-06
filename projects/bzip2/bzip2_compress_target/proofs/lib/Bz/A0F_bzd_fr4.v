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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzTac BzDefs BzInv BzTables BzLemmasT BzLemmasMtf BzWalkArith BzWalkArith2 S0_bzd_out BzSepTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem CmpArith BzCLemmas1.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDOut BzDOK BzDOKp BzDOKS DecCutF DecTacF.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKp OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKS OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import S0F_bzd_out S0F_bzd_outS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0F_bzd_fr1 S0F_bzd_fr2 S0F_bzd_fr3.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit DecCutA A0F_decV A0F_bzdV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require A0F_bzd_fr1 A0F_bzd_fr2 A0F_bzd_fr3 A0F_bzd_skV.
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
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
Local Ltac AsanKit.a_norm ::= AsanKit.sh_fold.
Section ACeilS1. Context {ACEIL__ : ACeil}.

Section FR.
  Variable c : foctx.
  Variable SHS : Z. Variable w0 w32 w104 w112 : word.
  Notation cx := (o_cx c). Notation J := (o_J c). Notation d0 := (o_d c). Notation s0 := (o_s c).
  Notation S := (b_s (o_cx c)). Notation STRM := (b_strm (o_cx c)). Notation DST := (b_dst (o_cx c)). Notation dlen := (b_dlen (o_cx c)).
  Notation n := (b_n (o_cx c)). Notation TT := (b_tt (o_cx c)).
  Notation snb := (sv_nblock (d_sv (o_d c))). Notation av0 := (s_avail_out (o_s c)). Notation PP := (sv_nblock (d_sv (o_d c)) + 1)%Z.
  Notation cap := (100000 * b_n (o_cx c))%Z.
  Notation F := (o_F c). Notation fc := (o_fc c). Notation KQ := (o_KQ c). Notation m0 := (o_m0 c).
  Notation uspi := (bv_unsigned (o_SP c)).
  Notation RO := (FROfA DI_A0 c). Notation WB := (FWBA c).
  Notation SRR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 t3 t4 t5 t6 :=
    (mkR ra (o_SP c) (o_gp c) (o_tp c) t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 (b_s (o_cx c))) a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 (b_s (o_cx c) + 16)) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 2147450880) (Z_to_bv 64 (b_s (o_cx c) + 1096))
         (Z_to_bv 64 (b_s (o_cx c) + 3152)) t3 t4 t5 t6) (only parsing).
  Notation csnb := (Z_to_bv 64 snb). Notation cnn := (Z_to_bv 64 (n * 100000)). Notation cstrm := (Z_to_bv 64 STRM).
  Notation cm4 := (Z_to_bv 64 (-4)). Notation cTT := (Z_to_bv 64 (b_tt (o_cx c))).
  (* [comment removed for export] *)
  Notation cra := (Z_to_bv 64 (SHS + 398)).           (* [comment removed for export] *)
  Notation ct1 := (Z_to_bv 64 (SHS + -2147450879)).   (* [comment removed for export] *)
  Notation ca2 := (Z_to_bv 64 (SHS + -2147450486)).   (* [comment removed for export] *)
  Notation ca7 := (Z_to_bv 64 (SHS + -2147450878)).   (* [comment removed for export] *)
  Notation csh := (Z_to_bv 64 SHS).                   (* [comment removed for export] *)
  Notation cs6 := (Z_to_bv 64 (b_s (o_cx c) + 12)). Notation cs8 := (Z_to_bv 64 (b_s (o_cx c) + 3184)).
  Notation c16 := (Z_to_bv 64 (SHS + 2)).             (* [comment removed for export] *)
  Notation c24 := (Z_to_bv 64 (SHS + 3)).             (* [comment removed for export] *)
  Notation c60 := (Z_to_bv 64 (SHS + 7)).             (* [comment removed for export] *)
  Notation c64 := (Z_to_bv 64 (SHS + 8)).             (* [comment removed for export] *)
  Notation cnu := (Z_to_bv 64 (SHS + 136)).           (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation D8 oc ol nu k0 tp rn rt cb := (set8 (o_d c) oc ol nu k0 tp rn rt cb).
  Notation S3 out av tout := (smod (o_s c) out av tout).
  Notation JJ tol toh := (jk_set_o (o_J c) tol toh).
  Hypothesis OK : foctx_okA c AIHI0. Hypothesis OKF : foctx_okFA c AIHI0.
  Hypothesis RD1 : d_rand (o_d c) = 1%Z.
  Hypothesis ANS : sanchor S SHS.
  Hypothesis SH : obz_sh DI_A0 c WB m0.
  Hypothesis KJ : A0_FKjoin c SHS w0 (FROfA DI_A0 c).
  Hypothesis KE : A0_FKexit c SHS w0 (FROfA DI_A0 c).
  Notation finv := (S0F_bzd_fr1.finv c).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac g8 := S0F_bzd_fr1.g8.
  Ltac hide H := lazymatch type of H with ?T => change T with (id T) in H end.
  Ltac unRO H := let GOT := ident:(GOT) in cps_destruct H as (SAV & TTA & CRC & RNA & GOT & MI); unfold FGOTA in GOT; a0img.
  Ltac unDS H := cps_destruct H as (HD & NBU & MID & SM).
  Ltac unSH := let SHbf := ident:(SHbf) in let SH' := fresh "SH" in pose proof SH as SH';
    cps_destruct SH' as (SHs & SHt & SHd & SHc & SHr & SHbf & _); a0img;
    let OKF' := fresh "OKF" in pose proof OKF as OKF'; specialize (SHbf (proj1 OKF')); clear OKF'.
  Ltac prep :=
    let JWF := ident:(JWF) in let ENT := ident:(ENT) in let Rcf := ident:(Rcf) in let Rrnd := ident:(Rrnd) in let OK' := fresh "OK" in pose proof OK as OK';
    cps_destruct OK' as (HS & HSTRM & HDST & Hdlen & HSP & HAL & SEP_SM & SEP_SD & SEP_MD & IAS & IAM & IAD & HIHI & JWF & ENT);
    let OKF' := fresh "OKF" in pose proof OKF as OKF';
    cps_destruct OKF' as (HSM & HTT & SEP_ST & SEP_MT & SEP_DT & IAT);
    cps_destruct ENT as (En & Rn & Esm & Rsnb & Rsnb1 & Rav0 & Lout0 & Eol0 & RtP0 & NK0 & Rcb0 & Roc0 & Rr01 & Rrnd & Rcf & Rtt & Rl16 & Rl4);
    cps_destruct JWF as (Lp1 & Lp2 & Lp3 & Ls1 & Ls2 & Lq1 & Lq2);
    unfold disj, bzd_img_apart in *;
    unfold FWBA, FWB in *; cbn [app] in *; pose proof alloc_ceiling_range as ACR;
    pose proof (zw32_length (d_tt d0) cap ltac:(lia)) as TTL; pose proof rnums_words_length as RNL; pose proof crc_words_length as CRCL;
    pose proof (proj2 ANS : saddr S SHS) as ANS0;
    hide Rcf; hide Rrnd; hide_disj.
  Ltac unFI H := cps_destruct H as (Ioc & Iol & Inu & Ik0 & Itp & Irn & Irt & Icb & Iav); hide_disj.
  Ltac ro_close := unfold FROfA, FGOTA; a0img; repeat match goal with |- _ /\ _ => split end; assumption.
  Ltac dsg_close HD NBU MID SM := unfold DSgA; a0img; focbn; repeat match goal with |- _ /\ _ => split end; [exact_cells HD| exact_cells NBU| exact_cells MID| exact_cells SM].
  Ltac destg_close DSTA DL Edb Lout := unfold DESTgA; a0img; focbn; repeat match goal with |- _ /\ _ => split end; [exact DSTA| exact DL| exact Edb| exact Lout].
  Ltac fsl_close FSL := first [ exact FSL | unfold bzd_slots; exact FSL ].
  (* [comment removed for export] *)
  Ltac goJ HD NBU MID SM DSTA DL Edb Lout FSL MU WM :=
    eapply KJ; [dsg_close HD NBU MID SM| destg_close DSTA DL Edb Lout| fsl_close FSL| ro_close| exact MU| exact WM
               | unfold ojoin; focbn; repeat match goal with |- _ /\ _ => split end].
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation CHf := (A0F_bzd_fr1.CHf c SHS w0 w32 w104 w112).
  Notation MSx := (A0F_bzd_fr1.MSx c SHS w0 w32 w104 w112). Notation TLS := (A0F_bzd_fr1.TLS c SHS w0 w32 w104 w112).
  Notation HS := (A0F_bzd_fr1.HS c SHS w0 w32 w104 w112). Notation OUTS := (A0F_bzd_fr1.OUTS c SHS w0 w32 w104 w112).
  Notation GS := (A0F_bzd_fr1.GS c SHS w0 w32 w104 w112).
  Notation R1S := (A0F_bzd_fr1.R1S c SHS w0 w32 w104 w112). Notation R2S := (A0F_bzd_fr1.R2S c SHS w0 w32 w104 w112).
  Notation R3S := (A0F_bzd_fr1.R3S c SHS w0 w32 w104 w112). Notation R4S := (A0F_bzd_fr1.R4S c SHS w0 w32 w104 w112).
  Notation R5S := (A0F_bzd_fr1.R5S c SHS w0 w32 w104 w112).
  Ltac ch_close HD NBU MID SM DSTA DL Edb Lout FSL MU WM :=
    unfold A0F_bzd_fr1.CHf; repeat match goal with |- _ /\ _ => split end;
    [dsg_close HD NBU MID SM| destg_close DSTA DL Edb Lout| unfold A0F_bzd_fr1.FSLf; fsl_close FSL| ro_close| exact MU| exact WM].
  (* [comment removed for export] *)
  Ltac unCHf CHm :=
    let FSL := ident:(FSL) in let DSm := fresh "DSm" in let DE := fresh "DE" in let ROm := fresh "ROm" in
    unfold A0F_bzd_fr1.CHf in CHm; cps_destruct CHm as (DSm & DE & FSL & ROm & MU & WM); unDS DSm; unRO ROm; cps_destruct DE as (DSTA & DL & Edb & Lout);
    unfold A0F_bzd_fr1.FSLf, bzd_slots in FSL.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Let fr_G1 := A0F_bzd_fr1.fr_G1 c SHS w0 w32 w104 w112 OK OKF RD1 ANS SH KJ KE.
  Let fr_L1 := A0F_bzd_fr2.fr_L1 c SHS w0 w32 w104 w112 OK OKF RD1 ANS SH KE.
  Let fr_L2 := A0F_bzd_fr2.fr_L2 c SHS w0 w32 w104 w112 OK OKF RD1 ANS SH KE.
  Let fr_L3 := A0F_bzd_fr3.fr_L3 c SHS w0 w32 w104 w112 OK OKF RD1 ANS SH KE.
  Let fr_L4 := A0F_bzd_fr3.fr_L4 c SHS w0 w32 w104 w112 OK OKF RD1 ANS SH KE.
  Let fr_L5 := A0F_bzd_fr3.fr_L5 c SHS w0 w32 w104 w112 OK OKF ANS SH.

  (* [comment removed for export] *)
  Ltac dst_write av oc :=
    lazymatch goal with DSTA : u8arr _ _ DST ?bs, Edb : _ = map _ (rev ?out) ++ ?rst |- _ =>
      lazymatch goal with DL : Z.of_nat (length bs) = _ |- _ =>
      let r0 := fresh "r0" in let rest' := fresh "rest" in let LR := fresh "LR" in
      pose proof (f_equal (@length byte) Edb) as LR; rewrite length_app, length_map, length_rev in LR;
      destruct rst as [|r0 rest']; [exfalso; cbn [length] in LR; lia|]; cbn [length] in LR;
      let E' := fresh "Edb" in
      pose proof (dest_snoc out (r0 :: rest') oc r0 rest' eq_refl) as E';
      replace (length out) with (Z.to_nat (dlen - av)) in E' by lia; rewrite <- Edb in E'; clear Edb LR;
      let SOK := fresh "SOK" in
      pose proof (u8arr_store_ok a0segs _ DST _ (dlen - av) _ DSTA ltac:(lia) eq_refl) as SOK;
      wstep; rewrite BzInv.le1_lit;
      let D := fresh "DSTB" in
      pose proof (u8arr_write a0segs _ DST _ (dlen - av) (Z_to_bv 8 oc) DSTA ltac:(lia)) as D;
      clear DSTA; store_done; try clear SOK; rename D into DSTA;
      let D2 := fresh "DLB" in
      pose proof DL as D2; rewrite <- (upd_length bs (Z.to_nat (dlen - av)) (Z_to_bv 8 oc)) in D2; clear DL; rename D2 into DL;
      let db := fresh "dbytes" in
      remember (upd bs (Z.to_nat (dlen - av)) (Z_to_bv 8 oc)) as db eqn:Xdb; clear Xdb; rename E' into Edb
      end end.
  Ltac crc_load crc ch Hidx :=
    lazymatch goal with CRC : u32arr _ ?mm 802816 crc_words |- _ =>
      let RD := fresh "RD" in
      pose proof (u32arr_read a0segs mm 802816 crc_words (Z.lxor (crc / 16777216) ch) _ _ CRC (crc_words_nth _ Hidx) ltac:(lia) eq_refl) as RD;
      wstep; clear RD end.
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
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma fr_OUT : forall f ol, HS f (ol - 1) -> OUTS f ol.
  Proof.
    intros f ol IHH. unfold A0F_bzd_fr1.OUTS. intros until rest. intros CHm FI Hf Hol Hav1.
    unCHf CHm. prep. unSH. unFI FI.
    unfold DSgA, DESTgA in *. a0img. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in SAV. focbn_in Lout. focbn_in Edb.
    rewrite K_PH_step by (g8; lia). cbv zeta. g8.
    pose proof (sx32_mod32 cb ltac:(lia)) as Hcrc.
    pose proof (u8arr_bound _ _ _ _ DSTA) as DB.
    (* [comment removed for export] *)
    arun_to 0x85eb4%Z. ack_rd (DST + (dlen - av))%Z 1%Z.
    (* [comment removed for export] *)
    wstep. rewrite zxb_lit8 by lia.
    ack_merge.
    (* [comment removed for export] *)
    dst_write av oc.
    (* [comment removed for export] *)
    arun_to 0x85edc%Z. rewrite Hcrc.
    pose proof (crc_idx_byte cb oc ltac:(lia) ltac:(lia)) as Hidx.
    wstep. wstep. wstep. arun_to 0x85ef8%Z. crc_load cb oc Hidx. clear Hidx.
    wstep. wstep.
    pose proof (crc_step_rel (sx32 (Z_to_bv 64 cb)) cb oc Hcrc ltac:(lia) ltac:(lia)) as Hcrc'.
    pose proof (crc_update_range cb oc ltac:(lia)) as CR'.
    wstep.
    let crcw := reg_val 10%Z in recell MID crcw (crc_update cb oc); [| rewrite Hcrc'; symmetry; apply Z.mod_small; lia].
    (* [comment removed for export] *)
    arun_to 0x85f14%Z. try rewrite (sx32_of_Z ol) by lia. wstep. wstep.
    (* [comment removed for export] *)
    arun_to 0x85f54%Z.
    replace (DST + (dlen - av) + 1)%Z with (DST + (dlen - (av - 1)))%Z in SM by lia.
    (* [comment removed for export] *)
    arun_to 0x85f68%Z. try rewrite (sx32_of_Z av) by lia.
    (* [comment removed for export] *)
    arun_to 0x85f90%Z.
    Ltac fin IHH HD NBU MID SM DSTA DL Edb Lout FSL MU WM oc ol nu k0 tp rn rt cb out av tout Hf Hol Hav1 Ioc Iol Inu Ik0 Itp Irn Irt Icb Iav Rrnd Rsnb CR' :=
      let KA := fresh "KA" in
      wstep; if_cases KA; zify_cond KA;
      [ (* [comment removed for export] *)
        replace (av - 1 =? 0)%Z with true by (symmetry; apply Z.eqb_eq; clear -KA; lia);
        goJ HD NBU MID SM DSTA DL Edb Lout FSL MU WM;
        unfold id in Ik0, Rrnd; clear -Ioc Iol Inu Ik0 Itp Irn Irt Icb Iav Rrnd KA Rsnb CR' Hol Hav1; first [lia | intros; lia]
      | replace (av - 1 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; clear -KA; lia);
        wstep;
        unfold A0F_bzd_fr1.HS in IHH;
        lazymatch goal with DSTA' : u8arr _ _ DST ?db, Edb' : ?db = _ ++ ?r |- _ =>
          enter_with (IHH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ oc nu k0 tp rn rt (crc_update cb oc) (oc :: out) (av - 1)%Z (tout + 1)%Z _ _ db r) end;
        [ st_eq
        | ch_close HD NBU MID SM DSTA DL Edb Lout FSL MU WM
        | unfold S0F_bzd_fr1.finv; unfold id in Ik0; clear -Ioc Iol Inu Ik0 Itp Irn Irt Icb Iav CR' Hol Hav1; repeat match goal with |- _ /\ _ => split end; lia
        | exact Hf | clear -Hav1 KA; lia ] ].
    assert (Lout2 : Z.of_nat (length (oc :: out)) = (dlen - (av - 1))%Z) by (cbn [length]; clear -Lout; lia).
    wstep. if_cases KT; zify_cond KT; clear KT.
    - fin IHH HD NBU MID SM DSTA DL Edb Lout2 FSL MU WM oc ol nu k0 tp rn rt cb out av tout Hf Hol Hav1 Ioc Iol Inu Ik0 Itp Irn Irt Icb Iav Rrnd Rsnb CR'.
    - arun_to 0x85fb4%Z.
      fin IHH HD NBU MID SM DSTA DL Edb Lout2 FSL MU WM oc ol nu k0 tp rn rt cb out av tout Hf Hol Hav1 Ioc Iol Inu Ik0 Itp Irn Irt Icb Iav Rrnd Rsnb CR'.
  Time Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma fr_H : forall f ol, GS f -> OUTS f ol -> HS f ol.
  Proof.
    intros f ol G O. unfold A0F_bzd_fr1.HS. intros until rest. intros CHm FI Hf Hav1.
    pose proof CHm as CH0. pose proof FI as FI0.
    unCHf CHm. prep. unSH. unFI FI.
    unfold DSgA in *. a0img. focbn_in HD.
    (* [comment removed for export] *)
    arun_to 0x85e80%Z. try rewrite (sx32_of_Z ol) by lia.
    wstep. if_cases K1; zify_cond K1.
    - assert (E0 : ol = 0%Z) by (clear -K1 Iol; lia). subst ol.
      rewrite K_PH_0 by (g8; reflexivity).
      unfold A0F_bzd_fr1.GS in G.
      enter_with (G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ oc nu k0 tp rn rt cb out av tout tol toh dbytes rest); [st_eq| exact CH0| exact FI0| exact Hf| exact Hav1].
    - unfold A0F_bzd_fr1.OUTS in O.
      enter_with (O _ _ _ _ _ _ _ _ _ _ _ _ _ _ oc nu k0 tp rn rt cb out av tout tol toh dbytes rest); [st_eq| exact CH0| exact FI0| exact Hf| clear -K1 Iol; lia| exact Hav1].
  Time Qed.

  Lemma fr_M : forall f, (forall ol, HS f ol) -> MSx f.
  Proof.
    intros f H. unfold A0F_bzd_fr1.MSx. intros until rest. intros CHm FI Hf.
    pose proof CHm as CH0. pose proof FI as FI0.
    unCHf CHm. prep. unSH. unFI FI.
    unfold DSgA in *. a0img. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in SAV. focbn_in Lout.
    rewrite K_PM_eq. g8.
    (* [comment removed for export] *)
    wstep. try rewrite (sx32_of_Z av) by lia.
    wstep. if_cases K1; zify_cond K1.
    - replace (av =? 0)%Z with false by (symmetry; apply Z.eqb_neq; clear -K1; lia).
      pose proof (H ol) as Hh. unfold A0F_bzd_fr1.HS in Hh.
      enter_with (Hh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ oc nu k0 tp rn rt cb out av tout tol toh dbytes rest); [st_eq| exact CH0| exact FI0| exact Hf| clear -K1 Iav; lia].
    - replace (av =? 0)%Z with true by (symmetry; apply Z.eqb_eq; clear -K1; lia).
      wstep. goJ HD NBU MID SM DSTA DL Edb Lout FSL MU WM.
      all: unfold id in Ik0, Rrnd; clear -Ioc Iol Inu Ik0 Itp Irn Irt Icb Iav Rrnd K1 Rsnb; first [lia | intros; lia].
  Time Qed.

  Lemma fr_TL : forall f, MSx f -> TLS f.
  Proof.
    intros f M. unfold A0F_bzd_fr1.TLS. intros until rest. intros CHm FI Hf.
    pose proof CHm as CH0. pose proof FI as FI0.
    unCHf CHm. prep. unSH. unFI FI.
    unfold DSgA in *. a0img. focbn_in HD. focbn_in SM.
    (* [comment removed for export] *)
    arun_to 0x85e64%Z.
    unfold A0F_bzd_fr1.MSx in M.
    enter_with (M _ _ _ _ _ _ _ _ _ _ _ _ _ _ oc ol nu k0 tp rn rt cb out av tout tol toh dbytes rest); [st_eq| exact CH0| exact FI0| exact Hf].
  Time Qed.

  (* [comment removed for export] *)
  Lemma fr_HO : forall f, GS f -> forall k ol, Z.to_nat ol = k -> HS f ol /\ OUTS f ol.
  Proof.
    intros f G k. induction k as [k IH] using lt_wf_ind. intros ol Hk.
    assert (O : OUTS f ol).
    { apply fr_OUT.
      destruct (Z_lt_le_dec ol 1) as [L|L].
      - unfold A0F_bzd_fr1.HS. intros until rest. intros CHm FI Hf Hav1.
        unfold S0F_bzd_fr1.finv in FI. exfalso. clear -FI L. lia.
      - destruct (IH (Z.to_nat (ol - 1)) ltac:(lia) (ol - 1)%Z eq_refl) as [H' _]. exact H'. }
    split; [| exact O]. apply fr_H; [exact G | exact O].
  Qed.

  (* [comment removed for export] *)
  Lemma fr_knot : forall f, MSx f /\ TLS f /\ (forall ol, HS f ol) /\ GS f.
  Proof.
    induction f as [|f IH].
    all: match goal with |- MSx ?g /\ _ => assert (IHM : forall f', g = Datatypes.S f' -> TLS f') by (intros f' E; first [discriminate E | injection E as <-; exact (proj1 (proj2 IH))]) end.
    all: match goal with |- MSx ?g /\ _ =>
           pose proof (fr_G1 g (fr_L1 g (fr_L2 g (fr_L3 g (fr_L4 g (fr_L5 g IHM)) IHM) IHM) IHM)) as G;
           assert (HH : forall ol, HS g ol) by (intros ol; exact (proj1 (fr_HO g G (Z.to_nat ol) ol eq_refl)));
           pose proof (fr_M g HH) as M;
           split; [exact M| split; [exact (fr_TL g M)| split; [exact HH| exact G]]] end.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem A0F_fastr : forall (t0 t2 a0 a1 a3 a4 a5 a6 s3 s4 s7 t3 t4 t5 t6 : word) (m : word -> option byte) (dbytes rest : list byte),
    DSgA DI_A0 c m J d0 s0 -> DESTgA DI_A0 c m s0 dbytes rest -> A0F_bzd_fr1.FSLf c SHS w0 w32 w104 w112 m -> RO m -> munch WB m0 m -> wmono a0segs m0 m ->
    evt a0segs (KQ (unRLE d0 s0))
        (MS (A0RR c SHS (Z_to_bv 64 (SHS + 398)) t0 (Z_to_bv 64 (SHS + -2147450879)) t2 a0 a1 (Z_to_bv 64 (SHS + -2147450486)) a3 a4 a5 a6
                  (Z_to_bv 64 (SHS + -2147450878)) s3 s4 s7 t3 t4 t5 t6)
            F (Z_to_bv 64 0x85e3c) fc None m (seg_rom a0segs)).
  Proof.
    intros until rest. intros DSm DE FSL ROm MU WM.
    pose proof DSm as DSm0. pose proof DE as DE0. pose proof ROm as RO0. pose proof FSL as FSL0.
    unDS DSm. unRO ROm. cps_destruct DE as (DSTA & DL & Edb & Lout). prep. unSH.
    rewrite (unRLE_plain d0 s0 (Z.to_nat (PP + 2 - d_nused d0))); [| rewrite RD1; destruct (smallb d0); reflexivity | unfold id in NK0; clear -NK0 Rsnb; lia].
    cps_destruct (fr_knot (Z.to_nat (PP + 2 - d_nused d0))) as (M1 & _ & _ & _).
    remember (Z.to_nat (PP + 2 - d_nused d0)) as f eqn:Hf.
    unfold DSgA in *. a0img. dvF_cbn_in HD. dvF_cbn_in SM. unfold A0F_bzd_fr1.FSLf, bzd_slots in FSL.
    (* [comment removed for export] *)
    arun_to 0x85e64%Z.
    unfold A0F_bzd_fr1.MSx in M1.
    rewrite <- (set8_id d0), <- (smod_id s0).
    enter_with (M1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ (d_out_ch d0) (d_out_len d0) (d_nused d0) (d_k0 d0) (d_tPos d0) (d_rNToGo d0) (d_rTPos d0) (d_cbcrc d0)
                   (s_out s0) av0 (s_tout s0) (j_tol J) (j_toh J) dbytes rest);
      [ st_eq
      | unfold A0F_bzd_fr1.CHf; rewrite (set8_id d0), (smod_id s0), (jk_set_o_id J); repeat match goal with |- _ /\ _ => split end; [exact DSm0| exact DE0| exact FSL0| exact RO0| exact MU| exact WM]
      | unfold S0F_bzd_fr1.finv; unfold id in NK0, Rrnd; destruct (Rrnd RD1) as [RrN RrT]; clear -Roc0 Eol0 NK0 RtP0 RrN RrT Rcb0 Rav0 Rsnb En; rewrite <- En; repeat match goal with |- _ /\ _ => split end; lia
      | subst f; unfold id in NK0; clear -NK0 Rsnb; lia ].
  Time Qed.
End FR.

(* [comment removed for export] *)
Theorem A0F_fastr_ok : A0F_bzd_skV.FASTR_aspec.
Proof.
  unfold A0F_bzd_skV.FASTR_aspec, A0F_bzd_skV.FAST_aspec. intros c SHS w0 OK OKF ANS SH KJ KE. intros until rest. intros DSm DE FSL ROm MU WM RD1.
  eapply (A0F_fastr c SHS w0 w32 w104 w112 OK OKF RD1 ANS SH KJ KE); eassumption.
Qed.
End ACeilS1.
