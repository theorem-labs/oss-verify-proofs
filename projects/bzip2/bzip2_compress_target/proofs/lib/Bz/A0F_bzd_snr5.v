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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0F_bzd_snr1.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit DecCutA A0F_decV A0F_bzdV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require A0F_bzd_snr1 A0F_bzd_snr2 A0F_bzd_snr3 A0F_bzd_snr4.
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

Section SNR.
  Variable c : foctx.
  Variable SHS : Z. Variable w0 w32 : word.
  Notation cx := (o_cx c). Notation J := (o_J c). Notation d0 := (o_d c). Notation s0 := (o_s c).
  Notation S := (b_s (o_cx c)). Notation STRM := (b_strm (o_cx c)). Notation DST := (b_dst (o_cx c)). Notation dlen := (b_dlen (o_cx c)).
  Notation n := (b_n (o_cx c)). Notation L16 := (b_ll16 (o_cx c)). Notation L4 := (b_ll4 (o_cx c)).
  Notation snb := (sv_nblock (d_sv (o_d c))). Notation av0 := (s_avail_out (o_s c)). Notation PP := (sv_nblock (d_sv (o_d c)) + 1)%Z.
  Notation cap := (100000 * b_n (o_cx c))%Z.
  Notation cf := (d_cftab (o_d c)).
  Notation F := (o_F c). Notation fc := (o_fc c). Notation KQ := (o_KQ c). Notation m0 := (o_m0 c).
  Notation uspi := (bv_unsigned (o_SP c)).
  Notation RO := (FROsA DI_A0 c). Notation WB := (FWBA c).
  Notation SRR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 t3 t4 t5 t6 :=
    (mkR ra (o_SP c) (o_gp c) (o_tp c) t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 (b_s (o_cx c))) a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 (b_s (o_cx c) + 16)) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 2147450880) (Z_to_bv 64 (b_s (o_cx c) + 1096))
         (Z_to_bv 64 (b_s (o_cx c) + 3152)) t3 t4 t5 t6) (only parsing).
  Hypothesis OK : foctx_okA c AIHI0. Hypothesis OKS : foctx_okSA c AIHI0. Hypothesis RD0 : d_rand (o_d c) = 0%Z.
  Hypothesis ANS : sanchor S SHS.
  Hypothesis SH : obz_sh DI_A0 c WB m0.
  Hypothesis KJ : A0_FKjoin c SHS w0 (FROsA DI_A0 c).
  Hypothesis KE : A0_FKexit c SHS w0 (FROsA DI_A0 c).

  Notation pst := S0F_bzd_snr1.pst. Notation PST := S0F_bzd_snr1.PST.
  Notation p_oc := S0F_bzd_snr1.p_oc. Notation p_ol := S0F_bzd_snr1.p_ol. Notation p_nu := S0F_bzd_snr1.p_nu. Notation p_k0 := S0F_bzd_snr1.p_k0.
  Notation p_tp := S0F_bzd_snr1.p_tp. Notation p_rn := S0F_bzd_snr1.p_rn. Notation p_rt := S0F_bzd_snr1.p_rt. Notation p_cb := S0F_bzd_snr1.p_cb.
  Notation p_out := S0F_bzd_snr1.p_out. Notation p_av := S0F_bzd_snr1.p_av. Notation p_tout := S0F_bzd_snr1.p_tout.
  Notation p_tol := S0F_bzd_snr1.p_tol. Notation p_toh := S0F_bzd_snr1.p_toh.
  Notation D := (S0F_bzd_snr1.D c). Notation Ss := (S0F_bzd_snr1.Ss c). Notation Jp := (S0F_bzd_snr1.Jp c).
  Notation sinv := (S0F_bzd_snr1.sinv c).
  Notation CH := (A0F_bzd_snr1.CH c SHS w0 w32).
  Notation MS_ := (A0F_bzd_snr1.MS_ c SHS w0 w32). Notation TLS := (A0F_bzd_snr1.TLS c SHS w0 w32).
  Notation HS := (A0F_bzd_snr1.HS c SHS w0 w32). Notation OUTS := (A0F_bzd_snr1.OUTS c SHS w0 w32).
  Notation GS := (A0F_bzd_snr1.GS c SHS w0 w32).
  Notation T1S := (A0F_bzd_snr1.T1S c SHS w0 w32). Notation T2S := (A0F_bzd_snr1.T2S c SHS w0 w32). Notation T3S := (A0F_bzd_snr1.T3S c SHS w0 w32).
  Notation T4S := (A0F_bzd_snr1.T4S c SHS w0 w32). Notation T5S := (A0F_bzd_snr1.T5S c SHS w0 w32).

  Notation cstrm := (Z_to_bv 64 (b_strm (o_cx c))). Notation csnb := (Z_to_bv 64 (sv_nblock (d_sv (o_d c)))).
  Notation cnn := (Z_to_bv 64 (b_n (o_cx c) * 100000)).
  Notation cm4 := (Z_to_bv 64 (-4)).
  Notation cl16 := (Z_to_bv 64 (b_ll16 (o_cx c))). Notation cl4 := (Z_to_bv 64 (b_ll4 (o_cx c))).

  (* [comment removed for export] *)
  Ltac pcut := cbn [S0F_bzd_snr1.p_oc S0F_bzd_snr1.p_ol S0F_bzd_snr1.p_nu S0F_bzd_snr1.p_k0 S0F_bzd_snr1.p_tp S0F_bzd_snr1.p_rn S0F_bzd_snr1.p_rt
                    S0F_bzd_snr1.p_cb S0F_bzd_snr1.p_out S0F_bzd_snr1.p_av S0F_bzd_snr1.p_tout S0F_bzd_snr1.p_tol S0F_bzd_snr1.p_toh].
  Ltac pcut_in H := cbn [S0F_bzd_snr1.p_oc S0F_bzd_snr1.p_ol S0F_bzd_snr1.p_nu S0F_bzd_snr1.p_k0 S0F_bzd_snr1.p_tp S0F_bzd_snr1.p_rn S0F_bzd_snr1.p_rt
                    S0F_bzd_snr1.p_cb S0F_bzd_snr1.p_out S0F_bzd_snr1.p_av S0F_bzd_snr1.p_tout S0F_bzd_snr1.p_tol S0F_bzd_snr1.p_toh] in H.
  Ltac pcut_all := cbn [S0F_bzd_snr1.p_oc S0F_bzd_snr1.p_ol S0F_bzd_snr1.p_nu S0F_bzd_snr1.p_k0 S0F_bzd_snr1.p_tp S0F_bzd_snr1.p_rn S0F_bzd_snr1.p_rt
                    S0F_bzd_snr1.p_cb S0F_bzd_snr1.p_out S0F_bzd_snr1.p_av S0F_bzd_snr1.p_tout S0F_bzd_snr1.p_tol S0F_bzd_snr1.p_toh] in *.
  Ltac unRO H := let GOT := ident:(GOT) in cps_destruct H as (SAV & L16A & L4A & CFA & CRC & RNA & GOT & MI); unfold FGOTA in GOT; a0img.
  Ltac unDS H := cps_destruct H as (HD & NBU & MID & SM).
  Ltac unCH H := let DSm := fresh "DSm" in let DE := fresh "DE" in let ROm := fresh "ROm" in let FSL := ident:(FSL) in
    cps_destruct H as (DSm & DE & FSL & ROm & MU & WM); unDS DSm; cps_destruct DE as (DSTA & DL & Edb & Lout); unRO ROm;
    unfold A0F_bzd_snr1.FSLs, bzd_slots in FSL.
  Ltac unSH := let SHbs := ident:(SHbs) in let SH' := fresh "SH" in pose proof SH as SH';
    cps_destruct SH' as (SHs & SHt & SHd & SHc & SHr & _ & SHbs); a0img;
    let OKS' := fresh "OKS" in pose proof OKS as OKS'; specialize (SHbs (proj1 OKS')); clear OKS';
    cps_destruct SHbs as (SH16 & SH4).
  Ltac prep :=
    let JWF := ident:(JWF) in let ENT := ident:(ENT) in let OK' := fresh "OK" in pose proof OK as OK';
    cps_destruct OK' as (HS & HSTRM & HDST & Hdlen & HSP & HAL & SEP_SM & SEP_SD & SEP_MD & IAS & IAM & IAD & HIHI & JWF & ENT);
    let OKS' := fresh "OKS" in pose proof OKS as OKS';
    cps_destruct OKS' as (HSM & HL16 & HL4 & SEP_S16 & SEP_M16 & SEP_D16 & SEP_S4 & SEP_M4 & SEP_D4 & SEP_164 & IA16 & IA4);
    cps_destruct ENT as (En & Rn & Esm & Rsnb & Rsnb1 & Rav0 & Lout0 & Eol0 & RtP0 & NK0 & Rcb0 & Roc0 & Rr01 & Rrnd & Rcf & Rtt & Rl16 & Rl4);
    cps_destruct JWF as (Lp1 & Lp2 & Lp3 & Ls1 & Ls2 & Lq1 & Lq2);
    unfold disj, bzd_img_apart in *;
    unfold FWBA, FWB in *; cbn [app] in *; pose proof alloc_ceiling_range as ACR;
    pose proof (zw32_length cf 257 ltac:(lia)) as CFL;
    pose proof (zh16_length (d_ll16 d0) (200000 * n) ltac:(lia)) as L16L; pose proof (zb8_length (d_ll4 d0) (50000 * n) ltac:(lia)) as L4L;
    pose proof rnums_words_length as RNL; pose proof crc_words_length as CRCL;
    pose proof (proj2 ANS : saddr S SHS) as ANS0;
    hide_disj.
  Ltac ro_close := unfold FROsA, FGOTA; a0img; repeat match goal with |- _ /\ _ => split end; assumption.
  (* [comment removed for export] *)
  Ltac dsg_close := let HD := ident:(HD) in let NBU := ident:(NBU) in let MID := ident:(MID) in let SM := ident:(SM) in
    unfold DSgA; a0img; focbn; repeat match goal with |- _ /\ _ => split end; [exact_cells HD | exact_cells NBU | exact_cells MID | exact_cells SM].
  Ltac destg_close := unfold DESTgA; a0img; focbn; repeat match goal with |- _ /\ _ => split end; first [eassumption | cbn [length]; lia].
  Ltac fsl_close := let FSL := ident:(FSL) in first [ exact FSL | unfold bzd_slots; exact FSL | unfold A0F_bzd_snr1.FSLs, bzd_slots; exact FSL ].
  Ltac ch_close MU WM := repeat match goal with |- _ /\ _ => split end; [dsg_close | destg_close | fsl_close | ro_close | exact MU | exact WM].
  (* [comment removed for export] *)
  Ltac unhide_k0 := try match goal with H : id ((0 <= _ < 256)%Z \/ _) |- _ => unfold id in H end.
  Ltac sinv_close := unfold S0F_bzd_snr1.sinv; pcut;
    repeat match goal with |- _ /\ _ => split end; first [assumption | cbn [length]; lia].
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac joinK MU WM := eapply KJ; [dsg_close | destg_close | fsl_close | ro_close | exact MU | exact WM | ];
    unfold ojoin; focbn; unhide_k0; repeat match goal with |- _ /\ _ => split end;
    first [assumption | lia | intros; exfalso; let RD0 := ident:(RD0) in rewrite RD0 in *; lia | idtac].
  Let snr_G := A0F_bzd_snr2.snr_G c SHS w0 w32 OK OKS RD0 ANS SH KJ KE.
  Let snr_T1 := A0F_bzd_snr3.snr_T1 c SHS w0 w32 OK OKS RD0 ANS SH KE.
  Let snr_T2 := A0F_bzd_snr3.snr_T2 c SHS w0 w32 OK OKS RD0 ANS SH KE.
  Let snr_T3 := A0F_bzd_snr4.snr_T3 c SHS w0 w32 OK OKS RD0 ANS SH KE.
  Let snr_T4 := A0F_bzd_snr4.snr_T4 c SHS w0 w32 OK OKS RD0 ANS SH KE.
  Let snr_T5 := A0F_bzd_snr4.snr_T5 c SHS w0 w32 OK OKS RD0 ANS SH.

  (* [comment removed for export] *)
  Ltac dst_write av oc :=
    lazymatch goal with DSTA : u8arr _ _ DST ?bs, Edb : _ = map _ (rev ?out) ++ ?rst |- _ =>
      lazymatch goal with DL : Z.of_nat (length bs) = _ |- _ =>
      (* [comment removed for export] *)
      let r0 := fresh "r0" in let rest' := fresh "rest" in let LR := fresh "LR" in
      pose proof (f_equal (@length byte) Edb) as LR; rewrite length_app, length_map, length_rev in LR;
      destruct rst as [|r0 rest']; [exfalso; cbn [length] in LR; lia|]; cbn [length] in LR;
      let E' := fresh "Edb" in
      pose proof (dest_snoc out (r0 :: rest') oc r0 rest' eq_refl) as E';
      replace (length out) with (Z.to_nat (dlen - av)) in E' by lia; rewrite <- Edb in E'; clear Edb LR;
      (* [comment removed for export] *)
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
  (* [comment removed for export] *)
  Ltac crc_load crc ch Hidx :=
    lazymatch goal with CRC : u32arr _ ?mm 802816 crc_words |- _ =>
      let RD := fresh "RD" in
      pose proof (u32arr_read a0segs mm 802816 crc_words (Z.lxor (crc / 16777216) ch) _ _ CRC (crc_words_nth _ Hidx) ltac:(lia) eq_refl) as RD;
      wstep; clear RD end.
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
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma snr_OUT : forall f p,
    (forall p', p_ol p' = (p_ol p - 1)%Z -> HS f p') -> OUTS f p.
  Proof.
    intros f p IHH. unfold A0F_bzd_snr1.OUTS. intros until rest. intros CHm SI Hf Hav Hol.
    destruct p as [oc ol nu k0 tp rn rt cb out av tout tol toh].
    unfold A0F_bzd_snr1.CH, S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp, S0F_bzd_snr1.sinv in *.
    pcut_all.
    cps_destruct SI as (Rcb & Roc & Rol & Rnu & Rk0 & Rtp & Ern & Ert & Rav & Lout').
    unCH CHm. prep. unSH.
    unfold DSgA, DESTgA in *. a0img. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in SAV. focbn_in Edb. focbn_in Lout.
    rewrite K_PH_step by (s8; lia). cbv zeta. s8.
    pose proof (sx32_mod32 cb ltac:(lia)) as Hcrc.
    pose proof (u8arr_bound _ _ _ _ DSTA) as DB.
    (* [comment removed for export] *)
    arun_to 0x85c68%Z. ack_rd (DST + (dlen - av))%Z 1%Z.
    (* [comment removed for export] *)
    wstep. rewrite zxb_lit8 by lia.
    ack_merge.
    (* [comment removed for export] *)
    dst_write av oc.
    (* [comment removed for export] *)
    arun_to 0x85c90%Z. rewrite Hcrc.
    (* [comment removed for export] *)
    pose proof (crc_idx_byte cb oc ltac:(lia) ltac:(lia)) as Hidx.
    wstep. wstep. wstep. arun_to 0x85cac%Z. crc_load cb oc Hidx. clear Hidx.
    (* [comment removed for export] *)
    wstep. wstep.
    pose proof (crc_step_rel (sx32 (Z_to_bv 64 cb)) cb oc Hcrc ltac:(lia) ltac:(lia)) as Hcrc'.
    pose proof (crc_update_range cb oc ltac:(lia)) as CR'.
    (* [comment removed for export] *)
    wstep.
    let crcw := reg_val 10%Z in recell MID crcw (crc_update cb oc); [| rewrite Hcrc'; symmetry; apply Z.mod_small; lia].
    (* [comment removed for export] *)
    arun_to 0x85cc8%Z. try rewrite (sx32_of_Z ol) by lia. wstep. wstep.
    (* [comment removed for export] *)
    arun_to 0x85d08%Z.
    replace (DST + (dlen - av) + 1)%Z with (DST + (dlen - (av - 1)))%Z in SM by lia.
    (* [comment removed for export] *)
    arun_to 0x85d1c%Z. try rewrite (sx32_of_Z av) by lia.
    (* [comment removed for export] *)
    arun_to 0x85d44%Z.
    (* [comment removed for export] *)
    Ltac fin IHH MU WM oc ol nu k0 tp rn rt cb out av tout dbytes rest :=
      let KA := fresh "KA" in
      wstep; if_cases KA; zify_cond KA;
      [ rewrite (proj2 (Z.eqb_neq (av - 1) 0)) by lia;
        enter_with (IHH (PST oc (ol - 1) nu k0 tp rn rt (crc_update cb oc) (oc :: out) (av - 1) (tout + 1) _ _) eq_refl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dbytes rest);
        [ pcut; unfold S0F_bzd_snr1.D, S0F_bzd_snr1.Ss; st_eq
        | unfold A0F_bzd_snr1.CH; unfold S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp; pcut; ch_close MU WM
        | sinv_close
        | pcut; lia
        | pcut; lia ]
      | (* [comment removed for export] *)
        rewrite (proj2 (Z.eqb_eq (av - 1) 0)) by lia;
        wstep; joinK MU WM ].
    wstep. if_cases KT; zify_cond KT.
    - lazymatch goal with DSTA : u8arr _ _ DST ?db, Edb : ?db = _ ++ ?r |- _ => fin IHH MU WM oc ol nu k0 tp rn rt cb out av tout db r end.
    - arun_to 0x85d68%Z.
      lazymatch goal with DSTA : u8arr _ _ DST ?db, Edb : ?db = _ ++ ?r |- _ => fin IHH MU WM oc ol nu k0 tp rn rt cb out av tout db r end.
  Time Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma snr_H : forall f p, GS f p -> OUTS f p -> HS f p.
  Proof.
    intros f p G O. unfold A0F_bzd_snr1.HS. intros until rest. intros CHm SI Hf Hav.
    pose proof CHm as CH0. pose proof SI as SI0.
    destruct p as [oc ol nu k0 tp rn rt cb out av tout tol toh].
    unfold A0F_bzd_snr1.CH, S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp, S0F_bzd_snr1.sinv in CHm, SI, Hf, Hav |- *.
    pcut_all.
    cps_destruct SI as (Rcb & Roc & Rol & Rnu & Rk0 & Rtp & Ern & Ert & Rav & Lout').
    unCH CHm. prep. unSH.
    unfold DSgA in *. a0img. focbn_in HD.
    (* [comment removed for export] *)
    arun_to 0x85c34%Z. try rewrite (sx32_of_Z ol) by lia.
    (* [comment removed for export] *)
    wstep. if_cases K0; zify_cond K0.
    - rewrite K_PH_0 by (s8; lia). unfold A0F_bzd_snr1.GS in G.
      enter_with (G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dbytes rest); [st_eq | exact CH0 | exact SI0 | pcut; lia | pcut; lia | pcut; lia].
    - unfold A0F_bzd_snr1.OUTS in O.
      enter_with (O _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dbytes rest); [st_eq | exact CH0 | exact SI0 | pcut; lia | pcut; lia | pcut; lia].
  Time Qed.

  Lemma snr_M : forall f p, HS f p -> MS_ f p.
  Proof.
    intros f p H. unfold A0F_bzd_snr1.MS_. intros until rest. intros CHm SI Hf.
    pose proof CHm as CH0. pose proof SI as SI0.
    destruct p as [oc ol nu k0 tp rn rt cb out av tout tol toh].
    unfold A0F_bzd_snr1.CH, S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp, S0F_bzd_snr1.sinv in CHm, SI, Hf |- *.
    pcut_all.
    cps_destruct SI as (Rcb & Roc & Rol & Rnu & Rk0 & Rtp & Ern & Ert & Rav & Lout').
    unCH CHm. prep.
    unfold DSgA in *. a0img. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in SAV. focbn_in Edb. focbn_in Lout.
    (* [comment removed for export] *)
    wstep. if_cases K0; zify_cond K0.
    - rewrite K_PM_go by (s8; lia).
      unfold A0F_bzd_snr1.HS in H.
      enter_with (H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dbytes rest); [st_eq | exact CH0 | exact SI0 | pcut; lia | pcut; lia].
    - rewrite K_PM_ret by (s8; lia). wstep. joinK MU WM.
  Time Qed.

  Lemma snr_TL : forall f p, MS_ f p -> TLS f p.
  Proof.
    intros f p M. unfold A0F_bzd_snr1.TLS. intros until rest. intros CHm SI Hf.
    pose proof CHm as CH0. pose proof SI as SI0.
    destruct p as [oc ol nu k0 tp rn rt cb out av tout tol toh].
    unfold A0F_bzd_snr1.CH, S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp, S0F_bzd_snr1.sinv in CHm, SI, Hf |- *.
    pcut_all.
    cps_destruct SI as (Rcb & Roc & Rol & Rnu & Rk0 & Rtp & Ern & Ert & Rav & Lout').
    unCH CHm. prep. unSH.
    unfold DSgA in *. a0img. focbn_in HD. focbn_in SM.
    (* [comment removed for export] *)
    arun_to 0x856d8%Z. try rewrite (sx32_of_Z av) by lia.
    (* [comment removed for export] *)
    wstep.
    unfold A0F_bzd_snr1.MS_ in M.
    enter_with (M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dbytes rest); [st_eq | exact CH0 | exact SI0 | pcut; lia].
  Time Qed.

  (* [comment removed for export] *)
  Lemma snr_HO : forall f, (forall p, GS f p) -> forall k p, Z.to_nat (p_ol p) = k -> HS f p /\ OUTS f p.
  Proof.
    intros f G k. induction k as [k IH] using lt_wf_ind. intros p Hk.
    assert (O : OUTS f p).
    { apply snr_OUT. intros p' E'.
      destruct (Z_lt_le_dec (p_ol p) 1) as [L|L].
      - unfold A0F_bzd_snr1.HS. intros until rest. intros CHm SI Hf Hav.
        unfold S0F_bzd_snr1.sinv in SI. exfalso. lia.
      - destruct (IH (Z.to_nat (p_ol p')) ltac:(lia) p' eq_refl) as [H' _]. exact H'. }
    split; [| exact O]. apply snr_H; [apply G | exact O].
  Qed.

  (* [comment removed for export] *)
  Lemma snr_knot : forall f,
    (forall p, GS f p) /\ (forall p, HS f p) /\ (forall p, OUTS f p) /\ (forall p, MS_ f p) /\ (forall p, TLS f p).
  Proof.
    induction f as [|f IH].
    - assert (G : forall p, GS 0%nat p) by (intros p; apply snr_G; intros f' p' E; discriminate E).
      assert (HO : forall p, HS 0%nat p /\ OUTS 0%nat p) by (intros p; eapply (snr_HO 0%nat G); reflexivity).
      assert (M : forall p, MS_ 0%nat p) by (intros p; apply snr_M; apply (proj1 (HO p))).
      repeat split; try apply G; try (intros p; apply (proj1 (HO p))); try (intros p; apply (proj2 (HO p))); try apply M.
      intros p. apply snr_TL. apply M.
    - cps_destruct IH as (G' & H' & O' & M' & TL').
      pose proof (snr_T5 f TL') as T5.
      pose proof (snr_T4 f T5) as T4.
      pose proof (snr_T3 f T4 TL') as T3.
      pose proof (snr_T2 f T3 TL') as T2.
      pose proof (snr_T1 f T2 TL') as T1.
      assert (G : forall p, GS (Datatypes.S f) p).
      { intros p; apply snr_G; intros f' p' E; injection E as <-; apply T1. }
      assert (HO : forall p, HS (Datatypes.S f) p /\ OUTS (Datatypes.S f) p) by (intros p; eapply (snr_HO _ G); reflexivity).
      assert (M : forall p, MS_ (Datatypes.S f) p) by (intros p; apply snr_M; apply (proj1 (HO p))).
      repeat split; try apply G; try (intros p; apply (proj1 (HO p))); try (intros p; apply (proj2 (HO p))); try apply M.
      intros p. apply snr_TL. apply M.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem A0F_smallnr : forall (t0 t2 a2 a3 a4 a5 a6 s3 s4 s7 t3 t4 t5 t6 : word) (m : word -> option byte) (dbytes rest : list byte),
    DSgA DI_A0 c m J d0 s0 -> DESTgA DI_A0 c m s0 dbytes rest -> A0F_bzd_snr1.FSLs c SHS w0 w32 m -> RO m -> munch WB m0 m -> wmono a0segs m0 m ->
    evt a0segs (KQ (unRLE d0 s0))
      (MS (SRR (Z_to_bv 64 (SHS + 398)) t0 (Z_to_bv 64 (SHS + -2147450879)) t2 (Z_to_bv 64 (s_avail_out s0)) cstrm a2 a3 a4 a5 a6
               (Z_to_bv 64 (SHS + -2147450878)) s3 s4 (Z_to_bv 64 SHS) (Z_to_bv 64 (b_s (o_cx c) + 12)) s7 (Z_to_bv 64 (b_s (o_cx c) + 3184)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x85c1c) fc None m (seg_rom a0segs)).
  Proof.
    intros until rest. intros DSm DE FSL ROm MU WM.
    pose proof OK as OK'. cps_destruct OK' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ENT).
    cps_destruct ENT as (En & Rn & Esm & Rsnb & Rsnb1 & Rav0 & Lout0 & Eol0 & RtP0 & NK0 & Rcb0 & Roc0 & Rr01 & Rrnd & _).
    pose proof (proj1 OKS) as HSM.
    assert (SMT : smallb d0 = true) by (unfold smallb; rewrite Esm, HSM; reflexivity).
    unfold id in NK0.
    rewrite (unRLE_plain d0 s0 (Z.to_nat (PP + 2 - d_nused d0))) by (first [rewrite SMT; reflexivity | lia]).
    cps_destruct (snr_knot (Z.to_nat (PP + 2 - d_nused d0))) as (_ & _ & _ & M1 & _).
    remember (Z.to_nat (PP + 2 - d_nused d0)) as f eqn:Hf.
    set (p0 := PST (d_out_ch d0) (d_out_len d0) (d_nused d0) (d_k0 d0) (d_tPos d0) (d_rNToGo d0) (d_rTPos d0) (d_cbcrc d0)
                   (s_out s0) (s_avail_out s0) (s_tout s0) (j_tol J) (j_toh J)).
    assert (ED : set8 d0 (d_out_ch d0) (d_out_len d0) (d_nused d0) (d_k0 d0) (d_tPos d0) (d_rNToGo d0) (d_rTPos d0) (d_cbcrc d0) = d0) by apply set8_id.
    assert (ES : smod s0 (s_out s0) (s_avail_out s0) (s_tout s0) = s0) by apply smod_id.
    assert (EJ : jk_set_o J (j_tol J) (j_toh J) = J) by apply jk_set_o_id.
    pose proof (M1 p0) as M. unfold A0F_bzd_snr1.MS_, A0F_bzd_snr1.CH in M. subst p0.
    unfold S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp in M. pcut_in M.
    rewrite ED, ES, EJ in M.
    cps_destruct DE as (DSTA & DL & Edb & Lout).
    enter_with (M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dbytes rest);
      [ st_eq
      | repeat match goal with |- _ /\ _ => split end; [exact DSm | unfold DESTgA; repeat match goal with |- _ /\ _ => split end; assumption | exact FSL | exact ROm | exact MU | exact WM]
      | unfold S0F_bzd_snr1.sinv; pcut;
        repeat match goal with |- _ /\ _ => split end; first [lia | reflexivity | exact Lout]
      | lia ].
  Time Qed.
End SNR.

(* [comment removed for export] *)
Theorem A0F_smallnr_ok : forall (c : foctx) (SHS : Z) (w0 : word),
  foctx_okA c AIHI0 -> foctx_okSA c AIHI0 -> sanchor (b_s (o_cx c)) SHS -> obz_sh DI_A0 c (FWBA c) (o_m0 c) ->
  A0_FKjoin c SHS w0 (FROsA DI_A0 c) -> A0_FKexit c SHS w0 (FROsA DI_A0 c) ->
  forall (t0 t2 a2 a3 a4 a5 a6 s3 s4 s7 t3 t4 t5 t6 w32 : word) (m : word -> option byte) (dbytes rest : list byte),
    DSgA DI_A0 c m (o_J c) (o_d c) (o_s c) -> DESTgA DI_A0 c m (o_s c) dbytes rest -> A0F_bzd_snr1.FSLs c SHS w0 w32 m ->
    FROsA DI_A0 c m -> munch (FWBA c) (o_m0 c) m -> wmono a0segs (o_m0 c) m ->
    d_rand (o_d c) = 0%Z ->
    evt a0segs (o_KQ c (unRLE (o_d c) (o_s c)))
      (MS (mkR (Z_to_bv 64 (SHS + 398)) (o_SP c) (o_gp c) (o_tp c) t0 (Z_to_bv 64 (SHS + -2147450879)) t2 (Z_to_bv 64 1) (Z_to_bv 64 (b_s (o_cx c)))
               (Z_to_bv 64 (s_avail_out (o_s c))) (Z_to_bv 64 (b_strm (o_cx c))) a2 a3 a4 a5 a6 (Z_to_bv 64 (SHS + -2147450878))
               (Z_to_bv 64 (b_s (o_cx c) + 16)) s3 s4 (Z_to_bv 64 SHS) (Z_to_bv 64 (b_s (o_cx c) + 12)) s7 (Z_to_bv 64 (b_s (o_cx c) + 3184))
               (Z_to_bv 64 2147450880) (Z_to_bv 64 (b_s (o_cx c) + 1096)) (Z_to_bv 64 (b_s (o_cx c) + 3152)) t3 t4 t5 t6)
          (o_F c) (Z_to_bv 64 0x85c1c) (o_fc c) None m (seg_rom a0segs)).
Proof.
  intros c SHS w0 OK OKS ANS SH KJ KE. intros until rest. intros DSm DE FSL ROm MU WM RD0.
  eapply (A0F_smallnr c SHS w0 w32 OK OKS RD0 ANS SH KJ KE); eassumption.
Qed.
End ACeilS1.
