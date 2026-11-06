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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0 StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzTac BzDefs BzInv BzTables BzLemmasT BzLemmasMtf BzWalkArith BzWalkArith2 S0_bzd_out BzSepTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem CmpArith BzCLemmas1.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDOut BzDOK BzDOKp BzDOKS DecCutF DecTacF.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKp OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKS OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import S0F_bzd_out S0F_bzd_outS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0F_bzd_snr1.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0F_bzd_fr1 S0F_bzd_fr2 S0F_bzd_fr3.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac2 AsanKit AsanCut AsanCutB0 AsanKitB0 DecCutB B0F_decV B0F_bzdV B0F_bzd_uV B0F_leafCut.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import S0F_bzd_outS S0F_bzd_fr1 S0F_bzd_fr2 S0F_bzd_fr3 S0F_bzd_outR S0F_bzd_snr1 S0F_bzd_sr1.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require B0F_bzd_sr1 B0F_bzd_sr2 B0F_bzd_sr3 B0F_bzd_sr4 B0F_bzd_sr5 B0F_bzd_sr6 B0F_bzd_sr7 B0F_bzd_sr8 B0F_bzd_srH B0F_bzd_srT B0F_bzd_skV.
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
Local Ltac AsanKit.a_norm ::= AsanKit.sh_fold; AsanKit.sh_norm.
Section ACeilS1. Context {ACEIL__ : ACeil}.

Section SR.
  Variable c : foctx.
  Variable SHS : Z. Variable w0 : word. Variable slo : Z.
  Notation cx := (o_cx c). Notation J := (o_J c). Notation d0 := (o_d c). Notation s0 := (o_s c).
  Notation S := (b_s (o_cx c)). Notation STRM := (b_strm (o_cx c)). Notation DST := (b_dst (o_cx c)). Notation dlen := (b_dlen (o_cx c)).
  Notation n := (b_n (o_cx c)). Notation L16 := (b_ll16 (o_cx c)). Notation L4 := (b_ll4 (o_cx c)).
  Notation snb := (sv_nblock (d_sv (o_d c))). Notation av0 := (s_avail_out (o_s c)). Notation PP := (sv_nblock (d_sv (o_d c)) + 1)%Z.
  Notation cap := (100000 * b_n (o_cx c))%Z.
  Notation cf := (d_cftab (o_d c)).
  Notation F := (o_F c). Notation fc := (o_fc c). Notation KQ := (o_KQ c). Notation m0 := (o_m0 c).
  Notation uspi := (bv_unsigned (o_SP c)).
  Notation RO := (FROsB c slo). Notation WB := (FWBAc c).
  Hypothesis OK : foctx_okA c BIHI0. Hypothesis OKS : foctx_okSA c BIHI0.
  Hypothesis OKB : (BIHI0 <= slo /\ alloc_ceiling <= slo /\ slo + 16 <= bv_unsigned (o_SP c) /\ BIHI0 <= b_s (o_cx c) /\ b_ll16 (o_cx c) mod 2 = 0)%Z.
  Hypothesis ANS : sanchor S SHS.
  Hypothesis SH : obz_sh DI_B0 c WB m0.
  Hypothesis KJ : B0_FKjoin c SHS w0 (FROsB c slo) (FWBAc c).
  Hypothesis KE : B0_FKexit c SHS w0 (FROsB c slo) (FWBAc c).

  (* [comment removed for export] *)
  Notation pst := S0F_bzd_snr1.pst. Notation PST := S0F_bzd_snr1.PST.
  Notation p_oc := S0F_bzd_snr1.p_oc. Notation p_ol := S0F_bzd_snr1.p_ol. Notation p_nu := S0F_bzd_snr1.p_nu. Notation p_k0 := S0F_bzd_snr1.p_k0.
  Notation p_tp := S0F_bzd_snr1.p_tp. Notation p_rn := S0F_bzd_snr1.p_rn. Notation p_rt := S0F_bzd_snr1.p_rt. Notation p_cb := S0F_bzd_snr1.p_cb.
  Notation p_out := S0F_bzd_snr1.p_out. Notation p_av := S0F_bzd_snr1.p_av. Notation p_tout := S0F_bzd_snr1.p_tout.
  Notation p_tol := S0F_bzd_snr1.p_tol. Notation p_toh := S0F_bzd_snr1.p_toh.
  Notation D := (S0F_bzd_snr1.D c). Notation Ss := (S0F_bzd_snr1.Ss c). Notation Jp := (S0F_bzd_snr1.Jp c).
  Notation sinv := (S0F_bzd_snr1.sinv c).
  Notation sinvR := (S0F_bzd_sr1.sinvR c). Notation DR := (S0F_bzd_sr1.DR c).

  Notation cstrm := (Z_to_bv 64 (b_strm (o_cx c))). Notation csnb := (Z_to_bv 64 (sv_nblock (d_sv (o_d c)))).
  Notation cpp := (Z_to_bv 64 (sv_nblock (d_sv (o_d c)) + 1)). Notation cnn := (Z_to_bv 64 (b_n (o_cx c) * 100000)).
  Notation cm4 := (Z_to_bv 64 (-4)).
  Notation cl16 := (Z_to_bv 64 (b_ll16 (o_cx c))). Notation cl4 := (Z_to_bv 64 (b_ll4 (o_cx c))).
  (* [comment removed for export] *)
  Notation hs7 := (Z_to_bv 64 (SHS + -2147450878)).   (* [comment removed for export] *)
  Notation hs9 := (Z_to_bv 64 (SHS + -2147450879)).   (* [comment removed for export] *)
  Notation c16 := (Z_to_bv 64 (SHS + 2)).             (* [comment removed for export] *)
  Notation c40 := (Z_to_bv 64 (SHS + 5)).             (* [comment removed for export] *)
  Notation c60 := (Z_to_bv 64 (SHS + 7)).             (* [comment removed for export] *)
  Notation c64 := (Z_to_bv 64 (SHS + 8)).             (* [comment removed for export] *)
  Notation cnu := (Z_to_bv 64 (SHS + 136)).           (* [comment removed for export] *)
  Notation c3160 := (Z_to_bv 64 (SHS + 395)).         (* [comment removed for export] *)
  Notation c3168 := (Z_to_bv 64 (SHS + 396)).         (* [comment removed for export] *)
  Notation csnbsh := (Z_to_bv 64 (SHS + 8010)).       (* [comment removed for export] *)

  (* [comment removed for export] *)
  Hypothesis RD1 : d_rand (o_d c) = 1%Z.
  Notation CH := (B0F_bzd_sr1.CH c SHS w0 slo).
  Notation H0S := (B0F_bzd_sr1.H0S c SHS w0 slo). Notation GS := (B0F_bzd_sr1.GS c SHS w0 slo). Notation MS_ := (B0F_bzd_sr1.MS_ c SHS w0 slo).
  Ltac pcut := cbn [S0F_bzd_snr1.p_oc S0F_bzd_snr1.p_ol S0F_bzd_snr1.p_nu S0F_bzd_snr1.p_k0 S0F_bzd_snr1.p_tp S0F_bzd_snr1.p_rn S0F_bzd_snr1.p_rt
                    S0F_bzd_snr1.p_cb S0F_bzd_snr1.p_out S0F_bzd_snr1.p_av S0F_bzd_snr1.p_tout S0F_bzd_snr1.p_tol S0F_bzd_snr1.p_toh].
  Ltac pcut_in H := cbn [S0F_bzd_snr1.p_oc S0F_bzd_snr1.p_ol S0F_bzd_snr1.p_nu S0F_bzd_snr1.p_k0 S0F_bzd_snr1.p_tp S0F_bzd_snr1.p_rn S0F_bzd_snr1.p_rt
                    S0F_bzd_snr1.p_cb S0F_bzd_snr1.p_out S0F_bzd_snr1.p_av S0F_bzd_snr1.p_tout S0F_bzd_snr1.p_tol S0F_bzd_snr1.p_toh] in H.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac unRO H := let GOT := ident:(GOT) in let ACG := ident:(ACG) in let ACV := ident:(ACV) in
    cps_destruct H as ((SAV & L16A & L4A & CFA & CRC & RNA & GOT & MI) & (ACG & ACV) & STK); unfold FGOTA in GOT; b0img;
    cbn [aci_segs aci_got_sh aci_shvar aci_c CmpCut.ci_segs B0C] in ACG, ACV.
  Ltac unDS H := cps_destruct H as (HD & NBU & MID & SM).
  (* [comment removed for export] *)
  Ltac unSH := let SHbs := ident:(SHbs) in let SH' := fresh "SH" in pose proof SH as SH';
    cps_destruct SH' as (SHs & SHt & SHd & SHc & SHr & _ & SHbs); b0img;
    let OKS' := fresh "OKS" in pose proof OKS as OKS'; specialize (SHbs (proj1 OKS')); clear OKS';
    cps_destruct SHbs as (SH16 & SH4).
  Ltac prep :=
    let JWF := ident:(JWF) in let ENT := ident:(ENT) in let ALS := ident:(ALS) in let ALM := ident:(ALM) in let AL16 := ident:(AL16) in
    let OK' := fresh "OK" in pose proof OK as OK';
    cps_destruct OK' as (HS & HSTRM & HDST & Hdlen & HSP & (ALS & ALM) & SEP_SM & SEP_SD & SEP_MD & IAS & IAM & IAD & HIHI & JWF & ENT);
    let OKS' := fresh "OKS" in pose proof OKS as OKS';
    cps_destruct OKS' as (HSM & HL16 & HL4 & SEP_S16 & SEP_M16 & SEP_D16 & SEP_S4 & SEP_M4 & SEP_D4 & SEP_164 & IA16 & IA4);
    let OKB' := fresh "OKB" in pose proof OKB as OKB';
    cps_destruct OKB' as (LOI & LOC & LOSP & LSI & AL16);
    destruct (zmod16_lin _ ALS) as [qS EqS]; destruct (zmod8_lin _ ALM) as [qSTRM EqSTRM]; destruct (zmod2_lin _ AL16) as [q16 Eq16];
    clear ALS ALM AL16;
    cps_destruct ENT as (En & Rn & Esm & Rsnb & Rsnb1 & Rav0 & Lout0 & Eol0 & RtP0 & NK0 & Rcb0 & Roc0 & Rr01 & Rrnd & Rcf & Rtt & Rl16 & Rl4);
    cps_destruct JWF as (Lp1 & Lp2 & Lp3 & Ls1 & Ls2 & Lq1 & Lq2);
    unfold disj, bzd_img_apart in *;
    unfold FWBAc, FWB in *; cbn [app] in *; pose proof alloc_ceiling_range as ACR;
    pose proof (zw32_length cf 257 ltac:(lia)) as CFL;
    pose proof (zh16_length (d_ll16 d0) (200000 * n) ltac:(lia)) as L16L; pose proof (zb8_length (d_ll4 d0) (50000 * n) ltac:(lia)) as L4L;
    pose proof rnums_words_length as RNL; pose proof crc_words_length as CRCL;
    pose proof (proj2 ANS : saddr S SHS) as ANS0;
    hide_disj.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Notation T1S := (B0F_bzd_sr2.T1S c SHS w0 slo). Notation R1S := (B0F_bzd_sr3.R1S c SHS w0 slo).
  Notation T2S := (B0F_bzd_sr4.T2S c SHS w0 slo). Notation R2S := (B0F_bzd_sr5.R2S c SHS w0 slo).
  Notation T3S := (B0F_bzd_sr6.T3S c SHS w0 slo). Notation R3S := (B0F_bzd_sr7.R3S c SHS w0 slo).
  Notation T4S := (B0F_bzd_srT.T4S c SHS w0 slo). Notation R4S := (B0F_bzd_srT.R4S c SHS w0 slo).
  Notation T5S := (B0F_bzd_srT.T5S c SHS w0 slo). Notation R5S := (B0F_bzd_srT.R5S c SHS w0 slo).
  (* [comment removed for export] *)
  Ltac hyps := first [exact OK | exact OKS | exact OKB | exact ANS | exact SH | exact KJ | exact KE | exact RD1].

  (* [comment removed for export] *)
  Lemma sr_knot : forall f,
    (forall p, GS f p) /\ (forall p, H0S f p) /\ (forall p, MS_ f p).
  Proof.
    induction f as [|f IH].
    - assert (G : forall p, GS 0%nat p).
      { intros p. eapply (B0F_bzd_sr2.sr_G c SHS w0 slo); try hyps. intros f' p' E; discriminate E. }
      assert (H0 : forall p, H0S 0%nat p).
      { intros p. eapply (B0F_bzd_srH.sr_H0 c SHS w0 slo); try hyps; [exact G | reflexivity]. }
      assert (M : forall p, MS_ 0%nat p).
      { intros p. eapply (B0F_bzd_sr2.sr_M c SHS w0 slo); try hyps. apply H0. }
      exact (conj G (conj H0 M)).
    - cps_destruct IH as (G' & H0' & M').
      assert (R5 : forall p, R5S f p) by (intros p; eapply (B0F_bzd_srT.sr_R5 c SHS w0 slo); try hyps; exact M').
      assert (T5 : forall p, T5S f p) by (intros p; eapply (B0F_bzd_srT.sr_T5 c SHS w0 slo); try hyps; exact R5).
      assert (R4 : forall p, R4S f p) by (intros p; eapply (B0F_bzd_srT.sr_R4 c SHS w0 slo); try hyps; exact T5).
      assert (T4 : forall p, T4S f p) by (intros p; eapply (B0F_bzd_srT.sr_T4 c SHS w0 slo); try hyps; exact R4).
      assert (R3 : forall p, R3S f p) by (intros p; eapply (B0F_bzd_sr8.sr_R3 c SHS w0 slo); try hyps; [exact T4 | exact M']).
      assert (T3 : forall p, T3S f p) by (intros p; eapply (B0F_bzd_sr7.sr_T3 c SHS w0 slo); try hyps; exact R3).
      assert (R2 : forall p, R2S f p) by (intros p; eapply (B0F_bzd_sr6.sr_R2 c SHS w0 slo); try hyps; [exact T3 | exact M']).
      assert (T2 : forall p, T2S f p) by (intros p; eapply (B0F_bzd_sr5.sr_T2 c SHS w0 slo); try hyps; exact R2).
      assert (R1 : forall p, R1S f p) by (intros p; eapply (B0F_bzd_sr4.sr_R1 c SHS w0 slo); try hyps; [exact T2 | exact M']).
      assert (T1 : forall p, T1S f p) by (intros p; eapply (B0F_bzd_sr3.sr_T1 c SHS w0 slo); try hyps; exact R1).
      assert (G : forall p, GS (Datatypes.S f) p).
      { intros p. eapply (B0F_bzd_sr2.sr_G c SHS w0 slo); try hyps. intros f' p' E; injection E as <-; apply T1. }
      assert (H0 : forall p, H0S (Datatypes.S f) p).
      { intros p. eapply (B0F_bzd_srH.sr_H0 c SHS w0 slo); try hyps; [exact G | reflexivity]. }
      assert (M : forall p, MS_ (Datatypes.S f) p).
      { intros p. eapply (B0F_bzd_sr2.sr_M c SHS w0 slo); try hyps. apply H0. }
      exact (conj G (conj H0 M)).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem B0F_smallr : forall (ra t0 t1 t2 a0 a3 a4 a5 a6 a7 s3 s5 t3 t4 t5 t6 w8 w40 w48 w56 w64 w72 w88 : word)
      (m : word -> option byte) (dbytes rest : list byte),
    DSgA DI_B0 c m J d0 s0 -> DESTgA DI_B0 c m s0 dbytes rest ->
    rw_cells b0segs m uspi
      (bzd_slots S SHS w0 w8 w40 w48 w56 w64 w72 w88 (Z_to_bv 64 (SHS + -2147450744)) (Z_to_bv 64 (SHS + -2147442870))) ->
    RO m -> munch WB m0 m -> wmono b0segs m0 m ->
    evt b0segs (KQ (unRLE d0 s0))
      (MS (B0RR c SHS ra t0 t1 t2 a0 (Z_to_bv 64 1) cstrm a3 a4 a5 a6 a7 s3 s5 hs7 hs9 t3 t4 t5 t6) F (Z_to_bv 64 0x8414c) fc None m (seg_rom b0segs)).
  Proof.
    intros until rest. intros DSm DE FSL0 ROm MU WM.
    pose proof DSm as DSm0. pose proof DE as DE0. pose proof ROm as RO0.
    unDS DSm. cps_destruct DE as (DSTA & DL & Edb & Lout). unRO ROm. prep. unSH.
    assert (SMT : smallb d0 = true) by (unfold smallb; rewrite Esm, HSM; reflexivity).
    unfold id in NK0. pose proof (Rrnd RD1) as [RrN0 RrT0].
    rewrite (unRLE_plain d0 s0 (Z.to_nat (PP + 2 - d_nused d0))) by (first [rewrite SMT; reflexivity | lia]).
    cps_destruct (sr_knot (Z.to_nat (PP + 2 - d_nused d0))) as (_ & H0 & _).
    remember (Z.to_nat (PP + 2 - d_nused d0)) as f eqn:Hf.
    set (p0 := PST (d_out_ch d0) (d_out_len d0) (d_nused d0) (d_k0 d0) (d_tPos d0) (d_rNToGo d0) (d_rTPos d0) (d_cbcrc d0)
                   (s_out s0) (s_avail_out s0) (s_tout s0) (j_tol J) (j_toh J)).
    assert (ED : set8 d0 (d_out_ch d0) (d_out_len d0) (d_nused d0) (d_k0 d0) (d_tPos d0) (d_rNToGo d0) (d_rTPos d0) (d_cbcrc d0) = d0) by apply set8_id.
    assert (ES : smod s0 (s_out s0) (s_avail_out s0) (s_tout s0) = s0) by apply smod_id.
    assert (EJ : jk_set_o J (j_tol J) (j_toh J) = J) by apply jk_set_o_id.
    unfold DSgA in *. b0img.
    (* [comment removed for export] *)
    brun_to 0x84168%Z.
    pose proof (H0 p0) as H. unfold B0F_bzd_sr1.H0S, B0F_bzd_sr1.CH in H. subst p0.
    unfold S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp in H. pcut_in H.
    rewrite ED, ES, EJ in H.
    enter_with (H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dbytes rest);
      [ st_eq
      | repeat match goal with |- _ /\ _ => split end; [exact DSm0 | exact DE0 | unfold B0F_bzd_sr1.FSLs; exact FSL0 | exact RO0 | exact MU | exact WM]
      | unfold S0F_bzd_sr1.sinvR; pcut;
        repeat match goal with |- _ /\ _ => split end; first [lia | reflexivity | exact Lout]
      | lia ].
  Time Qed.
End SR.

(* [comment removed for export] *)
Lemma B0_smallr_spec : B0F_bzd_skV.SMALLR_aspec.
Proof.
  unfold B0F_bzd_skV.SMALLR_aspec, B0F_bzd_skV.SMALL_aspec. intros c SHS w0 lo OK OKS OKB ANS SH KJ KE. intros until rest. intros DSm DE FSL ROm MU WM RD1.
  eapply (B0F_smallr c SHS w0 lo OK OKS OKB ANS SH KJ KE RD1); eassumption.
Qed.
End ACeilS1.
