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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require B0F_bzd_sr1.
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
  Ltac pcut_all := cbn [S0F_bzd_snr1.p_oc S0F_bzd_snr1.p_ol S0F_bzd_snr1.p_nu S0F_bzd_snr1.p_k0 S0F_bzd_snr1.p_tp S0F_bzd_snr1.p_rn S0F_bzd_snr1.p_rt
                    S0F_bzd_snr1.p_cb S0F_bzd_snr1.p_out S0F_bzd_snr1.p_av S0F_bzd_snr1.p_tout S0F_bzd_snr1.p_tol S0F_bzd_snr1.p_toh] in *.
  (* [comment removed for export] *)
  Ltac unRO H := let GOT := ident:(GOT) in let ACG := ident:(ACG) in let ACV := ident:(ACV) in
    cps_destruct H as ((SAV & L16A & L4A & CFA & CRC & RNA & GOT & MI) & (ACG & ACV) & STK); unfold FGOTA in GOT; b0img;
    cbn [aci_segs aci_got_sh aci_shvar aci_c CmpCut.ci_segs B0C] in ACG, ACV.
  Ltac unDS H := cps_destruct H as (HD & NBU & MID & SM).
  Ltac unCH H := let DSm := fresh "DSm" in let DE := fresh "DE" in let ROm := fresh "ROm" in let FSL := ident:(FSL) in
    cps_destruct H as (DSm & DE & FSL & ROm & MU & WM); unDS DSm; cps_destruct DE as (DSTA & DL & Edb & Lout); unRO ROm;
    unfold B0F_bzd_sr1.FSLs, bzd_slots in FSL.
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
  Ltac ro_close := unfold FROsB, FROsA, FGOTA, aconsts; b0img; cbn [aci_segs aci_got_sh aci_shvar aci_c CmpCut.ci_segs B0C];
    repeat match goal with |- _ /\ _ => split end; assumption.
  (* [comment removed for export] *)
  Ltac dsg_close := let HD := ident:(HD) in let NBU := ident:(NBU) in let MID := ident:(MID) in let SM := ident:(SM) in
    unfold DSgA; b0img; focbn; repeat match goal with |- _ /\ _ => split end; [exact_cells HD | exact_cells NBU | exact_cells MID | exact_cells SM].
  Ltac destg_close := unfold DESTgA; b0img; focbn; repeat match goal with |- _ /\ _ => split end; first [eassumption | cbn [length]; lia].
  Ltac fsl_close := let FSL := ident:(FSL) in first [ exact FSL | unfold bzd_slots; exact FSL | unfold B0F_bzd_sr1.FSLs, bzd_slots; exact FSL ].
  Ltac ch_close MU WM := repeat match goal with |- _ /\ _ => split end; [dsg_close | destg_close | fsl_close | ro_close | exact MU | exact WM].
  (* [comment removed for export] *)
  Ltac unhide_k0 := try match goal with H : id ((0 <= _ < 256)%Z \/ _) |- _ => unfold id in H end.
  Ltac sinv_close := unfold S0F_bzd_sr1.sinvR; pcut;
    repeat match goal with |- _ /\ _ => split end; first [assumption | cbn [length]; lia].
  (* [comment removed for export] *)
  Ltac sbl := wstep; lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) => rewrite ?le1_sx32_lit, ?BzInv.le1_lit; mem_after_store end.
  (* [comment removed for export] *)
  Ltac exitK MU WM := eapply KE; [dsg_close | destg_close | fsl_close | ro_close | exact MU | exact WM | unfold oexit; focbn; lia].
  Ltac joinK MU WM := eapply KJ; [dsg_close | destg_close | fsl_close | ro_close | exact MU | exact WM | ];
    unfold ojoin; focbn; unhide_k0; repeat match goal with |- _ /\ _ => split end;
    first [assumption | lia | intros; lia | idtac].
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition T1S (f' : nat) (p : pst) : Prop :=
    forall (t0 a0 a1 a5 a6 s5 t3 t5 t6 w8 w40 w48 w56 : word) (m : word -> option byte) (dbytes rest : list byte),
      CH m p w8 w40 w48 w56 c64 c60 cnu dbytes rest -> sinvR p -> (PP - p_nu p <= Z.of_nat f' + 1)%Z -> (1 <= p_av p)%Z ->
      p_ol p = 1%Z -> p_oc p = p_k0 p -> (0 <= p_k0 p < 256)%Z -> (p_nu p < PP)%Z -> (p_tp p < cap)%Z ->
      evt b0segs (KQ (PG1 (Datatypes.S f') PP (D p) (Ss p)))
        (MS (B0RR c SHS cm4 t0 (Z_to_bv 64 (indexIntoF (p_tp p) cf)) (Z_to_bv 64 (p_tp p)) a0 a1 cpp (Z_to_bv 64 (p_k0 p)) cnn a5 a6 (Z_to_bv 64 (p_nu p))
                  c16 s5 hs7 hs9 t3 c40 t5 t6)
            F (Z_to_bv 64 0x84544) fc None m (seg_rom b0segs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sr_G : forall f, (forall f' p', f = Datatypes.S f' -> T1S f' p') -> forall p, GS f p.
  Proof.
    intros f IHT1 p. unfold B0F_bzd_sr1.GS. intros until rest. intros CHm SI Hf Hav Hol.
    destruct p as [oc ol nu k0 tp rn rt cb out av tout tol toh].
    unfold B0F_bzd_sr1.CH, S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp, S0F_bzd_sr1.sinvR in *.
    pcut_all. subst ol.
    cps_destruct SI as (Rcb & Roc & Rol & Rnu & Rk0 & Rtp & Rrn & Rrt & Rav & Lout').
    unCH CHm. prep. unSH.
    unfold DSgA, DESTgA in *. b0img. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in SAV. focbn_in Edb. focbn_in Lout.
    (* [comment removed for export] *)
    brun_to 0x843f8%Z. try rewrite (sx32_of_Z nu) by lia.
    (* [comment removed for export] *)
    brun_to 0x84404%Z. try rewrite (sx32_of_Z snb) by lia.
    (* [comment removed for export] *)
    brun_to 0x84414%Z.
    (* [comment removed for export] *)
    wstep. if_cases K1; zify_cond K1.
    2:{ rewrite K_PG_done by (s8; lia). wstep. joinK MU WM. }
    (* [comment removed for export] *)
    wstep. wstep. if_cases K2; zify_cond K2; rewrite ?signed_lit_small in K2 by lia.
    { rewrite K_PG_over by (s8; lia). exitK MU WM. }
    rewrite K_PG_go by (s8; lia). s8.
    (* [comment removed for export] *)
    brun_to 0x84430%Z. wstep.
    (* [comment removed for export] *)
    brun_to 0x84458%Z.
    unfold id in Rk0. destruct Rk0 as [Rk0 | [Hnu0 Htp0]].
    - (* [comment removed for export] *)
      try rewrite (sx32_of_Z k0) by lia.
      (* [comment removed for export] *)
      brun_to 0x84460%Z. sbl. try rewrite (unsigned_lit k0) in HD by lia.
      (* [comment removed for export] *)
      brun_to 0x84484%Z. try rewrite (zx32_of_Z tp) by lia.
      (* [comment removed for export] *)
      brun_to 0x8448c%Z. rewrite ?En. try rewrite (sx32_of_Z n) by lia.
      (* [comment removed for export] *)
      brun_to 0x8449c%Z.
      (* [comment removed for export] *)
      pose proof (word_urange (Z_to_bv 64 tp)) as TPR.
      wstep. if_cases K3; zify_cond K3.
      { (* [comment removed for export] *)
        assert (K3' : (cap <= bv_swrap 32 (tp + 0) mod 18446744073709551616)%Z) by lia.
        pose proof (sextw_ge tp cap ltac:(lia) ltac:(lia) K3') as GE.
        change (2^32)%Z with 4294967296%Z in GE. rewrite (Z.mod_small tp 4294967296) in GE by lia.
        rewrite PG1_None by (apply get_sym_None; s8; unfold blk_cap; lia).
        exitK MU WM. }
      assert (K3' : (bv_swrap 32 (tp + 0) mod 18446744073709551616 < cap)%Z) by lia.
      destruct (sextw_lt tp cap ltac:(lia) ltac:(lia) K3') as [LT XV].
      change (2^32)%Z with 4294967296%Z in LT, XV. rewrite (Z.mod_small tp 4294967296) in LT, XV by lia.
      replace (Z_to_bv 64 (bv_swrap 32 (tp + 0))) with (Z_to_bv 64 tp) by (f_equal; rewrite swrap32_id by lia; lia).
      (* [comment removed for export] *)
      wstep. wstep. wstep.
      destruct f as [|f']; [exfalso; cbn [Z.of_nat] in Hf; lia|]. rewrite Nat2Z.inj_succ in Hf.
      lazymatch goal with |- evt _ ?P (MS _ _ _ _ _ ?mm _) =>
        eapply (B0F_bzd_sr1.sr_B1 c SHS slo OK OKS OKB ANS SH P mm tp) with (k := 7%nat) (t := 0%nat); [ro_close | exact MU | lia | | reflexivity | reflexivity] end.
      intros t0' a0' a6' t3' lo hi E8.
      pose proof (iif_result cf tp lo hi E8) as RES.
      pose proof (IHT1 f' (PST k0 1 nu k0 tp rn rt cb out av tout tol toh) eq_refl) as T1. unfold T1S, B0F_bzd_sr1.CH in T1.
      unfold S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp in T1. pcut_in T1.
      rewrite <- RES.
      enter_with (T1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ dbytes rest);
        [ st_eq
        | ch_close MU WM
        | sinv_close
        | lia | lia | reflexivity | reflexivity | lia | lia | lia ].
    - (* [comment removed for export] *)
      subst nu.
      brun_to 0x84460%Z. sbl.
      brun_to 0x84484%Z. try rewrite (zx32_of_Z tp) by lia.
      brun_to 0x8448c%Z. rewrite ?En. try rewrite (sx32_of_Z n) by lia.
      brun_to 0x8449c%Z.
      pose proof (word_urange (Z_to_bv 64 tp)) as TPR.
      wstep. if_cases K3; zify_cond K3.
      2:{ exfalso. assert (K3' : (bv_swrap 32 (tp + 0) mod 18446744073709551616 < cap)%Z) by lia.
        destruct (sextw_lt tp cap ltac:(lia) ltac:(lia) K3') as [LT _].
        change (2^32)%Z with 4294967296%Z in LT. rewrite (Z.mod_small tp 4294967296) in LT by lia. lia. }
      rewrite PG1_None by (apply get_sym_None; s8; unfold blk_cap; lia).
      exitK MU WM.
  Time Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sr_M : forall f p, H0S f p -> MS_ f p.
  Proof.
    intros f p H0. unfold B0F_bzd_sr1.MS_. intros until rest. intros CHm SI Hf Hol.
    pose proof CHm as CH0. pose proof SI as SI0.
    destruct p as [oc ol nu k0 tp rn rt cb out av tout tol toh].
    unfold B0F_bzd_sr1.CH, S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp, S0F_bzd_sr1.sinvR in CHm, SI, Hf, Hol |- *.
    pcut_all.
    cps_destruct SI as (Rcb & Roc & Rol & Rnu & Rk0 & Rtp & Rrn & Rrt & Rav & Lout').
    unCH CHm. prep. unSH.
    unfold DSgA, DESTgA in *. b0img. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in SAV.
    brun_to 0x84168%Z.
    unfold B0F_bzd_sr1.H0S in H0. eapply H0; [exact CH0 | exact SI0 | pcut; lia].
  Time Qed.
End SR.
End ACeilS1.
