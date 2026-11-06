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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require A0F_bzd_snr1.
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
  Ltac sbl := wstep; lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) => rewrite ?le1_sx32_lit, ?BzInv.le1_lit; mem_after_store end.
  (* [comment removed for export] *)
  Ltac exitK MU WM := eapply KE; [dsg_close | destg_close | fsl_close | ro_close | exact MU | exact WM | unfold oexit; focbn; lia].
  Ltac joinK MU WM := eapply KJ; [dsg_close | destg_close | fsl_close | ro_close | exact MU | exact WM | ];
    unfold ojoin; focbn; unhide_k0; repeat match goal with |- _ /\ _ => split end;
    first [assumption | lia | intros; exfalso; let RD0 := ident:(RD0) in rewrite RD0 in *; lia | idtac].
  Let snr_B1 := A0F_bzd_snr1.snr_B1 c SHS OK OKS ANS SH.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma snr_G : forall f, (forall f' p', f = Datatypes.S f' -> T1S f' p') -> forall p, GS f p.
  Proof.
    intros f IHT1 p. unfold A0F_bzd_snr1.GS. intros until rest. intros CHm SI Hf Hav Hol.
    destruct p as [oc ol nu k0 tp rn rt cb out av tout tol toh].
    unfold A0F_bzd_snr1.CH, S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp, S0F_bzd_snr1.sinv in *.
    pcut_all. subst ol.
    cps_destruct SI as (Rcb & Roc & Rol & Rnu & Rk0 & Rtp & Ern & Ert & Rav & Lout').
    unCH CHm. prep. unSH.
    unfold DSgA in *. a0img. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in SAV. focbn_in Edb. focbn_in Lout.
    (* [comment removed for export] *)
    arun_to 0x85e1c%Z. try rewrite (sx32_of_Z nu) by lia.
    (* [comment removed for export] *)
    arun_to 0x85e28%Z. try rewrite (sx32_of_Z snb) by lia. wstep.
    (* [comment removed for export] *)
    wstep. if_cases K1; zify_cond K1.
    2:{ (* [comment removed for export] *)
      rewrite K_PG_done by (s8; lia). wstep. joinK MU WM. }
    (* [comment removed for export] *)
    wstep. wstep. if_cases K2; zify_cond K2; rewrite ?signed_lit_small in K2 by lia.
    2:{ rewrite K_PG_over by (s8; lia). wstep. exitK MU WM. }
    rewrite K_PG_go by (s8; lia). s8.
    (* [comment removed for export] *)
    arun_to 0x85448%Z.
    unfold id in Rk0. destruct Rk0 as [Rk0 | [Hnu0 Htp0]].
    - (* [comment removed for export] *)
      try rewrite (sx32_of_Z k0) by lia.
      (* [comment removed for export] *)
      arun_to 0x8544c%Z. sbl. try rewrite (unsigned_lit k0) in HD by lia.
      (* [comment removed for export] *)
      arun_to 0x85474%Z. try rewrite (zx32_of_Z tp) by lia.
      (* [comment removed for export] *)
      arun_to 0x85480%Z. rewrite ?En. try rewrite (sx32_of_Z n) by lia.
      (* [comment removed for export] *)
      wstep. wstep. wstep.
      (* [comment removed for export] *)
      pose proof (word_urange (Z_to_bv 64 tp)) as TPR.
      wstep. if_cases K3; zify_cond K3.
      2:{ (* [comment removed for export] *)
        assert (K3' : (cap <= bv_swrap 32 (tp + 0) mod 18446744073709551616)%Z) by lia.
        pose proof (sextw_ge tp cap ltac:(lia) ltac:(lia) K3') as GE.
        change (2^32)%Z with 4294967296%Z in GE. rewrite (Z.mod_small tp 4294967296) in GE by lia.
        rewrite PG1_None by (apply get_sym_None; s8; unfold blk_cap; lia).
        wstep. exitK MU WM. }
      assert (K3' : (bv_swrap 32 (tp + 0) mod 18446744073709551616 < cap)%Z) by lia.
      destruct (sextw_lt tp cap ltac:(lia) ltac:(lia) K3') as [LT XV].
      change (2^32)%Z with 4294967296%Z in LT, XV. rewrite (Z.mod_small tp 4294967296) in LT, XV by lia.
      replace (Z_to_bv 64 (bv_swrap 32 (tp + 0))) with (Z_to_bv 64 tp) by (f_equal; rewrite swrap32_id by lia; lia).
      (* [comment removed for export] *)
      wstep. wstep.
      destruct f as [|f']; [exfalso; cbn [Z.of_nat] in Hf; lia|]. rewrite Nat2Z.inj_succ in Hf.
      lazymatch goal with |- evt _ ?P (MS _ _ _ _ _ ?mm _) =>
        eapply (snr_B1 P mm tp) with (k := 7%nat) (t := 0%nat); [ro_close | exact MU | lia | | reflexivity | reflexivity] end.
      intros a0' a1' t3' t4' lo hi E8.
      pose proof (iif_result cf tp lo hi E8) as RES.
      pose proof (IHT1 f' (PST k0 1 nu k0 tp rn rt cb out av tout tol toh) eq_refl) as T1. unfold A0F_bzd_snr1.T1S in T1.
      pcut_in T1. unfold A0F_bzd_snr1.CH in T1; unfold S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp in T1.
      rewrite <- RES.
      enter_with (T1 _ _ _ _ _ _ _ _ _ _ dbytes rest);
        [ st_eq
        | ch_close MU WM
        | sinv_close
        | lia | lia | reflexivity | reflexivity | lia | lia | lia ].
    - (* [comment removed for export] *)
      subst nu.
      arun_to 0x8544c%Z. sbl.
      arun_to 0x85474%Z. try rewrite (zx32_of_Z tp) by lia.
      arun_to 0x85480%Z. rewrite ?En. try rewrite (sx32_of_Z n) by lia.
      wstep. wstep. wstep.
      pose proof (word_urange (Z_to_bv 64 tp)) as TPR.
      wstep. if_cases K3; zify_cond K3.
      { exfalso. assert (K3' : (bv_swrap 32 (tp + 0) mod 18446744073709551616 < cap)%Z) by lia.
        destruct (sextw_lt tp cap ltac:(lia) ltac:(lia) K3') as [LT _].
        change (2^32)%Z with 4294967296%Z in LT. rewrite (Z.mod_small tp 4294967296) in LT by lia. lia. }
      rewrite PG1_None by (apply get_sym_None; s8; unfold blk_cap; lia).
      wstep. exitK MU WM.
  Time Qed.
End SNR.
End ACeilS1.
