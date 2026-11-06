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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require A0F_bzd_fr1.
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
  Ltac goE HD NBU MID SM DSTA DL Edb Lout FSL MU WM :=
    eapply KE; [dsg_close HD NBU MID SM| destg_close DSTA DL Edb Lout| fsl_close FSL| ro_close| exact MU| exact WM
               | unfold oexit; focbn].
  (* [comment removed for export] *)
  Ltac tt_load i :=
    lazymatch goal with TTA : u32arr _ ?mm TT _ |- _ =>
      let RD := fresh "RD" in
      pose proof (zw32_read a0segs mm TT (d_tt d0) cap i _ TTA ltac:(lia) eq_refl) as RD; wstep; clear RD end.
  (* [comment removed for export] *)
  Ltac rn_load i :=
    lazymatch goal with RNA : u32arr _ ?mm 804096 rnums_words |- _ =>
      let RD := fresh "RD" in
      pose proof (u32arr_read a0segs mm 804096 rnums_words i (Z_to_bv 64 (rNums i)) _ RNA (S0F_bzd_fr1.rnums_words_nth i ltac:(lia)) ltac:(lia) eq_refl) as RD;
      wstep; clear RD; rewrite ?(sx32_of_Z (rNums i)) by lia end.
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
  Ltac goTL IHM oc ol nu k0 tp rn rt cb out av tout tol toh dbytes rest HD NBU MID SM DSTA DL Edb Lout FSL MU WM :=
    unfold A0F_bzd_fr1.TLS in IHM;
    enter_with (IHM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ oc ol nu k0 tp rn rt cb out av tout tol toh dbytes rest);
    [ st_eq | ch_close HD NBU MID SM DSTA DL Edb Lout FSL MU WM | | ].
  (* [comment removed for export] *)
  Ltac refill pr pn pa pm rt Irt :=
    arun_to pr; try rewrite (sx32_of_Z rt) by (clear -Irt; lia);
    arun_to pn; rn_load rt;
    arun_to pa; rewrite (rtpos_wrap rt) by (clear -Irt; lia);
    arun_to pm.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma fr_L1 : forall f, R2S f -> (forall f', f = Datatypes.S f' -> TLS f') -> R1S f.
  Proof.
    intros f R2 IHM. unfold A0F_bzd_fr1.R1S. intros until rest. intros CHm FI Hf Hav1 Hk0 Hnu Rw1 RrN1.
    unCHf CHm. prep. unSH. unFI FI.
    unfold DSgA in *. a0img. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in SAV. focbn_in Lout.
    destruct f as [|f']; [exfalso; clear -Hf Hnu; cbn in Hf; lia|].
    specialize (IHM f' eq_refl). rewrite Nat2Z.inj_succ in Hf.
    rewrite PG1b_eq. cbv zeta. g8.
    (* [comment removed for export] *)
    arun_to 0x861d8%Z. try rewrite (sx32_of_Z rN1) by (clear -RrN1; lia). wstep. wstep.
    (* [comment removed for export] *)
    arun_to 0x861f0%Z. wstep.
    wstep. if_cases K1; zify_cond K1.
    { replace (nu + 1 =? PP)%Z with true by (symmetry; apply Z.eqb_eq; clear -K1; lia).
      goTL IHM k0 1%Z (nu + 1)%Z k0 (w / 256)%Z (rN1 - 1)%Z rt cb out av tout tol toh dbytes rest HD NBU MID SM DSTA DL Edb Lout FSL MU WM.
      - unfold S0F_bzd_fr1.finv. clear -Ioc Iol Inu Hk0 Itp Irn Irt Icb Iav Rw1 RrN1 Hnu. repeat match goal with |- _ /\ _ => split end; lia.
      - clear -Hf. lia. }
    replace (nu + 1 =? PP)%Z with false by (symmetry; apply Z.eqb_neq; clear -K1; lia).
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep.
    rewrite (S0F_bzd_fr2.mask_b2z rN1 RrN1).
    set (k1 := Z.lxor (Z.land w 255) (if (rN1 - 1 =? 1)%Z then 1%Z else 0%Z)) in *.
    pose proof (S0F_bzd_fr2.mask_byte w rN1) as Rk1. fold k1 in Rk1.
    (* [comment removed for export] *)
    wstep. if_cases K2; zify_cond K2.
    { replace (k1 =? k0)%Z with false by (symmetry; apply Z.eqb_neq; exact K2). cbn [negb]. clear K2.
      arun_to 0x86600%Z. wstep.
      goTL IHM k0 1%Z (nu + 1)%Z k1 (w / 256)%Z (rN1 - 1)%Z rt cb out av tout tol toh dbytes rest HD NBU MID SM DSTA DL Edb Lout FSL MU WM.
      - unfold S0F_bzd_fr1.finv. clear -Ioc Iol Inu Hk0 Itp Irn Irt Icb Iav Rw1 RrN1 Hnu Rk1. repeat match goal with |- _ /\ _ => split end; lia.
      - clear -Hf. lia. }
    replace (k1 =? k0)%Z with true by (symmetry; apply Z.eqb_eq; clear -K2; lia). cbn [negb].
    (* [comment removed for export] *)
    arun_to 0x86218%Z. wstep.
    wstep. if_cases K3; zify_cond K3.
    2:{ rewrite PG2_None by (apply get_sym_None; g8; unfold blk_cap; rewrite En; clear -K3 Rn; lia).
      wstep. goE HD NBU MID SM DSTA DL Edb Lout FSL MU WM. clear -Inu Iav; lia. }
    eassert (GS2 : get_sym (D8 k0 2 (nu + 1) k0 (w / 256) (rN1 - 1) rt cb) = Some _).
    { apply get_sym_FR; g8; [unfold blk_cap; rewrite En; clear -K3 Rn; lia | rewrite Esm; exact HSM | rewrite RD1; lia]. }
    rewrite (PG2_b _ _ _ _ _ _ GS2). clear GS2. g8.
    (* [comment removed for export] *)
    arun_to 0x86240%Z. tt_load (w / 256)%Z.
    pose proof (Rtt (w / 256)%Z) as Rw2. set (w2 := zget (d_tt d0) (w / 256)) in *. rewrite ?(zx32_of_Z w2) by lia.
    (* [comment removed for export] *)
    arun_to 0x86254%Z.
    wstep. if_cases K4; zify_cond K4.
    { (* [comment removed for export] *)
      rewrite (S0F_bzd_fr1.rNn_nz (rN1 - 1) rt ltac:(clear -K4; lia)), (S0F_bzd_fr1.rTn_nz (rN1 - 1) rt ltac:(clear -K4; lia)).
      unfold A0F_bzd_fr1.R2S in R2.
      enter_with (R2 _ _ _ _ _ _ nu k0 (rN1 - 1)%Z rt cb out av tout tol toh w2 dbytes rest);
        [ st_eq
        | ch_close HD NBU MID SM DSTA DL Edb Lout FSL MU WM
        | unfold S0F_bzd_fr1.finv; clear -Ioc Iol Inu Hk0 Itp Irn Irt Icb Iav Rw2 RrN1 Hnu K4; repeat match goal with |- _ /\ _ => split end; lia
        | clear -Hf; lia | exact Hav1 | exact Hk0 | clear -Hnu K1; lia | exact Rw2 | clear -RrN1 K4; lia ]. }
    (* [comment removed for export] *)
    pose proof (rNums_range rt ltac:(clear -Irt; lia)) as RNR.
    refill 0x86270%Z 0x86294%Z 0x862b0%Z 0x862c0%Z rt Irt.
    pose proof (Z.mod_pos_bound (rt + 1) 512 ltac:(lia)) as RT'.
    assert (Ez : (rN1 - 1 = 0)%Z) by (clear -K4 RrN1; lia).
    rewrite Ez. rewrite S0F_bzd_fr1.rNn_z, (S0F_bzd_fr1.rTn_z rt) by (clear -Irt; lia).
    unfold A0F_bzd_fr1.R2S in R2.
    enter_with (R2 _ _ _ _ _ _ nu k0 (rNums rt) ((rt + 1) mod 512)%Z cb out av tout tol toh w2 dbytes rest);
      [ st_eq
      | ch_close HD NBU MID SM DSTA DL Edb Lout FSL MU WM
      | unfold S0F_bzd_fr1.finv; clear -Ioc Iol Inu Hk0 Itp Irn Irt Icb Iav Rw2 RrN1 Hnu RT' RNR; repeat match goal with |- _ /\ _ => split end; lia
      | clear -Hf; lia | exact Hav1 | exact Hk0 | clear -Hnu K1; lia | exact Rw2 | clear -RNR; lia ].
  Time Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma fr_L2 : forall f, R3S f -> (forall f', f = Datatypes.S f' -> TLS f') -> R2S f.
  Proof.
    intros f R3 IHM. unfold A0F_bzd_fr1.R2S. intros until rest. intros CHm FI Hf Hav1 Hk0 Hnu Rw1 RrN1.
    unCHf CHm. prep. unSH. unFI FI.
    unfold DSgA in *. a0img. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in SAV. focbn_in Lout.
    destruct f as [|f']; [exfalso; clear -Hf Hnu; cbn in Hf; lia|].
    specialize (IHM f' eq_refl). rewrite Nat2Z.inj_succ in Hf.
    rewrite PG2b_eq. cbv zeta. g8.
    (* [comment removed for export] *)
    arun_to 0x862d0%Z. try rewrite (sx32_of_Z rN1) by (clear -RrN1; lia). wstep. wstep.
    (* [comment removed for export] *)
    arun_to 0x862e8%Z. wstep.
    wstep. if_cases K1; zify_cond K1.
    { replace (nu + 2 =? PP)%Z with true by (symmetry; apply Z.eqb_eq; clear -K1; lia).
      goTL IHM k0 2%Z (nu + 2)%Z k0 (w / 256)%Z (rN1 - 1)%Z rt cb out av tout tol toh dbytes rest HD NBU MID SM DSTA DL Edb Lout FSL MU WM.
      - unfold S0F_bzd_fr1.finv. clear -Ioc Iol Inu Hk0 Itp Irn Irt Icb Iav Rw1 RrN1 Hnu. repeat match goal with |- _ /\ _ => split end; lia.
      - clear -Hf. lia. }
    replace (nu + 2 =? PP)%Z with false by (symmetry; apply Z.eqb_neq; clear -K1; lia).
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep.
    rewrite (S0F_bzd_fr2.mask_b2z rN1 RrN1).
    set (k1 := Z.lxor (Z.land w 255) (if (rN1 - 1 =? 1)%Z then 1%Z else 0%Z)) in *.
    pose proof (S0F_bzd_fr2.mask_byte w rN1) as Rk1. fold k1 in Rk1.
    (* [comment removed for export] *)
    wstep. if_cases K2; zify_cond K2.
    { replace (k1 =? k0)%Z with false by (symmetry; apply Z.eqb_neq; exact K2). cbn [negb]. clear K2.
      arun_to 0x86600%Z. wstep.
      goTL IHM k0 2%Z (nu + 2)%Z k1 (w / 256)%Z (rN1 - 1)%Z rt cb out av tout tol toh dbytes rest HD NBU MID SM DSTA DL Edb Lout FSL MU WM.
      - unfold S0F_bzd_fr1.finv. clear -Ioc Iol Inu Hk0 Itp Irn Irt Icb Iav Rw1 RrN1 Hnu Rk1. repeat match goal with |- _ /\ _ => split end; lia.
      - clear -Hf. lia. }
    replace (k1 =? k0)%Z with true by (symmetry; apply Z.eqb_eq; clear -K2; lia). cbn [negb].
    (* [comment removed for export] *)
    arun_to 0x86310%Z. wstep.
    wstep. if_cases K3; zify_cond K3.
    2:{ rewrite PG3_None by (apply get_sym_None; g8; unfold blk_cap; rewrite En; clear -K3 Rn; lia).
      wstep. goE HD NBU MID SM DSTA DL Edb Lout FSL MU WM. clear -Inu Iav; lia. }
    eassert (GS2 : get_sym (D8 k0 3 (nu + 2) k0 (w / 256) (rN1 - 1) rt cb) = Some _).
    { apply get_sym_FR; g8; [unfold blk_cap; rewrite En; clear -K3 Rn; lia | rewrite Esm; exact HSM | rewrite RD1; lia]. }
    rewrite (PG3_b _ _ _ _ _ _ GS2). clear GS2. g8.
    (* [comment removed for export] *)
    arun_to 0x86338%Z. tt_load (w / 256)%Z.
    pose proof (Rtt (w / 256)%Z) as Rw2. set (w2 := zget (d_tt d0) (w / 256)) in *. rewrite ?(zx32_of_Z w2) by lia.
    (* [comment removed for export] *)
    arun_to 0x8634c%Z.
    wstep. if_cases K4; zify_cond K4.
    { (* [comment removed for export] *)
      rewrite (S0F_bzd_fr1.rNn_nz (rN1 - 1) rt ltac:(clear -K4; lia)), (S0F_bzd_fr1.rTn_nz (rN1 - 1) rt ltac:(clear -K4; lia)).
      unfold A0F_bzd_fr1.R3S in R3.
      enter_with (R3 _ _ _ _ _ _ nu k0 (rN1 - 1)%Z rt cb out av tout tol toh w2 dbytes rest);
        [ st_eq
        | ch_close HD NBU MID SM DSTA DL Edb Lout FSL MU WM
        | unfold S0F_bzd_fr1.finv; clear -Ioc Iol Inu Hk0 Itp Irn Irt Icb Iav Rw2 RrN1 Hnu K4; repeat match goal with |- _ /\ _ => split end; lia
        | clear -Hf; lia | exact Hav1 | exact Hk0 | clear -Hnu K1; lia | exact Rw2 | clear -RrN1 K4; lia ]. }
    (* [comment removed for export] *)
    pose proof (rNums_range rt ltac:(clear -Irt; lia)) as RNR.
    refill 0x86368%Z 0x8638c%Z 0x863a8%Z 0x863b8%Z rt Irt.
    pose proof (Z.mod_pos_bound (rt + 1) 512 ltac:(lia)) as RT'.
    assert (Ez : (rN1 - 1 = 0)%Z) by (clear -K4 RrN1; lia).
    rewrite Ez. rewrite S0F_bzd_fr1.rNn_z, (S0F_bzd_fr1.rTn_z rt) by (clear -Irt; lia).
    unfold A0F_bzd_fr1.R3S in R3.
    enter_with (R3 _ _ _ _ _ _ nu k0 (rNums rt) ((rt + 1) mod 512)%Z cb out av tout tol toh w2 dbytes rest);
      [ st_eq
      | ch_close HD NBU MID SM DSTA DL Edb Lout FSL MU WM
      | unfold S0F_bzd_fr1.finv; clear -Ioc Iol Inu Hk0 Itp Irn Irt Icb Iav Rw2 RrN1 Hnu RT' RNR; repeat match goal with |- _ /\ _ => split end; lia
      | clear -Hf; lia | exact Hav1 | exact Hk0 | clear -Hnu K1; lia | exact Rw2 | clear -RNR; lia ].
  Time Qed.
End FR.
End ACeilS1.
