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
  Ltac sbl := wstep; lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) => rewrite ?le1_sx32, ?S0F_bzd_fr1.byte_of_u64, ?BzInv.le1_lit; mem_after_store end.
  (* [comment removed for export] *)
  Definition FSLf (m : word -> option byte) : Prop :=
    rw_cells a0segs m uspi
      (bzd_slots S SHS w0 w32 w104 w112 (Z_to_bv 64 (SHS + -2147450877)) (Z_to_bv 64 (SHS + -2147450878)) (Z_to_bv 64 (SHS + -2147450872))
                 (Z_to_bv 64 (SHS + -2147450873)) (Z_to_bv 64 (SHS + -2147450875)) (Z_to_bv 64 (SHS + -2147450744)) (Z_to_bv 64 (SHS + -2147442870))).
  (* [comment removed for export] *)
  Definition CHf (m : word -> option byte) (oc ol nu k0 tp rn rt cb : Z) (out : list Z) (av tout : Z) (tol toh : word) (dbytes rest : list byte) : Prop :=
    DSgA DI_A0 c m (JJ tol toh) (D8 oc ol nu k0 tp rn rt cb) (S3 out av tout) /\ DESTgA DI_A0 c m (S3 out av tout) dbytes rest /\
    FSLf m /\ RO m /\ munch WB m0 m /\ wmono a0segs m0 m.

  (* [comment removed for export] *)
  Definition MSx (f : nat) : Prop :=
    forall (t0 t2 a3 a4 a5 a6 s3 s4 s7 t3 t4 t5 t6 : word) (m : word -> option byte)
           (oc ol nu k0 tp rn rt cb : Z) (out : list Z) (av tout : Z) (tol toh : word) (dbytes rest : list byte),
      CHf m oc ol nu k0 tp rn rt cb out av tout tol toh dbytes rest ->
      finv oc ol nu k0 tp rn rt cb av -> (PP - nu <= Z.of_nat f)%Z ->
      evt a0segs (KQ (K_PM f (D8 oc ol nu k0 tp rn rt cb) (S3 out av tout)))
          (MS (SRR cra t0 ct1 t2 (Z_to_bv 64 (STRM + 32)) cstrm ca2 a3 a4 a5 a6 ca7 s3 s4 csh cs6 s7 cs8 t3 t4 t5 t6) F (Z_to_bv 64 0x85e64) fc None m (seg_rom a0segs)).
  (* [comment removed for export] *)
  Definition TLS (f : nat) : Prop :=
    forall (t0 t2 a0 a1 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 t3 t4 t5 t6 : word) (m : word -> option byte)
           (oc ol nu k0 tp rn rt cb : Z) (out : list Z) (av tout : Z) (tol toh : word) (dbytes rest : list byte),
      CHf m oc ol nu k0 tp rn rt cb out av tout tol toh dbytes rest ->
      finv oc ol nu k0 tp rn rt cb av -> (PP - nu <= Z.of_nat f)%Z ->
      evt a0segs (KQ (K_PM f (D8 oc ol nu k0 tp rn rt cb) (S3 out av tout)))
          (MS (SRR cra t0 ct1 t2 a0 a1 ca2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 t3 t4 t5 t6) F (Z_to_bv 64 0x86604) fc None m (seg_rom a0segs)).
  (* [comment removed for export] *)
  Definition HS (f : nat) (ol : Z) : Prop :=
    forall (t0 t2 a0 a3 a4 a5 a6 s3 s4 s7 t3 t4 t5 t6 : word) (m : word -> option byte)
           (oc nu k0 tp rn rt cb : Z) (out : list Z) (av tout : Z) (tol toh : word) (dbytes rest : list byte),
      CHf m oc ol nu k0 tp rn rt cb out av tout tol toh dbytes rest ->
      finv oc ol nu k0 tp rn rt cb av -> (PP - nu <= Z.of_nat f)%Z -> (1 <= av)%Z ->
      evt a0segs (KQ (K_PH f (D8 oc ol nu k0 tp rn rt cb) (S3 out av tout)))
          (MS (SRR cra t0 ct1 t2 a0 cstrm ca2 a3 a4 a5 a6 ca7 s3 s4 csh cs6 s7 cs8 t3 t4 t5 t6) F (Z_to_bv 64 0x85e70) fc None m (seg_rom a0segs)).
  (* [comment removed for export] *)
  Definition OUTS (f : nat) (ol : Z) : Prop :=
    forall (t2 a0 a3 a4 a5 a6 s3 s4 s7 t3 t4 t5 t6 : word) (m : word -> option byte)
           (oc nu k0 tp rn rt cb : Z) (out : list Z) (av tout : Z) (tol toh : word) (dbytes rest : list byte),
      CHf m oc ol nu k0 tp rn rt cb out av tout tol toh dbytes rest ->
      finv oc ol nu k0 tp rn rt cb av -> (PP - nu <= Z.of_nat f)%Z -> (1 <= ol)%Z -> (1 <= av)%Z ->
      evt a0segs (KQ (K_PH f (D8 oc ol nu k0 tp rn rt cb) (S3 out av tout)))
          (MS (SRR cra c16 ct1 t2 a0 cstrm ca2 a3 a4 a5 a6 ca7 s3 s4 csh cs6 s7 cs8 t3 t4 t5 t6) F (Z_to_bv 64 0x85e84) fc None m (seg_rom a0segs)).
  (* [comment removed for export] *)
  Definition GS (f : nat) : Prop :=
    forall (t2 a0 a1 a3 a4 a5 a6 s3 s4 s7 t3 t4 t5 t6 : word) (m : word -> option byte)
           (oc nu k0 tp rn rt cb : Z) (out : list Z) (av tout : Z) (tol toh : word) (dbytes rest : list byte),
      CHf m oc 0 nu k0 tp rn rt cb out av tout tol toh dbytes rest ->
      finv oc 0 nu k0 tp rn rt cb av -> (PP - nu <= Z.of_nat f)%Z -> (1 <= av)%Z ->
      evt a0segs (KQ (K_PG f (D8 oc 0 nu k0 tp rn rt cb) (S3 out av tout)))
          (MS (SRR cra c16 ct1 t2 a0 a1 ca2 a3 a4 a5 a6 ca7 s3 s4 csh cs6 s7 cs8 t3 t4 t5 t6) F (Z_to_bv 64 0x86044) fc None m (seg_rom a0segs)).

  (* [comment removed for export] *)
  Definition R1S (f : nat) : Prop :=
    forall (a0 a1 s3 s6 s8 t3 : word) (m : word -> option byte)
           (nu k0 rN1 rt cb : Z) (out : list Z) (av tout : Z) (tol toh : word) (w : Z) (dbytes rest : list byte),
      CHf m k0 1 nu k0 (w / 256) rN1 rt cb out av tout tol toh dbytes rest ->
      finv k0 1 nu k0 (w / 256) rN1 rt cb av -> (PP - nu <= Z.of_nat f)%Z -> (1 <= av)%Z -> (0 <= k0 < 256)%Z ->
      (0 <= nu < PP)%Z -> (0 <= w < 4294967296)%Z -> (1 <= rN1 < 2147483648)%Z ->
      evt a0segs (KQ (PG1b f PP (Z.lxor (Z.land w 255) (if (rN1 - 1 =? 1)%Z then 1%Z else 0%Z))
                         (D8 k0 1 nu k0 (w / 256) (rN1 - 1) rt cb) (S3 out av tout)))
          (MS (SRR cra c16 ct1 cnn a0 a1 ca2 cnu (Z_to_bv 64 nu) c24 c60 c64 s3 (Z_to_bv 64 (w / 256)) (Z_to_bv 64 w) s6 cm4 s8 t3 cTT csnb (Z_to_bv 64 k0))
              F (Z_to_bv 64 0x861c8) fc None m (seg_rom a0segs)).
  Definition R2S (f : nat) : Prop :=
    forall (a0 a1 s5 s8 t3 : word) (m : word -> option byte)
           (nu k0 rN1 rt cb : Z) (out : list Z) (av tout : Z) (tol toh : word) (w : Z) (dbytes rest : list byte),
      CHf m k0 2 (nu + 1) k0 (w / 256) rN1 rt cb out av tout tol toh dbytes rest ->
      finv k0 2 (nu + 1) k0 (w / 256) rN1 rt cb av -> (PP - nu <= Z.of_nat f)%Z -> (1 <= av)%Z -> (0 <= k0 < 256)%Z ->
      (0 <= nu /\ nu + 1 < PP)%Z -> (0 <= w < 4294967296)%Z -> (1 <= rN1 < 2147483648)%Z ->
      evt a0segs (KQ (PG2b f PP (Z.lxor (Z.land w 255) (if (rN1 - 1 =? 1)%Z then 1%Z else 0%Z))
                         (D8 k0 2 (nu + 1) k0 (w / 256) (rN1 - 1) rt cb) (S3 out av tout)))
          (MS (SRR cra c16 ct1 cnn a0 a1 ca2 cnu (Z_to_bv 64 nu) c24 c60 c64 (Z_to_bv 64 (nu + 1)) (Z_to_bv 64 (w / 256)) s5 (Z_to_bv 64 w) cm4 s8 t3 cTT csnb (Z_to_bv 64 k0))
              F (Z_to_bv 64 0x862c0) fc None m (seg_rom a0segs)).
  Definition R3S (f : nat) : Prop :=
    forall (a0 a1 s6 s8 t3 : word) (m : word -> option byte)
           (nu k0 rN1 rt cb : Z) (out : list Z) (av tout : Z) (tol toh : word) (w : Z) (dbytes rest : list byte),
      CHf m k0 3 (nu + 2) k0 (w / 256) rN1 rt cb out av tout tol toh dbytes rest ->
      finv k0 3 (nu + 2) k0 (w / 256) rN1 rt cb av -> (PP - nu <= Z.of_nat f)%Z -> (1 <= av)%Z -> (0 <= k0 < 256)%Z ->
      (0 <= nu /\ nu + 2 < PP)%Z -> (0 <= w < 4294967296)%Z -> (1 <= rN1 < 2147483648)%Z ->
      evt a0segs (KQ (PG3b f PP (Z.lxor (Z.land w 255) (if (rN1 - 1 =? 1)%Z then 1%Z else 0%Z))
                         (D8 k0 3 (nu + 2) k0 (w / 256) (rN1 - 1) rt cb) (S3 out av tout)))
          (MS (SRR cra c16 ct1 cnn a0 a1 ca2 cnu (Z_to_bv 64 nu) c24 c60 c64 (Z_to_bv 64 w) (Z_to_bv 64 (w / 256)) (Z_to_bv 64 (nu + 2)) s6 cm4 s8 t3 cTT csnb (Z_to_bv 64 k0))
              F (Z_to_bv 64 0x863b8) fc None m (seg_rom a0segs)).
  (* [comment removed for export] *)
  Definition R4S (f : nat) : Prop :=
    forall (a0 a1 s3 s4 s5 s6 s8 t3 : word) (m : word -> option byte)
           (nu k0 rN1 rt cb : Z) (out : list Z) (av tout : Z) (tol toh : word) (w : Z) (dbytes rest : list byte),
      CHf m k0 3 (nu + 3) k0 (w / 256) rN1 rt cb out av tout tol toh dbytes rest ->
      finv k0 3 (nu + 3) k0 (w / 256) rN1 rt cb av -> (PP - nu <= Z.of_nat f)%Z -> (1 <= av)%Z -> (0 <= k0 < 256)%Z ->
      (0 <= nu /\ nu + 3 < PP)%Z -> (0 <= w < 4294967296)%Z -> (1 <= rN1 < 2147483648)%Z ->
      evt a0segs (KQ (PG4b f (Z.lxor (Z.land w 255) (if (rN1 - 1 =? 1)%Z then 1%Z else 0%Z))
                         (D8 k0 3 (nu + 3) k0 (w / 256) (rN1 - 1) rt cb) (S3 out av tout)))
          (MS (SRR cra c16 ct1 cnn a0 a1 ca2 cnu (Z_to_bv 64 nu) c24 c60 c64 s3 s4 s5 s6 cm4 s8 t3 cTT (Z_to_bv 64 w) (Z_to_bv 64 (w / 256)))
              F (Z_to_bv 64 0x864a0) fc None m (seg_rom a0segs)).
  (* [comment removed for export] *)
  Definition R5S (f : nat) : Prop :=
    forall (t0 t2 a0 a6 s3 s4 s5 s6 s7 s8 t3 t4 t5 t6 : word) (m : word -> option byte)
           (oc ol nu rN1 rt cb : Z) (out : list Z) (av tout : Z) (tol toh : word) (w : Z) (dbytes rest : list byte),
      CHf m oc ol (nu + 4) (Z.land w 255) (w / 256) rN1 rt cb out av tout tol toh dbytes rest ->
      finv oc ol (nu + 4) (Z.land w 255) (w / 256) rN1 rt cb av -> (PP - nu <= Z.of_nat f)%Z -> (1 <= av)%Z ->
      (0 <= nu /\ nu + 3 < PP)%Z -> (0 <= w < 4294967296)%Z -> (1 <= rN1 < 2147483648)%Z -> (4 <= ol <= 259)%Z ->
      evt a0segs (KQ (PG5b f (Z.lxor (Z.land w 255) (if (rN1 - 1 =? 1)%Z then 1%Z else 0%Z))
                         (D8 oc ol (nu + 4) (Z.land w 255) (w / 256) (rN1 - 1) rt cb) (S3 out av tout)))
          (MS (SRR cra t0 ct1 t2 a0 (Z_to_bv 64 (Z.land w 255)) ca2 cnu (Z_to_bv 64 nu) c24 a6 c64 s3 s4 s5 s6 s7 s8 t3 t4 t5 t6)
              F (Z_to_bv 64 0x865a8) fc None m (seg_rom a0segs)).

  Ltac ch_close HD NBU MID SM DSTA DL Edb Lout FSL MU WM :=
    unfold CHf; repeat match goal with |- _ /\ _ => split end;
    [dsg_close HD NBU MID SM| destg_close DSTA DL Edb Lout| unfold FSLf; fsl_close FSL| ro_close| exact MU| exact WM].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma fr_G1 : forall f, R1S f -> GS f.
  Proof.
    intros f R1. unfold GS. intros until rest. intros CHm FI Hf Hav1.
    cps_destruct CHm as (DSm & DE & FSL & ROm & MU & WM). unDS DSm. unRO ROm. cps_destruct DE as (DSTA & DL & Edb & Lout). prep. unSH. unFI FI.
    unfold DSgA in *. a0img. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in SAV. focbn_in Lout. unfold FSLf, bzd_slots in FSL.
    (* [comment removed for export] *)
    arun_to 0x86068%Z. try rewrite (sx32_of_Z nu) by lia.
    arun_to 0x86074%Z. try rewrite (sx32_of_Z snb) by lia. wstep.
    wstep. if_cases K1; zify_cond K1.
    { rewrite K_PG_done by (g8; clear -K1; lia). goJ HD NBU MID SM DSTA DL Edb Lout FSL MU WM.
      all: unfold id in Ik0, Rrnd; clear -Ioc Inu Ik0 Itp Irn Irt Icb Iav Rrnd K1 Rsnb; first [lia | intros; lia]. }
    (* [comment removed for export] *)
    wstep. wstep. if_cases K2; zify_cond K2; rewrite ?signed_lit_small in K2 by lia.
    2:{ rewrite K_PG_over by (g8; clear -K2; lia). wstep. goE HD NBU MID SM DSTA DL Edb Lout FSL MU WM. clear -Inu Iav; lia. }
    rewrite K_PG_go by (g8; clear -K1 K2; lia). g8.
    (* [comment removed for export] *)
    arun_to 0x860b8%Z. sbl.
    (* [comment removed for export] *)
    arun_to 0x860e0%Z. try rewrite (zx32_of_Z tp) by lia.
    (* [comment removed for export] *)
    arun_to 0x860ec%Z. rewrite ?En. try rewrite (sx32_of_Z n) by lia.
    wstep. wstep. wstep.
    (* [comment removed for export] *)
    pose proof (word_urange (Z_to_bv 64 tp)) as TPR.
    wstep. if_cases K3; zify_cond K3.
    2:{ assert (K3' : (cap <= bv_swrap 32 (tp + 0) mod 18446744073709551616)%Z) by (clear -K3; lia).
        pose proof (sextw_ge tp cap ltac:(lia) ltac:(lia) K3') as GE.
        change (2^32)%Z with 4294967296%Z in GE. rewrite (Z.mod_small tp 4294967296) in GE by lia.
        rewrite PG1_None by (apply get_sym_None; g8; unfold blk_cap; rewrite En; clear -GE; lia).
        wstep. goE HD NBU MID SM DSTA DL Edb Lout FSL MU WM. clear -Inu Iav; lia. }
    assert (K3' : (bv_swrap 32 (tp + 0) mod 18446744073709551616 < cap)%Z) by (clear -K3; lia).
    destruct (sextw_lt tp cap ltac:(lia) ltac:(lia) K3') as [LT XV].
    change (2^32)%Z with 4294967296%Z in LT, XV. rewrite (Z.mod_small tp 4294967296) in LT, XV by lia. clear K3 K3'.
    assert (Hk0 : (0 <= k0 < 256)%Z) by (unfold id in Ik0; clear -Ik0 LT En Rn; lia).
    eassert (GS1 : get_sym (D8 k0 1 nu k0 tp rn rt cb) = Some _).
    { apply get_sym_FR; g8; [unfold blk_cap; rewrite En; clear -LT; lia | rewrite Esm; exact HSM | rewrite RD1; lia]. }
    rewrite (PG1_b _ _ _ _ _ _ GS1). clear GS1. g8.
    (* [comment removed for export] *)
    arun_to 0x86130%Z.
    tt_load tp. pose proof (Rtt tp) as Rw1. set (w1 := zget (d_tt d0) tp) in *. rewrite ?(zx32_of_Z w1) by lia.
    (* [comment removed for export] *)
    arun_to 0x8615c%Z. try rewrite (sx32_of_Z rn) by lia.
    wstep. if_cases K4; zify_cond K4.
    { (* [comment removed for export] *)
      rewrite ?En, (S0F_bzd_fr1.rNn_nz rn rt K4), (S0F_bzd_fr1.rTn_nz rn rt K4).
      unfold R1S in R1.
      enter_with (R1 _ _ _ _ _ _ _ nu k0 rn rt cb out av tout tol toh w1 dbytes rest);
        [ st_eq
        | ch_close HD NBU MID SM DSTA DL Edb Lout FSL MU WM
        | unfold S0F_bzd_fr1.finv; clear -Ioc Iol Inu Hk0 Itp Irn Irt Icb Iav Rw1; repeat match goal with |- _ /\ _ => split end; lia
        | exact Hf | exact Hav1 | exact Hk0 | clear -Inu K1 K2; lia | exact Rw1 | clear -Irn K4; lia ]. }
    (* [comment removed for export] *)
    arun_to 0x86178%Z. try rewrite (sx32_of_Z rt) by lia.
    arun_to 0x8619c%Z.
    rn_load rt. pose proof (rNums_range rt ltac:(clear -Irt; lia)) as RNR.
    (* [comment removed for export] *)
    arun_to 0x861b8%Z. rewrite (rtpos_wrap rt) by (clear -Irt; lia).
    (* [comment removed for export] *)
    arun_to 0x861c8%Z.
    pose proof (Z.mod_pos_bound (rt + 1) 512 ltac:(lia)) as RT'.
    assert (Ern : rn = 0%Z) by (clear -K4 Irn; lia). subst rn. rewrite ?En, S0F_bzd_fr1.rNn_z, (S0F_bzd_fr1.rTn_z rt) by (clear -Irt; lia).
    unfold R1S in R1.
    enter_with (R1 _ _ _ _ _ _ _ nu k0 (rNums rt) ((rt + 1) mod 512)%Z cb out av tout tol toh w1 dbytes rest);
      [ st_eq
      | ch_close HD NBU MID SM DSTA DL Edb Lout FSL MU WM
      | unfold S0F_bzd_fr1.finv; clear -Ioc Iol Inu Hk0 Itp Irt Icb Iav Rw1 RT' RNR; repeat match goal with |- _ /\ _ => split end; lia
      | exact Hf | exact Hav1 | exact Hk0 | clear -Inu K1 K2; lia | exact Rw1 | clear -RNR; lia ].
  Time Qed.
End FR.
End ACeilS1.
