(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface D_defs D_kit. Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_kit.TwinB__.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2B Require Import L2Kit L2StmtD B0F_decK B0F_decX.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzTac BzTables CmpMem AsanKit AsanKit2 AsanCut AsanCutB0 AsanKitB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzInv BzContracts.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState BzDBlock BzDK BzDU4 DecCutFB B0F_decV B0F_leafCut B0F_mm B0F_hbc.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).

(* [comment removed for export] *)
Definition dk_setm0 (A : act14) (m : mem) (F : bvmap 5 word) (fc : bv 32) : act14 :=
  ACT (a_ra A) (a_sp A) (a_gp A) (a_tp A) (a_s0 A) (a_s1 A) (a_s2 A) (a_s3 A) (a_s4 A) (a_s5 A) (a_s6 A) (a_s7 A) (a_s8 A) (a_s9 A) (a_s10 A) (a_s11 A)
      F fc m (a_cx A) (a_h0 A) (a_b0 A) (a_lo A) (a_g1 A) (a_sv A) (a_payload A) (a_P A) (a_fb A) (a_shs A) (a_sht A) (a_shf A).

Section ACeilS1.
Context {ACEIL__ : ACeil}.

Lemma act_ok_setm0 : forall ihi A0 m F fc, act_ok ihi A0 -> act_ok ihi (dk_setm0 A0 m F fc).
Proof. intros ihi A0 m F fc H. destruct A0. exact H. Qed.

(* [comment removed for export] *)
Section QLS.
Variable RT : rt_sig. Variable PMc : Model -> Prop. Variable T : TSet.
Definition QL (Σ : rts RT) (R0 : dres) : dres -> machine_state -> Prop :=
  fun r ms => r = R0 -> forall c', ASTA RT Σ PMc (eq ms) c' -> realizes bsegs c' T.
End QLS.

(* [comment removed for export] *)
Ltac ag_sub AG := eapply agree_sub; [exact AG|]; let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; cbv beta in Hx.
Ltac dr_xfer_one AG m m' :=
  lazymatch goal with
  | |- Z.of_nat _ = _ => first [assumption| rewrite ?zw32_length, ?zb8_length by lia; reflexivity]
  | |- u32arr _ m' ?a _ => match goal with H : u32arr _ m a ?ws |- _ =>
        first [ solve [apply (n_u32arr_agree b0segs m m' a ws H); ag_sub AG; split; [unfold dfp; lia| cbn [outside]; lia]] | idtac ] end
  | |- u8arr _ m' ?a _ => match goal with H : u8arr _ m a ?bs |- _ =>
        first [ solve [apply (n_u8arr_agree b0segs m m' a bs H); ag_sub AG; split; [unfold dfp; lia| cbn [outside]; lia]] | idtac ] end
  end.
Ltac dr_xfer D AG m m' :=
  destruct D as ((A1&L1)&(A2&L2)&(A3&L3)&(A4&L4)&(A5&L5)&(A6&L6)&(A7&L7)&(A8&L8)&(A9&L9)&(A10&L10)&(A11&L11)&(A12&L12)&(A13&L13)&(A14&L14));
  unfold drest_at; repeat match goal with |- _ /\ _ => split end; dr_xfer_one AG m m'.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dmemL_restM : forall cx payload (m m' : mem) J d d' s (Hole : Z -> Prop), Z.of_nat (length payload) = b_len cx ->
  agree_on (fun x => dfp cx x /\ ~ Hole x) m m' ->
  (forall x, Hole x -> (b_s cx + 68 <= x < b_s cx + 1092) \/ (b_s cx + 2124 <= x < b_s cx + 64036)) ->
  (forall x, Hole x -> ~ (b_strm cx <= x < b_strm cx + 80) /\ ~ (b_src cx <= x < b_src cx + b_len cx) /\ outside (blk_ivls cx) x) ->
  hd_of cx J d' = hd_of cx J d -> d_nused d' = d_nused d -> d_cftab d' = d_cftab d ->
  sv_nblock (d_sv d') = sv_nblock (d_sv d) -> blk_of cx d' = blk_of cx d ->
  rw_cells b0segs m' (b_s cx + 3152) (MID_CELLS (mid_of cx d')) ->
  drest_at b0segs m' (b_s cx) (r_of d') ->
  dmemL cx payload m (dvF cx J d s) -> dmemL cx payload m' (dvF cx J d' s).
Proof.
  intros cx payload m m' J d d' s Hole PL AG HIN HOUT E1 E2 E3 E5 E6 MID' DR' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
  unfold dmemL. cbn [dvF dv_h dv_nbu dv_cf dv_d dv_j1 dv_snb dv_j2 dv_r dv_b dv_k] in *. rewrite E1, E2, E3, E5, E6.
  assert (NH : forall x, ~ ((b_s cx + 68 <= x < b_s cx + 1092) \/ (b_s cx + 2124 <= x < b_s cx + 64036)) -> ~ Hole x)
    by (intros x N HX; exact (N (HIN x HX))).
  split. { apply (n_rw_cells_agree b0segs m m' _ _ H1). ag_sub AG. cbn [cells_size csize Nat.add] in Hx. split; [unfold dfp; lia| apply NH; lia]. }
  split. { apply (n_rw_cells_agree b0segs m m' _ _ H2). ag_sub AG. cbn [cells_size csize Nat.add] in Hx. split; [unfold dfp; lia| apply NH; lia]. }
  split. { apply (n_u32arr_agree b0segs m m' _ _ H3). ag_sub AG. rewrite zw32_length in Hx by lia. split; [unfold dfp; lia| apply NH; lia]. }
  split; [exact MID'|].
  split. { apply (n_rw_cells_agree b0segs m m' _ _ H5). ag_sub AG. cbn [cells_size csize Nat.add] in Hx. split; [unfold dfp; lia| apply NH; lia]. }
  split; [exact DR'|].
  split. { apply (n_rw_cells_agree b0segs m m' _ _ H7). ag_sub AG. cbn [cells_size csize Nat.add] in Hx. split; [unfold dfp; lia|]. intros HX. destruct (HOUT x HX) as (N1 & _). apply N1. lia. }
  split. { apply (blk_agree m m' _ _ _ H8 AG). intros x Hx. split; [unfold dfp; tauto|]. intros HX. destruct (HOUT x HX) as (_ & _ & N3). exact (Hx N3). }
  apply (bytes_at_agree b0segs m m' _ _ H9). ag_sub AG. split; [unfold dfp; lia|]. intros HX. destruct (HOUT x HX) as (_ & N2 & _). apply N2. lia.
Qed.

(* [comment removed for export] *)
Lemma dmx_mm : forall cx payload (m m' : mem) J d s, Z.of_nat (length payload) = b_len cx ->
  agree_on (fun x => dfp cx x /\ outside [(b_s cx + 3192, b_s cx + 3196); (b_s cx + 3468, b_s cx + 3724)] x) m m' ->
  dsep cx ->
  rw_cells b0segs m' (b_s cx + 3152)
    [C8 (Z_to_bv 64 (b_tt cx)); C8 (Z_to_bv 64 (b_ll16 cx)); C8 (Z_to_bv 64 (b_ll4 cx));
     C4 (Z_to_bv 64 (d_sbcrc d)); C4 (Z_to_bv 64 (d_sccrc d)); C4 (Z_to_bv 64 (d_cbcrc d)); C4 (Z_to_bv 64 (d_cccrc d));
     C4 (Z_to_bv 64 (snd (mkmaps 256 0 (d_inUse d) (d_s2u d) 0)))] ->
  u8arr b0segs m' (b_s cx + 3468) (zb8 (fst (mkmaps 256 0 (d_inUse d) (d_s2u d) 0)) 256) ->
  dmemL cx payload m (dvF cx J d s) -> dmemL cx payload m' (dvF cx J (makeMaps_d d) s).
Proof.
  intros cx payload m m' J d s PL AG HOUT MID' S2U' DM.
  unfold makeMaps_d. destruct (mkmaps 256 0 (d_inUse d) (d_s2u d) 0) as [s2u' n'] eqn:MK. cbn [fst snd] in MID', S2U'.
  apply (dmemL_restM cx payload m m' J d _ s (fun x => (b_s cx + 3192 <= x < b_s cx + 3196) \/ (b_s cx + 3468 <= x < b_s cx + 3724)) PL); try reflexivity; try exact DM.
  - ag_sub AG. destruct Hx as [Hx1 Hx2]. split; [exact Hx1|]. cbn [outside]. lia.
  - intros x Hx. lia.
  - intros x Hx. apply HOUT. lia.
  - exact MID'.
  - destruct DM as (_ & _ & _ & _ & _ & D & _).
    cbn [dvF dv_r] in D. dr_xfer D AG m m'.
    all: cbn [r_of r_s2u r_inUse d_s2u d_inUse d_set_nInUse d_set_s2u].
    all: first [exact S2U' | rewrite zb8_length by lia; reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma B0F_mm_lift : forall A, act_ok BIHI0 A -> act_sh DI_B0 A -> BIHI0 <= b_s (a_cx A) ->
  forall (J : jk) (dm : dst) (s : dstrm) (m : mem)
         (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (Fr : bvmap 5 word) (fc : bv 32),
  dmem DI_B0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J dm s) ->
  stk b0segs m (a_lo A) (a_P A) -> munch (W14 A) (a_m0 A) m -> mem_inv b0segs m ->
  BzDU4.inUse_ok dm ->
  aconsts B0C m ->
  evt b0segs (B0F_leafCut.makeMaps_d_apostF B0F_leafCut.B0_FR_makeMaps_d b0segs ra (Z_to_bv 64 (a_P A)) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Fr fc
                (b_s (a_cx A)) (Z_to_bv 64 (b_tt (a_cx A))) (Z_to_bv 64 (b_ll16 (a_cx A))) (Z_to_bv 64 (b_ll4 (a_cx A)))
                (Z_to_bv 64 (d_sbcrc dm)) (Z_to_bv 64 (d_sccrc dm)) (Z_to_bv 64 (d_cbcrc dm)) (Z_to_bv 64 (d_cccrc dm)) (d_inUse dm) (d_s2u dm) (a_lo A) m)
      (MS (mkR ra (Z_to_bv 64 (a_P A)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (b_s (a_cx A))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0xb5bd8) fc None m (seg_rom b0segs)).
Proof.
  intros A AOK ASH HI J dm s m ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc DM ST MU MI IU AC.
  pose proof (alin_core _ _ AOK) as LIN. cbv zeta in LIN.
  assert (PU : bv_unsigned (Z_to_bv 64 (a_P A)) = a_P A) by (apply unsigned_lit; lia).
  pose proof (B0F_mm.B0_makeMaps_d ra (Z_to_bv 64 (a_P A)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (b_s (a_cx A))) a1 a2 a3 a4 a5 a6 a7
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m (b_s (a_cx A)) (a_lo A)
                (Z_to_bv 64 (b_tt (a_cx A))) (Z_to_bv 64 (b_ll16 (a_cx A))) (Z_to_bv 64 (b_ll4 (a_cx A)))
                (Z_to_bv 64 (d_sbcrc dm)) (Z_to_bv 64 (d_sccrc dm)) (Z_to_bv 64 (d_cbcrc dm)) (Z_to_bv 64 (d_cccrc dm)) (Z_to_bv 64 (d_nInUse dm))
                (d_inUse dm) (d_s2u dm)) as SPEC.
  cbv zeta in SPEC. unfold B0F_leafCut.B0_FR_makeMaps_d in SPEC |- *.
  cbn [aci_segs aci_hi aci_c CmpCut.ci_segs CmpCut.ci_hi B0C] in SPEC. rewrite PU in SPEC.
  pose proof DM as (_ & _ & _ & MID & _ & DR & _). cbn [dvF dv_d dv_r] in MID, DR.
  destruct DR as (_ & _ & (IUA & _) & _ & (S2A & _) & _). cbn [r_of r_inUse r_s2u] in IUA, S2A.
  apply SPEC; clear SPEC.
  - reflexivity.
  - exact MID.
  - exact IUA.
  - exact S2A.
  - intros i Hi. pose proof (IU i Hi) as B. clear - B. lia.
  - exact MI.
  - exact ST.
  - lia.
  - pose proof (act_ok_al _ _ AOK) as AL. unfold ctx_alA in AL. destruct AL as (ALS & _). clear - ALS. Z.div_mod_to_equations. lia.
  - lia.
  - lia.
  - right. lia.
  - exact AC.
  - lia.
  - lia.
  - destruct ASH as (SHS & _). cbv zeta in SHS. b0img.
    eapply (shzW_sub b0segs (W14 A) _ (a_m0 A) m _ _ _ _ SHS MU); [ | lia | lia ].
    unfold sub_fp, W14, DSTATE_SIZE. intros x Ho. cbn [outside app] in Ho |- *. destruct Ho as (H1 & _ & H3 & _). split; [lia|]. split; [lia|]. split; [lia| exact I].
Qed.

Lemma B0F_hbc_lift : forall A, act_ok BIHI0 A -> act_sh DI_B0 A -> BIHI0 <= b_s (a_cx A) ->
  forall (J : jk) (dm : dst) (s : dstrm) (m : mem) (t mn mx alpha : Z)
         (ra gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (Fr : bvmap 5 word) (fc : bv 32),
  let S := b_s (a_cx A) in
  dmem DI_B0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J dm s) ->
  stk b0segs m (a_lo A) (a_P A) -> munch (W14 A) (a_m0 A) m -> mem_inv b0segs m ->
  0 <= t < 6 -> 1 <= alpha <= 258 -> (1 <= mn /\ mn <= mx <= 20) ->
  (forall j, 0 <= j < alpha -> mn <= uv8 (rows_lbs dm t) j <= mx) ->
  aconsts B0C m ->
  evt b0segs (B0F_leafCut.hbCreateDecodeTables_apostF B0F_leafCut.B0_FR_hbCreate b0segs ra (Z_to_bv 64 (a_P A)) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Fr fc
                S t (rows_lws dm t) (rows_bws dm t) (rows_pws dm t) (rows_lbs dm t) mn mx alpha (a_lo A) m)
      (MS (mkR ra (Z_to_bv 64 (a_P A)) gp tp t0 t1 t2 s0 s1
               (Z_to_bv 64 (S + 45436 + 1032 * t)) (Z_to_bv 64 (S + 51628 + 1032 * t)) (Z_to_bv 64 (S + 57820 + 1032 * t)) (Z_to_bv 64 (S + 43888 + 258 * t))
               (Z_to_bv 64 mn) (Z_to_bv 64 mx) (Z_to_bv 64 alpha) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0xa8eac) fc None m (seg_rom b0segs)).
Proof.
  intros A AOK ASH HI J dm s m t mn mx alpha ra gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc.
  cbv zeta. intros DM ST MU MI Ht Ha Hmm HLEN AC.
  pose proof (alin_core _ _ AOK) as LIN. cbv zeta in LIN.
  assert (PU : bv_unsigned (Z_to_bv 64 (a_P A)) = a_P A) by (apply unsigned_lit; lia).
  destruct (dmx_rows_pre (a_cx A) (a_payload A) m J dm s t Ht (dmemL_of m (a_cx A) _ _ _ _ DM)) as (RL & NL & RB & NB & RP & NP & R8 & N8).
  pose proof (B0F_hbc.B0_hbCreateDecodeTables ra (Z_to_bv 64 (a_P A)) gp tp t0 t1 t2 s0 s1
                (Z_to_bv 64 (b_s (a_cx A) + 45436 + 1032 * t)) (Z_to_bv 64 (b_s (a_cx A) + 51628 + 1032 * t)) (Z_to_bv 64 (b_s (a_cx A) + 57820 + 1032 * t))
                (Z_to_bv 64 (b_s (a_cx A) + 43888 + 258 * t)) (Z_to_bv 64 mn) (Z_to_bv 64 mx) (Z_to_bv 64 alpha) a7
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m (b_s (a_cx A)) t (rows_lws dm t) (rows_bws dm t) (rows_pws dm t) (rows_lbs dm t)
                mn mx alpha (a_lo A)) as SPEC.
  cbv zeta in SPEC. unfold B0F_leafCut.B0_FR_hbCreate, B0F_leafCut.hbCreate_W in SPEC |- *.
  cbn [aci_segs aci_hi aci_c CmpCut.ci_segs CmpCut.ci_hi B0C] in SPEC. rewrite PU in SPEC.
  apply SPEC; clear SPEC; try reflexivity.
  - exact RL. - exact NL. - exact RB. - exact NB. - exact RP. - exact NP. - exact R8. - exact N8.
  - pose proof (act_ok_al _ _ AOK) as AL. unfold ctx_alA in AL. destruct AL as (ALS & _). split; [lia|]. split; [exact ALS| exact Ht].
  - lia.
  - right. lia.
  - exact ST.
  - lia.
  - exact MI.
  - exact Ha.
  - exact Hmm.
  - exact HLEN.
  - exact AC.
  - lia.
  - lia.
  - destruct ASH as (SHS & _). cbv zeta in SHS. b0img.
    eapply (shzW_sub b0segs (W14 A) _ (a_m0 A) m _ _ _ _ SHS MU); [ | lia | lia ].
    unfold sub_fp, W14, DSTATE_SIZE. intros x Ho. cbn [outside app] in Ho |- *. destruct Ho as (H1 & _ & H3 & _).
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia| exact I].
Qed.
End ACeilS1.
