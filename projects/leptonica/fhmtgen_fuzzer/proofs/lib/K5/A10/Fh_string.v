(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_leaf LeptL_kit Gm_iface Fh_iface Fh_sel_iface Fh_statics.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma tr_stringNew : In [0x9154c] CLIENT_TRACES. Proof. apply ct_mem_In; vm_compute; reflexivity. Qed.

Section STRNEW.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis RC : rt_contracts RT.

Theorem stringNew_ok : stringNew_cps RT.
Proof using AF GP RC.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo src str
    FDO MST -> -> SLO SHI S8 SLEN SB SNZ INL ENV RES.
  unfold lpost, lenv, lres, keeps, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (acc_lit RT AF Σ m src 8 ART0 INL) as SACC.
  assert (SRNG : rng_class RT Σ src 8) by (apply rng_class_image; assumption).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_stringNew, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  destruct str as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|]]]]]]]]; try discriminate SLEN. clear SLEN. cbn [app] in SB.
  assert (SRCB : forall mm, mem_inv asegs mm -> ro_cells asegs mm src [C1 b0; C1 b1; C1 b2; C1 b3; C1 b4; C1 b5; C1 b6; C1 (Z_to_bv 8 0)]).
  { intros mm MIm. split; [cbn; tauto|]. cbn [cells_bytes cbytes app]. apply (ro_bytes_at asegs mm src _ MIm); [lia| cbn [length]; lia| exact SB]. }
  walk_to AF MST [(usp - 48, usp)] [e_strlen].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  eapply cps_seq.
  { pose proof (rc_strlen RT RC) as SL; unfold strlen_icontract in SL;
    eapply SL with (lo := lo) (s := src) (str := [b0; b1; b2; b3; b4; b5; b6]) (slack := @nil byte); rt_side idtac.
    - lazymatch goal with |- bytes_at asegs ?mm _ _ => exact (proj2 (SRCB mm ltac:(assumption))) end.
    - cbn [length]; lia.
    - cbn [length]. change (Z.of_nat 7) with 7. change (Z.of_nat 0) with 0. clear - S8. Z.div_mod_to_equations. lia.
    - lia.
    - left. cbn [length]. change (Z.of_nat 7) with 7. change (Z.of_nat 0) with 0. lia.
    - cbn [length]. change (Z.of_nat 7 + 1) with 8. unfold checked_src. split; [intros _; split; assumption| left; lia]. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| lia]).
  refresh RT AF. unfold SHB in *.
  walk_to AF MST [(usp - 48, usp)] [e_calloc].
  cbn [length]. change (Z.of_nat 7) with 7.
  lazymatch goal with |- context [Z_to_bv 64 (bv_signed (Z_to_bv 64 ?e) / 4294967296)] =>
    let v := eval vm_compute in (bv_signed (Z_to_bv 64 e) / 4294967296) in
    change (bv_signed (Z_to_bv 64 e) / 4294967296) with v end.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  eapply cps_seq.
  { pose proof (gp_calloc RT GP) as CC; unfold calloc_contract in CC; eapply CC with (lo := lo) (nmemb := 8) (size := 1); rt_side idtac;
    [ unfold CALLOC_MAX; lia
    | apply unwind_okC_of_ok; rewrite ?unsigned_lit by lia; [exact tr_stringNew| left; ul] ]. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
  change (8 * 1) with 8 in *. change (Z.to_nat 8) with 8%nat in *.
  lazymatch goal with H : rt_live RT ?S = (?p, 8) :: _ |- _ => rename H into LVD; rename S into Σ1; set (dest := p) in * end.
  assert (SACCF : forall (S' : rts RT) m', ART RT S' m' -> acc asegs m' src 8) by (intros S' m' A'; exact (acc_lit RT AF S' m' src 8 A' INL)).
  assert (IND : In (dest, 8) (rt_live RT Σ1)) by (rewrite LVD; left; reflexivity).
  lazymatch goal with A : ART RT Σ1 ?mm, MIc : mem_inv asegs ?mm |- cps _ (ASTA RT Σ1 _ _) _ =>
    pose proof (af_live_range RT AF Σ1 mm dest 8 A IND) as (_ & PDHI & PDSEG);
    pose proof (gp_live_hi RT GP Σ1 mm dest 8 A IND) as PDSH;
    assert (NCA : forall a, PF a -> a < dest \/ dest + 8 <= a)
      by (intros a Ha; apply (new_chunk_apart RT AF Σ1 mm dest 8 (rt_live RT Σ) (rt_frames RT Σ) usp a A LVD);
          [ assumption | repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul | exact Ha ]);
    pose proof (SRCB mm MIc) as SRC; pose proof (SACCF Σ1 mm A) as SACC1 end.
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  refresh RT AF. unfold SHB in *.
  walk_to AF MST [(usp - 48, usp); (dest, dest + 8)] (@nil Z).
  assert (NZ : forall b, In b [b0; b1; b2; b3; b4; b5; b6] -> bv_unsigned b <> 0).
  { intros b Hb E. apply SNZ. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E. reflexivity. }
  pose proof (NZ b0 ltac:(cbn; tauto)) as NZ0. pose proof (NZ b1 ltac:(cbn; tauto)) as NZ1. pose proof (NZ b2 ltac:(cbn; tauto)) as NZ2.
  pose proof (NZ b3 ltac:(cbn; tauto)) as NZ3. pose proof (NZ b4 ltac:(cbn; tauto)) as NZ4. pose proof (NZ b5 ltac:(cbn; tauto)) as NZ5.
  pose proof (NZ b6 ltac:(cbn; tauto)) as NZ6.
  pose proof (bv_unsigned_in_range 8 b0) as RB0. pose proof (bv_unsigned_in_range 8 b1) as RB1. pose proof (bv_unsigned_in_range 8 b2) as RB2.
  pose proof (bv_unsigned_in_range 8 b3) as RB3. pose proof (bv_unsigned_in_range 8 b4) as RB4. pose proof (bv_unsigned_in_range 8 b5) as RB5.
  pose proof (bv_unsigned_in_range 8 b6) as RB6. change (bv_modulus 8) with 256 in *.
  awalk (@nil Z).
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [| exact I]];
                      intros zz Hzz; right; right; left; exists dest, 8; split; [exact IND| lia]).
  lazymatch goal with
  | AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ =>
      is_var PFx; agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); pose proof (NCA _ Hx); repeat split; lia)
  end.
  apply cps_finish; intros c Hc; subst QF; cbv beta.
  exists Σ1, dest.
  split; [| rewrite LVD; alg_tac].
  eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
  split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
  split; [split; [split; [assumption| split; [assumption| split; [| assumption]]]| split; assumption]|].
  { repeat match goal with H : wmono asegs _ _ |- _ => revert H end. clear. intros. eauto using wmono_trans. }
  split; [intros a Ha _; apply AGF; exact Ha|].
  lazymatch goal with H : rw_cells asegs ?mm dest ?cs |- bytes_at asegs ?mm dest _ =>
    destruct H as [[_ HB] _]; cbn [cells_bytes cbytes app] in HB; rewrite ?Z_to_bv_bv_unsigned in HB end.
  assert (EB : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b).
  { intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. }
  rewrite !EB in HB.
  exact HB.
Qed.

End STRNEW.
