(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_Img A_Cocsh B_Co6gg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN ExW.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require ShdFast.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_dead ::=
  exfalso;
  match goal with SOK : OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_val_ok ?b ?a ?k |- _ =>
    (let BR := fresh "SBR" in pose proof (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.byte_range b) as BR;
     let MB := fresh "SMB" in first [ pose proof (Z.mod_pos_bound a 8 (@eq_refl comparison Lt)) as MB | idtac ]);   (* [comment removed for export] *)
    let Z0 := fresh "SZ" in let R1 := fresh "SR" in let R2 := fresh "SR" in
    destruct SOK as [Z0 | [R1 R2]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.sb_norm b a; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ShdFast.shd_mlia0
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma land_pagemask64 : forall x, 0 <= x < 2^64 ->
  Z.land x 18446744073709547520 = x / 4096 * 4096.
Proof.
  intros x Hx.
  assert (E : 18446744073709547520 = Z.ldiff (Z.ones 64) (Z.ones 12)) by reflexivity.
  rewrite E. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.ldiff_spec, !Z.testbit_ones_nonneg by lia.
  replace (x / 4096 * 4096) with (Z.shiftl (Z.shiftr x 12) 12).
  2:{ rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity. }
  destruct (Z.ltb_spec i 12) as [Hlt|Hge].
  - rewrite Z.shiftl_spec_low by lia.
    destruct (Z.testbit x i); cbn; rewrite ?Bool.andb_false_r; reflexivity.
  - rewrite Z.shiftl_spec_high, Z.shiftr_spec by lia. replace (i - 12 + 12) with i by lia.
    destruct (Z.ltb_spec i 64) as [Hlt2|Hge2].
    + cbn. rewrite Bool.andb_true_r. reflexivity.
    + cbn. rewrite Bool.andb_false_r. symmetry. apply Z.bits_above_log2; [lia|].
      destruct (Z.eq_dec x 0) as [->|Hnz]; [cbn; lia|]. apply Z.log2_lt_pow2; [lia|].
      eapply Z.lt_le_trans; [apply (proj2 Hx)|]. apply Z.pow_le_mono_r; lia.
Qed.

Section S.
Context {Clg : Ceiling}.
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma assert_VSB_state_ok : assert_VSB_state_stmt.
  Proof.
    unfold assert_VSB_state_stmt.
    intros until lo. intros A0 VSBC VINV A1 SHD CE SAL Slo Shi ST LO CEIL MI.
    rewrite A0, A1. unfold assert_VSB_state_entry, ASSERT_STATE_STACK in *.
    (first [ dand8 SHD as P NP SHS PAL P0 PLE PGE PCE | destruct SHD as (P & NP & SHS & PAL & P0 & PLE & PGE & PCE) ]). fold_cl_segs.
    pose proof (map_cells_of_consts _ (proj1 CE)) as MC.
    (first [ dand8 VINV as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vb16 | destruct VINV as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vb16) ]).
    unfold vsb_cells in VSBC.
    pose proof alloc_ceiling_num as ACV. unfold kHighMemBeg in Slo. all_app_facts.
    pose proof (shpat_sh_boundL (Clg:=Clg) P NP ltac:(lia) ltac:(lia) ltac:(lia)) as SHPB.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] v) as MU.
    pose proof (wmono_refl rsegs v) as WM.
    open_map_cells MC.
    carve_frame 16%nat ST.
    (* [comment removed for export] *)
    zstep. zstep.
    (* [comment removed for export] *)
    zstep. if_cases K; zify_cond K. { dead K. } clear K.
    (* [comment removed for export] *)
    zstep. zstep. if_cases K; zify_cond K. { exfalso. apply K. apply land7_of_mod8; lia. } clear K.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. shadow_chk SHS 4%Z 13.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. if_cases K; zify_cond K.
    { exfalso. revert K. rewrite Vfl. destruct fin; vm_compute; congruence. }
    clear K.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    try replace (bv_unsigned sp + -16 + 16) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold vsb_leaf_post, leaf_post.
    hot_eexists_k16. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section ExtLoop.
    Variables (xra xsp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
              (F : bvmap 5 word) (fc : bv 32) (m : mem) (sz : Z).
    Hypothesis SZ : 17 <= sz <= 4095.

    Notation AT pc xa1 xa3 :=
      (MS (mkR xra xsp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 sz) xa1 (Z_to_bv 64 (2^62)) xa3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

    (* [comment removed for export] *)
    #[using="SZ"] Lemma extsz_loop : forall (k : nat) (ns : Z) (xa3 : word),
      16 <= ns -> ns < sz -> sz <= ns * 2 ^ Z.of_nat k ->
      evt rsegs (fun ms => exists xa3', ms = AT 0x8b194 (Z_to_bv 64 (vsb_dbl k ns sz)) xa3')
                (AT 0x8b170 (Z_to_bv 64 ns) xa3).
    Proof.
      induction k as [|k IH]; intros ns xa3 Hns Hlt Hsz.
      - rewrite Z.pow_0_r in Hsz. lia.
      - rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hsz by lia.
        cbn [vsb_dbl]. rewrite (proj2 (Z.ltb_lt ns sz) Hlt).
        (* [comment removed for export] *)
        zstep. zstep. if_cases KG; zify_cond KG. { exfalso. unsign KG. klia KG. } clear KG.
        (* [comment removed for export] *)
        zstep. shl1_to_mul. zstep. if_cases KL; zify_cond KL; unsign KL.
        + (* [comment removed for export] *)
          apply IH; [klia Hns | klia KL |].
          replace (2 * ns * 2 ^ Z.of_nat k) with (ns * (2 * 2 ^ Z.of_nat k)) by ring. exact Hsz.
        + (* [comment removed for export] *)
          zstep. apply evt_done. eexists.
          replace (vsb_dbl k (2 * ns) sz) with (2 * ns); [reflexivity|].
          destruct k; cbn [vsb_dbl]; [reflexivity|]. rewrite (proj2 (Z.ltb_ge (2 * ns) sz)); [reflexivity| klia KL].
    Qed.
  End ExtLoop.

  Lemma VSB_extendsize_ok : VSB_extendsize_stmt.
  Proof.
    unfold VSB_extendsize_stmt.
    intros until lo. intros A0 SZ ST LO CEIL MI.
    rewrite A0. unfold VSB_extendsize_entry, EXTSZ_STACK in *.
    pose proof alloc_ceiling_num as ACV.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] v) as MU.
    pose proof (wmono_refl rsegs v) as WM.
    assert (X16 : sz <= vsb_extendsize sz).
    { destruct (Z.le_gt_cases 16 sz) as [H16|H16].
      - exact (proj1 (vsb_extendsize_spec sz ltac:(lia))).
      - unfold vsb_extendsize. rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [vsb_dbl].
        rewrite (proj2 (Z.ltb_ge 16 sz)) by lia. lia. }
    assert (XHI : vsb_extendsize sz < 2 * sz + 4096).
    { destruct (Z.le_gt_cases 16 sz) as [H16|H16].
      - exact (proj1 (proj2 (vsb_extendsize_spec sz ltac:(lia)))).
      - unfold vsb_extendsize. rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [vsb_dbl].
        rewrite (proj2 (Z.ltb_ge 16 sz)) by lia. lia. }
    carve_frame 16%nat ST.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    eapply (evt_cut rsegs (fun ms => exists xa2' xa3', ms =
        MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 sz) (Z_to_bv 64 (vsb_extendsize sz)) xa2' xa3' a4 a5 a6 a7
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8b198) fc None m (seg_rom rsegs))).
    { zstep. if_cases KR; zify_cond KR; unsign KR.
      - (* [comment removed for export] *)
        zstep. zstep. if_cases KW; zify_cond KW. { exfalso. unsign KW. klia KW. } clear KW.
        zstep. zstep. rewrite land_pagemask64 by (clear - SZ; lia).
        replace ((sz + 4095) / 4096 * 4096) with (vsb_extendsize sz)
          by (unfold vsb_extendsize; rewrite (proj2 (Z.ltb_ge _ _)) by lia; reflexivity).
        zstep. if_cases KA; zify_cond KA. { exfalso. unsign KA. clear - KA X16; lia. } clear KA.
        apply evt_done. eexists _, _. reflexivity.
      - (* [comment removed for export] *)
        zstep. zstep. if_cases KS; zify_cond KS; unsign KS.
        + (* [comment removed for export] *)
          zstep. zstep. if_cases KB; zify_cond KB; unsign KB.
          2:{ exfalso. clear - KB KS; lia. }
          apply evt_done. eexists _, _.
          replace (vsb_extendsize sz) with 16; [reflexivity|].
          unfold vsb_extendsize. rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [vsb_dbl].
          rewrite (proj2 (Z.ltb_ge 16 sz)); [reflexivity|]. klia KS.
        + (* [comment removed for export] *)
          zstep. zstep. zstep.
          replace (Z_to_bv 64 (Z.shiftl 1 62)) with (Z_to_bv 64 (2^62)) by reflexivity.
          eapply evt_cut; [eapply (extsz_loop) with (sz := sz) (k := 9%nat) (ns := 16); cbn; clear - KS KR; lia|].
          intros ms1 [xa3' ->].
          replace (vsb_dbl 9 16 sz) with (vsb_extendsize sz)
            by (unfold vsb_extendsize; rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity).
          zstep. if_cases KA; zify_cond KA. { exfalso. unsign KA. clear - KA X16; lia. } clear KA.
          apply evt_done. eexists _, _. reflexivity. }
    (intros ms1; (first [ intro dR_3; dand3 dR_3 as xa2' xa3' -> | intros (xa2' & xa3' & ->) ])).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    try replace (bv_unsigned sp + -16 + 16) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold leaf_post.
    hot_eexists_k3. exists a0. hot_eexists_k12. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  Qed.
End S.
