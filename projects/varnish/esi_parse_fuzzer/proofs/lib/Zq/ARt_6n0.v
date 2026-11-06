(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import AIcpm9j ARtStmts ARt_fpo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8z6.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8z6.dlia_nc.
(* [comment removed for export] *)
(* [comment removed for export] *)
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.lia0_first := Ltac2.Init.true.
(* [comment removed for export] *)

Ltac br_auto := first [ br_not_taken | br_taken ].
Ltac bstep1 := first [ azstep | if_false | if_true | br_auto ].
Ltac run_to_a pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => bstep1 end).
Ltac at_pc pc :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => idtac
  | |- evt _ _ (MS _ _ ?pc' _ _ _ _) => fail "not at pc" pc "but" pc'
  end.

Ltac decide_depth2 :=
  unfold unwind_depth2;
  repeat (first [ rewrite (proj2 (Z.ltb_lt _ _)) by lia | rewrite (proj2 (Z.ltb_ge _ _)) by lia
                | rewrite (proj2 (Z.leb_le _ _)) by lia | rewrite (proj2 (Z.leb_gt _ _)) by lia ]; cbn [andb]).

(* [comment removed for export] *)
Lemma rw_cells_app_split : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[WF BA] WR].
  apply cells_wf_app in WF. destruct WF as [WF1 WF2].
  rewrite cells_bytes_app in BA. apply bytes_at_app in BA. destruct BA as [BA1 BA2].
  rewrite (cells_bytes_length cs1 WF1) in BA2.
  rewrite cells_size_app, Nat2Z.inj_add in WR. (first [ dand3 WR as W0 W1 W2 | destruct WR as (W0 & W1 & W2) ]).
  split; (split; [split; assumption|]).
  - split; [lia|]. split; [lia|]. intros i Hi. apply W2. lia.
  - split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply W2. lia.
Qed.

Lemma rw_cells_cons_split : forall m A c cs,
  rw_cells rsegs m A (c :: cs) -> forall n, Z.of_nat (csize c) = n ->
  rw_cells rsegs m A [c] /\ rw_cells rsegs m (A + n) cs.
Proof.
  intros m A c cs H n Hn. destruct (rw_cells_app_split m A [c] cs H) as [H1 H2].
  cbn [cells_size] in H2. rewrite Nat.add_0_r, Hn in H2. split; assumption.
Qed.

Tactic Notation "csplit" hyp(H) constr(n) "as" ident(X) :=
  let H2 := fresh "CS" in
  destruct (rw_cells_cons_split _ _ _ _ H n eq_refl) as [X H2]; clear H; rename H2 into H.

Lemma rw_cells_join2 : forall m A c1 c2,
  rw_cells rsegs m A [c1] -> rw_cells rsegs m (A + Z.of_nat (csize c1)) [c2] -> rw_cells rsegs m A [c1; c2].
Proof.
  intros m A c1 c2 [[W1 B1] (R10 & R11 & R12)] [[W2 B2] (R20 & R21 & R22)]. cbn in W1, W2.
  cbn [cells_bytes app] in B1, B2. rewrite app_nil_r in B1, B2. cbn [cells_size Nat.add] in R11, R12, R21, R22.
  rewrite Nat.add_0_r in R11, R12, R21, R22.
  split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes]. rewrite app_nil_r. apply bytes_at_app. rewrite (cbytes_length c1 (proj1 W1)). tauto.
  - cbn [cells_size]. rewrite Nat.add_0_r, Nat2Z.inj_add. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.lt_ge_cases i (Z.of_nat (csize c1))); [apply R12; lia|].
    replace (A + i) with (A + Z.of_nat (csize c1) + (i - Z.of_nat (csize c1))) by lia. apply R22. lia.
Qed.
(* [comment removed for export] *)
Ltac depth1_obj OBJ obj :=
  let O16 := fresh "O16" in let OJ8 := fresh "OJ8" in let OJK := fresh "OJK" in
  csplit OBJ 8 as O16;
  lazymatch type of OBJ with rw_cells _ ?mm ?a (CB ?n ?l :: ?post) =>
    apply (rw_cells_split_CB rsegs mm a [] n l post [8; 2024]%nat) in OBJ; [| reflexivity]; cbn [app mk_CB_cells] in OBJ end;
  csplit OBJ 8 as OJ8; csplit OBJ 2024 as OJK; clear OJK;
  replace (obj + 16 + 8 + 8 + 2024) with (obj + 2056) in OBJ by lia;
  apply (rw_cells_join2 _ _ _ _ O16) in OJ8; clear O16; rename OJ8 into O16.

(* [comment removed for export] *)
Ltac unwind_tail FR FR0 ST OBJ sp obj :=
  run_to_a 0x79764;
  release_frame FR ST (bv_unsigned sp + -80);
  azstep; run_to_a 0x60bc4;
  release_frame FR0 ST (bv_unsigned sp);
  azstep;
  (* [comment removed for export] *)
  let O0 := fresh "O0" in let O8 := fresh "O8" in let O12 := fresh "O12" in
  csplit OBJ 8 as O0; csplit OBJ 4 as O8; csplit OBJ 4 as O12; clear O0 O12;
  replace (obj + 8 + 4 + 4) with (obj + 16) in OBJ by lia.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Theorem unwind_ok : unwind_stmt.
Proof.
  unfold unwind_stmt. intros until tfb0.
  intros MI ST LOLE CEIL A0 A1 A2 A3 A4 A5 PCR RA0 RANE BPAL VLE TOPR BOTR TC Cini Cgotps Cps TB Tstk TUNW OBJ FRM
         OBJLO OBJHI BPHI THRSEP RA.
  pose proof alloc_ceiling_val as CV.
  unfold unwind_entry, off_th_unwinding, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_all.
  pose proof (munch_refl [(bv_unsigned sp - 224, bv_unsigned sp); (obj + 8, obj + 12); (obj + 16, obj + 32); (obj + 2056, obj + 2064);
                          (thr + 3168, thr + 3168 + 1)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  pose proof (zr_word ra0) as RA0R; unfold inr64 in RA0R.
  pose proof (zr_word v) as VR; unfold inr64 in VR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof TC as TC0.
  (first [ dand13 TC as Ctsdi Ckey Ctsd Cctx Cthr Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct TC as (Ctsdi & Ckey & Ctsd & Cctx & Cthr & Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]). unfold pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_all.
  subst a0 a1 a2 a3 a4 a5.
  (* [comment removed for export] *) lazymatch goal with |- evt _ ?hotQ0 _ => set (hotQ := hotQ0) end. carve_frame 80%nat ST.
  run_to_a 0x60ac8. zstep.
  callz get_thread_ok.
  1:{ exact MI. }
  1:{ rewrite unsigned_lit by lia. exact ST. }
  1:{ rewrite unsigned_lit by lia. lia. }
  1:{ lia. }
  1:{ unfold thread_cells, kHighMemBeg. split; [exact Ctsdi | split; [exact Ckey | split; [exact Ctsd | split; [exact Cctx | split; [exact Cthr | plia]]]]]. }
  1:{ rewrite unsigned_lit by lia. reflexivity. }
  rename POST into ST.
  zstep. br_not_taken.
  run_to_a 0x60ae8. azstep.
  (* [comment removed for export] *)
  run_to_a 0x626ec.
  azstep. azstep. azstep.
  remember (Z.land ((0 - Z.b2z (bot <? top)) mod 18446744073709551616) top) as top' eqn:Htop.
  azstep. (* [comment removed for export] *)
  run_to_a 0x62744.
  azstep. azstep. azstep.
  remember (Z.land ((0 - Z.b2z (bot <? top)) mod 18446744073709551616) bot) as bot' eqn:Hbot.
  assert (TB' : 0 <= top' <= top /\ 0 <= bot' <= bot /\ (bot < top -> top' = top /\ bot' = bot) /\ (top <= bot -> top' = 0 /\ bot' = 0)).
  { subst top' bot'. destruct (Z.ltb_spec bot top); cbn [Z.b2z].
    - change ((0 - 1) mod 18446744073709551616) with (Z.ones 64). rewrite !(Z.land_comm (Z.ones 64)), !Z.land_ones, !Z.mod_small by lia. lia.
    - change ((0 - 0) mod 18446744073709551616) with 0. rewrite !Z.land_0_l. lia. }
  clear Htop Hbot.
  azstep. (* [comment removed for export] *)
  run_to_a 0x60b90. azstep. (* [comment removed for export] *)
  at_pc 0x79ca0. rename FR into FR0.
  carve_frame 64%nat ST.
  run_to_a 0x79db4.
  release_frame FR ST (bv_unsigned sp + -80).
  azstep. at_pc 0x79644.
  carve_frame 64%nat ST.
  run_to_a 0x7969c.
  replace (Z.land 18446744073709551615 bp) with bp in * by (rewrite Z.land_comm; change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones, Z.mod_small by lia; lia).
  replace (bp - 16) with (bp + -16) in FRM by lia.
  assert (LBP : Z.land bp 7 = 0).
  { change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8.
    rewrite (proj2 (Z.div_exact bp 16 ltac:(lia)) BPAL).
    replace (16 * (bp / 16)) with ((2 * (bp / 16)) * 8) by lia. apply Z_mod_mult. }
  (first [ dand4 TB' as Rt Rb Cbt Ctb | destruct TB' as (Rt & Rb & Cbt & Ctb) ]).
  destruct (Z.lt_ge_cases bot top) as [BT|BT].
  - destruct (Cbt BT) as [-> ->]. clear Cbt Ctb.
    destruct (Z.lt_ge_cases top 4096) as [T4|T4].
    + (* [comment removed for export] *)
      replace (Z.shiftr top 12) with 0 by (rewrite Z.shiftr_div_pow2, Z.div_small by lia; lia).
      run_to_a 0x79740.
      unwind_tail FR FR0 ST OBJ sp obj.
      depth1_obj OBJ obj.
      (subst hotQ; finish).
      all: try (replace (bv_unsigned sp - 224) with (bv_unsigned sp + -224) by lia; replace (thr + 3169) with (thr + 3168 + 1) by lia; exact MU).
      all: try assumption.
      all: decide_depth2; split; eassumption.
    + assert (K12 : 1 <= Z.shiftr top 12 < 2^52).
      { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia]. }
      revert K12. generalize (Z.shiftr top 12). intros k12 K12.
      azstep. br_taken.
      destruct (Z.lt_ge_cases bot bp) as [BB|BB].
      * destruct (Z.lt_ge_cases bp (top - 16)) as [PT|PT].
        -- (* [comment removed for export] *)
           repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x79740) _ _ _ _) => fail | _ => bstep1; try rewrite LBP end).
           unwind_tail FR FR0 ST OBJ sp obj.
           destruct (rw_cells_app_split _ _ [C8 (Z_to_bv 64 pc0); C8 ra0] _ OBJ) as [O16 OBJ']. change (Z.of_nat (cells_size [C8 (Z_to_bv 64 pc0); C8 ra0])) with 16 in OBJ'.
           csplit OBJ' 2024 as OJK. clear OJK.
           replace (obj + 16 + 16 + 2024) with (obj + 2056) in OBJ' by lia.
           (subst hotQ; finish).
      all: try (replace (bv_unsigned sp - 224) with (bv_unsigned sp + -224) by lia; replace (thr + 3169) with (thr + 3168 + 1) by lia; exact MU).
      all: try assumption.
      all: decide_depth2; split; eassumption.
        -- (* [comment removed for export] *) run_to_a 0x79740.
           unwind_tail FR FR0 ST OBJ sp obj.
           depth1_obj OBJ obj.
           (subst hotQ; finish).
      all: try (replace (bv_unsigned sp - 224) with (bv_unsigned sp + -224) by lia; replace (thr + 3169) with (thr + 3168 + 1) by lia; exact MU).
      all: try assumption.
      all: decide_depth2; split; eassumption.
      * (* [comment removed for export] *) run_to_a 0x79740.
           unwind_tail FR FR0 ST OBJ sp obj.
           depth1_obj OBJ obj.
           (subst hotQ; finish).
      all: try (replace (bv_unsigned sp - 224) with (bv_unsigned sp + -224) by lia; replace (thr + 3169) with (thr + 3168 + 1) by lia; exact MU).
      all: try assumption.
      all: decide_depth2; split; eassumption.
  - (* [comment removed for export] *)
    destruct (Ctb BT) as [-> ->]. clear Cbt Ctb.
    change (Z.shiftr 0 12) with 0.
    run_to_a 0x79740.
    unwind_tail FR FR0 ST OBJ sp obj.
    depth1_obj OBJ obj.
    (subst hotQ; finish).
      all: try (replace (bv_unsigned sp - 224) with (bv_unsigned sp + -224) by lia; replace (thr + 3169) with (thr + 3168 + 1) by lia; exact MU).
      all: try assumption.
      all: decide_depth2; split; eassumption.
Unshelve. all: try exact (@nil byte).
Qed.

End CEIL.
