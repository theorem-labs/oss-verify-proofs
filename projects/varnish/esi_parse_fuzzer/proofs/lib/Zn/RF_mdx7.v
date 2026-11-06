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
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode Arr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require MRepAux MRepAux RF_egfy MTree Mallwlb.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mall5lv.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_egfy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallwlb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall5lv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RF_mx3o.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RF_mx3o.

Module RF_m8qy.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode Arr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require MRepAux MRepAux RF_egfy MTree Mallwlb.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_egfy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallwlb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3.Mallm24.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RF_mx3o.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RF_mx3o RF_m8yt.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_mx3o.RF_mcaj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_mx3o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_m8yt.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require MRep MRepAux MTree W_ge3a6 Mallkgx Mall1es.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RF_mx3o.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RAlllfc RF_m8yt RF_mx3o.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.W_ge3a6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall1es OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_mx3o.RF_mcaj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RAlllfc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_m8yt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_mx3o.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import F_sy88u MRep MRepAux RAlllfc Malllim.
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
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)

Ltac shw := match goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC" pc; idtac "REGS" R end.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition coarse_sc (st : mstate) (sc : Z) : Z :=
  match active st sc with
  | Some _ => sc
  | None =>
    if (4 <=? sc) && (sc <? 32) && negb (sc =? 6) && Z.even sc && (usage st sc =? 0) then
      let usage1 := usage st (Z.lor sc 1) in
      let usage1 := match active st (Z.lor sc 1) with
                    | None => usage1 + 3
                    | Some _ => let ar := get_meta_rec st (default (0%N,-1) (active st (Z.lor sc 1))) in
                                if (m_avail ar =? 0) && (m_freed ar =? 0) then usage1 + 3 else usage1
                    end in
      if usage1 <=? 12 then Z.lor sc 1 else sc
    else sc
  end.
Section CEIL.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Lemma malloc_small_ctrl_eq {R} lay st n (k : mstate -> option (aptr * Z) -> Malloc.M R) bail :
  malloc_small_ctrl lay st n k bail =
  let sc := coarse_sc st (size_to_class n) in
  let g := active st sc in
  let mask := match g with Some gp => m_avail (get_meta_rec st gp) | None => 0 end in
  let first := lowbit mask in
  match g, negb (first =? 0) with
  | Some gp, true => k (upd_meta gp (m_set_avail (mask - first)) st) (Some (gp, ctz32 first))
  | _, _ =>
    alloc_slot lay FUEL st sc n (fun st1 idx =>
      if idx <? 0 then k st1 None
      else match active st1 sc with
           | Some gp => k st1 (Some (gp, idx))
           | None => SVis (EUndef UBadPtr) (fun _ => bail)
           end) bail
  end.
Proof. reflexivity. Qed.

End CEIL.
Lemma usages_nth : forall st sc, 0 <= sc < 48 -> nth_error (usages st) (Z.to_nat sc) = Some (wz (usage st sc)).
Proof.
  intros st sc Hsc. unfold usages. rewrite nth_error_map, nth_error_seq.
  replace (Z.to_nat sc <? 48)%nat with true by (symmetry; apply Nat.ltb_lt; lia). cbn. rewrite Z2Nat.id by lia. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma land_ones64 y : Z.land y 18446744073709551615 = y mod 2^64.
Proof. change 18446744073709551615 with (Z.ones 64). apply Z.land_ones. lia. Qed.
Lemma land_1_even x : (Z.land x 1 = 0) <-> Z.even x = true.
Proof.
  change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. change (2^1) with 2.
  rewrite Z.even_spec. split.
  - intros H. exists (x / 2). lia.
  - intros [k ->]. rewrite Z.mul_comm, Z_mod_mult. reflexivity.
Qed.
Definition lor1_check : bool :=
  forallb (fun sc => negb ((4 <=? sc) && (sc <? 32) && Z.even sc) || (size_class sc <=? size_class (Z.lor sc 1))) (zseq 0 48).
Lemma lor1_check_true : lor1_check = true.
Proof. vm_compute. reflexivity. Qed.
Lemma size_class_lor1 sc : 4 <= sc < 32 -> Z.even sc = true -> size_class sc <= size_class (Z.lor sc 1).
Proof.
  intros H E. pose proof (forallb_zseq _ 0 48 sc lor1_check_true ltac:(lia) ltac:(lia)) as X. cbv beta in X.
  replace (4 <=? sc) with true in X by (symmetry; apply Z.leb_le; lia).
  replace (sc <? 32) with true in X by (symmetry; apply Z.ltb_lt; lia). rewrite E in X. cbn [andb negb orb] in X.
  apply Z.leb_le. exact X.
Qed.
Definition lor1_range_check : bool := forallb (fun sc => (0 <=? Z.lor sc 1) && (Z.lor sc 1 <? 48)) (zseq 0 48).
Lemma lor1_range_check_true : lor1_range_check = true.
Proof. vm_compute. reflexivity. Qed.
Lemma lor1_range sc : 0 <= sc < 48 -> 0 <= Z.lor sc 1 < 48.
Proof.
  intros H. pose proof (forallb_zseq _ 0 48 sc lor1_range_check_true ltac:(lia) ltac:(lia)) as X. cbv beta in X.
  apply andb_prop in X. destruct X as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2. lia.
Qed.
Definition lor1_ge_check : bool := forallb (fun sc => sc <=? Z.lor sc 1) (zseq 0 48).
Lemma lor1_ge_check_true : lor1_ge_check = true.
Proof. vm_compute. reflexivity. Qed.
Lemma lor1_ge sc : 0 <= sc < 48 -> sc <= Z.lor sc 1.
Proof.
  intros H. pose proof (forallb_zseq _ 0 48 sc lor1_ge_check_true ltac:(lia) ltac:(lia)) as X. cbv beta in X.
  apply Z.leb_le in X. exact X.
Qed.
Lemma coarse_sc_cases st sc : 0 <= sc < 48 ->
  coarse_sc st sc = sc \/ (coarse_sc st sc = Z.lor sc 1 /\ 4 <= sc < 32 /\ Z.even sc = true).
Proof.
  intros H. unfold coarse_sc. destruct (active st sc); [left; reflexivity|].
  destruct ((4 <=? sc) && (sc <? 32) && negb (sc =? 6) && Z.even sc && (usage st sc =? 0)) eqn:E; [|left; reflexivity].
  apply andb_prop in E. destruct E as [E E5]. apply andb_prop in E. destruct E as [E E4].
  apply andb_prop in E. destruct E as [E E3]. apply andb_prop in E. destruct E as [E1 E2].
  apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  cbv zeta. destruct (_ <=? 12); [right|left]; auto.
Qed.
Definition coarse_post (sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (st : mstate) (n sc' : Z) : machine_state -> Prop :=
  fun ms' => exists a0 a1 a2 a3,
    ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 MLOCK) a0 a1 a2 a3 a4 a5 a6 a7
                  (pw st (active st sc')) (Z_to_bv 64 DEBRUIJN) (Z_to_bv 64 sc') s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x23fbc) fc None m (seg_rom rsegs)
    /\ a0 = wz (sxv (match active st sc' with Some g => m_avail (get_meta_rec st g) | None => 0 end)).

Section COARSE.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Variables (st : mstate) (LB : list block) (m1 : mem) (t : N).
Let st1 := set_tick t st.
Hypothesis MF : MFACTS st LB.
Hypothesis MR : mrep st1 m1.
Hypothesis MI : mem_inv rsegs m1.

#[using="MR MF m1 LB Rr"] Lemma active_ptr_facts sc g : active st sc = Some g -> 0 < conc st1 g /\ conc st1 g + 40 <= alloc_ceiling /\ meta_slot st1 g
  /\ (exists b, m_mem (get_meta_rec st g) = Some b)
  /\ 0 <= m_avail (get_meta_rec st g) < 2^32 /\ 0 <= m_freed (get_meta_rec st g) < 2^32
  /\ 0 <= m_last_idx (get_meta_rec st g) + 32 * m_freeable (get_meta_rec st g) + 64 * m_sizeclass (get_meta_rec st g) + 4096 * m_maplen (get_meta_rec st g) < 2^64.
Proof.
  intros ACT.
  pose proof (mf_active _ _ MF) as FA. change (fact_active (strip st)) with (fact_active st) in FA.
  (first [ pose proof ((FA sc g ACT)) as dR_1; dand3 dR_1 as SC48 GSC NN | destruct (FA sc g ACT) as (SC48 & GSC & NN) ]).
  destruct (m_mem (get_meta_rec st g)) as [b|] eqn:Hm; [|congruence].
  pose proof (mf_gmeta _ _ MF) as FG. change (fact_gmeta (strip st)) with (fact_gmeta st) in FG.
  specialize (FG g b Hm). cbv zeta in FG. (first [ dand8 FG as MSL AV FR LI FB SC ML _ | destruct FG as (MSL & AV & FR & LI & FB & SC & ML & _) ]).
  (first [ pose proof ((meta_chunk_facts st1 m1 g MR MSL)) as dR_3; dand4 dR_3 as _ G0 GC _ | pose proof (meta_chunk_facts st1 m1 g MR MSL) as (_ & G0 & GC & _) ]).
  split; [exact G0|]. split; [exact GC|]. split; [exact MSL|]. split; [exists b; reflexivity|]. split; [exact AV|]. split; [exact FR|].
  pose proof (mf_maplen _ _ MF g b Hm) as MP. change (get_meta_rec (strip st) g) with (get_meta_rec st g) in MP. lia.
Qed.

Ltac fin_coarse := apply evt_done; unfold coarse_post; do 4 eexists; split; [reflexivity|].

#[using="MR MF LB Rr Clg"] Lemma coarse_walk : forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' : word) F fc (n sc : Z),
  0 <= sc < 48 -> (sc < 32 -> 0 <= Z.lor sc 1 < 48) ->
  evt rsegs (coarse_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' F fc m1 st1 n (coarse_sc st sc))
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 MLOCK) a0 a1 a2 a3 a4 a5 a6 a7
               s2 (Z_to_bv 64 DEBRUIJN) (Z_to_bv 64 sc) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x23f00) fc None m1 (seg_rom rsegs)).
Proof.
  intros until sc. intros SC48 SC1.
  pose proof MR as (WF & (CXH & CXA & CXU & _) & (ML & NL & _) & _).
  pose proof (mf_usage _ _ MF) as FU. change (fact_usage (strip st)) with (fact_usage st) in FU.
  unfold NEED_LOCKS, CTX, MLOCK, DEBRUIJN in *. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
  (* [comment removed for export] *)
  step. rewrite sextw_small by lia. step. rewrite (unsigned_lit sc), Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. step.
  pose proof (actives_nth st1 sc ltac:(lia)) as NTH. change (active st1 sc) with (active st sc) in NTH.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    pose proof (u64arr_read rsegs mc _ (actives st1) sc _ (wa (403456 + 80 + 8 * sc)) CXA NTH ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end.
  step.
  (* [comment removed for export] *)
  assert (J40 : forall (a0' a1' a2' a3' : word) (sc' : Z), 0 <= sc' < 48 ->
    evt rsegs (coarse_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' F fc m1 st1 n sc')
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 403448) a0' a1' a2' a3' a4 a5 a6 a7
               (pw st1 (active st sc')) (Z_to_bv 64 85128) (Z_to_bv 64 sc') s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x23fac) fc None m1 (seg_rom rsegs))).
  { intros a0' a1' a2' a3' sc' SC'.
    destruct (active st sc') as [g|] eqn:ACT'.
    - (first [ pose proof ((active_ptr_facts sc' g ACT')) as dR_4; dand7 dR_4 as G0 GC MSL _ AV FR MW | destruct (active_ptr_facts sc' g ACT') as (G0 & GC & MSL & _ & AV & FR & MW) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
      pose proof (meta_chunk_facts st1 m1 g MR MSL) as (MM & _).
      change (get_meta_rec st1 g) with (get_meta_rec st g) in MM. unfold meta_cells, meta_word in MM.
      unfold pw. cbn [oconc]. set (gw := wz (conc st1 g)) in *.
      assert (HG : bv_unsigned gw = conc st1 g) by (subst gw; apply wz_unsigned; lia).
      rewrite <- HG in MM.
      step. if_cases K; zify_cond K. { exfalso. rewrite HG in K. lia. }
      step. rewrite (sx32_wz_sxv (m_avail (get_meta_rec st g))) by lia. step.
      apply evt_done. unfold coarse_post. change (active st1 sc') with (active st sc'). rewrite ACT'. do 4 eexists. split; [subst gw; reflexivity| reflexivity].
    - unfold pw. cbn [oconc].
      step. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K by lia. lia. }
      step.
      apply evt_done. unfold coarse_post. change (active st1 sc') with (active st sc'). rewrite ACT'. do 4 eexists. split; [reflexivity| reflexivity]. }
  (* [comment removed for export] *)
  assert (J4c : forall (a0' a1' a2' a3' : word) (sc' : Z), active st sc' = None ->
    evt rsegs (coarse_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' F fc m1 st1 n sc')
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 403448) a0' a1' a2' a3' a4 a5 a6 a7
               (Z_to_bv 64 0) (Z_to_bv 64 85128) (Z_to_bv 64 sc') s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x23fb8) fc None m1 (seg_rom rsegs))).
  { intros a0' a1' a2' a3' sc' ACT'. step.
    apply evt_done. unfold coarse_post. change (active st1 sc') with (active st sc'). rewrite ACT'. do 4 eexists. split; [reflexivity| reflexivity]. }
  (* [comment removed for export] *)
  assert (J2c : forall (a1' a2' a3' s4' : word) (sc' : Z), 0 <= sc' < 48 ->
    evt rsegs (coarse_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' F fc m1 st1 n sc')
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 403448) (Z_to_bv 64 sc') a1' a2' a3' a4 a5 a6 a7
               (Z_to_bv 64 0) (Z_to_bv 64 85128) s4' s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x23f98) fc None m1 (seg_rom rsegs))).
  { intros a1' a2' a3' s4' sc' SC'.
    step. rewrite sextw_small by lia. step. rewrite (unsigned_lit sc'), Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. step.
    pose proof (actives_nth st1 sc' ltac:(lia)) as NTH'. change (active st1 sc') with (active st sc') in NTH'.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      pose proof (u64arr_read rsegs mc _ (actives st1) sc' _ (wa (403456 + 80 + 8 * sc')) CXA NTH' ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD' end.
    step. step. apply J40. exact SC'. }
  (* [comment removed for export] *)
  step.
  destruct (active st sc) as [g|] eqn:ACT.
  - (* [comment removed for export] *)
    (first [ pose proof ((active_ptr_facts sc g ACT)) as dR_5; dand3 dR_5 as G0 GC _ | destruct (active_ptr_facts sc g ACT) as (G0 & GC & _) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
    unfold pw. cbn [oconc].
    if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia. lia. }
    clear K1.
    replace (coarse_sc st sc) with sc by (unfold coarse_sc; rewrite ACT; reflexivity).
    change (wz (conc st1 g)) with (pw st1 (Some g)). rewrite <- ACT. apply J40. exact SC48.
  - (* [comment removed for export] *)
    unfold pw. cbn [oconc].
    if_cases K1; zify_cond K1. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia. lia. }
    clear K1.
    assert (CS : forall b : bool, (4 <=? sc) && (sc <? 32) && negb (sc =? 6) && Z.even sc && (usage st sc =? 0) = b ->
              coarse_sc st sc = if b then
                (let usage1 := usage st (Z.lor sc 1) in
                 let usage1 := match active st (Z.lor sc 1) with
                    | None => usage1 + 3
                    | Some _ => let ar := get_meta_rec st (default (0%N,-1) (active st (Z.lor sc 1))) in
                                if (m_avail ar =? 0) && (m_freed ar =? 0) then usage1 + 3 else usage1
                    end in
                 if usage1 <=? 12 then Z.lor sc 1 else sc) else sc).
    { intros b Hb. unfold coarse_sc. rewrite ACT, Hb. reflexivity. }
    (* [comment removed for export] *)
    step. step. if_cases K2; zify_cond K2; rewrite ?(unsigned_lit sc) in K2 by lia.
    + (* [comment removed for export] *)
      rewrite (CS false) by (subst sc; reflexivity).
      change (wz 0) with (pw st1 None). rewrite <- ACT. apply J40. exact SC48.
    + (* [comment removed for export] *)
      step. step. step. if_cases K3; zify_cond K3; rewrite (swrap32_small (sc + -4)), ?land_ones64 in K3 by lia.
      * (* [comment removed for export] *)
        rewrite (CS false). 2:{ destruct (Z.lt_ge_cases sc 4); [replace (4 <=? sc) with false by (symmetry; apply Z.leb_gt; lia); reflexivity|].
             replace (sc <? 32) with false by (symmetry; apply Z.ltb_ge; Z.div_mod_to_equations; lia). destruct (4 <=? sc); reflexivity. }
        change (wz 0) with (pw st1 None). rewrite <- ACT. apply J40. exact SC48.
      * assert (SC432 : 4 <= sc < 32) by (Z.div_mod_to_equations; lia). clear K3. rename K2 into NE6.
        (* [comment removed for export] *)
        step. step. if_cases K4; zify_cond K4; rewrite ?(unsigned_lit sc) in K4 by lia.
        -- (* [comment removed for export] *)
           rewrite (CS false).
           2:{ replace (4 <=? sc) with true by (symmetry; apply Z.leb_le; lia). replace (sc <? 32) with true by (symmetry; apply Z.ltb_lt; lia).
               replace (sc =? 6) with false by (symmetry; apply Z.eqb_neq; lia).
               destruct (Z.even sc) eqn:EV; [|reflexivity]. exfalso. apply K4. apply (proj2 (land_1_even sc)). exact EV. }
           step. step. apply J4c. exact ACT.
        -- pose proof (proj1 (land_1_even sc) K4) as EV.
           (* [comment removed for export] *)
           pose proof (usages_nth st1 sc ltac:(lia)) as NTHU. change (usage st1 sc) with (usage st sc) in NTHU.
           lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
             pose proof (u64arr_read rsegs mc _ (usages st1) sc _ (wa (403456 + 464 + 8 * sc)) CXU NTHU ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RDU end.
           step. pose proof (FU sc) as FUsc.
           step. if_cases K6; zify_cond K6; rewrite ?wz_unsigned in K6 by lia.
           ** (* [comment removed for export] *)
              assert (COND : (4 <=? sc) && (sc <? 32) && negb (sc =? 6) && Z.even sc && (usage st sc =? 0) = true).
              { replace (4 <=? sc) with true by (symmetry; apply Z.leb_le; lia).
                replace (sc <? 32) with true by (symmetry; apply Z.ltb_lt; lia).
                replace (sc =? 6) with false by (symmetry; apply Z.eqb_neq; lia).
                rewrite EV. replace (usage st sc =? 0) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity. }
              specialize (SC1 ltac:(lia)). set (sc1 := Z.lor sc 1) in *.
              (* [comment removed for export] *)
              step. rewrite (unsigned_lit sc) by lia. fold sc1.
              step. rewrite sextw_small by lia. step. rewrite (unsigned_lit sc1), Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. step.
              pose proof (actives_nth st1 sc1 ltac:(lia)) as NTH1. change (active st1 sc1) with (active st sc1) in NTH1.
              lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
                pose proof (u64arr_read rsegs mc _ (actives st1) sc1 _ (wa (403456 + 80 + 8 * sc1)) CXA NTH1 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD1 end.
              step.
              pose proof (usages_nth st1 sc1 ltac:(lia)) as NTHU1. change (usage st1 sc1) with (usage st sc1) in NTHU1.
              lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
                pose proof (u64arr_read rsegs mc _ (usages st1) sc1 _ (wa (403456 + 464 + 8 * sc1)) CXU NTHU1 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RDU1 end.
              step. pose proof (FU sc1) as FU1.
              (* [comment removed for export] *)
              set (u1 := match active st sc1 with
                         | None => usage st sc1 + 3
                         | Some _ => let ar := get_meta_rec st (default (0%N,-1) (active st sc1)) in
                                     if (m_avail ar =? 0) && (m_freed ar =? 0) then usage st sc1 + 3 else usage st sc1 end).
              assert (U1 : 0 <= u1 < 2^61).
              { unfold u1. destruct (active st sc1); [match goal with |- context [if ?c then _ else _] => destruct c end|]; lia. }
              assert (CS1 : coarse_sc st sc = if u1 <=? 12 then sc1 else sc).
              { rewrite (CS true COND). reflexivity. }
              clear CS.
              assert (J20 : forall (a2' a3' : word),
                evt rsegs (coarse_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' F fc m1 st1 n (coarse_sc st sc))
                  (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 403448) (Z_to_bv 64 sc1) (wz u1) a2' a3' a4 a5 a6 a7
                           (Z_to_bv 64 0) (Z_to_bv 64 85128) (Z_to_bv 64 sc) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x23f8c) fc None m1 (seg_rom rsegs))).
              { intros a2' a3'. step. step. if_cases K9; zify_cond K9; rewrite ?wz_unsigned, ?unsigned_lit in K9 by lia.
                - (* [comment removed for export] *)
                  rewrite CS1. replace (u1 <=? 12) with true by (symmetry; apply Z.leb_le; lia). apply J2c. exact SC1.
                - (* [comment removed for export] *)
                  step. rewrite CS1. replace (u1 <=? 12) with false by (symmetry; apply Z.leb_gt; lia). apply J2c. exact SC48. }
              change (Z_to_bv 64 0) with (wz 0).
              destruct (active st sc1) as [g1|] eqn:ACT1.
              +++ (* [comment removed for export] *)
                  (first [ pose proof ((active_ptr_facts sc1 g1 ACT1)) as dR_6; dand7 dR_6 as G10 G1C MSL1 _ AV1 FR1 MW1 | destruct (active_ptr_facts sc1 g1 ACT1) as (G10 & G1C & MSL1 & _ & AV1 & FR1 & MW1) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
                  pose proof (meta_chunk_facts st1 m1 g1 MR MSL1) as (MM1 & _).
                  change (get_meta_rec st1 g1) with (get_meta_rec st g1) in MM1. unfold meta_cells, meta_word in MM1.
                  unfold pw. cbn [oconc]. set (gw := wz (conc st1 g1)) in *.
                  assert (HG : bv_unsigned gw = conc st1 g1) by (subst gw; apply wz_unsigned; lia).
                  rewrite <- HG in MM1.
                  step. if_cases K7; zify_cond K7. { exfalso. rewrite HG in K7. lia. } clear K7.
                  cbn [default from_option id] in u1.
                  (* [comment removed for export] *)
                  step. rewrite (sx32_wz_sxv (m_avail (get_meta_rec st g1))) by lia.
                  pose proof (sxv_range (m_avail (get_meta_rec st g1))) as RA1.
                  step. if_cases K8; zify_cond K8; rewrite ?wz_unsigned in K8 by lia.
                  *** (* [comment removed for export] *)
                      assert (NA : m_avail (get_meta_rec st g1) <> 0) by (intros E; rewrite E in K8; apply K8; reflexivity).
                      replace (wz (usage st sc1)) with (wz u1).
                      2:{ unfold u1. replace (m_avail (get_meta_rec st g1) =? 0) with false by (symmetry; apply Z.eqb_neq; exact NA). reflexivity. }
                      apply J20.
                  *** apply (proj1 (sxv_zero (m_avail (get_meta_rec st g1)) ltac:(lia))) in K8.
                      (* [comment removed for export] *)
                      step. rewrite (sx32_wz_sxv (m_freed (get_meta_rec st g1))) by lia.
                      pose proof (sxv_range (m_freed (get_meta_rec st g1))) as RF1.
                      step. if_cases K9; zify_cond K9; rewrite ?wz_unsigned in K9 by lia.
                      ---- assert (NF : m_freed (get_meta_rec st g1) <> 0) by (intros E; rewrite E in K9; apply K9; reflexivity).
                           replace (wz (usage st sc1)) with (wz u1).
                           2:{ unfold u1. rewrite K8. replace (m_freed (get_meta_rec st g1) =? 0) with false by (symmetry; apply Z.eqb_neq; exact NF). reflexivity. }
                           apply J20.
                      ---- apply (proj1 (sxv_zero (m_freed (get_meta_rec st g1)) ltac:(lia))) in K9.
                           (* [comment removed for export] *)
                           step. rewrite (wz_unsigned (usage st sc1)) by lia.
                           replace (Z_to_bv 64 (usage st sc1 + 3)) with (wz u1).
                           2:{ unfold u1. rewrite K8, K9. reflexivity. }
                           apply J20.
              +++ (* [comment removed for export] *)
                  unfold pw. cbn [oconc].
                  step. if_cases K7; zify_cond K7. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K7 by lia. lia. } clear K7.
                  step. rewrite (wz_unsigned (usage st sc1)) by lia.
                  replace (Z_to_bv 64 (usage st sc1 + 3)) with (wz u1) by reflexivity.
                  apply J20.
           ** (* [comment removed for export] *)
              rewrite (CS false).
              2:{ replace (4 <=? sc) with true by (symmetry; apply Z.leb_le; lia). replace (sc <? 32) with true by (symmetry; apply Z.ltb_lt; lia).
                  replace (sc =? 6) with false by (symmetry; apply Z.eqb_neq; lia). rewrite EV.
                  replace (usage st sc =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
              step. step. apply J4c. exact ACT.
Qed.
End COARSE.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac mem_after_store ::=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
    let c' := cell_of_bytes bs in
    let n := eval cbv in (csize c') in
    lazymatch goal with
    | H : rw_cells segs m A ?cs0 |- _ =>
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          let HB := fresh "HB" in
          pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
          try lazymatch goal with
          | HI : mem_inv segs m |- _ =>
              apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
              [ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
          end;
          change bs with (cbytes c');
          let H' := fresh "CH" in
          pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
          clear H;
          cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
          transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
          footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
          let m' := fresh "m" in
          let E := fresh "EQ" m' in
          remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:E;
          clear HB; try rename H' into H
        end
    end
  end.

(* [comment removed for export] *)
Lemma mul_srliw27_sxv k : 0 <= k < 32 ->
  bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (Z_to_bv 64 (bv_unsigned (wz (sxv (2 ^ k))) * rDB32)))) 27) = rdbi k.
Proof.
  intros Hk. unfold rdbi. rewrite (wz_unsigned (sxv (2 ^ k))) by apply sxv_range.
  rewrite unsigned_lit_wrap. change (bv_wrap 32 ((sxv (2 ^ k) * rDB32) mod 2 ^ 64)) with (((sxv (2 ^ k) * rDB32) mod 2^64) mod 2^32).
  rewrite (mod_mod_pow2 _ 32 64) by lia. rewrite <- Z.mul_mod_idemp_l, sxv_mod32, Z.mul_mod_idemp_l by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.mod_pos_bound (2 ^ k * rDB32) (2^32) ltac:(lia)).
  apply swrap32_small. Z.div_mod_to_equations. nia.
Qed.

Definition rfc_post (sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' nw gw s4v : word) (F : bvmap 5 word) (fc : bv 32)
   (m : word -> option byte) (G avail k : Z) (prev next memw : word) (freed mword : Z) : machine_state -> Prop :=
  fun ms' => exists a0 a1 a2 a3 m3,
    ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 MLOCK) a0 a1 a2 a3 a4 a5 a6 a7
                  gw (wz k) s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x24018) fc None m3 (seg_rom rsegs)
    /\ m3 = write_to_mem m (wa (G + 24)) (le4 (wz (avail - 2 ^ k)))
    /\ munch [(G + 24, G + 28)]%Z m m3 /\ wmono rsegs m m3 /\ mem_inv rsegs m3
    /\ rw_cells rsegs m3 (bv_unsigned gw) [C8 prev; C8 next; C8 memw; C4 (wz (avail - 2 ^ k)); C4 (wz freed); C8 (wz mword)].

(* [comment removed for export] *)
Lemma rfast_walk : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw gw prev next memw : word) F fc m
    (G avail k freed mword : Z),
  bv_unsigned gw = G ->
  rw_cells rsegs m (bv_unsigned gw) [C8 prev; C8 next; C8 memw; C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
  mem_inv rsegs m -> (G + 40 <= 0x10000 \/ 0x64000 <= G) ->
  0 < avail < 2^32 -> 0 <= freed < 2^32 -> 0 <= mword < 2^64 ->
  0 <= k < 32 -> lowbit avail = 2 ^ k ->
  evt rsegs (rfc_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' nw gw s4v F fc m G avail k prev next memw freed mword)
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 MLOCK) (wz (sxv avail)) a1 a2 a3 a4 a5 a6 a7
               gw (Z_to_bv 64 DEBRUIJN) s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x23fbc) fc None m (seg_rom rsegs)).
Proof.
  intros until mword. intros HG MM MI GRES AV FRr MW HK LB.
  pose proof (munch_refl [(G + 24, G + 28)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ gw) as GWR. change (bv_modulus 64) with (2^64) in GWR.
  unfold MLOCK, DEBRUIJN in *.
  assert (P2 : 0 < 2 ^ k <= avail).
  { (first [ pose proof ((lowbit_nonzero avail ltac:(lia))) as dR_7; dex1 dR_7 as k'; dand3 dR_7 as Hk' E L | pose proof ((lowbit_nonzero avail ltac:(lia))) as dR_7; dand4 dR_7 as k' Hk' E L | destruct (lowbit_nonzero avail ltac:(lia)) as (k' & Hk' & E & L) ]). rewrite LB in E.
    apply Z.pow_inj_r in E; [|lia|lia|lia]. subst k'. split; [apply Z.pow_pos_nonneg; lia| exact L]. }
  assert (P32 : 2 ^ k < 2 ^ 32) by (apply Z.pow_lt_mono_r; lia).
  pose proof (sxv_range avail) as RA. pose proof (sxv_range (2 ^ k)) as RK.
  (* [comment removed for export] *)
  step. step. rewrite (Z.land_comm (bv_unsigned (wz (sxv avail)))). rewrite (negw_and_lowbit avail) by lia. rewrite LB.
  (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0.
  { exfalso. rewrite ?wz_unsigned in K0 by assumption. pose proof (proj1 (sxv_zero (2 ^ k) ltac:(lia)) K0). lia. }
  clear K0.
  (* [comment removed for export] *)
  step. step. step. rewrite (Z.land_comm (bv_unsigned (wz (sxv avail)))). rewrite (negw_and_lowbit avail) by lia. rewrite LB.
  step. step. change 125613361 with rDB32.
  step. rewrite (mul_srliw27_sxv k) by lia.
  pose proof (rdbi_range k) as DR.
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit (rdbi k)) by lia.
  lazymatch goal with HI : mem_inv rsegs ?mc |- _ => pose proof (rdebruijn_read mc k HI ltac:(lia)) as DBR; unfold DEBRUIJN in DBR end.
  step. rewrite ?zxb_b8 by lia. clear DBR.
  (* [comment removed for export] *)
  step. rewrite (wz_unsigned (sxv avail)), (wz_unsigned (sxv (2 ^ k))) by assumption.
  rewrite (swrap_word (sxv avail - sxv (2 ^ k))).
  (* [comment removed for export] *)
  step.
  lazymatch goal with H : rw_cells rsegs ?mc (bv_unsigned gw) ?cs |- evt _ _ (MS _ _ _ _ _ ?mc' _) =>
    apply (rw_cells_congr rsegs mc (bv_unsigned gw) cs
             [C8 prev; C8 next; C8 memw; C4 (wz (avail - 2 ^ k)); C4 (wz freed); C8 (wz mword)]) in H;
    [| cbn [cells_bytes cbytes]; rewrite (le4_avail_sub avail (2 ^ k)) by lia; reflexivity | reflexivity | cbn; tauto ]
  end.
  (* [comment removed for export] *)
  step.
  apply evt_done. unfold rfc_post.
  do 4 eexists.
  lazymatch goal with E : ?mx = write_to_mem m _ _ |- _ => exists mx end.
  split; [reflexivity|].
  split. { lazymatch goal with E : ?mx = write_to_mem m _ _ |- _ => rewrite E end.
           f_equal; [unfold wa; f_equal; lia | cbn [cbytes]; apply le4_avail_sub; lia]. }
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. assumption.
Qed.

(* [comment removed for export] *)
Ltac mem_after_store ::=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
    let c' := cell_of_bytes bs in
    let n := eval cbv in (csize c') in
    lazymatch goal with
    | H : rw_cells segs m A ?cs0 |- _ =>
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          let HB := fresh "HB" in
          pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
          try lazymatch goal with
          | HI : mem_inv segs m |- _ =>
              apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
              [ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
          end;
          change bs with (cbytes c');
          let H' := fresh "CH" in
          pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
          clear H;
          cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
          transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
          footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
          let m' := fresh "m" in
          remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
          clear Heqm; clear HB; try clear m; try rename H' into H
        end
    end
  end.

(* [comment removed for export] *)
Lemma core0_walk : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw : word) F fc (m : mem),
  evt rsegs (fun ms' => exists a1', ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 MLOCK) (wz (sxv 0)) a1' a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x23ff4) fc None m (seg_rom rsegs))
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 MLOCK) (wz (sxv 0)) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x23fbc) fc None m (seg_rom rsegs)).
Proof.
  intros.
  step. step. rewrite (Z.land_comm (bv_unsigned (wz (sxv 0)))). rewrite (negw_and_lowbit 0) by lia. rewrite lowbit_0.
  step. if_cases KZ; zify_cond KZ. 2:{ exfalso. apply KZ. reflexivity. }
  apply evt_done. eexists. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)


Section FASTCORE.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Context {R : Type}.
Variables (K : mstate -> option (aptr * Z) -> Malloc.M R) (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
          (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N).
Hypothesis HENF : enf_hyp K o m0 st s Q ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo.
Hypothesis MF : MFACTS st LB.
Hypothesis TP : tp = Z_to_bv 64 PTP.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 48.
Hypothesis N0 : 0 <= n.
Hypothesis NT : n < MMAP_THRESHOLD.
Hypothesis BL : brk_link_ps st s.

Let st1 := set_tick t st.

#[using="BL NT N0 LO CLO TP MF HENF LB"] Lemma rfast_core_implT :
  forall (m1 : mem) (errv : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 ra' : word) (sc : Z) (g : aptr),
  let mr := get_meta_rec st g in
  let mask := m_avail mr in
  let first := lowbit mask in
  mrep st1 m1 -> ticks_ok st1 -> unk_agree st1 o m1 -> mem_inv rsegs m1 ->
  stk rsegs m1 lo (bv_unsigned sp + -48) ->
  rw_cells rsegs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
  rw_cells rsegs m1 (errno_addr tp) [C4 errv] -> auxv_okd (c_init_done (ctx st)) m1 (bv_unsigned sp) ->
  pres_except (malloc_fp st st1 lo (bv_unsigned sp)) m0 m1 ->
  active st sc = Some g -> 0 < mask -> n + 4 <= 16 * size_class sc -> 0 <= sc <= Z.lor (size_to_class n) 1 ->
  implT o (K (upd_meta g (m_set_avail (mask - first)) st1) (Some (g, ctz32 first))) s Q
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 MLOCK) (wz (sxv mask)) a1 a2 a3 a4 a5 a6 a7
                 (pw st1 (Some g)) (Z_to_bv 64 DEBRUIJN) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x23fbc) fc None m1 (seg_rom rsegs)).
Proof.
  intros until g. intros mr mask first MR TK UA MI ST FR ERR AUX PE ACT AV NFIT SCLE.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
  (* [comment removed for export] *)
  pose proof (mf_active _ _ MF) as FA. change (fact_active (strip st)) with (fact_active st) in FA.
  (first [ pose proof ((FA sc g ACT)) as dR_8; dand3 dR_8 as SC48 GSC _ | destruct (FA sc g ACT) as (SC48 & GSC & _) ]). change (get_meta_rec st g) with mr in GSC.
  pose proof (mf_gmeta _ _ MF) as FG0.
  assert (AVr : 0 <= mask < 2^32 /\ 0 <= m_freed mr < 2^32 /\ 0 <= m_last_idx mr < 32 /\ 0 <= m_freeable mr < 2 /\ 0 <= m_sizeclass mr < 64 /\ 0 <= m_maplen mr < 2^19).
  { change (fact_gmeta (strip st)) with (fact_gmeta st) in FG0.
    destruct (m_mem mr) as [b|] eqn:Hm.
    - specialize (FG0 g b Hm). change (get_meta_rec st g) with mr in FG0. cbv zeta in FG0.
      (first [ dand8 FG0 as _ A1 A2 A3 A4 A5 A6 _ | destruct FG0 as (_ & A1 & A2 & A3 & A4 & A5 & A6 & _) ]). subst mask. clear - A1 A2 A3 A4 A5 A6 GSC SC48. lia.
    - exfalso. (first [ pose proof ((FA sc g ACT)) as dR_10; dand3 dR_10 as _ _ NN | destruct (FA sc g ACT) as (_ & _ & NN) ]). apply NN. exact Hm. }
  (first [ dand6 AVr as AVr FRr LIr FBr SCr MPr | destruct AVr as (AVr & FRr & LIr & FBr & SCr & MPr) ]).
  (first [ pose proof ((lowbit_facts mask ltac:(lia))) as dR_12; dex1 dR_12 as k; destruct dR_12 as [K32 LBK] | pose proof ((lowbit_facts mask ltac:(lia))) as dR_12; dand3 dR_12 as k K32 LBK | destruct (lowbit_facts mask ltac:(lia)) as (k & K32 & LBK) ]). fold first in LBK.
  assert (P2k : 0 < 2 ^ k <= mask).
  { split; [apply Z.pow_pos_nonneg; lia|]. (first [ pose proof ((lowbit_pow2 mask AV)) as dR_13; dex1 dR_13 as k'; dand3 dR_13 as _ E' LE' | pose proof ((lowbit_pow2 mask AV)) as dR_13; dand4 dR_13 as k' _ E' LE' | destruct (lowbit_pow2 mask AV) as (k' & _ & E' & LE') ]). unfold first, lowbit in LBK.
    rewrite LBK in E'. rewrite E'. exact LE'. }
  (first [ pose proof ((fast_slot_ok st LB sc n g k t MF ACT AV ltac:(lia) LBK N0 NFIT)) as dR_14; dex2 dR_14 as b r; dand5 dR_14 as SO SPANFP _ Hmem Hr | pose proof ((fast_slot_ok st LB sc n g k t MF ACT AV ltac:(lia) LBK N0 NFIT)) as dR_14; dand7 dR_14 as b r SO SPANFP _ Hmem Hr | destruct (fast_slot_ok st LB sc n g k t MF ACT AV ltac:(lia) LBK N0 NFIT) as (b & r & SO & SPANFP & _ & Hmem & Hr) ]).
  fold mr st1 in SO. change (get_meta_rec st g) with mr in Hmem.
  pose proof (mf_ctx _ _ MF) as FC. change (fact_ctx (strip st)) with (fact_ctx st) in FC. (first [ dand4 FC as CTR SEC INI _ | destruct FC as (CTR & SEC & INI & _) ]).
  (* [comment removed for export] *)
  assert (MSL : meta_slot st1 g) by (exact (so_mslot _ _ _ _ _ _ SO)).
  (first [ pose proof ((meta_chunk_facts st1 m1 g MR MSL)) as dR_16; dand7 dR_16 as MM G0 GC GI1 GI2 GDJ (rid0 & r0 & Hr0 & Hk0 & GR0 & GR1) | pose proof (meta_chunk_facts st1 m1 g MR MSL) as (MM & G0 & GC & GI1 & GI2 & GDJ & (rid0 & r0 & Hr0 & Hk0 & GR0 & GR1)) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
  set (G := conc st1 g) in *.
  change (get_meta_rec st1 g) with mr in MM. unfold meta_cells in MM. fold mask in MM. unfold meta_word in MM.
  (* [comment removed for export] *)
  iprefixT.
  eapply evt_mono.
  { eapply (rfast_walk sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' (Z_to_bv 64 n) (pw st1 (Some g))
              (pw st1 (m_prev mr)) (pw st1 (m_next mr)) (pw st1 (m_mem mr)) F fc m1 G mask k (m_freed mr)
              (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)).
    all: lazymatch goal with
         | |- rw_cells _ _ (bv_unsigned (pw _ _)) _ => unfold pw; cbn [oconc]; fold G; rewrite (wz_unsigned G) by lia; exact MM
         | |- mem_inv _ _ => exact MI
         | |- bv_unsigned (pw _ _) = _ => unfold pw; cbn [oconc]; fold G; apply wz_unsigned; lia
         | |- _ => idtac end.
    all: try lia. all: try assumption. }
  intros ms' PO. cbv beta in PO. unfold rfc_post in PO.
  (first [ dex5 PO as v0 v1 v2 v3 m3; dand6 PO as -> E3 MU WM MI' MM' | dand11 PO as v0 v1 v2 v3 m3 -> E3 MU WM MI' MM' | destruct PO as (v0 & v1 & v2 & v3 & m3 & -> & E3 & MU & WM & MI' & MM') ]).
  (* [comment removed for export] *)
  pose proof (ctz32_pow2 k ltac:(lia)) as CTZ.
  replace (ctz32 first) with k by (rewrite LBK; symmetry; exact CTZ).
  replace (mask - first) with (mask - 2 ^ k) by (rewrite LBK; reflexivity).
  set (st2 := upd_meta g (m_set_avail (mask - 2 ^ k)) st1) in *.
  change (pw st1 (Some g)) with (pw st2 (Some g)).
  assert (RB0 : forall rid r1, (s_regions st1) !! rid = Some r1 -> 0 <= r_base r1 /\ r_base r1 + round_up_pg (r_len r1) <= alloc_ceiling).
  { intros rid r1 H1. (first [ pose proof ((rregion_facts st1 m1 rid r1 MR H1)) as dR_18; dand4 dR_18 as X1 _ X2 _ | pose proof (rregion_facts st1 m1 rid r1 MR H1) as (X1 & _ & X2 & _) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). lia. }
  assert (RB : forall rid r1, (s_regions st1) !! rid = Some r1 -> 0 <= r_base r1 /\ r_base r1 + round_up_pg (r_len r1) <= 2^64).
  { intros rid r1 H1. pose proof (RB0 rid r1 H1). lia. }
  eapply (HENF st2 g b r k m3 s errv).
  - (* [comment removed for export] *) rewrite E3. unfold st2. apply mrep_meta_set_avail; [exact MR| exact MSL| lia].
  - apply ticks_ok_upd_meta. exact TK.
  - eapply unk_agree_munch; [| exact MU | |].
    + eapply unk_agree_ext; [exact UA| reflexivity| intros; reflexivity| reflexivity].
    + intros rid r1 H1 K1. change (s_regions st2) with (s_regions st1) in H1.
      pose proof (GDJ rid r1 H1 K1). pose proof (RB0 rid r1 H1). cbn. lia.
    + intros rid r1 H1. exact (RB rid r1 H1).
  - exact MI'.
  - eapply stk_transport; [exact ST| exact MU| exact WM|]. cbn. lia.
  - eapply rw_cells_transport; [exact FR| exact MU| exact WM|]. cbn. lia.
  - eapply rw_cells_transport; [exact ERR| exact MU| exact WM|]. subst tp. unfold PTP. rewrite unsigned_lit by lia. cbn. lia.
  - eapply auxv_okd_frame; [exact AUX| exact MU| exact WM|].
    unfold AUXV_CELL. constructor; [cbn; lia|]. constructor.
  - eapply pres_except_munch_frame; [| exact MU| exact WM|].
    + eapply pres_except_mono; [exact PE|]. intros a Ha. eapply malloc_fp_mono; [|exact Ha].
      intros rid r1 H1. exists r1. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto. lia.
    + intros x Hx NC. cbn. split; [|exact I].
      intros HX. apply NC. left. right. right. right. exists rid0, r0. split; [exact Hr0|]. split; [exact Hk0|]. lia.
  - intros a Ha. right. right. left. apply SPANFP.
    replace (get_stride (get_meta_rec st2 g)) with (get_stride mr) in Ha; [exact Ha|].
    unfold st2. rewrite get_meta_rec_upd_same. reflexivity.
  - exact CTR.
  - exact SO.
  - intros [X|X]; [exfalso; lia|]. exfalso. change (s_regions st1) with (s_regions st) in Hr. rewrite X in Hr. rewrite lookup_empty in Hr. discriminate.
  - right. exists sc. split; [| exact SCLE]. unfold st2. unfold active, ctx, upd_meta, put_meta. cbn. exact ACT.
  - apply mrel_same; reflexivity.
  - exact BL.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.
End FASTCORE.


(* [comment removed for export] *)
(* [comment removed for export] *)


Section ASCALL.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Context {R : Type}.
Variables (K : mstate -> option (aptr * Z) -> Malloc.M R) (bail : Malloc.M R) (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
          (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N).
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : alloc_slot_stmt as_pre as_inv.
Hypothesis HENF : enf_hyp K o m0 st s Q ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo.
Hypothesis HFAIL : fail_hyp K o m0 st s Q ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc lo.
Hypothesis MF : MFACTS st LB.
Hypothesis MR0 : mrep st m0.
Hypothesis TP : tp = Z_to_bv 64 PTP.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 48 - AS_STACK 0.
Hypothesis N0 : 0 <= n < 2^32.
Hypothesis NT : n < MMAP_THRESHOLD.
Hypothesis BL : brk_link_ps st s.

Let st1 := set_tick t st.

#[using="BL NT LO CLO TP MR0 HFAIL HENF RAS as_inv"] Lemma ras_call_implT :
  forall (m1 : mem) (errv : word) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2r t3 t4 t5 t6 ra' : word) (sc : Z),
  as_pre st st1 sc n FUEL ->
  mrep st1 m1 -> ticks_ok st1 -> unk_agree st1 o m1 -> mem_inv rsegs m1 ->
  stk rsegs m1 lo (bv_unsigned sp + -48) ->
  rw_cells rsegs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
  rw_cells rsegs m1 (errno_addr tp) [C4 errv] -> auxv_okd (c_init_done (ctx st)) m1 (bv_unsigned sp) ->
  pres_except (malloc_fp st st1 lo (bv_unsigned sp)) m0 m1 ->
  0 <= sc < 48 -> sc <= Z.lor (size_to_class n) 1 ->
  implT o (alloc_slot full_lay FUEL st1 sc n
             (fun st2 idx => if idx <? 0 then K st2 None
                             else match active st2 sc with
                                  | Some gp => K st2 (Some (gp, idx))
                                  | None => SVis (EUndef UBadPtr) (fun _ => bail)
                                  end) bail) s Q
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 MLOCK) a0 a1 a2 a3 a4 a5 a6 a7
                 s2r (Z_to_bv 64 DEBRUIJN) (Z_to_bv 64 sc) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x23ff4) fc None m1 (seg_rom rsegs)).
Proof.
  intros until sc. intros PRE MR TK UA MI ST FR ERR AUX PE SC48 SCLE.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). pose proof (AS_STACK_ge sc) as ASG. pose proof (RAS_STACK_mono 0 sc ltac:(lia)) as ASM.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m1) as MU. pose proof (wmono_refl rsegs m1) as WM.
  assert (RB0 : forall rid r1, (s_regions st1) !! rid = Some r1 -> 0 <= r_base r1 /\ r_base r1 + round_up_pg (r_len r1) <= alloc_ceiling).
  { intros rid r1 H1. (first [ pose proof ((rregion_facts st1 m1 rid r1 MR H1)) as dR_19; dand4 dR_19 as X1 _ X2 _ | pose proof (rregion_facts st1 m1 rid r1 MR H1) as (X1 & _ & X2 & _) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). lia. }
  subst tp. unfold PTP in *. rewrite unsigned_lit in ERR by lia.
  unfold MLOCK, DEBRUIJN in *.
  iprefixT.
  (* [comment removed for export] *)
  step. rewrite sextw_small by lia. step. step.
  (* [comment removed for export] *)
  step. apply evt_done.
  eapply (RAS FUEL) with (st0 := st) (lo := lo).
  all: lazymatch goal with
       | |- as_pre _ _ _ _ _ => try exact PRE
       | |- mrep _ _ => try exact MR
       | |- ticks_ok _ => try exact TK
       | |- unk_agree _ _ _ => try exact UA
       | |- brk_link_ps _ _ => try exact BL
       | |- auxv_okd (c_init_done (ctx st)) _ _ => try (rewrite unsigned_lit by lia; eapply auxv_okd_weaken; [exact AUX| (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia])
       | |- stk _ _ _ _ => try (rewrite unsigned_lit by lia; exact ST)
       | |- mem_inv _ _ => try assumption
       | |- rw_cells _ _ _ [C4 _] => try (rewrite unsigned_lit by lia; exact ERR)
       | |- _ => idtac
       end.
  all: try (rewrite ?unsigned_lit by lia; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia).
  all: try reflexivity.
  (* [comment removed for export] *)
  intros st2 idx s' ms' PO.
  (first [ dex16 PO as u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m' errv'; dand17 PO as -> MI' ST' ERR' AUX' MR' TK' UA' PE' MREL BL' PSM PSF PSO INV' CTR' RES | dand33 PO as u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m' errv' -> MI' ST' ERR' AUX' MR' TK' UA' PE' MREL BL' PSM PSF PSO INV' CTR' RES | destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m' & errv' & -> & MI' & ST' & ERR' & AUX' & MR' & TK' & UA' & PE' & MREL & BL' & PSM & PSF & PSO & INV' & CTR' & RES) ]).
  replace (ret_pc (Z_to_bv 64 0x24004)) with (Z_to_bv 64 0x24004) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  rewrite ?unsigned_lit in ST', AUX', PE', RES by lia.
  (* [comment removed for export] *)
  pose proof (frame_after_call (Clg:=Clg) (Rr:=Rr) st st2 lo _ m0 m1 m' m' _ _ MR0 MR' PE' FR ltac:(lia) ltac:((let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia)) as FR'.
  assert (AUX2' : auxv_okd (c_init_done (ctx st)) m' (bv_unsigned sp)) by (eapply (auxv_okd_malloc_fp st st2 lo _ m0 m' m1 m'); [exact MR0| exact MR'| exact AUX| exact PE'| (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia| lia]).
  assert (PE2 : pres_except (malloc_fp st st2 lo (bv_unsigned sp)) m0 m').
  { eapply pres_except_trans; [| eapply pres_except_mono; [exact PE'|]; intros a Ha; eapply malloc_fp_sp_mono; [|exact Ha]; lia].
    eapply pres_except_mono; [exact PE|]. intros a Ha. eapply malloc_fp_st_mono; [exact MREL|].
    eapply malloc_fp_mono; [|exact Ha]. intros rid r1 H1. exists r1. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto. lia. }
  assert (MREL2 : mrel st st2) by (eapply mrel_trans; [|exact MREL]; apply mrel_same; reflexivity).
  (first [ pose proof (MR') as dR_21; dand4 dR_21 as _ (CXH' & CXA' & _) (ML' & _) _ | pose proof MR' as (_ & (CXH' & CXA' & _) & (ML' & _) & _) ]). unfold CTX in CXA'. unfold MLOCK in ML'.
  clear MU WM PE AUX.
  destruct RES as [-> | (IDX0 & g & b & r & ACT2 & SO & SPANFP & EXPO)].
  - (* [comment removed for export] *)
    change (-1 <? 0) with true. cbv iota.
    iprefixT.
    step. if_cases KB; zify_cond KB. 2:{ exfalso. lia. }
    clear KB.
    step. step.
    (* [comment removed for export] *)
    step.
    eapply evt_cut.
    { eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact ML']. }
    intros ms'' ->.
    replace (ret_pc (Z_to_bv 64 0x24060)) with (Z_to_bv 64 0x24060) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    (* [comment removed for export] *)
    step. step. step. step. step. step. step. step. step. step.
    release_frame FR' ST' (bv_unsigned sp).
    apply evt_done. eapply (HFAIL st2 m' s' errv').
    all: try assumption.
  - (* [comment removed for export] *)
    replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia). rewrite ACT2.
    pose proof SO as [Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD S31 N0' NS NOGRP HDR0 Q16 SSL MSL AVr FRr FBr MPL SCr].
    iprefixT.
    step. if_cases KB; zify_cond KB. { exfalso. rewrite ?unsigned_lit in KB by lia. lia. }
    clear KB.
    step. step. rewrite (unsigned_lit sc), Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. step.
    pose proof (actives_nth st2 sc ltac:(lia)) as NTH. rewrite ACT2 in NTH.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      pose proof (u64arr_read rsegs mc _ (actives st2) sc (pw st2 (Some g)) (wa (403456 + 80 + 8 * sc)) CXA' NTH ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end.
    step.
    apply evt_done.
    change (Z_to_bv 64 idx) with (wz idx).
    eapply (HENF st2 g b r idx m' s' errv').
    all: try assumption.
    + intros a Ha. eapply malloc_fp_sp_mono; [|apply SPANFP; exact Ha]. lia.
    + intros [X|X]; [exfalso; unfold MMAP_THRESHOLD in *; lia|]. apply EXPO. exact X.
    + right. exists sc. split; [exact ACT2| lia].
Qed.
End ASCALL.


(* [comment removed for export] *)
(* [comment removed for export] *)


Section SMALL.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Context {R : Type}.
Variables (K : mstate -> option (aptr * Z) -> Malloc.M R) (bail : Malloc.M R) (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
          (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N).
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : alloc_slot_stmt as_pre as_inv.
Hypothesis HENF : enf_hyp K o m0 st s Q ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo.
Hypothesis HFAIL : fail_hyp K o m0 st s Q ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc lo.
Hypothesis MF : MFACTS st LB.
Hypothesis MR0 : mrep st m0.
Hypothesis TP : tp = Z_to_bv 64 PTP.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 48 - AS_STACK 0.
Hypothesis N0 : 0 <= n < 2^32.
Hypothesis NT : n < MMAP_THRESHOLD.
Hypothesis BL : brk_link_ps st s.

Let st1 := set_tick t st.

#[using="BL NT N0 LO CLO TP MR0 MF HFAIL HENF RAS as_inv LB"] Lemma malloc_small_implT :
  forall (m1 : mem) (errv : word) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2r t3 t4 t5 t6 ra' : word) (sc : Z),
  sc = size_to_class n -> 0 <= sc < 48 -> n + 4 <= 16 * size_class sc ->
  (forall sc', 0 <= sc' < 48 -> n + 4 <= 16 * size_class sc' -> as_pre st st1 sc' n FUEL) ->
  mrep st1 m1 -> ticks_ok st1 -> unk_agree st1 o m1 -> mem_inv rsegs m1 ->
  stk rsegs m1 lo (bv_unsigned sp + -48) ->
  rw_cells rsegs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
  rw_cells rsegs m1 (errno_addr tp) [C4 errv] -> auxv_okd (c_init_done (ctx st)) m1 (bv_unsigned sp) ->
  pres_except (malloc_fp st st1 lo (bv_unsigned sp)) m0 m1 ->
  implT o (malloc_small_ctrl full_lay st1 n K bail) s Q
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 MLOCK) a0 a1 a2 a3 a4 a5 a6 a7
                 s2r (Z_to_bv 64 DEBRUIJN) (Z_to_bv 64 sc) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x23f00) fc None m1 (seg_rom rsegs)).
Proof.
  intros until sc. intros SCE SC48 NFIT ASP MR TK UA MI ST FR ERR AUX PE.
  pose proof (AS_STACK_ge 0) as ASG. unfold st1 in *.
  rewrite malloc_small_ctrl_eq. rewrite <- SCE. change (coarse_sc (set_tick t st) sc) with (coarse_sc st sc). cbv zeta.
  pose proof (coarse_sc_cases st sc SC48) as CC.
  assert (SC48' : 0 <= coarse_sc st sc < 48) by (destruct CC as [-> | (-> & H4 & EV)]; [lia| apply lor1_range; lia]).
  assert (NFIT' : n + 4 <= 16 * size_class (coarse_sc st sc)).
  { destruct CC as [-> | (E & H4 & EV)]; [lia|]. rewrite E. pose proof (size_class_lor1 sc H4 EV). lia. }
  assert (SCLE' : coarse_sc st sc <= Z.lor (size_to_class n) 1).
  { rewrite <- SCE. pose proof (lor1_ge sc SC48). destruct CC as [-> | (E & H4 & EV)]; [lia| rewrite E; lia]. }
  set (sc' := coarse_sc st sc) in *.
  change (active (set_tick t st) sc') with (active st sc').
  iprefixT. eapply evt_cut.
  { eapply (coarse_walk st LB m1 t MF MR); [exact SC48| intros; apply lor1_range; lia]. }
  fold sc'. (intros ms'; (first [ intro dR_24; dex4 dR_24 as a0' a1' a2' a3'; destruct dR_24 as [-> HA0] | intro dR_24; dand6 dR_24 as a0' a1' a2' a3' -> HA0 | intros (a0' & a1' & a2' & a3' & -> & HA0) ])).
  change (active (set_tick t st) sc') with (active st sc') in HA0 |- *.
  destruct (active st sc') as [g|] eqn:ACT'.
  - cbn iota. change (get_meta_rec (set_tick t st) g) with (get_meta_rec st g) in HA0 |- *. subst a0'.
    destruct (Z.eq_dec (m_avail (get_meta_rec st g)) 0) as [AZ|ANZ].
    + (* [comment removed for export] *)
      rewrite AZ, lowbit_0. cbn.
      eapply evt_cut. { apply core0_walk. }
      intros ms'' (a1'' & ->). apply evt_done.
      eapply ras_call_implT; try eassumption; try lia. apply ASP; [exact SC48'| exact NFIT'].
    + (* [comment removed for export] *)
      apply evt_done.
      (first [ pose proof ((active_ptr_facts st LB m1 t MF MR sc' g ACT')) as dR_22; dand6 dR_22 as _ _ _ _ AVr _ | destruct (active_ptr_facts st LB m1 t MF MR sc' g ACT') as (_ & _ & _ & _ & AVr & _) ]).
      (first [ pose proof ((lowbit_facts (m_avail (get_meta_rec st g)) ltac:(lia))) as dR_23; dex1 dR_23 as k; destruct dR_23 as [K32 LBK] | pose proof ((lowbit_facts (m_avail (get_meta_rec st g)) ltac:(lia))) as dR_23; dand3 dR_23 as k K32 LBK | destruct (lowbit_facts (m_avail (get_meta_rec st g)) ltac:(lia)) as (k & K32 & LBK) ]).
      assert (P2 : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
      replace (lowbit (m_avail (get_meta_rec st g)) =? 0) with false by (rewrite LBK; symmetry; apply Z.eqb_neq; lia).
      cbn [negb]. cbv iota.
      change (pw (set_tick t st) (Some g)) with (pw (set_tick t st) (Some g)).
      eapply rfast_core_implT; try eassumption; try lia.
  - cbn iota. subst a0'.
    eapply evt_cut. { change (pw (set_tick t st) None) with (pw (set_tick t st) (@None aptr)). apply core0_walk. }
    intros ms'' (a1'' & ->). apply evt_done.
    eapply ras_call_implT; try eassumption; try lia. apply ASP; [exact SC48'| exact NFIT'].
Qed.
End SMALL.
End RF_m8qy.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RF_m8yt.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_mx3o.RF_mcaj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_mx3o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_mdx7.RF_m8qy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_m8yt.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require MRep MRepAux MTree W_ge3a6 Mallkgx Mall1es.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RF_mx3o.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RAlllfc RF_m8yt RF_mx3o SlotMisc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.W_ge3a6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall1es OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_mx3o.RF_mcaj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RAlllfc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_m8yt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_mx3o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.SlotMisc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import F_sy88u MRep MRepAux RAlllfc Malllim Mallj6y.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Notation AREACH := (AREACH_from p0_reserved).

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Definition coreQ (o m0 : mem) (st : mstate) (s : PState)
    (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z)
    (res : mstate * option (aptr * Z)) (s' : PState) (ms' : machine_state) : Prop :=
  match res with
  | (st2, Some (g, idx)) =>
    exists (b : aptr) (r : region) (m1 : mem) (errv : word) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 ra' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 MLOCK)
                   a0 a1 a2 a3 a4 a5 a6 a7 (pw st2 (Some g)) (wz idx) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x24018) fc None m1 (seg_rom rsegs)
      /\ mrep st2 m1 /\ ticks_ok st2 /\ unk_agree st2 o m1 /\ mem_inv rsegs m1
      /\ stk rsegs m1 lo (bv_unsigned sp + -48)
      /\ rw_cells rsegs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra]
      /\ rw_cells rsegs m1 (errno_addr tp) [C4 errv] /\ auxv_okd (c_init_done (ctx st)) m1 (bv_unsigned sp)
      /\ pres_except (malloc_fp st st2 lo (bv_unsigned sp)) m0 m1
      /\ (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx - 4 <= a
                   < r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) - 4 ->
            malloc_fp st st2 lo (bv_unsigned sp) a)
      /\ 0 <= c_mmap_counter (ctx st2) < 2^32
      /\ slot_ok st2 g b r idx n
      /\ (expo_cond st n -> rdv pans_mem o st2 (fst b, snd b + (16 + get_stride (get_meta_rec st2 g) * idx) + -3) = 0)
      /\ (MMAP_THRESHOLD <= n \/ exists sc', active st2 sc' = Some g /\ 0 <= sc' <= Z.lor (size_to_class n) 1)
      /\ mrel st st2 /\ brk_link_ps st2 s' /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
  | (st2, None) =>
    exists (m1 : mem) (errv : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0v s1v (wz 0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m1 (seg_rom rsegs)
      /\ mrep st2 m1 /\ ticks_ok st2 /\ mem_inv rsegs m1 /\ stk rsegs m1 lo (bv_unsigned sp)
      /\ rw_cells rsegs m1 (errno_addr tp) [C4 errv] /\ auxv_okd (c_init_done (ctx st)) m1 (bv_unsigned sp)
      /\ pres_except (malloc_fp st st2 lo (bv_unsigned sp)) m0 m1
      /\ mrel st st2 /\ brk_link_ps st2 s' /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
  end.

Lemma enf_hyp_ret o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo :
  enf_hyp (fun st1 r => ret (st1, r)) o m0 st s (coreQ o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo)
           ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo.
Proof.
  intros st2 g b r idx m1 s' errv t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 ra'; intros.
  apply implT_ret. apply evt_done. cbn [coreQ].
  exists b, r, m1, errv. do 17 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
Qed.

Lemma fail_hyp_ret o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo :
  fail_hyp (fun st1 r => ret (st1, r)) o m0 st s (coreQ o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo)
            ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc lo.
Proof.
  intros st2 m1 s' errv t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6; intros.
  apply implT_ret. apply evt_done. cbn [coreQ].
  exists m1, errv. do 14 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
Qed.

(* [comment removed for export] *)
Definition big_stmt : Prop :=
  forall (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
         (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N)
         (m1 : mem) (errv : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2r s3r s4r t3 t4 t5 t6 ra' : word),
  let st1 := set_tick t st in
  AREACH st LB -> MFACTS st LB -> mrep st m0 -> tp = Z_to_bv 64 PTP ->
  alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 - AM_STACK -> MMAP_THRESHOLD <= n < 2^32 -> brk_link_ps st s ->
  mrep st1 m1 -> ticks_ok st1 -> unk_agree st1 o m1 -> mem_inv rsegs m1 ->
  stk rsegs m1 lo (bv_unsigned sp + -48) ->
  rw_cells rsegs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
  rw_cells rsegs m1 (errno_addr tp) [C4 errv] -> auxv_okd (c_init_done (ctx st)) m1 (bv_unsigned sp) ->
  pres_except (malloc_fp st st1 lo (bv_unsigned sp)) m0 m1 ->
  implT o (malloc_core full_lay st1 n) s (coreQ o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 MLOCK) (Z_to_bv 64 131052) a1 a2 a3 a4 a5 a6 a7
                 s2r s3r s4r s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x23d68) fc None m1 (seg_rom rsegs)).

End CEIL.

Section CORE.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : alloc_slot_stmt as_pre as_inv.
Hypothesis AS_PRE : forall st LB t sc n, AREACH st LB -> MFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
  n + 4 <= 16 * size_class sc -> as_pre st (set_tick t st) sc n FUEL.
Hypothesis RBIG : big_stmt.

Lemma malloc_core_implT :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (st : mstate) (LB : list block) (s : PState) (n lo : Z) (errv : word) (t : N),
  AREACH st LB -> MFACTS st LB -> mrep st m -> brk_link_ps st s ->
  auxv_okd (c_init_done (ctx st)) m (bv_unsigned sp) ->
  stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 8192 ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m ->
  tp = Z_to_bv 64 PTP ->
  a0 = Z_to_bv 64 n -> 0 <= n < 2^32 -> (s_tick st < t)%N ->
  implT m (malloc_core full_lay (set_tick t st) n) s
        (coreQ m m st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 malloc_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until t. intros AR MF MR BL AUX ST CLO LO ERR MI TP HA N TT.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (AS_STACK_ge 0) as ASG.
  assert (RB0 : forall rid r1, (s_regions st) !! rid = Some r1 -> 0 <= r_base r1 /\ r_base r1 + round_up_pg (r_len r1) <= alloc_ceiling).
  { intros rid r1 H1. (first [ pose proof ((rregion_facts st m rid r1 MR H1)) as dR_1; dand4 dR_1 as X1 _ X2 _ | pose proof (rregion_facts st m rid r1 MR H1) as (X1 & _ & X2 & _) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). lia. }
  (first [ pose proof (MR) as dR_2; dand4 dR_2 as WF0 CX0 GL0 _ | pose proof MR as (WF0 & CX0 & GL0 & _) ]). (first [ dand3 GL0 as _ NL _ | destruct GL0 as (_ & NL & _) ]).
  assert (PREP : forall m1, munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1 -> wmono rsegs m m1 ->
            mrep (set_tick t st) m1 /\ ticks_ok (set_tick t st) /\ unk_agree (set_tick t st) m m1
            /\ rw_cells rsegs m1 (errno_addr tp) [C4 errv] /\ auxv_okd (c_init_done (ctx st)) m1 (bv_unsigned sp)
            /\ pres_except (malloc_fp st (set_tick t st) lo (bv_unsigned sp)) m m1).
  { intros m1 MU WM. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
    split. { apply mrep_set_tick. eapply mrep_transport_high; [exact MR| exact MU| exact WM| intros lo' hi' [E|[]]; inversion E; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia]. }
    split. { apply ticks_ok_set_tick; [lia|]. exact (mf_ticks _ _ MF). }
    split. { eapply unk_agree_munch; [| exact MU| |].
             - eapply unk_agree_ext; [apply unk_agree_refl| reflexivity| intros; reflexivity| reflexivity].
             - intros rid r1 H1 K1. pose proof (RB0 rid r1 H1). cbn. lia.
             - intros rid r1 H1. pose proof (RB0 rid r1 H1). lia. }
    split. { eapply rw_cells_transport; [exact ERR| exact MU| exact WM|]. subst tp. unfold PTP. rewrite unsigned_lit by lia. cbn. lia. }
    split. { eapply auxv_okd_frame; [exact AUX| exact MU| exact WM|]. unfold AUXV_CELL. constructor; [cbn; lia| constructor]. }
    eapply pres_except_of_munch; [exact MU| exact WM|]. intros a Ha NC. cbn. split; [|exact I]. intros HX. apply NC. left. left. lia. }
  destruct (Z.le_gt_cases MMAP_THRESHOLD n) as [TH|TH].
  - (* [comment removed for export] *)
    iprefixT. eapply evt_cut.
    { eapply (entry_big_walk ra sp gp tp); [exact HA| unfold MMAP_THRESHOLD in *; lia| exact ST| (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia| lia| exact MI]. }
    (intros ms'; (first [ intro dR_7; dex2 dR_7 as a1' m1; dand6 dR_7 as -> FR ST1 MU WM MI1 | intro dR_7; dand8 dR_7 as a1' m1 -> FR ST1 MU WM MI1 | intros (a1' & m1 & -> & FR & ST1 & MU & WM & MI1) ])).
    (first [ pose proof ((PREP m1 MU WM)) as dR_4; dand6 dR_4 as MR1 TK1 UA1 ERR1 AUX1 PE1 | destruct (PREP m1 MU WM) as (MR1 & TK1 & UA1 & ERR1 & AUX1 & PE1) ]).
    apply evt_done.
    eapply (RBIG m m st LB s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo t); try eassumption.
    + unfold AM_STACK. lia.
    + lia.
  - (* [comment removed for export] *)
    unfold malloc_core.
    replace (size_overflows n) with false by (symmetry; unfold size_overflows; apply Z.leb_gt; lia).
    replace (MMAP_THRESHOLD <=? n) with false by (symmetry; apply Z.leb_gt; lia).
    iprefixT. eapply evt_cut.
    { eapply (malloc_entry_walk ra sp gp tp); [exact HA| unfold MMAP_THRESHOLD in *; lia| exact ST| (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia| lia| exact MI| exact NL]. }
    (intros ms'; (first [ intro dR_8; dex5 dR_8 as a0' a1' a2' a3' m1; dand6 dR_8 as -> FR ST1 MU WM MI1 | intro dR_8; dand11 dR_8 as a0' a1' a2' a3' m1 -> FR ST1 MU WM MI1 | intros (a0' & a1' & a2' & a3' & m1 & -> & FR & ST1 & MU & WM & MI1) ])).
    (first [ pose proof ((PREP m1 MU WM)) as dR_5; dand6 dR_5 as MR1 TK1 UA1 ERR1 AUX1 PE1 | destruct (PREP m1 MU WM) as (MR1 & TK1 & UA1 & ERR1 & AUX1 & PE1) ]).
    (first [ pose proof ((size_to_class_props n ltac:(lia))) as dR_6; dand3 dR_6 as SCR SFIT _ | pose proof (size_to_class_props n ltac:(lia)) as (SCR & SFIT & _) ]).
    apply evt_done.
    eapply (malloc_small_implT (fun st1 r => ret (st1, r)) (ret (set_tick t st, None)) m m st LB s _ ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo t as_pre as_inv RAS).
    all: try eassumption.
    + apply enf_hyp_ret.
    + apply fail_hyp_ret.
    + unfold AS_STACK. lia.
    + reflexivity.
    + intros sc' Hsc' Hfit'. eapply AS_PRE; [exact AR| exact MF| exact TT| exact Hsc'| lia| exact Hfit'].
Qed.
End CORE.