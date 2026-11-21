(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (7 recorded proofs replaced by written proofs (follow_steq, follow_sbind, strel_follow and 4 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A Malloc_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import Malloc_fp F_malloc_enf AllocSlot_iface F_malloc_join F_malloc_small F_malloc_entry F_malloc_core.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require MallocFacts_inv2.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_malloc_top () := "I59OSSVerify5KrLib4Spec5STree4steq00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalI35stdpp9countable9Countable00C59OSSVerify5KrLib4Spec:MallocCtrl4prunC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3retC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC35stdpp4base;RelDecisionC59OSSVerify5KrLib4Spec6Malloc3rd8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4rd16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<enframe_fullC1?~~~~~~~~~~~~~~~C35stdpp4base4fmapC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5STree8steq_indC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl6followC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5STree;sbind_ret_lC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5STree9sbind_visC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes6option00I47Corelib4Init5Logic2eq00K59OSSVerify5KrLib4Spec5STree5stree01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes6option02K59OSSVerify5KrLib4Spec5STree5stree02C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib4Spec6Malloc<undef_reason00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib4Spec5STree9stree_indC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5STree5sbindC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C47Corelib4Init5Logic9False_indI47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C59OSSVerify5KrLib4Spec5STree9strel_indC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5STree5strel00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<F_malloc_enf=surj_pair_letC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree4mrunC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc@F_malloc_enframe:rd8_oracleC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc@F_malloc_enframe;rd16_oracleC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib4Spec6Malloc8fold_offC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C47Corelib4Init9Datatypes2idK47Corelib4Init9Datatypes4prod01C35stdpp6option;from_optionC59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;slot_start'C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib4Spec6Malloc:enframe_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eqb_eqC47Corelib4Init5Logic5proj2C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib6Malloc@F_malloc_enframe3rdvC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3divC59OSSVerify5KrLib4Spec6Malloc5havocC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C59OSSVerify5KrLib6Malloc:MallocTree3memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree8pans_memC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree8pupd_memC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1N01K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib6Malloc:MallocTree>pans_mem_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5stripC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~I35stdpp4gmap4gmap00C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5STree5erunsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl4pselC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev06C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z:mod_divideC56Stdlib6ZArith6BinInt1Z6divideI47Corelib4Init5Logic2ex00I46Stdlib;setoid_ring<Ring_polynom5PExpr00K47Corelib4Init9Datatypes4list02K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr03K46Stdlib;setoid_ring<Ring_polynom5PExpr07I46Stdlib;setoid_ring<Ring_polynom3Pol00C46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib6ZArith6BinInt1Z2leC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterI46Stdlib9micromega:ZMicromega;ZArithProof00I46Stdlib;setoid_ring<Ring_polynom3Mon00I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Lemma follow_steq {R} (t1 t2 : Malloc.M R) : steq t1 t2 -> forall ans, follow t1 ans = follow t2 ans.
Proof.
  induction 1 as [r | e k1 k2 Hk IH]; intros ans; [reflexivity|].
  cbn. destruct e; try reflexivity; destruct ans; try reflexivity; apply IH.
Qed.

Lemma follow_sbind {R S} (t : Malloc.M R) (f : R -> Malloc.M S) :
  forall ans x y, follow t ans = Some x ->
  (forall ans', follow (f x) ans' = Some y) ->
  follow (sbind t f) ans = Some y.
Proof.
  induction t as [r | e k IH]; intros ans x y H Hf.
  - cbn in H. inversion H; subst. rewrite sbind_ret_l. apply Hf.
  - rewrite sbind_vis. cbn in H |- *. destruct e; try discriminate; destruct ans as [|a ans]; try discriminate; eapply IH; eauto.
Qed.

Lemma strel_follow {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : Malloc.M R1) (t2 : Malloc.M R2) :
  strel RR t1 t2 -> forall ans r1 r2, follow t1 ans = Some r1 -> follow t2 ans = Some r2 -> RR r1 r2.
Proof.
  induction 1 as [a b Hab | e k1 k2 Hk IH]; intros ans r1 r2 F1 F2.
  - cbn in F1, F2. inversion F1; inversion F2; subst. exact Hab.
  - cbn in F1, F2. destruct e; try discriminate; destruct ans as [|z ans]; try discriminate; eapply IH; eauto.
Qed.

(* [comment removed for export] *)
Lemma mrun_enframe_full o st g b idx n ctr :
  m_mem (get_meta_rec st g) = Some b ->
  let stride := get_stride (get_meta_rec st g) in
  let off := fold_off (if rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -3) =? 0 then Z.land ctr 255
                       else Z.land (rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -2)
                                    + 256 * rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -2 + 1) + 1) 255)
                      ((stride - IB - n) / UNIT) in
  mrun o (enframe_full st g idx n ctr (fun st2 p => ret (havoc p n st2, Some p)))
  = SRet (o, (havoc (snd (enframe_at st g idx n off)) n (fst (enframe_at st g idx n off)), Some (snd (enframe_at st g idx n off)))).
Proof.
  intros Hmem stride off. unfold mrun, enframe_full, enframe_read_off.
  assert (Hp0 : slot_start' (get_meta_rec st g) idx = (fst b, snd b + (16 + stride * idx))).
  { unfold slot_start'. rewrite Hmem. cbn [default from_option id]. unfold aadd, UNIT. cbn [fst snd]. reflexivity. }
  rewrite Hp0. unfold aadd. cbn [fst snd]. fold stride.
  rewrite (rd8_oracle pans_mem pans_mem_range).
  assert (OFFa : rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -3) = 0 -> fold_off (Z.land ctr 255) ((stride - IB - n) / UNIT) = off).
  { intros E0. subst off. rewrite (proj2 (Z.eqb_eq _ _) E0). reflexivity. }
  assert (OFFb : rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -3) <> 0 ->
     fold_off (Z.land (rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -2) + 256 * rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -2 + 1) + 1) 255)
              ((stride - IB - n) / UNIT) = off).
  { intros E0. subst off. rewrite (proj2 (Z.eqb_neq _ _) E0). reflexivity. }
  clearbody off.
  destruct (Z.eqb_spec (rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -3)) 0) as [E|NE]; cbn [negb].
  - rewrite (OFFa E). rewrite surj_pair_let. reflexivity.
  - rewrite (rd16_oracle pans_mem pans_mem_range). unfold aadd. cbn [fst snd].
    rewrite (OFFb NE). rewrite surj_pair_let. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma strip_eq_proj a b : strip a = strip b ->
  s_ctx a = s_ctx b /\ s_regions a = s_regions b /\ s_next_rid a = s_next_rid b /\ s_metas a = s_metas b
  /\ s_areas a = s_areas b /\ s_groups a = s_groups b /\ s_slots a = s_slots b /\ s_reserved a = s_reserved b.
Proof.
  intros E.
  pose proof (f_equal s_ctx E) as E1. pose proof (f_equal s_regions E) as E2. pose proof (f_equal s_next_rid E) as E3.
  pose proof (f_equal s_metas E) as E4. pose proof (f_equal s_areas E) as E5. pose proof (f_equal s_groups E) as E6.
  pose proof (f_equal s_slots E) as E7. pose proof (f_equal s_reserved E) as E8.
  cbn in E1, E2, E3, E4, E5, E6, E7, E8. repeat split; assumption.
Qed.

(* [comment removed for export] *)
Lemma mrun_fst {R} (t : Malloc.M R) : forall o ans o1 x, follow (mrun o t) ans = Some (o1, x) -> o1 = o.
Proof.
  unfold mrun, prun. induction t as [r | e k IH]; intros o ans o1 x H.
  - cbn in H. inversion H. reflexivity.
  - cbn [eruns] in H. destruct (psel pans_mem o e) as [a|] eqn:P.
    + unfold pupd_mem in H. eapply IH. exact H.
    + cbn in H. destruct e; try discriminate; destruct ans; try discriminate; unfold pupd_mem in H; eapply IH; exact H.
Qed.

Lemma mod16_slot (B s st k off : Z) : B mod 4096 = 0 -> s mod 16 = 0 -> st mod 16 = 0 -> 0 <= k ->
  (B + s + 16 + st * k + 16 * off) mod 16 = 0.
Proof.
  intros HB HS HT HK.
  destruct (Z.mod_divide st 16 ltac:(lia)) as [D _]. destruct (D HT) as [q Hq].
  assert (E : st * k = 16 * (q * k)) by (rewrite Hq; ring).
  set (w := q * k) in E. clearbody w. rewrite E. Z.div_mod_to_equations. lia.
Qed.

Section TOPLEVEL.
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis AS_PRE : forall st LB t sc n, AREACH st LB -> MFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
  n + 4 <= 16 * size_class sc -> as_pre st (set_tick t st) sc n FUEL.
End TOPLEVEL.


End CANSEC1.
