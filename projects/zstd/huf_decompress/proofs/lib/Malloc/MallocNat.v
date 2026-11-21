(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (18 recorded proofs replaced by written proofs (steq_trans, steq_sbind, eruns_steq and 15 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep MallocTree.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MallocNat () := "I59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5STree=strel_eq_steqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5STree>strel_trans_eqC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5STree4steq00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I59OSSVerify5KrLib4Spec5STree5strel00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C59OSSVerify5KrLib4Spec5STree5sbindC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec5STree;strel_sbindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5STree5erunsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5STree8steq_indC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K59OSSVerify5KrLib4Spec5STree4steq01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree4steq02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9MallocNat:steq_transC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9MallocNat:steq_sbindC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9MallocNat2kSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5STree9steq_reflC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9MallocNat2bSC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9MallocNat2KFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5STree;sbind_assocC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9MallocNat3kS1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9MallocNat3KF1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5queueC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9free_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>activate_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7am_takeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8am_carveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9am_finishC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<am_after_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:alloc_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6ta_finC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9try_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7ag_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;alloc_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:alloc_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5guardC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02K59OSSVerify5KrLib4Spec6Malloc<undef_reason01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev06C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes4bool00c59OSSVerify5KrLib6Malloc9MallocNat:guard_nat1C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8optr_eqbC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02C59OSSVerify5KrLib4Spec6Malloc6m_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8get_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_set_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_set_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8set_headC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5lhead00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9MallocNat9queue_natC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8put_metaC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5meta0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9MallocNat9guard_natC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idK47Corelib7Numbers7BinNums1Z03C35stdpp6option;from_optionC59OSSVerify5KrLib4Spec6Malloc@group_active_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9mask_uptoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z5ldiffC59OSSVerify5KrLib4Spec6Malloc;m_set_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_set_availC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1N00K47Corelib7Numbers7BinNums1N01C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<c_avail_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_countC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec6MallocDset_avail_meta_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>set_avail_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7upd_ctxC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9META_SIZEC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc<undef_reason03C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9MallocNat;am_take_natC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableI35stdpp4gmap4gmap00C35stdpp4gmapBgmap_partial_alterC35stdpp8fin_maps:map_insertC59OSSVerify5KrLib4Spec6MallocBset_meta_area_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocGc_avail_meta_area_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocIset_avail_meta_area_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocDset_avail_meta_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_tailC1?~~~~~~~~~~~~~~~C35stdpp4gmap;gmap_lookupC59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupC59OSSVerify5KrLib4Spec6Malloc7a_checkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8a_nslotsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4area01C1?~~~~~~~~~~~~~~~C35stdpp4base6insertC59OSSVerify5KrLib4Spec6Malloc9set_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBset_meta_area_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6a_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8AREA_HDRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6NSLOTSC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countableC59OSSVerify5KrLib4Spec6MallocBc_avail_meta_areasC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC56Stdlib6ZArith6BinInt1Z6moduloC47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBmprotect_answer_okC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbK59OSSVerify5KrLib4Spec6Malloc2ev04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7PROT_RWC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02K59OSSVerify5KrLib4Spec6Malloc<undef_reason04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5TWO64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6ENOSYSC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9MallocNat=am_finish_natC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addK59OSSVerify5KrLib4Spec6Malloc2ev02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;live_rangesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>mmap_answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6is_errC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:new_regionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_meta_alloc_shiftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocDset_meta_alloc_shiftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N4succK59OSSVerify5KrLib4Spec6Malloc6region01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;set_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<set_next_ridC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftlC59OSSVerify5KrLib4Spec6Malloc9PROT_NONEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;MAP_PRIVATEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8MAP_ANONC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind02C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9MallocNat@am_after_brk_natC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_free_meta_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7dequeueC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_brkC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbK59OSSVerify5KrLib4Spec6Malloc2ev01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>brk0_answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7set_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocDmmap_fixed_answer_okC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc8brkstate03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_init_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=set_init_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=brk_answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<brk_pages_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:upd_regionC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool01K59OSSVerify5KrLib4Spec6Malloc5rkind01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc8brkstate00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc8brkstate02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9MAP_FIXEDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6lowbitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree8steq_symC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9MallocNatBactivate_group_natC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9MallocNat:ta_fin_natC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9span_loopC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC59OSSVerify5KrLib4Spec6MallocDset_group_active_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=decay_bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_activeC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9m_set_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>m_set_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>m_set_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc?m_set_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6lh_hdrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9set_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9put_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9add_slotsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc;layout_hook00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9MallocNat=free_meta_natC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9MallocNat>alloc_meta_natC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9MallocNat;ag_tail_natC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC59OSSVerify5KrLib4Spec6Malloc>small_cnt_pickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7med_cntC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4evenC56Stdlib6ZArith6BinInt1Z3lebC59OSSVerify5KrLib4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3u32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@set_mmap_counterC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrC59OSSVerify5KrLib4Spec6Malloc<m_set_maplenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=size_to_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7slot_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7lh_nestC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:halve_evenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9halve_bigC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;is_bouncingC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>account_bounceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8step_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9MallocNat=try_avail_natC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9MallocNat?alloc_group_natC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5ctz32C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indI47Corelib4Init9Datatypes3nat00K59OSSVerify5KrLib4Spec6Malloc<undef_reason02C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Lemma steq_trans {E A R} (t1 t2 t3 : stree E A R) : steq t1 t2 -> steq t2 t3 -> steq t1 t3.
Proof.
  intros H1 H2. apply strel_eq_steq. apply strel_eq_steq in H1. apply strel_eq_steq in H2.
  eapply strel_trans_eq; [exact H1| exact H2].
Qed.

Lemma steq_sbind {E A R S} (t1 t2 : stree E A R) (f1 f2 : R -> stree E A S) :
  steq t1 t2 -> (forall r, steq (f1 r) (f2 r)) -> steq (sbind t1 f1) (sbind t2 f2).
Proof.
  intros Ht Hf. apply strel_eq_steq. eapply (strel_sbind (RR := eq)); [apply strel_eq_steq; exact Ht|].
  intros r1 r2 ->. apply strel_eq_steq. apply Hf.
Qed.

Lemma eruns_steq {E A O R} (sel : O -> E -> option A) (upd : O -> E -> A -> O) (t1 t2 : stree E A R) :
  steq t1 t2 -> forall o, steq (eruns sel upd o t1) (eruns sel upd o t2).
Proof.
  induction 1 as [r|e k1 k2 Hk IH]; intros o; cbn [eruns].
  - constructor.
  - destruct (sel o e) as [a|]; [apply IH|]. constructor. intros a. apply IH.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition kS {X Y : Type} : X -> Y -> Malloc.M (option (X * Y)) := fun x y => SRet (Some (x, y)).
Definition bS {T : Type} : Malloc.M (option T) := SRet None.
Definition KF {X Y R : Type} (k : X -> Y -> Malloc.M R) (bail : Malloc.M R) (r : option (X * Y)) : Malloc.M R :=
  match r with Some (x, y) => k x y | None => bail end.
(* [comment removed for export] *)
Definition kS1 {X : Type} : X -> Malloc.M (option X) := fun x => SRet (Some x).
Definition KF1 {X R : Type} (k : X -> Malloc.M R) (bail : Malloc.M R) (r : option X) : Malloc.M R :=
  match r with Some x => k x | None => bail end.

(* [comment removed for export] *)
End CANSEC1.
Ltac nat_leaf := cbn [sbind KF KF1 kS kS1 bS]; apply steq_refl.
Ltac nat_vis := cbn [sbind]; apply steq_vis; intros ?.
Ltac nat_case :=
  lazymatch goal with
  | |- steq _ (sbind (match ?c with _ => _ end) _) => destruct c
  end.

(* [comment removed for export] *)
Ltac nat_call NAT :=
  eapply steq_trans; [apply NAT|];
  eapply steq_trans; [| apply steq_sym; eapply steq_trans; [eapply steq_sbind; [apply NAT| intros ?; apply steq_refl]| apply sbind_assoc]];
  apply steq_sbind; [apply steq_refl|];
  intros [[? ?]|]; cbn [KF sbind].
Ltac nat_call1 NAT :=
  eapply steq_trans; [apply NAT|];
  eapply steq_trans; [| apply steq_sym; eapply steq_trans; [eapply steq_sbind; [apply NAT| intros ?; apply steq_refl]| apply sbind_assoc]];
  apply steq_sbind; [apply steq_refl|];
  intros [?|]; cbn [KF1 sbind].

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC2. Context {rc : runConstT}.
Lemma guard_nat {X Y R} tag c (K : Malloc.M R) (K' : Malloc.M (option (X * Y))) bail f :
  steq K (sbind K' f) -> steq bail (f None) ->
  steq (guard tag c K bail) (sbind (guard tag c K' bS) f).
Proof. intros HK HB. unfold guard. destruct c; [exact HK|]. nat_vis. cbn [sbind bS]. exact HB. Qed.

Lemma guard_nat1 {X R} tag c (K : Malloc.M R) (K' : Malloc.M (option X)) bail f :
  steq K (sbind K' f) -> steq bail (f None) ->
  steq (guard tag c K bail) (sbind (guard tag c K' bS) f).
Proof. intros HK HB. unfold guard. destruct c; [exact HK|]. nat_vis. cbn [sbind bS]. exact HB. Qed.

Lemma queue_nat {R} h m st (k : mstate -> Malloc.M R) bail :
  steq (queue h m st k bail) (sbind (queue h m st kS1 bS) (KF1 k bail)).
Proof.
  unfold queue. apply guard_nat1; [|nat_leaf]. apply guard_nat1; [|nat_leaf].
  nat_case; cbv zeta; [destruct (m_prev _)|]; nat_leaf.
Qed.

Lemma free_meta_nat {R} m st (k : mstate -> Malloc.M R) bail :
  steq (free_meta m st k bail) (sbind (free_meta m st kS1 bS) (KF1 k bail)).
Proof. unfold free_meta. apply queue_nat. Qed.

Lemma activate_group_nat {R} m st (k : mstate -> Z -> Malloc.M R) bail :
  steq (activate_group m st k bail) (sbind (activate_group m st kS bS) (KF k bail)).
Proof. unfold activate_group. apply guard_nat; [|nat_leaf]. cbv zeta. nat_leaf. Qed.

(* [comment removed for export] *)
End CANSEC2.
Ltac nat_auto cal :=
  first [ nat_leaf
        | cal
        | nat_vis; nat_auto cal
        | nat_case; nat_auto cal
        | progress (cbv zeta); nat_auto cal ].

Section CANSEC3. Context {rc : runConstT}.
Lemma am_take_nat {R} st (k : mstate -> optr -> Malloc.M R) bail :
  steq (am_take st k bail) (sbind (am_take st kS bS) (KF k bail)).
Proof. unfold am_take. nat_auto fail. Qed.

Lemma am_carve_nat {R} st p (k : mstate -> optr -> Malloc.M R) bail :
  steq (am_carve st p k bail) (sbind (am_carve st p kS bS) (KF k bail)).
Proof. unfold am_carve. cbv zeta. apply am_take_nat. Qed.

Lemma am_finish_nat {R} st nu (k : mstate -> optr -> Malloc.M R) bail :
  steq (am_finish st nu k bail) (sbind (am_finish st nu kS bS) (KF k bail)).
Proof. unfold am_finish, bad_answer. nat_auto ltac:(apply am_carve_nat). Qed.

Lemma am_after_brk_nat {R} st nu (k : mstate -> optr -> Malloc.M R) bail :
  steq (am_after_brk st nu k bail) (sbind (am_after_brk st nu kS bS) (KF k bail)).
Proof. unfold am_after_brk, bad_answer. nat_auto ltac:(apply am_finish_nat). Qed.

Lemma alloc_meta_nat {R} st (k : mstate -> optr -> Malloc.M R) bail :
  steq (alloc_meta st k bail) (sbind (alloc_meta st kS bS) (KF k bail)).
Proof.
  unfold alloc_meta, bad_answer. nat_auto ltac:(first [apply am_take_nat | apply am_after_brk_nat]).
Qed.

Lemma ta_fin_nat {R} st m mask (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) :
  steq (ta_fin st m mask k) (sbind (ta_fin st m mask kS) (KF k bail)).
Proof. unfold ta_fin. cbv zeta. nat_leaf. Qed.

Lemma try_avail_nat {R} sc st (k : mstate -> Z -> Malloc.M R) bail :
  steq (try_avail sc st k bail) (sbind (try_avail sc st kS bS) (KF k bail)).
Proof.
  unfold try_avail. nat_case; [|nat_leaf]. cbv zeta. nat_case; [apply ta_fin_nat|].
  nat_case.
  - destruct p as [st1 m1]. nat_case. destruct p as [st2 m2]. nat_case.
    eapply steq_trans; [apply activate_group_nat|].
    eapply steq_trans; [| apply steq_sym; eapply steq_trans; [eapply steq_sbind; [apply activate_group_nat| intros ?; apply steq_refl]| apply sbind_assoc]].
    apply steq_sbind; [apply steq_refl|]. intros [[st4 mask]|]; cbn [KF sbind]; [|nat_leaf].
    apply guard_nat; [apply ta_fin_nat| nat_leaf].
  - nat_case; [nat_leaf|]. nat_vis. nat_leaf.
Qed.

Lemma ag_tail_nat {R} lay st sc m p cnt ai (k : mstate -> optr -> Malloc.M R) (bail : Malloc.M R) :
  steq (ag_tail lay st sc m p cnt ai k) (sbind (ag_tail lay st sc m p cnt ai kS) (KF k bail)).
Proof. unfold ag_tail. cbv zeta. nat_leaf. Qed.

Section AG.
Variable lay : layout_hook.
Variable rec : forall R, mstate -> Z -> Z -> (mstate -> Z -> Malloc.M R) -> Malloc.M R -> Malloc.M R.
Hypothesis rec_nat : forall R st sc req (k : mstate -> Z -> Malloc.M R) bail,
  steq (rec R st sc req k bail) (sbind (rec _ st sc req kS bS) (KF k bail)).

Lemma alloc_group_nat {R} st sc req (k : mstate -> optr -> Malloc.M R) bail :
  steq (alloc_group R lay (rec R) st sc req k bail)
       (sbind (alloc_group _ lay (rec _) st sc req kS bS) (KF k bail)).
Proof.
  unfold alloc_group, bad_answer. cbv zeta. nat_call (@alloc_meta_nat); [|nat_leaf].
  nat_case; [|nat_leaf]. nat_case.
  - (* [comment removed for export] *)
    match goal with |- steq _ (sbind (let '(_, _) := ?p in _) _) => destruct p as [cnt' needed] end.
    nat_vis. nat_case; [nat_vis; nat_leaf|]. nat_case.
    + nat_call1 (@free_meta_nat); nat_leaf.
    + nat_case. cbv zeta. apply ag_tail_nat.
  - (* [comment removed for export] *)
    nat_call rec_nat; [|nat_leaf]. nat_case.
    + nat_call1 (@free_meta_nat); nat_leaf.
    + nat_case; [|nat_vis; nat_leaf]. cbv zeta. apply ag_tail_nat.
Qed.
End AG.

Lemma alloc_slot_nat lay fuel : forall R st sc req (k : mstate -> Z -> Malloc.M R) bail,
  steq (alloc_slot lay fuel st sc req k bail) (sbind (alloc_slot lay fuel st sc req kS bS) (KF k bail)).
Proof.
  induction fuel as [|f IH]; intros R st sc req k bail.
  - cbn [alloc_slot]. nat_vis. nat_leaf.
  - cbn [alloc_slot]. nat_call (@try_avail_nat); [|nat_leaf]. nat_case; [nat_leaf|].
    eapply steq_trans; [apply (alloc_group_nat lay (fun R => @alloc_slot R lay f) IH)|].
    eapply steq_trans; [| apply steq_sym; eapply steq_trans; [eapply steq_sbind; [apply (alloc_group_nat lay (fun R => @alloc_slot R lay f) IH)| intros ?; apply steq_refl]| apply sbind_assoc]].
    apply steq_sbind; [apply steq_refl|]. intros [[st2 go]|]; cbn [KF sbind]; [|nat_leaf].
    nat_case; [|nat_leaf]. cbv zeta. nat_call1 (@queue_nat); nat_leaf.
Qed.

End CANSEC3.
