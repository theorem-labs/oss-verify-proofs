(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (4 recorded proofs replaced by written proofs (AMpre_set_tick, AMpre_step_seq, AMpre_new_region and 1 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep MallocTree MallocFacts_B.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MallocFacts_AM () := "C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I35stdpp9countable9Countable00C47Corelib4Init9Datatypes3fstC35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4base4fmapC35stdpp4base6lookupC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C35stdpp4base7is_SomeI35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap4gmap00C35stdpp8fin_maps:map_eq_iffC35stdpp8fin_maps@lookup_insert_eqC47Corelib4Init5Logic8eq_ind_rC35stdpp8fin_maps@lookup_insert_neC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_foldi59OSSVerify5KrLib6Malloc>MallocFacts_AM7AMpre_g00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8set_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_secretC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib4Spec6Malloc;c_init_doneC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init5Logic2or00C59OSSVerify5KrLib4Spec6Malloc8s_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_countC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib4Spec6MallocGc_avail_meta_area_countC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C59OSSVerify5KrLib4Spec6MallocBc_meta_alloc_shiftC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc=MallocFacts_B:ci_links_t00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_free_meta_headC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic3notC59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C59OSSVerify5KrLib4Spec6Malloc:m_set_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_set_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_prevC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep9meta_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<c_avail_metaC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib6Malloc9MallocRep5lr_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc>MallocFacts_AM;fresh_aboveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2ltC59OSSVerify5KrLib6Malloc:MallocTree7ptrs_inC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2leC59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffK59OSSVerify5KrLib6Malloc=MallocFacts_B:ci_links_t01C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib6Malloc>MallocFacts_AM7AMpre_g01C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib4Spec6Malloc6NSLOTSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5meta0C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countableC59OSSVerify5KrLib4Spec6Malloc8AREA_HDRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9META_SIZEC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc8brkstate00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K59OSSVerify5KrLib4Spec6Malloc5rkind01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_seqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC35stdpp4base5emptyC59OSSVerify5KrLib4Spec6MallocAset_unmap_seq_mapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7set_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7upd_ctxC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C59OSSVerify5KrLib4Spec6Malloc8step_seqC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:new_regionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z9is_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revI47Corelib4Init6Specif7sumbool00K59OSSVerify5KrLib4Spec6Malloc6region01C1?~~~~~~~~~~~~~~~C35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap;gmap_finmapC47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic9False_indC56Stdlib6NArith6BinNat1N4succC59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;set_regionsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indK47Corelib4Init5Logic2ex01C47Corelib4Init5Logic7f_equalC56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03C59OSSVerify5KrLib6Malloc:MallocTree<ptrs_in_monoC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes4prod01C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C35stdpp4base:decide_relC35stdpp4base6decideC35stdpp4base6insertC59OSSVerify5KrLib4Spec6Malloc<set_next_ridC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses5mkappC56Stdlib6ZArith4Znat3N2Z6inj_leK46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith4Znat3N2Z8inj_succC56Stdlib6ZArith4Znat3N2Z6inj_ltI46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01c59OSSVerify5KrLib6Malloc>MallocFacts_AM>AMpre_set_tickC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc>MallocFacts_AM@AMpre_new_regionC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc>MallocFacts_AM>AMpre_step_seqC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition fresh_above (st : mstate) (rid : N) (o : Z) : Prop :=
  forall q, fst q = rid -> o <= snd q -> (s_areas st) !! q = None /\ (s_metas st) !! q = None.

(* [comment removed for export] *)
Record AMpre_g {resv : list (Z * Z)} (st : mstate) : Prop := mkAMP {
  (* [comment removed for export] *)
  amp_secret : 0 <= c_secret (ctx st) < 2^64;
  amp_init : c_init_done (ctx st) = 0 \/ c_init_done (ctx st) = 1;
  amp_s_secret : s_secret st = 0;       (* [comment removed for export] *)
  amp_count : 0 <= c_avail_meta_count (ctx st) <= NSLOTS;
  amp_acount : 0 <= c_avail_meta_area_count (ctx st) < 2^40;
  amp_shift : 0 <= c_meta_alloc_shift (ctx st) <= 38;   (* [comment removed for export] *)
  amp_reserved : s_reserved st = resv;
  (* [comment removed for export] *)
  amp_links : ci_links_t st;
  amp_fmh : forall h, c_free_meta_head (ctx st) = Some h -> m_next (get_meta_rec st h) <> None /\ m_mem (get_meta_rec st h) = None;
  amp_fml : forall g, m_mem (get_meta_rec st g) = None -> m_next (get_meta_rec st g) <> None ->
              m_set_prev None (m_set_next None (get_meta_rec st g)) = meta0
              /\ (forall nx, m_next (get_meta_rec st g) = Some nx -> m_mem (get_meta_rec st nx) = None)
              /\ (forall pv, m_prev (get_meta_rec st g) = Some pv -> m_mem (get_meta_rec st pv) = None);
  (* [comment removed for export] *)
  amp_mkeys : forall q mr, (s_metas st) !! q = Some mr -> meta_slot st q;
  (* [comment removed for export] *)
  amp_avail : c_avail_meta_count (ctx st) <> 0 ->
      exists a ar k, (s_areas st) !! a = Some ar /\ c_avail_meta (ctx st) = Some (aadd a (AREA_HDR + META_SIZE * k))
                     /\ 0 <= k /\ k + c_avail_meta_count (ctx st) <= NSLOTS
                     /\ (s_metas st) !! (aadd a (AREA_HDR + META_SIZE * k)) = None;
  (* [comment removed for export] *)
  amp_tail : forall tl, c_meta_area_tail (ctx st) = Some tl -> is_Some ((s_areas st) !! tl);
  (* [comment removed for export] *)
  amp_avail_areas : c_avail_meta_area_count (ctx st) <> 0 ->
      exists p r, c_avail_meta_areas (ctx st) = Some p /\ (s_regions st) !! (fst p) = Some r /\ r_kind r <> RKGroup
                  /\ snd p mod PGSZ = 0 /\ 0 <= snd p /\ lr_lo r <= r_base r + snd p
                  /\ snd p + PGSZ * c_avail_meta_area_count (ctx st) <= round_up_pg (r_len r)
                  /\ fresh_above st (fst p) (snd p);
  (* [comment removed for export] *)
  amp_rpos : forall q rq, (s_regions st) !! q = Some rq -> 0 < r_len rq;
  (* [comment removed for export] *)
  amp_brk : match c_brk (ctx st) with
            | BrkLive rid off => exists r, (s_regions st) !! rid = Some r /\ r_kind r = RKBrk /\ r_len r = off
                                           /\ off mod PGSZ = 0 /\ PGSZ <= off /\ fresh_above st rid off
                                           /\ (forall q rq, (s_regions st) !! q = Some rq -> r_kind rq = RKBrk -> q = rid)
            | _ => True
            end;
  (* [comment removed for export] *)
  amp_ptrs : ptrs_in (fun rid => (rid < s_next_rid st)%N) st
             /\ (forall rid, (s_next_rid st <= rid)%N -> (s_regions st) !! rid = None /\ (s_shadow st) !! rid = None);
  (* [comment removed for export] *)
  amp_s_atop : s_atop st = ATOP
}.

End CANSEC1.
Notation AMpre := (@AMpre_g _ agent_reserved).
Section CANSEC2. Context {rc : runConstT}.
Definition am_pre_g (resv : list (Z * Z)) : mstate -> Prop := @AMpre_g _ resv.
End CANSEC2.
Notation am_pre := (am_pre_g agent_reserved).

Section CANSEC3. Context {rc : runConstT}.
Section GENERIC.
Context {resv : list (Z * Z)}.
Local Notation AMpreR := (@AMpre_g _ resv).

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma AMpre_set_tick st t : AMpreR st -> AMpreR (set_tick t st).
Proof. intros H. destruct H. split; cbn; try assumption. destruct amp_links0; split; cbn; assumption. Qed.

Lemma AMpre_step_seq st : AMpreR st -> AMpreR (step_seq st).
Proof.
  intros H. unfold step_seq. destruct H as [A1 A2 A3 A4 A5 A6 A7 [L1 L2 L3 L4] A9 A10 A11 A12 A13 A14 A15 A16 [P1 P2]].
  destruct (c_seq (ctx st) =? 255); (split; cbn; try assumption; [split; cbn; assumption | split; [exact P1| exact P2]]).
Qed.

Lemma AMpre_new_region st k base len : AMpreR st -> 0 < len -> k <> RKBrk -> AMpreR (fst (new_region k base len st)).
Proof.
  intros H LEN NB. destruct H as [A1 A2 A3 A4 A5 A6 A7 [L1 L2 L3 L4] A9 A10 A11 A12 A13 A14 A15 A16 [P1 P2] AT].
  destruct (P2 (s_next_rid st) ltac:(lia)) as [FRr FRs].
  unfold new_region. cbn [fst]. set (rid := s_next_rid st).
  assert (LK : forall q, (<[rid := mkRegion k base len]> (s_regions st)) !! q = if decide (q = rid) then Some (mkRegion k base len) else (s_regions st) !! q).
  { intros q. destruct (decide (q = rid)) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity. }
  assert (MSs : forall q, meta_slot st q -> meta_slot (set_next_rid (N.succ rid) (set_regions (<[rid:=mkRegion k base len]> (s_regions st)) st)) q).
  { intros q Hq. exact Hq. }
  split; cbn -[insert].
  - exact A1. - exact A2. - exact A3. - exact A4. - exact A5. - exact A6. - exact A7.
  - split; cbn; [exact L1| exact L2| exact L3| exact L4].
  - exact A9. - exact A10. - exact A11. - exact A12. - exact A13.
  - intros AC. destruct (A14 AC) as (p & r & E1 & E2 & REST). exists p, r. split; [exact E1|]. split; [| exact REST].
    rewrite LK. destruct (decide (fst p = rid)) as [E|NE]; [rewrite E, FRr in E2; discriminate| exact E2].
  - intros q rq Hq. rewrite LK in Hq. destruct (decide (q = rid)) as [->|NE]; [inversion Hq; subst; cbn; lia| exact (A15 q rq Hq)].
  - unfold ctx in A16. destruct (c_brk (s_ctx st)) as [| |brid boff]; [exact I| exact I|]. destruct A16 as (r & Hr & K1 & K2 & K3 & K4 & K5 & UNQ).
    exists r. rewrite LK. destruct (decide (brid = rid)) as [E|NE]; [rewrite E, FRr in Hr; discriminate|].
    split; [exact Hr|]. split; [exact K1|]. split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K5|].
    intros q rq Hq Kq. rewrite LK in Hq. destruct (decide (q = rid)) as [->|NE2]; [inversion Hq; subst; cbn in Kq; congruence|]. exact (UNQ q rq Hq Kq).
  - split.
    + eapply ptrs_in_mono; [| exact P1]. intros q Hq. cbn in Hq |- *. unfold rid. lia.
    + intros q Hq. rewrite LK. destruct (decide (q = rid)) as [->|NE]; [unfold rid in Hq; lia|]. apply P2. unfold rid in Hq. lia.
  - exact AT.
Qed.

(* [comment removed for export] *)
Lemma AMpre_big_call st t xa len : AMpreR st -> 0 < len -> AMpreR (step_seq (fst (new_region RKGroup xa len (set_tick t st)))).
Proof. intros H LEN. apply AMpre_step_seq, AMpre_new_region; [apply AMpre_set_tick; exact H| exact LEN| discriminate]. Qed.
End GENERIC.


End CANSEC3.
