(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Agent Require Import MallocRep_u5 MallocTree_u5 MallocFacts_B_u5.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
Definition fresh_above (st : mstate) (rid : N) (o : Z) : Prop :=
  forall q, fst q = rid -> o <= snd q -> (s_areas st) !! q = None /\ (s_metas st) !! q = None.

(* [comment removed for export] *)
Record AMpre_g {resv : list (Z * Z)} (st : mstate) : Prop := mkAMP {
  (* [comment removed for export] *)
  amp_secret : 0 <= c_secret (ctx st) < 2^64;
  amp_init : c_init_done (ctx st) = 0 \/ c_init_done (ctx st) = 1;
  amp_s_secret : s_secret st = secret_val;   (* [comment removed for export] *)
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
             /\ (forall rid, (s_next_rid st <= rid)%N -> (s_regions st) !! rid = None /\ (s_shadow st) !! rid = None)
}.
(* [comment removed for export] *)
Definition am_pre_g (resv : list (Z * Z)) : mstate -> Prop := @AMpre_g resv.
(* [comment removed for export] *)

Section GENERIC.
Context {resv : list (Z * Z)}.
Local Notation AMpreR := (@AMpre_g resv).

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
  intros H LEN NB. destruct H as [A1 A2 A3 A4 A5 A6 A7 [L1 L2 L3 L4] A9 A10 A11 A12 A13 A14 A15 A16 [P1 P2]].
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
Qed.

(* [comment removed for export] *)
Lemma AMpre_big_call st t xa len : AMpreR st -> 0 < len -> AMpreR (step_seq (fst (new_region RKGroup xa len (set_tick t st)))).
Proof. intros H LEN. apply AMpre_step_seq, AMpre_new_region; [apply AMpre_set_tick; exact H| exact LEN| discriminate]. Qed.
End GENERIC.
End CEIL_WRAP_1.

