(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocRep MallocTree MallocFacts_B.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01N01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~hf6mstate35stdpp7numbers1Nm66eq_dec35stdpp7numbers1Zo06eq_dechf4areahf4metahf4aptr25stdpp9countableqfbN_countableqfbZ_countableqfeprod_countable25stdpp9decidableudbprod_eq_dec37Corelib4Init9Datatypeshgc4prod37Corelib4Init5Logichic2eqhgc4Nonehgc6option25stdpp4basehl86lookup25stdpp4gmaphme4gmaphmebgmap_lookuphgc3fsthgc3sndhic3andhf7s_areashf7s_metas46Stdlib6ZArith6BinInt1Zhra2lehgc4list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgenteMallocFacts_AM~~~~~~hu07AMpre_ghf8set_tickhf8step_seqhf5rkindhic3nothf5RKBrkhfanew_regionhra2lthf7RKGroup" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Definition fresh_above : ltac2:(zQ "30!h9!hc!ld>2st$2>3rid$0>1o$1P") := ltac2:(zQ "h90!h9!hc!n7!p1!pa!q1!q8!s0!se!tc!ve!hi4!hk0!hk6!hke!hm4!hna!ho2!hp1!hp8!hpf!ld!hq6!hr0!ht2\2st$h5\3rid$0\1o$1>1q@2$b$0$1>0@3$c$0@3$h2$0$1^1^3>0@2$h8^3@3$h3$0$1^2@2$h4@3$c@1$e$4@6$f@2$b$0$1$4@4$h0$6@4$a$0$2$1$3@6$9$0$2$7$1$3$8$4@4$h1$6@4$a$0$2$1$3@6$9$0$2$7$1$3$8$4^3@1$h6^6@1$d$4@3$c@1$e$5@6$f@2$b$0$1$5@4$h0$6@4$a$0$2$1$3@6$9$0$2$7$1$3$8$5@4$h1$6@4$a$0$2$1$3@6$9$0$2$7$1$3$8$5^3@1$h7^6@1$d$5").

(* [comment removed for export] *)
Record AMpre_g {resv : list (Z * Z)} (st : mstate) : Prop := mkAMP {
  (* [comment removed for export] *)
  amp_secret : 0 <= c_secret (ctx st) < 2^64;
  amp_init : c_init_done (ctx st) = 0 \/ c_init_done (ctx st) = 1;
  amp_s_secret : s_secret st = hsecret;       (* [comment removed for export] *)
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

End HCW.


Notation AMpre := (@AMpre_g _ agent_reserved).
Section HCW2.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Definition am_pre_g : ltac2:(zQ "40!hc!ht8!hi4!ld>4resv@1$1@2$2$0$0>0$3P") := ltac2:(zQ "40!hc!ht8!hi4!ii7\4resv@1$1@2$2$0$0@2$3?4HSEC^1").

End HCW2.

Notation am_pre := (am_pre_g agent_reserved).

Section HCW3.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Section GENERIC.
Context {resv : list (Z * Z)}.
Local Notation AMpreR := (@AMpre_g _ resv).

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma AMpre_set_tick : ltac2:(zQ "40!ii7!h9!ld!ij2>2st$2>1t$1>0@3$0?4HSEC?4resv^2@3$0?4HSEC?4resv@2$3^2^3").
Proof. intros st t. intros H. destruct H. split; cbn; try assumption. destruct amp_links0; split; cbn; assumption. Qed.

Lemma AMpre_step_seq : ltac2:(zQ "30!ii7!ld!ijd>2st$1>0@3$0?4HSEC?4resv^1@3$0?4HSEC?4resv@1$2^2").
Proof. intros st.
  intros H. unfold step_seq. destruct H as [A1 A2 A3 A4 A5 A6 A7 [L1 L2 L3 L4] A9 A10 A11 A12 A13 A14 A15 A16 [P1 P2]].
  destruct (c_seq (ctx st) =? 255); (split; cbn; try assumption; [split; cbn; assumption | split; [exact P1| exact P2]]).
Qed.

Lemma AMpre_new_region : ltac2:(zQ "b0!hc!ii7!ld!ik8!hp1!hk0!il0!h9!il7!ilf!imc>2st$2>1k$3>4base$0>3len$0>0@3$1?4HSEC?4resv^4>0@2$aZ^2>0@1$6@3$5$3^5$8@3$1?4HSEC?4resv@3$4$2$7@4$9^6^5^4^7").
Proof. intros st k base len.
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
  - intros AC. ndestruct (A14 AC) as (p & r & E1 & E2 & REST). exists p, r. split; [exact E1|]. split; [| exact REST].
    rewrite LK. destruct (decide (fst p = rid)) as [E|NE]; [rewrite E, FRr in E2; discriminate| exact E2].
  - intros q rq Hq. rewrite LK in Hq. destruct (decide (q = rid)) as [->|NE]; [inversion Hq; subst; cbn; lia| exact (A15 q rq Hq)].
  - unfold ctx in A16. destruct (c_brk (s_ctx st)) as [| |brid boff]; [exact I| exact I|]. ndestruct A16 as (r & Hr & K1 & K2 & K3 & K4 & K5 & UNQ).
    exists r. rewrite LK. destruct (decide (brid = rid)) as [E|NE]; [rewrite E, FRr in Hr; discriminate|].
    split; [exact Hr|]. split; [exact K1|]. split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K5|].
    intros q rq Hq Kq. rewrite LK in Hq. destruct (decide (q = rid)) as [->|NE2]; [inversion Hq; subst; cbn in Kq; congruence|]. exact (UNQ q rq Hq Kq).
  - split.
    + eapply ptrs_in_mono; [| exact P1]. intros q Hq. cbn in Hq |- *. unfold rid. lia.
    + intros q Hq. rewrite LK. destruct (decide (q = rid)) as [->|NE]; [unfold rid in Hq; lia|]. apply P2. unfold rid in Hq. lia.
Qed.

(* [comment removed for export] *)
Lemma AMpre_big_call : ltac2:(zQ "a0!h9!hc!ii7!ld!hp1!in2!ilf!ij2!ijd!imc>2st$3>1t$0>2xa$1>3len$1>0@3$2?4HSEC?4resv^4>0@2$9Z^2@3$2?4HSEC?4resv@1$8@3$4$3$0@4$6$5^4^3@2$7^5^6").
Proof. intros st t xa len. intros H LEN. apply AMpre_step_seq, AMpre_new_region; [apply AMpre_set_tick; exact H| exact LEN| discriminate]. Qed.
End GENERIC.

End HCW3.

