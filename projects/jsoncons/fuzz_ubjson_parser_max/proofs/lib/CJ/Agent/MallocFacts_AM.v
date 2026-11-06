(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocRep MallocTree MallocFacts_B.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_MallocFacts_AM () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocFacts_AM.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.ZArith.BinInt.Z."], [["1fst"; "2eq"; "2not"; "3N"; "3Z"; "4AMpre_g"; "5RKBrk"; "5RKGroup"; "5mstate"; "5new_region"; "5rkind"; "5set_tick"; "5step_seq"; "6lt"; "0base"; "0k"]; ["0len"; "0resv"; "0st"; "0t"; "0xa"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition fresh_above (st : mstate) (rid : N) (o : Z) : Prop :=
forall q, fst q = rid -> o <= snd q -> (s_areas st) !! q = None /\ (s_metas st) !! q = None.
Record AMpre_g {resv : list (Z * Z)} (st : mstate) : Prop := mkAMP {
amp_secret : 0 <= c_secret (ctx st) < 2^64;
amp_init : c_init_done (ctx st) = 0 \/ c_init_done (ctx st) = 1;
amp_s_secret : s_secret st = secret_val;
amp_count : 0 <= c_avail_meta_count (ctx st) <= NSLOTS;
amp_acount : 0 <= c_avail_meta_area_count (ctx st) < 2^40;
amp_shift : 0 <= c_meta_alloc_shift (ctx st) <= 38;
amp_reserved : s_reserved st = resv;
amp_links : ci_links_t st;
amp_fmh : forall h, c_free_meta_head (ctx st) = Some h -> m_next (get_meta_rec st h) <> None /\ m_mem (get_meta_rec st h) = None;
amp_fml : forall g, m_mem (get_meta_rec st g) = None -> m_next (get_meta_rec st g) <> None ->
m_set_prev None (m_set_next None (get_meta_rec st g)) = meta0
/\ (forall nx, m_next (get_meta_rec st g) = Some nx -> m_mem (get_meta_rec st nx) = None)
/\ (forall pv, m_prev (get_meta_rec st g) = Some pv -> m_mem (get_meta_rec st pv) = None);
amp_mkeys : forall q mr, (s_metas st) !! q = Some mr -> meta_slot st q;
amp_avail : c_avail_meta_count (ctx st) <> 0 ->
exists a ar k, (s_areas st) !! a = Some ar /\ c_avail_meta (ctx st) = Some (aadd a (AREA_HDR + META_SIZE * k))
/\ 0 <= k /\ k + c_avail_meta_count (ctx st) <= NSLOTS
/\ (s_metas st) !! (aadd a (AREA_HDR + META_SIZE * k)) = None;
amp_tail : forall tl, c_meta_area_tail (ctx st) = Some tl -> is_Some ((s_areas st) !! tl);
amp_avail_areas : c_avail_meta_area_count (ctx st) <> 0 ->
exists p r, c_avail_meta_areas (ctx st) = Some p /\ (s_regions st) !! (fst p) = Some r /\ r_kind r <> RKGroup
/\ snd p mod PGSZ = 0 /\ 0 <= snd p /\ lr_lo r <= r_base r + snd p
/\ snd p + PGSZ * c_avail_meta_area_count (ctx st) <= round_up_pg (r_len r)
/\ fresh_above st (fst p) (snd p);
amp_rpos : forall q rq, (s_regions st) !! q = Some rq -> 0 < r_len rq;
amp_brk : match c_brk (ctx st) with
| BrkLive rid off => exists r, (s_regions st) !! rid = Some r /\ r_kind r = RKBrk /\ r_len r = off
/\ off mod PGSZ = 0 /\ PGSZ <= off /\ fresh_above st rid off
/\ (forall q rq, (s_regions st) !! q = Some rq -> r_kind rq = RKBrk -> q = rid)
| _ => True
end;
amp_ptrs : ptrs_in (fun rid => (rid < s_next_rid st)%N) st
/\ (forall rid, (s_next_rid st <= rid)%N -> (s_regions st) !! rid = None /\ (s_shadow st) !! rid = None)
}.
Definition am_pre_g (resv : list (Z * Z)) : mstate -> Prop := @AMpre_g resv.
Section GENERIC.
Context {resv : list (Z * Z)}.
Local Notation AMpreR := (@AMpre_g resv).
Lemma AMpre_set_tick : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_AM "='8'3'5vAr2%3221&;r3%2241%7261p051pQ8:1pQ6<1").
Proof. intros st t. intros H. destruct H. split; cbn; try assumption. destruct amp_links0; split; cbn; assumption. Qed.
Lemma AMpre_step_seq : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_AM ";'8'5vAr1%3221&<r2%211%7261p051pQ6:1").
Proof. intros st.
intros H. unfold step_seq. destruct H as [A1 A2 A3 A4 A5 A6 A7 [L1 L2 L3 L4] A9 A10 A11 A12 A13 A14 A15 A16 [P1 P2]].
destruct (c_seq (ctx st) =? 255); (split; cbn; try assumption; [split; cbn; assumption | split; [exact P1| exact P2]]).
Qed.
Section SE.
Local Abbreviation SEC_T_AMpre_new_region := (ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_AM "Q0'8':'4'5vAr4%3221&=zr2%3221&2'1r5(6%33>21%511&0'3&9r6r7%3429A1%63G51%E2D1p091p0@1p0E1pQ2J1pNK1pQ0M1pQ6O1")) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_AMpre_new_region) 0%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SEC_T_AMpre_new_region) 1%nat 0%nat).
Variable base : ltac:(sec_ty2 constr:(SEC_T_AMpre_new_region) 2%nat 0%nat).
Variable len : ltac:(sec_ty2 constr:(SEC_T_AMpre_new_region) 3%nat 0%nat).
Lemma AMpre_new_region : ltac:(sec_stmt2 constr:(SEC_T_AMpre_new_region) 4%nat 0%nat).
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
End SE.
Lemma AMpre_big_call : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocFacts_AM "N'8'3'4'5vAr4%3221&=zr2%3221&<&0&9(7r3&;r5r6%3221%746?51%93ED1%;11%D2C1p0>1p0C1pQ2H1pQ:I1pQ8K1pQ6M1").
Proof. intros st t xa len. intros H LEN. apply AMpre_step_seq, AMpre_new_region; [apply AMpre_set_tick; exact H| exact LEN| discriminate]. Qed.
End GENERIC.
End CEIL_WRAP_1.
