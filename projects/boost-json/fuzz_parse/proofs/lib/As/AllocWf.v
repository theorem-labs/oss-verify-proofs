(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FMapPositive.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~06astate05chunk37Corelib4Init5Logicl03andl02eq37Corelib7Numbers7BinNumsmf1Z0cch_alloc_beg37Corelib4Init9Datatypespa4bool06schunk46Stdlib6ZArith6BinInt1Zs12les13sub07ch_used0aclass_size09kPageSize0aregion_beg09rq_neededs13addpa5falsepa3natpa4truel02ex05ch_rz0ain_primary0arq_primary07sc_sizepa4Somepa6option06as_sec08ch_class0ach_primary0bch_user_beg08class_id0dclass_of_addr0bcompute_req0aget_region03req0h1rg_allocated_user08round_up05rq_rz07rq_size0asc_map_beg0bsc_map_size36Stdlib5Lists4Listihc9nth_errors16modulo06qbatch0bkBatchClass07qb_addr09qb_chunks08qb_count09as_chunks0afind_chunk0h0kChunkHeaderSize0bCQuarantine08ch_state06cstate0bkBatchCount0akBatchSize07qb_size04zlenihc2Inihcafold_right06qcache07qc_list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AllocWf~~~~~~jge8batch_ok08qc_bytespa4list37Corelib5Lists7ListDefjm83mappa3app0fcompact_to_addrjm83seq05as_gq05as_tq0achunk_list06get_pc09pc_chunks0drg_free_arrayihc6filterihc8flat_maps16of_nat0das_n_reservedihc5NoDuppa6lengthjge9qcache_ok09as_qcache07as_qmax0h1kChunksBlockCount08pc_count0erg_mapped_user46Stdlib5FSetscFMapPositivebPositiveMapkmf3keys12ltpa4negbjge8cache_okjgeh0carved_addr_listjge8chunk_okjge9region_ok08as_cache07as_qmin0aas_regions0cch_chunk_beg04ckey0dkMaxCacheSize0bkNumClasses0h2kQuarantineMaxSize0h2kQuarantineMinSize06pclass06regionkmf4finds13muljge2WF09max_count07rz_sizel02or" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Record region_ok (st : astate) (c : Z) : Prop := mkRegionOk {
  ro_alloc_nonneg : 0 <= rg_allocated_user (get_region st c);
  ro_alloc_le     : rg_allocated_user (get_region st c) <= rg_mapped_user (get_region st c);
  ro_mapped_mod   : rg_mapped_user (get_region st c) mod kUserMapSize = 0;
  ro_mapped_bound : rg_mapped_user (get_region st c) + kUserMapSize <= kFreeArrayOffset;
  ro_alloc_mod    : class_size c <> 0 -> rg_allocated_user (get_region st c) mod class_size c = 0;
  ro_tail_small   : class_size c <> 0 -> rg_mapped_user (get_region st c) - rg_allocated_user (get_region st c) < class_size c
                                          + (if rg_allocated_user (get_region st c) =? 0 then kUserMapSize else 0);
  ro_empty        : class_size c = 0 -> rg_mapped_user (get_region st c) = 0;
  ro_numfreed     : rg_num_freed (get_region st c) = zlen (rg_free_array (get_region st c));
  ro_fa_le        : 4 * rg_num_freed (get_region st c) <= rg_mapped_free_array (get_region st c);
  ro_fa_mod       : rg_mapped_free_array (get_region st c) mod kFreeArrayMapSize = 0;
  ro_fa_bound     : rg_mapped_free_array (get_region st c) <= kFreeArraySize;
  ro_fa_elems     : forall cp, In cp (rg_free_array (get_region st c)) ->
                      0 <= cp /\ Z.shiftl cp kCompactPtrScale < rg_allocated_user (get_region st c)
                      /\ class_size c <> 0 /\ Z.shiftl cp kCompactPtrScale mod class_size c = 0
}.

(* [comment removed for export] *)
Record cache_ok (st : astate) (c : Z) : Prop := mkCacheOk {
  co_count     : pc_count (get_pc st c) = zlen (pc_chunks (get_pc st c));
  co_bound     : if as_cache_inited st then pc_count (get_pc st c) <= max_count c else pc_count (get_pc st c) = 0;
  co_elems     : forall cp, In cp (pc_chunks (get_pc st c)) ->
                   0 <= cp /\ Z.shiftl cp kCompactPtrScale < rg_allocated_user (get_region st c)
                   /\ class_size c <> 0 /\ Z.shiftl cp kCompactPtrScale mod class_size c = 0
}.

(* [comment removed for export] *)
Definition chunk_ok : ltac2:(zQ "20!k1!k9>2st$0>2ch$1P") := ltac2:(zQ "ib0!m4!ma!o8!oc!r2!r9!t9!te!u4!ud!v9!hg4!hh0!hhb!hi1!hi9!hif!hj6!hjb!hk2!hke!hla!hm3!hma!hn3!k1!hnb!ho5!hp1!k9!hpe!hq8!hr7!hs4!ht0!ht5!hu9!hv3!hva!ig3!igf!iif!ijc\2st$h9\2ch$hd=1r$i2@1$i0@1$8^1@2$0@2$6+1@1$8^2@2$0@3$1$2@1$8^2@1$i6^1@2$0@3$1$2@1$h2^2@1$i5^1@2$0@3$1$2@1$hc^2@2$d@1$3^2@1$h2^2M4\0$4P@1$hb^2=1c$2@1$ha^2@2$0@3$1$4@1$h4^2$h0@2$0@3$1$2^1@1$he@1$c^2@2$0@3$1$2^1@2$hf^4@1$3^3@2$0@3$1$4@2$h3^4@1$3^3$h0@2$0@3$1$2@2$ia@2$7@1$3^3@2$b^4^1@1$9^1Z@2$0@2$6Z@2$7@1$3^3@2$b^4^1@2$0@2$6@2$d@2$7@1$3^3@2$b^4^1@1$9^1@1$i3@2$i1^4^1@2$6@1$c^2@1$9^1@2$0@3$1$4@1$h4^1$e@2$0@3$1$4@2$h3^3@1$3^2$e@2$h1$f\1i$f@2$h1$5\1h$5@2$0@3$1@1$h7$5@3$i9$5@1$h8^5^2@2$h6$5^1@2$0@3$1$2@1$i7^1@2$7@1$3^4$a@2$0@3$1$2@1$h5^1@1$c^3@3$1$2@1$i8^1@2$d@2$i4@1$h5^1$a$a").

(* [comment removed for export] *)
Definition batch_ok : ltac2:(zQ "20!k1!ik5>2st$0>1b$1P") := ltac2:(zQ "i60!o8!m4!ma!ikd!k9!ila!hhb!t9!hma!im3!ime!hg4!te!in8!ud!io3!iof!hm3!r2!hif!hj6!iq2!k1!iqf!u4!hq8!ir9!hs4!hk2!is1!ise!ita!ik5!ht5!iu3!iu9!iuf!ijc\2st$h6\1b$i0@2$1@3$2$0@1$a^1@2$i2$0@1$9^1@2$1@2$1@2$7+1@1$a^1@2$7@1$a^1$hd@2$1@3$2$h2@2$hc^2@1$5^1$h3@2$1@3$2$0@2$h9^2@1$5^1$3@2$1@3$2$0@2$i5@2$c@1$5^1@2$b^2$3@1$e$3Z@2$1@2$7Z@2$c@1$5^1@2$b^2$3@2$1@2$7@2$6@2$c@1$5^1@2$b^2$3@1$e$3@1$i1@2$hb^2$3@2$1@3$2$0@1$hf^1@2$6$he@5$i4$0$0\1m$0\3acc$0@2$6M8\1x@1$8$4$0@2$f@1$d^4@2$6^2$h0\2ch$4@1$h8^1Z^1Z@1$9^1>1m$0>0@3$i3$0^1@1$9^2@2$h4$4\2ch$4@2$1@3$2@1$8$4@2$f@1$d^5@2$6^3$h0@2$h1$4^1@3$2$ha@1$h7^1$h5").

Definition qcache_ok : ltac2:(zQ "20!k1!ivd>2st$0>1q$1P") := ltac2:(zQ "d0!ik5!o8!jg5!m4!ma!jkb!k1!ita!jl7!ivd!iu9!iuf!hhb\2st$6\1q$9@2$3>1b$0>0@3$a$0^1@1$2^2@2$5^4^2@3$4$1@1$8^1@5$b$1$0\1b$0\3acc$1@2$c@1$7^2^1Z@1$2^1").

(* [comment removed for export] *)
Definition carved_addr_list : ltac2:(zQ "30!jm1!o8!k1>2st$2@1$0$1") := ltac2:(zQ "h70!o8!jnf!jo6!k9!joc!ik5!jg5!hi9!jpd!jq4!jqb!k1!oc!ho5!jr2!jre!hs4!js6!ila!jt1!ju0!jua!jv6\2st$b@3$2$0@4$h5$0$0\1c$0@3$2$0@4$1$0$0@2$4^2^1@1$h3@2$h0^2^1@4$1$0$0@2$4^2^1@1$h1@2$f^2^1@4$1$7$0$h6@2$8N0Ni0@3$2$0@4$1$3$0$c@3$h4$3$d@1$e^1@4$1$5$0$h2@3$2$5@1$6@1$a^1@1$6@1$9^1").

Definition WF : ltac2:(zQ "10!k1>2st$0P") := ltac2:(zQ "k00!m4!o8!ma!k9!ik5!iu9!t9!jr2!jq4!jvf!jqb!hp1!jg5!hn3!r9!iu3!kge!jo6!kh7!hi9!ki0!kid!kj8!jre!hs4!kk1!kl5!im3!jl7!klf!kp6!kpd!hm3!kq2!hma!hj6!jnf!kq9!kr5!ksa!kt6!iq2!ku3!in8!kud!kv6!k1!lg2!ho5!iqf!lh0!ir9!lh6!li5!lj2!lk7!llc!lm4!ig3!lmc!ju0!jua!ijc!ln4\2st$ie@2$0>1c$1>0@2$0@2$6Z^1@2$hf^1$j5@2$0@2$i8^3^2@2$i5^3^2@2$0@2$h0$1@1$i6^1@2$0>2ch$3>0@3$5$3^1@1$7^2@2$i7^3^2@2$0>2ch$3>3ch'$3>0@3$5$3^2@1$7^3>0@3$5$3^2@1$7^4>0@3$2$1@1$b^4@1$b^3@3$2$3^5^4@2$0@3$2$1@2$f$3@3$jc$3\2ch$3@1$i1@1$j0^1@1$7^1@2$f$e@1$d^1@2$0@2$h0$1@4$i4$e$1$ja@1$d^1@2$0@2$6@2$f$e@1$d^1@1$9^1@2$0@2$0@3$2$1@2$je@1$9^1$h9Z@2$0@2$6Z@1$9^1@2$6@1$9^1@2$jf+jf$h9@2$0@2$h4^1@1$a^1@2$0@2$h4^1@1$8^1@2$0@2$6@1$hc@1$a^1@1$h5^1@2$0@2$6@1$hc@1$8^1@1$h6^1@2$0@2$h0$1@4$jd$4$1$hb@3$h1$4@1$c@1$a^1@1$c@1$8^1@2$0>2ch$3>0@3$5$3^1@1$7^2>0@3$2$j3@1$j1^2$i9@2$i3$4\1b$4@2$0@3$5$4^1@3$h1$4@1$c@1$a^5@1$c@1$8^5@3$5$1@1$if^4@1$hb^1@2$0@3$2$1@1$hd@2$h8^1ZZ@2$0@3$2$1@1$hd@2$h8^1+hfZ@2$0@3$2$1@1$ha@2$h7^1ZZ@2$0@3$2$1@1$ha@2$h7^1+hfZ@2$0@3$2$h3@2$h2$j9@1$id^1Ni0@2$0@3$2$h3@2$h2$j8@1$ia^1Ni0@2$0@3$2$1@1$h6^1$j6@2$0@3$2$1@1$ic^1$j7@2$0@3$2$1@1$h5^1$j4>1k$he>1x$3>0@3$2@1$i2$3@3$jb$3^2@1$ib^3@2$i0$3^1@2$0@3$2$he^3@1$j2@1$b^2@2$hfZ@1$b^2").

(* [comment removed for export] *)
Lemma WF_region : ltac2:(zQ "80!m4!o8!lna!kt6!k1!li5!t9!kpd>2st$4>1c$1>0@1$2^2>0@2$0@2$6Z^2@2$7^2$5@2$3^4^3").
Proof. intros st c W Hc. destruct W as [H _]. apply (H c Hc). Qed.
Lemma WF_cache : ltac2:(zQ "80!m4!o8!lna!kq9!k1!li5!t9!kpd>2st$4>1c$1>0@1$2^2>0@2$0@2$6Z^2@2$7^2$5@2$3^4^3").
Proof. intros st c W Hc. destruct W as [H _]. apply (H c Hc). Qed.
Lemma WF_chunk : ltac2:(zQ "60!k9!lna!ksa!k1!jr2!iu9>2st$3>2ch$0>0@1$1^2>0@3$5$0^2@1$4^3@2$2^4^3").
Proof. intros st ch W Hin. ndestruct W as (_ & _ & H & _). apply H, Hin. Qed.
Lemma WF_tq : ltac2:(zQ "40!lna!ki0!jqb!k1>2st$3>0@1$0^1@2$1^2@1$2^2").
Proof. intros st W. ndestruct W as (_ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma WF_gq : ltac2:(zQ "40!lna!ki0!jq4!k1>2st$3>0@1$0^1@2$1^2@1$2^2").
Proof. intros st W. ndestruct W as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma WF_batch : ltac2:(zQ "90!ik5!jg5!jo6!lna!jkb!jq4!jqb!k1!iu9>2st$7>1b$0>0@1$3^2>0@3$8$0^2@3$2$0@1$1@1$6^3@1$1@1$5^3@2$4^4^3").
Proof.
  intros st b W Hin. apply in_app_iff in Hin as [Hin|Hin]; [apply (proj1 (WF_tq st W)) | apply (proj1 (WF_gq st W))]; exact Hin.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac eval_class_consts :=
  repeat match goal with
  | |- context [class_size ?k] => let v := eval vm_compute in (class_size k) in change (class_size k) with v
  | |- context [max_count ?k] => let v := eval vm_compute in (max_count k) in change (max_count k) with v
  end.
Ltac class_cases c :=
  let rec go k := lazymatch k with
    | 32%Z => lia
    | _ => let k' := eval compute in (k + 1)%Z in
           destruct (Z.eq_dec c k) as [-> | ?]; [eval_class_consts | go k']
    end in go 0%Z.
(* [comment removed for export] *)

Lemma class_size_table_facts : ltac2:(zQ "80!t9!m4!ud!lo0!o8!ma!ijc!kpd>1c$4>0@2$1@2$0Z^1@2$7^1+i0@2$1@2$1@2$0Z@1$2^2@2$0@1$2^2+hggg0@2$1@3$5$4@2$6@1$2^2+i0Z@2$1>0@2$0+1^2@2$0+i0@1$2^3@2$1@2$1@2$0Z@1$3^2@2$0@1$3^2+h0@2$1>0@2$0+1^2@2$0+2@1$3^3@3$5$4@2$6@1$3^2+2Z").
Proof. intros c Hc. class_cases c; repeat split; intros; try reflexivity; lia. Qed.

Lemma rz_size_facts : ltac2:(zQ "70!lob!o8!ma!lp4!m4!t9!ijc>1n$1@2$4@2$4@2$5+h0@1$0^1@2$5@1$0^1+og0@2$4@3$2$1@2$6@1$0^1+h0Z@2$3@3$2$1@1$0^1+h0@2$3@3$2$1@1$0^1+i0@2$3@3$2$1@1$0^1+k0@2$3@3$2$1@1$0^1+o0@2$3@3$2$1@1$0^1+hg0@2$3@3$2$1@1$0^1+ig0@2$3@3$2$1@1$0^1+kg0@3$2$1@1$0^1+og0").
Proof.
  intros n. unfold rz_size, rz_log, kMinRedzoneLog, kMaxRedzoneLog.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; cbn; repeat split; try reflexivity; lia.
Qed.
