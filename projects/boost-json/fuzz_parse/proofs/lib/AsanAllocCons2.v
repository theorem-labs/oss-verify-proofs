(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FMapPositive.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel AsanAllocCons.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import AllocWf AllocKit AG_MallocModel AG_WFHit CidBits AllocBudget.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~06astate37Corelib4Init5Logick92eq37Corelib7Numbers7BinNumsm21Z0cas_ptr_array0cas_space_begk93and69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocCons2~~~~~~q14sbpa69OSSVerify6Proofsaboost_jsonafuzz_parse3libdAsanAllocCons~~~~~~u99same_core0h3ensure_cache_inited37Corelib4Init9Datatypeshkb4list06effecthkb4prodhkb4Somehkb6optionhkb4pair0dpoison_shadowhkb6lengthhkb3nat0aas_regions0bkNumClasses0h3populate_free_array06region46Stdlib6ZArith6BinInt1Zhuc2lehuc2lt0h2get_from_allocator0bcache_alloc0dcache_dealloc0h0large_deallocate0acb_recycle0fcb_recycle_list0ado_recycle06qbatch0h2quarantine_recycle0h0quarantine_drain0h2quarantine_enqueue05chunk0equarantine_put79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AllocWf~~~~~~it92WF0cam_free_full" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sbpa : ltac2:(zQ "10!k1>2st$0>3st'$0P") := ltac2:(zQ "60!ld!nb!nf!od!k1!pb\2st$4\3st'$4@2$5@3$0$1@1$3^1@1$3^2@3$0$1@1$2^1@1$2^2").
Lemma sbpa_refl : ltac2:(zQ "20!u2!k1>2st$1@2$0^1^1"). Proof. intros st. split; reflexivity. Qed.
Lemma sbpa_trans : ltac2:(zQ "20!u2!k1>1a$1>1b$1>1c$1>0@2$0^3^2>0@2$0^3^2@2$0^5^3").
Proof. intros a b c [A1 A2] [B1 B2]. split; congruence. Qed.
Lemma sbpa_of_core : ltac2:(zQ "30!k1!hi9!u2>1a$0>1b$0>0@2$1^2^1@2$2^2^3").
Proof. intros a b C. ndestruct C as (S & P & _). split; [exact S| exact P]. Qed.
Lemma eci_sbpa : ltac2:(zQ "30!u2!k1!hj5>2st$1@2$0^1@1$2^1").
Proof. intros st. unfold sbpa, ensure_cache_inited. destruct (as_cache_inited st); split; reflexivity. Qed.

Lemma poison_shadow_sbpa : ltac2:(zQ "b0!k1!hm3!hmb!nb!hn3!hnb!ho3!hod!ld!u2!hp5>2st$0>1a$3>1n$3>1v$3>3st'$0>2ev@1$1$2>0@3$8@1$6@2$4$0@1$1$2@4$a^6^5^4^3@2$5@2$4$0@1$1$2@4$7$0@1$1$2^2^1@2$9^7^3").
Proof. intros st a n v st' ev H. exact (sbpa_of_core _ _ (poison_shadow_core _ _ _ _ _ _ H)). Qed.

Lemma populate_sbpa : ltac2:(zQ "h30!k1!hm3!hmb!hn3!ld!nb!hnb!hq4!hqe!ho3!hod!pb!u2!hr5!hs1!hse!hu4!ig4!iga>2st$0>1c$5>3req$5>3st'$0>2ev@1$1$2>0@3$4$8@2$7$h0@1$d^5Ni0>0@2$b@2$h1Z^5@2$h2^5$e>0@3$4@1$9@2$3$0@1$1$2@3$f^7^6^5@2$6@2$3$0@1$1$2@4$a$0@1$1$2^4^3@2$c^8^5").
Proof.
  intros st c req st' ev L Hc H. ndestruct (populate_free_array_core st c req st' ev L Hc H) as (mu' & mfa' & C & _). cbv zeta in C.
  exact (sbpa_of_core _ _ C).
Qed.

Lemma get_from_allocator_sbpa : ltac2:(zQ "h30!hm3!nb!k1!hn3!hmb!hod!ld!hnb!hq4!hqe!ho3!pb!u2!hr5!ih0!hs1!hu4!ig4!iga>2st$2>1c$1>1n$1>3st'$2>5taken@1$0$1>2ev@1$0$4>0@3$6$9@2$8$h0@1$d^6Ni0>0@2$b@2$h1Z^6@2$h2^6$f>0@3$6@1$a@2$3@2$3$2@1$0$1@1$0$4@3$e^8^7^6@2$7@2$3@2$3$2@1$0$1@1$0$4@4$5@2$3$2@1$0$1@1$0$4@4$5$2@1$0$1^5^4^3@2$c^9^6").
Proof.
  intros st c n st' taken ev L Hc H. ndestruct (get_from_allocator_core st c n st' taken ev H) as (st1 & A & _ & ->).
  destruct A as [[-> _]|(_ & (ev1 & P & _))]; [split; reflexivity|].
  exact (populate_sbpa st c _ st1 ev1 L Hc P).
Qed.

Lemma cache_alloc_sbpa : ltac2:(zQ "h00!nb!k1!hn3!hm3!hmb!hod!ld!hnb!hq4!hqe!ho3!u2!hr5!ii5!hu4!ig4>2st$1>1c$0>3st'$1>1a$0>2ev@1$3$4>0@3$6$9@2$8$e@1$c^5Ni0>0@2$fZ^5>0@3$6@1$a@2$2@2$2$1$0@1$3$4@2$d^7^6@2$7@2$2@2$2$1$0@1$3$4@4$5@2$2$1$0@1$3$4@4$5$1$0^5^4^3@2$b^8^6").
Proof.
  intros st c st' a ev L C00 H. ndestruct (cache_alloc_core st c st' a ev H) as ((C0 & C1) & st1 & pc1 & cp & rest & A & _ & -> & _).
  destruct A as [(PZ & taken & ev' & G & _)|(PZ & -> & _)].
  - assert (Hc : 0 <= c < kNumClasses) by lia.
    pose proof (get_from_allocator_sbpa (ensure_cache_inited st) c _ st1 taken ev' ltac:(rewrite eci_regions; exact L) Hc G) as S1.
    exact (sbpa_trans _ _ _ (eci_sbpa st) S1).
  - split; reflexivity.
Qed.

Lemma cache_dealloc_sbpa : ltac2:(zQ "b0!k1!hm3!hmb!hn3!nb!hnb!ho3!hod!ld!u2!ij2>2st$0>1c$4>1p$4>3st'$0>2ev@1$1$2>0@3$8@1$6@2$3$0@1$1$2@3$a^5^4^3@2$5@2$3$0@1$1$2@4$7$0@1$1$2^2^1@2$9^6^3").
Proof.
  intros st c p st' ev H. unfold cache_dealloc in H.
  destruct ((c =? 0) || (kNumClasses <=? c)); [discriminate H|].
  set (st0 := ensure_cache_inited st) in H.
  assert (S0 : sbpa st st0) by (subst st0; apply eci_sbpa).
  clearbody st0.
  destruct (pc_count (get_pc st0 c) =? max_count c).
  - destruct (_ <? _); [discriminate H|].
    destruct (return_to_allocator (set_pc st0 c _) c _ _) as [[st1 ev1]|] eqn:RT; [| discriminate H]. injection H as <- _.
    unfold return_to_allocator in RT. destruct (ensure_free_array_space _ c _) as [[st2 ev2]|] eqn:EN; [| discriminate RT]. injection RT as <- _.
    destruct (ensure_free_array_space_core _ c _ st2 ev2 EN) as (mfa' & C2 & _). cbv zeta in C2.
    pose proof (sbpa_of_core _ _ C2) as S2. exact (sbpa_trans _ _ _ S0 S2).
  - injection H as <- _. exact S0.
Qed.

Lemma large_deallocate_sbpa : ltac2:(zQ "b0!k1!hm3!hmb!hn3!hnb!ho3!hod!ld!nb!u2!ik1>2st$0>1p$8>3st'$0>2ev@1$1$2>0@3$7@1$5@2$3$0@1$1$2@2$a^4^3@2$4@2$3$0@1$1$2@4$6$0@1$1$2^2^1@2$9^5^3").
Proof. intros st p st' ev H. destruct (large_deallocate_core st p st' ev H) as [_ C]. exact (sbpa_of_core _ _ C). Qed.

Lemma cb_recycle_sbpa : ltac2:(zQ "b0!k1!hm3!hmb!hn3!hnb!ho3!hod!ld!nb!u2!il4>2st$0>1m$8>3st'$0>2ev@1$1$2>0@3$7@1$5@2$3$0@1$1$2@2$a^4^3@2$4@2$3$0@1$1$2@4$6$0@1$1$2^2^1@2$9^5^3").
Proof.
  intros st m st' ev H. unfold cb_recycle in H.
  destruct (find_chunk (as_chunks st) (m + kChunkHeaderSize)) as [ch|]; [| discriminate H].
  destruct (ch_state ch); [discriminate H|].
  destruct (in_primary st m).
  - destruct (class_of_addr st m =? 0); [discriminate H|]. destruct (_ <? _); [discriminate H|]. destruct (negb _); [discriminate H|].
    destruct (poison_shadow st _ _ _) as [[st1 ev1]|] eqn:PS; [| discriminate H].
    destruct (cache_dealloc _ _ _) as [[st3 ev3]|] eqn:CD; [| discriminate H]. injection H as <- _.
    exact (sbpa_trans _ _ _ (poison_shadow_sbpa _ _ _ _ _ _ PS) (cache_dealloc_sbpa _ _ _ _ _ CD)).
  - destruct (large_get_block_begin st m) as [p|]; [| discriminate H]. destruct (p =? 0); [discriminate H|].
    destruct (in_primary st p); [discriminate H|]. destruct (negb _); [discriminate H|].
    exact (large_deallocate_sbpa _ _ _ _ H).
Qed.

Lemma cb_recycle_list_sbpa : ltac2:(zQ "b0!hm3!k1!hmb!hn3!hnb!ho3!hod!ld!nb!u2!im0>2ms@1$0$8>2st$1>4racc@1$0$2>3st'$1>5racc'@1$0$2>0@3$7@1$5@2$3$1@1$0$2@3$a^4^5^3@2$4@2$3$1@1$0$2@4$6$1@1$0$2^2^1@2$9^5^3").
Proof.
  induction ms as [|m ms IH]; intros st racc st' racc' H; cbn in H.
  - injection H as <- _. apply sbpa_refl.
  - destruct (cb_recycle st m) as [[st1 ev1]|] eqn:CB; [| discriminate H].
    exact (sbpa_trans _ _ _ (cb_recycle_sbpa _ _ _ _ CB) (IH _ _ _ _ H)).
Qed.

Lemma do_recycle_sbpa : ltac2:(zQ "b0!hm3!k1!hmb!hn3!hnb!ho3!hod!ld!u2!in1!ind>2bs@1$0$a>2st$1>4racc@1$0$2>3st'$1>5racc'@1$0$2>0@3$7@1$5@2$3$1@1$0$2@3$9^4^5^3@2$4@2$3$1@1$0$2@4$6$1@1$0$2^2^1@2$8^5^3").
Proof.
  induction bs as [|b bs IH]; intros st racc st' racc' H; cbn in H.
  - injection H as <- _. apply sbpa_refl.
  - destruct (cb_recycle_list st (qb_chunks b) racc) as [[st1 racc1]|] eqn:CL; [| discriminate H].
    destruct (negb _); [discriminate H|].
    destruct (cache_dealloc st1 _ _) as [[st2 ev2]|] eqn:CD; [| discriminate H].
    eapply sbpa_trans; [exact (cb_recycle_list_sbpa _ _ _ _ _ CL)|].
    eapply sbpa_trans; [exact (cache_dealloc_sbpa _ _ _ _ _ CD)| exact (IH _ _ _ _ H)].
Qed.

Lemma quarantine_recycle_sbpa : ltac2:(zQ "b0!k1!hm3!hmb!hn3!hnb!ho3!hod!ld!nb!u2!io5>2st$0>2ms$8>3st'$0>2ev@1$1$2>0@3$7@1$5@2$3$0@1$1$2@2$a^4^3@2$4@2$3$0@1$1$2@4$6$0@1$1$2^2^1@2$9^5^3").
Proof.
  intros st ms st' ev H. unfold quarantine_recycle in H.
  destruct (_ <? _); [discriminate H|].
  match type of H with (match ?mg with _ => _ end) = _ => destruct mg as [[g1 extracted]|]; [| discriminate H] end.
  destruct (pop_while _ _ _ _ _) as [[[l2 bytes2] rpopped]|]; [| discriminate H].
  destruct (do_recycle (set_gq st _) _ _) as [[st2 racc]|] eqn:DR; [| discriminate H]. injection H as <- _.
  exact (do_recycle_sbpa _ _ _ _ _ DR).
Qed.

Lemma quarantine_drain_sbpa : ltac2:(zQ "a0!k1!hm3!hmb!hn3!hnb!ho3!hod!ld!u2!ipa>2st$0>3st'$0>2ev@1$1$2>0@3$7@1$5@2$3$0@1$1$2@1$9^3@2$4@2$3$0@1$1$2@4$6$0@1$1$2^2^1@2$8^4^3").
Proof.
  intros st st' ev H. unfold quarantine_drain in H.
  destruct (as_qmax st <? _).
  - exact (quarantine_recycle_sbpa _ _ _ _ H).
  - injection H as <- _. split; reflexivity.
Qed.

Lemma quarantine_enqueue_sbpa : ltac2:(zQ "f0!k1!hm3!hmb!hn3!ld!nb!hnb!hq4!hqe!ho3!hod!u2!hr5!iqd!hu4>2st$0>1m$5>4size$5>3st'$0>2ev@1$1$2>0@3$4$8@2$7$e@1$c^5Ni0>0@3$4@1$9@2$3$0@1$1$2@3$d^6^5^4@2$6@2$3$0@1$1$2@4$a$0@1$1$2^3^2@2$b^7^4").
Proof.
  intros st m size st' ev L H. unfold quarantine_enqueue in H.
  destruct (qc_list (as_tq st)) as [|b0 l0] eqn:TQ.
  - destruct (cache_alloc st kBatchClass) as [[[st1 b] ev1]|] eqn:CA; [| discriminate H].
    destruct (b =? 0); [discriminate H|]. injection H as <- _.
    exact (cache_alloc_sbpa st kBatchClass _ _ _ L ltac:(unfold kBatchClass; lia) CA).
  - destruct (kBatchCount <=? _).
    + destruct (cache_alloc st kBatchClass) as [[[st1 b] ev1]|] eqn:CA; [| discriminate H].
      destruct (b =? 0); [discriminate H|]. injection H as <- _.
      exact (cache_alloc_sbpa st kBatchClass _ _ _ L ltac:(unfold kBatchClass; lia) CA).
    + injection H as <- _. split; reflexivity.
Qed.

Lemma quarantine_put_sbpa : ltac2:(zQ "f0!k1!hm3!hmb!hn3!ld!hnb!hq4!hqe!ho3!hod!u2!hr5!is2!is9!hu4>2st$0>2ch$c>3st'$0>2ev@1$1$2>0@3$4$7@2$6$e@1$b^4Ni0>0@3$4@1$8@2$3$0@1$1$2@2$d^5^4@2$5@2$3$0@1$1$2@4$9$0@1$1$2^3^2@2$a^6^4").
Proof.
  intros st ch st' ev L H. unfold quarantine_put in H.
  destruct (_ || _); [discriminate H|].
  destruct (poison_shadow st _ _ _) as [[st1 ev1]|] eqn:PS; [| discriminate H].
  pose proof (poison_shadow_core _ _ _ _ _ _ PS) as C1.
  assert (L1 : length (as_regions st1) = 32%nat) by (rewrite (same_core_len_regions _ _ C1); exact L).
  destruct (quarantine_enqueue st1 _ _) as [[st2 ev2]|] eqn:EQ; [| discriminate H].
  pose proof (sbpa_trans _ _ _ (poison_shadow_sbpa _ _ _ _ _ _ PS) (quarantine_enqueue_sbpa _ _ _ _ _ L1 EQ)) as S2.
  destruct (_ <? _).
  - destruct (quarantine_drain st2) as [[st3 ev3]|] eqn:DR; [| discriminate H]. injection H as <- _.
    exact (sbpa_trans _ _ _ S2 (quarantine_drain_sbpa _ _ _ DR)).
  - injection H as <- _. exact S2.
Qed.

Theorem am_free_full_sbpa : ltac2:(zQ "e0!k1!hm3!hmb!ld!nb!hn3!nf!od!hnb!ho3!hod!pb!jh6!jhc>2st$0>1p$4>3st'$0>2ev@1$1$2>0@1$c^4>0@3$3@1$9@2$5$0@1$1$2@2$d^5^4@2$8@2$5$0@1$1$2@4$a$0@1$1$2^3^2@2$b@3$3$4@1$7^4@1$7^6@3$3$4@1$6^4@1$6^6").
Proof.
  intros st p st' ev W H. pose proof (WF_lengths st W) as [LENR LENC].
  assert (K : forall st0 (ev0 : list effect), sbpa st st0 -> as_regions st0 = as_regions st ->
    (if p =? 0 then Some (st0, ev0) else
     match find_chunk (as_chunks st0) p with
     | None => None
     | Some ch => match ch_state ch with
                  | CQuarantine => None
                  | CAllocated =>
                      match quarantine_put (upd_chunk st0 (mkChunk (ch_alloc_beg ch) (ch_user_beg ch) (ch_used ch) (ch_rz ch) (ch_class ch) CQuarantine))
                              (mkChunk (ch_alloc_beg ch) (ch_user_beg ch) (ch_used ch) (ch_rz ch) (ch_class ch) CQuarantine) with
                      | None => None
                      | Some (st2, ev2) => Some (st2, ev0 ++ [EStore64 p 0xFFFFFFFF00000000; EStore64 p 0] ++ ev2)
                      end
                  end
     end) = Some (st', ev) -> sbpa st st').
  { intros st0 ev0 S0 R0 H0. destruct (Z.eqb_spec p 0) as [P0|P0].
    - injection H0 as <- _. exact S0.
    - destruct (find_chunk (as_chunks st0) p) as [ch|]; [| discriminate H0]. destruct (ch_state ch); [| discriminate H0].
      match type of H0 with (match quarantine_put ?a ?b with _ => _ end) = _ => destruct (quarantine_put a b) as [[st2 ev2]|] eqn:QP; [| discriminate H0] end.
      injection H0 as <- _.
      match type of QP with quarantine_put ?s1 ?c1 = _ =>
        pose proof (quarantine_put_sbpa s1 c1 _ _ ltac:(cbn; rewrite R0; exact LENR) QP) as S2 end.
      exact (sbpa_trans _ _ _ S0 S2). }
  unfold am_free_full in H.
  destruct (as_internal_init st); [exact (K st [] (sbpa_refl st) eq_refl H)| exact (K (set_internal_init st) [EInternalAllocInit] ltac:(split; reflexivity) eq_refl H)].
Qed.
