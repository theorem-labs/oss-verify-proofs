(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import PropExec MState Mem ITree Nodes Decode.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prelim Monad MSafeP STree Malloc Prog KInv MmNodes GapGrid KLink KLink2.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require MI_Contracts.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec5KLink~~~~~~hc6tbound79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~m26EUndefm21Mm22evm2cundef_reason79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec5STree~~~~~~s14SVis37Corelib4Init9Datatypeshg54boolm25guardm26mstatem24aptrm25lheadm25queuem29free_metam2eactivate_groupm29dec_slotsm27mapinfom2afree_groups15streehg53natm2fnontrivial_free37Corelib4Init5Logichqe4Truem29free_tailm24cptrhg54Somem25cfree79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4KInv~~~~~~hud4mledhg54list36Stdlib5Lists4Listij92Inhg56lengthhqe3andhqe2exhud7ld_live79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6KLink3~~~~~~in44HCNT46Stdlib6ZArith6BinInt1Zira3addira2leira6of_nathud6creachin46hreach79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~ivd6PState3h5LinuxProcessSemanticsfLinuxProcessSem5Statejk35Model79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6MSafeP~~~~~~jna4assnivd4bptrhg53fsthg54prod37Corelib5Lists7ListDefjt73maphc3BUDhc3KLBivd6ps_brkivd4ps_mij95NoDupij94inclhg56option79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec7GapGrid~~~~~~kie6GRID_Jhc6BUDCAPhc8RESV_MAXhc6lcounthc6ltotalira2lthg54Nonehg53sndhqe2eqhqe3notin4blive_cnt_okm27cmallochud8set_livehudaevent_posthg54truehqe3iffm28aptr_eqbhud9ap_removehg54pairm2esize_overflowsm25strips14SRet89OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6KLink32HC~~~~~~lk13OWNhg54conshqe5Falsehc8frame_oklk14MBUDjna5mspec79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec7MmNodes~~~~~~lr66mmsafeivdaraw_mallocira3powhg54unitivd8raw_free" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
Notation mspec := (MSafeP.mspec mmsafe).
Notation MP := (Monad.M PState).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section TBFree.
Context {R : Type}.
Implicit Types (k : mstate -> mapinfo -> M R) (bail : M R) (P : R -> Prop).

Lemma tb_undef : ltac2:(zQ "70!h9!l9!q0!q9!qd!r2!ve>1u$5>2k0>0$0@1$3?1R>1P>0?1RP@5$1?1R@5$6$4$0?1R@1$2^3^2ZZ^1").
Proof. intros. cbn. splits; [lia|lia|]. intros z []. Qed.

Lemma tb_guard : ltac2:(zQ "50!l9!q9!hhd!h9!hi5>3tag$3>1c$2>1t@1$1?1R>4bail@1$1?1R>1P>0?1RP>0@5$0?1R^3ZZ^1@5$0?1R@5$4?1R^6^5^4^3ZZ^2").
Proof. intros. unfold guard. destruct c; [assumption| apply tb_undef]. Qed.

Lemma tb_queue : ltac2:(zQ "60!hid!l9!q9!hj6!hjd!hk5>1h$4>1m$3>2st$0>2k1>0$0@1$2?1R>4bail@1$2?1R>1P>0?1RP>0>3st'$0@5$1?1R@1^4^1ZZ^2@5$1?1R@6$5?1R^7^6^5^4^3ZZ^2").
Proof. intros. unfold queue. apply tb_guard. apply tb_guard. destruct (get_head st h); apply H. Qed.

Lemma tb_free_meta : ltac2:(zQ "50!hid!l9!q9!hj6!hkd>1m$3>2st$0>2k1>0$0@1$2?1R>4bail@1$2?1R>1P>0?1RP>0>3st'$0@5$1?1R@1^4^1ZZ^2@5$1?1R@5$4?1R^6^5^4^3ZZ^2").
Proof. intros. unfold free_meta. apply tb_queue. exact H. Qed.

Lemma tb_activate_group : ltac2:(zQ "60!hid!h9!l9!q9!hl9!hj6>1m$5>2st$0>2k2>0$0>0$1@1$3?1R>4bail@1$3?1R>1P>0?1RP>0>3st'$0>1z$1@5$2?1R@2^5^2^1ZZ^3@5$2?1R@5$4?1R^6^5^4^3ZZ^2").
Proof. intros. unfold activate_group. apply tb_guard. apply H. Qed.

Lemma tb_dec_slots : ltac2:(zQ "60!hj6!h9!l9!q9!hma!hid>2st$5>1p$0>2k3>0$0>0$1@1$3?1R>4bail@1$3?1R>1P>0?1RP>0>1g$0>1i$1@5$2?1R@2^5^2^1ZZ^3@5$2?1R@5$4?1R^6^5^4^3ZZ^2").
Proof. intros. unfold dec_slots. destruct (_ !! _) as [[g i]|]; [apply H| apply tb_undef]. Qed.

Lemma tb_free_group : ltac2:(zQ "a0!hid!q9!hn6!l9!h9!hj6!hma!qd!ho0!hod>3rec>1x$0>2x0$5>2x1$4>2x2>0$0>0$2@1$1?1R>2x3@1$1?1R@3$9$7$4?1R>2st$0>1g$5>1k>0$0>0$2@1$1?1R>4bail@1$1?1R>1P>0?1RP>0>3st1$0>1m$5>3idx$4>2k'>0$0>0$2@1$1?1R>0>3st3$0>2mi$2@5$3?1R@2^3^2^1ZZ^7@5$3?1R@5^b^5^4^3^2^7ZZ^6>0>3st'$0>2mi$2@5$3?1R@2^6^2^1ZZ^4@5$3?1R@7$8?1R@1$6?1R^8^7^6^5^4ZZ^3").
Proof.
  intros rec st g k bail P Hrec Hk. unfold free_group.
  destruct (m_mem _) as [p|]; [| apply tb_undef].
  destruct (negb _).
  - apply tb_free_meta. intros; apply Hk.
  - apply tb_dec_slots. intros g' i. apply Hrec. intros st3 mi. apply tb_free_meta. intros; apply Hk.
Qed.

Lemma tb_nontrivial_free : ltac2:(zQ "90!hid!l9!q9!hn6!hp5!h9!hj6!hma!hpc>4fuel$4>2st$0>1g$6>1i$5>1k>0$0>0$3@1$2?1R>4bail@1$2?1R>1P>0?1RP>0>3st'$0>2mi$3@5$1?1R@2^5^2^1ZZ^3@5$1?1R@8$8?1R@1$7?1R^8^7^6^5^4^3ZZ^2").
Proof.
  induction fuel as [|f IH]; intros st g i k bail P Hk; cbn [nontrivial_free]; [apply tb_undef|].
  destruct (_ && _).
  - destruct (m_next _).
    + apply tb_guard. destruct (optr_eqb _ _); [destruct (active _ _)|];
        [apply tb_activate_group; intros; apply tb_free_group; auto| apply tb_free_group; auto| apply tb_free_group; auto].
    + apply tb_free_group; auto.
  - destruct (_ =? _).
    + apply tb_guard. destruct (negb _); [apply tb_queue; intros; apply Hk| apply Hk].
    + apply Hk.
Qed.
End TBFree.

Lemma tb_free_tail : ltac2:(zQ "70!hid!hs2!h9!l9!hj6!hma!hsa>2st$0>1g$4>3idx$2@5$3$0@4$6@1$5$0^3^2^1ZZ\0$0$1").
Proof.
  intros st g idx. unfold free_tail. apply tb_guard. destruct (negb _); [exact I|].
  apply tb_nontrivial_free. intros st2 [[base len]|]; [|exact I].
  destruct (negb _); [|exact I]. cbn. splits; [lia|lia|]. intros z _. destruct (munmap_answer_ok z); [exact I|].
  unfold bad_answer. apply tb_undef.
Qed.

Lemma tb_sbind_ret {A B} : forall (t : stree ev Z A) (g : A -> B) (P : B -> Prop) cb ck,
  tbound t cb ck (fun a => P (g a)) -> tbound (sbind t (fun a => SRet (g a))) cb ck P.
Proof.
  intros t. induction t as [r|e k IH]; intros g P cb ck H; cbn in *; [exact H|].
  destruct H as (H1 & H2 & H3). splits; [exact H1| exact H2|]. intros z Hz. apply IH. exact (H3 z Hz).
Qed.

Lemma tb_cfree : ltac2:(zQ "60!hid!ht6!htd!hs2!l9!hu5>2cs$0>1c$1@5$4$0@2$5^2@2$2$1^1ZZ\0$0$3").
Proof.
  intros cs c. unfold cfree. destruct (_ !! _) as [[g idx]|]; [| apply tb_undef].
  apply (tb_sbind_ret _ strip (fun _ => True)). apply tb_free_tail.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition HCNT : Z := 1024.
Definition live_cnt_ok : ltac2:(zQ "10!ii9>1L$0P") := ltac2:(zQ "c0!ht6!ij1!ikc!il2!ilc!im3!im9!ii9!ir2!it2!it9!itf\1L$7@2$5@1$1$0\1X@1$1$0@2$4>1c$0>0@3$2$0^1@1$6^3@3$2$0^2^3@2$a@2$9@1$b@2$3$0^1+1$8").

Inductive hreach : mstate -> mled -> Prop :=
| hreach_init secret resv : 0 <= secret < 2^64 -> hreach (strip (minit secret resv)) (led_init resv)
| hreach_malloc cs L n L' cs' r :
    hreach cs L -> 0 <= n -> live_cnt_ok L -> cpath L (cmalloc cs n) L' (cs', r) ->
    hreach cs' (match r with Some c => set_live (c :: ld_live L') L' | None => L' end)
| hreach_free cs L c L' cs' :
    hreach cs L -> In c (ld_live L) -> cpath L (cfree cs (Some c)) L' cs' ->
    hreach cs' (set_live (ap_remove c (ld_live L')) L').

Lemma hreach_creach : ltac2:(zQ "40!iu9!ii9!iv3!hid>2cs$3>1L$1>0@2$2^2^1@2$0^3^2").
Proof.
  intros cs L H. induction H.
  - apply creach_init. assumption.
  - eapply creach_malloc; eauto.
  - eapply creach_free; eauto.
Qed.

(* [comment removed for export] *)
Section HC.
Context {HC : HeapCeil}.

Definition OWN : ltac2:(zQ "50!jj9!ij1!jn1!jr8!js0>1X@1$1$4>1G>0$0>0$2P@1$3$0") := ltac2:(zQ "h40!ht6!ilc!h9!js8!jsf!jue!jn1!ii9!jj9!ij1!im3!im9!jv5!jvb!iv3!js0!kg1!kgb!kh3!khc\1X@1$9$f\1G>0$8>0$6P\1s$8\2mo$6@2$1@2$a$7\1L$7@2$1@2$e@1$h1^3^1@2$1@4$d?2HC^1@1$h0^3^2@2$1@3$h3$0@4$5@2$4$0$2$0@2$3$0$2^5@1$b^1@4$c^1^2ZZ@2$1@2$h2$0@4$5@2$4$0$2$0@2$3$0$2^4@2^3^2^1").

(* [comment removed for export] *)
Definition MBUD : ltac2:(zQ "20!h9!hid>2cs$1>1n$0P") := ltac2:(zQ "h80!ilc!h9!ht6!ki4!hid!it2!it9!jsf!im3!kmd!kn7!ko0!kob!kp4!kpd!kq3!kqb!kr2!kr8!ii9!l9!iv3!krf!kse\2cs$4\1n$1>1L$h3>0@2$h5^3^1>0@2$6@1$d^2$a>0@2$e@2$5@1$c^3$b$9@2$0@1$h6^4@2$8$1\2cb$1@2$8$1\2ck$1@2$0@2$6Z^2@2$0@2$6Z^1@2$0@5$h4@2$7$4@1$3$2@2$h7^8^7^2^1\1r@2$7$4@1$3$2@1$h2@3$h1@1$3$2@3$h0$4@1$3$2^1@1$f$2@2$0@2$6@2$5@1$d^6^2$a@2$e@2$5@2$5@1$c^6^1$b$9").

(* [comment removed for export] *)

Lemma KLB_set_live : ltac2:(zQ "70!jvb!ij1!h9!jn1!ii9!kt8!ht6>1L$4>1v@1$1$6>4pbrk$2>2mo$3>0@4$0?2HC^4^2^1@4$0?2HC@2$5^4^5^3^2").
Proof.
  intros L v pbrk mo K. destruct K; constructor; cbn; auto.
Qed.

Lemma event_post_live : ltac2:(zQ "80!im9!ij1!kr2!h9!ku4!ii9!ht6!qd>1L$5>1e$7>1z$3@3$2@1$1$6@1$0@3$4^3^2^1@1$0^3").
Proof.
  intros L e z. destruct e; cbn; repeat (destruct (_ =? _)); try reflexivity;
  try (destruct (ld_brk L); try reflexivity; destruct (ld_brkreg L) as [[? ?]|]; reflexivity);
  try (destruct (is_err z); reflexivity); try (destruct (_ || _); reflexivity).
Qed.

Lemma cpath_live {R} : forall L (t : stree ev Z R) L' r, cpath L t L' r -> ld_live L' = ld_live L.
Proof. intros L t L' r H. induction H; [reflexivity|]. rewrite IHcpath. apply event_post_live. Qed.

Lemma aptr_eqb_eq : ltac2:(zQ "60!hj6!kr2!hhd!kv2!kva!lg1>1a$0>1b$0@2$4@3$1$2@2$5^2^1$3@3$1$0^2^1").
Proof.
  intros [a1 a2] [b1 b2]. unfold aptr_eqb. cbn. rewrite andb_true_iff, N.eqb_eq, Z.eqb_eq.
  split; [intros [-> ->]; reflexivity| intros H; inversion H; auto].
Qed.

Lemma in_ap_remove : ltac2:(zQ "60!hj6!ikc!ij1!kr2!kr8!lgc>1x$0>1c$0>1l@1$2$0>0@3$1$0^3^1>0@1$4@3$3$0^4^3@3$1$0^5@2$5^4^3").
Proof.
  intros x c l. induction l as [|y l IH]; intros Hin Hne; [destruct Hin|].
  cbn. destruct (aptr_eqb y c) eqn:E.
  - apply aptr_eqb_eq in E. subst y. destruct Hin as [->|Hin]; [congruence| exact Hin].
  - destruct Hin as [->|Hin]; [left; reflexivity| right; apply IH; assumption].
Qed.

Lemma cmalloc_overflow : ltac2:(zQ "h00!ht6!hid!ki4!jsf!kr2!h9!kq3!hhd!lh9!kv2!q9!kse!qd!li1!lj2!lja>2cs$1>1n$5>0@3$4$7@1$d^1$9@3$4@1$a@2$3$1@1$2$0@2$b^3^2@4$f$c$5@2$3$1@1$2$0@4$8$1@1$2$0@1$e^3@1$6$0").
Proof. intros cs n H. unfold cmalloc, malloc_core. rewrite H. reflexivity. Qed.

Lemma mspec_get_bind {A} (P : assn PState) (f : PState -> MP A) Q :
  (forall s0, mspec (fun s mo => s = s0 /\ P s mo) (f s0) Q) -> mspec P (x <- mget ;; f x) Q.
Proof. intros H s mo HP. unfold mbind, mget. cbn. apply (H s). auto. Qed.

(* [comment removed for export] *)
Theorem raw_malloc_spec : ltac2:(zQ "h30!js0!ki4!jj9!jn1!ilc!lo2!lo9!ij1!lp1!h9!lpa!lq5!lqd!lv5!kgb!lvf!it9!kpd!mgd>1X@1$7$0>1G>0$2>0$3P>1n$9>0@1$a^2>0@2$h0Z^2@6$c$d$2@1$1$0\1s$2\2mo$3@2$4@4$5^7^6^2^1@2$b@1$e^2^5@2$f?2HC^3\1r@1$1$0\1s$2\2mo$3M1\1r@1$1$0P^3\1p$0@2$4@4$5@3$6$0^1^9^8^3^2@2$h1^7@2$h2+2+jf$8").
Proof.
  intros X G n HG Hn. unfold raw_malloc.
  apply mspec_get_bind. intros s0.
  apply mspec_pointwise. intros s1 mo1 [-> [((L & Hc & HK & Hi & HB0) & Hnd & HGs) HB]].
  destruct (HB L Hc ltac:(unfold BUD in HB0; lia) ltac:(unfold BUD in HB0; lia)) as (HLC & cb & ck & Hcb & Hck & TB & B1 & B2).
  eapply mspec_bind.
  { eapply mspec_pre; [apply (membed_spec (cmalloc (ps_m s0) n) _ (fun r => snd r <> None) G L s0 cb ck HG (MI_Contracts.cmalloc_contract_proof _ _ _ (hreach_creach _ _ Hc) Hn) TB Hcb Hck)|].
    intros s mo [-> ->]. splits; auto. unfold BUD. splits; auto. exact (kb_limit _ _ _ HK). }
  intros [st' p]. cbn beta iota.
  apply mspec_pointwise. intros s2 mo2 (L' & Hp & HPost & HP & HK' & HG' & Hm & Hfa & Hso & HB').
  pose proof (cpath_live _ _ _ _ Hp) as Hlive. cbn [snd] in HPost, HP.
  eapply mspec_seq with (R := fun s mo => s = set_m st' s2 /\ mo = mo2).
  { apply mspec_upd'. intros s mo [-> ->]. auto. }
  intros []. apply mspec_ret. intros s mo [-> ->].
  assert (Hcr : hreach st' (match p with Some c => set_live (c :: ld_live L') L' | None => L' end)).
  { exact (hreach_malloc _ _ _ _ _ _ Hc Hn HLC Hp). }
  assert (HG2 : G (set_m st' s2) mo2). { apply (HG s2 _ mo2 _); [reflexivity|reflexivity|apply vm_only_refl| exact HG']. }
  destruct p as [c|]; [| exact (HP eq_refl)].
  split.
  - split; [|split; [|exact HG2]].
    + exists (set_live (c :: ld_live L') L'). split; [exact Hcr|]. split; [apply KLB_set_live; exact HK'|].
      split; [| unfold BUD, ltotal, lcount, lbrk_bytes, lbrk_cnt in *; cbn; exact HB'].
      cbn. intros x [<-|Hx]; [left; reflexivity| right]. rewrite Hlive. apply Hi. exact Hx.
    + cbn. constructor; [|exact Hnd]. intros Hin. apply HPost. rewrite Hlive. apply Hi. exact Hin.
  - destruct (size_overflows n) eqn:E.
    + exfalso. rewrite (cmalloc_overflow _ _ E) in Hp. inversion Hp.
    + unfold size_overflows in E. apply Z.leb_gt in E. lia.
Qed.

Theorem raw_free_spec : ltac2:(zQ "b0!js0!mh4!lo2!jj9!lo9!ij1!jn1!lpa!lqd!lv5!mhc>1X@1$5$0>1G>0$3>0$6P>1p$0>0@1$7^2@6$8$9$3$1@2$2@3$4$0^2^4^3@2$a?2HC^2\0$1@2$2^5^4").
Proof.
  intros X G p HG. unfold raw_free.
  apply mspec_get_bind. intros s0.
  apply mspec_pointwise. intros s1 mo1 [-> ((L & Hc & HK & Hi & HB0) & Hnd & HGs)].
  assert (Hin : In (fst p) (ld_live L)) by (apply Hi; left; reflexivity).
  eapply mspec_bind.
  { eapply mspec_pre; [apply (membed_spec (cfree (ps_m s0) (Some (fst p))) _ (fun _ => True) G L s0 0 0 HG
                               (MI_Contracts.cfree_contract_proof _ _ _ (hreach_creach _ _ Hc) Hin) (tb_cfree _ _) (Z.le_refl 0) (Z.le_refl 0))|].
    intros s mo [-> ->]. splits; auto. }
  intros st'. cbn beta iota.
  apply mspec_pointwise. intros s2 mo2 (L' & Hp & _ & _ & HK' & HG' & Hm & Hfa & Hso & HB').
  pose proof (cpath_live _ _ _ _ Hp) as Hlive.
  apply mspec_upd'. intros s mo [-> ->].
  assert (Hcr : hreach st' (set_live (ap_remove (fst p) (ld_live L')) L')).
  { exact (hreach_free _ _ _ _ _ Hc Hin Hp). }
  split; [|split; [inversion Hnd; assumption| apply (HG s2 _ mo2 _); [reflexivity|reflexivity|apply vm_only_refl| exact HG']]].
  exists (set_live (ap_remove (fst p) (ld_live L')) L'). split; [exact Hcr|]. split; [apply KLB_set_live; exact HK'|].
  split; [| unfold BUD, ltotal, lcount, lbrk_bytes, lbrk_cnt in *; cbn; exact HB'].
  cbn. intros x Hx. rewrite Hlive. apply in_ap_remove.
  - apply Hi. right. exact Hx.
  - inversion Hnd; subst. intros ->. apply H1. exact Hx.
Qed.
End HC.
(* [comment removed for export] *)
