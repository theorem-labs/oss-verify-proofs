(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_Shadow
  MI_Pres1 MI_Pres2 MI_Read MI_WFree2 MI_WGroup MI_Cnt MI_TF2.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04bool37Corelib7Numbers7BinNumshe1Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~jb8fold_off46Stdlib6ZArith6BinInt1Zo43leb04andb04negb03orb79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6MI_Cnt~~~~~~r36zrange36Stdlib5Lists4Listva7forallbo43ltb04true37Corelib4Init5Logichi32eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4SpecbMI_WEnframe~~~~~~hjd6fold_fo42lehi33ando42lthe1Njb6shadow25stdpp9countablehq8bN_countable35stdpp7numbers1Nhs86eq_dec25stdpp4gmaphu34gmap03fstjb5havocjb8s_shadowjb4aptrjbaget_shadowjb6mstate25stdpp4baseiic6insert25stdpp8fin_mapsik2amap_inserthu3h2gmap_partial_alter79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec9MI_WGroup~~~~~~in73TKSjb6s_tick04prod03sndo46modulojb6regionin74DOMS04Some06optionhi32exjb7RKGroupjb6r_kindjb5rkindjb9s_regionsiic6lookuphu3bgmap_lookup79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6MI_Ext~~~~~~jk17ctrl_eq04listjb4aadd04cons04pair03nilo46shiftr03appo43eqbo43addo44lando43oppo46shiftl89OSSVerify6Proofsaboost_jsonafuzz_parse3lib4SpecbMI_WEnframe2EF~~~~~~jt87ef_listin73wrsjbaenframe_atjb4UNITo43mulhjd5lastw04Nonejb9cell_readjb7cellvaljb5Known79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4KInv~~~~~~kn74mled79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6MI_Inv~~~~~~krb4INVLkrb3blkkrb6extrasjb5lheadjb4metajbcget_meta_recjbaget_stride02idhe2N0jb5m_mem25stdpp6optionlkebfrom_optionjb2IBo43subo43div" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fold_f : ltac2:(zQ "20!h8!j7>1s$1$0") := ltac2:(zQ "90!j7!n9!pc!q2!q8!qe!v1!hgd!hh7\1s$0@3$7$0\3off$0@2$5@1$4@2$8^2^1@2$3@2$2Z@2$1^1^2@2$2@2$1^1^2^2@2$6Z+hg0").
Lemma fold_all : ltac2:(zQ "70!h8!hhd!hj7!j7!v1!ho0!hgd@3$2$0@3$6$3$5@2$4Z+hg0$1"). Proof. vm_compute. reflexivity. Qed.

Lemma fold_off_le : ltac2:(zQ "50!hoa!hof!j7!n9!hp6>3off$2>5slack$2>0@2$1@2$0Z^2@2$4^2+hg0>0@2$0Z^2@2$1@2$0Z@2$3^4^3@2$0@2$3^4^3^3").
Proof. intros off slack.
  intros Ho Hs. destruct (Z.ltb_spec slack off) as [LT|GE].
  - pose proof (forallb_zrange fold_f 0 256 slack fold_all ltac:(lia) ltac:(lia)) as H. unfold fold_f in H.
    pose proof (forallb_zrange _ 0 256 off H ltac:(lia) ltac:(lia)) as H2. cbn beta in H2.
    replace (slack <? off) with true in H2 by (symmetry; apply Z.ltb_lt; exact LT). cbn in H2.
    apply andb_true_iff in H2 as [A B]. apply Z.leb_le in A. apply Z.leb_le in B. lia.
  - unfold fold_off. replace (slack <? off) with false by (symmetry; apply Z.ltb_ge; exact GE). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma s_shadow_havoc : ltac2:(zQ "h10!hpb!hpf!hr9!ht9!j7!huf!hv7!hvc!ig4!hj7!igf!ih6!ii3!hp6!ij8!il2!im0>1p$a>1n$4>2st$c>0@2$dZ^2@3$9@4$5$0$3$2$1@1$8@3$7^4^3^2@7$e$0$1@4$5$0$3$2$1@4$f$0$1@4$5$0$3$2$1@4$h0$0$3$2$1@3$6$0$4^4@2$b@3$7^4^3^2@3$6$0$4^4@1$8^2").
Proof. intros p n st.
  intros Hn. unfold havoc at 1. replace (n <=? 0) with false by (symmetry; apply Z.leb_gt; lia). unfold upd_shadow. cbn -[havoc get_shadow Z.add Z.mul Z.div Z.ltb].
  f_equal. unfold havoc. replace (n <=? 0) with false by (symmetry; apply Z.leb_gt; lia). rewrite get_shadow_upd_shadow, N.eqb_refl. reflexivity.
Qed.

Lemma TKS_havoc : ltac2:(zQ "b0!j7!hpb!ir8!irf!is8!ise!hj7!hvc!ii3!hp6!it3>1p@2$4$1$0>1n$0>2st$8>0@3$6$0@2$a@3$5$1$0^3+h0Z>0@2$9Z^3>0@2$2^3@1$3^3@2$2@3$7^6^5^4@1$3^4").
Proof. intros p n st.
  intros Al Hn TK rid sh. rewrite s_shadow_havoc by exact Hn.
  destruct (N.eq_dec rid (fst p)) as [->|NE]; [| rewrite lookup_insert_ne by congruence; apply TK].
  rewrite lookup_insert_eq. intros E. inversion E. subst sh. clear E.
  pose proof (sh_ticks_of st (fst p) TK) as [T1 T2].
  destruct (havoc_ticks p n st Hn ltac:(intros u hl Hu ch Hch; exact (T1 u hl ch Hu Hch)) (fst p)
              ltac:(intros u hl Hu ch Hch; exact (T1 u hl ch Hu Hch)) T2) as [A B].
  split; [| split; [intros u hl ch Hu Hch; exact (A u hl Hu ch Hch)| exact B]].
  rewrite havoc_cells by exact Hn. unfold get_shadow. destruct (s_shadow st !! fst p) as [sh0|] eqn:E0; cbn.
  - exact (proj1 (TK _ _ E0)).
  - intros o w t Ho. rewrite lookup_empty in Ho. discriminate.
Qed.

Lemma DOMS_havoc : ltac2:(zQ "h70!itc!hpb!j7!hj7!iu5!ii3!hr9!ht9!iud!hv7!iv3!is8!hof!ivb!jg1!hvc!jgb!jh4!jhc!hp6!ji8!huf!jj2>3st0$5>1p@2$b$1$2>1n$2>2st$5>0@2$h3Z^2>0@2$4^5^2>0@2$d$0\1r$0@2$c@3$3@1$a$0@6$h4$1$0@4$h5$1$7$6$0@4$h6$1$7$6$0@3$9$1$2^6@1$h2^7@2$8$0^1@3$3$h1@1$h0^1$e@2$4^7@3$f^6^5^4").
Proof. intros st0 p n st.
  intros Hn D Hp rid sh. rewrite s_shadow_havoc by exact Hn.
  destruct (N.eq_dec rid (fst p)) as [->|NE]; [intros _; exact Hp|]. rewrite lookup_insert_ne by congruence. apply D.
Qed.

Lemma havoc_ctrl : ltac2:(zQ "90!hvc!irf!hof!hj7!hpb!j7!jnf!igf!ii3>1p$7>1n$5>2st$8@2$2@2$6^1@3$0^3^2^1@3$3$4@1$1@3$0^3^2^1@1$1^1").
Proof. intros p n st. unfold havoc. destruct (n <=? 0); [split; [apply ctrl_eq_refl| reflexivity]|]. split; [constructor; reflexivity| reflexivity]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section EF.
Variables (st : mstate) (g : aptr) (idx n off : Z).
Let mr : ltac2:(zQ "10!lha$0") := ltac2:(zQ "10!li1@2$0?2st?1g").
Let stride : ltac2:(zQ "10!j7$0") := ltac2:(zQ "10!lj0@1$0?2mr").
Let gm : ltac2:(zQ "30!is8!hpb!j7@2$0$1$2") := ltac2:(zQ "80!hpb!j7!is8!ljd!jpd!lk1!lk6!llc@5$7@2$2$0$1@2$2$0$1@1$3@2$2$0$1@4$4$0$1$5Z@1$6?2mr").
Let c : ltac2:(zQ "10!igf$0") := ltac2:(zQ "40!kjd!jp0!jrc!kk4@2$1?2gm@2$2$0@2$3?6stride?3idx").
Let e : ltac2:(zQ "10!igf$0") := ltac2:(zQ "30!lmb!jp0!ln0@2$1?1c@2$2?6stride$0").
Let p0 : ltac2:(zQ "10!igf$0") := ltac2:(zQ "60!h8!kjd!jp0!igf!jr6!kk4M0\0$0$3@2$4?3offZ?1c@2$2?1c@2$5$1?3off").
Let res : ltac2:(zQ "10!j7$0") := ltac2:(zQ "40!ise!hpb!j7!ln0@2$3@2$3@3$0$1$2?1e@3$0$1$2?2p0?1n").
Let q : ltac2:(zQ "10!j7$0") := ltac2:(zQ "70!ise!hpb!j7!kjd!jrc!ln6!ln0@2$5@2$6@3$0$1$2?2p0@2$4@3$0$1$2?2gm$3$3").

Definition ef_list : ltac2:(zQ "40!joa!is8!j7!igf@1$0@2$1$3$2") := ltac2:(zQ "h20!j7!igf!is8!jp0!jp7!jpd!h8!jq3!jq8!jr1!joa!q8!jr6!pc!jrc!js2!js9!jsf@3$9@2$2$1$0M6\0$6@1$a@2$2$1$0@1$b@2$c?3offZ@3$4@2$2$1$0@4$5$1$0@2$3?1c-2?3off@3$4@2$2$1$0@4$5$1$0@2$3@2$3?1c-2+1@2$8?3off+8@3$4@2$2$1$0@4$5$1$0@2$3?1c-3+u0@3$4@2$2$1$0@4$5$1$0@2$3?2p0-4Z@1$7@2$2$1$0@1$7@2$2$1$0@3$9@2$2$1$0@3$4@2$2$1$0@4$5$1$0@2$3?2p0-2?1q@3$4@2$2$1$0@4$5$1$0@2$3@2$3?2p0-2+1@2$8?1q+8@3$4@2$2$1$0@4$5$1$0@2$3?2p0-3?3idx@1$7@2$2$1$0@3$9@2$2$1$0M6\0$6@1$a@2$2$1$0@1$b@2$c?3resZ@3$4@2$2$1$0@4$5$1$0@2$3?1e@1$h0?3resZ@1$7@2$2$1$0@1$7@2$2$1$0@3$9@2$2$1$0M6\0$6@1$a@2$2$1$0@2$d+5?3res@3$4@2$2$1$0@4$5$1$0@2$3?1e-4?3res@3$4@2$2$1$0@4$5$1$0@2$3@2$3?1e-4+1@2$8?3res+8@3$4@2$2$1$0@4$5$1$0@2$3@2$3?1e-4+2@2$8?3res+h0@3$4@2$2$1$0@4$5$1$0@2$3@2$3?1e-4+3@2$8?3res+h8@3$4@2$2$1$0@4$5$1$0@2$3?1e-5Z@1$7@2$2$1$0@1$7@2$2$1$0@3$4@2$2$1$0@4$5$1$0@2$3?2p0-3@2$e@2$f?3idx+hf@2$h1M6\0$6$0@2$d+5?3res+5?3res+5@1$7@2$2$1$0").

Lemma enframe_at_eq : ltac2:(zQ "80!igf!ii3!jpd!is8!hj7!khe!ki9!kj0@3$4@2$3$1$0@5$7?2st?1g?3idx?1n?3off@4$2$1$0@2$6$5?2st?2p0").
Proof.
  unfold enframe_at, set_size, ef_list. unfold q, res, p0, e, c, gm, stride, mr.
  (* [comment removed for export] *)
  destruct (off =? 0); cbn beta iota delta [app negb];
    match goal with |- context [if negb (?x =? 0) then _ else _] => destruct (x =? 0) end; cbn beta iota delta [app negb];
    match goal with |- context [if 5 <=? ?x then _ else _] => destruct (5 <=? x) end; cbn beta iota delta [app negb]; reflexivity.
Qed.

Lemma p0_eq : ltac2:(zQ "50!hj7!kjd!jp0!igf!kk4@3$0$3?2p0@2$2?1c@2$4$1?3off").
Proof. unfold p0. destruct (Z.eqb_spec off 0) as [->|]; [| reflexivity]. unfold c, aadd. cbn. f_equal. lia. Qed.
End EF.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint lastw (l : list (aptr * Z)) (r : aptr) (acc : option Z) : option Z :=
  match l with
  | [] => acc
  | (a, v) :: l' => lastw l' r (if aptr_eqb a r then Some v else acc)
  end.

Lemma lastw_acc : ltac2:(zQ "90!j7!iv3!iud!kka!igf!kl3!joa!is8!hj7>1l@1$6@2$7$4$0>1r$4>1v$0@3$8@1$1$0@3$3^3^2@2$2$0^1M1\1x@1$1$0@1$1$0@3$3^3^2@1$5$0\1w$0@2$2$0^1@2$2$0^1").
Proof. intros l r v.
  revert v. induction l as [|[a w] l IH]; intros v; cbn; [reflexivity|].
  destruct (aptr_eqb a r); [| apply IH]. rewrite !(IH w). destruct (lastw l r None); reflexivity.
Qed.

Lemma wrs_lastw : ltac2:(zQ "h40!j7!hpb!hv7!iv3!is8!ise!kl9!km5!ih6!kl3!joa!hj7!kka!ir8!ki9!kmf!igf!ii3!irf!js2>1l@1$a@2$4$h0$0>2st$h1>1r@2$4$1$0>0@2$d^2@1$h2^2@3$b$7@2$6@2$8@2$e^4^3@3$2$1$0^2@3$5$1$0^2M3\1x@1$3$0$7@3$c^4^2@1$9$0\1w$0@1$f@2$h3^1+vf@2$6@2$8^3@3$2$1$0^2@3$5$1$0^2").
Proof. intros l.
  induction l as [|[a v] l IH]; intros st r TK; cbn [wrs lastw]; [reflexivity|].
  rewrite IH by (apply TKS_wr8; [cbn; lia| exact TK]).
  destruct (aptr_eqb_spec a r) as [<-|NE].
  - rewrite lastw_acc. destruct (lastw l a None); [reflexivity|]. apply cell_read_wr8_same. apply sh_ticks_of. exact TK.
  - destruct (lastw l r None); [reflexivity|]. apply cell_read_wr8_other. congruence.
Qed.

Lemma known_range : ltac2:(zQ "h50!j7!hpb!joa!hv7!is8!ise!hof!hj7!kr3!kv9!lg1!lg8!kmf!igf!kl9!km5!ih6!lh2!ii3!hoa!hp6>1X$b>2st$h2>1L$8>2BL@1$2$a>2LS>0$h1@1$2$d>1q@2$4$1$0>1v$0>0@5$9^7^6^5^4^3>0@3$7$f@2$e@2$h0^7@3$3$1$0^3@3$5$1$0^3@1$c^2@2$6@2$h3Z^3@2$h4^3+hg0").
Proof. intros X st L BL LS q v.
  intros INV H. eapply known_byte; [| exact H]. intros sh o' v' t Hs Hc. exact (proj1 (proj1 (TKS_of _ _ _ _ _ INV _ _ Hs) o' v' t Hc)).
Qed.

Lemma land255_range : ltac2:(zQ "50!js2!hof!j7!hoa!hp6>1a$2@2$1@2$3Z@2$0^1+vf@2$4@2$0^1+vf+hg0").
Proof. intros a.
  split; [apply Z.land_nonneg; right; lia|].
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
Qed.
(* [comment removed for export] *)
