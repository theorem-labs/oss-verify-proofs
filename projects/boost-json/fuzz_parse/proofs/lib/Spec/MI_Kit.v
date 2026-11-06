(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04bool04true37Corelib4Init5Logici42eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~jd4aptrjd8aptr_eqbi43iff07reflect05falsei43notjd4optrjd8optr_eqbjd4metajdcget_meta_recjd6mstatejd8put_metajd8upd_meta37Corelib7Numbers7BinNumsv01Nv01Z35stdpp7numbers1Nhh16eq_dec35stdpp7numbers1Zhic6eq_dec25stdpp9countablehk7bN_countablehk7bZ_countablehk7eprod_countable25stdpp9decidableho8bprod_eq_dec25stdpp4gmaphq84gmapjd7s_metas25stdpp4basehs66insert25stdpp8fin_mapshtcamap_inserthq8h2gmap_partial_alter06optionhs66lookuphq8bgmap_lookup04Somejd4mctxjd5s_ctxjd7upd_ctxjd9s_regionsjd6regionjd8s_shadowjd6shadowjdas_next_ridjd7s_areasjd4areajd8s_groupsjd4ghdrjd7s_slots04prodjd6s_tickjd8s_secretjdas_reserved04listjdbset_regionsjdaset_shadowjdcset_next_ridjd9set_metasjd9set_areasjdaset_groupsjd9set_slotsjd8set_tickjd8c_secretjdaset_secretjdbc_init_donejdec_mmap_counterjdh0c_free_meta_headjdcc_avail_metajdh2c_avail_meta_countjdh7c_avail_meta_area_countjdh2c_meta_alloc_shiftjdh0c_meta_area_headjdh0c_meta_area_tailjdh2c_avail_meta_areasjd8c_activejd7c_usagejdbc_unmap_seqjd9c_bouncesjd5c_seqjd5c_brkjd8brkstatejddset_init_donejdh0set_mmap_counterjdh2set_free_meta_headjdeset_avail_metajdh4set_avail_meta_countjdh9set_avail_meta_area_countjdh4set_meta_alloc_shiftjdh2set_meta_area_headjdh2set_meta_area_tailjdh4set_avail_meta_areasjdeset_active_mapjddset_usage_mapjdh1set_unmap_seq_mapjdfset_bounces_mapjd7set_seqjd7set_brkjdaset_activejd9set_usagejdaset_bouncejd9put_groupjd9del_groupjdh4set_group_active_idxjdbdrop_regionjdaupd_regionjd9add_slotsjd9del_slotsjdaupd_shadowjd3wr8jd4wr16jd4wr32jd5havocjd9hdr_havocjd8step_seqjdarecord_seqjdeaccount_bouncejdddecay_bouncesjd5lheadjd8set_headjd7dequeuejd8set_sizejd5stripi43and03natjd9zero_hdrs03fstjdaenframe_atjdbnest_layoutjd8mkRegionjdanew_regionjd5rkind46Stdlib6NArith6BinNat1Nni64succ03sndhs66deletehtcamap_deletejd6mkGhdr46Stdlib6ZArith6BinInt1Znmc4landjdaget_shadowjd6activenmc3eqbjd5usagejd7bouncesjd8get_headni63eqb04None0aoption_mapjd4concjd6r_basenmc3addnmc3subjd4UNIT04andbnmc3div04pairnmc2lenmc3lebnmc2ltnmc3ltbnmc6modulojd7cellvaljd9cell_read02id03nil03orbjd5Knownjd7Unknownjd5r_havjd6r_havpjd5stalejd8stale_pg25stdpp6optionop5bfrom_optionni62le36Stdlib5Lists4Listor82In79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6MI_Kit~~~~~~ot18sh_ticks" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma aptr_eqb_refl : ltac2:(zQ "50!h8!he!j8!nb!o2>1a$3@3$2$0@2$4^1^1$1").
Proof. intros a. unfold aptr_eqb. rewrite N.eqb_refl, Z.eqb_refl. reflexivity. Qed.

Lemma aptr_eqb_eq : ltac2:(zQ "60!nb!j8!h8!he!od!o2>1a$0>1b$0@2$4@3$1$2@2$5^2^1$3@3$1$0^2^1").
Proof. intros a b.
  unfold aptr_eqb. destruct a as [r o], b as [r' o']; cbn. rewrite Bool.andb_true_iff, N.eqb_eq, Z.eqb_eq.
  split; [intros [-> ->]; reflexivity| intros H; inversion H; auto].
Qed.

Lemma aptr_eqb_spec : ltac2:(zQ "40!nb!p3!j8!o2>1a$0>1b$0@2$1@3$2$0^2^1@2$3^2^1").
Proof. intros a b.
  destruct (aptr_eqb a b) eqn:E; constructor.
  - apply aptr_eqb_eq. exact E.
  - intros ->. rewrite aptr_eqb_refl in E. discriminate.
Qed.

Lemma aptr_eqb_neq : ltac2:(zQ "60!nb!j8!h8!pc!q3!o2>1a$0>1b$0>0@1$4@3$1$0^2^1@3$1$2@2$5^3^2$3").
Proof. intros a b. intros H. destruct (aptr_eqb_spec a b); [contradiction| reflexivity]. Qed.

Lemma optr_eqb_spec : ltac2:(zQ "40!q9!p3!j8!r0>1a$0>1b$0@2$1@3$2$0^2^1@2$3^2^1").
Proof. intros a b.
  destruct a as [a|], b as [b|]; cbn; try (constructor; congruence).
  destruct (aptr_eqb_spec a b); constructor; congruence.
Qed.

Lemma optr_eqb_refl : ltac2:(zQ "50!h8!he!j8!q9!r0>1a$3@3$2$0@2$4^1^1$1").
Proof. intros a. destruct (optr_eqb_spec a a); [reflexivity| contradiction]. Qed.

(* [comment removed for export] *)

#[export] Instance aptr_eq_dec : EqDecision aptr := _.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma get_meta_rec_put : ltac2:(zQ "80!rb!h8!nb!s2!j8!o2!t1!ta>2st$6>1m$2>1r$0>1x$2@3$4$0@2$3@3$7^3^2^4^1M1\0$1$0@2$5^1^3^2@2$3^4^1").
Proof. intros st m r x.
  unfold get_meta_rec, put_meta; cbn. destruct (aptr_eqb_spec x m) as [->|NE].
  - rewrite lookup_insert_eq. reflexivity.
  - rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma get_meta_rec_upd : ltac2:(zQ "80!rb!s2!h8!nb!j8!o2!t1!u5>2st$6>1m$3>1f>0$0$0>1x$3@3$4$0@2$1@3$7^3^2^4^1M2\0$2$0@2$5^1^3@1^2@2$1^4^3@2$1^4^1").
Proof. intros st m f x. unfold upd_meta. apply get_meta_rec_put. Qed.

Lemma get_meta_rec_put_same : ltac2:(zQ "60!rb!j8!nb!s2!t1!ta>2st$4>1m$2>1r$0@3$1$0@2$3@3$5^2^1^3^2^1").
Proof. intros st m r. rewrite get_meta_rec_put, aptr_eqb_refl. reflexivity. Qed.
Lemma get_meta_rec_upd_same : ltac2:(zQ "60!rb!s2!j8!nb!t1!u5>2st$4>1m$3>1f>0$0$0@3$2$0@2$1@3$5^2^1^3^2@1^1@2$1^3^2").
Proof. intros st m f. rewrite get_meta_rec_upd, aptr_eqb_refl. reflexivity. Qed.
Lemma get_meta_rec_upd_other : ltac2:(zQ "70!nb!rb!j8!s2!q3!t1!u5>2st$5>1m$0>1f>0$1$1>1x$0>0@1$4@3$2$0^1^3@3$2$1@2$3@3$6^4^3^5^2@2$3^5^2").
Proof. intros st m f x. intros H. rewrite get_meta_rec_upd, aptr_eqb_neq by exact H. reflexivity. Qed.

Lemma s_metas_upd_meta : ltac2:(zQ "h31!hg9!hgd!rb!hi2!hjd!nb!hl8!hm7!hn6!hp9!hr4!hrc!j8!s2!t1!u5!ht2!huc!hva&@4$a$5@4$9$0$3$1$4@6$8$0$3$6$1$4$7$2>1m$5>1f>0$2$2>2st$e@3$c~0@1$b@3$f^3^2^1@7$h0$5$2~0@4$h1$5$2~0@4$h2$5@4$9$0$3$1$4@6$8$0$3$6$1$4$7$2^3@1^2@2$d^1^3@1$b^1").
Proof. intros m f st. reflexivity. Qed.

Lemma lookup_metas_put : ltac2:(zQ "h52!rb!hg9!hgd!nb!hi2!hjd!hl8!hm7!hn6!hp9!h8!ih1!hrc!ih9!hr4!ii3!ij2!j8!o2!t1!ta&@4$e$3@4$9$1$4$2$5@6$8$1$4$6$2$5$7$0&@4$f$3@4$9$1$4$2$5@6$8$1$4$6$2$5$7$0>2st$h3>1m$3>1r$0>1x$3@3$h1@1$b$0@6$d$3$0~0~1^1@1$c@3$h4^3^2^4Ma\0$a@1$b$0@2$h2^1^3@2$h0$0^2@6$d$3$0~0~1^1@1$c^4").
Proof. intros st m r x.
  cbn. destruct (aptr_eqb_spec x m) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
Qed.
Lemma lookup_metas_upd : ltac2:(zQ "h62!rb!hg9!hgd!nb!hi2!hjd!hl8!hm7!hn6!hp9!h8!ih1!hrc!ih9!hr4!ii3!ij2!j8!o2!s2!t1!u5&@4$e$3@4$9$1$4$2$5@6$8$1$4$6$2$5$7$0&@4$f$3@4$9$1$4$2$5@6$8$1$4$6$2$5$7$0>2st$h4>1m$3>1f>0$0$0>1x$3@3$h1@1$b$0@6$d$3$0~0~1^1@1$c@3$h5^3^2^4Ma\0$a@1$b$0@2$h2^1^3@2$h0$0@1^2@2$h3^4^3@6$d$3$0~0~1^1@1$c^4").
Proof. intros st m f x. unfold upd_meta. apply lookup_metas_put. Qed.

(* [comment removed for export] *)
Lemma get_meta_rec_ext : ltac2:(zQ "f0!j8!hg9!hgd!nb!s2!rb!t1!hrc!hi2!hjd!hl8!hm7!hn6!hp9!hr4>2st$6>3st'$6>1x$3>0@3$0@4$e$3@4$d$1$8$2$9@6$c$1$8$a$2$9$b$5@1$7^2@1$7^3@3$0$5@2$4^3^2@2$4^4^2").
Proof. intros st st' x. intros H. unfold get_meta_rec. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma s_ctx_upd_ctx : ltac2:(zQ "50!ij8!ijf!j8!t1!ik7>1f>0$0$0>2st$3@3$2$0@1$1@2$4^2^1@1^2@1$1^1"). Proof. intros f st. reflexivity. Qed.
Lemma s_regions_upd_ctx : ltac2:(zQ "a0!ij8!il1!j8!hg9!t1!ild!ik7!hl8!hr4!hi2>1f>0$0$0>2st$4@3$2@4$8$3$9$7$5@1$1@2$6^2^1@1$1^1"). Proof. intros f st. reflexivity. Qed.
Lemma s_shadow_upd_ctx : ltac2:(zQ "a0!ij8!im6!j8!hg9!t1!in1!ik7!hl8!hr4!hi2>1f>0$0$0>2st$4@3$2@4$8$3$9$7$5@1$1@2$6^2^1@1$1^1"). Proof. intros f st. reflexivity. Qed.
Lemma s_next_rid_upd_ctx : ltac2:(zQ "60!ij8!ina!j8!hg9!t1!ik7>1f>0$0$0>2st$4@3$2$3@1$1@2$5^2^1@1$1^1"). Proof. intros f st. reflexivity. Qed.
Lemma s_metas_upd_ctx : ltac2:(zQ "h00!hg9!hgd!ij8!hrc!hi2!hjd!j8!nb!rb!t1!ik7!hl8!hm7!hn6!hp9!hr4>1f>0$2$2>2st$9@3$6@4$f$7@4$e$0$4$1$5@6$d$0$4$b$1$5$c$8@1$3@2$a^2^1@1$3^1"). Proof. intros f st. reflexivity. Qed.
Lemma s_areas_upd_ctx : ltac2:(zQ "h00!hg9!hgd!ij8!io7!hi2!hjd!j8!nb!ip1!t1!ik7!hl8!hm7!hn6!hp9!hr4>1f>0$2$2>2st$9@3$6@4$f$7@4$e$0$4$1$5@6$d$0$4$b$1$5$c$8@1$3@2$a^2^1@1$3^1"). Proof. intros f st. reflexivity. Qed.
Lemma s_groups_upd_ctx : ltac2:(zQ "h00!hg9!hgd!ij8!ip8!hi2!hjd!j8!nb!iq3!t1!ik7!hl8!hm7!hn6!hp9!hr4>1f>0$2$2>2st$9@3$6@4$f$7@4$e$0$4$1$5@6$d$0$4$b$1$5$c$8@1$3@2$a^2^1@1$3^1"). Proof. intros f st. reflexivity. Qed.
Lemma s_slots_upd_ctx : ltac2:(zQ "h00!hgd!hg9!nb!ij8!iqa!hi2!hjd!ir4!j8!t1!ik7!hl8!hm7!hn6!hp9!hr4>1f>0$3$3>2st$9@3$8@4$f$2@4$e$1$5$0$6@6$d$1$5$b$0$6$c@2$7$2$0@1$4@2$a^2^1@1$4^1"). Proof. intros f st. reflexivity. Qed.
Lemma s_tick_upd_ctx : ltac2:(zQ "60!ij8!ira!j8!hg9!t1!ik7>1f>0$0$0>2st$4@3$2$3@1$1@2$5^2^1@1$1^1"). Proof. intros f st. reflexivity. Qed.
Lemma s_secret_upd_ctx : ltac2:(zQ "60!ij8!is3!j8!hgd!t1!ik7>1f>0$0$0>2st$4@3$2$3@1$1@2$5^2^1@1$1^1"). Proof. intros f st. reflexivity. Qed.
Lemma s_reserved_upd_ctx : ltac2:(zQ "80!hgd!ij8!ise!itb!ir4!j8!t1!ik7>1f>0$1$1>2st$6@3$5@1$3@2$4$0$0@1$2@2$7^2^1@1$2^1"). Proof. intros f st. reflexivity. Qed.
Lemma s_ctx_set_regions : ltac2:(zQ "a0!ijf!j8!hg9!ij8!t1!ild!iu1!hl8!hr4!hi2>1v@4$8$2$9$7$5>2st$4@3$1$3@1$0@2$6^2^1@1$0^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_regions_set_regions : ltac2:(zQ "90!hg9!ild!hl8!hr4!hi2!j8!t1!il1!iu1>1v@4$3$0$4$2$1>2st$6@3$5@4$3$0$4$2$1@1$7@2$8^2^1^2"). Proof. intros v st. reflexivity. Qed.
Lemma s_shadow_set_regions : ltac2:(zQ "a0!hg9!im6!hl8!hr4!hi2!j8!t1!ild!iu1!in1>1v@4$3$0$4$2$7>2st$6@3$5@4$3$0$4$2$9@1$1@2$8^2^1@1$1^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_next_rid_set_regions : ltac2:(zQ "90!hg9!ina!j8!t1!ild!iu1!hl8!hr4!hi2>1v@4$7$0$8$6$4>2st$3@3$2$0@1$1@2$5^2^1@1$1^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_metas_set_regions : ltac2:(zQ "h00!hg9!hi2!hgd!hrc!hl8!hr4!hjd!j8!nb!rb!t1!ild!iu1!hm7!hn6!hp9>1v@4$5$0$1$4$b>2st$a@3$7@4$5$8@4$f$0$1$2$6@6$e$0$1$4$2$6$d$9@1$3@2$c^2^1@1$3^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_areas_set_regions : ltac2:(zQ "h00!hg9!hi2!hgd!io7!hl8!hr4!hjd!j8!nb!ip1!t1!ild!iu1!hm7!hn6!hp9>1v@4$5$0$1$4$b>2st$a@3$7@4$5$8@4$f$0$1$2$6@6$e$0$1$4$2$6$d$9@1$3@2$c^2^1@1$3^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_groups_set_regions : ltac2:(zQ "h00!hg9!hi2!hgd!ip8!hl8!hr4!hjd!j8!nb!iq3!t1!ild!iu1!hm7!hn6!hp9>1v@4$5$0$1$4$b>2st$a@3$7@4$5$8@4$f$0$1$2$6@6$e$0$1$4$2$6$d$9@1$3@2$c^2^1@1$3^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_slots_set_regions : ltac2:(zQ "h00!hg9!hgd!hi2!nb!iqa!hl8!hr4!hjd!ir4!j8!t1!ild!iu1!hm7!hn6!hp9>1v@4$6$0$2$5$b>2st$a@3$9@4$6$3@4$f$0$2$1$7@6$e$0$2$5$1$7$d@2$8$3$1@1$4@2$c^2^1@1$4^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_tick_set_regions : ltac2:(zQ "90!hg9!ira!j8!t1!ild!iu1!hl8!hr4!hi2>1v@4$7$0$8$6$4>2st$3@3$2$0@1$1@2$5^2^1@1$1^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_secret_set_regions : ltac2:(zQ "a0!is3!j8!hg9!hgd!t1!ild!iu1!hl8!hr4!hi2>1v@4$8$2$9$7$5>2st$4@3$1$3@1$0@2$6^2^1@1$0^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_reserved_set_regions : ltac2:(zQ "c0!hgd!ise!itb!ir4!j8!hg9!t1!ild!iu1!hl8!hr4!hi2>1v@4$a$5$b$9$7>2st$6@3$4@1$2@2$3$0$0@1$1@2$8^2^1@1$1^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_ctx_set_shadow : ltac2:(zQ "a0!ijf!j8!hg9!ij8!t1!iuf!in1!hl8!hr4!hi2>1v@4$8$2$9$7$6>2st$4@3$1$3@1$0@2$5^2^1@1$0^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_regions_set_shadow : ltac2:(zQ "a0!hg9!il1!hl8!hr4!hi2!j8!t1!ild!iuf!in1>1v@4$3$0$4$2$9>2st$6@3$5@4$3$0$4$2$7@1$1@2$8^2^1@1$1^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_shadow_set_shadow : ltac2:(zQ "90!hg9!in1!hl8!hr4!hi2!j8!t1!im6!iuf>1v@4$3$0$4$2$1>2st$6@3$5@4$3$0$4$2$1@1$7@2$8^2^1^2"). Proof. intros v st. reflexivity. Qed.
Lemma s_next_rid_set_shadow : ltac2:(zQ "90!hg9!ina!j8!t1!iuf!in1!hl8!hr4!hi2>1v@4$7$0$8$6$5>2st$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_metas_set_shadow : ltac2:(zQ "h00!hg9!hi2!hgd!hrc!hl8!hr4!hjd!j8!nb!rb!t1!iuf!in1!hm7!hn6!hp9>1v@4$5$0$1$4$c>2st$a@3$7@4$5$8@4$f$0$1$2$6@6$e$0$1$4$2$6$d$9@1$3@2$b^2^1@1$3^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_areas_set_shadow : ltac2:(zQ "h00!hg9!hi2!hgd!io7!hl8!hr4!hjd!j8!nb!ip1!t1!iuf!in1!hm7!hn6!hp9>1v@4$5$0$1$4$c>2st$a@3$7@4$5$8@4$f$0$1$2$6@6$e$0$1$4$2$6$d$9@1$3@2$b^2^1@1$3^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_groups_set_shadow : ltac2:(zQ "h00!hg9!hi2!hgd!ip8!hl8!hr4!hjd!j8!nb!iq3!t1!iuf!in1!hm7!hn6!hp9>1v@4$5$0$1$4$c>2st$a@3$7@4$5$8@4$f$0$1$2$6@6$e$0$1$4$2$6$d$9@1$3@2$b^2^1@1$3^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_slots_set_shadow : ltac2:(zQ "h00!hg9!hgd!hi2!nb!iqa!hl8!hr4!hjd!ir4!j8!t1!iuf!in1!hm7!hn6!hp9>1v@4$6$0$2$5$c>2st$a@3$9@4$6$3@4$f$0$2$1$7@6$e$0$2$5$1$7$d@2$8$3$1@1$4@2$b^2^1@1$4^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_tick_set_shadow : ltac2:(zQ "90!hg9!ira!j8!t1!iuf!in1!hl8!hr4!hi2>1v@4$7$0$8$6$5>2st$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_secret_set_shadow : ltac2:(zQ "a0!is3!j8!hg9!hgd!t1!iuf!in1!hl8!hr4!hi2>1v@4$8$2$9$7$6>2st$4@3$1$3@1$0@2$5^2^1@1$0^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_reserved_set_shadow : ltac2:(zQ "c0!hgd!ise!itb!ir4!j8!hg9!t1!iuf!in1!hl8!hr4!hi2>1v@4$a$5$b$9$8>2st$6@3$4@1$2@2$3$0$0@1$1@2$7^2^1@1$1^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_ctx_set_next_rid : ltac2:(zQ "60!ijf!j8!hg9!ij8!t1!ivc>1v$2>2st$4@3$1$3@1$0@2$5^2^1@1$0^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_regions_set_next_rid : ltac2:(zQ "90!hg9!il1!j8!t1!ild!ivc!hl8!hr4!hi2>1v$0>2st$3@3$2@4$7$0$8$6$4@1$1@2$5^2^1@1$1^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_shadow_set_next_rid : ltac2:(zQ "90!hg9!im6!j8!t1!ivc!in1!hl8!hr4!hi2>1v$0>2st$3@3$2@4$7$0$8$6$5@1$1@2$4^2^1@1$1^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_next_rid_set_next_rid : ltac2:(zQ "50!hg9!j8!t1!ina!ivc>1v$0>2st$2@3$1$0@1$3@2$4^2^1^2"). Proof. intros v st. reflexivity. Qed.
Lemma s_metas_set_next_rid : ltac2:(zQ "f0!hg9!hgd!hrc!hi2!hjd!j8!nb!rb!t1!ivc!hl8!hm7!hn6!hp9!hr4>1v$0>2st$8@3$5@4$e$6@4$d$0$3$1$4@6$c$0$3$a$1$4$b$7@1$2@2$9^2^1@1$2^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_areas_set_next_rid : ltac2:(zQ "f0!hg9!hgd!io7!hi2!hjd!j8!nb!ip1!t1!ivc!hl8!hm7!hn6!hp9!hr4>1v$0>2st$8@3$5@4$e$6@4$d$0$3$1$4@6$c$0$3$a$1$4$b$7@1$2@2$9^2^1@1$2^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_groups_set_next_rid : ltac2:(zQ "f0!hg9!hgd!ip8!hi2!hjd!j8!nb!iq3!t1!ivc!hl8!hm7!hn6!hp9!hr4>1v$0>2st$8@3$5@4$e$6@4$d$0$3$1$4@6$c$0$3$a$1$4$b$7@1$2@2$9^2^1@1$2^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_slots_set_next_rid : ltac2:(zQ "f0!hg9!hgd!nb!iqa!hi2!hjd!ir4!j8!t1!ivc!hl8!hm7!hn6!hp9!hr4>1v$0>2st$8@3$7@4$e$2@4$d$0$4$1$5@6$c$0$4$a$1$5$b@2$6$2$1@1$3@2$9^2^1@1$3^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_tick_set_next_rid : ltac2:(zQ "50!hg9!ira!j8!t1!ivc>1v$0>2st$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_secret_set_next_rid : ltac2:(zQ "60!is3!j8!hg9!hgd!t1!ivc>1v$2>2st$4@3$1$3@1$0@2$5^2^1@1$0^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_reserved_set_next_rid : ltac2:(zQ "80!hgd!ise!itb!ir4!j8!hg9!t1!ivc>1v$5>2st$6@3$4@1$2@2$3$0$0@1$1@2$7^2^1@1$1^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_ctx_set_metas : ltac2:(zQ "h00!hg9!hgd!ijf!hi2!hjd!j8!nb!ij8!rb!t1!jgb!hl8!hm7!hn6!hp9!hr4>1v@4$f$6@4$e$0$3$1$4@6$d$0$3$b$1$4$c$8>2st$9@3$5$7@1$2@2$a^2^1@1$2^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_regions_set_metas : ltac2:(zQ "h00!hg9!hi2!hgd!il1!hl8!hr4!hjd!j8!nb!rb!t1!ild!jgb!hm7!hn6!hp9>1v@4$5$8@4$f$0$1$2$6@6$e$0$1$4$2$6$d$9>2st$a@3$7@4$5$0$1$4$b@1$3@2$c^2^1@1$3^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_shadow_set_metas : ltac2:(zQ "h00!hg9!hi2!hgd!im6!hl8!hr4!hjd!j8!nb!rb!t1!jgb!in1!hm7!hn6!hp9>1v@4$5$8@4$f$0$1$2$6@6$e$0$1$4$2$6$d$9>2st$a@3$7@4$5$0$1$4$c@1$3@2$b^2^1@1$3^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_next_rid_set_metas : ltac2:(zQ "f0!hg9!hgd!ina!hi2!hjd!j8!nb!rb!t1!jgb!hl8!hm7!hn6!hp9!hr4>1v@4$e$6@4$d$0$3$1$4@6$c$0$3$a$1$4$b$7>2st$8@3$5$0@1$2@2$9^2^1@1$2^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_metas_set_metas : ltac2:(zQ "f1!hg9!hgd!hi2!hjd!nb!rb!hl8!hm7!hn6!hp9!hr4!j8!t1!hrc!jgb&@4$a$4@4$9$0$2$1$3@6$8$0$2$6$1$3$7$5>1v~0>2st$c@3$b~0@1$d@2$e^2^1^2"). Proof. intros v st. reflexivity. Qed.
Lemma s_areas_set_metas : ltac2:(zQ "h00!hg9!hgd!hi2!hjd!nb!io7!hl8!hm7!hn6!hp9!hr4!j8!ip1!rb!t1!jgb>1v@4$a$4@4$9$0$2$1$3@6$8$0$2$6$1$3$7$d>2st$e@3$b@4$a$4@4$9$0$2$1$3@6$8$0$2$6$1$3$7$c@1$5@2$f^2^1@1$5^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_groups_set_metas : ltac2:(zQ "h00!hg9!hgd!hi2!hjd!nb!ip8!hl8!hm7!hn6!hp9!hr4!j8!iq3!rb!t1!jgb>1v@4$a$4@4$9$0$2$1$3@6$8$0$2$6$1$3$7$d>2st$e@3$b@4$a$4@4$9$0$2$1$3@6$8$0$2$6$1$3$7$c@1$5@2$f^2^1@1$5^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_slots_set_metas : ltac2:(zQ "h00!hgd!hg9!hi2!hjd!nb!iqa!hl8!hm7!hn6!hp9!hr4!ir4!j8!rb!t1!jgb>1v@4$a$4@4$9$1$2$0$3@6$8$1$2$6$0$3$7$d>2st$e@3$c@4$a$4@4$9$1$2$0$3@6$8$1$2$6$0$3$7@2$b$4$0@1$5@2$f^2^1@1$5^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_tick_set_metas : ltac2:(zQ "f0!hg9!hgd!ira!hi2!hjd!j8!nb!rb!t1!jgb!hl8!hm7!hn6!hp9!hr4>1v@4$e$6@4$d$0$3$1$4@6$c$0$3$a$1$4$b$7>2st$8@3$5$0@1$2@2$9^2^1@1$2^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_secret_set_metas : ltac2:(zQ "f0!hgd!hg9!is3!hi2!hjd!j8!nb!rb!t1!jgb!hl8!hm7!hn6!hp9!hr4>1v@4$e$6@4$d$1$3$0$4@6$c$1$3$a$0$4$b$7>2st$8@3$5$0@1$2@2$9^2^1@1$2^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_reserved_set_metas : ltac2:(zQ "h10!hgd!hg9!ise!hi2!hjd!itb!ir4!j8!nb!rb!t1!jgb!hl8!hm7!hn6!hp9!hr4>1v@4$h0$8@4$f$1$3$0$4@6$e$1$3$c$0$4$d$9>2st$a@3$7@1$5@2$6$0$0@1$2@2$b^2^1@1$2^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_ctx_set_areas : ltac2:(zQ "h00!hg9!hgd!ijf!hi2!hjd!j8!nb!ip1!ij8!t1!jh7!hl8!hm7!hn6!hp9!hr4>1v@4$f$6@4$e$0$3$1$4@6$d$0$3$b$1$4$c$7>2st$9@3$5$8@1$2@2$a^2^1@1$2^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_regions_set_areas : ltac2:(zQ "h00!hg9!hi2!hgd!il1!hl8!hr4!hjd!j8!nb!ip1!t1!ild!jh7!hm7!hn6!hp9>1v@4$5$8@4$f$0$1$2$6@6$e$0$1$4$2$6$d$9>2st$a@3$7@4$5$0$1$4$b@1$3@2$c^2^1@1$3^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_shadow_set_areas : ltac2:(zQ "h00!hg9!hi2!hgd!im6!hl8!hr4!hjd!j8!nb!ip1!t1!jh7!in1!hm7!hn6!hp9>1v@4$5$8@4$f$0$1$2$6@6$e$0$1$4$2$6$d$9>2st$a@3$7@4$5$0$1$4$c@1$3@2$b^2^1@1$3^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_next_rid_set_areas : ltac2:(zQ "f0!hg9!hgd!ina!hi2!hjd!j8!nb!ip1!t1!jh7!hl8!hm7!hn6!hp9!hr4>1v@4$e$6@4$d$0$3$1$4@6$c$0$3$a$1$4$b$7>2st$8@3$5$0@1$2@2$9^2^1@1$2^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_metas_set_areas : ltac2:(zQ "h00!hg9!hgd!hi2!hjd!nb!hrc!hl8!hm7!hn6!hp9!hr4!j8!ip1!rb!t1!jh7>1v@4$a$4@4$9$0$2$1$3@6$8$0$2$6$1$3$7$c>2st$e@3$b@4$a$4@4$9$0$2$1$3@6$8$0$2$6$1$3$7$d@1$5@2$f^2^1@1$5^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_areas_set_areas : ltac2:(zQ "f1!hg9!hgd!hi2!hjd!nb!ip1!hl8!hm7!hn6!hp9!hr4!j8!t1!io7!jh7&@4$a$4@4$9$0$2$1$3@6$8$0$2$6$1$3$7$5>1v~0>2st$c@3$b~0@1$d@2$e^2^1^2"). Proof. intros v st. reflexivity. Qed.
Lemma s_groups_set_areas : ltac2:(zQ "h00!hg9!hgd!hi2!hjd!nb!ip8!hl8!hm7!hn6!hp9!hr4!j8!ip1!iq3!t1!jh7>1v@4$a$4@4$9$0$2$1$3@6$8$0$2$6$1$3$7$c>2st$e@3$b@4$a$4@4$9$0$2$1$3@6$8$0$2$6$1$3$7$d@1$5@2$f^2^1@1$5^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_slots_set_areas : ltac2:(zQ "h00!hgd!hg9!hi2!hjd!nb!iqa!hl8!hm7!hn6!hp9!hr4!ir4!j8!ip1!t1!jh7>1v@4$a$4@4$9$1$2$0$3@6$8$1$2$6$0$3$7$d>2st$e@3$c@4$a$4@4$9$1$2$0$3@6$8$1$2$6$0$3$7@2$b$4$0@1$5@2$f^2^1@1$5^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_tick_set_areas : ltac2:(zQ "f0!hg9!hgd!ira!hi2!hjd!j8!nb!ip1!t1!jh7!hl8!hm7!hn6!hp9!hr4>1v@4$e$6@4$d$0$3$1$4@6$c$0$3$a$1$4$b$7>2st$8@3$5$0@1$2@2$9^2^1@1$2^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_secret_set_areas : ltac2:(zQ "f0!hgd!hg9!is3!hi2!hjd!j8!nb!ip1!t1!jh7!hl8!hm7!hn6!hp9!hr4>1v@4$e$6@4$d$1$3$0$4@6$c$1$3$a$0$4$b$7>2st$8@3$5$0@1$2@2$9^2^1@1$2^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_reserved_set_areas : ltac2:(zQ "h10!hgd!hg9!ise!hi2!hjd!itb!ir4!j8!nb!ip1!t1!jh7!hl8!hm7!hn6!hp9!hr4>1v@4$h0$8@4$f$1$3$0$4@6$e$1$3$c$0$4$d$9>2st$a@3$7@1$5@2$6$0$0@1$2@2$b^2^1@1$2^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_ctx_set_groups : ltac2:(zQ "h00!hg9!hgd!ijf!hi2!hjd!j8!nb!iq3!ij8!t1!ji3!hl8!hm7!hn6!hp9!hr4>1v@4$f$6@4$e$0$3$1$4@6$d$0$3$b$1$4$c$7>2st$9@3$5$8@1$2@2$a^2^1@1$2^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_regions_set_groups : ltac2:(zQ "h00!hg9!hi2!hgd!il1!hl8!hr4!hjd!j8!nb!iq3!t1!ild!ji3!hm7!hn6!hp9>1v@4$5$8@4$f$0$1$2$6@6$e$0$1$4$2$6$d$9>2st$a@3$7@4$5$0$1$4$b@1$3@2$c^2^1@1$3^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_shadow_set_groups : ltac2:(zQ "h00!hg9!hi2!hgd!im6!hl8!hr4!hjd!j8!nb!iq3!t1!ji3!in1!hm7!hn6!hp9>1v@4$5$8@4$f$0$1$2$6@6$e$0$1$4$2$6$d$9>2st$a@3$7@4$5$0$1$4$c@1$3@2$b^2^1@1$3^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_next_rid_set_groups : ltac2:(zQ "f0!hg9!hgd!ina!hi2!hjd!j8!nb!iq3!t1!ji3!hl8!hm7!hn6!hp9!hr4>1v@4$e$6@4$d$0$3$1$4@6$c$0$3$a$1$4$b$7>2st$8@3$5$0@1$2@2$9^2^1@1$2^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_metas_set_groups : ltac2:(zQ "h00!hg9!hgd!hi2!hjd!nb!hrc!hl8!hm7!hn6!hp9!hr4!j8!iq3!rb!t1!ji3>1v@4$a$4@4$9$0$2$1$3@6$8$0$2$6$1$3$7$c>2st$e@3$b@4$a$4@4$9$0$2$1$3@6$8$0$2$6$1$3$7$d@1$5@2$f^2^1@1$5^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_areas_set_groups : ltac2:(zQ "h00!hg9!hgd!hi2!hjd!nb!io7!hl8!hm7!hn6!hp9!hr4!j8!ip1!iq3!t1!ji3>1v@4$a$4@4$9$0$2$1$3@6$8$0$2$6$1$3$7$d>2st$e@3$b@4$a$4@4$9$0$2$1$3@6$8$0$2$6$1$3$7$c@1$5@2$f^2^1@1$5^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_groups_set_groups : ltac2:(zQ "f1!hg9!hgd!hi2!hjd!nb!iq3!hl8!hm7!hn6!hp9!hr4!j8!t1!ip8!ji3&@4$a$4@4$9$0$2$1$3@6$8$0$2$6$1$3$7$5>1v~0>2st$c@3$b~0@1$d@2$e^2^1^2"). Proof. intros v st. reflexivity. Qed.
Lemma s_slots_set_groups : ltac2:(zQ "h00!hgd!hg9!hi2!hjd!nb!iqa!hl8!hm7!hn6!hp9!hr4!ir4!j8!iq3!t1!ji3>1v@4$a$4@4$9$1$2$0$3@6$8$1$2$6$0$3$7$d>2st$e@3$c@4$a$4@4$9$1$2$0$3@6$8$1$2$6$0$3$7@2$b$4$0@1$5@2$f^2^1@1$5^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_tick_set_groups : ltac2:(zQ "f0!hg9!hgd!ira!hi2!hjd!j8!nb!iq3!t1!ji3!hl8!hm7!hn6!hp9!hr4>1v@4$e$6@4$d$0$3$1$4@6$c$0$3$a$1$4$b$7>2st$8@3$5$0@1$2@2$9^2^1@1$2^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_secret_set_groups : ltac2:(zQ "f0!hgd!hg9!is3!hi2!hjd!j8!nb!iq3!t1!ji3!hl8!hm7!hn6!hp9!hr4>1v@4$e$6@4$d$1$3$0$4@6$c$1$3$a$0$4$b$7>2st$8@3$5$0@1$2@2$9^2^1@1$2^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_reserved_set_groups : ltac2:(zQ "h10!hgd!hg9!ise!hi2!hjd!itb!ir4!j8!nb!iq3!t1!ji3!hl8!hm7!hn6!hp9!hr4>1v@4$h0$8@4$f$1$3$0$4@6$e$1$3$c$0$4$d$9>2st$a@3$7@1$5@2$6$0$0@1$2@2$b^2^1@1$2^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_ctx_set_slots : ltac2:(zQ "h00!hgd!hg9!nb!ijf!hi2!hjd!ir4!j8!ij8!t1!jj0!hl8!hm7!hn6!hp9!hr4>1v@4$f$2@4$e$1$4$0$5@6$d$1$4$b$0$5$c@2$6$2$0>2st$9@3$7$8@1$3@2$a^2^1@1$3^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_regions_set_slots : ltac2:(zQ "h00!hg9!hgd!hi2!nb!il1!hl8!hr4!hjd!ir4!j8!t1!ild!jj0!hm7!hn6!hp9>1v@4$6$3@4$f$0$2$1$7@6$e$0$2$5$1$7$d@2$8$3$1>2st$a@3$9@4$6$0$2$5$b@1$4@2$c^2^1@1$4^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_shadow_set_slots : ltac2:(zQ "h00!hg9!hgd!hi2!nb!im6!hl8!hr4!hjd!ir4!j8!t1!jj0!in1!hm7!hn6!hp9>1v@4$6$3@4$f$0$2$1$7@6$e$0$2$5$1$7$d@2$8$3$1>2st$a@3$9@4$6$0$2$5$c@1$4@2$b^2^1@1$4^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_next_rid_set_slots : ltac2:(zQ "f0!hg9!hgd!nb!ina!hi2!hjd!ir4!j8!t1!jj0!hl8!hm7!hn6!hp9!hr4>1v@4$e$2@4$d$0$4$1$5@6$c$0$4$a$1$5$b@2$6$2$1>2st$8@3$7$0@1$3@2$9^2^1@1$3^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_metas_set_slots : ltac2:(zQ "h00!hgd!hg9!hi2!hjd!nb!hrc!hl8!hm7!hn6!hp9!hr4!ir4!j8!rb!t1!jj0>1v@4$a$4@4$9$1$2$0$3@6$8$1$2$6$0$3$7@2$b$4$0>2st$e@3$c@4$a$4@4$9$1$2$0$3@6$8$1$2$6$0$3$7$d@1$5@2$f^2^1@1$5^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_areas_set_slots : ltac2:(zQ "h00!hgd!hg9!hi2!hjd!nb!io7!hl8!hm7!hn6!hp9!hr4!ir4!j8!ip1!t1!jj0>1v@4$a$4@4$9$1$2$0$3@6$8$1$2$6$0$3$7@2$b$4$0>2st$e@3$c@4$a$4@4$9$1$2$0$3@6$8$1$2$6$0$3$7$d@1$5@2$f^2^1@1$5^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_groups_set_slots : ltac2:(zQ "h00!hgd!hg9!hi2!hjd!nb!ip8!hl8!hm7!hn6!hp9!hr4!ir4!j8!iq3!t1!jj0>1v@4$a$4@4$9$1$2$0$3@6$8$1$2$6$0$3$7@2$b$4$0>2st$e@3$c@4$a$4@4$9$1$2$0$3@6$8$1$2$6$0$3$7$d@1$5@2$f^2^1@1$5^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_slots_set_slots : ltac2:(zQ "f1!hgd!hg9!nb!hi2!hjd!ir4!hl8!hm7!hn6!hp9!hr4!j8!t1!iqa!jj0&@4$a$2@4$9$1$3$0$4@6$8$1$3$6$0$4$7@2$5$2$0>1v~0>2st$c@3$b~0@1$d@2$e^2^1^2"). Proof. intros v st. reflexivity. Qed.
Lemma s_tick_set_slots : ltac2:(zQ "f0!hg9!hgd!nb!ira!hi2!hjd!ir4!j8!t1!jj0!hl8!hm7!hn6!hp9!hr4>1v@4$e$2@4$d$0$4$1$5@6$c$0$4$a$1$5$b@2$6$2$1>2st$8@3$7$0@1$3@2$9^2^1@1$3^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_secret_set_slots : ltac2:(zQ "f0!hgd!hg9!nb!is3!hi2!hjd!ir4!j8!t1!jj0!hl8!hm7!hn6!hp9!hr4>1v@4$e$2@4$d$1$4$0$5@6$c$1$4$a$0$5$b@2$6$2$0>2st$8@3$7$0@1$3@2$9^2^1@1$3^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_reserved_set_slots : ltac2:(zQ "h00!hgd!ir4!hg9!nb!ise!hi2!hjd!itb!j8!t1!jj0!hl8!hm7!hn6!hp9!hr4>1v@4$f$3@4$e$2$5$0$6@6$d$2$5$b$0$6$c@2$1$3$0>2st$9@3$8@1$7@2$1$0$0@1$4@2$a^2^1@1$4^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_ctx_set_tick : ltac2:(zQ "60!ijf!j8!hg9!ij8!t1!jjc>1v$2>2st$4@3$1$3@1$0@2$5^2^1@1$0^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_regions_set_tick : ltac2:(zQ "90!hg9!il1!j8!t1!ild!jjc!hl8!hr4!hi2>1v$0>2st$3@3$2@4$7$0$8$6$4@1$1@2$5^2^1@1$1^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_shadow_set_tick : ltac2:(zQ "90!hg9!im6!j8!t1!jjc!in1!hl8!hr4!hi2>1v$0>2st$3@3$2@4$7$0$8$6$5@1$1@2$4^2^1@1$1^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_next_rid_set_tick : ltac2:(zQ "50!hg9!ina!j8!t1!jjc>1v$0>2st$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_metas_set_tick : ltac2:(zQ "f0!hg9!hgd!hrc!hi2!hjd!j8!nb!rb!t1!jjc!hl8!hm7!hn6!hp9!hr4>1v$0>2st$8@3$5@4$e$6@4$d$0$3$1$4@6$c$0$3$a$1$4$b$7@1$2@2$9^2^1@1$2^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_areas_set_tick : ltac2:(zQ "f0!hg9!hgd!io7!hi2!hjd!j8!nb!ip1!t1!jjc!hl8!hm7!hn6!hp9!hr4>1v$0>2st$8@3$5@4$e$6@4$d$0$3$1$4@6$c$0$3$a$1$4$b$7@1$2@2$9^2^1@1$2^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_groups_set_tick : ltac2:(zQ "f0!hg9!hgd!ip8!hi2!hjd!j8!nb!iq3!t1!jjc!hl8!hm7!hn6!hp9!hr4>1v$0>2st$8@3$5@4$e$6@4$d$0$3$1$4@6$c$0$3$a$1$4$b$7@1$2@2$9^2^1@1$2^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_slots_set_tick : ltac2:(zQ "f0!hg9!hgd!nb!iqa!hi2!hjd!ir4!j8!t1!jjc!hl8!hm7!hn6!hp9!hr4>1v$0>2st$8@3$7@4$e$2@4$d$0$4$1$5@6$c$0$4$a$1$5$b@2$6$2$1@1$3@2$9^2^1@1$3^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_tick_set_tick : ltac2:(zQ "50!hg9!j8!t1!ira!jjc>1v$0>2st$2@3$1$0@1$3@2$4^2^1^2"). Proof. intros v st. reflexivity. Qed.
Lemma s_secret_set_tick : ltac2:(zQ "60!is3!j8!hg9!hgd!t1!jjc>1v$2>2st$4@3$1$3@1$0@2$5^2^1@1$0^1"). Proof. intros v st. reflexivity. Qed.
Lemma s_reserved_set_tick : ltac2:(zQ "80!hgd!ise!itb!ir4!j8!hg9!t1!jjc>1v$5>2st$6@3$4@1$2@2$3$0$0@1$1@2$7^2^1@1$1^1"). Proof. intros v st. reflexivity. Qed.
Lemma c_secret_set_secret : ltac2:(zQ "50!hgd!j8!jk7!ij8!jl2>1v$0>1c$3@3$1$0@1$2@2$4^2^1^2"). Proof. intros v c. reflexivity. Qed.
Lemma c_init_done_set_secret : ltac2:(zQ "50!hgd!jlf!j8!ij8!jl2>1v$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_mmap_counter_set_secret : ltac2:(zQ "50!hgd!jmd!j8!ij8!jl2>1v$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_free_meta_head_set_secret : ltac2:(zQ "60!jne!j8!hgd!ij8!q9!jl2>1v$2>1c$3@3$1$4@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_set_secret : ltac2:(zQ "60!jp2!j8!hgd!ij8!q9!jl2>1v$2>1c$3@3$1$4@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_count_set_secret : ltac2:(zQ "50!hgd!jq1!j8!ij8!jl2>1v$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_secret : ltac2:(zQ "50!hgd!jr7!j8!ij8!jl2>1v$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_secret : ltac2:(zQ "50!hgd!jt2!j8!ij8!jl2>1v$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_head_set_secret : ltac2:(zQ "60!ju8!j8!hgd!ij8!q9!jl2>1v$2>1c$3@3$1$4@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_tail_set_secret : ltac2:(zQ "60!jvc!j8!hgd!ij8!q9!jl2>1v$2>1c$3@3$1$4@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_areas_set_secret : ltac2:(zQ "60!kh0!j8!hgd!ij8!q9!jl2>1v$2>1c$3@3$1$4@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_active_set_secret : ltac2:(zQ "90!hgd!ki6!j8!nb!ij8!jl2!hm7!hr4!hjd>1v$0>1c$4@3$2@4$7$0$8$6$3@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_usage_set_secret : ltac2:(zQ "80!hgd!kj1!j8!ij8!jl2!hm7!hr4!hjd>1v$0>1c$3@3$2@4$6$0$7$5$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_unmap_seq_set_secret : ltac2:(zQ "80!hgd!kjb!j8!ij8!jl2!hm7!hr4!hjd>1v$0>1c$3@3$2@4$6$0$7$5$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_bounces_set_secret : ltac2:(zQ "80!hgd!kk9!j8!ij8!jl2!hm7!hr4!hjd>1v$0>1c$3@3$2@4$6$0$7$5$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_seq_set_secret : ltac2:(zQ "50!hgd!kl5!j8!ij8!jl2>1v$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_brk_set_secret : ltac2:(zQ "60!kld!j8!hgd!km5!ij8!jl2>1v$2>1c$4@3$1$3@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_secret_set_init_done : ltac2:(zQ "50!hgd!jk7!j8!ij8!kn0>1v$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_init_done_set_init_done : ltac2:(zQ "50!hgd!j8!jlf!ij8!kn0>1v$0>1c$3@3$1$0@1$2@2$4^2^1^2"). Proof. intros v c. reflexivity. Qed.
Lemma c_mmap_counter_set_init_done : ltac2:(zQ "50!hgd!jmd!j8!ij8!kn0>1v$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_free_meta_head_set_init_done : ltac2:(zQ "60!jne!j8!hgd!ij8!q9!kn0>1v$2>1c$3@3$1$4@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_set_init_done : ltac2:(zQ "60!jp2!j8!hgd!ij8!q9!kn0>1v$2>1c$3@3$1$4@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_count_set_init_done : ltac2:(zQ "50!hgd!jq1!j8!ij8!kn0>1v$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_init_done : ltac2:(zQ "50!hgd!jr7!j8!ij8!kn0>1v$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_init_done : ltac2:(zQ "50!hgd!jt2!j8!ij8!kn0>1v$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_head_set_init_done : ltac2:(zQ "60!ju8!j8!hgd!ij8!q9!kn0>1v$2>1c$3@3$1$4@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_tail_set_init_done : ltac2:(zQ "60!jvc!j8!hgd!ij8!q9!kn0>1v$2>1c$3@3$1$4@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_areas_set_init_done : ltac2:(zQ "60!kh0!j8!hgd!ij8!q9!kn0>1v$2>1c$3@3$1$4@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_active_set_init_done : ltac2:(zQ "90!hgd!ki6!j8!nb!ij8!kn0!hm7!hr4!hjd>1v$0>1c$4@3$2@4$7$0$8$6$3@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_usage_set_init_done : ltac2:(zQ "80!hgd!kj1!j8!ij8!kn0!hm7!hr4!hjd>1v$0>1c$3@3$2@4$6$0$7$5$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_unmap_seq_set_init_done : ltac2:(zQ "80!hgd!kjb!j8!ij8!kn0!hm7!hr4!hjd>1v$0>1c$3@3$2@4$6$0$7$5$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_bounces_set_init_done : ltac2:(zQ "80!hgd!kk9!j8!ij8!kn0!hm7!hr4!hjd>1v$0>1c$3@3$2@4$6$0$7$5$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_seq_set_init_done : ltac2:(zQ "50!hgd!kl5!j8!ij8!kn0>1v$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_brk_set_init_done : ltac2:(zQ "60!kld!j8!hgd!km5!ij8!kn0>1v$2>1c$4@3$1$3@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_secret_set_mmap_counter : ltac2:(zQ "50!hgd!jk7!j8!ij8!ko0>1v$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_init_done_set_mmap_counter : ltac2:(zQ "50!hgd!jlf!j8!ij8!ko0>1v$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_mmap_counter_set_mmap_counter : ltac2:(zQ "50!hgd!j8!jmd!ij8!ko0>1v$0>1c$3@3$1$0@1$2@2$4^2^1^2"). Proof. intros v c. reflexivity. Qed.
Lemma c_free_meta_head_set_mmap_counter : ltac2:(zQ "60!jne!j8!hgd!ij8!q9!ko0>1v$2>1c$3@3$1$4@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_set_mmap_counter : ltac2:(zQ "60!jp2!j8!hgd!ij8!q9!ko0>1v$2>1c$3@3$1$4@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_count_set_mmap_counter : ltac2:(zQ "50!hgd!jq1!j8!ij8!ko0>1v$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_mmap_counter : ltac2:(zQ "50!hgd!jr7!j8!ij8!ko0>1v$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_mmap_counter : ltac2:(zQ "50!hgd!jt2!j8!ij8!ko0>1v$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_head_set_mmap_counter : ltac2:(zQ "60!ju8!j8!hgd!ij8!q9!ko0>1v$2>1c$3@3$1$4@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_tail_set_mmap_counter : ltac2:(zQ "60!jvc!j8!hgd!ij8!q9!ko0>1v$2>1c$3@3$1$4@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_areas_set_mmap_counter : ltac2:(zQ "60!kh0!j8!hgd!ij8!q9!ko0>1v$2>1c$3@3$1$4@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_active_set_mmap_counter : ltac2:(zQ "90!hgd!ki6!j8!nb!ij8!ko0!hm7!hr4!hjd>1v$0>1c$4@3$2@4$7$0$8$6$3@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_usage_set_mmap_counter : ltac2:(zQ "80!hgd!kj1!j8!ij8!ko0!hm7!hr4!hjd>1v$0>1c$3@3$2@4$6$0$7$5$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_unmap_seq_set_mmap_counter : ltac2:(zQ "80!hgd!kjb!j8!ij8!ko0!hm7!hr4!hjd>1v$0>1c$3@3$2@4$6$0$7$5$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_bounces_set_mmap_counter : ltac2:(zQ "80!hgd!kk9!j8!ij8!ko0!hm7!hr4!hjd>1v$0>1c$3@3$2@4$6$0$7$5$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_seq_set_mmap_counter : ltac2:(zQ "50!hgd!kl5!j8!ij8!ko0>1v$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_brk_set_mmap_counter : ltac2:(zQ "60!kld!j8!hgd!km5!ij8!ko0>1v$2>1c$4@3$1$3@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_secret_set_free_meta_head : ltac2:(zQ "60!jk7!j8!hgd!ij8!q9!kp4>1v$4>1c$3@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_init_done_set_free_meta_head : ltac2:(zQ "60!jlf!j8!hgd!ij8!q9!kp4>1v$4>1c$3@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_mmap_counter_set_free_meta_head : ltac2:(zQ "60!jmd!j8!hgd!ij8!q9!kp4>1v$4>1c$3@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_free_meta_head_set_free_meta_head : ltac2:(zQ "50!q9!j8!jne!ij8!kp4>1v$0>1c$3@3$1$0@1$2@2$4^2^1^2"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_set_free_meta_head : ltac2:(zQ "50!jp2!q9!j8!ij8!kp4>1v$1>1c$3@3$2$1@1$0@2$4^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_count_set_free_meta_head : ltac2:(zQ "60!jq1!j8!hgd!ij8!q9!kp4>1v$4>1c$3@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_free_meta_head : ltac2:(zQ "60!jr7!j8!hgd!ij8!q9!kp4>1v$4>1c$3@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_free_meta_head : ltac2:(zQ "60!jt2!j8!hgd!ij8!q9!kp4>1v$4>1c$3@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_head_set_free_meta_head : ltac2:(zQ "50!ju8!q9!j8!ij8!kp4>1v$1>1c$3@3$2$1@1$0@2$4^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_tail_set_free_meta_head : ltac2:(zQ "50!jvc!q9!j8!ij8!kp4>1v$1>1c$3@3$2$1@1$0@2$4^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_areas_set_free_meta_head : ltac2:(zQ "50!kh0!q9!j8!ij8!kp4>1v$1>1c$3@3$2$1@1$0@2$4^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_active_set_free_meta_head : ltac2:(zQ "a0!ki6!j8!hgd!nb!ij8!q9!kp4!hm7!hr4!hjd>1v$5>1c$4@3$1@4$8$2$9$7$3@1$0@2$6^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_usage_set_free_meta_head : ltac2:(zQ "90!hgd!kj1!j8!ij8!q9!kp4!hm7!hr4!hjd>1v$4>1c$3@3$2@4$7$0$8$6$0@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_unmap_seq_set_free_meta_head : ltac2:(zQ "90!hgd!kjb!j8!ij8!q9!kp4!hm7!hr4!hjd>1v$4>1c$3@3$2@4$7$0$8$6$0@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_bounces_set_free_meta_head : ltac2:(zQ "90!hgd!kk9!j8!ij8!q9!kp4!hm7!hr4!hjd>1v$4>1c$3@3$2@4$7$0$8$6$0@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_seq_set_free_meta_head : ltac2:(zQ "60!kl5!j8!hgd!ij8!q9!kp4>1v$4>1c$3@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_brk_set_free_meta_head : ltac2:(zQ "60!kld!j8!km5!ij8!q9!kp4>1v$4>1c$3@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_secret_set_avail_meta : ltac2:(zQ "60!jk7!j8!hgd!ij8!q9!kqa>1v$4>1c$3@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_init_done_set_avail_meta : ltac2:(zQ "60!jlf!j8!hgd!ij8!q9!kqa>1v$4>1c$3@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_mmap_counter_set_avail_meta : ltac2:(zQ "60!jmd!j8!hgd!ij8!q9!kqa>1v$4>1c$3@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_free_meta_head_set_avail_meta : ltac2:(zQ "50!jne!q9!j8!ij8!kqa>1v$1>1c$3@3$2$1@1$0@2$4^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_set_avail_meta : ltac2:(zQ "50!q9!j8!jp2!ij8!kqa>1v$0>1c$3@3$1$0@1$2@2$4^2^1^2"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_count_set_avail_meta : ltac2:(zQ "60!jq1!j8!hgd!ij8!q9!kqa>1v$4>1c$3@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_avail_meta : ltac2:(zQ "60!jr7!j8!hgd!ij8!q9!kqa>1v$4>1c$3@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_avail_meta : ltac2:(zQ "60!jt2!j8!hgd!ij8!q9!kqa>1v$4>1c$3@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_head_set_avail_meta : ltac2:(zQ "50!ju8!q9!j8!ij8!kqa>1v$1>1c$3@3$2$1@1$0@2$4^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_tail_set_avail_meta : ltac2:(zQ "50!jvc!q9!j8!ij8!kqa>1v$1>1c$3@3$2$1@1$0@2$4^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_areas_set_avail_meta : ltac2:(zQ "50!kh0!q9!j8!ij8!kqa>1v$1>1c$3@3$2$1@1$0@2$4^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_active_set_avail_meta : ltac2:(zQ "a0!ki6!j8!hgd!nb!ij8!q9!kqa!hm7!hr4!hjd>1v$5>1c$4@3$1@4$8$2$9$7$3@1$0@2$6^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_usage_set_avail_meta : ltac2:(zQ "90!hgd!kj1!j8!ij8!q9!kqa!hm7!hr4!hjd>1v$4>1c$3@3$2@4$7$0$8$6$0@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_unmap_seq_set_avail_meta : ltac2:(zQ "90!hgd!kjb!j8!ij8!q9!kqa!hm7!hr4!hjd>1v$4>1c$3@3$2@4$7$0$8$6$0@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_bounces_set_avail_meta : ltac2:(zQ "90!hgd!kk9!j8!ij8!q9!kqa!hm7!hr4!hjd>1v$4>1c$3@3$2@4$7$0$8$6$0@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_seq_set_avail_meta : ltac2:(zQ "60!kl5!j8!hgd!ij8!q9!kqa>1v$4>1c$3@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_brk_set_avail_meta : ltac2:(zQ "60!kld!j8!km5!ij8!q9!kqa>1v$4>1c$3@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_secret_set_avail_meta_count : ltac2:(zQ "50!hgd!jk7!j8!ij8!krb>1v$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_init_done_set_avail_meta_count : ltac2:(zQ "50!hgd!jlf!j8!ij8!krb>1v$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_mmap_counter_set_avail_meta_count : ltac2:(zQ "50!hgd!jmd!j8!ij8!krb>1v$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_free_meta_head_set_avail_meta_count : ltac2:(zQ "60!jne!j8!hgd!ij8!q9!krb>1v$2>1c$3@3$1$4@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_set_avail_meta_count : ltac2:(zQ "60!jp2!j8!hgd!ij8!q9!krb>1v$2>1c$3@3$1$4@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_count_set_avail_meta_count : ltac2:(zQ "50!hgd!j8!jq1!ij8!krb>1v$0>1c$3@3$1$0@1$2@2$4^2^1^2"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_avail_meta_count : ltac2:(zQ "50!hgd!jr7!j8!ij8!krb>1v$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_avail_meta_count : ltac2:(zQ "50!hgd!jt2!j8!ij8!krb>1v$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_head_set_avail_meta_count : ltac2:(zQ "60!ju8!j8!hgd!ij8!q9!krb>1v$2>1c$3@3$1$4@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_tail_set_avail_meta_count : ltac2:(zQ "60!jvc!j8!hgd!ij8!q9!krb>1v$2>1c$3@3$1$4@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_areas_set_avail_meta_count : ltac2:(zQ "60!kh0!j8!hgd!ij8!q9!krb>1v$2>1c$3@3$1$4@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_active_set_avail_meta_count : ltac2:(zQ "90!hgd!ki6!j8!nb!ij8!krb!hm7!hr4!hjd>1v$0>1c$4@3$2@4$7$0$8$6$3@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_usage_set_avail_meta_count : ltac2:(zQ "80!hgd!kj1!j8!ij8!krb!hm7!hr4!hjd>1v$0>1c$3@3$2@4$6$0$7$5$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_unmap_seq_set_avail_meta_count : ltac2:(zQ "80!hgd!kjb!j8!ij8!krb!hm7!hr4!hjd>1v$0>1c$3@3$2@4$6$0$7$5$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_bounces_set_avail_meta_count : ltac2:(zQ "80!hgd!kk9!j8!ij8!krb!hm7!hr4!hjd>1v$0>1c$3@3$2@4$6$0$7$5$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_seq_set_avail_meta_count : ltac2:(zQ "50!hgd!kl5!j8!ij8!krb>1v$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_brk_set_avail_meta_count : ltac2:(zQ "60!kld!j8!hgd!km5!ij8!krb>1v$2>1c$4@3$1$3@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_secret_set_avail_meta_area_count : ltac2:(zQ "50!hgd!jk7!j8!ij8!kt3>1v$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_init_done_set_avail_meta_area_count : ltac2:(zQ "50!hgd!jlf!j8!ij8!kt3>1v$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_mmap_counter_set_avail_meta_area_count : ltac2:(zQ "50!hgd!jmd!j8!ij8!kt3>1v$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_free_meta_head_set_avail_meta_area_count : ltac2:(zQ "60!jne!j8!hgd!ij8!q9!kt3>1v$2>1c$3@3$1$4@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_set_avail_meta_area_count : ltac2:(zQ "60!jp2!j8!hgd!ij8!q9!kt3>1v$2>1c$3@3$1$4@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_count_set_avail_meta_area_count : ltac2:(zQ "50!hgd!jq1!j8!ij8!kt3>1v$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_avail_meta_area_count : ltac2:(zQ "50!hgd!j8!jr7!ij8!kt3>1v$0>1c$3@3$1$0@1$2@2$4^2^1^2"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_avail_meta_area_count : ltac2:(zQ "50!hgd!jt2!j8!ij8!kt3>1v$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_head_set_avail_meta_area_count : ltac2:(zQ "60!ju8!j8!hgd!ij8!q9!kt3>1v$2>1c$3@3$1$4@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_tail_set_avail_meta_area_count : ltac2:(zQ "60!jvc!j8!hgd!ij8!q9!kt3>1v$2>1c$3@3$1$4@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_areas_set_avail_meta_area_count : ltac2:(zQ "60!kh0!j8!hgd!ij8!q9!kt3>1v$2>1c$3@3$1$4@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_active_set_avail_meta_area_count : ltac2:(zQ "90!hgd!ki6!j8!nb!ij8!kt3!hm7!hr4!hjd>1v$0>1c$4@3$2@4$7$0$8$6$3@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_usage_set_avail_meta_area_count : ltac2:(zQ "80!hgd!kj1!j8!ij8!kt3!hm7!hr4!hjd>1v$0>1c$3@3$2@4$6$0$7$5$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_unmap_seq_set_avail_meta_area_count : ltac2:(zQ "80!hgd!kjb!j8!ij8!kt3!hm7!hr4!hjd>1v$0>1c$3@3$2@4$6$0$7$5$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_bounces_set_avail_meta_area_count : ltac2:(zQ "80!hgd!kk9!j8!ij8!kt3!hm7!hr4!hjd>1v$0>1c$3@3$2@4$6$0$7$5$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_seq_set_avail_meta_area_count : ltac2:(zQ "50!hgd!kl5!j8!ij8!kt3>1v$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_brk_set_avail_meta_area_count : ltac2:(zQ "60!kld!j8!hgd!km5!ij8!kt3>1v$2>1c$4@3$1$3@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_secret_set_meta_alloc_shift : ltac2:(zQ "50!hgd!jk7!j8!ij8!kv0>1v$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_init_done_set_meta_alloc_shift : ltac2:(zQ "50!hgd!jlf!j8!ij8!kv0>1v$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_mmap_counter_set_meta_alloc_shift : ltac2:(zQ "50!hgd!jmd!j8!ij8!kv0>1v$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_free_meta_head_set_meta_alloc_shift : ltac2:(zQ "60!jne!j8!hgd!ij8!q9!kv0>1v$2>1c$3@3$1$4@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_set_meta_alloc_shift : ltac2:(zQ "60!jp2!j8!hgd!ij8!q9!kv0>1v$2>1c$3@3$1$4@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_count_set_meta_alloc_shift : ltac2:(zQ "50!hgd!jq1!j8!ij8!kv0>1v$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_meta_alloc_shift : ltac2:(zQ "50!hgd!jr7!j8!ij8!kv0>1v$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_meta_alloc_shift : ltac2:(zQ "50!hgd!j8!jt2!ij8!kv0>1v$0>1c$3@3$1$0@1$2@2$4^2^1^2"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_head_set_meta_alloc_shift : ltac2:(zQ "60!ju8!j8!hgd!ij8!q9!kv0>1v$2>1c$3@3$1$4@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_tail_set_meta_alloc_shift : ltac2:(zQ "60!jvc!j8!hgd!ij8!q9!kv0>1v$2>1c$3@3$1$4@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_areas_set_meta_alloc_shift : ltac2:(zQ "60!kh0!j8!hgd!ij8!q9!kv0>1v$2>1c$3@3$1$4@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_active_set_meta_alloc_shift : ltac2:(zQ "90!hgd!ki6!j8!nb!ij8!kv0!hm7!hr4!hjd>1v$0>1c$4@3$2@4$7$0$8$6$3@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_usage_set_meta_alloc_shift : ltac2:(zQ "80!hgd!kj1!j8!ij8!kv0!hm7!hr4!hjd>1v$0>1c$3@3$2@4$6$0$7$5$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_unmap_seq_set_meta_alloc_shift : ltac2:(zQ "80!hgd!kjb!j8!ij8!kv0!hm7!hr4!hjd>1v$0>1c$3@3$2@4$6$0$7$5$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_bounces_set_meta_alloc_shift : ltac2:(zQ "80!hgd!kk9!j8!ij8!kv0!hm7!hr4!hjd>1v$0>1c$3@3$2@4$6$0$7$5$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_seq_set_meta_alloc_shift : ltac2:(zQ "50!hgd!kl5!j8!ij8!kv0>1v$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_brk_set_meta_alloc_shift : ltac2:(zQ "60!kld!j8!hgd!km5!ij8!kv0>1v$2>1c$4@3$1$3@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_secret_set_meta_area_head : ltac2:(zQ "60!jk7!j8!hgd!ij8!q9!lg8>1v$4>1c$3@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_init_done_set_meta_area_head : ltac2:(zQ "60!jlf!j8!hgd!ij8!q9!lg8>1v$4>1c$3@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_mmap_counter_set_meta_area_head : ltac2:(zQ "60!jmd!j8!hgd!ij8!q9!lg8>1v$4>1c$3@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_free_meta_head_set_meta_area_head : ltac2:(zQ "50!jne!q9!j8!ij8!lg8>1v$1>1c$3@3$2$1@1$0@2$4^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_set_meta_area_head : ltac2:(zQ "50!jp2!q9!j8!ij8!lg8>1v$1>1c$3@3$2$1@1$0@2$4^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_count_set_meta_area_head : ltac2:(zQ "60!jq1!j8!hgd!ij8!q9!lg8>1v$4>1c$3@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_meta_area_head : ltac2:(zQ "60!jr7!j8!hgd!ij8!q9!lg8>1v$4>1c$3@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_meta_area_head : ltac2:(zQ "60!jt2!j8!hgd!ij8!q9!lg8>1v$4>1c$3@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_head_set_meta_area_head : ltac2:(zQ "50!q9!j8!ju8!ij8!lg8>1v$0>1c$3@3$1$0@1$2@2$4^2^1^2"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_tail_set_meta_area_head : ltac2:(zQ "50!jvc!q9!j8!ij8!lg8>1v$1>1c$3@3$2$1@1$0@2$4^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_areas_set_meta_area_head : ltac2:(zQ "50!kh0!q9!j8!ij8!lg8>1v$1>1c$3@3$2$1@1$0@2$4^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_active_set_meta_area_head : ltac2:(zQ "a0!ki6!j8!hgd!nb!ij8!q9!lg8!hm7!hr4!hjd>1v$5>1c$4@3$1@4$8$2$9$7$3@1$0@2$6^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_usage_set_meta_area_head : ltac2:(zQ "90!hgd!kj1!j8!ij8!q9!lg8!hm7!hr4!hjd>1v$4>1c$3@3$2@4$7$0$8$6$0@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_unmap_seq_set_meta_area_head : ltac2:(zQ "90!hgd!kjb!j8!ij8!q9!lg8!hm7!hr4!hjd>1v$4>1c$3@3$2@4$7$0$8$6$0@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_bounces_set_meta_area_head : ltac2:(zQ "90!hgd!kk9!j8!ij8!q9!lg8!hm7!hr4!hjd>1v$4>1c$3@3$2@4$7$0$8$6$0@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_seq_set_meta_area_head : ltac2:(zQ "60!kl5!j8!hgd!ij8!q9!lg8>1v$4>1c$3@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_brk_set_meta_area_head : ltac2:(zQ "60!kld!j8!km5!ij8!q9!lg8>1v$4>1c$3@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_secret_set_meta_area_tail : ltac2:(zQ "60!jk7!j8!hgd!ij8!q9!lhe>1v$4>1c$3@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_init_done_set_meta_area_tail : ltac2:(zQ "60!jlf!j8!hgd!ij8!q9!lhe>1v$4>1c$3@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_mmap_counter_set_meta_area_tail : ltac2:(zQ "60!jmd!j8!hgd!ij8!q9!lhe>1v$4>1c$3@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_free_meta_head_set_meta_area_tail : ltac2:(zQ "50!jne!q9!j8!ij8!lhe>1v$1>1c$3@3$2$1@1$0@2$4^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_set_meta_area_tail : ltac2:(zQ "50!jp2!q9!j8!ij8!lhe>1v$1>1c$3@3$2$1@1$0@2$4^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_count_set_meta_area_tail : ltac2:(zQ "60!jq1!j8!hgd!ij8!q9!lhe>1v$4>1c$3@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_meta_area_tail : ltac2:(zQ "60!jr7!j8!hgd!ij8!q9!lhe>1v$4>1c$3@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_meta_area_tail : ltac2:(zQ "60!jt2!j8!hgd!ij8!q9!lhe>1v$4>1c$3@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_head_set_meta_area_tail : ltac2:(zQ "50!ju8!q9!j8!ij8!lhe>1v$1>1c$3@3$2$1@1$0@2$4^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_tail_set_meta_area_tail : ltac2:(zQ "50!q9!j8!jvc!ij8!lhe>1v$0>1c$3@3$1$0@1$2@2$4^2^1^2"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_areas_set_meta_area_tail : ltac2:(zQ "50!kh0!q9!j8!ij8!lhe>1v$1>1c$3@3$2$1@1$0@2$4^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_active_set_meta_area_tail : ltac2:(zQ "a0!ki6!j8!hgd!nb!ij8!q9!lhe!hm7!hr4!hjd>1v$5>1c$4@3$1@4$8$2$9$7$3@1$0@2$6^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_usage_set_meta_area_tail : ltac2:(zQ "90!hgd!kj1!j8!ij8!q9!lhe!hm7!hr4!hjd>1v$4>1c$3@3$2@4$7$0$8$6$0@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_unmap_seq_set_meta_area_tail : ltac2:(zQ "90!hgd!kjb!j8!ij8!q9!lhe!hm7!hr4!hjd>1v$4>1c$3@3$2@4$7$0$8$6$0@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_bounces_set_meta_area_tail : ltac2:(zQ "90!hgd!kk9!j8!ij8!q9!lhe!hm7!hr4!hjd>1v$4>1c$3@3$2@4$7$0$8$6$0@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_seq_set_meta_area_tail : ltac2:(zQ "60!kl5!j8!hgd!ij8!q9!lhe>1v$4>1c$3@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_brk_set_meta_area_tail : ltac2:(zQ "60!kld!j8!km5!ij8!q9!lhe>1v$4>1c$3@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_secret_set_avail_meta_areas : ltac2:(zQ "60!jk7!j8!hgd!ij8!q9!lj4>1v$4>1c$3@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_init_done_set_avail_meta_areas : ltac2:(zQ "60!jlf!j8!hgd!ij8!q9!lj4>1v$4>1c$3@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_mmap_counter_set_avail_meta_areas : ltac2:(zQ "60!jmd!j8!hgd!ij8!q9!lj4>1v$4>1c$3@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_free_meta_head_set_avail_meta_areas : ltac2:(zQ "50!jne!q9!j8!ij8!lj4>1v$1>1c$3@3$2$1@1$0@2$4^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_set_avail_meta_areas : ltac2:(zQ "50!jp2!q9!j8!ij8!lj4>1v$1>1c$3@3$2$1@1$0@2$4^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_count_set_avail_meta_areas : ltac2:(zQ "60!jq1!j8!hgd!ij8!q9!lj4>1v$4>1c$3@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_avail_meta_areas : ltac2:(zQ "60!jr7!j8!hgd!ij8!q9!lj4>1v$4>1c$3@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_avail_meta_areas : ltac2:(zQ "60!jt2!j8!hgd!ij8!q9!lj4>1v$4>1c$3@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_head_set_avail_meta_areas : ltac2:(zQ "50!ju8!q9!j8!ij8!lj4>1v$1>1c$3@3$2$1@1$0@2$4^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_tail_set_avail_meta_areas : ltac2:(zQ "50!jvc!q9!j8!ij8!lj4>1v$1>1c$3@3$2$1@1$0@2$4^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_areas_set_avail_meta_areas : ltac2:(zQ "50!q9!j8!kh0!ij8!lj4>1v$0>1c$3@3$1$0@1$2@2$4^2^1^2"). Proof. intros v c. reflexivity. Qed.
Lemma c_active_set_avail_meta_areas : ltac2:(zQ "a0!ki6!j8!hgd!nb!ij8!q9!lj4!hm7!hr4!hjd>1v$5>1c$4@3$1@4$8$2$9$7$3@1$0@2$6^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_usage_set_avail_meta_areas : ltac2:(zQ "90!hgd!kj1!j8!ij8!q9!lj4!hm7!hr4!hjd>1v$4>1c$3@3$2@4$7$0$8$6$0@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_unmap_seq_set_avail_meta_areas : ltac2:(zQ "90!hgd!kjb!j8!ij8!q9!lj4!hm7!hr4!hjd>1v$4>1c$3@3$2@4$7$0$8$6$0@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_bounces_set_avail_meta_areas : ltac2:(zQ "90!hgd!kk9!j8!ij8!q9!lj4!hm7!hr4!hjd>1v$4>1c$3@3$2@4$7$0$8$6$0@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_seq_set_avail_meta_areas : ltac2:(zQ "60!kl5!j8!hgd!ij8!q9!lj4>1v$4>1c$3@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_brk_set_avail_meta_areas : ltac2:(zQ "60!kld!j8!km5!ij8!q9!lj4>1v$4>1c$3@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_secret_set_active_map : ltac2:(zQ "90!hgd!jk7!j8!nb!ij8!lkc!hm7!hr4!hjd>1v@4$7$0$8$6$3>1c$4@3$2$0@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_init_done_set_active_map : ltac2:(zQ "90!hgd!jlf!j8!nb!ij8!lkc!hm7!hr4!hjd>1v@4$7$0$8$6$3>1c$4@3$2$0@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_mmap_counter_set_active_map : ltac2:(zQ "90!hgd!jmd!j8!nb!ij8!lkc!hm7!hr4!hjd>1v@4$7$0$8$6$3>1c$4@3$2$0@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_free_meta_head_set_active_map : ltac2:(zQ "a0!jne!j8!hgd!nb!ij8!q9!lkc!hm7!hr4!hjd>1v@4$8$2$9$7$3>1c$4@3$1$5@1$0@2$6^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_set_active_map : ltac2:(zQ "a0!jp2!j8!hgd!nb!ij8!q9!lkc!hm7!hr4!hjd>1v@4$8$2$9$7$3>1c$4@3$1$5@1$0@2$6^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_count_set_active_map : ltac2:(zQ "90!hgd!jq1!j8!nb!ij8!lkc!hm7!hr4!hjd>1v@4$7$0$8$6$3>1c$4@3$2$0@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_active_map : ltac2:(zQ "90!hgd!jr7!j8!nb!ij8!lkc!hm7!hr4!hjd>1v@4$7$0$8$6$3>1c$4@3$2$0@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_active_map : ltac2:(zQ "90!hgd!jt2!j8!nb!ij8!lkc!hm7!hr4!hjd>1v@4$7$0$8$6$3>1c$4@3$2$0@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_head_set_active_map : ltac2:(zQ "a0!ju8!j8!hgd!nb!ij8!q9!lkc!hm7!hr4!hjd>1v@4$8$2$9$7$3>1c$4@3$1$5@1$0@2$6^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_tail_set_active_map : ltac2:(zQ "a0!jvc!j8!hgd!nb!ij8!q9!lkc!hm7!hr4!hjd>1v@4$8$2$9$7$3>1c$4@3$1$5@1$0@2$6^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_areas_set_active_map : ltac2:(zQ "a0!kh0!j8!hgd!nb!ij8!q9!lkc!hm7!hr4!hjd>1v@4$8$2$9$7$3>1c$4@3$1$5@1$0@2$6^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_active_set_active_map : ltac2:(zQ "90!hgd!nb!hm7!hr4!hjd!j8!ki6!ij8!lkc>1v@4$3$0$4$2$1>1c$7@3$5@4$3$0$4$2$1@1$6@2$8^2^1^2"). Proof. intros v c. reflexivity. Qed.
Lemma c_usage_set_active_map : ltac2:(zQ "90!hgd!kj1!hm7!hr4!hjd!j8!nb!ij8!lkc>1v@4$3$0$4$2$6>1c$7@3$5@4$3$0$4$2$0@1$1@2$8^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_unmap_seq_set_active_map : ltac2:(zQ "90!hgd!kjb!hm7!hr4!hjd!j8!nb!ij8!lkc>1v@4$3$0$4$2$6>1c$7@3$5@4$3$0$4$2$0@1$1@2$8^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_bounces_set_active_map : ltac2:(zQ "90!hgd!kk9!hm7!hr4!hjd!j8!nb!ij8!lkc>1v@4$3$0$4$2$6>1c$7@3$5@4$3$0$4$2$0@1$1@2$8^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_seq_set_active_map : ltac2:(zQ "90!hgd!kl5!j8!nb!ij8!lkc!hm7!hr4!hjd>1v@4$7$0$8$6$3>1c$4@3$2$0@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_brk_set_active_map : ltac2:(zQ "a0!kld!j8!hgd!nb!km5!ij8!lkc!hm7!hr4!hjd>1v@4$8$2$9$7$3>1c$5@3$1$4@1$0@2$6^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_secret_set_usage_map : ltac2:(zQ "80!hgd!jk7!j8!ij8!lld!hm7!hr4!hjd>1v@4$6$0$7$5$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_init_done_set_usage_map : ltac2:(zQ "80!hgd!jlf!j8!ij8!lld!hm7!hr4!hjd>1v@4$6$0$7$5$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_mmap_counter_set_usage_map : ltac2:(zQ "80!hgd!jmd!j8!ij8!lld!hm7!hr4!hjd>1v@4$6$0$7$5$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_free_meta_head_set_usage_map : ltac2:(zQ "90!hgd!jne!j8!ij8!q9!lld!hm7!hr4!hjd>1v@4$7$0$8$6$0>1c$3@3$2$4@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_set_usage_map : ltac2:(zQ "90!hgd!jp2!j8!ij8!q9!lld!hm7!hr4!hjd>1v@4$7$0$8$6$0>1c$3@3$2$4@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_count_set_usage_map : ltac2:(zQ "80!hgd!jq1!j8!ij8!lld!hm7!hr4!hjd>1v@4$6$0$7$5$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_usage_map : ltac2:(zQ "80!hgd!jr7!j8!ij8!lld!hm7!hr4!hjd>1v@4$6$0$7$5$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_usage_map : ltac2:(zQ "80!hgd!jt2!j8!ij8!lld!hm7!hr4!hjd>1v@4$6$0$7$5$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_head_set_usage_map : ltac2:(zQ "90!hgd!ju8!j8!ij8!q9!lld!hm7!hr4!hjd>1v@4$7$0$8$6$0>1c$3@3$2$4@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_tail_set_usage_map : ltac2:(zQ "90!hgd!jvc!j8!ij8!q9!lld!hm7!hr4!hjd>1v@4$7$0$8$6$0>1c$3@3$2$4@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_areas_set_usage_map : ltac2:(zQ "90!hgd!kh0!j8!ij8!q9!lld!hm7!hr4!hjd>1v@4$7$0$8$6$0>1c$3@3$2$4@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_active_set_usage_map : ltac2:(zQ "90!hgd!ki6!hm7!hr4!hjd!j8!nb!ij8!lld>1v@4$3$0$4$2$0>1c$7@3$5@4$3$0$4$2$6@1$1@2$8^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_usage_set_usage_map : ltac2:(zQ "80!hgd!hm7!hr4!hjd!j8!kj1!ij8!lld>1v@4$2$0$3$1$0>1c$6@3$4@4$2$0$3$1$0@1$5@2$7^2^1^2"). Proof. intros v c. reflexivity. Qed.
Lemma c_unmap_seq_set_usage_map : ltac2:(zQ "80!hgd!kjb!hm7!hr4!hjd!j8!ij8!lld>1v@4$3$0$4$2$0>1c$6@3$5@4$3$0$4$2$0@1$1@2$7^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_bounces_set_usage_map : ltac2:(zQ "80!hgd!kk9!hm7!hr4!hjd!j8!ij8!lld>1v@4$3$0$4$2$0>1c$6@3$5@4$3$0$4$2$0@1$1@2$7^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_seq_set_usage_map : ltac2:(zQ "80!hgd!kl5!j8!ij8!lld!hm7!hr4!hjd>1v@4$6$0$7$5$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_brk_set_usage_map : ltac2:(zQ "90!hgd!kld!j8!km5!ij8!lld!hm7!hr4!hjd>1v@4$7$0$8$6$0>1c$4@3$2$3@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_secret_set_unmap_seq_map : ltac2:(zQ "80!hgd!jk7!j8!ij8!lmd!hm7!hr4!hjd>1v@4$6$0$7$5$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_init_done_set_unmap_seq_map : ltac2:(zQ "80!hgd!jlf!j8!ij8!lmd!hm7!hr4!hjd>1v@4$6$0$7$5$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_mmap_counter_set_unmap_seq_map : ltac2:(zQ "80!hgd!jmd!j8!ij8!lmd!hm7!hr4!hjd>1v@4$6$0$7$5$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_free_meta_head_set_unmap_seq_map : ltac2:(zQ "90!hgd!jne!j8!ij8!q9!lmd!hm7!hr4!hjd>1v@4$7$0$8$6$0>1c$3@3$2$4@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_set_unmap_seq_map : ltac2:(zQ "90!hgd!jp2!j8!ij8!q9!lmd!hm7!hr4!hjd>1v@4$7$0$8$6$0>1c$3@3$2$4@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_count_set_unmap_seq_map : ltac2:(zQ "80!hgd!jq1!j8!ij8!lmd!hm7!hr4!hjd>1v@4$6$0$7$5$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_unmap_seq_map : ltac2:(zQ "80!hgd!jr7!j8!ij8!lmd!hm7!hr4!hjd>1v@4$6$0$7$5$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_unmap_seq_map : ltac2:(zQ "80!hgd!jt2!j8!ij8!lmd!hm7!hr4!hjd>1v@4$6$0$7$5$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_head_set_unmap_seq_map : ltac2:(zQ "90!hgd!ju8!j8!ij8!q9!lmd!hm7!hr4!hjd>1v@4$7$0$8$6$0>1c$3@3$2$4@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_tail_set_unmap_seq_map : ltac2:(zQ "90!hgd!jvc!j8!ij8!q9!lmd!hm7!hr4!hjd>1v@4$7$0$8$6$0>1c$3@3$2$4@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_areas_set_unmap_seq_map : ltac2:(zQ "90!hgd!kh0!j8!ij8!q9!lmd!hm7!hr4!hjd>1v@4$7$0$8$6$0>1c$3@3$2$4@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_active_set_unmap_seq_map : ltac2:(zQ "90!hgd!ki6!hm7!hr4!hjd!j8!nb!ij8!lmd>1v@4$3$0$4$2$0>1c$7@3$5@4$3$0$4$2$6@1$1@2$8^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_usage_set_unmap_seq_map : ltac2:(zQ "80!hgd!kj1!hm7!hr4!hjd!j8!ij8!lmd>1v@4$3$0$4$2$0>1c$6@3$5@4$3$0$4$2$0@1$1@2$7^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_unmap_seq_set_unmap_seq_map : ltac2:(zQ "80!hgd!hm7!hr4!hjd!j8!kjb!ij8!lmd>1v@4$2$0$3$1$0>1c$6@3$4@4$2$0$3$1$0@1$5@2$7^2^1^2"). Proof. intros v c. reflexivity. Qed.
Lemma c_bounces_set_unmap_seq_map : ltac2:(zQ "80!hgd!kk9!hm7!hr4!hjd!j8!ij8!lmd>1v@4$3$0$4$2$0>1c$6@3$5@4$3$0$4$2$0@1$1@2$7^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_seq_set_unmap_seq_map : ltac2:(zQ "80!hgd!kl5!j8!ij8!lmd!hm7!hr4!hjd>1v@4$6$0$7$5$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_brk_set_unmap_seq_map : ltac2:(zQ "90!hgd!kld!j8!km5!ij8!lmd!hm7!hr4!hjd>1v@4$7$0$8$6$0>1c$4@3$2$3@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_secret_set_bounces_map : ltac2:(zQ "80!hgd!jk7!j8!ij8!lo2!hm7!hr4!hjd>1v@4$6$0$7$5$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_init_done_set_bounces_map : ltac2:(zQ "80!hgd!jlf!j8!ij8!lo2!hm7!hr4!hjd>1v@4$6$0$7$5$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_mmap_counter_set_bounces_map : ltac2:(zQ "80!hgd!jmd!j8!ij8!lo2!hm7!hr4!hjd>1v@4$6$0$7$5$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_free_meta_head_set_bounces_map : ltac2:(zQ "90!hgd!jne!j8!ij8!q9!lo2!hm7!hr4!hjd>1v@4$7$0$8$6$0>1c$3@3$2$4@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_set_bounces_map : ltac2:(zQ "90!hgd!jp2!j8!ij8!q9!lo2!hm7!hr4!hjd>1v@4$7$0$8$6$0>1c$3@3$2$4@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_count_set_bounces_map : ltac2:(zQ "80!hgd!jq1!j8!ij8!lo2!hm7!hr4!hjd>1v@4$6$0$7$5$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_bounces_map : ltac2:(zQ "80!hgd!jr7!j8!ij8!lo2!hm7!hr4!hjd>1v@4$6$0$7$5$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_bounces_map : ltac2:(zQ "80!hgd!jt2!j8!ij8!lo2!hm7!hr4!hjd>1v@4$6$0$7$5$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_head_set_bounces_map : ltac2:(zQ "90!hgd!ju8!j8!ij8!q9!lo2!hm7!hr4!hjd>1v@4$7$0$8$6$0>1c$3@3$2$4@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_tail_set_bounces_map : ltac2:(zQ "90!hgd!jvc!j8!ij8!q9!lo2!hm7!hr4!hjd>1v@4$7$0$8$6$0>1c$3@3$2$4@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_areas_set_bounces_map : ltac2:(zQ "90!hgd!kh0!j8!ij8!q9!lo2!hm7!hr4!hjd>1v@4$7$0$8$6$0>1c$3@3$2$4@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_active_set_bounces_map : ltac2:(zQ "90!hgd!ki6!hm7!hr4!hjd!j8!nb!ij8!lo2>1v@4$3$0$4$2$0>1c$7@3$5@4$3$0$4$2$6@1$1@2$8^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_usage_set_bounces_map : ltac2:(zQ "80!hgd!kj1!hm7!hr4!hjd!j8!ij8!lo2>1v@4$3$0$4$2$0>1c$6@3$5@4$3$0$4$2$0@1$1@2$7^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_unmap_seq_set_bounces_map : ltac2:(zQ "80!hgd!kjb!hm7!hr4!hjd!j8!ij8!lo2>1v@4$3$0$4$2$0>1c$6@3$5@4$3$0$4$2$0@1$1@2$7^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_bounces_set_bounces_map : ltac2:(zQ "80!hgd!hm7!hr4!hjd!j8!kk9!ij8!lo2>1v@4$2$0$3$1$0>1c$6@3$4@4$2$0$3$1$0@1$5@2$7^2^1^2"). Proof. intros v c. reflexivity. Qed.
Lemma c_seq_set_bounces_map : ltac2:(zQ "80!hgd!kl5!j8!ij8!lo2!hm7!hr4!hjd>1v@4$6$0$7$5$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_brk_set_bounces_map : ltac2:(zQ "90!hgd!kld!j8!km5!ij8!lo2!hm7!hr4!hjd>1v@4$7$0$8$6$0>1c$4@3$2$3@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_secret_set_seq : ltac2:(zQ "50!hgd!jk7!j8!ij8!lp4>1v$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_init_done_set_seq : ltac2:(zQ "50!hgd!jlf!j8!ij8!lp4>1v$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_mmap_counter_set_seq : ltac2:(zQ "50!hgd!jmd!j8!ij8!lp4>1v$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_free_meta_head_set_seq : ltac2:(zQ "60!jne!j8!hgd!ij8!q9!lp4>1v$2>1c$3@3$1$4@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_set_seq : ltac2:(zQ "60!jp2!j8!hgd!ij8!q9!lp4>1v$2>1c$3@3$1$4@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_count_set_seq : ltac2:(zQ "50!hgd!jq1!j8!ij8!lp4>1v$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_seq : ltac2:(zQ "50!hgd!jr7!j8!ij8!lp4>1v$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_seq : ltac2:(zQ "50!hgd!jt2!j8!ij8!lp4>1v$0>1c$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_head_set_seq : ltac2:(zQ "60!ju8!j8!hgd!ij8!q9!lp4>1v$2>1c$3@3$1$4@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_tail_set_seq : ltac2:(zQ "60!jvc!j8!hgd!ij8!q9!lp4>1v$2>1c$3@3$1$4@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_areas_set_seq : ltac2:(zQ "60!kh0!j8!hgd!ij8!q9!lp4>1v$2>1c$3@3$1$4@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_active_set_seq : ltac2:(zQ "90!hgd!ki6!j8!nb!ij8!lp4!hm7!hr4!hjd>1v$0>1c$4@3$2@4$7$0$8$6$3@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_usage_set_seq : ltac2:(zQ "80!hgd!kj1!j8!ij8!lp4!hm7!hr4!hjd>1v$0>1c$3@3$2@4$6$0$7$5$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_unmap_seq_set_seq : ltac2:(zQ "80!hgd!kjb!j8!ij8!lp4!hm7!hr4!hjd>1v$0>1c$3@3$2@4$6$0$7$5$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_bounces_set_seq : ltac2:(zQ "80!hgd!kk9!j8!ij8!lp4!hm7!hr4!hjd>1v$0>1c$3@3$2@4$6$0$7$5$0@1$1@2$4^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_seq_set_seq : ltac2:(zQ "50!hgd!j8!kl5!ij8!lp4>1v$0>1c$3@3$1$0@1$2@2$4^2^1^2"). Proof. intros v c. reflexivity. Qed.
Lemma c_brk_set_seq : ltac2:(zQ "60!kld!j8!hgd!km5!ij8!lp4>1v$2>1c$4@3$1$3@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_secret_set_brk : ltac2:(zQ "60!jk7!j8!hgd!km5!ij8!lpe>1v$3>1c$4@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_init_done_set_brk : ltac2:(zQ "60!jlf!j8!hgd!km5!ij8!lpe>1v$3>1c$4@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_mmap_counter_set_brk : ltac2:(zQ "60!jmd!j8!hgd!km5!ij8!lpe>1v$3>1c$4@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_free_meta_head_set_brk : ltac2:(zQ "60!jne!j8!km5!ij8!q9!lpe>1v$2>1c$3@3$1$4@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_set_brk : ltac2:(zQ "60!jp2!j8!km5!ij8!q9!lpe>1v$2>1c$3@3$1$4@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_count_set_brk : ltac2:(zQ "60!jq1!j8!hgd!km5!ij8!lpe>1v$3>1c$4@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_brk : ltac2:(zQ "60!jr7!j8!hgd!km5!ij8!lpe>1v$3>1c$4@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_brk : ltac2:(zQ "60!jt2!j8!hgd!km5!ij8!lpe>1v$3>1c$4@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_head_set_brk : ltac2:(zQ "60!ju8!j8!km5!ij8!q9!lpe>1v$2>1c$3@3$1$4@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_tail_set_brk : ltac2:(zQ "60!jvc!j8!km5!ij8!q9!lpe>1v$2>1c$3@3$1$4@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_areas_set_brk : ltac2:(zQ "60!kh0!j8!km5!ij8!q9!lpe>1v$2>1c$3@3$1$4@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_active_set_brk : ltac2:(zQ "a0!ki6!j8!hgd!nb!km5!ij8!lpe!hm7!hr4!hjd>1v$4>1c$5@3$1@4$8$2$9$7$3@1$0@2$6^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_usage_set_brk : ltac2:(zQ "90!hgd!kj1!j8!km5!ij8!lpe!hm7!hr4!hjd>1v$3>1c$4@3$2@4$7$0$8$6$0@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_unmap_seq_set_brk : ltac2:(zQ "90!hgd!kjb!j8!km5!ij8!lpe!hm7!hr4!hjd>1v$3>1c$4@3$2@4$7$0$8$6$0@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_bounces_set_brk : ltac2:(zQ "90!hgd!kk9!j8!km5!ij8!lpe!hm7!hr4!hjd>1v$3>1c$4@3$2@4$7$0$8$6$0@1$1@2$5^2^1@1$1^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_seq_set_brk : ltac2:(zQ "60!kl5!j8!hgd!km5!ij8!lpe>1v$3>1c$4@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros v c. reflexivity. Qed.
Lemma c_brk_set_brk : ltac2:(zQ "50!km5!j8!kld!ij8!lpe>1v$0>1c$3@3$1$0@1$2@2$4^2^1^2"). Proof. intros v c. reflexivity. Qed.
#[export] Hint Rewrite s_ctx_upd_ctx s_regions_upd_ctx s_shadow_upd_ctx s_next_rid_upd_ctx s_metas_upd_ctx s_areas_upd_ctx s_groups_upd_ctx s_slots_upd_ctx s_tick_upd_ctx s_secret_upd_ctx s_reserved_upd_ctx s_ctx_set_regions s_regions_set_regions s_shadow_set_regions s_next_rid_set_regions s_metas_set_regions s_areas_set_regions s_groups_set_regions s_slots_set_regions s_tick_set_regions s_secret_set_regions s_reserved_set_regions s_ctx_set_shadow s_regions_set_shadow s_shadow_set_shadow s_next_rid_set_shadow s_metas_set_shadow s_areas_set_shadow s_groups_set_shadow s_slots_set_shadow s_tick_set_shadow s_secret_set_shadow s_reserved_set_shadow s_ctx_set_next_rid s_regions_set_next_rid s_shadow_set_next_rid s_next_rid_set_next_rid s_metas_set_next_rid s_areas_set_next_rid s_groups_set_next_rid s_slots_set_next_rid s_tick_set_next_rid s_secret_set_next_rid s_reserved_set_next_rid s_ctx_set_metas s_regions_set_metas s_shadow_set_metas s_next_rid_set_metas s_metas_set_metas s_areas_set_metas s_groups_set_metas s_slots_set_metas s_tick_set_metas s_secret_set_metas s_reserved_set_metas s_ctx_set_areas s_regions_set_areas s_shadow_set_areas s_next_rid_set_areas s_metas_set_areas s_areas_set_areas s_groups_set_areas s_slots_set_areas s_tick_set_areas s_secret_set_areas s_reserved_set_areas s_ctx_set_groups s_regions_set_groups s_shadow_set_groups s_next_rid_set_groups s_metas_set_groups s_areas_set_groups s_groups_set_groups s_slots_set_groups s_tick_set_groups s_secret_set_groups s_reserved_set_groups s_ctx_set_slots s_regions_set_slots s_shadow_set_slots s_next_rid_set_slots s_metas_set_slots s_areas_set_slots s_groups_set_slots s_slots_set_slots s_tick_set_slots s_secret_set_slots s_reserved_set_slots s_ctx_set_tick s_regions_set_tick s_shadow_set_tick s_next_rid_set_tick s_metas_set_tick s_areas_set_tick s_groups_set_tick s_slots_set_tick s_tick_set_tick s_secret_set_tick s_reserved_set_tick c_secret_set_secret c_init_done_set_secret c_mmap_counter_set_secret c_free_meta_head_set_secret c_avail_meta_set_secret c_avail_meta_count_set_secret c_avail_meta_area_count_set_secret c_meta_alloc_shift_set_secret c_meta_area_head_set_secret c_meta_area_tail_set_secret c_avail_meta_areas_set_secret c_active_set_secret c_usage_set_secret c_unmap_seq_set_secret c_bounces_set_secret c_seq_set_secret c_brk_set_secret c_secret_set_init_done c_init_done_set_init_done c_mmap_counter_set_init_done c_free_meta_head_set_init_done c_avail_meta_set_init_done c_avail_meta_count_set_init_done c_avail_meta_area_count_set_init_done c_meta_alloc_shift_set_init_done c_meta_area_head_set_init_done c_meta_area_tail_set_init_done c_avail_meta_areas_set_init_done c_active_set_init_done c_usage_set_init_done c_unmap_seq_set_init_done c_bounces_set_init_done c_seq_set_init_done c_brk_set_init_done c_secret_set_mmap_counter c_init_done_set_mmap_counter c_mmap_counter_set_mmap_counter c_free_meta_head_set_mmap_counter c_avail_meta_set_mmap_counter c_avail_meta_count_set_mmap_counter c_avail_meta_area_count_set_mmap_counter c_meta_alloc_shift_set_mmap_counter c_meta_area_head_set_mmap_counter c_meta_area_tail_set_mmap_counter c_avail_meta_areas_set_mmap_counter c_active_set_mmap_counter c_usage_set_mmap_counter c_unmap_seq_set_mmap_counter c_bounces_set_mmap_counter c_seq_set_mmap_counter c_brk_set_mmap_counter c_secret_set_free_meta_head c_init_done_set_free_meta_head c_mmap_counter_set_free_meta_head c_free_meta_head_set_free_meta_head c_avail_meta_set_free_meta_head c_avail_meta_count_set_free_meta_head c_avail_meta_area_count_set_free_meta_head c_meta_alloc_shift_set_free_meta_head c_meta_area_head_set_free_meta_head c_meta_area_tail_set_free_meta_head c_avail_meta_areas_set_free_meta_head c_active_set_free_meta_head c_usage_set_free_meta_head c_unmap_seq_set_free_meta_head c_bounces_set_free_meta_head c_seq_set_free_meta_head c_brk_set_free_meta_head c_secret_set_avail_meta c_init_done_set_avail_meta c_mmap_counter_set_avail_meta c_free_meta_head_set_avail_meta c_avail_meta_set_avail_meta c_avail_meta_count_set_avail_meta c_avail_meta_area_count_set_avail_meta c_meta_alloc_shift_set_avail_meta c_meta_area_head_set_avail_meta c_meta_area_tail_set_avail_meta c_avail_meta_areas_set_avail_meta c_active_set_avail_meta c_usage_set_avail_meta c_unmap_seq_set_avail_meta c_bounces_set_avail_meta c_seq_set_avail_meta c_brk_set_avail_meta c_secret_set_avail_meta_count c_init_done_set_avail_meta_count c_mmap_counter_set_avail_meta_count c_free_meta_head_set_avail_meta_count c_avail_meta_set_avail_meta_count c_avail_meta_count_set_avail_meta_count c_avail_meta_area_count_set_avail_meta_count c_meta_alloc_shift_set_avail_meta_count c_meta_area_head_set_avail_meta_count c_meta_area_tail_set_avail_meta_count c_avail_meta_areas_set_avail_meta_count c_active_set_avail_meta_count c_usage_set_avail_meta_count c_unmap_seq_set_avail_meta_count c_bounces_set_avail_meta_count c_seq_set_avail_meta_count c_brk_set_avail_meta_count c_secret_set_avail_meta_area_count c_init_done_set_avail_meta_area_count c_mmap_counter_set_avail_meta_area_count c_free_meta_head_set_avail_meta_area_count c_avail_meta_set_avail_meta_area_count c_avail_meta_count_set_avail_meta_area_count c_avail_meta_area_count_set_avail_meta_area_count c_meta_alloc_shift_set_avail_meta_area_count c_meta_area_head_set_avail_meta_area_count c_meta_area_tail_set_avail_meta_area_count c_avail_meta_areas_set_avail_meta_area_count c_active_set_avail_meta_area_count c_usage_set_avail_meta_area_count c_unmap_seq_set_avail_meta_area_count c_bounces_set_avail_meta_area_count c_seq_set_avail_meta_area_count c_brk_set_avail_meta_area_count c_secret_set_meta_alloc_shift c_init_done_set_meta_alloc_shift c_mmap_counter_set_meta_alloc_shift c_free_meta_head_set_meta_alloc_shift c_avail_meta_set_meta_alloc_shift c_avail_meta_count_set_meta_alloc_shift c_avail_meta_area_count_set_meta_alloc_shift c_meta_alloc_shift_set_meta_alloc_shift c_meta_area_head_set_meta_alloc_shift c_meta_area_tail_set_meta_alloc_shift c_avail_meta_areas_set_meta_alloc_shift c_active_set_meta_alloc_shift c_usage_set_meta_alloc_shift c_unmap_seq_set_meta_alloc_shift c_bounces_set_meta_alloc_shift c_seq_set_meta_alloc_shift c_brk_set_meta_alloc_shift c_secret_set_meta_area_head c_init_done_set_meta_area_head c_mmap_counter_set_meta_area_head c_free_meta_head_set_meta_area_head c_avail_meta_set_meta_area_head c_avail_meta_count_set_meta_area_head c_avail_meta_area_count_set_meta_area_head c_meta_alloc_shift_set_meta_area_head c_meta_area_head_set_meta_area_head c_meta_area_tail_set_meta_area_head c_avail_meta_areas_set_meta_area_head c_active_set_meta_area_head c_usage_set_meta_area_head c_unmap_seq_set_meta_area_head c_bounces_set_meta_area_head c_seq_set_meta_area_head c_brk_set_meta_area_head c_secret_set_meta_area_tail c_init_done_set_meta_area_tail c_mmap_counter_set_meta_area_tail c_free_meta_head_set_meta_area_tail c_avail_meta_set_meta_area_tail c_avail_meta_count_set_meta_area_tail c_avail_meta_area_count_set_meta_area_tail c_meta_alloc_shift_set_meta_area_tail c_meta_area_head_set_meta_area_tail c_meta_area_tail_set_meta_area_tail c_avail_meta_areas_set_meta_area_tail c_active_set_meta_area_tail c_usage_set_meta_area_tail c_unmap_seq_set_meta_area_tail c_bounces_set_meta_area_tail c_seq_set_meta_area_tail c_brk_set_meta_area_tail c_secret_set_avail_meta_areas c_init_done_set_avail_meta_areas c_mmap_counter_set_avail_meta_areas c_free_meta_head_set_avail_meta_areas c_avail_meta_set_avail_meta_areas c_avail_meta_count_set_avail_meta_areas c_avail_meta_area_count_set_avail_meta_areas c_meta_alloc_shift_set_avail_meta_areas c_meta_area_head_set_avail_meta_areas c_meta_area_tail_set_avail_meta_areas c_avail_meta_areas_set_avail_meta_areas c_active_set_avail_meta_areas c_usage_set_avail_meta_areas c_unmap_seq_set_avail_meta_areas c_bounces_set_avail_meta_areas c_seq_set_avail_meta_areas c_brk_set_avail_meta_areas c_secret_set_active_map c_init_done_set_active_map c_mmap_counter_set_active_map c_free_meta_head_set_active_map c_avail_meta_set_active_map c_avail_meta_count_set_active_map c_avail_meta_area_count_set_active_map c_meta_alloc_shift_set_active_map c_meta_area_head_set_active_map c_meta_area_tail_set_active_map c_avail_meta_areas_set_active_map c_active_set_active_map c_usage_set_active_map c_unmap_seq_set_active_map c_bounces_set_active_map c_seq_set_active_map c_brk_set_active_map c_secret_set_usage_map c_init_done_set_usage_map c_mmap_counter_set_usage_map c_free_meta_head_set_usage_map c_avail_meta_set_usage_map c_avail_meta_count_set_usage_map c_avail_meta_area_count_set_usage_map c_meta_alloc_shift_set_usage_map c_meta_area_head_set_usage_map c_meta_area_tail_set_usage_map c_avail_meta_areas_set_usage_map c_active_set_usage_map c_usage_set_usage_map c_unmap_seq_set_usage_map c_bounces_set_usage_map c_seq_set_usage_map c_brk_set_usage_map c_secret_set_unmap_seq_map c_init_done_set_unmap_seq_map c_mmap_counter_set_unmap_seq_map c_free_meta_head_set_unmap_seq_map c_avail_meta_set_unmap_seq_map c_avail_meta_count_set_unmap_seq_map c_avail_meta_area_count_set_unmap_seq_map c_meta_alloc_shift_set_unmap_seq_map c_meta_area_head_set_unmap_seq_map c_meta_area_tail_set_unmap_seq_map c_avail_meta_areas_set_unmap_seq_map c_active_set_unmap_seq_map c_usage_set_unmap_seq_map c_unmap_seq_set_unmap_seq_map c_bounces_set_unmap_seq_map c_seq_set_unmap_seq_map c_brk_set_unmap_seq_map c_secret_set_bounces_map c_init_done_set_bounces_map c_mmap_counter_set_bounces_map c_free_meta_head_set_bounces_map c_avail_meta_set_bounces_map c_avail_meta_count_set_bounces_map c_avail_meta_area_count_set_bounces_map c_meta_alloc_shift_set_bounces_map c_meta_area_head_set_bounces_map c_meta_area_tail_set_bounces_map c_avail_meta_areas_set_bounces_map c_active_set_bounces_map c_usage_set_bounces_map c_unmap_seq_set_bounces_map c_bounces_set_bounces_map c_seq_set_bounces_map c_brk_set_bounces_map c_secret_set_seq c_init_done_set_seq c_mmap_counter_set_seq c_free_meta_head_set_seq c_avail_meta_set_seq c_avail_meta_count_set_seq c_avail_meta_area_count_set_seq c_meta_alloc_shift_set_seq c_meta_area_head_set_seq c_meta_area_tail_set_seq c_avail_meta_areas_set_seq c_active_set_seq c_usage_set_seq c_unmap_seq_set_seq c_bounces_set_seq c_seq_set_seq c_brk_set_seq c_secret_set_brk c_init_done_set_brk c_mmap_counter_set_brk c_free_meta_head_set_brk c_avail_meta_set_brk c_avail_meta_count_set_brk c_avail_meta_area_count_set_brk c_meta_alloc_shift_set_brk c_meta_area_head_set_brk c_meta_area_tail_set_brk c_avail_meta_areas_set_brk c_active_set_brk c_usage_set_brk c_unmap_seq_set_brk c_bounces_set_brk c_seq_set_brk c_brk_set_brk : mst.
Lemma s_regions_set_active : ltac2:(zQ "b0!il1!j8!hg9!hgd!t1!q9!ild!lq8!hl8!hr4!hi2>2sc$3>1v$5>2st$4@3$1@4$9$2$a$8$6@1$0@3$7^3^2^1@1$0^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma s_shadow_set_active : ltac2:(zQ "b0!im6!j8!hg9!hgd!t1!q9!lq8!in1!hl8!hr4!hi2>2sc$3>1v$5>2st$4@3$1@4$9$2$a$8$7@1$0@3$6^3^2^1@1$0^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma s_next_rid_set_active : ltac2:(zQ "70!ina!j8!hg9!hgd!t1!q9!lq8>2sc$3>1v$5>2st$4@3$1$2@1$0@3$6^3^2^1@1$0^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma s_metas_set_active : ltac2:(zQ "h00!hgd!hg9!hrc!hi2!hjd!j8!nb!rb!t1!q9!lq8!hl8!hm7!hn6!hp9!hr4>2sc$0>1v$9>2st$8@3$5@4$f$6@4$e$1$3$0$4@6$d$1$3$b$0$4$c$7@1$2@3$a^3^2^1@1$2^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma s_areas_set_active : ltac2:(zQ "h00!hgd!hg9!io7!hi2!hjd!j8!nb!ip1!t1!q9!lq8!hl8!hm7!hn6!hp9!hr4>2sc$0>1v$9>2st$8@3$5@4$f$6@4$e$1$3$0$4@6$d$1$3$b$0$4$c$7@1$2@3$a^3^2^1@1$2^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma s_groups_set_active : ltac2:(zQ "h00!hgd!hg9!ip8!hi2!hjd!j8!nb!iq3!t1!q9!lq8!hl8!hm7!hn6!hp9!hr4>2sc$0>1v$9>2st$8@3$5@4$f$6@4$e$1$3$0$4@6$d$1$3$b$0$4$c$7@1$2@3$a^3^2^1@1$2^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma s_slots_set_active : ltac2:(zQ "h00!hgd!hg9!nb!iqa!hi2!hjd!ir4!j8!t1!q9!lq8!hl8!hm7!hn6!hp9!hr4>2sc$0>1v$9>2st$8@3$7@4$f$2@4$e$1$4$0$5@6$d$1$4$b$0$5$c@2$6$2$0@1$3@3$a^3^2^1@1$3^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma s_tick_set_active : ltac2:(zQ "70!ira!j8!hg9!hgd!t1!q9!lq8>2sc$3>1v$5>2st$4@3$1$2@1$0@3$6^3^2^1@1$0^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma s_secret_set_active : ltac2:(zQ "60!hgd!is3!j8!t1!q9!lq8>2sc$0>1v$4>2st$3@3$2$0@1$1@3$5^3^2^1@1$1^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma s_reserved_set_active : ltac2:(zQ "80!hgd!ise!itb!ir4!j8!t1!q9!lq8>2sc$0>1v$6>2st$5@3$4@1$2@2$3$0$0@1$1@3$7^3^2^1@1$1^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma s_regions_set_usage : ltac2:(zQ "a0!hgd!il1!j8!hg9!t1!ild!lr5!hl8!hr4!hi2>2sc$0>1v$0>2st$4@3$2@4$8$3$9$7$5@1$1@3$6^3^2^1@1$1^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma s_shadow_set_usage : ltac2:(zQ "a0!hgd!im6!j8!hg9!t1!lr5!in1!hl8!hr4!hi2>2sc$0>1v$0>2st$4@3$2@4$8$3$9$7$6@1$1@3$5^3^2^1@1$1^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma s_next_rid_set_usage : ltac2:(zQ "60!hgd!ina!j8!hg9!t1!lr5>2sc$0>1v$0>2st$4@3$2$3@1$1@3$5^3^2^1@1$1^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma s_metas_set_usage : ltac2:(zQ "f0!hgd!hg9!hrc!hi2!hjd!j8!nb!rb!t1!lr5!hl8!hm7!hn6!hp9!hr4>2sc$0>1v$0>2st$8@3$5@4$e$6@4$d$1$3$0$4@6$c$1$3$a$0$4$b$7@1$2@3$9^3^2^1@1$2^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma s_areas_set_usage : ltac2:(zQ "f0!hgd!hg9!io7!hi2!hjd!j8!nb!ip1!t1!lr5!hl8!hm7!hn6!hp9!hr4>2sc$0>1v$0>2st$8@3$5@4$e$6@4$d$1$3$0$4@6$c$1$3$a$0$4$b$7@1$2@3$9^3^2^1@1$2^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma s_groups_set_usage : ltac2:(zQ "f0!hgd!hg9!ip8!hi2!hjd!j8!nb!iq3!t1!lr5!hl8!hm7!hn6!hp9!hr4>2sc$0>1v$0>2st$8@3$5@4$e$6@4$d$1$3$0$4@6$c$1$3$a$0$4$b$7@1$2@3$9^3^2^1@1$2^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma s_slots_set_usage : ltac2:(zQ "f0!hgd!hg9!nb!iqa!hi2!hjd!ir4!j8!t1!lr5!hl8!hm7!hn6!hp9!hr4>2sc$0>1v$0>2st$8@3$7@4$e$2@4$d$1$4$0$5@6$c$1$4$a$0$5$b@2$6$2$0@1$3@3$9^3^2^1@1$3^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma s_tick_set_usage : ltac2:(zQ "60!hgd!ira!j8!hg9!t1!lr5>2sc$0>1v$0>2st$4@3$2$3@1$1@3$5^3^2^1@1$1^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma s_secret_set_usage : ltac2:(zQ "50!hgd!is3!j8!t1!lr5>2sc$0>1v$0>2st$3@3$2$0@1$1@3$4^3^2^1@1$1^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma s_reserved_set_usage : ltac2:(zQ "70!hgd!ise!itb!ir4!j8!t1!lr5>2sc$0>1v$0>2st$5@3$4@1$2@2$3$0$0@1$1@3$6^3^2^1@1$1^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma s_regions_set_bounce : ltac2:(zQ "a0!hgd!il1!j8!hg9!t1!ild!ls1!hl8!hr4!hi2>1i$0>1v$0>2st$4@3$2@4$8$3$9$7$5@1$1@3$6^3^2^1@1$1^1"). Proof. intros i v st. reflexivity. Qed.
Lemma s_shadow_set_bounce : ltac2:(zQ "a0!hgd!im6!j8!hg9!t1!ls1!in1!hl8!hr4!hi2>1i$0>1v$0>2st$4@3$2@4$8$3$9$7$6@1$1@3$5^3^2^1@1$1^1"). Proof. intros i v st. reflexivity. Qed.
Lemma s_next_rid_set_bounce : ltac2:(zQ "60!hgd!ina!j8!hg9!t1!ls1>1i$0>1v$0>2st$4@3$2$3@1$1@3$5^3^2^1@1$1^1"). Proof. intros i v st. reflexivity. Qed.
Lemma s_metas_set_bounce : ltac2:(zQ "f0!hgd!hg9!hrc!hi2!hjd!j8!nb!rb!t1!ls1!hl8!hm7!hn6!hp9!hr4>1i$0>1v$0>2st$8@3$5@4$e$6@4$d$1$3$0$4@6$c$1$3$a$0$4$b$7@1$2@3$9^3^2^1@1$2^1"). Proof. intros i v st. reflexivity. Qed.
Lemma s_areas_set_bounce : ltac2:(zQ "f0!hgd!hg9!io7!hi2!hjd!j8!nb!ip1!t1!ls1!hl8!hm7!hn6!hp9!hr4>1i$0>1v$0>2st$8@3$5@4$e$6@4$d$1$3$0$4@6$c$1$3$a$0$4$b$7@1$2@3$9^3^2^1@1$2^1"). Proof. intros i v st. reflexivity. Qed.
Lemma s_groups_set_bounce : ltac2:(zQ "f0!hgd!hg9!ip8!hi2!hjd!j8!nb!iq3!t1!ls1!hl8!hm7!hn6!hp9!hr4>1i$0>1v$0>2st$8@3$5@4$e$6@4$d$1$3$0$4@6$c$1$3$a$0$4$b$7@1$2@3$9^3^2^1@1$2^1"). Proof. intros i v st. reflexivity. Qed.
Lemma s_slots_set_bounce : ltac2:(zQ "f0!hgd!hg9!nb!iqa!hi2!hjd!ir4!j8!t1!ls1!hl8!hm7!hn6!hp9!hr4>1i$0>1v$0>2st$8@3$7@4$e$2@4$d$1$4$0$5@6$c$1$4$a$0$5$b@2$6$2$0@1$3@3$9^3^2^1@1$3^1"). Proof. intros i v st. reflexivity. Qed.
Lemma s_tick_set_bounce : ltac2:(zQ "60!hgd!ira!j8!hg9!t1!ls1>1i$0>1v$0>2st$4@3$2$3@1$1@3$5^3^2^1@1$1^1"). Proof. intros i v st. reflexivity. Qed.
Lemma s_secret_set_bounce : ltac2:(zQ "50!hgd!is3!j8!t1!ls1>1i$0>1v$0>2st$3@3$2$0@1$1@3$4^3^2^1@1$1^1"). Proof. intros i v st. reflexivity. Qed.
Lemma s_reserved_set_bounce : ltac2:(zQ "70!hgd!ise!itb!ir4!j8!t1!ls1>1i$0>1v$0>2st$5@3$4@1$2@2$3$0$0@1$1@3$6^3^2^1@1$1^1"). Proof. intros i v st. reflexivity. Qed.
Lemma s_ctx_put_meta : ltac2:(zQ "70!ijf!j8!nb!ij8!rb!t1!ta>1m$2>1r$4>2st$5@3$1$3@1$0@3$6^3^2^1@1$0^1"). Proof. intros m r st. reflexivity. Qed.
Lemma s_regions_put_meta : ltac2:(zQ "b0!il1!j8!hg9!nb!rb!t1!ta!ild!hl8!hr4!hi2>1m$3>1r$4>2st$5@3$1@4$9$2$a$8$7@1$0@3$6^3^2^1@1$0^1"). Proof. intros m r st. reflexivity. Qed.
Lemma s_shadow_put_meta : ltac2:(zQ "b0!im6!j8!hg9!nb!rb!t1!ta!in1!hl8!hr4!hi2>1m$3>1r$4>2st$5@3$1@4$9$2$a$8$7@1$0@3$6^3^2^1@1$0^1"). Proof. intros m r st. reflexivity. Qed.
Lemma s_next_rid_put_meta : ltac2:(zQ "70!ina!j8!hg9!nb!rb!t1!ta>1m$3>1r$4>2st$5@3$1$2@1$0@3$6^3^2^1@1$0^1"). Proof. intros m r st. reflexivity. Qed.
Lemma s_areas_put_meta : ltac2:(zQ "h00!hg9!hgd!nb!io7!hi2!hjd!j8!ip1!rb!t1!ta!hl8!hm7!hn6!hp9!hr4>1m$2>1r$8>2st$9@3$6@4$f$2@4$e$0$4$1$5@6$d$0$4$b$1$5$c$7@1$3@3$a^3^2^1@1$3^1"). Proof. intros m r st. reflexivity. Qed.
Lemma s_groups_put_meta : ltac2:(zQ "h00!hg9!hgd!nb!ip8!hi2!hjd!j8!iq3!rb!t1!ta!hl8!hm7!hn6!hp9!hr4>1m$2>1r$8>2st$9@3$6@4$f$2@4$e$0$4$1$5@6$d$0$4$b$1$5$c$7@1$3@3$a^3^2^1@1$3^1"). Proof. intros m r st. reflexivity. Qed.
Lemma s_slots_put_meta : ltac2:(zQ "h00!hgd!nb!hg9!iqa!hi2!hjd!ir4!j8!rb!t1!ta!hl8!hm7!hn6!hp9!hr4>1m$1>1r$8>2st$9@3$7@4$f$1@4$e$2$4$0$5@6$d$2$4$b$0$5$c@2$6$1$0@1$3@3$a^3^2^1@1$3^1"). Proof. intros m r st. reflexivity. Qed.
Lemma s_tick_put_meta : ltac2:(zQ "70!ira!j8!hg9!nb!rb!t1!ta>1m$3>1r$4>2st$5@3$1$2@1$0@3$6^3^2^1@1$0^1"). Proof. intros m r st. reflexivity. Qed.
Lemma s_secret_put_meta : ltac2:(zQ "70!is3!j8!hgd!nb!rb!t1!ta>1m$3>1r$4>2st$5@3$1$2@1$0@3$6^3^2^1@1$0^1"). Proof. intros m r st. reflexivity. Qed.
Lemma s_reserved_put_meta : ltac2:(zQ "90!hgd!ise!itb!ir4!j8!nb!rb!t1!ta>1m$5>1r$6>2st$7@3$4@1$2@2$3$0$0@1$1@3$8^3^2^1@1$1^1"). Proof. intros m r st. reflexivity. Qed.
Lemma s_ctx_upd_meta : ltac2:(zQ "70!rb!ijf!j8!nb!ij8!t1!u5>1m$3>1f>0$0$0>2st$5@3$2$4@1$1@3$6^3^2^1@1$1^1"). Proof. intros m f st. reflexivity. Qed.
Lemma s_regions_upd_meta : ltac2:(zQ "b0!rb!il1!j8!hg9!nb!t1!ild!u5!hl8!hr4!hi2>1m$4>1f>0$0$0>2st$5@3$2@4$9$3$a$8$6@1$1@3$7^3^2^1@1$1^1"). Proof. intros m f st. reflexivity. Qed.
Lemma s_shadow_upd_meta : ltac2:(zQ "b0!rb!im6!j8!hg9!nb!t1!in1!u5!hl8!hr4!hi2>1m$4>1f>0$0$0>2st$5@3$2@4$9$3$a$8$6@1$1@3$7^3^2^1@1$1^1"). Proof. intros m f st. reflexivity. Qed.
Lemma s_next_rid_upd_meta : ltac2:(zQ "70!rb!ina!j8!hg9!nb!t1!u5>1m$4>1f>0$0$0>2st$5@3$2$3@1$1@3$6^3^2^1@1$1^1"). Proof. intros m f st. reflexivity. Qed.
Lemma s_areas_upd_meta : ltac2:(zQ "h00!hg9!hgd!nb!rb!io7!hi2!hjd!j8!ip1!t1!u5!hl8!hm7!hn6!hp9!hr4>1m$2>1f>0$3$3>2st$9@3$7@4$f$2@4$e$0$5$1$6@6$d$0$5$b$1$6$c$8@1$4@3$a^3^2^1@1$4^1"). Proof. intros m f st. reflexivity. Qed.
Lemma s_groups_upd_meta : ltac2:(zQ "h00!hg9!hgd!nb!rb!ip8!hi2!hjd!j8!iq3!t1!u5!hl8!hm7!hn6!hp9!hr4>1m$2>1f>0$3$3>2st$9@3$7@4$f$2@4$e$0$5$1$6@6$d$0$5$b$1$6$c$8@1$4@3$a^3^2^1@1$4^1"). Proof. intros m f st. reflexivity. Qed.
Lemma s_slots_upd_meta : ltac2:(zQ "h00!hgd!nb!hg9!rb!iqa!hi2!hjd!ir4!j8!t1!u5!hl8!hm7!hn6!hp9!hr4>1m$1>1f>0$3$3>2st$9@3$8@4$f$1@4$e$2$5$0$6@6$d$2$5$b$0$6$c@2$7$1$0@1$4@3$a^3^2^1@1$4^1"). Proof. intros m f st. reflexivity. Qed.
Lemma s_tick_upd_meta : ltac2:(zQ "70!rb!ira!j8!hg9!nb!t1!u5>1m$4>1f>0$0$0>2st$5@3$2$3@1$1@3$6^3^2^1@1$1^1"). Proof. intros m f st. reflexivity. Qed.
Lemma s_secret_upd_meta : ltac2:(zQ "70!rb!is3!j8!hgd!nb!t1!u5>1m$4>1f>0$0$0>2st$5@3$2$3@1$1@3$6^3^2^1@1$1^1"). Proof. intros m f st. reflexivity. Qed.
Lemma s_reserved_upd_meta : ltac2:(zQ "90!hgd!rb!ise!itb!ir4!j8!nb!t1!u5>1m$6>1f>0$1$1>2st$7@3$5@1$3@2$4$0$0@1$2@3$8^3^2^1@1$2^1"). Proof. intros m f st. reflexivity. Qed.
Lemma s_ctx_put_group : ltac2:(zQ "80!ijf!j8!hgd!nb!ij8!t1!q9!lse>1g$3>2mo$6>2ai$2>2st$5@3$1$4@1$0@4$7^4^3^2^1@1$0^1"). Proof. intros g mo ai st. reflexivity. Qed.
Lemma s_regions_put_group : ltac2:(zQ "c0!il1!j8!hg9!hgd!nb!t1!q9!lse!ild!hl8!hr4!hi2>1g$4>2mo$6>2ai$3>2st$5@3$1@4$a$2$b$9$8@1$0@4$7^4^3^2^1@1$0^1"). Proof. intros g mo ai st. reflexivity. Qed.
Lemma s_shadow_put_group : ltac2:(zQ "c0!im6!j8!hg9!hgd!nb!t1!q9!lse!in1!hl8!hr4!hi2>1g$4>2mo$6>2ai$3>2st$5@3$1@4$a$2$b$9$8@1$0@4$7^4^3^2^1@1$0^1"). Proof. intros g mo ai st. reflexivity. Qed.
Lemma s_next_rid_put_group : ltac2:(zQ "80!ina!j8!hg9!hgd!nb!t1!q9!lse>1g$4>2mo$6>2ai$3>2st$5@3$1$2@1$0@4$7^4^3^2^1@1$0^1"). Proof. intros g mo ai st. reflexivity. Qed.
Lemma s_metas_put_group : ltac2:(zQ "h00!hgd!hg9!nb!hrc!hi2!hjd!j8!rb!t1!q9!lse!hl8!hm7!hn6!hp9!hr4>1g$2>2mo$9>2ai$0>2st$8@3$6@4$f$2@4$e$1$4$0$5@6$d$1$4$b$0$5$c$7@1$3@4$a^4^3^2^1@1$3^1"). Proof. intros g mo ai st. reflexivity. Qed.
Lemma s_areas_put_group : ltac2:(zQ "h00!hgd!hg9!nb!io7!hi2!hjd!j8!ip1!t1!q9!lse!hl8!hm7!hn6!hp9!hr4>1g$2>2mo$9>2ai$0>2st$8@3$6@4$f$2@4$e$1$4$0$5@6$d$1$4$b$0$5$c$7@1$3@4$a^4^3^2^1@1$3^1"). Proof. intros g mo ai st. reflexivity. Qed.
Lemma s_slots_put_group : ltac2:(zQ "h00!hgd!nb!hg9!iqa!hi2!hjd!ir4!j8!t1!q9!lse!hl8!hm7!hn6!hp9!hr4>1g$1>2mo$9>2ai$0>2st$8@3$7@4$f$1@4$e$2$4$0$5@6$d$2$4$b$0$5$c@2$6$1$0@1$3@4$a^4^3^2^1@1$3^1"). Proof. intros g mo ai st. reflexivity. Qed.
Lemma s_tick_put_group : ltac2:(zQ "80!ira!j8!hg9!hgd!nb!t1!q9!lse>1g$4>2mo$6>2ai$3>2st$5@3$1$2@1$0@4$7^4^3^2^1@1$0^1"). Proof. intros g mo ai st. reflexivity. Qed.
Lemma s_secret_put_group : ltac2:(zQ "70!hgd!is3!j8!nb!t1!q9!lse>1g$3>2mo$5>2ai$0>2st$4@3$2$0@1$1@4$6^4^3^2^1@1$1^1"). Proof. intros g mo ai st. reflexivity. Qed.
Lemma s_reserved_put_group : ltac2:(zQ "90!hgd!ise!itb!ir4!j8!nb!t1!q9!lse>1g$5>2mo$7>2ai$0>2st$6@3$4@1$2@2$3$0$0@1$1@4$8^4^3^2^1@1$1^1"). Proof. intros g mo ai st. reflexivity. Qed.
Lemma s_ctx_del_group : ltac2:(zQ "60!ijf!j8!nb!lta!ij8!t1>1g$2>2st$5@3$1$4@1$0@2$3^2^1@1$0^1"). Proof. intros g st. reflexivity. Qed.
Lemma s_regions_del_group : ltac2:(zQ "a0!il1!j8!hg9!nb!lta!t1!ild!hl8!hr4!hi2>1g$3>2st$5@3$1@4$8$2$9$7$6@1$0@2$4^2^1@1$0^1"). Proof. intros g st. reflexivity. Qed.
Lemma s_shadow_del_group : ltac2:(zQ "a0!im6!j8!hg9!nb!lta!t1!in1!hl8!hr4!hi2>1g$3>2st$5@3$1@4$8$2$9$7$6@1$0@2$4^2^1@1$0^1"). Proof. intros g st. reflexivity. Qed.
Lemma s_next_rid_del_group : ltac2:(zQ "60!ina!j8!hg9!nb!lta!t1>1g$3>2st$5@3$1$2@1$0@2$4^2^1@1$0^1"). Proof. intros g st. reflexivity. Qed.
Lemma s_metas_del_group : ltac2:(zQ "f0!hg9!hgd!nb!hrc!hi2!hjd!j8!lta!rb!t1!hl8!hm7!hn6!hp9!hr4>1g$2>2st$9@3$6@4$e$2@4$d$0$4$1$5@6$c$0$4$a$1$5$b$8@1$3@2$7^2^1@1$3^1"). Proof. intros g st. reflexivity. Qed.
Lemma s_areas_del_group : ltac2:(zQ "f0!hg9!hgd!nb!io7!hi2!hjd!j8!ip1!lta!t1!hl8!hm7!hn6!hp9!hr4>1g$2>2st$9@3$6@4$e$2@4$d$0$4$1$5@6$c$0$4$a$1$5$b$7@1$3@2$8^2^1@1$3^1"). Proof. intros g st. reflexivity. Qed.
Lemma s_slots_del_group : ltac2:(zQ "f0!hgd!nb!hg9!iqa!hi2!hjd!ir4!j8!lta!t1!hl8!hm7!hn6!hp9!hr4>1g$1>2st$9@3$7@4$e$1@4$d$2$4$0$5@6$c$2$4$a$0$5$b@2$6$1$0@1$3@2$8^2^1@1$3^1"). Proof. intros g st. reflexivity. Qed.
Lemma s_tick_del_group : ltac2:(zQ "60!ira!j8!hg9!nb!lta!t1>1g$3>2st$5@3$1$2@1$0@2$4^2^1@1$0^1"). Proof. intros g st. reflexivity. Qed.
Lemma s_secret_del_group : ltac2:(zQ "60!is3!j8!hgd!nb!lta!t1>1g$3>2st$5@3$1$2@1$0@2$4^2^1@1$0^1"). Proof. intros g st. reflexivity. Qed.
Lemma s_reserved_del_group : ltac2:(zQ "80!hgd!ise!itb!ir4!j8!nb!lta!t1>1g$5>2st$7@3$4@1$2@2$3$0$0@1$1@2$6^2^1@1$1^1"). Proof. intros g st. reflexivity. Qed.
Lemma s_ctx_set_group_active_idx : ltac2:(zQ "70!ijf!j8!hgd!nb!ij8!t1!lu6>1g$3>2ai$2>2st$5@3$1$4@1$0@3$6^3^2^1@1$0^1"). Proof. intros g ai st. unfold set_group_active_idx; destruct (get_group st g); reflexivity. Qed.
Lemma s_regions_set_group_active_idx : ltac2:(zQ "b0!il1!j8!hg9!hgd!nb!t1!ild!lu6!hl8!hr4!hi2>1g$4>2ai$3>2st$5@3$1@4$9$2$a$8$6@1$0@3$7^3^2^1@1$0^1"). Proof. intros g ai st. unfold set_group_active_idx; destruct (get_group st g); reflexivity. Qed.
Lemma s_shadow_set_group_active_idx : ltac2:(zQ "b0!im6!j8!hg9!hgd!nb!t1!lu6!in1!hl8!hr4!hi2>1g$4>2ai$3>2st$5@3$1@4$9$2$a$8$7@1$0@3$6^3^2^1@1$0^1"). Proof. intros g ai st. unfold set_group_active_idx; destruct (get_group st g); reflexivity. Qed.
Lemma s_next_rid_set_group_active_idx : ltac2:(zQ "70!ina!j8!hg9!hgd!nb!t1!lu6>1g$4>2ai$3>2st$5@3$1$2@1$0@3$6^3^2^1@1$0^1"). Proof. intros g ai st. unfold set_group_active_idx; destruct (get_group st g); reflexivity. Qed.
Lemma s_metas_set_group_active_idx : ltac2:(zQ "f0!hgd!hg9!nb!hrc!hi2!hjd!j8!rb!t1!lu6!hl8!hm7!hn6!hp9!hr4>1g$2>2ai$0>2st$8@3$6@4$e$2@4$d$1$4$0$5@6$c$1$4$a$0$5$b$7@1$3@3$9^3^2^1@1$3^1"). Proof. intros g ai st. unfold set_group_active_idx; destruct (get_group st g); reflexivity. Qed.
Lemma s_areas_set_group_active_idx : ltac2:(zQ "f0!hgd!hg9!nb!io7!hi2!hjd!j8!ip1!t1!lu6!hl8!hm7!hn6!hp9!hr4>1g$2>2ai$0>2st$8@3$6@4$e$2@4$d$1$4$0$5@6$c$1$4$a$0$5$b$7@1$3@3$9^3^2^1@1$3^1"). Proof. intros g ai st. unfold set_group_active_idx; destruct (get_group st g); reflexivity. Qed.
Lemma s_slots_set_group_active_idx : ltac2:(zQ "f0!hgd!nb!hg9!iqa!hi2!hjd!ir4!j8!t1!lu6!hl8!hm7!hn6!hp9!hr4>1g$1>2ai$0>2st$8@3$7@4$e$1@4$d$2$4$0$5@6$c$2$4$a$0$5$b@2$6$1$0@1$3@3$9^3^2^1@1$3^1"). Proof. intros g ai st. unfold set_group_active_idx; destruct (get_group st g); reflexivity. Qed.
Lemma s_tick_set_group_active_idx : ltac2:(zQ "70!ira!j8!hg9!hgd!nb!t1!lu6>1g$4>2ai$3>2st$5@3$1$2@1$0@3$6^3^2^1@1$0^1"). Proof. intros g ai st. unfold set_group_active_idx; destruct (get_group st g); reflexivity. Qed.
Lemma s_secret_set_group_active_idx : ltac2:(zQ "60!hgd!is3!j8!nb!t1!lu6>1g$3>2ai$0>2st$4@3$2$0@1$1@3$5^3^2^1@1$1^1"). Proof. intros g ai st. unfold set_group_active_idx; destruct (get_group st g); reflexivity. Qed.
Lemma s_reserved_set_group_active_idx : ltac2:(zQ "80!hgd!ise!itb!ir4!j8!nb!t1!lu6>1g$5>2ai$0>2st$6@3$4@1$2@2$3$0$0@1$1@3$7^3^2^1@1$1^1"). Proof. intros g ai st. unfold set_group_active_idx; destruct (get_group st g); reflexivity. Qed.
Lemma s_ctx_drop_region : ltac2:(zQ "60!ijf!j8!hg9!lve!ij8!t1>3rid$2>2st$5@3$1$4@1$0@2$3^2^1@1$0^1"). Proof. intros rid st. reflexivity. Qed.
Lemma s_next_rid_drop_region : ltac2:(zQ "50!hg9!ina!j8!lve!t1>3rid$0>2st$4@3$2$0@1$1@2$3^2^1@1$1^1"). Proof. intros rid st. reflexivity. Qed.
Lemma s_metas_drop_region : ltac2:(zQ "f0!hg9!hgd!hrc!hi2!hjd!j8!nb!lve!rb!t1!hl8!hm7!hn6!hp9!hr4>3rid$0>2st$9@3$5@4$e$6@4$d$0$3$1$4@6$c$0$3$a$1$4$b$8@1$2@2$7^2^1@1$2^1"). Proof. intros rid st. reflexivity. Qed.
Lemma s_areas_drop_region : ltac2:(zQ "f0!hg9!hgd!io7!hi2!hjd!j8!nb!ip1!lve!t1!hl8!hm7!hn6!hp9!hr4>3rid$0>2st$9@3$5@4$e$6@4$d$0$3$1$4@6$c$0$3$a$1$4$b$7@1$2@2$8^2^1@1$2^1"). Proof. intros rid st. reflexivity. Qed.
Lemma s_groups_drop_region : ltac2:(zQ "f0!hg9!hgd!ip8!hi2!hjd!j8!nb!lve!iq3!t1!hl8!hm7!hn6!hp9!hr4>3rid$0>2st$9@3$5@4$e$6@4$d$0$3$1$4@6$c$0$3$a$1$4$b$8@1$2@2$7^2^1@1$2^1"). Proof. intros rid st. reflexivity. Qed.
Lemma s_slots_drop_region : ltac2:(zQ "f0!hg9!hgd!nb!iqa!hi2!hjd!ir4!j8!lve!t1!hl8!hm7!hn6!hp9!hr4>3rid$0>2st$9@3$7@4$e$2@4$d$0$4$1$5@6$c$0$4$a$1$5$b@2$6$2$1@1$3@2$8^2^1@1$3^1"). Proof. intros rid st. reflexivity. Qed.
Lemma s_tick_drop_region : ltac2:(zQ "50!hg9!ira!j8!lve!t1>3rid$0>2st$4@3$2$0@1$1@2$3^2^1@1$1^1"). Proof. intros rid st. reflexivity. Qed.
Lemma s_secret_drop_region : ltac2:(zQ "60!is3!j8!hg9!hgd!lve!t1>3rid$2>2st$5@3$1$3@1$0@2$4^2^1@1$0^1"). Proof. intros rid st. reflexivity. Qed.
Lemma s_reserved_drop_region : ltac2:(zQ "80!hgd!ise!itb!ir4!j8!hg9!lve!t1>3rid$5>2st$7@3$4@1$2@2$3$0$0@1$1@2$6^2^1@1$1^1"). Proof. intros rid st. reflexivity. Qed.
Lemma s_ctx_upd_region : ltac2:(zQ "70!ild!ijf!j8!hg9!ij8!t1!mgc>3rid$3>1f>0$0$0>2st$5@3$2$4@1$1@3$6^3^2^1@1$1^1"). Proof. intros rid f st. unfold upd_region; destruct (get_region st rid); reflexivity. Qed.
Lemma s_shadow_upd_region : ltac2:(zQ "a0!hg9!ild!im6!j8!t1!in1!mgc!hl8!hr4!hi2>3rid$0>1f>0$1$1>2st$4@3$3@4$8$0$9$7$5@1$2@3$6^3^2^1@1$2^1"). Proof. intros rid f st. unfold upd_region; destruct (get_region st rid); reflexivity. Qed.
Lemma s_next_rid_upd_region : ltac2:(zQ "60!hg9!ild!ina!j8!t1!mgc>3rid$0>1f>0$1$1>2st$4@3$3$0@1$2@3$5^3^2^1@1$2^1"). Proof. intros rid f st. unfold upd_region; destruct (get_region st rid); reflexivity. Qed.
Lemma s_metas_upd_region : ltac2:(zQ "h00!hg9!hgd!ild!hrc!hi2!hjd!j8!nb!rb!t1!mgc!hl8!hm7!hn6!hp9!hr4>3rid$0>1f>0$2$2>2st$9@3$6@4$f$7@4$e$0$4$1$5@6$d$0$4$b$1$5$c$8@1$3@3$a^3^2^1@1$3^1"). Proof. intros rid f st. unfold upd_region; destruct (get_region st rid); reflexivity. Qed.
Lemma s_areas_upd_region : ltac2:(zQ "h00!hg9!hgd!ild!io7!hi2!hjd!j8!nb!ip1!t1!mgc!hl8!hm7!hn6!hp9!hr4>3rid$0>1f>0$2$2>2st$9@3$6@4$f$7@4$e$0$4$1$5@6$d$0$4$b$1$5$c$8@1$3@3$a^3^2^1@1$3^1"). Proof. intros rid f st. unfold upd_region; destruct (get_region st rid); reflexivity. Qed.
Lemma s_groups_upd_region : ltac2:(zQ "h00!hg9!hgd!ild!ip8!hi2!hjd!j8!nb!iq3!t1!mgc!hl8!hm7!hn6!hp9!hr4>3rid$0>1f>0$2$2>2st$9@3$6@4$f$7@4$e$0$4$1$5@6$d$0$4$b$1$5$c$8@1$3@3$a^3^2^1@1$3^1"). Proof. intros rid f st. unfold upd_region; destruct (get_region st rid); reflexivity. Qed.
Lemma s_slots_upd_region : ltac2:(zQ "h00!hg9!hgd!nb!ild!iqa!hi2!hjd!ir4!j8!t1!mgc!hl8!hm7!hn6!hp9!hr4>3rid$0>1f>0$3$3>2st$9@3$8@4$f$2@4$e$0$5$1$6@6$d$0$5$b$1$6$c@2$7$2$1@1$4@3$a^3^2^1@1$4^1"). Proof. intros rid f st. unfold upd_region; destruct (get_region st rid); reflexivity. Qed.
Lemma s_tick_upd_region : ltac2:(zQ "60!hg9!ild!ira!j8!t1!mgc>3rid$0>1f>0$1$1>2st$4@3$3$0@1$2@3$5^3^2^1@1$2^1"). Proof. intros rid f st. unfold upd_region; destruct (get_region st rid); reflexivity. Qed.
Lemma s_secret_upd_region : ltac2:(zQ "70!ild!is3!j8!hg9!hgd!t1!mgc>3rid$3>1f>0$0$0>2st$5@3$2$4@1$1@3$6^3^2^1@1$1^1"). Proof. intros rid f st. unfold upd_region; destruct (get_region st rid); reflexivity. Qed.
Lemma s_reserved_upd_region : ltac2:(zQ "90!hgd!ild!ise!itb!ir4!j8!hg9!t1!mgc>3rid$6>1f>0$1$1>2st$7@3$5@1$3@2$4$0$0@1$2@3$8^3^2^1@1$2^1"). Proof. intros rid f st. unfold upd_region; destruct (get_region st rid); reflexivity. Qed.
Lemma s_ctx_add_slots : ltac2:(zQ "70!hgd!nb!ijf!j8!mh9!ij8!t1>1m$1>1p$1>6stride$0>3cnt$0>2st$6@3$3$5@1$2@5$4^5^4^3^2^1@1$2^1"). Proof. intros m p stride cnt st. reflexivity. Qed.
Lemma s_regions_add_slots : ltac2:(zQ "b0!hgd!nb!il1!j8!hg9!mh9!t1!ild!hl8!hr4!hi2>1m$1>1p$1>6stride$0>3cnt$0>2st$6@3$3@4$9$4$a$8$7@1$2@5$5^5^4^3^2^1@1$2^1"). Proof. intros m p stride cnt st. reflexivity. Qed.
Lemma s_shadow_add_slots : ltac2:(zQ "b0!hgd!nb!im6!j8!hg9!mh9!t1!in1!hl8!hr4!hi2>1m$1>1p$1>6stride$0>3cnt$0>2st$6@3$3@4$9$4$a$8$7@1$2@5$5^5^4^3^2^1@1$2^1"). Proof. intros m p stride cnt st. reflexivity. Qed.
Lemma s_next_rid_add_slots : ltac2:(zQ "70!hgd!nb!ina!j8!hg9!mh9!t1>1m$1>1p$1>6stride$0>3cnt$0>2st$6@3$3$4@1$2@5$5^5^4^3^2^1@1$2^1"). Proof. intros m p stride cnt st. reflexivity. Qed.
Lemma s_metas_add_slots : ltac2:(zQ "f0!hgd!nb!hg9!hrc!hi2!hjd!j8!mh9!rb!t1!hl8!hm7!hn6!hp9!hr4>1m$1>1p$1>6stride$0>3cnt$0>2st$9@3$6@4$e$1@4$d$2$4$0$5@6$c$2$4$a$0$5$b$8@1$3@5$7^5^4^3^2^1@1$3^1"). Proof. intros m p stride cnt st. reflexivity. Qed.
Lemma s_areas_add_slots : ltac2:(zQ "f0!hgd!nb!hg9!io7!hi2!hjd!j8!mh9!ip1!t1!hl8!hm7!hn6!hp9!hr4>1m$1>1p$1>6stride$0>3cnt$0>2st$9@3$6@4$e$1@4$d$2$4$0$5@6$c$2$4$a$0$5$b$8@1$3@5$7^5^4^3^2^1@1$3^1"). Proof. intros m p stride cnt st. reflexivity. Qed.
Lemma s_groups_add_slots : ltac2:(zQ "f0!hgd!nb!hg9!ip8!hi2!hjd!j8!mh9!iq3!t1!hl8!hm7!hn6!hp9!hr4>1m$1>1p$1>6stride$0>3cnt$0>2st$9@3$6@4$e$1@4$d$2$4$0$5@6$c$2$4$a$0$5$b$8@1$3@5$7^5^4^3^2^1@1$3^1"). Proof. intros m p stride cnt st. reflexivity. Qed.
Lemma s_tick_add_slots : ltac2:(zQ "70!hgd!nb!ira!j8!hg9!mh9!t1>1m$1>1p$1>6stride$0>3cnt$0>2st$6@3$3$4@1$2@5$5^5^4^3^2^1@1$2^1"). Proof. intros m p stride cnt st. reflexivity. Qed.
Lemma s_secret_add_slots : ltac2:(zQ "60!hgd!nb!is3!j8!mh9!t1>1m$1>1p$1>6stride$0>3cnt$0>2st$5@3$3$0@1$2@5$4^5^4^3^2^1@1$2^1"). Proof. intros m p stride cnt st. reflexivity. Qed.
Lemma s_reserved_add_slots : ltac2:(zQ "80!hgd!nb!ise!itb!ir4!j8!mh9!t1>1m$1>1p$1>6stride$0>3cnt$0>2st$7@3$5@1$3@2$4$0$0@1$2@5$6^5^4^3^2^1@1$2^1"). Proof. intros m p stride cnt st. reflexivity. Qed.
Lemma s_ctx_del_slots : ltac2:(zQ "70!hgd!ijf!j8!nb!mi5!ij8!t1>1p$3>6stride$0>3cnt$0>2st$6@3$2$5@1$1@4$4^4^3^2^1@1$1^1"). Proof. intros p stride cnt st. reflexivity. Qed.
Lemma s_regions_del_slots : ltac2:(zQ "b0!hgd!il1!j8!hg9!nb!mi5!t1!ild!hl8!hr4!hi2>1p$4>6stride$0>3cnt$0>2st$6@3$2@4$9$3$a$8$7@1$1@4$5^4^3^2^1@1$1^1"). Proof. intros p stride cnt st. reflexivity. Qed.
Lemma s_shadow_del_slots : ltac2:(zQ "b0!hgd!im6!j8!hg9!nb!mi5!t1!in1!hl8!hr4!hi2>1p$4>6stride$0>3cnt$0>2st$6@3$2@4$9$3$a$8$7@1$1@4$5^4^3^2^1@1$1^1"). Proof. intros p stride cnt st. reflexivity. Qed.
Lemma s_next_rid_del_slots : ltac2:(zQ "70!hgd!ina!j8!hg9!nb!mi5!t1>1p$4>6stride$0>3cnt$0>2st$6@3$2$3@1$1@4$5^4^3^2^1@1$1^1"). Proof. intros p stride cnt st. reflexivity. Qed.
Lemma s_metas_del_slots : ltac2:(zQ "f0!hgd!hg9!nb!hrc!hi2!hjd!j8!mi5!rb!t1!hl8!hm7!hn6!hp9!hr4>1p$2>6stride$0>3cnt$0>2st$9@3$6@4$e$2@4$d$1$4$0$5@6$c$1$4$a$0$5$b$8@1$3@4$7^4^3^2^1@1$3^1"). Proof. intros p stride cnt st. reflexivity. Qed.
Lemma s_areas_del_slots : ltac2:(zQ "f0!hgd!hg9!nb!io7!hi2!hjd!j8!ip1!mi5!t1!hl8!hm7!hn6!hp9!hr4>1p$2>6stride$0>3cnt$0>2st$9@3$6@4$e$2@4$d$1$4$0$5@6$c$1$4$a$0$5$b$7@1$3@4$8^4^3^2^1@1$3^1"). Proof. intros p stride cnt st. reflexivity. Qed.
Lemma s_groups_del_slots : ltac2:(zQ "f0!hgd!hg9!nb!ip8!hi2!hjd!j8!mi5!iq3!t1!hl8!hm7!hn6!hp9!hr4>1p$2>6stride$0>3cnt$0>2st$9@3$6@4$e$2@4$d$1$4$0$5@6$c$1$4$a$0$5$b$8@1$3@4$7^4^3^2^1@1$3^1"). Proof. intros p stride cnt st. reflexivity. Qed.
Lemma s_tick_del_slots : ltac2:(zQ "70!hgd!ira!j8!hg9!nb!mi5!t1>1p$4>6stride$0>3cnt$0>2st$6@3$2$3@1$1@4$5^4^3^2^1@1$1^1"). Proof. intros p stride cnt st. reflexivity. Qed.
Lemma s_secret_del_slots : ltac2:(zQ "60!hgd!is3!j8!nb!mi5!t1>1p$3>6stride$0>3cnt$0>2st$5@3$2$0@1$1@4$4^4^3^2^1@1$1^1"). Proof. intros p stride cnt st. reflexivity. Qed.
Lemma s_reserved_del_slots : ltac2:(zQ "80!hgd!ise!itb!ir4!j8!nb!mi5!t1>1p$5>6stride$0>3cnt$0>2st$7@3$4@1$2@2$3$0$0@1$1@4$6^4^3^2^1@1$1^1"). Proof. intros p stride cnt st. reflexivity. Qed.
Lemma s_ctx_upd_shadow : ltac2:(zQ "70!ijf!in1!j8!hg9!ij8!t1!mj1>3rid$3>1f>0$1$1>2st$5@3$2$4@1$0@3$6^3^2^1@1$0^1"). Proof. intros rid f st. reflexivity. Qed.
Lemma s_regions_upd_shadow : ltac2:(zQ "a0!hg9!il1!in1!j8!t1!ild!mj1!hl8!hr4!hi2>3rid$0>1f>0$2$2>2st$4@3$3@4$8$0$9$7$5@1$1@3$6^3^2^1@1$1^1"). Proof. intros rid f st. reflexivity. Qed.
Lemma s_next_rid_upd_shadow : ltac2:(zQ "60!hg9!ina!in1!j8!t1!mj1>3rid$0>1f>0$2$2>2st$4@3$3$0@1$1@3$5^3^2^1@1$1^1"). Proof. intros rid f st. reflexivity. Qed.
Lemma s_metas_upd_shadow : ltac2:(zQ "h00!hg9!hgd!hrc!in1!hi2!hjd!j8!nb!rb!t1!mj1!hl8!hm7!hn6!hp9!hr4>3rid$0>1f>0$3$3>2st$9@3$6@4$f$7@4$e$0$4$1$5@6$d$0$4$b$1$5$c$8@1$2@3$a^3^2^1@1$2^1"). Proof. intros rid f st. reflexivity. Qed.
Lemma s_areas_upd_shadow : ltac2:(zQ "h00!hg9!hgd!io7!in1!hi2!hjd!j8!nb!ip1!t1!mj1!hl8!hm7!hn6!hp9!hr4>3rid$0>1f>0$3$3>2st$9@3$6@4$f$7@4$e$0$4$1$5@6$d$0$4$b$1$5$c$8@1$2@3$a^3^2^1@1$2^1"). Proof. intros rid f st. reflexivity. Qed.
Lemma s_groups_upd_shadow : ltac2:(zQ "h00!hg9!hgd!ip8!in1!hi2!hjd!j8!nb!iq3!t1!mj1!hl8!hm7!hn6!hp9!hr4>3rid$0>1f>0$3$3>2st$9@3$6@4$f$7@4$e$0$4$1$5@6$d$0$4$b$1$5$c$8@1$2@3$a^3^2^1@1$2^1"). Proof. intros rid f st. reflexivity. Qed.
Lemma s_slots_upd_shadow : ltac2:(zQ "h00!hg9!hgd!nb!iqa!in1!hi2!hjd!ir4!j8!t1!mj1!hl8!hm7!hn6!hp9!hr4>3rid$0>1f>0$4$4>2st$9@3$8@4$f$2@4$e$0$5$1$6@6$d$0$5$b$1$6$c@2$7$2$1@1$3@3$a^3^2^1@1$3^1"). Proof. intros rid f st. reflexivity. Qed.
Lemma s_tick_upd_shadow : ltac2:(zQ "60!hg9!ira!in1!j8!t1!mj1>3rid$0>1f>0$2$2>2st$4@3$3$0@1$1@3$5^3^2^1@1$1^1"). Proof. intros rid f st. reflexivity. Qed.
Lemma s_secret_upd_shadow : ltac2:(zQ "70!is3!in1!j8!hg9!hgd!t1!mj1>3rid$3>1f>0$1$1>2st$5@3$2$4@1$0@3$6^3^2^1@1$0^1"). Proof. intros rid f st. reflexivity. Qed.
Lemma s_reserved_upd_shadow : ltac2:(zQ "90!hgd!ise!in1!itb!ir4!j8!hg9!t1!mj1>3rid$6>1f>0$2$2>2st$7@3$5@1$3@2$4$0$0@1$1@3$8^3^2^1@1$1^1"). Proof. intros rid f st. reflexivity. Qed.
Lemma s_ctx_wr8 : ltac2:(zQ "70!ijf!j8!hgd!nb!ij8!t1!mje>1p$3>1v$2>2st$5@3$1$4@1$0@3$6^3^2^1@1$0^1"). Proof. intros p v st. reflexivity. Qed.
Lemma s_regions_wr8 : ltac2:(zQ "b0!il1!j8!hg9!hgd!nb!t1!ild!mje!hl8!hr4!hi2>1p$4>1v$3>2st$5@3$1@4$9$2$a$8$6@1$0@3$7^3^2^1@1$0^1"). Proof. intros p v st. reflexivity. Qed.
Lemma s_next_rid_wr8 : ltac2:(zQ "70!ina!j8!hg9!hgd!nb!t1!mje>1p$4>1v$3>2st$5@3$1$2@1$0@3$6^3^2^1@1$0^1"). Proof. intros p v st. reflexivity. Qed.
Lemma s_metas_wr8 : ltac2:(zQ "f0!hgd!hg9!nb!hrc!hi2!hjd!j8!rb!t1!mje!hl8!hm7!hn6!hp9!hr4>1p$2>1v$0>2st$8@3$6@4$e$2@4$d$1$4$0$5@6$c$1$4$a$0$5$b$7@1$3@3$9^3^2^1@1$3^1"). Proof. intros p v st. reflexivity. Qed.
Lemma s_areas_wr8 : ltac2:(zQ "f0!hgd!hg9!nb!io7!hi2!hjd!j8!ip1!t1!mje!hl8!hm7!hn6!hp9!hr4>1p$2>1v$0>2st$8@3$6@4$e$2@4$d$1$4$0$5@6$c$1$4$a$0$5$b$7@1$3@3$9^3^2^1@1$3^1"). Proof. intros p v st. reflexivity. Qed.
Lemma s_groups_wr8 : ltac2:(zQ "f0!hgd!hg9!nb!ip8!hi2!hjd!j8!iq3!t1!mje!hl8!hm7!hn6!hp9!hr4>1p$2>1v$0>2st$8@3$6@4$e$2@4$d$1$4$0$5@6$c$1$4$a$0$5$b$7@1$3@3$9^3^2^1@1$3^1"). Proof. intros p v st. reflexivity. Qed.
Lemma s_slots_wr8 : ltac2:(zQ "f0!hgd!nb!hg9!iqa!hi2!hjd!ir4!j8!t1!mje!hl8!hm7!hn6!hp9!hr4>1p$1>1v$0>2st$8@3$7@4$e$1@4$d$2$4$0$5@6$c$2$4$a$0$5$b@2$6$1$0@1$3@3$9^3^2^1@1$3^1"). Proof. intros p v st. reflexivity. Qed.
Lemma s_tick_wr8 : ltac2:(zQ "70!ira!j8!hg9!hgd!nb!t1!mje>1p$4>1v$3>2st$5@3$1$2@1$0@3$6^3^2^1@1$0^1"). Proof. intros p v st. reflexivity. Qed.
Lemma s_secret_wr8 : ltac2:(zQ "60!hgd!is3!j8!nb!t1!mje>1p$3>1v$0>2st$4@3$2$0@1$1@3$5^3^2^1@1$1^1"). Proof. intros p v st. reflexivity. Qed.
Lemma s_reserved_wr8 : ltac2:(zQ "80!hgd!ise!itb!ir4!j8!nb!t1!mje>1p$5>1v$0>2st$6@3$4@1$2@2$3$0$0@1$1@3$7^3^2^1@1$1^1"). Proof. intros p v st. reflexivity. Qed.
Lemma s_ctx_wr16 : ltac2:(zQ "70!ijf!j8!hgd!nb!ij8!t1!mk4>1p$3>1v$2>2st$5@3$1$4@1$0@3$6^3^2^1@1$0^1"). Proof. intros p v st. reflexivity. Qed.
Lemma s_regions_wr16 : ltac2:(zQ "b0!il1!j8!hg9!hgd!nb!t1!ild!mk4!hl8!hr4!hi2>1p$4>1v$3>2st$5@3$1@4$9$2$a$8$6@1$0@3$7^3^2^1@1$0^1"). Proof. intros p v st. reflexivity. Qed.
Lemma s_next_rid_wr16 : ltac2:(zQ "70!ina!j8!hg9!hgd!nb!t1!mk4>1p$4>1v$3>2st$5@3$1$2@1$0@3$6^3^2^1@1$0^1"). Proof. intros p v st. reflexivity. Qed.
Lemma s_metas_wr16 : ltac2:(zQ "f0!hgd!hg9!nb!hrc!hi2!hjd!j8!rb!t1!mk4!hl8!hm7!hn6!hp9!hr4>1p$2>1v$0>2st$8@3$6@4$e$2@4$d$1$4$0$5@6$c$1$4$a$0$5$b$7@1$3@3$9^3^2^1@1$3^1"). Proof. intros p v st. reflexivity. Qed.
Lemma s_areas_wr16 : ltac2:(zQ "f0!hgd!hg9!nb!io7!hi2!hjd!j8!ip1!t1!mk4!hl8!hm7!hn6!hp9!hr4>1p$2>1v$0>2st$8@3$6@4$e$2@4$d$1$4$0$5@6$c$1$4$a$0$5$b$7@1$3@3$9^3^2^1@1$3^1"). Proof. intros p v st. reflexivity. Qed.
Lemma s_groups_wr16 : ltac2:(zQ "f0!hgd!hg9!nb!ip8!hi2!hjd!j8!iq3!t1!mk4!hl8!hm7!hn6!hp9!hr4>1p$2>1v$0>2st$8@3$6@4$e$2@4$d$1$4$0$5@6$c$1$4$a$0$5$b$7@1$3@3$9^3^2^1@1$3^1"). Proof. intros p v st. reflexivity. Qed.
Lemma s_slots_wr16 : ltac2:(zQ "f0!hgd!nb!hg9!iqa!hi2!hjd!ir4!j8!t1!mk4!hl8!hm7!hn6!hp9!hr4>1p$1>1v$0>2st$8@3$7@4$e$1@4$d$2$4$0$5@6$c$2$4$a$0$5$b@2$6$1$0@1$3@3$9^3^2^1@1$3^1"). Proof. intros p v st. reflexivity. Qed.
Lemma s_tick_wr16 : ltac2:(zQ "70!ira!j8!hg9!hgd!nb!t1!mk4>1p$4>1v$3>2st$5@3$1$2@1$0@3$6^3^2^1@1$0^1"). Proof. intros p v st. reflexivity. Qed.
Lemma s_secret_wr16 : ltac2:(zQ "60!hgd!is3!j8!nb!t1!mk4>1p$3>1v$0>2st$4@3$2$0@1$1@3$5^3^2^1@1$1^1"). Proof. intros p v st. reflexivity. Qed.
Lemma s_reserved_wr16 : ltac2:(zQ "80!hgd!ise!itb!ir4!j8!nb!t1!mk4>1p$5>1v$0>2st$6@3$4@1$2@2$3$0$0@1$1@3$7^3^2^1@1$1^1"). Proof. intros p v st. reflexivity. Qed.
Lemma s_ctx_wr32 : ltac2:(zQ "70!ijf!j8!hgd!nb!ij8!t1!mkb>1p$3>1v$2>2st$5@3$1$4@1$0@3$6^3^2^1@1$0^1"). Proof. intros p v st. reflexivity. Qed.
Lemma s_regions_wr32 : ltac2:(zQ "b0!il1!j8!hg9!hgd!nb!t1!ild!mkb!hl8!hr4!hi2>1p$4>1v$3>2st$5@3$1@4$9$2$a$8$6@1$0@3$7^3^2^1@1$0^1"). Proof. intros p v st. reflexivity. Qed.
Lemma s_next_rid_wr32 : ltac2:(zQ "70!ina!j8!hg9!hgd!nb!t1!mkb>1p$4>1v$3>2st$5@3$1$2@1$0@3$6^3^2^1@1$0^1"). Proof. intros p v st. reflexivity. Qed.
Lemma s_metas_wr32 : ltac2:(zQ "f0!hgd!hg9!nb!hrc!hi2!hjd!j8!rb!t1!mkb!hl8!hm7!hn6!hp9!hr4>1p$2>1v$0>2st$8@3$6@4$e$2@4$d$1$4$0$5@6$c$1$4$a$0$5$b$7@1$3@3$9^3^2^1@1$3^1"). Proof. intros p v st. reflexivity. Qed.
Lemma s_areas_wr32 : ltac2:(zQ "f0!hgd!hg9!nb!io7!hi2!hjd!j8!ip1!t1!mkb!hl8!hm7!hn6!hp9!hr4>1p$2>1v$0>2st$8@3$6@4$e$2@4$d$1$4$0$5@6$c$1$4$a$0$5$b$7@1$3@3$9^3^2^1@1$3^1"). Proof. intros p v st. reflexivity. Qed.
Lemma s_groups_wr32 : ltac2:(zQ "f0!hgd!hg9!nb!ip8!hi2!hjd!j8!iq3!t1!mkb!hl8!hm7!hn6!hp9!hr4>1p$2>1v$0>2st$8@3$6@4$e$2@4$d$1$4$0$5@6$c$1$4$a$0$5$b$7@1$3@3$9^3^2^1@1$3^1"). Proof. intros p v st. reflexivity. Qed.
Lemma s_slots_wr32 : ltac2:(zQ "f0!hgd!nb!hg9!iqa!hi2!hjd!ir4!j8!t1!mkb!hl8!hm7!hn6!hp9!hr4>1p$1>1v$0>2st$8@3$7@4$e$1@4$d$2$4$0$5@6$c$2$4$a$0$5$b@2$6$1$0@1$3@3$9^3^2^1@1$3^1"). Proof. intros p v st. reflexivity. Qed.
Lemma s_tick_wr32 : ltac2:(zQ "70!ira!j8!hg9!hgd!nb!t1!mkb>1p$4>1v$3>2st$5@3$1$2@1$0@3$6^3^2^1@1$0^1"). Proof. intros p v st. reflexivity. Qed.
Lemma s_secret_wr32 : ltac2:(zQ "60!hgd!is3!j8!nb!t1!mkb>1p$3>1v$0>2st$4@3$2$0@1$1@3$5^3^2^1@1$1^1"). Proof. intros p v st. reflexivity. Qed.
Lemma s_reserved_wr32 : ltac2:(zQ "80!hgd!ise!itb!ir4!j8!nb!t1!mkb>1p$5>1v$0>2st$6@3$4@1$2@2$3$0$0@1$1@3$7^3^2^1@1$1^1"). Proof. intros p v st. reflexivity. Qed.
Lemma s_ctx_havoc : ltac2:(zQ "70!ijf!j8!hgd!nb!ml2!ij8!t1>1p$3>1n$2>2st$6@3$1$5@1$0@3$4^3^2^1@1$0^1"). Proof. intros p n st. unfold havoc; destruct (n <=? 0); reflexivity. Qed.
Lemma s_regions_havoc : ltac2:(zQ "b0!il1!j8!hg9!hgd!nb!ml2!t1!ild!hl8!hr4!hi2>1p$4>1n$3>2st$6@3$1@4$9$2$a$8$7@1$0@3$5^3^2^1@1$0^1"). Proof. intros p n st. unfold havoc; destruct (n <=? 0); reflexivity. Qed.
Lemma s_next_rid_havoc : ltac2:(zQ "70!ina!j8!hg9!hgd!nb!ml2!t1>1p$4>1n$3>2st$6@3$1$2@1$0@3$5^3^2^1@1$0^1"). Proof. intros p n st. unfold havoc; destruct (n <=? 0); reflexivity. Qed.
Lemma s_metas_havoc : ltac2:(zQ "f0!hgd!hg9!nb!hrc!hi2!hjd!j8!ml2!rb!t1!hl8!hm7!hn6!hp9!hr4>1p$2>1n$0>2st$9@3$6@4$e$2@4$d$1$4$0$5@6$c$1$4$a$0$5$b$8@1$3@3$7^3^2^1@1$3^1"). Proof. intros p n st. unfold havoc; destruct (n <=? 0); reflexivity. Qed.
Lemma s_areas_havoc : ltac2:(zQ "f0!hgd!hg9!nb!io7!hi2!hjd!j8!ip1!ml2!t1!hl8!hm7!hn6!hp9!hr4>1p$2>1n$0>2st$9@3$6@4$e$2@4$d$1$4$0$5@6$c$1$4$a$0$5$b$7@1$3@3$8^3^2^1@1$3^1"). Proof. intros p n st. unfold havoc; destruct (n <=? 0); reflexivity. Qed.
Lemma s_groups_havoc : ltac2:(zQ "f0!hgd!hg9!nb!ip8!hi2!hjd!j8!iq3!ml2!t1!hl8!hm7!hn6!hp9!hr4>1p$2>1n$0>2st$9@3$6@4$e$2@4$d$1$4$0$5@6$c$1$4$a$0$5$b$7@1$3@3$8^3^2^1@1$3^1"). Proof. intros p n st. unfold havoc; destruct (n <=? 0); reflexivity. Qed.
Lemma s_slots_havoc : ltac2:(zQ "f0!hgd!nb!hg9!iqa!hi2!hjd!ir4!j8!ml2!t1!hl8!hm7!hn6!hp9!hr4>1p$1>1n$0>2st$9@3$7@4$e$1@4$d$2$4$0$5@6$c$2$4$a$0$5$b@2$6$1$0@1$3@3$8^3^2^1@1$3^1"). Proof. intros p n st. unfold havoc; destruct (n <=? 0); reflexivity. Qed.
Lemma s_tick_havoc : ltac2:(zQ "70!ira!j8!hg9!hgd!nb!ml2!t1>1p$4>1n$3>2st$6@3$1$2@1$0@3$5^3^2^1@1$0^1"). Proof. intros p n st. unfold havoc; destruct (n <=? 0); reflexivity. Qed.
Lemma s_secret_havoc : ltac2:(zQ "60!hgd!is3!j8!nb!ml2!t1>1p$3>1n$0>2st$5@3$2$0@1$1@3$4^3^2^1@1$1^1"). Proof. intros p n st. unfold havoc; destruct (n <=? 0); reflexivity. Qed.
Lemma s_reserved_havoc : ltac2:(zQ "80!hgd!ise!itb!ir4!j8!nb!ml2!t1>1p$5>1n$0>2st$7@3$4@1$2@2$3$0$0@1$1@3$6^3^2^1@1$1^1"). Proof. intros p n st. unfold havoc; destruct (n <=? 0); reflexivity. Qed.
Lemma s_ctx_hdr_havoc : ltac2:(zQ "60!ijf!j8!nb!mla!ij8!t1>1b$2>2st$5@3$1$4@1$0@2$3^2^1@1$0^1"). Proof. intros b st. reflexivity. Qed.
Lemma s_regions_hdr_havoc : ltac2:(zQ "a0!il1!j8!hg9!nb!mla!t1!ild!hl8!hr4!hi2>1b$3>2st$5@3$1@4$8$2$9$7$6@1$0@2$4^2^1@1$0^1"). Proof. intros b st. reflexivity. Qed.
Lemma s_next_rid_hdr_havoc : ltac2:(zQ "60!ina!j8!hg9!nb!mla!t1>1b$3>2st$5@3$1$2@1$0@2$4^2^1@1$0^1"). Proof. intros b st. reflexivity. Qed.
Lemma s_metas_hdr_havoc : ltac2:(zQ "f0!hg9!hgd!nb!hrc!hi2!hjd!j8!mla!rb!t1!hl8!hm7!hn6!hp9!hr4>1b$2>2st$9@3$6@4$e$2@4$d$0$4$1$5@6$c$0$4$a$1$5$b$8@1$3@2$7^2^1@1$3^1"). Proof. intros b st. reflexivity. Qed.
Lemma s_areas_hdr_havoc : ltac2:(zQ "f0!hg9!hgd!nb!io7!hi2!hjd!j8!ip1!mla!t1!hl8!hm7!hn6!hp9!hr4>1b$2>2st$9@3$6@4$e$2@4$d$0$4$1$5@6$c$0$4$a$1$5$b$7@1$3@2$8^2^1@1$3^1"). Proof. intros b st. reflexivity. Qed.
Lemma s_groups_hdr_havoc : ltac2:(zQ "f0!hg9!hgd!nb!ip8!hi2!hjd!j8!iq3!mla!t1!hl8!hm7!hn6!hp9!hr4>1b$2>2st$9@3$6@4$e$2@4$d$0$4$1$5@6$c$0$4$a$1$5$b$7@1$3@2$8^2^1@1$3^1"). Proof. intros b st. reflexivity. Qed.
Lemma s_slots_hdr_havoc : ltac2:(zQ "f0!hgd!nb!hg9!iqa!hi2!hjd!ir4!j8!mla!t1!hl8!hm7!hn6!hp9!hr4>1b$1>2st$9@3$7@4$e$1@4$d$2$4$0$5@6$c$2$4$a$0$5$b@2$6$1$0@1$3@2$8^2^1@1$3^1"). Proof. intros b st. reflexivity. Qed.
Lemma s_tick_hdr_havoc : ltac2:(zQ "60!ira!j8!hg9!nb!mla!t1>1b$3>2st$5@3$1$2@1$0@2$4^2^1@1$0^1"). Proof. intros b st. reflexivity. Qed.
Lemma s_secret_hdr_havoc : ltac2:(zQ "60!is3!j8!hgd!nb!mla!t1>1b$3>2st$5@3$1$2@1$0@2$4^2^1@1$0^1"). Proof. intros b st. reflexivity. Qed.
Lemma s_reserved_hdr_havoc : ltac2:(zQ "80!hgd!ise!itb!ir4!j8!nb!mla!t1>1b$5>2st$7@3$4@1$2@2$3$0$0@1$1@2$6^2^1@1$1^1"). Proof. intros b st. reflexivity. Qed.
Lemma s_regions_step_seq : ltac2:(zQ "90!il1!j8!hg9!t1!ild!mm6!hl8!hr4!hi2>2st$3@3$1@4$7$2$8$6$4@1$0@1$5^1@1$0^1"). Proof. intros st. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma s_shadow_step_seq : ltac2:(zQ "90!im6!j8!hg9!t1!in1!mm6!hl8!hr4!hi2>2st$3@3$1@4$7$2$8$6$4@1$0@1$5^1@1$0^1"). Proof. intros st. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma s_next_rid_step_seq : ltac2:(zQ "50!ina!j8!hg9!t1!mm6>2st$3@3$1$2@1$0@1$4^1@1$0^1"). Proof. intros st. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma s_metas_step_seq : ltac2:(zQ "f0!hg9!hgd!hrc!hi2!hjd!j8!nb!rb!t1!mm6!hl8!hm7!hn6!hp9!hr4>2st$8@3$5@4$e$6@4$d$0$3$1$4@6$c$0$3$a$1$4$b$7@1$2@1$9^1@1$2^1"). Proof. intros st. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma s_areas_step_seq : ltac2:(zQ "f0!hg9!hgd!io7!hi2!hjd!j8!nb!ip1!t1!mm6!hl8!hm7!hn6!hp9!hr4>2st$8@3$5@4$e$6@4$d$0$3$1$4@6$c$0$3$a$1$4$b$7@1$2@1$9^1@1$2^1"). Proof. intros st. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma s_groups_step_seq : ltac2:(zQ "f0!hg9!hgd!ip8!hi2!hjd!j8!nb!iq3!t1!mm6!hl8!hm7!hn6!hp9!hr4>2st$8@3$5@4$e$6@4$d$0$3$1$4@6$c$0$3$a$1$4$b$7@1$2@1$9^1@1$2^1"). Proof. intros st. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma s_slots_step_seq : ltac2:(zQ "f0!hgd!hg9!nb!iqa!hi2!hjd!ir4!j8!t1!mm6!hl8!hm7!hn6!hp9!hr4>2st$8@3$7@4$e$2@4$d$1$4$0$5@6$c$1$4$a$0$5$b@2$6$2$0@1$3@1$9^1@1$3^1"). Proof. intros st. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma s_tick_step_seq : ltac2:(zQ "50!ira!j8!hg9!t1!mm6>2st$3@3$1$2@1$0@1$4^1@1$0^1"). Proof. intros st. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma s_secret_step_seq : ltac2:(zQ "50!is3!j8!hgd!t1!mm6>2st$3@3$1$2@1$0@1$4^1@1$0^1"). Proof. intros st. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma s_reserved_step_seq : ltac2:(zQ "70!hgd!ise!itb!ir4!j8!t1!mm6>2st$5@3$4@1$2@2$3$0$0@1$1@1$6^1@1$1^1"). Proof. intros st. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma s_regions_record_seq : ltac2:(zQ "a0!il1!j8!hg9!hgd!t1!mn1!ild!hl8!hr4!hi2>2sc$3>2st$4@3$1@4$8$2$9$7$6@1$0@2$5^2^1@1$0^1"). Proof. intros sc st. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma s_shadow_record_seq : ltac2:(zQ "a0!im6!j8!hg9!hgd!t1!mn1!in1!hl8!hr4!hi2>2sc$3>2st$4@3$1@4$8$2$9$7$6@1$0@2$5^2^1@1$0^1"). Proof. intros sc st. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma s_next_rid_record_seq : ltac2:(zQ "60!ina!j8!hg9!hgd!t1!mn1>2sc$3>2st$4@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros sc st. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma s_metas_record_seq : ltac2:(zQ "f0!hgd!hg9!hrc!hi2!hjd!j8!nb!rb!t1!mn1!hl8!hm7!hn6!hp9!hr4>2sc$0>2st$8@3$5@4$e$6@4$d$1$3$0$4@6$c$1$3$a$0$4$b$7@1$2@2$9^2^1@1$2^1"). Proof. intros sc st. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma s_areas_record_seq : ltac2:(zQ "f0!hgd!hg9!io7!hi2!hjd!j8!nb!ip1!t1!mn1!hl8!hm7!hn6!hp9!hr4>2sc$0>2st$8@3$5@4$e$6@4$d$1$3$0$4@6$c$1$3$a$0$4$b$7@1$2@2$9^2^1@1$2^1"). Proof. intros sc st. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma s_groups_record_seq : ltac2:(zQ "f0!hgd!hg9!ip8!hi2!hjd!j8!nb!iq3!t1!mn1!hl8!hm7!hn6!hp9!hr4>2sc$0>2st$8@3$5@4$e$6@4$d$1$3$0$4@6$c$1$3$a$0$4$b$7@1$2@2$9^2^1@1$2^1"). Proof. intros sc st. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma s_slots_record_seq : ltac2:(zQ "f0!hgd!hg9!nb!iqa!hi2!hjd!ir4!j8!t1!mn1!hl8!hm7!hn6!hp9!hr4>2sc$0>2st$8@3$7@4$e$2@4$d$1$4$0$5@6$c$1$4$a$0$5$b@2$6$2$0@1$3@2$9^2^1@1$3^1"). Proof. intros sc st. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma s_tick_record_seq : ltac2:(zQ "60!ira!j8!hg9!hgd!t1!mn1>2sc$3>2st$4@3$1$2@1$0@2$5^2^1@1$0^1"). Proof. intros sc st. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma s_secret_record_seq : ltac2:(zQ "50!hgd!is3!j8!t1!mn1>2sc$0>2st$3@3$2$0@1$1@2$4^2^1@1$1^1"). Proof. intros sc st. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma s_reserved_record_seq : ltac2:(zQ "70!hgd!ise!itb!ir4!j8!t1!mn1>2sc$0>2st$5@3$4@1$2@2$3$0$0@1$1@2$6^2^1@1$1^1"). Proof. intros sc st. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma s_regions_account_bounce : ltac2:(zQ "a0!il1!j8!hg9!hgd!mne!t1!ild!hl8!hr4!hi2>2sc$3>2st$5@3$1@4$8$2$9$7$6@1$0@2$4^2^1@1$0^1"). Proof. intros sc st. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma s_shadow_account_bounce : ltac2:(zQ "a0!im6!j8!hg9!hgd!mne!t1!in1!hl8!hr4!hi2>2sc$3>2st$5@3$1@4$8$2$9$7$6@1$0@2$4^2^1@1$0^1"). Proof. intros sc st. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma s_next_rid_account_bounce : ltac2:(zQ "60!ina!j8!hg9!hgd!mne!t1>2sc$3>2st$5@3$1$2@1$0@2$4^2^1@1$0^1"). Proof. intros sc st. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma s_metas_account_bounce : ltac2:(zQ "f0!hgd!hg9!hrc!hi2!hjd!j8!mne!nb!rb!t1!hl8!hm7!hn6!hp9!hr4>2sc$0>2st$9@3$5@4$e$7@4$d$1$3$0$4@6$c$1$3$a$0$4$b$8@1$2@2$6^2^1@1$2^1"). Proof. intros sc st. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma s_areas_account_bounce : ltac2:(zQ "f0!hgd!hg9!io7!hi2!hjd!j8!mne!nb!ip1!t1!hl8!hm7!hn6!hp9!hr4>2sc$0>2st$9@3$5@4$e$7@4$d$1$3$0$4@6$c$1$3$a$0$4$b$8@1$2@2$6^2^1@1$2^1"). Proof. intros sc st. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma s_groups_account_bounce : ltac2:(zQ "f0!hgd!hg9!ip8!hi2!hjd!j8!mne!nb!iq3!t1!hl8!hm7!hn6!hp9!hr4>2sc$0>2st$9@3$5@4$e$7@4$d$1$3$0$4@6$c$1$3$a$0$4$b$8@1$2@2$6^2^1@1$2^1"). Proof. intros sc st. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma s_slots_account_bounce : ltac2:(zQ "f0!hgd!hg9!nb!iqa!hi2!hjd!ir4!j8!mne!t1!hl8!hm7!hn6!hp9!hr4>2sc$0>2st$9@3$7@4$e$2@4$d$1$4$0$5@6$c$1$4$a$0$5$b@2$6$2$0@1$3@2$8^2^1@1$3^1"). Proof. intros sc st. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma s_tick_account_bounce : ltac2:(zQ "60!ira!j8!hg9!hgd!mne!t1>2sc$3>2st$5@3$1$2@1$0@2$4^2^1@1$0^1"). Proof. intros sc st. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma s_secret_account_bounce : ltac2:(zQ "50!hgd!is3!j8!mne!t1>2sc$0>2st$4@3$2$0@1$1@2$3^2^1@1$1^1"). Proof. intros sc st. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma s_reserved_account_bounce : ltac2:(zQ "70!hgd!ise!itb!ir4!j8!mne!t1>2sc$0>2st$6@3$4@1$2@2$3$0$0@1$1@2$5^2^1@1$1^1"). Proof. intros sc st. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma s_regions_decay_bounces : ltac2:(zQ "a0!il1!j8!hg9!hgd!mof!t1!ild!hl8!hr4!hi2>2sc$3>2st$5@3$1@4$8$2$9$7$6@1$0@2$4^2^1@1$0^1"). Proof. intros sc st. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma s_shadow_decay_bounces : ltac2:(zQ "a0!im6!j8!hg9!hgd!mof!t1!in1!hl8!hr4!hi2>2sc$3>2st$5@3$1@4$8$2$9$7$6@1$0@2$4^2^1@1$0^1"). Proof. intros sc st. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma s_next_rid_decay_bounces : ltac2:(zQ "60!ina!j8!hg9!hgd!mof!t1>2sc$3>2st$5@3$1$2@1$0@2$4^2^1@1$0^1"). Proof. intros sc st. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma s_metas_decay_bounces : ltac2:(zQ "f0!hgd!hg9!hrc!hi2!hjd!j8!nb!mof!rb!t1!hl8!hm7!hn6!hp9!hr4>2sc$0>2st$9@3$5@4$e$6@4$d$1$3$0$4@6$c$1$3$a$0$4$b$8@1$2@2$7^2^1@1$2^1"). Proof. intros sc st. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma s_areas_decay_bounces : ltac2:(zQ "f0!hgd!hg9!io7!hi2!hjd!j8!nb!ip1!mof!t1!hl8!hm7!hn6!hp9!hr4>2sc$0>2st$9@3$5@4$e$6@4$d$1$3$0$4@6$c$1$3$a$0$4$b$7@1$2@2$8^2^1@1$2^1"). Proof. intros sc st. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma s_groups_decay_bounces : ltac2:(zQ "f0!hgd!hg9!ip8!hi2!hjd!j8!nb!mof!iq3!t1!hl8!hm7!hn6!hp9!hr4>2sc$0>2st$9@3$5@4$e$6@4$d$1$3$0$4@6$c$1$3$a$0$4$b$8@1$2@2$7^2^1@1$2^1"). Proof. intros sc st. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma s_slots_decay_bounces : ltac2:(zQ "f0!hgd!hg9!nb!iqa!hi2!hjd!ir4!j8!mof!t1!hl8!hm7!hn6!hp9!hr4>2sc$0>2st$9@3$7@4$e$2@4$d$1$4$0$5@6$c$1$4$a$0$5$b@2$6$2$0@1$3@2$8^2^1@1$3^1"). Proof. intros sc st. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma s_tick_decay_bounces : ltac2:(zQ "60!ira!j8!hg9!hgd!mof!t1>2sc$3>2st$5@3$1$2@1$0@2$4^2^1@1$0^1"). Proof. intros sc st. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma s_secret_decay_bounces : ltac2:(zQ "50!hgd!is3!j8!mof!t1>2sc$0>2st$4@3$2$0@1$1@2$3^2^1@1$1^1"). Proof. intros sc st. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma s_reserved_decay_bounces : ltac2:(zQ "70!hgd!ise!itb!ir4!j8!mof!t1>2sc$0>2st$6@3$4@1$2@2$3$0$0@1$1@2$5^2^1@1$1^1"). Proof. intros sc st. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma s_regions_set_head : ltac2:(zQ "b0!il1!j8!hg9!mpf!t1!q9!ild!mq7!hl8!hr4!hi2>1h$3>1v$5>2st$4@3$1@4$9$2$a$8$6@1$0@3$7^3^2^1@1$0^1"). Proof. intros h v st. destruct h; reflexivity. Qed.
Lemma s_shadow_set_head : ltac2:(zQ "b0!im6!j8!hg9!mpf!t1!q9!mq7!in1!hl8!hr4!hi2>1h$3>1v$5>2st$4@3$1@4$9$2$a$8$7@1$0@3$6^3^2^1@1$0^1"). Proof. intros h v st. destruct h; reflexivity. Qed.
Lemma s_next_rid_set_head : ltac2:(zQ "70!ina!j8!hg9!mpf!t1!q9!mq7>1h$3>1v$5>2st$4@3$1$2@1$0@3$6^3^2^1@1$0^1"). Proof. intros h v st. destruct h; reflexivity. Qed.
Lemma s_metas_set_head : ltac2:(zQ "h10!hg9!hgd!hrc!hi2!hjd!j8!nb!mpf!rb!t1!q9!mq7!hl8!hm7!hn6!hp9!hr4>1h$7>1v$a>2st$9@3$5@4$h0$6@4$f$0$3$1$4@6$e$0$3$c$1$4$d$8@1$2@3$b^3^2^1@1$2^1"). Proof. intros h v st. destruct h; reflexivity. Qed.
Lemma s_areas_set_head : ltac2:(zQ "h10!hg9!hgd!io7!hi2!hjd!j8!nb!ip1!mpf!t1!q9!mq7!hl8!hm7!hn6!hp9!hr4>1h$8>1v$a>2st$9@3$5@4$h0$6@4$f$0$3$1$4@6$e$0$3$c$1$4$d$7@1$2@3$b^3^2^1@1$2^1"). Proof. intros h v st. destruct h; reflexivity. Qed.
Lemma s_groups_set_head : ltac2:(zQ "h10!hg9!hgd!ip8!hi2!hjd!j8!nb!iq3!mpf!t1!q9!mq7!hl8!hm7!hn6!hp9!hr4>1h$8>1v$a>2st$9@3$5@4$h0$6@4$f$0$3$1$4@6$e$0$3$c$1$4$d$7@1$2@3$b^3^2^1@1$2^1"). Proof. intros h v st. destruct h; reflexivity. Qed.
Lemma s_slots_set_head : ltac2:(zQ "h10!hgd!hg9!nb!iqa!hi2!hjd!ir4!j8!mpf!t1!q9!mq7!hl8!hm7!hn6!hp9!hr4>1h$8>1v$a>2st$9@3$7@4$h0$2@4$f$1$4$0$5@6$e$1$4$c$0$5$d@2$6$2$0@1$3@3$b^3^2^1@1$3^1"). Proof. intros h v st. destruct h; reflexivity. Qed.
Lemma s_tick_set_head : ltac2:(zQ "70!ira!j8!hg9!mpf!t1!q9!mq7>1h$3>1v$5>2st$4@3$1$2@1$0@3$6^3^2^1@1$0^1"). Proof. intros h v st. destruct h; reflexivity. Qed.
Lemma s_secret_set_head : ltac2:(zQ "70!is3!j8!hgd!mpf!t1!q9!mq7>1h$3>1v$5>2st$4@3$1$2@1$0@3$6^3^2^1@1$0^1"). Proof. intros h v st. destruct h; reflexivity. Qed.
Lemma s_reserved_set_head : ltac2:(zQ "90!hgd!ise!itb!ir4!j8!mpf!t1!q9!mq7>1h$5>1v$7>2st$6@3$4@1$2@2$3$0$0@1$1@3$8^3^2^1@1$1^1"). Proof. intros h v st. destruct h; reflexivity. Qed.
Lemma s_regions_dequeue : ltac2:(zQ "b0!il1!j8!hg9!nb!mr2!mpf!t1!ild!hl8!hr4!hi2>1h$5>1m$3>2st$6@3$1@4$9$2$a$8$7@1$0@3$4^3^2^1@1$0^1"). Proof. intros h m st. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma s_shadow_dequeue : ltac2:(zQ "b0!im6!j8!hg9!nb!mr2!mpf!t1!in1!hl8!hr4!hi2>1h$5>1m$3>2st$6@3$1@4$9$2$a$8$7@1$0@3$4^3^2^1@1$0^1"). Proof. intros h m st. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma s_next_rid_dequeue : ltac2:(zQ "70!ina!j8!hg9!nb!mr2!mpf!t1>1h$5>1m$3>2st$6@3$1$2@1$0@3$4^3^2^1@1$0^1"). Proof. intros h m st. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma s_areas_dequeue : ltac2:(zQ "h00!hg9!hgd!nb!io7!hi2!hjd!j8!ip1!mr2!mpf!t1!hl8!hm7!hn6!hp9!hr4>1h$9>1m$2>2st$a@3$6@4$f$2@4$e$0$4$1$5@6$d$0$4$b$1$5$c$7@1$3@3$8^3^2^1@1$3^1"). Proof. intros h m st. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma s_groups_dequeue : ltac2:(zQ "h00!hg9!hgd!nb!ip8!hi2!hjd!j8!mr2!iq3!mpf!t1!hl8!hm7!hn6!hp9!hr4>1h$9>1m$2>2st$a@3$6@4$f$2@4$e$0$4$1$5@6$d$0$4$b$1$5$c$8@1$3@3$7^3^2^1@1$3^1"). Proof. intros h m st. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma s_slots_dequeue : ltac2:(zQ "h00!hgd!nb!hg9!iqa!hi2!hjd!ir4!j8!mr2!mpf!t1!hl8!hm7!hn6!hp9!hr4>1h$9>1m$1>2st$a@3$7@4$f$1@4$e$2$4$0$5@6$d$2$4$b$0$5$c@2$6$1$0@1$3@3$8^3^2^1@1$3^1"). Proof. intros h m st. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma s_tick_dequeue : ltac2:(zQ "70!ira!j8!hg9!nb!mr2!mpf!t1>1h$5>1m$3>2st$6@3$1$2@1$0@3$4^3^2^1@1$0^1"). Proof. intros h m st. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma s_secret_dequeue : ltac2:(zQ "70!is3!j8!hgd!nb!mr2!mpf!t1>1h$5>1m$3>2st$6@3$1$2@1$0@3$4^3^2^1@1$0^1"). Proof. intros h m st. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma s_reserved_dequeue : ltac2:(zQ "90!hgd!ise!itb!ir4!j8!nb!mr2!mpf!t1>1h$7>1m$5>2st$8@3$4@1$2@2$3$0$0@1$1@3$6^3^2^1@1$1^1"). Proof. intros h m st. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma s_ctx_set_size : ltac2:(zQ "70!hgd!nb!ijf!j8!ij8!t1!mrc>1p$1>1e$1>1n$0>2b3$0>2st$5@3$3$4@1$2@5$6^5^4^3^2^1@1$2^1"). Proof. intros p e n b3 st. unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
Lemma s_regions_set_size : ltac2:(zQ "b0!hgd!nb!il1!j8!hg9!t1!ild!mrc!hl8!hr4!hi2>1p$1>1e$1>1n$0>2b3$0>2st$5@3$3@4$9$4$a$8$6@1$2@5$7^5^4^3^2^1@1$2^1"). Proof. intros p e n b3 st. unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
Lemma s_next_rid_set_size : ltac2:(zQ "70!hgd!nb!ina!j8!hg9!t1!mrc>1p$1>1e$1>1n$0>2b3$0>2st$5@3$3$4@1$2@5$6^5^4^3^2^1@1$2^1"). Proof. intros p e n b3 st. unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
Lemma s_metas_set_size : ltac2:(zQ "f0!hgd!nb!hg9!hrc!hi2!hjd!j8!rb!t1!mrc!hl8!hm7!hn6!hp9!hr4>1p$1>1e$1>1n$0>2b3$0>2st$8@3$6@4$e$1@4$d$2$4$0$5@6$c$2$4$a$0$5$b$7@1$3@5$9^5^4^3^2^1@1$3^1"). Proof. intros p e n b3 st. unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
Lemma s_areas_set_size : ltac2:(zQ "f0!hgd!nb!hg9!io7!hi2!hjd!j8!ip1!t1!mrc!hl8!hm7!hn6!hp9!hr4>1p$1>1e$1>1n$0>2b3$0>2st$8@3$6@4$e$1@4$d$2$4$0$5@6$c$2$4$a$0$5$b$7@1$3@5$9^5^4^3^2^1@1$3^1"). Proof. intros p e n b3 st. unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
Lemma s_groups_set_size : ltac2:(zQ "f0!hgd!nb!hg9!ip8!hi2!hjd!j8!iq3!t1!mrc!hl8!hm7!hn6!hp9!hr4>1p$1>1e$1>1n$0>2b3$0>2st$8@3$6@4$e$1@4$d$2$4$0$5@6$c$2$4$a$0$5$b$7@1$3@5$9^5^4^3^2^1@1$3^1"). Proof. intros p e n b3 st. unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
Lemma s_slots_set_size : ltac2:(zQ "f0!hgd!nb!hg9!iqa!hi2!hjd!ir4!j8!t1!mrc!hl8!hm7!hn6!hp9!hr4>1p$1>1e$1>1n$0>2b3$0>2st$8@3$7@4$e$1@4$d$2$4$0$5@6$c$2$4$a$0$5$b@2$6$1$0@1$3@5$9^5^4^3^2^1@1$3^1"). Proof. intros p e n b3 st. unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
Lemma s_tick_set_size : ltac2:(zQ "70!hgd!nb!ira!j8!hg9!t1!mrc>1p$1>1e$1>1n$0>2b3$0>2st$5@3$3$4@1$2@5$6^5^4^3^2^1@1$2^1"). Proof. intros p e n b3 st. unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
Lemma s_secret_set_size : ltac2:(zQ "60!hgd!nb!is3!j8!t1!mrc>1p$1>1e$1>1n$0>2b3$0>2st$4@3$3$0@1$2@5$5^5^4^3^2^1@1$2^1"). Proof. intros p e n b3 st. unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
Lemma s_reserved_set_size : ltac2:(zQ "80!hgd!nb!ise!itb!ir4!j8!t1!mrc>1p$1>1e$1>1n$0>2b3$0>2st$6@3$5@1$3@2$4$0$0@1$2@5$7^5^4^3^2^1@1$2^1"). Proof. intros p e n b3 st. unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
Lemma c_secret_set_active : ltac2:(zQ "70!hgd!jk7!ijf!j8!t1!q9!lq8>2sc$0>1v$5>2st$4@3$3$0@1$1@1$2@3$6^3^2^1@1$1@1$2^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma c_init_done_set_active : ltac2:(zQ "70!hgd!jlf!ijf!j8!t1!q9!lq8>2sc$0>1v$5>2st$4@3$3$0@1$1@1$2@3$6^3^2^1@1$1@1$2^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma c_mmap_counter_set_active : ltac2:(zQ "70!hgd!jmd!ijf!j8!t1!q9!lq8>2sc$0>1v$5>2st$4@3$3$0@1$1@1$2@3$6^3^2^1@1$1@1$2^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma c_free_meta_head_set_active : ltac2:(zQ "70!jne!q9!ijf!j8!hgd!t1!lq8>2sc$4>1v$1>2st$5@3$3$1@1$0@1$2@3$6^3^2^1@1$0@1$2^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma c_avail_meta_set_active : ltac2:(zQ "70!jp2!q9!ijf!j8!hgd!t1!lq8>2sc$4>1v$1>2st$5@3$3$1@1$0@1$2@3$6^3^2^1@1$0@1$2^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma c_avail_meta_count_set_active : ltac2:(zQ "70!hgd!jq1!ijf!j8!t1!q9!lq8>2sc$0>1v$5>2st$4@3$3$0@1$1@1$2@3$6^3^2^1@1$1@1$2^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_active : ltac2:(zQ "70!hgd!jr7!ijf!j8!t1!q9!lq8>2sc$0>1v$5>2st$4@3$3$0@1$1@1$2@3$6^3^2^1@1$1@1$2^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_active : ltac2:(zQ "70!hgd!jt2!ijf!j8!t1!q9!lq8>2sc$0>1v$5>2st$4@3$3$0@1$1@1$2@3$6^3^2^1@1$1@1$2^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma c_meta_area_head_set_active : ltac2:(zQ "70!ju8!q9!ijf!j8!hgd!t1!lq8>2sc$4>1v$1>2st$5@3$3$1@1$0@1$2@3$6^3^2^1@1$0@1$2^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma c_meta_area_tail_set_active : ltac2:(zQ "70!jvc!q9!ijf!j8!hgd!t1!lq8>2sc$4>1v$1>2st$5@3$3$1@1$0@1$2@3$6^3^2^1@1$0@1$2^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma c_avail_meta_areas_set_active : ltac2:(zQ "70!kh0!q9!ijf!j8!hgd!t1!lq8>2sc$4>1v$1>2st$5@3$3$1@1$0@1$2@3$6^3^2^1@1$0@1$2^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma c_usage_set_active : ltac2:(zQ "a0!hgd!kj1!ijf!j8!t1!q9!lq8!hm7!hr4!hjd>2sc$0>1v$5>2st$4@3$3@4$8$0$9$7$0@1$1@1$2@3$6^3^2^1@1$1@1$2^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma c_unmap_seq_set_active : ltac2:(zQ "a0!hgd!kjb!ijf!j8!t1!q9!lq8!hm7!hr4!hjd>2sc$0>1v$5>2st$4@3$3@4$8$0$9$7$0@1$1@1$2@3$6^3^2^1@1$1@1$2^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma c_bounces_set_active : ltac2:(zQ "a0!hgd!kk9!ijf!j8!t1!q9!lq8!hm7!hr4!hjd>2sc$0>1v$5>2st$4@3$3@4$8$0$9$7$0@1$1@1$2@3$6^3^2^1@1$1@1$2^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma c_seq_set_active : ltac2:(zQ "70!hgd!kl5!ijf!j8!t1!q9!lq8>2sc$0>1v$5>2st$4@3$3$0@1$1@1$2@3$6^3^2^1@1$1@1$2^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma c_brk_set_active : ltac2:(zQ "80!kld!ijf!j8!hgd!km5!t1!q9!lq8>2sc$3>1v$6>2st$5@3$2$4@1$0@1$1@3$7^3^2^1@1$0@1$1^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma c_secret_set_usage : ltac2:(zQ "60!hgd!jk7!ijf!j8!t1!lr5>2sc$0>1v$0>2st$4@3$3$0@1$1@1$2@3$5^3^2^1@1$1@1$2^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma c_init_done_set_usage : ltac2:(zQ "60!hgd!jlf!ijf!j8!t1!lr5>2sc$0>1v$0>2st$4@3$3$0@1$1@1$2@3$5^3^2^1@1$1@1$2^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma c_mmap_counter_set_usage : ltac2:(zQ "60!hgd!jmd!ijf!j8!t1!lr5>2sc$0>1v$0>2st$4@3$3$0@1$1@1$2@3$5^3^2^1@1$1@1$2^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma c_free_meta_head_set_usage : ltac2:(zQ "70!hgd!jne!ijf!j8!t1!q9!lr5>2sc$0>1v$0>2st$4@3$3$5@1$1@1$2@3$6^3^2^1@1$1@1$2^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma c_avail_meta_set_usage : ltac2:(zQ "70!hgd!jp2!ijf!j8!t1!q9!lr5>2sc$0>1v$0>2st$4@3$3$5@1$1@1$2@3$6^3^2^1@1$1@1$2^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma c_avail_meta_count_set_usage : ltac2:(zQ "60!hgd!jq1!ijf!j8!t1!lr5>2sc$0>1v$0>2st$4@3$3$0@1$1@1$2@3$5^3^2^1@1$1@1$2^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_usage : ltac2:(zQ "60!hgd!jr7!ijf!j8!t1!lr5>2sc$0>1v$0>2st$4@3$3$0@1$1@1$2@3$5^3^2^1@1$1@1$2^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_usage : ltac2:(zQ "60!hgd!jt2!ijf!j8!t1!lr5>2sc$0>1v$0>2st$4@3$3$0@1$1@1$2@3$5^3^2^1@1$1@1$2^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma c_meta_area_head_set_usage : ltac2:(zQ "70!hgd!ju8!ijf!j8!t1!q9!lr5>2sc$0>1v$0>2st$4@3$3$5@1$1@1$2@3$6^3^2^1@1$1@1$2^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma c_meta_area_tail_set_usage : ltac2:(zQ "70!hgd!jvc!ijf!j8!t1!q9!lr5>2sc$0>1v$0>2st$4@3$3$5@1$1@1$2@3$6^3^2^1@1$1@1$2^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma c_avail_meta_areas_set_usage : ltac2:(zQ "70!hgd!kh0!ijf!j8!t1!q9!lr5>2sc$0>1v$0>2st$4@3$3$5@1$1@1$2@3$6^3^2^1@1$1@1$2^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma c_active_set_usage : ltac2:(zQ "a0!hgd!ki6!ijf!j8!nb!t1!lr5!hm7!hr4!hjd>2sc$0>1v$0>2st$5@3$3@4$8$0$9$7$4@1$1@1$2@3$6^3^2^1@1$1@1$2^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma c_unmap_seq_set_usage : ltac2:(zQ "90!hgd!kjb!ijf!j8!t1!lr5!hm7!hr4!hjd>2sc$0>1v$0>2st$4@3$3@4$7$0$8$6$0@1$1@1$2@3$5^3^2^1@1$1@1$2^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma c_bounces_set_usage : ltac2:(zQ "90!hgd!kk9!ijf!j8!t1!lr5!hm7!hr4!hjd>2sc$0>1v$0>2st$4@3$3@4$7$0$8$6$0@1$1@1$2@3$5^3^2^1@1$1@1$2^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma c_seq_set_usage : ltac2:(zQ "60!hgd!kl5!ijf!j8!t1!lr5>2sc$0>1v$0>2st$4@3$3$0@1$1@1$2@3$5^3^2^1@1$1@1$2^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma c_brk_set_usage : ltac2:(zQ "70!hgd!kld!ijf!j8!km5!t1!lr5>2sc$0>1v$0>2st$5@3$3$4@1$1@1$2@3$6^3^2^1@1$1@1$2^1"). Proof. intros sc v st. reflexivity. Qed.
Lemma c_secret_set_bounce : ltac2:(zQ "60!hgd!jk7!ijf!j8!t1!ls1>1i$0>1v$0>2st$4@3$3$0@1$1@1$2@3$5^3^2^1@1$1@1$2^1"). Proof. intros i v st. reflexivity. Qed.
Lemma c_init_done_set_bounce : ltac2:(zQ "60!hgd!jlf!ijf!j8!t1!ls1>1i$0>1v$0>2st$4@3$3$0@1$1@1$2@3$5^3^2^1@1$1@1$2^1"). Proof. intros i v st. reflexivity. Qed.
Lemma c_mmap_counter_set_bounce : ltac2:(zQ "60!hgd!jmd!ijf!j8!t1!ls1>1i$0>1v$0>2st$4@3$3$0@1$1@1$2@3$5^3^2^1@1$1@1$2^1"). Proof. intros i v st. reflexivity. Qed.
Lemma c_free_meta_head_set_bounce : ltac2:(zQ "70!hgd!jne!ijf!j8!t1!q9!ls1>1i$0>1v$0>2st$4@3$3$5@1$1@1$2@3$6^3^2^1@1$1@1$2^1"). Proof. intros i v st. reflexivity. Qed.
Lemma c_avail_meta_set_bounce : ltac2:(zQ "70!hgd!jp2!ijf!j8!t1!q9!ls1>1i$0>1v$0>2st$4@3$3$5@1$1@1$2@3$6^3^2^1@1$1@1$2^1"). Proof. intros i v st. reflexivity. Qed.
Lemma c_avail_meta_count_set_bounce : ltac2:(zQ "60!hgd!jq1!ijf!j8!t1!ls1>1i$0>1v$0>2st$4@3$3$0@1$1@1$2@3$5^3^2^1@1$1@1$2^1"). Proof. intros i v st. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_bounce : ltac2:(zQ "60!hgd!jr7!ijf!j8!t1!ls1>1i$0>1v$0>2st$4@3$3$0@1$1@1$2@3$5^3^2^1@1$1@1$2^1"). Proof. intros i v st. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_bounce : ltac2:(zQ "60!hgd!jt2!ijf!j8!t1!ls1>1i$0>1v$0>2st$4@3$3$0@1$1@1$2@3$5^3^2^1@1$1@1$2^1"). Proof. intros i v st. reflexivity. Qed.
Lemma c_meta_area_head_set_bounce : ltac2:(zQ "70!hgd!ju8!ijf!j8!t1!q9!ls1>1i$0>1v$0>2st$4@3$3$5@1$1@1$2@3$6^3^2^1@1$1@1$2^1"). Proof. intros i v st. reflexivity. Qed.
Lemma c_meta_area_tail_set_bounce : ltac2:(zQ "70!hgd!jvc!ijf!j8!t1!q9!ls1>1i$0>1v$0>2st$4@3$3$5@1$1@1$2@3$6^3^2^1@1$1@1$2^1"). Proof. intros i v st. reflexivity. Qed.
Lemma c_avail_meta_areas_set_bounce : ltac2:(zQ "70!hgd!kh0!ijf!j8!t1!q9!ls1>1i$0>1v$0>2st$4@3$3$5@1$1@1$2@3$6^3^2^1@1$1@1$2^1"). Proof. intros i v st. reflexivity. Qed.
Lemma c_active_set_bounce : ltac2:(zQ "a0!hgd!ki6!ijf!j8!nb!t1!ls1!hm7!hr4!hjd>1i$0>1v$0>2st$5@3$3@4$8$0$9$7$4@1$1@1$2@3$6^3^2^1@1$1@1$2^1"). Proof. intros i v st. reflexivity. Qed.
Lemma c_usage_set_bounce : ltac2:(zQ "90!hgd!kj1!ijf!j8!t1!ls1!hm7!hr4!hjd>1i$0>1v$0>2st$4@3$3@4$7$0$8$6$0@1$1@1$2@3$5^3^2^1@1$1@1$2^1"). Proof. intros i v st. reflexivity. Qed.
Lemma c_unmap_seq_set_bounce : ltac2:(zQ "90!hgd!kjb!ijf!j8!t1!ls1!hm7!hr4!hjd>1i$0>1v$0>2st$4@3$3@4$7$0$8$6$0@1$1@1$2@3$5^3^2^1@1$1@1$2^1"). Proof. intros i v st. reflexivity. Qed.
Lemma c_seq_set_bounce : ltac2:(zQ "60!hgd!kl5!ijf!j8!t1!ls1>1i$0>1v$0>2st$4@3$3$0@1$1@1$2@3$5^3^2^1@1$1@1$2^1"). Proof. intros i v st. reflexivity. Qed.
Lemma c_brk_set_bounce : ltac2:(zQ "70!hgd!kld!ijf!j8!km5!t1!ls1>1i$0>1v$0>2st$5@3$3$4@1$1@1$2@3$6^3^2^1@1$1@1$2^1"). Proof. intros i v st. reflexivity. Qed.
Lemma c_secret_step_seq : ltac2:(zQ "60!jk7!ijf!j8!hgd!t1!mm6>2st$4@3$2$3@1$0@1$1@1$5^1@1$0@1$1^1"). Proof. intros st. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_init_done_step_seq : ltac2:(zQ "60!jlf!ijf!j8!hgd!t1!mm6>2st$4@3$2$3@1$0@1$1@1$5^1@1$0@1$1^1"). Proof. intros st. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_mmap_counter_step_seq : ltac2:(zQ "60!jmd!ijf!j8!hgd!t1!mm6>2st$4@3$2$3@1$0@1$1@1$5^1@1$0@1$1^1"). Proof. intros st. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_free_meta_head_step_seq : ltac2:(zQ "60!jne!ijf!j8!t1!q9!mm6>2st$3@3$2$4@1$0@1$1@1$5^1@1$0@1$1^1"). Proof. intros st. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_avail_meta_step_seq : ltac2:(zQ "60!jp2!ijf!j8!t1!q9!mm6>2st$3@3$2$4@1$0@1$1@1$5^1@1$0@1$1^1"). Proof. intros st. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_avail_meta_count_step_seq : ltac2:(zQ "60!jq1!ijf!j8!hgd!t1!mm6>2st$4@3$2$3@1$0@1$1@1$5^1@1$0@1$1^1"). Proof. intros st. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_avail_meta_area_count_step_seq : ltac2:(zQ "60!jr7!ijf!j8!hgd!t1!mm6>2st$4@3$2$3@1$0@1$1@1$5^1@1$0@1$1^1"). Proof. intros st. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_meta_alloc_shift_step_seq : ltac2:(zQ "60!jt2!ijf!j8!hgd!t1!mm6>2st$4@3$2$3@1$0@1$1@1$5^1@1$0@1$1^1"). Proof. intros st. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_meta_area_head_step_seq : ltac2:(zQ "60!ju8!ijf!j8!t1!q9!mm6>2st$3@3$2$4@1$0@1$1@1$5^1@1$0@1$1^1"). Proof. intros st. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_meta_area_tail_step_seq : ltac2:(zQ "60!jvc!ijf!j8!t1!q9!mm6>2st$3@3$2$4@1$0@1$1@1$5^1@1$0@1$1^1"). Proof. intros st. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_avail_meta_areas_step_seq : ltac2:(zQ "60!kh0!ijf!j8!t1!q9!mm6>2st$3@3$2$4@1$0@1$1@1$5^1@1$0@1$1^1"). Proof. intros st. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_active_step_seq : ltac2:(zQ "a0!ki6!ijf!j8!hgd!nb!t1!mm6!hm7!hr4!hjd>2st$5@3$2@4$8$3$9$7$4@1$0@1$1@1$6^1@1$0@1$1^1"). Proof. intros st. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_usage_step_seq : ltac2:(zQ "90!hgd!kj1!ijf!j8!t1!mm6!hm7!hr4!hjd>2st$4@3$3@4$7$0$8$6$0@1$1@1$2@1$5^1@1$1@1$2^1"). Proof. intros st. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_bounces_step_seq : ltac2:(zQ "90!hgd!kk9!ijf!j8!t1!mm6!hm7!hr4!hjd>2st$4@3$3@4$7$0$8$6$0@1$1@1$2@1$5^1@1$1@1$2^1"). Proof. intros st. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_brk_step_seq : ltac2:(zQ "60!kld!ijf!j8!km5!t1!mm6>2st$4@3$2$3@1$0@1$1@1$5^1@1$0@1$1^1"). Proof. intros st. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_secret_record_seq : ltac2:(zQ "60!hgd!jk7!ijf!j8!t1!mn1>2sc$0>2st$4@3$3$0@1$1@1$2@2$5^2^1@1$1@1$2^1"). Proof. intros sc st. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_init_done_record_seq : ltac2:(zQ "60!hgd!jlf!ijf!j8!t1!mn1>2sc$0>2st$4@3$3$0@1$1@1$2@2$5^2^1@1$1@1$2^1"). Proof. intros sc st. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_mmap_counter_record_seq : ltac2:(zQ "60!hgd!jmd!ijf!j8!t1!mn1>2sc$0>2st$4@3$3$0@1$1@1$2@2$5^2^1@1$1@1$2^1"). Proof. intros sc st. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_free_meta_head_record_seq : ltac2:(zQ "70!jne!ijf!j8!hgd!t1!q9!mn1>2sc$3>2st$4@3$2$5@1$0@1$1@2$6^2^1@1$0@1$1^1"). Proof. intros sc st. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_avail_meta_record_seq : ltac2:(zQ "70!jp2!ijf!j8!hgd!t1!q9!mn1>2sc$3>2st$4@3$2$5@1$0@1$1@2$6^2^1@1$0@1$1^1"). Proof. intros sc st. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_avail_meta_count_record_seq : ltac2:(zQ "60!hgd!jq1!ijf!j8!t1!mn1>2sc$0>2st$4@3$3$0@1$1@1$2@2$5^2^1@1$1@1$2^1"). Proof. intros sc st. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_avail_meta_area_count_record_seq : ltac2:(zQ "60!hgd!jr7!ijf!j8!t1!mn1>2sc$0>2st$4@3$3$0@1$1@1$2@2$5^2^1@1$1@1$2^1"). Proof. intros sc st. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_meta_alloc_shift_record_seq : ltac2:(zQ "60!hgd!jt2!ijf!j8!t1!mn1>2sc$0>2st$4@3$3$0@1$1@1$2@2$5^2^1@1$1@1$2^1"). Proof. intros sc st. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_meta_area_head_record_seq : ltac2:(zQ "70!ju8!ijf!j8!hgd!t1!q9!mn1>2sc$3>2st$4@3$2$5@1$0@1$1@2$6^2^1@1$0@1$1^1"). Proof. intros sc st. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_meta_area_tail_record_seq : ltac2:(zQ "70!jvc!ijf!j8!hgd!t1!q9!mn1>2sc$3>2st$4@3$2$5@1$0@1$1@2$6^2^1@1$0@1$1^1"). Proof. intros sc st. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_avail_meta_areas_record_seq : ltac2:(zQ "70!kh0!ijf!j8!hgd!t1!q9!mn1>2sc$3>2st$4@3$2$5@1$0@1$1@2$6^2^1@1$0@1$1^1"). Proof. intros sc st. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_active_record_seq : ltac2:(zQ "a0!hgd!ki6!ijf!j8!nb!t1!mn1!hm7!hr4!hjd>2sc$0>2st$5@3$3@4$8$0$9$7$4@1$1@1$2@2$6^2^1@1$1@1$2^1"). Proof. intros sc st. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_usage_record_seq : ltac2:(zQ "90!hgd!kj1!ijf!j8!t1!mn1!hm7!hr4!hjd>2sc$0>2st$4@3$3@4$7$0$8$6$0@1$1@1$2@2$5^2^1@1$1@1$2^1"). Proof. intros sc st. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_bounces_record_seq : ltac2:(zQ "90!hgd!kk9!ijf!j8!t1!mn1!hm7!hr4!hjd>2sc$0>2st$4@3$3@4$7$0$8$6$0@1$1@1$2@2$5^2^1@1$1@1$2^1"). Proof. intros sc st. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_seq_record_seq : ltac2:(zQ "60!hgd!kl5!ijf!j8!t1!mn1>2sc$0>2st$4@3$3$0@1$1@1$2@2$5^2^1@1$1@1$2^1"). Proof. intros sc st. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_brk_record_seq : ltac2:(zQ "70!kld!ijf!j8!hgd!km5!t1!mn1>2sc$3>2st$5@3$2$4@1$0@1$1@2$6^2^1@1$0@1$1^1"). Proof. intros sc st. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_secret_account_bounce : ltac2:(zQ "60!hgd!jk7!ijf!j8!mne!t1>2sc$0>2st$5@3$3$0@1$1@1$2@2$4^2^1@1$1@1$2^1"). Proof. intros sc st. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_init_done_account_bounce : ltac2:(zQ "60!hgd!jlf!ijf!j8!mne!t1>2sc$0>2st$5@3$3$0@1$1@1$2@2$4^2^1@1$1@1$2^1"). Proof. intros sc st. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_mmap_counter_account_bounce : ltac2:(zQ "60!hgd!jmd!ijf!j8!mne!t1>2sc$0>2st$5@3$3$0@1$1@1$2@2$4^2^1@1$1@1$2^1"). Proof. intros sc st. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_free_meta_head_account_bounce : ltac2:(zQ "70!jne!ijf!j8!hgd!mne!t1!q9>2sc$3>2st$5@3$2$6@1$0@1$1@2$4^2^1@1$0@1$1^1"). Proof. intros sc st. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_avail_meta_account_bounce : ltac2:(zQ "70!jp2!ijf!j8!hgd!mne!t1!q9>2sc$3>2st$5@3$2$6@1$0@1$1@2$4^2^1@1$0@1$1^1"). Proof. intros sc st. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_avail_meta_count_account_bounce : ltac2:(zQ "60!hgd!jq1!ijf!j8!mne!t1>2sc$0>2st$5@3$3$0@1$1@1$2@2$4^2^1@1$1@1$2^1"). Proof. intros sc st. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_avail_meta_area_count_account_bounce : ltac2:(zQ "60!hgd!jr7!ijf!j8!mne!t1>2sc$0>2st$5@3$3$0@1$1@1$2@2$4^2^1@1$1@1$2^1"). Proof. intros sc st. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_meta_alloc_shift_account_bounce : ltac2:(zQ "60!hgd!jt2!ijf!j8!mne!t1>2sc$0>2st$5@3$3$0@1$1@1$2@2$4^2^1@1$1@1$2^1"). Proof. intros sc st. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_meta_area_head_account_bounce : ltac2:(zQ "70!ju8!ijf!j8!hgd!mne!t1!q9>2sc$3>2st$5@3$2$6@1$0@1$1@2$4^2^1@1$0@1$1^1"). Proof. intros sc st. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_meta_area_tail_account_bounce : ltac2:(zQ "70!jvc!ijf!j8!hgd!mne!t1!q9>2sc$3>2st$5@3$2$6@1$0@1$1@2$4^2^1@1$0@1$1^1"). Proof. intros sc st. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_avail_meta_areas_account_bounce : ltac2:(zQ "70!kh0!ijf!j8!hgd!mne!t1!q9>2sc$3>2st$5@3$2$6@1$0@1$1@2$4^2^1@1$0@1$1^1"). Proof. intros sc st. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_active_account_bounce : ltac2:(zQ "a0!hgd!ki6!ijf!j8!mne!nb!t1!hm7!hr4!hjd>2sc$0>2st$6@3$3@4$8$0$9$7$5@1$1@1$2@2$4^2^1@1$1@1$2^1"). Proof. intros sc st. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_usage_account_bounce : ltac2:(zQ "90!hgd!kj1!ijf!j8!mne!t1!hm7!hr4!hjd>2sc$0>2st$5@3$3@4$7$0$8$6$0@1$1@1$2@2$4^2^1@1$1@1$2^1"). Proof. intros sc st. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_unmap_seq_account_bounce : ltac2:(zQ "90!hgd!kjb!ijf!j8!mne!t1!hm7!hr4!hjd>2sc$0>2st$5@3$3@4$7$0$8$6$0@1$1@1$2@2$4^2^1@1$1@1$2^1"). Proof. intros sc st. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_seq_account_bounce : ltac2:(zQ "60!hgd!kl5!ijf!j8!mne!t1>2sc$0>2st$5@3$3$0@1$1@1$2@2$4^2^1@1$1@1$2^1"). Proof. intros sc st. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_brk_account_bounce : ltac2:(zQ "70!kld!ijf!j8!hgd!mne!km5!t1>2sc$3>2st$6@3$2$5@1$0@1$1@2$4^2^1@1$0@1$1^1"). Proof. intros sc st. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_secret_decay_bounces : ltac2:(zQ "60!hgd!jk7!ijf!j8!mof!t1>2sc$0>2st$5@3$3$0@1$1@1$2@2$4^2^1@1$1@1$2^1"). Proof. intros sc st. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_init_done_decay_bounces : ltac2:(zQ "60!hgd!jlf!ijf!j8!mof!t1>2sc$0>2st$5@3$3$0@1$1@1$2@2$4^2^1@1$1@1$2^1"). Proof. intros sc st. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_mmap_counter_decay_bounces : ltac2:(zQ "60!hgd!jmd!ijf!j8!mof!t1>2sc$0>2st$5@3$3$0@1$1@1$2@2$4^2^1@1$1@1$2^1"). Proof. intros sc st. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_free_meta_head_decay_bounces : ltac2:(zQ "70!jne!ijf!j8!hgd!mof!t1!q9>2sc$3>2st$5@3$2$6@1$0@1$1@2$4^2^1@1$0@1$1^1"). Proof. intros sc st. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_avail_meta_decay_bounces : ltac2:(zQ "70!jp2!ijf!j8!hgd!mof!t1!q9>2sc$3>2st$5@3$2$6@1$0@1$1@2$4^2^1@1$0@1$1^1"). Proof. intros sc st. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_avail_meta_count_decay_bounces : ltac2:(zQ "60!hgd!jq1!ijf!j8!mof!t1>2sc$0>2st$5@3$3$0@1$1@1$2@2$4^2^1@1$1@1$2^1"). Proof. intros sc st. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_avail_meta_area_count_decay_bounces : ltac2:(zQ "60!hgd!jr7!ijf!j8!mof!t1>2sc$0>2st$5@3$3$0@1$1@1$2@2$4^2^1@1$1@1$2^1"). Proof. intros sc st. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_meta_alloc_shift_decay_bounces : ltac2:(zQ "60!hgd!jt2!ijf!j8!mof!t1>2sc$0>2st$5@3$3$0@1$1@1$2@2$4^2^1@1$1@1$2^1"). Proof. intros sc st. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_meta_area_head_decay_bounces : ltac2:(zQ "70!ju8!ijf!j8!hgd!mof!t1!q9>2sc$3>2st$5@3$2$6@1$0@1$1@2$4^2^1@1$0@1$1^1"). Proof. intros sc st. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_meta_area_tail_decay_bounces : ltac2:(zQ "70!jvc!ijf!j8!hgd!mof!t1!q9>2sc$3>2st$5@3$2$6@1$0@1$1@2$4^2^1@1$0@1$1^1"). Proof. intros sc st. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_avail_meta_areas_decay_bounces : ltac2:(zQ "70!kh0!ijf!j8!hgd!mof!t1!q9>2sc$3>2st$5@3$2$6@1$0@1$1@2$4^2^1@1$0@1$1^1"). Proof. intros sc st. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_active_decay_bounces : ltac2:(zQ "a0!hgd!ki6!ijf!j8!nb!mof!t1!hm7!hr4!hjd>2sc$0>2st$6@3$3@4$8$0$9$7$4@1$1@1$2@2$5^2^1@1$1@1$2^1"). Proof. intros sc st. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_usage_decay_bounces : ltac2:(zQ "90!hgd!kj1!ijf!j8!mof!t1!hm7!hr4!hjd>2sc$0>2st$5@3$3@4$7$0$8$6$0@1$1@1$2@2$4^2^1@1$1@1$2^1"). Proof. intros sc st. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_unmap_seq_decay_bounces : ltac2:(zQ "90!hgd!kjb!ijf!j8!mof!t1!hm7!hr4!hjd>2sc$0>2st$5@3$3@4$7$0$8$6$0@1$1@1$2@2$4^2^1@1$1@1$2^1"). Proof. intros sc st. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_seq_decay_bounces : ltac2:(zQ "60!hgd!kl5!ijf!j8!mof!t1>2sc$0>2st$5@3$3$0@1$1@1$2@2$4^2^1@1$1@1$2^1"). Proof. intros sc st. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_brk_decay_bounces : ltac2:(zQ "70!kld!ijf!j8!hgd!km5!mof!t1>2sc$3>2st$6@3$2$4@1$0@1$1@2$5^2^1@1$0@1$1^1"). Proof. intros sc st. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_secret_dequeue : ltac2:(zQ "80!jk7!ijf!j8!hgd!nb!mr2!mpf!t1>1h$6>1m$4>2st$7@3$2$3@1$0@1$1@3$5^3^2^1@1$0@1$1^1"). Proof. intros h m st. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma c_init_done_dequeue : ltac2:(zQ "80!jlf!ijf!j8!hgd!nb!mr2!mpf!t1>1h$6>1m$4>2st$7@3$2$3@1$0@1$1@3$5^3^2^1@1$0@1$1^1"). Proof. intros h m st. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma c_mmap_counter_dequeue : ltac2:(zQ "80!jmd!ijf!j8!hgd!nb!mr2!mpf!t1>1h$6>1m$4>2st$7@3$2$3@1$0@1$1@3$5^3^2^1@1$0@1$1^1"). Proof. intros h m st. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma c_avail_meta_dequeue : ltac2:(zQ "80!jp2!ijf!j8!nb!mr2!mpf!t1!q9>1h$5>1m$3>2st$6@3$2$7@1$0@1$1@3$4^3^2^1@1$0@1$1^1"). Proof. intros h m st. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma c_avail_meta_count_dequeue : ltac2:(zQ "80!jq1!ijf!j8!hgd!nb!mr2!mpf!t1>1h$6>1m$4>2st$7@3$2$3@1$0@1$1@3$5^3^2^1@1$0@1$1^1"). Proof. intros h m st. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma c_avail_meta_area_count_dequeue : ltac2:(zQ "80!jr7!ijf!j8!hgd!nb!mr2!mpf!t1>1h$6>1m$4>2st$7@3$2$3@1$0@1$1@3$5^3^2^1@1$0@1$1^1"). Proof. intros h m st. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma c_meta_alloc_shift_dequeue : ltac2:(zQ "80!jt2!ijf!j8!hgd!nb!mr2!mpf!t1>1h$6>1m$4>2st$7@3$2$3@1$0@1$1@3$5^3^2^1@1$0@1$1^1"). Proof. intros h m st. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma c_meta_area_head_dequeue : ltac2:(zQ "80!ju8!ijf!j8!nb!mr2!mpf!t1!q9>1h$5>1m$3>2st$6@3$2$7@1$0@1$1@3$4^3^2^1@1$0@1$1^1"). Proof. intros h m st. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma c_meta_area_tail_dequeue : ltac2:(zQ "80!jvc!ijf!j8!nb!mr2!mpf!t1!q9>1h$5>1m$3>2st$6@3$2$7@1$0@1$1@3$4^3^2^1@1$0@1$1^1"). Proof. intros h m st. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma c_avail_meta_areas_dequeue : ltac2:(zQ "80!kh0!ijf!j8!nb!mr2!mpf!t1!q9>1h$5>1m$3>2st$6@3$2$7@1$0@1$1@3$4^3^2^1@1$0@1$1^1"). Proof. intros h m st. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma c_usage_dequeue : ltac2:(zQ "b0!hgd!kj1!ijf!j8!nb!mr2!mpf!t1!hm7!hr4!hjd>1h$6>1m$4>2st$7@3$3@4$9$0$a$8$0@1$1@1$2@3$5^3^2^1@1$1@1$2^1"). Proof. intros h m st. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma c_unmap_seq_dequeue : ltac2:(zQ "b0!hgd!kjb!ijf!j8!nb!mr2!mpf!t1!hm7!hr4!hjd>1h$6>1m$4>2st$7@3$3@4$9$0$a$8$0@1$1@1$2@3$5^3^2^1@1$1@1$2^1"). Proof. intros h m st. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma c_bounces_dequeue : ltac2:(zQ "b0!hgd!kk9!ijf!j8!nb!mr2!mpf!t1!hm7!hr4!hjd>1h$6>1m$4>2st$7@3$3@4$9$0$a$8$0@1$1@1$2@3$5^3^2^1@1$1@1$2^1"). Proof. intros h m st. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma c_seq_dequeue : ltac2:(zQ "80!kl5!ijf!j8!hgd!nb!mr2!mpf!t1>1h$6>1m$4>2st$7@3$2$3@1$0@1$1@3$5^3^2^1@1$0@1$1^1"). Proof. intros h m st. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma c_brk_dequeue : ltac2:(zQ "80!kld!ijf!j8!nb!km5!mr2!mpf!t1>1h$6>1m$3>2st$7@3$2$4@1$0@1$1@3$5^3^2^1@1$0@1$1^1"). Proof. intros h m st. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
#[export] Hint Rewrite s_regions_set_active s_shadow_set_active s_next_rid_set_active s_metas_set_active s_areas_set_active s_groups_set_active s_slots_set_active s_tick_set_active s_secret_set_active s_reserved_set_active s_regions_set_usage s_shadow_set_usage s_next_rid_set_usage s_metas_set_usage s_areas_set_usage s_groups_set_usage s_slots_set_usage s_tick_set_usage s_secret_set_usage s_reserved_set_usage s_regions_set_bounce s_shadow_set_bounce s_next_rid_set_bounce s_metas_set_bounce s_areas_set_bounce s_groups_set_bounce s_slots_set_bounce s_tick_set_bounce s_secret_set_bounce s_reserved_set_bounce s_ctx_put_meta s_regions_put_meta s_shadow_put_meta s_next_rid_put_meta s_areas_put_meta s_groups_put_meta s_slots_put_meta s_tick_put_meta s_secret_put_meta s_reserved_put_meta s_ctx_upd_meta s_regions_upd_meta s_shadow_upd_meta s_next_rid_upd_meta s_areas_upd_meta s_groups_upd_meta s_slots_upd_meta s_tick_upd_meta s_secret_upd_meta s_reserved_upd_meta s_ctx_put_group s_regions_put_group s_shadow_put_group s_next_rid_put_group s_metas_put_group s_areas_put_group s_slots_put_group s_tick_put_group s_secret_put_group s_reserved_put_group s_ctx_del_group s_regions_del_group s_shadow_del_group s_next_rid_del_group s_metas_del_group s_areas_del_group s_slots_del_group s_tick_del_group s_secret_del_group s_reserved_del_group s_ctx_set_group_active_idx s_regions_set_group_active_idx s_shadow_set_group_active_idx s_next_rid_set_group_active_idx s_metas_set_group_active_idx s_areas_set_group_active_idx s_slots_set_group_active_idx s_tick_set_group_active_idx s_secret_set_group_active_idx s_reserved_set_group_active_idx s_ctx_drop_region s_next_rid_drop_region s_metas_drop_region s_areas_drop_region s_groups_drop_region s_slots_drop_region s_tick_drop_region s_secret_drop_region s_reserved_drop_region s_ctx_upd_region s_shadow_upd_region s_next_rid_upd_region s_metas_upd_region s_areas_upd_region s_groups_upd_region s_slots_upd_region s_tick_upd_region s_secret_upd_region s_reserved_upd_region s_ctx_add_slots s_regions_add_slots s_shadow_add_slots s_next_rid_add_slots s_metas_add_slots s_areas_add_slots s_groups_add_slots s_tick_add_slots s_secret_add_slots s_reserved_add_slots s_ctx_del_slots s_regions_del_slots s_shadow_del_slots s_next_rid_del_slots s_metas_del_slots s_areas_del_slots s_groups_del_slots s_tick_del_slots s_secret_del_slots s_reserved_del_slots s_ctx_upd_shadow s_regions_upd_shadow s_next_rid_upd_shadow s_metas_upd_shadow s_areas_upd_shadow s_groups_upd_shadow s_slots_upd_shadow s_tick_upd_shadow s_secret_upd_shadow s_reserved_upd_shadow s_ctx_wr8 s_regions_wr8 s_next_rid_wr8 s_metas_wr8 s_areas_wr8 s_groups_wr8 s_slots_wr8 s_tick_wr8 s_secret_wr8 s_reserved_wr8 s_ctx_wr16 s_regions_wr16 s_next_rid_wr16 s_metas_wr16 s_areas_wr16 s_groups_wr16 s_slots_wr16 s_tick_wr16 s_secret_wr16 s_reserved_wr16 s_ctx_wr32 s_regions_wr32 s_next_rid_wr32 s_metas_wr32 s_areas_wr32 s_groups_wr32 s_slots_wr32 s_tick_wr32 s_secret_wr32 s_reserved_wr32 s_ctx_havoc s_regions_havoc s_next_rid_havoc s_metas_havoc s_areas_havoc s_groups_havoc s_slots_havoc s_tick_havoc s_secret_havoc s_reserved_havoc s_ctx_hdr_havoc s_regions_hdr_havoc s_next_rid_hdr_havoc s_metas_hdr_havoc s_areas_hdr_havoc s_groups_hdr_havoc s_slots_hdr_havoc s_tick_hdr_havoc s_secret_hdr_havoc s_reserved_hdr_havoc s_regions_step_seq s_shadow_step_seq s_next_rid_step_seq s_metas_step_seq s_areas_step_seq s_groups_step_seq s_slots_step_seq s_tick_step_seq s_secret_step_seq s_reserved_step_seq s_regions_record_seq s_shadow_record_seq s_next_rid_record_seq s_metas_record_seq s_areas_record_seq s_groups_record_seq s_slots_record_seq s_tick_record_seq s_secret_record_seq s_reserved_record_seq s_regions_account_bounce s_shadow_account_bounce s_next_rid_account_bounce s_metas_account_bounce s_areas_account_bounce s_groups_account_bounce s_slots_account_bounce s_tick_account_bounce s_secret_account_bounce s_reserved_account_bounce s_regions_decay_bounces s_shadow_decay_bounces s_next_rid_decay_bounces s_metas_decay_bounces s_areas_decay_bounces s_groups_decay_bounces s_slots_decay_bounces s_tick_decay_bounces s_secret_decay_bounces s_reserved_decay_bounces s_regions_set_head s_shadow_set_head s_next_rid_set_head s_metas_set_head s_areas_set_head s_groups_set_head s_slots_set_head s_tick_set_head s_secret_set_head s_reserved_set_head s_regions_dequeue s_shadow_dequeue s_next_rid_dequeue s_areas_dequeue s_groups_dequeue s_slots_dequeue s_tick_dequeue s_secret_dequeue s_reserved_dequeue s_ctx_set_size s_regions_set_size s_next_rid_set_size s_metas_set_size s_areas_set_size s_groups_set_size s_slots_set_size s_tick_set_size s_secret_set_size s_reserved_set_size c_secret_set_active c_init_done_set_active c_mmap_counter_set_active c_free_meta_head_set_active c_avail_meta_set_active c_avail_meta_count_set_active c_avail_meta_area_count_set_active c_meta_alloc_shift_set_active c_meta_area_head_set_active c_meta_area_tail_set_active c_avail_meta_areas_set_active c_usage_set_active c_unmap_seq_set_active c_bounces_set_active c_seq_set_active c_brk_set_active c_secret_set_usage c_init_done_set_usage c_mmap_counter_set_usage c_free_meta_head_set_usage c_avail_meta_set_usage c_avail_meta_count_set_usage c_avail_meta_area_count_set_usage c_meta_alloc_shift_set_usage c_meta_area_head_set_usage c_meta_area_tail_set_usage c_avail_meta_areas_set_usage c_active_set_usage c_unmap_seq_set_usage c_bounces_set_usage c_seq_set_usage c_brk_set_usage c_secret_set_bounce c_init_done_set_bounce c_mmap_counter_set_bounce c_free_meta_head_set_bounce c_avail_meta_set_bounce c_avail_meta_count_set_bounce c_avail_meta_area_count_set_bounce c_meta_alloc_shift_set_bounce c_meta_area_head_set_bounce c_meta_area_tail_set_bounce c_avail_meta_areas_set_bounce c_active_set_bounce c_usage_set_bounce c_unmap_seq_set_bounce c_seq_set_bounce c_brk_set_bounce c_secret_step_seq c_init_done_step_seq c_mmap_counter_step_seq c_free_meta_head_step_seq c_avail_meta_step_seq c_avail_meta_count_step_seq c_avail_meta_area_count_step_seq c_meta_alloc_shift_step_seq c_meta_area_head_step_seq c_meta_area_tail_step_seq c_avail_meta_areas_step_seq c_active_step_seq c_usage_step_seq c_bounces_step_seq c_brk_step_seq c_secret_record_seq c_init_done_record_seq c_mmap_counter_record_seq c_free_meta_head_record_seq c_avail_meta_record_seq c_avail_meta_count_record_seq c_avail_meta_area_count_record_seq c_meta_alloc_shift_record_seq c_meta_area_head_record_seq c_meta_area_tail_record_seq c_avail_meta_areas_record_seq c_active_record_seq c_usage_record_seq c_bounces_record_seq c_seq_record_seq c_brk_record_seq c_secret_account_bounce c_init_done_account_bounce c_mmap_counter_account_bounce c_free_meta_head_account_bounce c_avail_meta_account_bounce c_avail_meta_count_account_bounce c_avail_meta_area_count_account_bounce c_meta_alloc_shift_account_bounce c_meta_area_head_account_bounce c_meta_area_tail_account_bounce c_avail_meta_areas_account_bounce c_active_account_bounce c_usage_account_bounce c_unmap_seq_account_bounce c_seq_account_bounce c_brk_account_bounce c_secret_decay_bounces c_init_done_decay_bounces c_mmap_counter_decay_bounces c_free_meta_head_decay_bounces c_avail_meta_decay_bounces c_avail_meta_count_decay_bounces c_avail_meta_area_count_decay_bounces c_meta_alloc_shift_decay_bounces c_meta_area_head_decay_bounces c_meta_area_tail_decay_bounces c_avail_meta_areas_decay_bounces c_active_decay_bounces c_usage_decay_bounces c_unmap_seq_decay_bounces c_seq_decay_bounces c_brk_decay_bounces c_secret_dequeue c_init_done_dequeue c_mmap_counter_dequeue c_avail_meta_dequeue c_avail_meta_count_dequeue c_avail_meta_area_count_dequeue c_meta_alloc_shift_dequeue c_meta_area_head_dequeue c_meta_area_tail_dequeue c_avail_meta_areas_dequeue c_usage_dequeue c_unmap_seq_dequeue c_bounces_dequeue c_seq_dequeue c_brk_dequeue : mst.

(* [comment removed for export] *)
Lemma strip_fields : ltac2:(zQ "he0!hgd!hg9!j8!ms7!hi2!msf!hjd!nb!hl8!hr4!hm7!hn6!hp9!ir4!io7!ijf!ip8!hrc!ina!il1!ise!is3!iqa!itb!ip1!iq3!ij8!rb!t1!ild>2st$hc@2$5@3$2$ha@1$f@1$3^1@1$f^1@2$5@3$2@4$9$1$4$8$hd@1$h3@1$3^1@1$h3^1@2$5@3$2$1@1$h2@1$3^1@1$h2^1@2$5@3$2@4$9$7@4$c$1$4$0$6@6$b$1$4$8$0$6$a$hb@1$h1@1$3^1@1$h1^1@2$5@3$2@4$9$7@4$c$1$4$0$6@6$b$1$4$8$0$6$a$h8@1$e@1$3^1@1$e^1@2$5@3$2@4$9$7@4$c$1$4$0$6@6$b$1$4$8$0$6$a$h9@1$h0@1$3^1@1$h0^1@2$5@3$2@4$9$7@4$c$1$4$0$6@6$b$1$4$8$0$6$a@2$d$7$0@1$h6@1$3^1@1$h6^1@2$5@3$2$0@1$h5@1$3^1@1$h5^1@3$2@1$h7@2$d$0$0@1$h4@1$3^1@1$h4^1").
Proof. intros st. repeat split; reflexivity. Qed.

(* [comment removed for export] *)

Section LAYOUT_FIELDS.
  Ltac lay lem := intros; pose proof lem as H; cbn [strip] in H;
    match goal with |- ?F _ = _ => apply (f_equal F) in H; cbn in H; exact H end.
  Lemma s_ctx_zero_hdrs : ltac2:(zQ "80!hgd!ijf!mt5!j8!nb!ij8!t1!mta>1p$4>4size$0>1i$0>3cnt$2>2st$6@3$3$5@1$1@5$7^5^4^3^2^1@1$1^1"). Proof. intros p size i cnt st. lay (strip_zero_hdrs p size i cnt st). Qed.
  Lemma s_regions_zero_hdrs : ltac2:(zQ "c0!hgd!il1!mt5!j8!hg9!nb!t1!ild!mta!hl8!hr4!hi2>1p$5>4size$0>1i$0>3cnt$2>2st$6@3$3@4$a$4$b$9$7@1$1@5$8^5^4^3^2^1@1$1^1"). Proof. intros p size i cnt st. lay (strip_zero_hdrs p size i cnt st). Qed.
  Lemma s_next_rid_zero_hdrs : ltac2:(zQ "80!hgd!ina!mt5!j8!hg9!nb!t1!mta>1p$5>4size$0>1i$0>3cnt$2>2st$6@3$3$4@1$1@5$7^5^4^3^2^1@1$1^1"). Proof. intros p size i cnt st. lay (strip_zero_hdrs p size i cnt st). Qed.
  Lemma s_metas_zero_hdrs : ltac2:(zQ "h00!hgd!hg9!nb!hrc!hi2!hjd!mt5!j8!rb!t1!mta!hl8!hm7!hn6!hp9!hr4>1p$2>4size$0>1i$0>3cnt$6>2st$9@3$7@4$f$2@4$e$1$4$0$5@6$d$1$4$b$0$5$c$8@1$3@5$a^5^4^3^2^1@1$3^1"). Proof. intros p size i cnt st. lay (strip_zero_hdrs p size i cnt st). Qed.
  Lemma s_areas_zero_hdrs : ltac2:(zQ "h00!hgd!hg9!nb!io7!hi2!hjd!mt5!j8!ip1!t1!mta!hl8!hm7!hn6!hp9!hr4>1p$2>4size$0>1i$0>3cnt$6>2st$9@3$7@4$f$2@4$e$1$4$0$5@6$d$1$4$b$0$5$c$8@1$3@5$a^5^4^3^2^1@1$3^1"). Proof. intros p size i cnt st. lay (strip_zero_hdrs p size i cnt st). Qed.
  Lemma s_groups_zero_hdrs : ltac2:(zQ "h00!hgd!hg9!nb!ip8!hi2!hjd!mt5!j8!iq3!t1!mta!hl8!hm7!hn6!hp9!hr4>1p$2>4size$0>1i$0>3cnt$6>2st$9@3$7@4$f$2@4$e$1$4$0$5@6$d$1$4$b$0$5$c$8@1$3@5$a^5^4^3^2^1@1$3^1"). Proof. intros p size i cnt st. lay (strip_zero_hdrs p size i cnt st). Qed.
  Lemma s_slots_zero_hdrs : ltac2:(zQ "h00!hgd!nb!hg9!iqa!hi2!hjd!mt5!ir4!j8!t1!mta!hl8!hm7!hn6!hp9!hr4>1p$1>4size$0>1i$0>3cnt$6>2st$9@3$8@4$f$1@4$e$2$4$0$5@6$d$2$4$b$0$5$c@2$7$1$0@1$3@5$a^5^4^3^2^1@1$3^1"). Proof. intros p size i cnt st. lay (strip_zero_hdrs p size i cnt st). Qed.
  Lemma s_secret_zero_hdrs : ltac2:(zQ "70!hgd!is3!mt5!j8!nb!t1!mta>1p$4>4size$0>1i$0>3cnt$2>2st$5@3$3$0@1$1@5$6^5^4^3^2^1@1$1^1"). Proof. intros p size i cnt st. lay (strip_zero_hdrs p size i cnt st). Qed.
  Lemma s_reserved_zero_hdrs : ltac2:(zQ "90!hgd!ise!itb!mt5!ir4!j8!nb!t1!mta>1p$6>4size$0>1i$0>3cnt$3>2st$7@3$5@1$2@2$4$0$0@1$1@5$8^5^4^3^2^1@1$1^1"). Proof. intros p size i cnt st. lay (strip_zero_hdrs p size i cnt st). Qed.
  Lemma s_tick_zero_hdrs : ltac2:(zQ "80!hgd!ira!mt5!j8!hg9!nb!t1!mta>1p$5>4size$0>1i$0>3cnt$2>2st$6@3$3$4@1$1@5$7^5^4^3^2^1@1$1^1").
  Proof. intros p size i cnt st. revert i st; induction cnt; intros; cbn [zero_hdrs]; [reflexivity|]. rewrite IHcnt. reflexivity. Qed.

  Lemma s_ctx_enframe_at : ltac2:(zQ "80!hgd!nb!t1!ijf!mu6!j8!mub!ij8>2st$2>1g$1>3idx$0>1n$0>3off$0@3$5$7@1$3@3$4$2$1@5$6^5^4^3^2^1@1$3^5"). Proof. intros st g idx n off. lay (strip_enframe_at st g idx n off). Qed.
  Lemma s_regions_enframe_at : ltac2:(zQ "c0!hgd!nb!t1!il1!mu6!j8!hg9!mub!ild!hl8!hr4!hi2>2st$2>1g$1>3idx$0>1n$0>3off$0@3$5@4$a$6$b$9$8@1$3@3$4$2$1@5$7^5^4^3^2^1@1$3^5"). Proof. intros st g idx n off. lay (strip_enframe_at st g idx n off). Qed.
  Lemma s_next_rid_enframe_at : ltac2:(zQ "80!hgd!nb!t1!ina!mu6!j8!hg9!mub>2st$2>1g$1>3idx$0>1n$0>3off$0@3$5$6@1$3@3$4$2$1@5$7^5^4^3^2^1@1$3^5"). Proof. intros st g idx n off. lay (strip_enframe_at st g idx n off). Qed.
  Lemma s_metas_enframe_at : ltac2:(zQ "h00!hgd!nb!hg9!t1!hrc!hi2!hjd!mu6!j8!mub!rb!hl8!hm7!hn6!hp9!hr4>2st$3>1g$1>3idx$0>1n$0>3off$0@3$8@4$f$1@4$e$2$5$0$6@6$d$2$5$b$0$6$c$a@1$4@3$7$3$1@5$9^5^4^3^2^1@1$4^5"). Proof. intros st g idx n off. lay (strip_enframe_at st g idx n off). Qed.
  Lemma s_areas_enframe_at : ltac2:(zQ "h00!hgd!nb!hg9!t1!io7!hi2!hjd!mu6!j8!ip1!mub!hl8!hm7!hn6!hp9!hr4>2st$3>1g$1>3idx$0>1n$0>3off$0@3$8@4$f$1@4$e$2$5$0$6@6$d$2$5$b$0$6$c$9@1$4@3$7$3$1@5$a^5^4^3^2^1@1$4^5"). Proof. intros st g idx n off. lay (strip_enframe_at st g idx n off). Qed.
  Lemma s_groups_enframe_at : ltac2:(zQ "h00!hgd!nb!hg9!t1!ip8!hi2!hjd!mu6!j8!mub!iq3!hl8!hm7!hn6!hp9!hr4>2st$3>1g$1>3idx$0>1n$0>3off$0@3$8@4$f$1@4$e$2$5$0$6@6$d$2$5$b$0$6$c$a@1$4@3$7$3$1@5$9^5^4^3^2^1@1$4^5"). Proof. intros st g idx n off. lay (strip_enframe_at st g idx n off). Qed.
  Lemma s_slots_enframe_at : ltac2:(zQ "h00!hgd!nb!hg9!t1!iqa!hi2!hjd!mu6!ir4!j8!mub!hl8!hm7!hn6!hp9!hr4>2st$3>1g$1>3idx$0>1n$0>3off$0@3$9@4$f$1@4$e$2$5$0$6@6$d$2$5$b$0$6$c@2$8$1$0@1$4@3$7$3$1@5$a^5^4^3^2^1@1$4^5"). Proof. intros st g idx n off. lay (strip_enframe_at st g idx n off). Qed.
  Lemma s_secret_enframe_at : ltac2:(zQ "70!hgd!nb!t1!is3!mu6!j8!mub>2st$2>1g$1>3idx$0>1n$0>3off$0@3$5$0@1$3@3$4$2$1@5$6^5^4^3^2^1@1$3^5"). Proof. intros st g idx n off. lay (strip_enframe_at st g idx n off). Qed.
  Lemma s_reserved_enframe_at : ltac2:(zQ "90!hgd!nb!t1!ise!mu6!itb!ir4!j8!mub>2st$2>1g$1>3idx$0>1n$0>3off$0@3$7@1$5@2$6$0$0@1$3@3$4$2$1@5$8^5^4^3^2^1@1$3^5"). Proof. intros st g idx n off. lay (strip_enframe_at st g idx n off). Qed.
  Lemma s_tick_enframe_at : ltac2:(zQ "80!hgd!nb!t1!ira!mu6!j8!hg9!mub>2st$2>1g$1>3idx$0>1n$0>3off$0@3$5$6@1$3@3$4$2$1@5$7^5^4^3^2^1@1$3^5").
  Proof. intros st g idx n off. unfold enframe_at. destruct (negb (off =? 0)); cbn -[set_size wr8 wr16 Z.add Z.sub Z.mul Z.div get_stride];
    unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.

  Lemma s_ctx_nest_layout : ltac2:(zQ "70!hgd!ijf!j8!nb!ij8!t1!mv8>2st$5>1g$3>3idx$0>1j$0>4size$0>3cnt$0@3$2$4@1$1@6$6^6^5^4^3^2^1@1$1^6"). Proof. intros st g idx j size cnt. lay (strip_nest_layout st g idx j size cnt). Qed.
  Lemma s_regions_nest_layout : ltac2:(zQ "b0!hgd!il1!j8!hg9!nb!t1!mv8!ild!hl8!hr4!hi2>2st$5>1g$4>3idx$0>1j$0>4size$0>3cnt$0@3$2@4$9$3$a$8$7@1$1@6$6^6^5^4^3^2^1@1$1^6"). Proof. intros st g idx j size cnt. lay (strip_nest_layout st g idx j size cnt). Qed.
  Lemma s_next_rid_nest_layout : ltac2:(zQ "70!hgd!ina!j8!hg9!nb!t1!mv8>2st$5>1g$4>3idx$0>1j$0>4size$0>3cnt$0@3$2$3@1$1@6$6^6^5^4^3^2^1@1$1^6"). Proof. intros st g idx j size cnt. lay (strip_nest_layout st g idx j size cnt). Qed.
  Lemma s_metas_nest_layout : ltac2:(zQ "f0!hgd!hg9!nb!hrc!hi2!hjd!j8!rb!t1!mv8!hl8!hm7!hn6!hp9!hr4>2st$8>1g$2>3idx$0>1j$0>4size$0>3cnt$0@3$6@4$e$2@4$d$1$4$0$5@6$c$1$4$a$0$5$b$7@1$3@6$9^6^5^4^3^2^1@1$3^6"). Proof. intros st g idx j size cnt. lay (strip_nest_layout st g idx j size cnt). Qed.
  Lemma s_areas_nest_layout : ltac2:(zQ "f0!hgd!hg9!nb!io7!hi2!hjd!j8!ip1!t1!mv8!hl8!hm7!hn6!hp9!hr4>2st$8>1g$2>3idx$0>1j$0>4size$0>3cnt$0@3$6@4$e$2@4$d$1$4$0$5@6$c$1$4$a$0$5$b$7@1$3@6$9^6^5^4^3^2^1@1$3^6"). Proof. intros st g idx j size cnt. lay (strip_nest_layout st g idx j size cnt). Qed.
  Lemma s_groups_nest_layout : ltac2:(zQ "f0!hgd!hg9!nb!ip8!hi2!hjd!j8!iq3!t1!mv8!hl8!hm7!hn6!hp9!hr4>2st$8>1g$2>3idx$0>1j$0>4size$0>3cnt$0@3$6@4$e$2@4$d$1$4$0$5@6$c$1$4$a$0$5$b$7@1$3@6$9^6^5^4^3^2^1@1$3^6"). Proof. intros st g idx j size cnt. lay (strip_nest_layout st g idx j size cnt). Qed.
  Lemma s_slots_nest_layout : ltac2:(zQ "f0!hgd!nb!hg9!iqa!hi2!hjd!ir4!j8!t1!mv8!hl8!hm7!hn6!hp9!hr4>2st$8>1g$1>3idx$0>1j$0>4size$0>3cnt$0@3$7@4$e$1@4$d$2$4$0$5@6$c$2$4$a$0$5$b@2$6$1$0@1$3@6$9^6^5^4^3^2^1@1$3^6"). Proof. intros st g idx j size cnt. lay (strip_nest_layout st g idx j size cnt). Qed.
  Lemma s_secret_nest_layout : ltac2:(zQ "60!hgd!is3!j8!nb!t1!mv8>2st$4>1g$3>3idx$0>1j$0>4size$0>3cnt$0@3$2$0@1$1@6$5^6^5^4^3^2^1@1$1^6"). Proof. intros st g idx j size cnt. lay (strip_nest_layout st g idx j size cnt). Qed.
  Lemma s_reserved_nest_layout : ltac2:(zQ "80!hgd!ise!itb!ir4!j8!nb!t1!mv8>2st$6>1g$5>3idx$0>1j$0>4size$0>3cnt$0@3$4@1$2@2$3$0$0@1$1@6$7^6^5^4^3^2^1@1$1^6"). Proof. intros st g idx j size cnt. lay (strip_nest_layout st g idx j size cnt). Qed.
  Lemma s_tick_nest_layout : ltac2:(zQ "70!hgd!ira!j8!hg9!nb!t1!mv8>2st$5>1g$4>3idx$0>1j$0>4size$0>3cnt$0@3$2$3@1$1@6$6^6^5^4^3^2^1@1$1^6").
  Proof. intros st g idx j size cnt. unfold nest_layout. destruct (enframe_at st g idx _ 0) as [st1 p] eqn:E.
    rewrite s_tick_zero_hdrs. cbn. pose proof (s_tick_enframe_at st g idx (UNIT * size_class j - IB) 0) as H. rewrite E in H. exact H. Qed.
End LAYOUT_FIELDS.
#[export] Hint Rewrite s_ctx_zero_hdrs s_regions_zero_hdrs s_next_rid_zero_hdrs s_metas_zero_hdrs s_areas_zero_hdrs s_groups_zero_hdrs s_slots_zero_hdrs s_secret_zero_hdrs s_reserved_zero_hdrs s_tick_zero_hdrs
  s_ctx_enframe_at s_regions_enframe_at s_next_rid_enframe_at s_metas_enframe_at s_areas_enframe_at s_groups_enframe_at s_slots_enframe_at s_secret_enframe_at s_reserved_enframe_at s_tick_enframe_at
  s_ctx_nest_layout s_regions_nest_layout s_next_rid_nest_layout s_metas_nest_layout s_areas_nest_layout s_groups_nest_layout s_slots_nest_layout s_secret_nest_layout s_reserved_nest_layout s_tick_nest_layout : mst.

(* [comment removed for export] *)
Lemma s_regions_new_region : ltac2:(zQ "h10!hg9!ild!hl8!hi2!hr4!hgd!t1!il1!mu6!j8!ng6!nh1!nhe!ina!ht2!huc!hva>1k$c>1b$5>1l$5>2st$6@3$9@4$4$0$3$2$1@1$7@3$8$6$0@4$b^4^3^2^1@7$e$0$1@4$4$0$3$2$1@4$f$0$1@4$4$0$3$2$1@4$h0$0$3$2$1@1$d^1@3$a^4^3^2@1$7^1").
Proof. intros k b l st. reflexivity. Qed.
Lemma s_next_rid_new_region : ltac2:(zQ "90!hg9!hgd!t1!ina!mu6!j8!nh1!nhe!nje>1k$7>1b$1>1l$1>2st$2@3$5$0@1$3@3$4$2$0@4$6^4^3^2^1@1$8@1$3^1").
Proof. intros k b l st. reflexivity. Qed.
Lemma snd_new_region : ltac2:(zQ "80!hg9!hgd!t1!nk6!j8!nh1!nhe!ina>1k$6>1b$1>1l$1>2st$2@3$4$0@3$3$2$0@4$5^4^3^2^1@1$7^1").
Proof. intros k b l st. reflexivity. Qed.
Lemma s_regions_drop_region : ltac2:(zQ "c0!hg9!ild!hl8!hi2!hr4!il1!j8!lve!t1!nkb!nl5!hva>3rid$0>2st$8@3$6@4$4$0$3$2$1@1$5@2$7^2^1@5$9$0@4$4$0$3$2$1@4$a$0$1@4$4$0$3$2$1@4$b$0$3$2$1^2@1$5^1").
Proof. intros rid st. reflexivity. Qed.
Lemma s_shadow_drop_region : ltac2:(zQ "c0!hg9!in1!hl8!hi2!hr4!im6!j8!lve!t1!nkb!nl5!hva>3rid$0>2st$8@3$6@4$4$0$3$2$1@1$5@2$7^2^1@5$9$0@4$4$0$3$2$1@4$a$0$1@4$4$0$3$2$1@4$b$0$3$2$1^2@1$5^1").
Proof. intros rid st. reflexivity. Qed.
Lemma s_groups_put_group : ltac2:(zQ "h51!hgd!hg9!hi2!hjd!nb!iq3!hl8!hm7!hn6!hp9!hr4!ip8!j8!nm3!t1!q9!lse!no4!ht2!huc!hva&@4$a$4@4$9$1$2$0$3@6$8$1$2$6$0$3$7$5>1g$4>2mo$f>2ai$0>2st$e@3$c~0@1$b@4$h0^4^3^2^1@7$h2$4$5~0@4$h3$4$5~0@4$h4$4@4$9$1$2$0$3@6$8$1$2$6$0$3$7$5^4@2$d^3@2$h1^2+hf@1$b^1").
Proof. intros g mo ai st. reflexivity. Qed.
Lemma s_groups_del_group : ltac2:(zQ "h21!hg9!hgd!hi2!hjd!nb!iq3!hl8!hm7!hn6!hp9!hr4!ip8!j8!lta!t1!nkb!nl5!hva&@4$a$4@4$9$0$2$1$3@6$8$0$2$6$1$3$7$5>1g$4>2st$e@3$c~0@1$b@2$d^2^1@5$f$4~0@4$h0$4$5~0@4$h1$4@4$9$0$2$1$3@6$8$0$2$6$1$3$7$5^2@1$b^1").
Proof. intros g st. reflexivity. Qed.
Lemma s_shadow_upd_shadow : ltac2:(zQ "d0!in1!hg9!hl8!hi2!hr4!im6!j8!noc!t1!mj1!ht2!huc!hva>3rid$1>1f>0$0$0>2st$8@3$6@4$4$1$3$2$0@1$5@3$9^3^2^1@7$a$1$0@4$4$1$3$2$0@4$b$1$0@4$4$1$3$2$0@4$c$1$3$2$0^3@1^2@2$7^1^3@1$5^1").
Proof. intros rid f st. reflexivity. Qed.
#[export] Hint Rewrite s_regions_new_region s_next_rid_new_region snd_new_region s_regions_drop_region s_shadow_drop_region
  s_groups_put_group s_groups_del_group s_shadow_upd_shadow : mst.

(* [comment removed for export] *)
Lemma active_set_active : ltac2:(zQ "80!q9!h8!hgd!np9!j8!t1!lq8!nq2>2st$5>2sc$2>1v$0>3sc'$2@3$4$0@2$3@3$6^3^2^4^1M1\0$1$0@2$7^1^3^2@2$3^4^1").
Proof. intros st sc v sc'.
  unfold active, set_active, ctx; cbn. destruct (Z.eqb_spec sc' sc) as [->|NE].
  - destruct v; [rewrite lookup_insert_eq| rewrite lookup_delete_eq]; reflexivity.
  - destruct v; [rewrite lookup_insert_ne by congruence| rewrite lookup_delete_ne by congruence]; reflexivity.
Qed.
Lemma usage_set_usage : ltac2:(zQ "70!hgd!h8!nq9!j8!t1!lr5!nq2>2st$4>2sc$0>1v$0>3sc'$0@3$3$0@2$2@3$5^3^2^4^1M1\0$1$0@2$6^1^3^2@2$2^4^1").
Proof. intros st sc v sc'.
  unfold usage, set_usage, ctx; cbn. destruct (Z.eqb_spec sc' sc) as [->|NE];
  [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
Qed.
Lemma bounces_set_bounce : ltac2:(zQ "70!hgd!h8!nr1!j8!t1!ls1!nq2>2st$4>1i$0>1v$0>2i'$0@3$3$0@2$2@3$5^3^2^4^1M1\0$1$0@2$6^1^3^2@2$2^4^1").
Proof. intros st i v i'.
  unfold bounces, set_bounce, ctx; cbn. destruct (Z.eqb_spec i' i) as [->|NE];
  [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
Qed.
Lemma get_head_set_head : ltac2:(zQ "60!q9!j8!nrb!mpf!t1!mq7>2st$4>1h$3>1v$0@3$1$0@2$2@3$5^2^1^3^2^1").
Proof. intros st h v. destruct h; cbn; [rewrite active_set_active, Z.eqb_refl|]; reflexivity. Qed.
Lemma get_head_set_head_other : ltac2:(zQ "70!mpf!j8!nrb!q9!q3!t1!mq7>2st$5>1h$0>2h'$0>1v$3>0@1$4@3$1$0^2^3@3$1$3@2$2@3$6^4^2^5^3@2$2^5^3").
Proof. intros st h h' v.
  intros NE. destruct h as [sc|], h' as [sc'|]; cbn; try reflexivity; try congruence.
  rewrite active_set_active. destruct (Z.eqb_spec sc' sc); [congruence| reflexivity].
Qed.
Lemma active_upd_meta : ltac2:(zQ "80!np9!rb!j8!hgd!nb!t1!q9!u5>2st$5>1m$4>1f>0$1$1>2sc$3@3$2$6@2$0@3$7^3^2^4^1@2$0^4^1"). Proof. intros st m f sc. reflexivity. Qed.
Lemma active_put_meta : ltac2:(zQ "80!np9!j8!hgd!nb!rb!t1!q9!ta>2st$5>1m$3>1r$4>2sc$2@3$1$6@2$0@3$7^3^2^4^1@2$0^4^1"). Proof. intros st m r sc. reflexivity. Qed.
Lemma usage_upd_meta : ltac2:(zQ "70!hgd!rb!nq9!j8!nb!t1!u5>2st$5>1m$4>1f>0$1$1>2sc$0@3$3$0@2$2@3$6^3^2^4^1@2$2^4^1"). Proof. intros st m f sc. reflexivity. Qed.
Lemma get_head_upd_meta : ltac2:(zQ "80!nrb!rb!j8!nb!mpf!t1!q9!u5>2st$5>1m$3>1f>0$1$1>1h$4@3$2$6@2$0@3$7^3^2^4^1@2$0^4^1"). Proof. intros st m f h. destruct h; reflexivity. Qed.
Lemma get_head_put_meta : ltac2:(zQ "80!nrb!j8!nb!mpf!rb!t1!q9!ta>2st$5>1m$2>1r$4>1h$3@3$1$6@2$0@3$7^3^2^4^1@2$0^4^1"). Proof. intros st m r h. destruct h; reflexivity. Qed.
Lemma get_meta_rec_set_head : ltac2:(zQ "80!s2!j8!nb!mpf!rb!t1!q9!mq7>2st$5>1h$3>1v$6>1x$2@3$1$4@2$0@3$7^3^2^4^1@2$0^4^1"). Proof. intros st h v x. destruct h; reflexivity. Qed.
Lemma get_meta_rec_upd_ctx : ltac2:(zQ "70!s2!ij8!j8!nb!rb!t1!ik7>2st$5>1f>0$1$1>1x$3@3$2$4@2$0@2$6^2^3^1@2$0^3^1"). Proof. intros st f x. reflexivity. Qed.
#[export] Hint Rewrite active_set_active usage_set_usage bounces_set_bounce get_head_set_head
  active_upd_meta active_put_meta usage_upd_meta get_head_upd_meta get_head_put_meta get_meta_rec_set_head get_meta_rec_upd_ctx : mst.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lookup_new_region : ltac2:(zQ "h40!ild!hg9!hl8!hi2!h8!ih1!hgd!t1!il1!ih9!hr4!ii3!ij2!mu6!j8!ng6!nh1!nhe!ina!ns6>1k$h1>1b$6>1l$6>2st$7>3rid$1@3$e@1$5$0@6$9$1$0@4$a$1$3$2$0@4$b$1$3$2$0^1@1$8@3$d$7$1@4$h0^5^4^3^2M4\0$4@1$5$0@2$h3^1@1$h2^2@2$c$0@3$f^5^4^3@6$9$1$0@4$a$1$3$2$0@4$b$1$3$2$0^1@1$8^2").
Proof. intros k b l st rid.
  rewrite s_regions_new_region. destruct (N.eqb_spec rid (s_next_rid st)) as [->|NE];
  [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
Qed.
Lemma lookup_drop_region : ltac2:(zQ "f0!ild!hg9!hl8!hi2!h8!ih1!il1!ih9!hr4!ii3!nsd!j8!lve!t1!ns6>3rid$1>2st$d>4rid'$1@3$b@1$5$0@6$7$1$0@4$8$1$3$2$0@4$9$1$3$2$0^1@1$6@2$c^3^2M4\0$4@1$5$0@2$e^1^3@1$a$0@6$7$1$0@4$8$1$3$2$0@4$9$1$3$2$0^1@1$6^2").
Proof. intros rid st rid'.
  rewrite s_regions_drop_region. destruct (N.eqb_spec rid' rid) as [->|NE];
  [rewrite lookup_delete_eq| rewrite lookup_delete_ne by congruence]; reflexivity.
Qed.
Lemma lookup_upd_region : ltac2:(zQ "f0!ild!hg9!hl8!hi2!il1!ih9!hr4!ii3!h8!ih1!nt3!j8!t1!mgc!ns6>3rid$1>1f>0$0$0>2st$c>4rid'$1@3$b@1$9$0@6$5$1$0@4$6$1$3$2$0@4$7$1$3$2$0^1@1$4@3$d^4^3^2M8\0$8@1$9$0@2$e^1^4@4$a$0$0^3@6$5$1$0@4$6$1$3$2$0@4$7$1$3$2$0^4@1$4^2@6$5$1$0@4$6$1$3$2$0@4$7$1$3$2$0^1@1$4^2").
Proof. intros rid f st rid'.
  unfold upd_region, get_region. destruct (s_regions st !! rid) as [r|] eqn:E; cbn.
  - destruct (N.eqb_spec rid' rid) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; [reflexivity|reflexivity].
  - destruct (N.eqb_spec rid' rid) as [->|NE]; [rewrite E|]; reflexivity.
Qed.
Lemma conc_eq : ltac2:(zQ "h30!hg9!ild!hgd!j8!hl8!hi2!ij2!mu6!ih1!ir4!nk6!ntf!t1!nu6!il1!nuf!ih9!hr4!ii3>2st$c>1p@2$9$0$2>1r$1>0@3$3@1$8$1@6$h0$0$1@4$h1$0$5$4$1@4$h2$0$5$4$1@3$7$0$2^2@1$e^3@2$6$1^1@3$3$2@2$b^4^3@2$f@1$d^2@3$a$0$2^3").
Proof. intros st p r. intros H. unfold conc, get_region. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma Z_iter_ind {A} (f : A -> A) (P : Z -> A -> Prop) x :
  P 0 x -> (forall n a, 0 <= n -> P n a -> P (n + 1) (f a)) -> forall n, 0 <= n -> P n (Z.iter n f x).
Proof.
  intros H0 HS n Hn. rewrite iter_nat_of_Z by exact Hn.
  rewrite <- (Z2Nat.id n) at 1 by exact Hn. rewrite <- Zabs2Nat.abs_nat_nonneg by exact Hn.
  induction (Z.abs_nat n) as [|k IH]; [exact H0|].
  cbn [nat_rect]. rewrite Nat2Z.inj_succ, <- Z.add_1_r. apply HS; [lia| exact IH].
Qed.

(* [comment removed for export] *)
Lemma lookup_add_slots : ltac2:(zQ "i25!hgd!hg9!nb!ir4!nk6!nv6!hi2!hjd!nvd!hl8!hm7!hn6!hp9!og4!h8!mu6!ih1!iqa!oga!ih9!hr4!ii3!ij2!oh1!j8!mh9!t1!ns6!nq2!oh7!ohd!oi4!oia!oj1&@4$h4$2@4$c$1$6$0$7@6$b$1$6$9$0$7$a@2$3$2$0&@4$h5$2@4$c$1$6$0$7@6$b$1$6$9$0$7$a@2$3$2$0&@2$5@3$4$1$0^3@3$4$1$0^7&@2$5~2$8&@2$h2~3^6>1m$2>1p$2>6stride$0>3cnt$0>2st$ha>1s@2$3$1$0>0@2$hdZ^3>0@2$hfZ^5@3$h8@1$h0@2$3$2$0@6$h3@2$3$1$0@2$3$2$0~0~1^3@1$h1@5$h9^8^7^6^5^4Me\0$e@1$h0@2$3$2$0@2$d@2$d@2$d@2$hb@3$f$1$0^3@3$f$1$0^7@2$heZ~3@2$hc@2$i1~3^6Z@2$i0~4^5@2$h6@2$3$2$0@4$h7$2$0^8~4@6$h3@2$3$1$0@2$3$2$0~0~1^3@1$h1^4").
Proof. intros m p stride cnt st s.
  intros Hc Hs. unfold add_slots. cbn -[Z.iter Z.add Z.mul Z.sub Z.div Z.modulo Z.leb Z.ltb Z.eqb lookup insert].
  set (F := fun acc : Z * gmap aptr (aptr * Z) => let (i, tb) := acc in (i + 1, <[aadd p (UNIT + stride * i) := (m, i)]> tb)).
  assert (GEN : forall n, 0 <= n -> let r := Z.iter n F (0, s_slots st) in fst r = n /\
            snd r !! s = if (fst s =? fst p)%N && (0 <=? snd s - snd p - UNIT) && ((snd s - snd p - UNIT) mod stride =? 0) && ((snd s - snd p - UNIT) / stride <? n)
                         then Some (m, (snd s - snd p - UNIT) / stride) else s_slots st !! s).
  { intros n Hn. apply (Z_iter_ind F (fun n r => fst r = n /\ snd r !! s = (if (fst s =? fst p)%N && (0 <=? snd s - snd p - UNIT) && ((snd s - snd p - UNIT) mod stride =? 0) && ((snd s - snd p - UNIT) / stride <? n) then Some (m, (snd s - snd p - UNIT) / stride) else s_slots st !! s))); [| |exact Hn].
    - cbn. split; [reflexivity|]. destruct ((fst s =? fst p)%N && _ && _) eqn:E; [|reflexivity].
      destruct (Z.ltb_spec ((snd s - snd p - UNIT) / stride) 0); [|rewrite Bool.andb_false_r; reflexivity].
      exfalso. apply Bool.andb_true_iff in E as [E _]. apply Bool.andb_true_iff in E as [_ E]. apply Z.leb_le in E.
      pose proof (Z.div_pos (snd s - snd p - UNIT) stride E Hs). lia.
    - intros k [i tb] Hk [Hi IH]. cbn in Hi; subst i. unfold F. cbn [fst snd]. split; [reflexivity|].
      destruct (aptr_eqb_spec s (aadd p (UNIT + stride * k))) as [->|NE].
      + rewrite lookup_insert_eq. unfold aadd; cbn [fst snd]. rewrite N.eqb_refl.
        replace (snd p + (UNIT + stride * k) - snd p - UNIT) with (k * stride) by lia.
        rewrite Z_mod_mult, Z.div_mul, Z.eqb_refl by lia. cbn.
        destruct (Z.leb_spec 0 (k * stride)); [|nia]. destruct (Z.ltb_spec k (k + 1)); [|lia]. reflexivity.
      + rewrite lookup_insert_ne by congruence. rewrite IH.
        destruct ((fst s =? fst p)%N) eqn:E1; cbn; [|reflexivity].
        destruct (Z.leb_spec 0 (snd s - snd p - UNIT)); cbn; [|reflexivity].
        destruct (Z.eqb_spec ((snd s - snd p - UNIT) mod stride) 0); cbn; [|reflexivity].
        destruct (Z.ltb_spec ((snd s - snd p - UNIT) / stride) k), (Z.ltb_spec ((snd s - snd p - UNIT) / stride) (k + 1)); try reflexivity; try lia.
        exfalso. apply NE. apply N.eqb_eq in E1. unfold aadd. destruct s as [sr so], p as [pr po]; cbn in *. subst sr. f_equal.
        assert ((so - po - UNIT) / stride = k) by lia.
        pose proof (Z.div_mod (so - po - UNIT) stride ltac:(lia)). lia. }
  destruct (GEN cnt Hc) as [_ G]. exact G.
Qed.

Lemma lookup_del_slots : ltac2:(zQ "i14!hgd!hg9!nb!ir4!hi2!hjd!nk6!nv6!hl8!hm7!hn6!hp9!og4!nvd!h8!mu6!ih1!iqa!ih9!hr4!ii3!nsd!j8!mi5!t1!ns6!oga!nq2!oh7!ohd!oi4!oia!oj1&@4$h3$2@4$b$1$4$0$5@6$a$1$4$8$0$5$9@2$3$2$0&@4$h4$2@4$b$1$4$0$5@6$a$1$4$8$0$5$9@2$3$2$0&@2$7@3$6$1$0^3@3$6$1$0^7&@2$7~2$d>1p$2>6stride$0>3cnt$0>2st$h8>1s@2$3$1$0>0@2$hcZ^3>0@2$heZ^5@3$h6@1$h0@2$3$2$0@6$h2@2$3$1$0@2$3$2$0~0~1^3@1$h1@4$h7^7^6^5^4Me\0$e@1$h0@2$3$2$0@2$c@2$c@2$c@2$h9@3$f$1$0^3@3$f$1$0^7@2$hdZ~3@2$hb@2$i0~3^6Z@2$hf@2$ha~3^6^5@1$h5@2$3$2$0@6$h2@2$3$1$0@2$3$2$0~0~1^3@1$h1^4").
Proof. intros p stride cnt st s.
  intros Hc Hs. unfold del_slots. cbn -[Z.iter Z.add Z.mul Z.sub Z.div Z.modulo Z.leb Z.ltb Z.eqb lookup delete].
  set (F := fun acc : Z * gmap aptr (aptr * Z) => let (i, tb) := acc in (i + 1, delete (aadd p (UNIT + stride * i)) tb)).
  assert (GEN : forall n, 0 <= n -> let r := Z.iter n F (0, s_slots st) in fst r = n /\
            snd r !! s = if (fst s =? fst p)%N && (0 <=? snd s - snd p - UNIT) && ((snd s - snd p - UNIT) mod stride =? 0) && ((snd s - snd p - UNIT) / stride <? n)
                         then None else s_slots st !! s).
  { intros n Hn. apply (Z_iter_ind F (fun n r => fst r = n /\ snd r !! s = (if (fst s =? fst p)%N && (0 <=? snd s - snd p - UNIT) && ((snd s - snd p - UNIT) mod stride =? 0) && ((snd s - snd p - UNIT) / stride <? n) then None else s_slots st !! s))); [| |exact Hn].
    - cbn. split; [reflexivity|]. destruct ((fst s =? fst p)%N && _ && _) eqn:E; [|reflexivity].
      destruct (Z.ltb_spec ((snd s - snd p - UNIT) / stride) 0); [|rewrite Bool.andb_false_r; reflexivity].
      exfalso. apply Bool.andb_true_iff in E as [E _]. apply Bool.andb_true_iff in E as [_ E]. apply Z.leb_le in E.
      pose proof (Z.div_pos (snd s - snd p - UNIT) stride E Hs). lia.
    - intros k [i tb] Hk [Hi IH]. cbn in Hi; subst i. unfold F. cbn [fst snd]. split; [reflexivity|].
      destruct (aptr_eqb_spec s (aadd p (UNIT + stride * k))) as [->|NE].
      + rewrite lookup_delete_eq. unfold aadd; cbn [fst snd]. rewrite N.eqb_refl.
        replace (snd p + (UNIT + stride * k) - snd p - UNIT) with (k * stride) by lia.
        rewrite Z_mod_mult, Z.div_mul, Z.eqb_refl by lia. cbn.
        destruct (Z.leb_spec 0 (k * stride)); [|nia]. destruct (Z.ltb_spec k (k + 1)); [|lia]. reflexivity.
      + rewrite lookup_delete_ne by congruence. rewrite IH.
        destruct ((fst s =? fst p)%N) eqn:E1; cbn; [|reflexivity].
        destruct (Z.leb_spec 0 (snd s - snd p - UNIT)); cbn; [|reflexivity].
        destruct (Z.eqb_spec ((snd s - snd p - UNIT) mod stride) 0); cbn; [|reflexivity].
        destruct (Z.ltb_spec ((snd s - snd p - UNIT) / stride) k), (Z.ltb_spec ((snd s - snd p - UNIT) / stride) (k + 1)); try reflexivity; try lia.
        exfalso. apply NE. apply N.eqb_eq in E1. unfold aadd. destruct s as [sr so], p as [pr po]; cbn in *. subst sr. f_equal.
        assert ((so - po - UNIT) / stride = k) by lia.
        pose proof (Z.div_mod (so - po - UNIT) stride ltac:(lia)). lia. }
  destruct (GEN cnt Hc) as [_ G]. exact G.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma get_shadow_ext : ltac2:(zQ "90!j8!hg9!noc!t1!im6!in1!hl8!hr4!hi2>2st$3>3st'$3>3rid$1>0@3$0@4$7$1$8$6$5@1$4^2@1$4^3@3$0$5@2$2^3^2@2$2^4^2").
Proof. intros st st' rid. intros H. unfold get_shadow. rewrite H. reflexivity. Qed.
Lemma get_shadow_upd_shadow : ltac2:(zQ "80!in1!noc!h8!hg9!j8!t1!mj1!ns6>3rid$3>1f>0$0$0>2st$5>4rid'$3@3$4$0@2$1@3$6^4^3^2^1M2\0$2$0@2$7^1^4@1^3@2$1^2^4@2$1^2^1").
Proof. intros rid f st rid'.
  unfold get_shadow, upd_shadow; cbn. destruct (N.eqb_spec rid' rid) as [->|NE];
  [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma cell_read_wr8 : ltac2:(zQ "i50!hgd!hg9!ir4!itb!nk6!h8!hm7!hjd!mu6!ojb!noc!ij2!ok5!ira!oga!no4!ih9!hr4!ii3!ol1!ol5!ih1!ola!j8!olf!om7!nb!o2!t1!on1!on9!in1!oo2!ooa!mje!oj1!oq3>1p$ha>1v$0>2st$hc>1q@2$2$1$0@3$h7$9@2$c@2$a@3$i2^4^3^2@3$8$1$0^1@3$4$1$0^1M5\0$5$9@2$hb^1^4=1r$hf@2$a^2@3$8$1$0^4=2hl@1$3@2$2$0$1@5$i4@1$3@2$2$0$1@1$3@2$2$0$1@1$h3@1$3@2$2$0$1@1$h4@2$2$0$1@6$h0$0@1$3@2$2$0$1@4$h1$0$7$6@1$3@2$2$0$1@4$h2$0$7$6@1$3@2$2$0$1@2$e@3$4$1$0^5+h0@1$hd^1=2hp@1$h5$1@6$h0$0$1@4$h1$0$7$6$1@4$h2$0$7$6$1@2$e@3$4$1$0^6+hgg0@1$he^2M5\0$5$9@2$h6@2$i1^1@2$b$1@1$d^5@3$i0^2@2$i3@3$4$1$0^7+h0@2$b$1@1$d^5@1$h9@2$f^6+vf@1$h8@2$f^6+vf@2$c@2$a^2@3$8$1$0^1@3$4$1$0^1").
Proof. intros p v st q.
  unfold wr8. rewrite get_shadow_upd_shadow. destruct (aptr_eqb_spec q p) as [->|NE].
  - rewrite N.eqb_refl. unfold cell_read; cbn. rewrite lookup_insert_eq. reflexivity.
  - destruct (N.eqb_spec (fst q) (fst p)) as [E|NE2]; [|reflexivity].
    unfold cell_read; cbn. rewrite E. rewrite lookup_insert_ne; [reflexivity|].
    intros E2. apply NE. destruct q, p; cbn in *; congruence.
Qed.

(* [comment removed for export] *)
Definition sh_ticks : ltac2:(zQ "20!hg9!in1>1r$1>1t$0P") := ltac2:(zQ "h30!hgd!hg9!ir4!itb!hm7!hjd!ij2!ih1!j8!or2!ih9!hr4!ii3!nk6!msf!on1!on9!in1!osb\1r$h1\1t$1@2$e>1u$0>2hl@1$3@2$2$0$1>2ch@2$2$0$1>0@3$8@1$7@1$3@2$2$0$1@6$a$0@1$3@2$2$0$1@4$b$0$5$4@1$3@2$2$0$1@4$c$0$5$4@1$3@2$2$0$1^3@1$f^5@2$6@1$3@2$2$0$1^2>0@3$h2@2$2$0$1^2^3@2$9@3$d$0$1^3^6>2pg$0>2t'$1>0@3$8@1$7$1@6$a$0$1@4$b$0$5$4$1@4$c$0$5$4$1^2@1$h0^4@2$6$1^1@2$9^2^4").

Lemma not_stale_cur : ltac2:(zQ "h70!hgd!hg9!ir4!itb!hm7!hjd!ij2!ih9!hr4!ii3!h8!pc!ol1!ol5!ola!j8!pgf!on1!on9!in1!oo2!ooa!oq3>1r$h3>1t$1>1b$0>0@2$h0^3^2>1u$0>2pg$0@3$f$a@2$e@2$h5@6$7$0$1@4$8$0$5$4$1@4$9$0$5$4$1^1@1$h2^6@2$6$1^5@3$h4@5$h6@1$3@2$2$0$1@1$3@2$2$0$1@1$c@1$3@2$2$0$1@1$d@2$2$0$1@6$7$0@1$3@2$2$0$1@4$8$0$5$4@1$3@2$2$0$1@4$9$0$5$4@1$3@2$2$0$1^2@1$h1^6^4@2$6$1^5$b").
Proof. intros r t b.
  intros [Hh Hp] u pg. apply Bool.orb_false_iff. split.
  - destruct (r_havp r !! pg) as [t'|] eqn:E; cbn; [|reflexivity]. apply N.ltb_ge. eapply Hp; eauto.
  - unfold stale. apply Bool.not_true_iff_false. rewrite existsb_exists. intros ([c h] & Hin & Hb). cbn in Hb.
    apply Bool.andb_true_iff in Hb as [_ Hb]. apply N.ltb_lt in Hb.
    destruct (r_hav r !! u) as [hl|] eqn:E; cbn in Hin; [|contradiction].
    pose proof (Hh u hl (c, h) E Hin). cbn in H. lia.
Qed.

Lemma cell_read_wr8_same : ltac2:(zQ "f0!hgd!hg9!mu6!noc!ir4!nk6!j8!pgf!olf!ok5!ojb!t1!ira!mje!no4>1p@2$4$1$0>1v$0>2st$b>0@2$7@2$3^1@3$2$1$0^3@1$c^1@3$6$a@2$9@2$3@3$d^4^3^2@3$2$1$0^4@3$5$1$0^4@1$8@2$e^3+vf").
Proof. intros p v st.
  intros HT. rewrite (cell_read_wr8 p v st p), aptr_eqb_refl. cbn zeta. rewrite (not_stale_cur _ _ _ HT). reflexivity.
Qed.
Lemma cell_read_wr8_other : ltac2:(zQ "c0!hgd!hg9!nb!mu6!nk6!j8!ok5!noc!q3!ojb!t1!mje>1p$2>1v$0>2st$a>1q$2>0@1$8@3$5$2^1^4@3$5$9@2$6@2$7@3$b^5^4^3@3$3$1$0^2@3$4$1$0^2@2$6@2$7^3@3$3$1$0^2@3$4$1$0^2").
Proof. intros p v st q. intros NE. rewrite cell_read_wr8, aptr_eqb_neq by exact NE. reflexivity. Qed.

(* [comment removed for export] *)
