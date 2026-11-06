(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Spec_MI_Kit () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "stdpp.base."; "stdpp.countable."; "stdpp.decidable."; "stdpp.fin_maps."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["1bool"; "1false"; "1list"; "1prod"; "1reflect"; "1true"; "2eq"; "2iff"; "2not"; "3N"; "3Z"; "4aptr"; "4aptr_eqb"; "4area"; "4brkstate"; "4c_active"]; ["4c_avail_meta"; "4c_avail_meta_area_count"; "4c_avail_meta_areas"; "4c_avail_meta_count"; "4c_bounces"; "4c_brk"; "4c_free_meta_head"; "4c_init_done"; "4c_meta_alloc_shift"; "4c_meta_area_head"; "4c_meta_area_tail"; "4c_mmap_counter"; "4c_secret"; "4c_seq"; "4c_unmap_seq"; "4c_usage"]; ["4get_meta_rec"; "4ghdr"; "4mctx"; "4meta"; "4mstate"; "4optr"; "4optr_eqb"; "4put_meta"; "4region"; "4s_areas"; "4s_ctx"; "4s_groups"; "4s_metas"; "4s_next_rid"; "4s_regions"; "4s_reserved"]; ["4s_secret"; "4s_shadow"; "4s_slots"; "4s_tick"; "4set_active_map"; "4set_areas"; "4set_avail_meta"; "4set_avail_meta_area_count"; "4set_avail_meta_areas"; "4set_avail_meta_count"; "4set_bounces_map"; "4set_brk"; "4set_free_meta_head"; "4set_groups"; "4set_init_done"; "4set_meta_alloc_shift"]; ["4set_meta_area_head"; "4set_meta_area_tail"; "4set_metas"; "4set_mmap_counter"; "4set_next_rid"; "4set_regions"; "4set_secret"; "4set_seq"; "4set_shadow"; "4set_slots"; "4set_tick"; "4set_unmap_seq_map"; "4set_usage_map"; "4shadow"; "4upd_ctx"; "4upd_meta"]; ["0a"; "0b"; "0c"; "0f"; "0m"; "0r"; "0st"; "0st'"; "5insert"; "6N_countable"; "6Z_countable"; "6prod_countable"; "7prod_eq_dec"; "8map_insert"; "9gmap"; "9gmap_partial_alter"]; [":eq_dec"; ";eq_dec"; "0v"; "0x"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma aptr_eqb_refl : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "9&;'6'0&<r1%2211(5%63521pU281").
Proof. intros a. unfold aptr_eqb. rewrite N.eqb_refl, Z.eqb_refl. reflexivity. Qed.
Lemma aptr_eqb_eq : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">&;&7'6'0&<r2r1%3221(5%73621%83:54%:221pU4<1pU2=1").
Proof. intros a b.
unfold aptr_eqb. destruct a as [r o], b as [r' o']; cbn. rewrite Bool.andb_true_iff, N.eqb_eq, Z.eqb_eq.
split; [intros [-> ->]; reflexivity| intros H; inversion H; auto].
Qed.
Lemma aptr_eqb_spec : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ";&;'4'6r2r1%33521&<%1243%7231pU491pU2:1").
Proof. intros a b.
destruct (aptr_eqb a b) eqn:E; constructor.
- apply aptr_eqb_eq. exact E.
- intros ->. rewrite aptr_eqb_refl in E. discriminate.
Qed.
Lemma aptr_eqb_neq : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "@&;&8'6r2r1%33521%511'0&<r3%2217(1%:3521p071pU4>1pU2?1").
Proof. intros a b. intros H. destruct (aptr_eqb_spec a b); [contradiction| reflexivity]. Qed.
Lemma optr_eqb_spec : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ";&Q5'4'6r2r1%33521&Q6%1243%7231pU491pU2:1").
Proof. intros a b.
destruct a as [a|], b as [b|]; cbn; try (constructor; congruence).
destruct (aptr_eqb_spec a b); constructor; congruence.
Qed.
Lemma optr_eqb_refl : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "9&Q5'6'0&Q6r1%2211(5%63521pU281").
Proof. intros a. destruct (optr_eqb_spec a a); [reflexivity| contradiction]. Qed.
End CEIL_WRAP_1.
Ltac case_ptr x y := destruct (aptr_eqb_spec x y) as [?EQp|?NEp]; [first [subst x | subst y | idtac]|].
Section CEIL_WRAP_2.
Context {RUNp : RunP}.
#[export] Instance aptr_eq_dec : EqDecision aptr := _.
Lemma get_meta_rec_put st m r x :
get_meta_rec (put_meta m r st) x = if aptr_eqb x m then r else get_meta_rec st x.
Proof.
unfold get_meta_rec, put_meta; cbn. destruct (aptr_eqb_spec x m) as [->|NE].
- rewrite lookup_insert_eq. reflexivity.
- rewrite lookup_insert_ne by congruence. reflexivity.
Qed.
Lemma get_meta_rec_upd st m f x :
get_meta_rec (upd_meta m f st) x = if aptr_eqb x m then f (get_meta_rec st m) else get_meta_rec st x.
Proof. unfold upd_meta. apply get_meta_rec_put. Qed.
Lemma get_meta_rec_put_same : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "?'Q4&;'Q3'6&Q0&Q7r2r1r3%43321%6214%83914pU<:1pU:<1pU>>1").
Proof. intros st m r. rewrite get_meta_rec_put, aptr_eqb_refl. reflexivity. Qed.
Lemma get_meta_rec_put_other : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "G'Q4&;'Q3&8'6r1r3%33621%511&Q0&Q7r4r5%33271r2%6221%7242%=3?21p0:1pV8B1pU<B1pU:D1pU>F1").
Proof. intros st m r x. intros H. rewrite get_meta_rec_put, aptr_eqb_neq by exact H. reflexivity. Qed.
Lemma get_meta_rec_upd_same : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B'Q4&;'Q3p011'6&Q0&R?r2r1r3%43321%6214%7235%511%:3<31pU8<1pU:?1pU>A1").
Proof. intros st m f. rewrite get_meta_rec_upd, aptr_eqb_refl. reflexivity. Qed.
Lemma get_meta_rec_upd_other : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "H'Q4&;'Q3p011&8'6r1r3%33721%511&Q0&R?r4r5%33271r2%6221%7242%=3@21p0:1pV8C1pU8B1pU:E1pU>G1").
Proof. intros st m f x. intros H. rewrite get_meta_rec_upd, aptr_eqb_neq by exact H. reflexivity. Qed.
Lemma s_metas_put_meta : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "Q2&;'Q3'Q4'6'RN&RL'9&S0':&S1%544321&RK&RI&RJ%36872651%;4?51>&Q<&Q7r3r2r1%43321%611&RH&RM&RO%14J@<I%34KJ<1%<18%67ML>2;:1%K3?81pU>M1pU<O1pU:Q11").
Proof. intros m r st. reflexivity. Qed.
Lemma s_metas_upd_meta : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "Q6&;'Q3p011'Q4'6'RN&RL'9&S0':&S1%544321&RK&RI&RJ%36872651%;4@51?&Q<&R?r3r2r1%43321%611&RH&RM&RO%14K@<J%34LK<1&Q0%129;%;11%?1;%97Q1Q0A5>21%N3B;1pU>Q01pU8Q21pU:Q51").
Proof. intros m f st. reflexivity. Qed.
Lemma lookup_metas_put st m r x :
s_metas (put_meta m r st) !! x = if aptr_eqb x m then Some r else s_metas st !! x.
Proof.
cbn. destruct (aptr_eqb_spec x m) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
Qed.
Lemma lookup_metas_upd st m f x :
s_metas (upd_meta m f st) !! x = if aptr_eqb x m then Some (f (get_meta_rec st m)) else s_metas st !! x.
Proof. unfold upd_meta. apply lookup_metas_put. Qed.
Lemma get_meta_rec_ext : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "O'Q4&;'6'RN&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'Q3%<4>621&Q<r2%211r3%411%C3631&Q0%1246r4%3218%H3<31p061pV8K1pU@M1pU>N1").
Proof. intros st st' x. intros H. unfold get_meta_rec. rewrite H. reflexivity. Qed.
End CEIL_WRAP_2.
Ltac msimp := cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen
m_set_prev m_set_next m_set_mem m_set_avail m_set_freed m_set_last_idx m_set_freeable m_set_sizeclass m_set_maplen
meta0] in *.
Section CEIL_WRAP_3.
Context {RUNp : RunP}.
Lemma s_ctx_upd_ctx : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "?'Q2p011'Q4'6&Q:&R>r2r1%3221%511%613%511%93<31pU>;1pU8=1"). Proof. intros f st. reflexivity. Qed.
Lemma s_regions_upd_ctx : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "D'Q2p011'Q4'6'RN'9&S0&RI'Q8%544321&Q>&R>r2r1%3221%511%613%>3821pU>@1pU8B1"). Proof. intros f st. reflexivity. Qed.
Lemma s_shadow_upd_ctx : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "D'Q2p011'Q4'6'RN'9&S0&RI'R=%544321&QA&R>r2r1%3221%511%613%>3821pU>@1pU8B1"). Proof. intros f st. reflexivity. Qed.
Lemma s_next_rid_upd_ctx : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "?'Q2p011'Q4'6'9&Q=&R>r2r1%3221%511%613%93821pU>;1pU8=1"). Proof. intros f st. reflexivity. Qed.
Lemma s_metas_upd_ctx : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "L'Q2p011'Q4'6'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'Q3%=4<621&Q<&R>r2r1%3221%511%613%F3821pU>H1pU8J1"). Proof. intros f st. reflexivity. Qed.
Lemma s_areas_upd_ctx : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "L'Q2p011'Q4'6'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'=%=4<621&Q9&R>r2r1%3221%511%613%F3821pU>H1pU8J1"). Proof. intros f st. reflexivity. Qed.
Lemma s_groups_upd_ctx : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "L'Q2p011'Q4'6'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'Q1%=4<621&Q;&R>r2r1%3221%511%613%F3821pU>H1pU8J1"). Proof. intros f st. reflexivity. Qed.
Lemma s_slots_upd_ctx : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "M'Q2p011'Q4'6'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'3%12<8%>4=731&QB&R>r2r1%3221%511%613%G3821pU>I1pU8K1"). Proof. intros f st. reflexivity. Qed.
Lemma s_tick_upd_ctx : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "?'Q2p011'Q4'6'9&QC&R>r2r1%3221%511%613%93821pU>;1pU8=1"). Proof. intros f st. reflexivity. Qed.
Lemma s_secret_upd_ctx : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "?'Q2p011'Q4'6':&Q@&R>r2r1%3221%511%613%93821pU>;1pU8=1"). Proof. intros f st. reflexivity. Qed.
Lemma s_reserved_upd_ctx : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "C'Q2p011'Q4'6'2'3':%2211%411&Q?&R>r2r1%3221%511%613%=3821pU>?1pU8A1"). Proof. intros f st. reflexivity. Qed.
Lemma s_ctx_set_regions : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "C'RN'9&S0&RI'Q8%544321'Q4'6'Q2&Q:&R5r2r1%3221%511%613%93821pU>;1pV6=1"). Proof. intros v st. reflexivity. Qed.
Lemma s_regions_set_regions : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A'RN'9&S0&RI'Q8%544321'Q4'6&Q>&R5r2r1%3221%511%73914pU>91pV6;1"). Proof. intros v st. reflexivity. Qed.
Lemma s_shadow_set_regions : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "D'RN'9&S0&RI'Q8%544321'Q4'6'R=%948761&QA&R5r2r1%3221%511%613%:3821pU><1pV6>1"). Proof. intros v st. reflexivity. Qed.
Lemma s_next_rid_set_regions : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B'RN'9&S0&RI'Q8%544321'Q4'6&Q=&R5r2r1%3221%511%613%83>21pU>:1pV6<1"). Proof. intros v st. reflexivity. Qed.
Lemma s_metas_set_regions : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "L'RN'9&S0&RI'Q8%544321'Q4'6&;&RL':&S1%34;:21&RK&RJ%26>=<541'Q3%A49521&Q<&R5r2r1%3221%511%613%B3821pU>D1pV6F1"). Proof. intros v st. reflexivity. Qed.
Lemma s_areas_set_regions : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "L'RN'9&S0&RI'Q8%544321'Q4'6&;&RL':&S1%34;:21&RK&RJ%26>=<541'=%A49521&Q9&R5r2r1%3221%511%613%B3821pU>D1pV6F1"). Proof. intros v st. reflexivity. Qed.
Lemma s_groups_set_regions : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "L'RN'9&S0&RI'Q8%544321'Q4'6&;&RL':&S1%34;:21&RK&RJ%26>=<541'Q1%A49521&Q;&R5r2r1%3221%511%613%B3821pU>D1pV6F1"). Proof. intros v st. reflexivity. Qed.
Lemma s_slots_set_regions : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "M'RN'9&S0&RI'Q8%544321'Q4'6&;&RL':&S1%34;:21&RK&RJ%26>=<541'3%1297%B4:631&QB&R5r2r1%3221%511%613%C3821pU>E1pV6G1"). Proof. intros v st. reflexivity. Qed.
Lemma s_tick_set_regions : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B'RN'9&S0&RI'Q8%544321'Q4'6&QC&R5r2r1%3221%511%613%83>21pU>:1pV6<1"). Proof. intros v st. reflexivity. Qed.
Lemma s_secret_set_regions : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "C'RN'9&S0&RI'Q8%544321'Q4'6':&Q@&R5r2r1%3221%511%613%93821pU>;1pV6=1"). Proof. intros v st. reflexivity. Qed.
Lemma s_reserved_set_regions : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "G'RN'9&S0&RI'Q8%544321'Q4'6'2'3':%2211%411&Q?&R5r2r1%3221%511%613%=3821pU>?1pV6A1"). Proof. intros v st. reflexivity. Qed.
Lemma s_ctx_set_shadow : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "C'RN'9&S0&RI'R=%544321'Q4'6'Q2&Q:&R8r2r1%3221%511%613%93821pU>;1pV6=1"). Proof. intros v st. reflexivity. Qed.
Lemma s_regions_set_shadow : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "D'RN'9&S0&RI'R=%544321'Q4'6'Q8%948761&Q>&R8r2r1%3221%511%613%:3821pU><1pV6>1"). Proof. intros v st. reflexivity. Qed.
Lemma s_shadow_set_shadow : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A'RN'9&S0&RI'R=%544321'Q4'6&QA&R8r2r1%3221%511%73914pU>91pV6;1"). Proof. intros v st. reflexivity. Qed.
Lemma s_next_rid_set_shadow : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B'RN'9&S0&RI'R=%544321'Q4'6&Q=&R8r2r1%3221%511%613%83>21pU>:1pV6<1"). Proof. intros v st. reflexivity. Qed.
Lemma s_metas_set_shadow : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "L'RN'9&S0&RI'R=%544321'Q4'6&;&RL':&S1%34;:21&RK&RJ%26>=<541'Q3%A49521&Q<&R8r2r1%3221%511%613%B3821pU>D1pV6F1"). Proof. intros v st. reflexivity. Qed.
Lemma s_areas_set_shadow : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "L'RN'9&S0&RI'R=%544321'Q4'6&;&RL':&S1%34;:21&RK&RJ%26>=<541'=%A49521&Q9&R8r2r1%3221%511%613%B3821pU>D1pV6F1"). Proof. intros v st. reflexivity. Qed.
Lemma s_groups_set_shadow : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "L'RN'9&S0&RI'R=%544321'Q4'6&;&RL':&S1%34;:21&RK&RJ%26>=<541'Q1%A49521&Q;&R8r2r1%3221%511%613%B3821pU>D1pV6F1"). Proof. intros v st. reflexivity. Qed.
Lemma s_slots_set_shadow : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "M'RN'9&S0&RI'R=%544321'Q4'6&;&RL':&S1%34;:21&RK&RJ%26>=<541'3%1297%B4:631&QB&R8r2r1%3221%511%613%C3821pU>E1pV6G1"). Proof. intros v st. reflexivity. Qed.
Lemma s_tick_set_shadow : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B'RN'9&S0&RI'R=%544321'Q4'6&QC&R8r2r1%3221%511%613%83>21pU>:1pV6<1"). Proof. intros v st. reflexivity. Qed.
Lemma s_secret_set_shadow : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "C'RN'9&S0&RI'R=%544321'Q4'6':&Q@&R8r2r1%3221%511%613%93821pU>;1pV6=1"). Proof. intros v st. reflexivity. Qed.
Lemma s_reserved_set_shadow : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "G'RN'9&S0&RI'R=%544321'Q4'6'2'3':%2211%411&Q?&R8r2r1%3221%511%613%=3821pU>?1pV6A1"). Proof. intros v st. reflexivity. Qed.
Lemma s_ctx_set_next_rid : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">'9'Q4'6'Q2&Q:&R4r2r1%3221%511%613%93821pU>;1pV6=1"). Proof. intros v st. reflexivity. Qed.
Lemma s_regions_set_next_rid : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B'9'Q4'6'RN&S0&RI'Q8%447321&Q>&R4r2r1%3221%511%613%=3821pU>?1pV6A1"). Proof. intros v st. reflexivity. Qed.
Lemma s_shadow_set_next_rid : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B'9'Q4'6'RN&S0&RI'R=%447321&QA&R4r2r1%3221%511%613%=3821pU>?1pV6A1"). Proof. intros v st. reflexivity. Qed.
Lemma s_next_rid_set_next_rid : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "<'9'Q4'6&Q=&R4r2r1%3221%511%73914pU>91pV6;1"). Proof. intros v st. reflexivity. Qed.
Lemma s_metas_set_next_rid : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "J'9'Q4'6'RN&;&RL&S0':&S1%449321&RK&RI&RJ%36=72651'Q3%<4;621&Q<&R4r2r1%3221%511%613%E3821pU>G1pV6I1"). Proof. intros v st. reflexivity. Qed.
Lemma s_areas_set_next_rid : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "J'9'Q4'6'RN&;&RL&S0':&S1%449321&RK&RI&RJ%36=72651'=%<4;621&Q9&R4r2r1%3221%511%613%E3821pU>G1pV6I1"). Proof. intros v st. reflexivity. Qed.
Lemma s_groups_set_next_rid : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "J'9'Q4'6'RN&;&RL&S0':&S1%449321&RK&RI&RJ%36=72651'Q1%<4;621&Q;&R4r2r1%3221%511%613%E3821pU>G1pV6I1"). Proof. intros v st. reflexivity. Qed.
Lemma s_slots_set_next_rid : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "K'9'Q4'6'RN&;&RL&S0':&S1%449321&RK&RI&RJ%36=72651'3%12;8%=4<731&QB&R4r2r1%3221%511%613%F3821pU>H1pV6J1"). Proof. intros v st. reflexivity. Qed.
Lemma s_tick_set_next_rid : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "='9'Q4'6&QC&R4r2r1%3221%511%613%83:21pU>:1pV6<1"). Proof. intros v st. reflexivity. Qed.
Lemma s_secret_set_next_rid : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">'9'Q4'6':&Q@&R4r2r1%3221%511%613%93821pU>;1pV6=1"). Proof. intros v st. reflexivity. Qed.
Lemma s_reserved_set_next_rid : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B'9'Q4'6'2'3':%2211%411&Q?&R4r2r1%3221%511%613%=3821pU>?1pV6A1"). Proof. intros v st. reflexivity. Qed.
Lemma s_ctx_set_metas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "K'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'Q3%=4<621'Q4'6'Q2&Q:&R2r2r1%3221%511%613%93821pU>;1pV6=1"). Proof. intros v st. reflexivity. Qed.
Lemma s_regions_set_metas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "L'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'Q3%=4<621'Q4'6'Q8%A4>=81&Q>&R2r2r1%3221%511%613%:3821pU><1pV6>1"). Proof. intros v st. reflexivity. Qed.
Lemma s_shadow_set_metas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "L'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'Q3%=4<621'Q4'6'R=%A4>=81&QA&R2r2r1%3221%511%613%:3821pU><1pV6>1"). Proof. intros v st. reflexivity. Qed.
Lemma s_next_rid_set_metas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "J'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'Q3%=4<621'Q4'6&Q=&R2r2r1%3221%511%613%83D21pU>:1pV6<1"). Proof. intros v st. reflexivity. Qed.
Lemma s_metas_set_metas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "I'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'Q3%=4<621'Q4'6&Q<&R2r2r1%3221%511%73914pU>91pV6;1"). Proof. intros v st. reflexivity. Qed.
Lemma s_areas_set_metas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "L'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'Q3%=4<621'Q4'6'=%A4@:61&Q9&R2r2r1%3221%511%613%:3821pU><1pV6>1"). Proof. intros v st. reflexivity. Qed.
Lemma s_groups_set_metas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "L'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'Q3%=4<621'Q4'6'Q1%A4@:61&Q;&R2r2r1%3221%511%613%:3821pU><1pV6>1"). Proof. intros v st. reflexivity. Qed.
Lemma s_slots_set_metas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "M'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'Q3%=4<621'Q4'6'3%12@<%B4A;71&QB&R2r2r1%3221%511%613%;3821pU>=1pV6?1"). Proof. intros v st. reflexivity. Qed.
Lemma s_tick_set_metas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "J'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'Q3%=4<621'Q4'6&QC&R2r2r1%3221%511%613%83D21pU>:1pV6<1"). Proof. intros v st. reflexivity. Qed.
Lemma s_secret_set_metas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "J'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'Q3%=4<621'Q4'6&Q@&R2r2r1%3221%511%613%83B21pU>:1pV6<1"). Proof. intros v st. reflexivity. Qed.
Lemma s_reserved_set_metas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "N'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'Q3%=4<621'Q4'6'2'3%12==%311&Q?&R2r2r1%3221%511%613%<3821pU>>1pV6@1"). Proof. intros v st. reflexivity. Qed.
Lemma s_ctx_set_areas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "K'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'=%=4<621'Q4'6'Q2&Q:&QEr2r1%3221%511%613%93821pU>;1pV6=1"). Proof. intros v st. reflexivity. Qed.
Lemma s_regions_set_areas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "L'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'=%=4<621'Q4'6'Q8%A4>=81&Q>&QEr2r1%3221%511%613%:3821pU><1pV6>1"). Proof. intros v st. reflexivity. Qed.
Lemma s_shadow_set_areas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "L'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'=%=4<621'Q4'6'R=%A4>=81&QA&QEr2r1%3221%511%613%:3821pU><1pV6>1"). Proof. intros v st. reflexivity. Qed.
Lemma s_next_rid_set_areas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "J'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'=%=4<621'Q4'6&Q=&QEr2r1%3221%511%613%83D21pU>:1pV6<1"). Proof. intros v st. reflexivity. Qed.
Lemma s_metas_set_areas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "L'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'=%=4<621'Q4'6'Q3%A4@:61&Q<&QEr2r1%3221%511%613%:3821pU><1pV6>1"). Proof. intros v st. reflexivity. Qed.
Lemma s_areas_set_areas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "I'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'=%=4<621'Q4'6&Q9&QEr2r1%3221%511%73914pU>91pV6;1"). Proof. intros v st. reflexivity. Qed.
Lemma s_groups_set_areas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "L'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'=%=4<621'Q4'6'Q1%A4@:61&Q;&QEr2r1%3221%511%613%:3821pU><1pV6>1"). Proof. intros v st. reflexivity. Qed.
Lemma s_slots_set_areas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "M'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'=%=4<621'Q4'6'3%12@<%B4A;71&QB&QEr2r1%3221%511%613%;3821pU>=1pV6?1"). Proof. intros v st. reflexivity. Qed.
Lemma s_tick_set_areas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "J'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'=%=4<621'Q4'6&QC&QEr2r1%3221%511%613%83D21pU>:1pV6<1"). Proof. intros v st. reflexivity. Qed.
Lemma s_secret_set_areas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "J'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'=%=4<621'Q4'6&Q@&QEr2r1%3221%511%613%83B21pU>:1pV6<1"). Proof. intros v st. reflexivity. Qed.
Lemma s_reserved_set_areas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "N'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'=%=4<621'Q4'6'2'3%12==%311&Q?&QEr2r1%3221%511%613%<3821pU>>1pV6@1"). Proof. intros v st. reflexivity. Qed.
Lemma s_ctx_set_groups : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "K'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'Q1%=4<621'Q4'6'Q2&Q:&QMr2r1%3221%511%613%93821pU>;1pV6=1"). Proof. intros v st. reflexivity. Qed.
Lemma s_regions_set_groups : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "L'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'Q1%=4<621'Q4'6'Q8%A4>=81&Q>&QMr2r1%3221%511%613%:3821pU><1pV6>1"). Proof. intros v st. reflexivity. Qed.
Lemma s_shadow_set_groups : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "L'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'Q1%=4<621'Q4'6'R=%A4>=81&QA&QMr2r1%3221%511%613%:3821pU><1pV6>1"). Proof. intros v st. reflexivity. Qed.
Lemma s_next_rid_set_groups : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "J'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'Q1%=4<621'Q4'6&Q=&QMr2r1%3221%511%613%83D21pU>:1pV6<1"). Proof. intros v st. reflexivity. Qed.
Lemma s_metas_set_groups : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "L'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'Q1%=4<621'Q4'6'Q3%A4@:61&Q<&QMr2r1%3221%511%613%:3821pU><1pV6>1"). Proof. intros v st. reflexivity. Qed.
Lemma s_areas_set_groups : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "L'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'Q1%=4<621'Q4'6'=%A4@:61&Q9&QMr2r1%3221%511%613%:3821pU><1pV6>1"). Proof. intros v st. reflexivity. Qed.
Lemma s_groups_set_groups : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "I'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'Q1%=4<621'Q4'6&Q;&QMr2r1%3221%511%73914pU>91pV6;1"). Proof. intros v st. reflexivity. Qed.
Lemma s_slots_set_groups : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "M'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'Q1%=4<621'Q4'6'3%12@<%B4A;71&QB&QMr2r1%3221%511%613%;3821pU>=1pV6?1"). Proof. intros v st. reflexivity. Qed.
Lemma s_tick_set_groups : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "J'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'Q1%=4<621'Q4'6&QC&QMr2r1%3221%511%613%83D21pU>:1pV6<1"). Proof. intros v st. reflexivity. Qed.
Lemma s_secret_set_groups : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "J'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'Q1%=4<621'Q4'6&Q@&QMr2r1%3221%511%613%83B21pU>:1pV6<1"). Proof. intros v st. reflexivity. Qed.
Lemma s_reserved_set_groups : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "N'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'Q1%=4<621'Q4'6'2'3%12==%311&Q?&QMr2r1%3221%511%613%<3821pU>>1pV6@1"). Proof. intros v st. reflexivity. Qed.
Lemma s_ctx_set_slots : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "L'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'3%12<8%>4=731'Q4'6'Q2&Q:&R9r2r1%3221%511%613%93821pU>;1pV6=1"). Proof. intros v st. reflexivity. Qed.
Lemma s_regions_set_slots : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "M'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'3%12<8%>4=731'Q4'6'Q8%B4?>91&Q>&R9r2r1%3221%511%613%:3821pU><1pV6>1"). Proof. intros v st. reflexivity. Qed.
Lemma s_shadow_set_slots : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "M'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'3%12<8%>4=731'Q4'6'R=%B4?>91&QA&R9r2r1%3221%511%613%:3821pU><1pV6>1"). Proof. intros v st. reflexivity. Qed.
Lemma s_next_rid_set_slots : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "K'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'3%12<8%>4=731'Q4'6&Q=&R9r2r1%3221%511%613%83E21pU>:1pV6<1"). Proof. intros v st. reflexivity. Qed.
Lemma s_metas_set_slots : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "M'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'3%12<8%>4=731'Q4'6'Q3%B4A;71&Q<&R9r2r1%3221%511%613%:3821pU><1pV6>1"). Proof. intros v st. reflexivity. Qed.
Lemma s_areas_set_slots : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "M'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'3%12<8%>4=731'Q4'6'=%B4A;71&Q9&R9r2r1%3221%511%613%:3821pU><1pV6>1"). Proof. intros v st. reflexivity. Qed.
Lemma s_groups_set_slots : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "M'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'3%12<8%>4=731'Q4'6'Q1%B4A;71&Q;&R9r2r1%3221%511%613%:3821pU><1pV6>1"). Proof. intros v st. reflexivity. Qed.
Lemma s_slots_set_slots : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "J'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'3%12<8%>4=731'Q4'6&QB&R9r2r1%3221%511%73914pU>91pV6;1"). Proof. intros v st. reflexivity. Qed.
Lemma s_tick_set_slots : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "K'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'3%12<8%>4=731'Q4'6&QC&R9r2r1%3221%511%613%83E21pU>:1pV6<1"). Proof. intros v st. reflexivity. Qed.
Lemma s_secret_set_slots : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "K'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'3%12<8%>4=731'Q4'6&Q@&R9r2r1%3221%511%613%83C21pU>:1pV6<1"). Proof. intros v st. reflexivity. Qed.
Lemma s_reserved_set_slots : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "N'RN&;&RL'9&S0':&S1%544321&RK&RI&RJ%36872651'3%12<8%>4=731'Q4'6'2%62==%211&Q?&R9r2r1%3221%511%613%;3821pU>=1pV6?1"). Proof. intros v st. reflexivity. Qed.
Lemma s_ctx_set_tick : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">'9'Q4'6'Q2&Q:&R:r2r1%3221%511%613%93821pU>;1pV6=1"). Proof. intros v st. reflexivity. Qed.
Lemma s_regions_set_tick : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B'9'Q4'6'RN&S0&RI'Q8%447321&Q>&R:r2r1%3221%511%613%=3821pU>?1pV6A1"). Proof. intros v st. reflexivity. Qed.
Lemma s_shadow_set_tick : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B'9'Q4'6'RN&S0&RI'R=%447321&QA&R:r2r1%3221%511%613%=3821pU>?1pV6A1"). Proof. intros v st. reflexivity. Qed.
Lemma s_next_rid_set_tick : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "='9'Q4'6&Q=&R:r2r1%3221%511%613%83:21pU>:1pV6<1"). Proof. intros v st. reflexivity. Qed.
Lemma s_metas_set_tick : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "J'9'Q4'6'RN&;&RL&S0':&S1%449321&RK&RI&RJ%36=72651'Q3%<4;621&Q<&R:r2r1%3221%511%613%E3821pU>G1pV6I1"). Proof. intros v st. reflexivity. Qed.
Lemma s_areas_set_tick : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "J'9'Q4'6'RN&;&RL&S0':&S1%449321&RK&RI&RJ%36=72651'=%<4;621&Q9&R:r2r1%3221%511%613%E3821pU>G1pV6I1"). Proof. intros v st. reflexivity. Qed.
Lemma s_groups_set_tick : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "J'9'Q4'6'RN&;&RL&S0':&S1%449321&RK&RI&RJ%36=72651'Q1%<4;621&Q;&R:r2r1%3221%511%613%E3821pU>G1pV6I1"). Proof. intros v st. reflexivity. Qed.
Lemma s_slots_set_tick : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "K'9'Q4'6'RN&;&RL&S0':&S1%449321&RK&RI&RJ%36=72651'3%12;8%=4<731&QB&R:r2r1%3221%511%613%F3821pU>H1pV6J1"). Proof. intros v st. reflexivity. Qed.
Lemma s_tick_set_tick : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "<'9'Q4'6&QC&R:r2r1%3221%511%73914pU>91pV6;1"). Proof. intros v st. reflexivity. Qed.
Lemma s_secret_set_tick : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">'9'Q4'6':&Q@&R:r2r1%3221%511%613%93821pU>;1pV6=1"). Proof. intros v st. reflexivity. Qed.
Lemma s_reserved_set_tick : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B'9'Q4'6'2'3':%2211%411&Q?&R:r2r1%3221%511%613%=3821pU>?1pV6A1"). Proof. intros v st. reflexivity. Qed.
Lemma c_secret_set_secret : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "<':'Q2'6&L&R6r2r1%3221%511%73914pU691pV6;1"). Proof. intros v c. reflexivity. Qed.
Lemma c_init_done_set_secret : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=':'Q2'6&G&R6r2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_mmap_counter_set_secret : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=':'Q2'6&K&R6r2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_free_meta_head_set_secret : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">':'Q2'6&Q5&F&R6r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_set_secret : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">':'Q2'6&Q5&@&R6r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_count_set_secret : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=':'Q2'6&C&R6r2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_secret : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=':'Q2'6&A&R6r2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_secret : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=':'Q2'6&H&R6r2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_head_set_secret : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">':'Q2'6&Q5&I&R6r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_tail_set_secret : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">':'Q2'6&Q5&J&R6r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_areas_set_secret : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">':'Q2'6&Q5&B&R6r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_active_set_secret : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B':'Q2'6'RN&S1&RJ&;%447321&?&R6r2r1%3221%511%613%=3821pU6?1pV6A1"). Proof. intros v c. reflexivity. Qed.
Lemma c_usage_set_secret : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A':'Q2'6'RN&S1&RJ%346216&O&R6r2r1%3221%511%613%<3821pU6>1pV6@1"). Proof. intros v c. reflexivity. Qed.
Lemma c_unmap_seq_set_secret : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A':'Q2'6'RN&S1&RJ%346216&N&R6r2r1%3221%511%613%<3821pU6>1pV6@1"). Proof. intros v c. reflexivity. Qed.
Lemma c_bounces_set_secret : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A':'Q2'6'RN&S1&RJ%346216&D&R6r2r1%3221%511%613%<3821pU6>1pV6@1"). Proof. intros v c. reflexivity. Qed.
Lemma c_seq_set_secret : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=':'Q2'6&M&R6r2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_brk_set_secret : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">':'Q2'6'>&E&R6r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_secret_set_init_done : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=':'Q2'6&L&QNr2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_init_done_set_init_done : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "<':'Q2'6&G&QNr2r1%3221%511%73914pU691pV6;1"). Proof. intros v c. reflexivity. Qed.
Lemma c_mmap_counter_set_init_done : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=':'Q2'6&K&QNr2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_free_meta_head_set_init_done : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">':'Q2'6&Q5&F&QNr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_set_init_done : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">':'Q2'6&Q5&@&QNr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_count_set_init_done : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=':'Q2'6&C&QNr2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_init_done : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=':'Q2'6&A&QNr2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_init_done : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=':'Q2'6&H&QNr2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_head_set_init_done : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">':'Q2'6&Q5&I&QNr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_tail_set_init_done : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">':'Q2'6&Q5&J&QNr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_areas_set_init_done : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">':'Q2'6&Q5&B&QNr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_active_set_init_done : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B':'Q2'6'RN&S1&RJ&;%447321&?&QNr2r1%3221%511%613%=3821pU6?1pV6A1"). Proof. intros v c. reflexivity. Qed.
Lemma c_usage_set_init_done : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A':'Q2'6'RN&S1&RJ%346216&O&QNr2r1%3221%511%613%<3821pU6>1pV6@1"). Proof. intros v c. reflexivity. Qed.
Lemma c_unmap_seq_set_init_done : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A':'Q2'6'RN&S1&RJ%346216&N&QNr2r1%3221%511%613%<3821pU6>1pV6@1"). Proof. intros v c. reflexivity. Qed.
Lemma c_bounces_set_init_done : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A':'Q2'6'RN&S1&RJ%346216&D&QNr2r1%3221%511%613%<3821pU6>1pV6@1"). Proof. intros v c. reflexivity. Qed.
Lemma c_seq_set_init_done : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=':'Q2'6&M&QNr2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_brk_set_init_done : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">':'Q2'6'>&E&QNr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_secret_set_mmap_counter : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=':'Q2'6&L&R3r2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_init_done_set_mmap_counter : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=':'Q2'6&G&R3r2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_mmap_counter_set_mmap_counter : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "<':'Q2'6&K&R3r2r1%3221%511%73914pU691pV6;1"). Proof. intros v c. reflexivity. Qed.
Lemma c_free_meta_head_set_mmap_counter : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">':'Q2'6&Q5&F&R3r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_set_mmap_counter : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">':'Q2'6&Q5&@&R3r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_count_set_mmap_counter : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=':'Q2'6&C&R3r2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_mmap_counter : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=':'Q2'6&A&R3r2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_mmap_counter : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=':'Q2'6&H&R3r2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_head_set_mmap_counter : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">':'Q2'6&Q5&I&R3r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_tail_set_mmap_counter : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">':'Q2'6&Q5&J&R3r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_areas_set_mmap_counter : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">':'Q2'6&Q5&B&R3r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_active_set_mmap_counter : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B':'Q2'6'RN&S1&RJ&;%447321&?&R3r2r1%3221%511%613%=3821pU6?1pV6A1"). Proof. intros v c. reflexivity. Qed.
Lemma c_usage_set_mmap_counter : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A':'Q2'6'RN&S1&RJ%346216&O&R3r2r1%3221%511%613%<3821pU6>1pV6@1"). Proof. intros v c. reflexivity. Qed.
Lemma c_unmap_seq_set_mmap_counter : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A':'Q2'6'RN&S1&RJ%346216&N&R3r2r1%3221%511%613%<3821pU6>1pV6@1"). Proof. intros v c. reflexivity. Qed.
Lemma c_bounces_set_mmap_counter : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A':'Q2'6'RN&S1&RJ%346216&D&R3r2r1%3221%511%613%<3821pU6>1pV6@1"). Proof. intros v c. reflexivity. Qed.
Lemma c_seq_set_mmap_counter : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=':'Q2'6&M&R3r2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_brk_set_mmap_counter : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">':'Q2'6'>&E&R3r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_secret_set_free_meta_head : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">&Q5'Q2'6':&L&QLr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_init_done_set_free_meta_head : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">&Q5'Q2'6':&G&QLr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_mmap_counter_set_free_meta_head : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">&Q5'Q2'6':&K&QLr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_free_meta_head_set_free_meta_head : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "<&Q5'Q2'6&F&QLr2r1%3221%511%73914pU691pV6;1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_set_free_meta_head : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=&Q5'Q2'6&@&QLr2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_count_set_free_meta_head : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">&Q5'Q2'6':&C&QLr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_free_meta_head : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">&Q5'Q2'6':&A&QLr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_free_meta_head : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">&Q5'Q2'6':&H&QLr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_head_set_free_meta_head : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=&Q5'Q2'6&I&QLr2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_tail_set_free_meta_head : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=&Q5'Q2'6&J&QLr2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_areas_set_free_meta_head : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=&Q5'Q2'6&B&QLr2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_active_set_free_meta_head : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "C&Q5'Q2'6'RN':&S1&RJ&;%544321&?&QLr2r1%3221%511%613%>3821pU6@1pV6B1"). Proof. intros v c. reflexivity. Qed.
Lemma c_usage_set_free_meta_head : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B&Q5'Q2'6'RN':&S1&RJ%443213&O&QLr2r1%3221%511%613%=3821pU6?1pV6A1"). Proof. intros v c. reflexivity. Qed.
Lemma c_unmap_seq_set_free_meta_head : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B&Q5'Q2'6'RN':&S1&RJ%443213&N&QLr2r1%3221%511%613%=3821pU6?1pV6A1"). Proof. intros v c. reflexivity. Qed.
Lemma c_bounces_set_free_meta_head : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B&Q5'Q2'6'RN':&S1&RJ%443213&D&QLr2r1%3221%511%613%=3821pU6?1pV6A1"). Proof. intros v c. reflexivity. Qed.
Lemma c_seq_set_free_meta_head : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">&Q5'Q2'6':&M&QLr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_brk_set_free_meta_head : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">&Q5'Q2'6'>&E&QLr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_secret_set_avail_meta : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">&Q5'Q2'6':&L&QFr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_init_done_set_avail_meta : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">&Q5'Q2'6':&G&QFr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_mmap_counter_set_avail_meta : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">&Q5'Q2'6':&K&QFr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_free_meta_head_set_avail_meta : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=&Q5'Q2'6&F&QFr2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_set_avail_meta : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "<&Q5'Q2'6&@&QFr2r1%3221%511%73914pU691pV6;1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_count_set_avail_meta : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">&Q5'Q2'6':&C&QFr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_avail_meta : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">&Q5'Q2'6':&A&QFr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_avail_meta : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">&Q5'Q2'6':&H&QFr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_head_set_avail_meta : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=&Q5'Q2'6&I&QFr2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_tail_set_avail_meta : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=&Q5'Q2'6&J&QFr2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_areas_set_avail_meta : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=&Q5'Q2'6&B&QFr2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_active_set_avail_meta : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "C&Q5'Q2'6'RN':&S1&RJ&;%544321&?&QFr2r1%3221%511%613%>3821pU6@1pV6B1"). Proof. intros v c. reflexivity. Qed.
Lemma c_usage_set_avail_meta : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B&Q5'Q2'6'RN':&S1&RJ%443213&O&QFr2r1%3221%511%613%=3821pU6?1pV6A1"). Proof. intros v c. reflexivity. Qed.
Lemma c_unmap_seq_set_avail_meta : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B&Q5'Q2'6'RN':&S1&RJ%443213&N&QFr2r1%3221%511%613%=3821pU6?1pV6A1"). Proof. intros v c. reflexivity. Qed.
Lemma c_bounces_set_avail_meta : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B&Q5'Q2'6'RN':&S1&RJ%443213&D&QFr2r1%3221%511%613%=3821pU6?1pV6A1"). Proof. intros v c. reflexivity. Qed.
Lemma c_seq_set_avail_meta : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">&Q5'Q2'6':&M&QFr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_brk_set_avail_meta : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">&Q5'Q2'6'>&E&QFr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_secret_set_avail_meta_count : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=':'Q2'6&L&QIr2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_init_done_set_avail_meta_count : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=':'Q2'6&G&QIr2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_mmap_counter_set_avail_meta_count : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=':'Q2'6&K&QIr2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_free_meta_head_set_avail_meta_count : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">':'Q2'6&Q5&F&QIr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_set_avail_meta_count : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">':'Q2'6&Q5&@&QIr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_count_set_avail_meta_count : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "<':'Q2'6&C&QIr2r1%3221%511%73914pU691pV6;1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_avail_meta_count : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=':'Q2'6&A&QIr2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_avail_meta_count : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=':'Q2'6&H&QIr2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_head_set_avail_meta_count : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">':'Q2'6&Q5&I&QIr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_tail_set_avail_meta_count : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">':'Q2'6&Q5&J&QIr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_areas_set_avail_meta_count : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">':'Q2'6&Q5&B&QIr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_active_set_avail_meta_count : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B':'Q2'6'RN&S1&RJ&;%447321&?&QIr2r1%3221%511%613%=3821pU6?1pV6A1"). Proof. intros v c. reflexivity. Qed.
Lemma c_usage_set_avail_meta_count : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A':'Q2'6'RN&S1&RJ%346216&O&QIr2r1%3221%511%613%<3821pU6>1pV6@1"). Proof. intros v c. reflexivity. Qed.
Lemma c_unmap_seq_set_avail_meta_count : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A':'Q2'6'RN&S1&RJ%346216&N&QIr2r1%3221%511%613%<3821pU6>1pV6@1"). Proof. intros v c. reflexivity. Qed.
Lemma c_bounces_set_avail_meta_count : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A':'Q2'6'RN&S1&RJ%346216&D&QIr2r1%3221%511%613%<3821pU6>1pV6@1"). Proof. intros v c. reflexivity. Qed.
Lemma c_seq_set_avail_meta_count : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=':'Q2'6&M&QIr2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_brk_set_avail_meta_count : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">':'Q2'6'>&E&QIr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_secret_set_avail_meta_area_count : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=':'Q2'6&L&QGr2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_init_done_set_avail_meta_area_count : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=':'Q2'6&G&QGr2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_mmap_counter_set_avail_meta_area_count : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=':'Q2'6&K&QGr2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_free_meta_head_set_avail_meta_area_count : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">':'Q2'6&Q5&F&QGr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_set_avail_meta_area_count : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">':'Q2'6&Q5&@&QGr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_count_set_avail_meta_area_count : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=':'Q2'6&C&QGr2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_avail_meta_area_count : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "<':'Q2'6&A&QGr2r1%3221%511%73914pU691pV6;1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_avail_meta_area_count : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=':'Q2'6&H&QGr2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_head_set_avail_meta_area_count : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">':'Q2'6&Q5&I&QGr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_tail_set_avail_meta_area_count : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">':'Q2'6&Q5&J&QGr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_areas_set_avail_meta_area_count : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">':'Q2'6&Q5&B&QGr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_active_set_avail_meta_area_count : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B':'Q2'6'RN&S1&RJ&;%447321&?&QGr2r1%3221%511%613%=3821pU6?1pV6A1"). Proof. intros v c. reflexivity. Qed.
Lemma c_usage_set_avail_meta_area_count : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A':'Q2'6'RN&S1&RJ%346216&O&QGr2r1%3221%511%613%<3821pU6>1pV6@1"). Proof. intros v c. reflexivity. Qed.
Lemma c_unmap_seq_set_avail_meta_area_count : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A':'Q2'6'RN&S1&RJ%346216&N&QGr2r1%3221%511%613%<3821pU6>1pV6@1"). Proof. intros v c. reflexivity. Qed.
Lemma c_bounces_set_avail_meta_area_count : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A':'Q2'6'RN&S1&RJ%346216&D&QGr2r1%3221%511%613%<3821pU6>1pV6@1"). Proof. intros v c. reflexivity. Qed.
Lemma c_seq_set_avail_meta_area_count : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=':'Q2'6&M&QGr2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_brk_set_avail_meta_area_count : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">':'Q2'6'>&E&QGr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_secret_set_meta_alloc_shift : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=':'Q2'6&L&QOr2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_init_done_set_meta_alloc_shift : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=':'Q2'6&G&QOr2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_mmap_counter_set_meta_alloc_shift : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=':'Q2'6&K&QOr2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_free_meta_head_set_meta_alloc_shift : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">':'Q2'6&Q5&F&QOr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_set_meta_alloc_shift : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">':'Q2'6&Q5&@&QOr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_count_set_meta_alloc_shift : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=':'Q2'6&C&QOr2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_meta_alloc_shift : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=':'Q2'6&A&QOr2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_meta_alloc_shift : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "<':'Q2'6&H&QOr2r1%3221%511%73914pU691pV6;1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_head_set_meta_alloc_shift : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">':'Q2'6&Q5&I&QOr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_tail_set_meta_alloc_shift : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">':'Q2'6&Q5&J&QOr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_areas_set_meta_alloc_shift : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">':'Q2'6&Q5&B&QOr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_active_set_meta_alloc_shift : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B':'Q2'6'RN&S1&RJ&;%447321&?&QOr2r1%3221%511%613%=3821pU6?1pV6A1"). Proof. intros v c. reflexivity. Qed.
Lemma c_usage_set_meta_alloc_shift : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A':'Q2'6'RN&S1&RJ%346216&O&QOr2r1%3221%511%613%<3821pU6>1pV6@1"). Proof. intros v c. reflexivity. Qed.
Lemma c_unmap_seq_set_meta_alloc_shift : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A':'Q2'6'RN&S1&RJ%346216&N&QOr2r1%3221%511%613%<3821pU6>1pV6@1"). Proof. intros v c. reflexivity. Qed.
Lemma c_bounces_set_meta_alloc_shift : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A':'Q2'6'RN&S1&RJ%346216&D&QOr2r1%3221%511%613%<3821pU6>1pV6@1"). Proof. intros v c. reflexivity. Qed.
Lemma c_seq_set_meta_alloc_shift : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=':'Q2'6&M&QOr2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_brk_set_meta_alloc_shift : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">':'Q2'6'>&E&QOr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_secret_set_meta_area_head : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">&Q5'Q2'6':&L&R0r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_init_done_set_meta_area_head : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">&Q5'Q2'6':&G&R0r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_mmap_counter_set_meta_area_head : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">&Q5'Q2'6':&K&R0r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_free_meta_head_set_meta_area_head : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=&Q5'Q2'6&F&R0r2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_set_meta_area_head : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=&Q5'Q2'6&@&R0r2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_count_set_meta_area_head : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">&Q5'Q2'6':&C&R0r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_meta_area_head : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">&Q5'Q2'6':&A&R0r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_meta_area_head : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">&Q5'Q2'6':&H&R0r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_head_set_meta_area_head : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "<&Q5'Q2'6&I&R0r2r1%3221%511%73914pU691pV6;1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_tail_set_meta_area_head : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=&Q5'Q2'6&J&R0r2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_areas_set_meta_area_head : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=&Q5'Q2'6&B&R0r2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_active_set_meta_area_head : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "C&Q5'Q2'6'RN':&S1&RJ&;%544321&?&R0r2r1%3221%511%613%>3821pU6@1pV6B1"). Proof. intros v c. reflexivity. Qed.
Lemma c_usage_set_meta_area_head : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B&Q5'Q2'6'RN':&S1&RJ%443213&O&R0r2r1%3221%511%613%=3821pU6?1pV6A1"). Proof. intros v c. reflexivity. Qed.
Lemma c_unmap_seq_set_meta_area_head : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B&Q5'Q2'6'RN':&S1&RJ%443213&N&R0r2r1%3221%511%613%=3821pU6?1pV6A1"). Proof. intros v c. reflexivity. Qed.
Lemma c_bounces_set_meta_area_head : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B&Q5'Q2'6'RN':&S1&RJ%443213&D&R0r2r1%3221%511%613%=3821pU6?1pV6A1"). Proof. intros v c. reflexivity. Qed.
Lemma c_seq_set_meta_area_head : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">&Q5'Q2'6':&M&R0r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_brk_set_meta_area_head : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">&Q5'Q2'6'>&E&R0r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_secret_set_meta_area_tail : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">&Q5'Q2'6':&L&R1r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_init_done_set_meta_area_tail : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">&Q5'Q2'6':&G&R1r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_mmap_counter_set_meta_area_tail : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">&Q5'Q2'6':&K&R1r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_free_meta_head_set_meta_area_tail : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=&Q5'Q2'6&F&R1r2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_set_meta_area_tail : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=&Q5'Q2'6&@&R1r2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_count_set_meta_area_tail : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">&Q5'Q2'6':&C&R1r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_meta_area_tail : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">&Q5'Q2'6':&A&R1r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_meta_area_tail : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">&Q5'Q2'6':&H&R1r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_head_set_meta_area_tail : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=&Q5'Q2'6&I&R1r2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_tail_set_meta_area_tail : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "<&Q5'Q2'6&J&R1r2r1%3221%511%73914pU691pV6;1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_areas_set_meta_area_tail : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=&Q5'Q2'6&B&R1r2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_active_set_meta_area_tail : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "C&Q5'Q2'6'RN':&S1&RJ&;%544321&?&R1r2r1%3221%511%613%>3821pU6@1pV6B1"). Proof. intros v c. reflexivity. Qed.
Lemma c_usage_set_meta_area_tail : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B&Q5'Q2'6'RN':&S1&RJ%443213&O&R1r2r1%3221%511%613%=3821pU6?1pV6A1"). Proof. intros v c. reflexivity. Qed.
Lemma c_unmap_seq_set_meta_area_tail : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B&Q5'Q2'6'RN':&S1&RJ%443213&N&R1r2r1%3221%511%613%=3821pU6?1pV6A1"). Proof. intros v c. reflexivity. Qed.
Lemma c_bounces_set_meta_area_tail : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B&Q5'Q2'6'RN':&S1&RJ%443213&D&R1r2r1%3221%511%613%=3821pU6?1pV6A1"). Proof. intros v c. reflexivity. Qed.
Lemma c_seq_set_meta_area_tail : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">&Q5'Q2'6':&M&R1r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_brk_set_meta_area_tail : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">&Q5'Q2'6'>&E&R1r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_secret_set_avail_meta_areas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">&Q5'Q2'6':&L&QHr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_init_done_set_avail_meta_areas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">&Q5'Q2'6':&G&QHr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_mmap_counter_set_avail_meta_areas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">&Q5'Q2'6':&K&QHr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_free_meta_head_set_avail_meta_areas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=&Q5'Q2'6&F&QHr2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_set_avail_meta_areas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=&Q5'Q2'6&@&QHr2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_count_set_avail_meta_areas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">&Q5'Q2'6':&C&QHr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_avail_meta_areas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">&Q5'Q2'6':&A&QHr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_avail_meta_areas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">&Q5'Q2'6':&H&QHr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_head_set_avail_meta_areas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=&Q5'Q2'6&I&QHr2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_tail_set_avail_meta_areas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=&Q5'Q2'6&J&QHr2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_areas_set_avail_meta_areas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "<&Q5'Q2'6&B&QHr2r1%3221%511%73914pU691pV6;1"). Proof. intros v c. reflexivity. Qed.
Lemma c_active_set_avail_meta_areas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "C&Q5'Q2'6'RN':&S1&RJ&;%544321&?&QHr2r1%3221%511%613%>3821pU6@1pV6B1"). Proof. intros v c. reflexivity. Qed.
Lemma c_usage_set_avail_meta_areas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B&Q5'Q2'6'RN':&S1&RJ%443213&O&QHr2r1%3221%511%613%=3821pU6?1pV6A1"). Proof. intros v c. reflexivity. Qed.
Lemma c_unmap_seq_set_avail_meta_areas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B&Q5'Q2'6'RN':&S1&RJ%443213&N&QHr2r1%3221%511%613%=3821pU6?1pV6A1"). Proof. intros v c. reflexivity. Qed.
Lemma c_bounces_set_avail_meta_areas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B&Q5'Q2'6'RN':&S1&RJ%443213&D&QHr2r1%3221%511%613%=3821pU6?1pV6A1"). Proof. intros v c. reflexivity. Qed.
Lemma c_seq_set_avail_meta_areas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">&Q5'Q2'6':&M&QHr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_brk_set_avail_meta_areas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">&Q5'Q2'6'>&E&QHr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_secret_set_active_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B'RN':&S1&RJ&;%544321'Q2'6&L&QDr2r1%3221%511%613%83>21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_init_done_set_active_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B'RN':&S1&RJ&;%544321'Q2'6&G&QDr2r1%3221%511%613%83>21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_mmap_counter_set_active_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B'RN':&S1&RJ&;%544321'Q2'6&K&QDr2r1%3221%511%613%83>21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_free_meta_head_set_active_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "C'RN':&S1&RJ&;%544321'Q2'6&Q5&F&QDr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_set_active_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "C'RN':&S1&RJ&;%544321'Q2'6&Q5&@&QDr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_count_set_active_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B'RN':&S1&RJ&;%544321'Q2'6&C&QDr2r1%3221%511%613%83>21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_active_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B'RN':&S1&RJ&;%544321'Q2'6&A&QDr2r1%3221%511%613%83>21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_active_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B'RN':&S1&RJ&;%544321'Q2'6&H&QDr2r1%3221%511%613%83>21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_head_set_active_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "C'RN':&S1&RJ&;%544321'Q2'6&Q5&I&QDr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_tail_set_active_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "C'RN':&S1&RJ&;%544321'Q2'6&Q5&J&QDr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_areas_set_active_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "C'RN':&S1&RJ&;%544321'Q2'6&Q5&B&QDr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_active_set_active_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A'RN':&S1&RJ&;%544321'Q2'6&?&QDr2r1%3221%511%73914pU691pV6;1"). Proof. intros v c. reflexivity. Qed.
Lemma c_usage_set_active_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "C'RN':&S1&RJ&;%544321'Q2'6%847657&O&QDr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_unmap_seq_set_active_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "C'RN':&S1&RJ&;%544321'Q2'6%847657&N&QDr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_bounces_set_active_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "C'RN':&S1&RJ&;%544321'Q2'6%847657&D&QDr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_seq_set_active_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B'RN':&S1&RJ&;%544321'Q2'6&M&QDr2r1%3221%511%613%83>21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_brk_set_active_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "C'RN':&S1&RJ&;%544321'Q2'6'>&E&QDr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_secret_set_usage_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A'RN':&S1&RJ%443213'Q2'6&L&R<r2r1%3221%511%613%83=21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_init_done_set_usage_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A'RN':&S1&RJ%443213'Q2'6&G&R<r2r1%3221%511%613%83=21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_mmap_counter_set_usage_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A'RN':&S1&RJ%443213'Q2'6&K&R<r2r1%3221%511%613%83=21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_free_meta_head_set_usage_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B'RN':&S1&RJ%443213'Q2'6&Q5&F&R<r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_set_usage_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B'RN':&S1&RJ%443213'Q2'6&Q5&@&R<r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_count_set_usage_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A'RN':&S1&RJ%443213'Q2'6&C&R<r2r1%3221%511%613%83=21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_usage_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A'RN':&S1&RJ%443213'Q2'6&A&R<r2r1%3221%511%613%83=21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_usage_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A'RN':&S1&RJ%443213'Q2'6&H&R<r2r1%3221%511%613%83=21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_head_set_usage_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B'RN':&S1&RJ%443213'Q2'6&Q5&I&R<r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_tail_set_usage_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B'RN':&S1&RJ%443213'Q2'6&Q5&J&R<r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_areas_set_usage_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B'RN':&S1&RJ%443213'Q2'6&Q5&B&R<r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_active_set_usage_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "C'RN':&S1&RJ%443213'Q2'6&;%847651&?&R<r2r1%3221%511%613%:3821pU6<1pV6>1"). Proof. intros v c. reflexivity. Qed.
Lemma c_usage_set_usage_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "@'RN':&S1&RJ%443213'Q2'6&O&R<r2r1%3221%511%73914pU691pV6;1"). Proof. intros v c. reflexivity. Qed.
Lemma c_unmap_seq_set_usage_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A'RN':&S1&RJ%443213'Q2'6&N&R<r2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_bounces_set_usage_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A'RN':&S1&RJ%443213'Q2'6&D&R<r2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_seq_set_usage_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A'RN':&S1&RJ%443213'Q2'6&M&R<r2r1%3221%511%613%83=21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_brk_set_usage_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B'RN':&S1&RJ%443213'Q2'6'>&E&R<r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_secret_set_unmap_seq_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A'RN':&S1&RJ%443213'Q2'6&L&R;r2r1%3221%511%613%83=21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_init_done_set_unmap_seq_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A'RN':&S1&RJ%443213'Q2'6&G&R;r2r1%3221%511%613%83=21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_mmap_counter_set_unmap_seq_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A'RN':&S1&RJ%443213'Q2'6&K&R;r2r1%3221%511%613%83=21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_free_meta_head_set_unmap_seq_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B'RN':&S1&RJ%443213'Q2'6&Q5&F&R;r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_set_unmap_seq_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B'RN':&S1&RJ%443213'Q2'6&Q5&@&R;r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_count_set_unmap_seq_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A'RN':&S1&RJ%443213'Q2'6&C&R;r2r1%3221%511%613%83=21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_unmap_seq_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A'RN':&S1&RJ%443213'Q2'6&A&R;r2r1%3221%511%613%83=21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_unmap_seq_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A'RN':&S1&RJ%443213'Q2'6&H&R;r2r1%3221%511%613%83=21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_head_set_unmap_seq_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B'RN':&S1&RJ%443213'Q2'6&Q5&I&R;r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_tail_set_unmap_seq_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B'RN':&S1&RJ%443213'Q2'6&Q5&J&R;r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_areas_set_unmap_seq_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B'RN':&S1&RJ%443213'Q2'6&Q5&B&R;r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_active_set_unmap_seq_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "C'RN':&S1&RJ%443213'Q2'6&;%847651&?&R;r2r1%3221%511%613%:3821pU6<1pV6>1"). Proof. intros v c. reflexivity. Qed.
Lemma c_usage_set_unmap_seq_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A'RN':&S1&RJ%443213'Q2'6&O&R;r2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_unmap_seq_set_unmap_seq_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "@'RN':&S1&RJ%443213'Q2'6&N&R;r2r1%3221%511%73914pU691pV6;1"). Proof. intros v c. reflexivity. Qed.
Lemma c_bounces_set_unmap_seq_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A'RN':&S1&RJ%443213'Q2'6&D&R;r2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_seq_set_unmap_seq_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A'RN':&S1&RJ%443213'Q2'6&M&R;r2r1%3221%511%613%83=21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_brk_set_unmap_seq_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B'RN':&S1&RJ%443213'Q2'6'>&E&R;r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_secret_set_bounces_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A'RN':&S1&RJ%443213'Q2'6&L&QJr2r1%3221%511%613%83=21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_init_done_set_bounces_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A'RN':&S1&RJ%443213'Q2'6&G&QJr2r1%3221%511%613%83=21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_mmap_counter_set_bounces_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A'RN':&S1&RJ%443213'Q2'6&K&QJr2r1%3221%511%613%83=21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_free_meta_head_set_bounces_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B'RN':&S1&RJ%443213'Q2'6&Q5&F&QJr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_set_bounces_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B'RN':&S1&RJ%443213'Q2'6&Q5&@&QJr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_count_set_bounces_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A'RN':&S1&RJ%443213'Q2'6&C&QJr2r1%3221%511%613%83=21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_bounces_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A'RN':&S1&RJ%443213'Q2'6&A&QJr2r1%3221%511%613%83=21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_bounces_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A'RN':&S1&RJ%443213'Q2'6&H&QJr2r1%3221%511%613%83=21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_head_set_bounces_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B'RN':&S1&RJ%443213'Q2'6&Q5&I&QJr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_tail_set_bounces_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B'RN':&S1&RJ%443213'Q2'6&Q5&J&QJr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_areas_set_bounces_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B'RN':&S1&RJ%443213'Q2'6&Q5&B&QJr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_active_set_bounces_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "C'RN':&S1&RJ%443213'Q2'6&;%847651&?&QJr2r1%3221%511%613%:3821pU6<1pV6>1"). Proof. intros v c. reflexivity. Qed.
Lemma c_usage_set_bounces_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A'RN':&S1&RJ%443213'Q2'6&O&QJr2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_unmap_seq_set_bounces_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A'RN':&S1&RJ%443213'Q2'6&N&QJr2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_bounces_set_bounces_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "@'RN':&S1&RJ%443213'Q2'6&D&QJr2r1%3221%511%73914pU691pV6;1"). Proof. intros v c. reflexivity. Qed.
Lemma c_seq_set_bounces_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A'RN':&S1&RJ%443213'Q2'6&M&QJr2r1%3221%511%613%83=21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_brk_set_bounces_map : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B'RN':&S1&RJ%443213'Q2'6'>&E&QJr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_secret_set_seq : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=':'Q2'6&L&R7r2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_init_done_set_seq : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=':'Q2'6&G&R7r2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_mmap_counter_set_seq : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=':'Q2'6&K&R7r2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_free_meta_head_set_seq : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">':'Q2'6&Q5&F&R7r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_set_seq : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">':'Q2'6&Q5&@&R7r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_count_set_seq : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=':'Q2'6&C&R7r2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_seq : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=':'Q2'6&A&R7r2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_seq : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "=':'Q2'6&H&R7r2r1%3221%511%613%83:21pU6:1pV6<1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_head_set_seq : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">':'Q2'6&Q5&I&R7r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_tail_set_seq : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">':'Q2'6&Q5&J&R7r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_areas_set_seq : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">':'Q2'6&Q5&B&R7r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_active_set_seq : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B':'Q2'6'RN&S1&RJ&;%447321&?&R7r2r1%3221%511%613%=3821pU6?1pV6A1"). Proof. intros v c. reflexivity. Qed.
Lemma c_usage_set_seq : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A':'Q2'6'RN&S1&RJ%346216&O&R7r2r1%3221%511%613%<3821pU6>1pV6@1"). Proof. intros v c. reflexivity. Qed.
Lemma c_unmap_seq_set_seq : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A':'Q2'6'RN&S1&RJ%346216&N&R7r2r1%3221%511%613%<3821pU6>1pV6@1"). Proof. intros v c. reflexivity. Qed.
Lemma c_bounces_set_seq : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "A':'Q2'6'RN&S1&RJ%346216&D&R7r2r1%3221%511%613%<3821pU6>1pV6@1"). Proof. intros v c. reflexivity. Qed.
Lemma c_seq_set_seq : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "<':'Q2'6&M&R7r2r1%3221%511%73914pU691pV6;1"). Proof. intros v c. reflexivity. Qed.
Lemma c_brk_set_seq : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">':'Q2'6'>&E&R7r2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_secret_set_brk : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">'>'Q2'6':&L&QKr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_init_done_set_brk : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">'>'Q2'6':&G&QKr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_mmap_counter_set_brk : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">'>'Q2'6':&K&QKr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_free_meta_head_set_brk : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">'>'Q2'6&Q5&F&QKr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_set_brk : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">'>'Q2'6&Q5&@&QKr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_count_set_brk : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">'>'Q2'6':&C&QKr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_brk : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">'>'Q2'6':&A&QKr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_brk : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">'>'Q2'6':&H&QKr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_head_set_brk : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">'>'Q2'6&Q5&I&QKr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_meta_area_tail_set_brk : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">'>'Q2'6&Q5&J&QKr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_avail_meta_areas_set_brk : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">'>'Q2'6&Q5&B&QKr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_active_set_brk : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "C'>'Q2'6'RN':&S1&RJ&;%544321&?&QKr2r1%3221%511%613%>3821pU6@1pV6B1"). Proof. intros v c. reflexivity. Qed.
Lemma c_usage_set_brk : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B'>'Q2'6'RN':&S1&RJ%443213&O&QKr2r1%3221%511%613%=3821pU6?1pV6A1"). Proof. intros v c. reflexivity. Qed.
Lemma c_unmap_seq_set_brk : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B'>'Q2'6'RN':&S1&RJ%443213&N&QKr2r1%3221%511%613%=3821pU6?1pV6A1"). Proof. intros v c. reflexivity. Qed.
Lemma c_bounces_set_brk : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "B'>'Q2'6'RN':&S1&RJ%443213&D&QKr2r1%3221%511%613%=3821pU6?1pV6A1"). Proof. intros v c. reflexivity. Qed.
Lemma c_seq_set_brk : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit ">'>'Q2'6':&M&QKr2r1%3221%511%613%93821pU6;1pV6=1"). Proof. intros v c. reflexivity. Qed.
Lemma c_brk_set_brk : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Kit "<'>'Q2'6&E&QKr2r1%3221%511%73914pU691pV6;1"). Proof. intros v c. reflexivity. Qed.
End CEIL_WRAP_3.
#[export] Hint Rewrite s_ctx_upd_ctx s_regions_upd_ctx s_shadow_upd_ctx s_next_rid_upd_ctx s_metas_upd_ctx s_areas_upd_ctx s_groups_upd_ctx s_slots_upd_ctx s_tick_upd_ctx s_secret_upd_ctx s_reserved_upd_ctx s_ctx_set_regions s_regions_set_regions s_shadow_set_regions s_next_rid_set_regions s_metas_set_regions s_areas_set_regions s_groups_set_regions s_slots_set_regions s_tick_set_regions s_secret_set_regions s_reserved_set_regions s_ctx_set_shadow s_regions_set_shadow s_shadow_set_shadow s_next_rid_set_shadow s_metas_set_shadow s_areas_set_shadow s_groups_set_shadow s_slots_set_shadow s_tick_set_shadow s_secret_set_shadow s_reserved_set_shadow s_ctx_set_next_rid s_regions_set_next_rid s_shadow_set_next_rid s_next_rid_set_next_rid s_metas_set_next_rid s_areas_set_next_rid s_groups_set_next_rid s_slots_set_next_rid s_tick_set_next_rid s_secret_set_next_rid s_reserved_set_next_rid s_ctx_set_metas s_regions_set_metas s_shadow_set_metas s_next_rid_set_metas s_metas_set_metas s_areas_set_metas s_groups_set_metas s_slots_set_metas s_tick_set_metas s_secret_set_metas s_reserved_set_metas s_ctx_set_areas s_regions_set_areas s_shadow_set_areas s_next_rid_set_areas s_metas_set_areas s_areas_set_areas s_groups_set_areas s_slots_set_areas s_tick_set_areas s_secret_set_areas s_reserved_set_areas s_ctx_set_groups s_regions_set_groups s_shadow_set_groups s_next_rid_set_groups s_metas_set_groups s_areas_set_groups s_groups_set_groups s_slots_set_groups s_tick_set_groups s_secret_set_groups s_reserved_set_groups s_ctx_set_slots s_regions_set_slots s_shadow_set_slots s_next_rid_set_slots s_metas_set_slots s_areas_set_slots s_groups_set_slots s_slots_set_slots s_tick_set_slots s_secret_set_slots s_reserved_set_slots s_ctx_set_tick s_regions_set_tick s_shadow_set_tick s_next_rid_set_tick s_metas_set_tick s_areas_set_tick s_groups_set_tick s_slots_set_tick s_tick_set_tick s_secret_set_tick s_reserved_set_tick c_secret_set_secret c_init_done_set_secret c_mmap_counter_set_secret c_free_meta_head_set_secret c_avail_meta_set_secret c_avail_meta_count_set_secret c_avail_meta_area_count_set_secret c_meta_alloc_shift_set_secret c_meta_area_head_set_secret c_meta_area_tail_set_secret c_avail_meta_areas_set_secret c_active_set_secret c_usage_set_secret c_unmap_seq_set_secret c_bounces_set_secret c_seq_set_secret c_brk_set_secret c_secret_set_init_done c_init_done_set_init_done c_mmap_counter_set_init_done c_free_meta_head_set_init_done c_avail_meta_set_init_done c_avail_meta_count_set_init_done c_avail_meta_area_count_set_init_done c_meta_alloc_shift_set_init_done c_meta_area_head_set_init_done c_meta_area_tail_set_init_done c_avail_meta_areas_set_init_done c_active_set_init_done c_usage_set_init_done c_unmap_seq_set_init_done c_bounces_set_init_done c_seq_set_init_done c_brk_set_init_done c_secret_set_mmap_counter c_init_done_set_mmap_counter c_mmap_counter_set_mmap_counter c_free_meta_head_set_mmap_counter c_avail_meta_set_mmap_counter c_avail_meta_count_set_mmap_counter c_avail_meta_area_count_set_mmap_counter c_meta_alloc_shift_set_mmap_counter c_meta_area_head_set_mmap_counter c_meta_area_tail_set_mmap_counter c_avail_meta_areas_set_mmap_counter c_active_set_mmap_counter c_usage_set_mmap_counter c_unmap_seq_set_mmap_counter c_bounces_set_mmap_counter c_seq_set_mmap_counter c_brk_set_mmap_counter c_secret_set_free_meta_head c_init_done_set_free_meta_head c_mmap_counter_set_free_meta_head c_free_meta_head_set_free_meta_head c_avail_meta_set_free_meta_head c_avail_meta_count_set_free_meta_head c_avail_meta_area_count_set_free_meta_head c_meta_alloc_shift_set_free_meta_head c_meta_area_head_set_free_meta_head c_meta_area_tail_set_free_meta_head c_avail_meta_areas_set_free_meta_head c_active_set_free_meta_head c_usage_set_free_meta_head c_unmap_seq_set_free_meta_head c_bounces_set_free_meta_head c_seq_set_free_meta_head c_brk_set_free_meta_head c_secret_set_avail_meta c_init_done_set_avail_meta c_mmap_counter_set_avail_meta c_free_meta_head_set_avail_meta c_avail_meta_set_avail_meta c_avail_meta_count_set_avail_meta c_avail_meta_area_count_set_avail_meta c_meta_alloc_shift_set_avail_meta c_meta_area_head_set_avail_meta c_meta_area_tail_set_avail_meta c_avail_meta_areas_set_avail_meta c_active_set_avail_meta c_usage_set_avail_meta c_unmap_seq_set_avail_meta c_bounces_set_avail_meta c_seq_set_avail_meta c_brk_set_avail_meta c_secret_set_avail_meta_count c_init_done_set_avail_meta_count c_mmap_counter_set_avail_meta_count c_free_meta_head_set_avail_meta_count c_avail_meta_set_avail_meta_count c_avail_meta_count_set_avail_meta_count c_avail_meta_area_count_set_avail_meta_count c_meta_alloc_shift_set_avail_meta_count c_meta_area_head_set_avail_meta_count c_meta_area_tail_set_avail_meta_count c_avail_meta_areas_set_avail_meta_count c_active_set_avail_meta_count c_usage_set_avail_meta_count c_unmap_seq_set_avail_meta_count c_bounces_set_avail_meta_count c_seq_set_avail_meta_count c_brk_set_avail_meta_count c_secret_set_avail_meta_area_count c_init_done_set_avail_meta_area_count c_mmap_counter_set_avail_meta_area_count c_free_meta_head_set_avail_meta_area_count c_avail_meta_set_avail_meta_area_count c_avail_meta_count_set_avail_meta_area_count c_avail_meta_area_count_set_avail_meta_area_count c_meta_alloc_shift_set_avail_meta_area_count c_meta_area_head_set_avail_meta_area_count c_meta_area_tail_set_avail_meta_area_count c_avail_meta_areas_set_avail_meta_area_count c_active_set_avail_meta_area_count c_usage_set_avail_meta_area_count c_unmap_seq_set_avail_meta_area_count c_bounces_set_avail_meta_area_count c_seq_set_avail_meta_area_count c_brk_set_avail_meta_area_count c_secret_set_meta_alloc_shift c_init_done_set_meta_alloc_shift c_mmap_counter_set_meta_alloc_shift c_free_meta_head_set_meta_alloc_shift c_avail_meta_set_meta_alloc_shift c_avail_meta_count_set_meta_alloc_shift c_avail_meta_area_count_set_meta_alloc_shift c_meta_alloc_shift_set_meta_alloc_shift c_meta_area_head_set_meta_alloc_shift c_meta_area_tail_set_meta_alloc_shift c_avail_meta_areas_set_meta_alloc_shift c_active_set_meta_alloc_shift c_usage_set_meta_alloc_shift c_unmap_seq_set_meta_alloc_shift c_bounces_set_meta_alloc_shift c_seq_set_meta_alloc_shift c_brk_set_meta_alloc_shift c_secret_set_meta_area_head c_init_done_set_meta_area_head c_mmap_counter_set_meta_area_head c_free_meta_head_set_meta_area_head c_avail_meta_set_meta_area_head c_avail_meta_count_set_meta_area_head c_avail_meta_area_count_set_meta_area_head c_meta_alloc_shift_set_meta_area_head c_meta_area_head_set_meta_area_head c_meta_area_tail_set_meta_area_head c_avail_meta_areas_set_meta_area_head c_active_set_meta_area_head c_usage_set_meta_area_head c_unmap_seq_set_meta_area_head c_bounces_set_meta_area_head c_seq_set_meta_area_head c_brk_set_meta_area_head c_secret_set_meta_area_tail c_init_done_set_meta_area_tail c_mmap_counter_set_meta_area_tail c_free_meta_head_set_meta_area_tail c_avail_meta_set_meta_area_tail c_avail_meta_count_set_meta_area_tail c_avail_meta_area_count_set_meta_area_tail c_meta_alloc_shift_set_meta_area_tail c_meta_area_head_set_meta_area_tail c_meta_area_tail_set_meta_area_tail c_avail_meta_areas_set_meta_area_tail c_active_set_meta_area_tail c_usage_set_meta_area_tail c_unmap_seq_set_meta_area_tail c_bounces_set_meta_area_tail c_seq_set_meta_area_tail c_brk_set_meta_area_tail c_secret_set_avail_meta_areas c_init_done_set_avail_meta_areas c_mmap_counter_set_avail_meta_areas c_free_meta_head_set_avail_meta_areas c_avail_meta_set_avail_meta_areas c_avail_meta_count_set_avail_meta_areas c_avail_meta_area_count_set_avail_meta_areas c_meta_alloc_shift_set_avail_meta_areas c_meta_area_head_set_avail_meta_areas c_meta_area_tail_set_avail_meta_areas c_avail_meta_areas_set_avail_meta_areas c_active_set_avail_meta_areas c_usage_set_avail_meta_areas c_unmap_seq_set_avail_meta_areas c_bounces_set_avail_meta_areas c_seq_set_avail_meta_areas c_brk_set_avail_meta_areas c_secret_set_active_map c_init_done_set_active_map c_mmap_counter_set_active_map c_free_meta_head_set_active_map c_avail_meta_set_active_map c_avail_meta_count_set_active_map c_avail_meta_area_count_set_active_map c_meta_alloc_shift_set_active_map c_meta_area_head_set_active_map c_meta_area_tail_set_active_map c_avail_meta_areas_set_active_map c_active_set_active_map c_usage_set_active_map c_unmap_seq_set_active_map c_bounces_set_active_map c_seq_set_active_map c_brk_set_active_map c_secret_set_usage_map c_init_done_set_usage_map c_mmap_counter_set_usage_map c_free_meta_head_set_usage_map c_avail_meta_set_usage_map c_avail_meta_count_set_usage_map c_avail_meta_area_count_set_usage_map c_meta_alloc_shift_set_usage_map c_meta_area_head_set_usage_map c_meta_area_tail_set_usage_map c_avail_meta_areas_set_usage_map c_active_set_usage_map c_usage_set_usage_map c_unmap_seq_set_usage_map c_bounces_set_usage_map c_seq_set_usage_map c_brk_set_usage_map c_secret_set_unmap_seq_map c_init_done_set_unmap_seq_map c_mmap_counter_set_unmap_seq_map c_free_meta_head_set_unmap_seq_map c_avail_meta_set_unmap_seq_map c_avail_meta_count_set_unmap_seq_map c_avail_meta_area_count_set_unmap_seq_map c_meta_alloc_shift_set_unmap_seq_map c_meta_area_head_set_unmap_seq_map c_meta_area_tail_set_unmap_seq_map c_avail_meta_areas_set_unmap_seq_map c_active_set_unmap_seq_map c_usage_set_unmap_seq_map c_unmap_seq_set_unmap_seq_map c_bounces_set_unmap_seq_map c_seq_set_unmap_seq_map c_brk_set_unmap_seq_map c_secret_set_bounces_map c_init_done_set_bounces_map c_mmap_counter_set_bounces_map c_free_meta_head_set_bounces_map c_avail_meta_set_bounces_map c_avail_meta_count_set_bounces_map c_avail_meta_area_count_set_bounces_map c_meta_alloc_shift_set_bounces_map c_meta_area_head_set_bounces_map c_meta_area_tail_set_bounces_map c_avail_meta_areas_set_bounces_map c_active_set_bounces_map c_usage_set_bounces_map c_unmap_seq_set_bounces_map c_bounces_set_bounces_map c_seq_set_bounces_map c_brk_set_bounces_map c_secret_set_seq c_init_done_set_seq c_mmap_counter_set_seq c_free_meta_head_set_seq c_avail_meta_set_seq c_avail_meta_count_set_seq c_avail_meta_area_count_set_seq c_meta_alloc_shift_set_seq c_meta_area_head_set_seq c_meta_area_tail_set_seq c_avail_meta_areas_set_seq c_active_set_seq c_usage_set_seq c_unmap_seq_set_seq c_bounces_set_seq c_seq_set_seq c_brk_set_seq c_secret_set_brk c_init_done_set_brk c_mmap_counter_set_brk c_free_meta_head_set_brk c_avail_meta_set_brk c_avail_meta_count_set_brk c_avail_meta_area_count_set_brk c_meta_alloc_shift_set_brk c_meta_area_head_set_brk c_meta_area_tail_set_brk c_avail_meta_areas_set_brk c_active_set_brk c_usage_set_brk c_unmap_seq_set_brk c_bounces_set_brk c_seq_set_brk c_brk_set_brk : mst.
Section CEIL_WRAP_4.
Context {RUNp : RunP}.
Lemma s_regions_set_active sc v st : s_regions (set_active sc v st) = s_regions st. Proof. reflexivity. Qed.
Lemma s_shadow_set_active sc v st : s_shadow (set_active sc v st) = s_shadow st. Proof. reflexivity. Qed.
Lemma s_next_rid_set_active sc v st : s_next_rid (set_active sc v st) = s_next_rid st. Proof. reflexivity. Qed.
Lemma s_metas_set_active sc v st : s_metas (set_active sc v st) = s_metas st. Proof. reflexivity. Qed.
Lemma s_areas_set_active sc v st : s_areas (set_active sc v st) = s_areas st. Proof. reflexivity. Qed.
Lemma s_groups_set_active sc v st : s_groups (set_active sc v st) = s_groups st. Proof. reflexivity. Qed.
Lemma s_slots_set_active sc v st : s_slots (set_active sc v st) = s_slots st. Proof. reflexivity. Qed.
Lemma s_tick_set_active sc v st : s_tick (set_active sc v st) = s_tick st. Proof. reflexivity. Qed.
Lemma s_secret_set_active sc v st : s_secret (set_active sc v st) = s_secret st. Proof. reflexivity. Qed.
Lemma s_reserved_set_active sc v st : s_reserved (set_active sc v st) = s_reserved st. Proof. reflexivity. Qed.
Lemma s_regions_set_usage sc v st : s_regions (set_usage sc v st) = s_regions st. Proof. reflexivity. Qed.
Lemma s_shadow_set_usage sc v st : s_shadow (set_usage sc v st) = s_shadow st. Proof. reflexivity. Qed.
Lemma s_next_rid_set_usage sc v st : s_next_rid (set_usage sc v st) = s_next_rid st. Proof. reflexivity. Qed.
Lemma s_metas_set_usage sc v st : s_metas (set_usage sc v st) = s_metas st. Proof. reflexivity. Qed.
Lemma s_areas_set_usage sc v st : s_areas (set_usage sc v st) = s_areas st. Proof. reflexivity. Qed.
Lemma s_groups_set_usage sc v st : s_groups (set_usage sc v st) = s_groups st. Proof. reflexivity. Qed.
Lemma s_slots_set_usage sc v st : s_slots (set_usage sc v st) = s_slots st. Proof. reflexivity. Qed.
Lemma s_tick_set_usage sc v st : s_tick (set_usage sc v st) = s_tick st. Proof. reflexivity. Qed.
Lemma s_secret_set_usage sc v st : s_secret (set_usage sc v st) = s_secret st. Proof. reflexivity. Qed.
Lemma s_reserved_set_usage sc v st : s_reserved (set_usage sc v st) = s_reserved st. Proof. reflexivity. Qed.
Lemma s_regions_set_bounce i v st : s_regions (set_bounce i v st) = s_regions st. Proof. reflexivity. Qed.
Lemma s_shadow_set_bounce i v st : s_shadow (set_bounce i v st) = s_shadow st. Proof. reflexivity. Qed.
Lemma s_next_rid_set_bounce i v st : s_next_rid (set_bounce i v st) = s_next_rid st. Proof. reflexivity. Qed.
Lemma s_metas_set_bounce i v st : s_metas (set_bounce i v st) = s_metas st. Proof. reflexivity. Qed.
Lemma s_areas_set_bounce i v st : s_areas (set_bounce i v st) = s_areas st. Proof. reflexivity. Qed.
Lemma s_groups_set_bounce i v st : s_groups (set_bounce i v st) = s_groups st. Proof. reflexivity. Qed.
Lemma s_slots_set_bounce i v st : s_slots (set_bounce i v st) = s_slots st. Proof. reflexivity. Qed.
Lemma s_tick_set_bounce i v st : s_tick (set_bounce i v st) = s_tick st. Proof. reflexivity. Qed.
Lemma s_secret_set_bounce i v st : s_secret (set_bounce i v st) = s_secret st. Proof. reflexivity. Qed.
Lemma s_reserved_set_bounce i v st : s_reserved (set_bounce i v st) = s_reserved st. Proof. reflexivity. Qed.
Lemma s_ctx_put_meta m r st : s_ctx (put_meta m r st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_regions_put_meta m r st : s_regions (put_meta m r st) = s_regions st. Proof. reflexivity. Qed.
Lemma s_shadow_put_meta m r st : s_shadow (put_meta m r st) = s_shadow st. Proof. reflexivity. Qed.
Lemma s_next_rid_put_meta m r st : s_next_rid (put_meta m r st) = s_next_rid st. Proof. reflexivity. Qed.
Lemma s_areas_put_meta m r st : s_areas (put_meta m r st) = s_areas st. Proof. reflexivity. Qed.
Lemma s_groups_put_meta m r st : s_groups (put_meta m r st) = s_groups st. Proof. reflexivity. Qed.
Lemma s_slots_put_meta m r st : s_slots (put_meta m r st) = s_slots st. Proof. reflexivity. Qed.
Lemma s_tick_put_meta m r st : s_tick (put_meta m r st) = s_tick st. Proof. reflexivity. Qed.
Lemma s_secret_put_meta m r st : s_secret (put_meta m r st) = s_secret st. Proof. reflexivity. Qed.
Lemma s_reserved_put_meta m r st : s_reserved (put_meta m r st) = s_reserved st. Proof. reflexivity. Qed.
Lemma s_ctx_upd_meta m f st : s_ctx (upd_meta m f st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_regions_upd_meta m f st : s_regions (upd_meta m f st) = s_regions st. Proof. reflexivity. Qed.
Lemma s_shadow_upd_meta m f st : s_shadow (upd_meta m f st) = s_shadow st. Proof. reflexivity. Qed.
Lemma s_next_rid_upd_meta m f st : s_next_rid (upd_meta m f st) = s_next_rid st. Proof. reflexivity. Qed.
Lemma s_areas_upd_meta m f st : s_areas (upd_meta m f st) = s_areas st. Proof. reflexivity. Qed.
Lemma s_groups_upd_meta m f st : s_groups (upd_meta m f st) = s_groups st. Proof. reflexivity. Qed.
Lemma s_slots_upd_meta m f st : s_slots (upd_meta m f st) = s_slots st. Proof. reflexivity. Qed.
Lemma s_tick_upd_meta m f st : s_tick (upd_meta m f st) = s_tick st. Proof. reflexivity. Qed.
Lemma s_secret_upd_meta m f st : s_secret (upd_meta m f st) = s_secret st. Proof. reflexivity. Qed.
Lemma s_reserved_upd_meta m f st : s_reserved (upd_meta m f st) = s_reserved st. Proof. reflexivity. Qed.
Lemma s_ctx_put_group g mo ai st : s_ctx (put_group g mo ai st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_regions_put_group g mo ai st : s_regions (put_group g mo ai st) = s_regions st. Proof. reflexivity. Qed.
Lemma s_shadow_put_group g mo ai st : s_shadow (put_group g mo ai st) = s_shadow st. Proof. reflexivity. Qed.
Lemma s_next_rid_put_group g mo ai st : s_next_rid (put_group g mo ai st) = s_next_rid st. Proof. reflexivity. Qed.
Lemma s_metas_put_group g mo ai st : s_metas (put_group g mo ai st) = s_metas st. Proof. reflexivity. Qed.
Lemma s_areas_put_group g mo ai st : s_areas (put_group g mo ai st) = s_areas st. Proof. reflexivity. Qed.
Lemma s_slots_put_group g mo ai st : s_slots (put_group g mo ai st) = s_slots st. Proof. reflexivity. Qed.
Lemma s_tick_put_group g mo ai st : s_tick (put_group g mo ai st) = s_tick st. Proof. reflexivity. Qed.
Lemma s_secret_put_group g mo ai st : s_secret (put_group g mo ai st) = s_secret st. Proof. reflexivity. Qed.
Lemma s_reserved_put_group g mo ai st : s_reserved (put_group g mo ai st) = s_reserved st. Proof. reflexivity. Qed.
Lemma s_ctx_del_group g st : s_ctx (del_group g st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_regions_del_group g st : s_regions (del_group g st) = s_regions st. Proof. reflexivity. Qed.
Lemma s_shadow_del_group g st : s_shadow (del_group g st) = s_shadow st. Proof. reflexivity. Qed.
Lemma s_next_rid_del_group g st : s_next_rid (del_group g st) = s_next_rid st. Proof. reflexivity. Qed.
Lemma s_metas_del_group g st : s_metas (del_group g st) = s_metas st. Proof. reflexivity. Qed.
Lemma s_areas_del_group g st : s_areas (del_group g st) = s_areas st. Proof. reflexivity. Qed.
Lemma s_slots_del_group g st : s_slots (del_group g st) = s_slots st. Proof. reflexivity. Qed.
Lemma s_tick_del_group g st : s_tick (del_group g st) = s_tick st. Proof. reflexivity. Qed.
Lemma s_secret_del_group g st : s_secret (del_group g st) = s_secret st. Proof. reflexivity. Qed.
Lemma s_reserved_del_group g st : s_reserved (del_group g st) = s_reserved st. Proof. reflexivity. Qed.
Lemma s_ctx_set_group_active_idx g ai st : s_ctx (set_group_active_idx g ai st) = s_ctx st. Proof. unfold set_group_active_idx; destruct (get_group st g); reflexivity. Qed.
Lemma s_regions_set_group_active_idx g ai st : s_regions (set_group_active_idx g ai st) = s_regions st. Proof. unfold set_group_active_idx; destruct (get_group st g); reflexivity. Qed.
Lemma s_shadow_set_group_active_idx g ai st : s_shadow (set_group_active_idx g ai st) = s_shadow st. Proof. unfold set_group_active_idx; destruct (get_group st g); reflexivity. Qed.
Lemma s_next_rid_set_group_active_idx g ai st : s_next_rid (set_group_active_idx g ai st) = s_next_rid st. Proof. unfold set_group_active_idx; destruct (get_group st g); reflexivity. Qed.
Lemma s_metas_set_group_active_idx g ai st : s_metas (set_group_active_idx g ai st) = s_metas st. Proof. unfold set_group_active_idx; destruct (get_group st g); reflexivity. Qed.
Lemma s_areas_set_group_active_idx g ai st : s_areas (set_group_active_idx g ai st) = s_areas st. Proof. unfold set_group_active_idx; destruct (get_group st g); reflexivity. Qed.
Lemma s_slots_set_group_active_idx g ai st : s_slots (set_group_active_idx g ai st) = s_slots st. Proof. unfold set_group_active_idx; destruct (get_group st g); reflexivity. Qed.
Lemma s_tick_set_group_active_idx g ai st : s_tick (set_group_active_idx g ai st) = s_tick st. Proof. unfold set_group_active_idx; destruct (get_group st g); reflexivity. Qed.
Lemma s_secret_set_group_active_idx g ai st : s_secret (set_group_active_idx g ai st) = s_secret st. Proof. unfold set_group_active_idx; destruct (get_group st g); reflexivity. Qed.
Lemma s_reserved_set_group_active_idx g ai st : s_reserved (set_group_active_idx g ai st) = s_reserved st. Proof. unfold set_group_active_idx; destruct (get_group st g); reflexivity. Qed.
Lemma s_ctx_drop_region rid st : s_ctx (drop_region rid st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_next_rid_drop_region rid st : s_next_rid (drop_region rid st) = s_next_rid st. Proof. reflexivity. Qed.
Lemma s_metas_drop_region rid st : s_metas (drop_region rid st) = s_metas st. Proof. reflexivity. Qed.
Lemma s_areas_drop_region rid st : s_areas (drop_region rid st) = s_areas st. Proof. reflexivity. Qed.
Lemma s_groups_drop_region rid st : s_groups (drop_region rid st) = s_groups st. Proof. reflexivity. Qed.
Lemma s_slots_drop_region rid st : s_slots (drop_region rid st) = s_slots st. Proof. reflexivity. Qed.
Lemma s_tick_drop_region rid st : s_tick (drop_region rid st) = s_tick st. Proof. reflexivity. Qed.
Lemma s_secret_drop_region rid st : s_secret (drop_region rid st) = s_secret st. Proof. reflexivity. Qed.
Lemma s_reserved_drop_region rid st : s_reserved (drop_region rid st) = s_reserved st. Proof. reflexivity. Qed.
Lemma s_ctx_upd_region rid f st : s_ctx (upd_region rid f st) = s_ctx st. Proof. unfold upd_region; destruct (get_region st rid); reflexivity. Qed.
Lemma s_shadow_upd_region rid f st : s_shadow (upd_region rid f st) = s_shadow st. Proof. unfold upd_region; destruct (get_region st rid); reflexivity. Qed.
Lemma s_next_rid_upd_region rid f st : s_next_rid (upd_region rid f st) = s_next_rid st. Proof. unfold upd_region; destruct (get_region st rid); reflexivity. Qed.
Lemma s_metas_upd_region rid f st : s_metas (upd_region rid f st) = s_metas st. Proof. unfold upd_region; destruct (get_region st rid); reflexivity. Qed.
Lemma s_areas_upd_region rid f st : s_areas (upd_region rid f st) = s_areas st. Proof. unfold upd_region; destruct (get_region st rid); reflexivity. Qed.
Lemma s_groups_upd_region rid f st : s_groups (upd_region rid f st) = s_groups st. Proof. unfold upd_region; destruct (get_region st rid); reflexivity. Qed.
Lemma s_slots_upd_region rid f st : s_slots (upd_region rid f st) = s_slots st. Proof. unfold upd_region; destruct (get_region st rid); reflexivity. Qed.
Lemma s_tick_upd_region rid f st : s_tick (upd_region rid f st) = s_tick st. Proof. unfold upd_region; destruct (get_region st rid); reflexivity. Qed.
Lemma s_secret_upd_region rid f st : s_secret (upd_region rid f st) = s_secret st. Proof. unfold upd_region; destruct (get_region st rid); reflexivity. Qed.
Lemma s_reserved_upd_region rid f st : s_reserved (upd_region rid f st) = s_reserved st. Proof. unfold upd_region; destruct (get_region st rid); reflexivity. Qed.
Lemma s_ctx_add_slots m p stride cnt st : s_ctx (add_slots m p stride cnt st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_regions_add_slots m p stride cnt st : s_regions (add_slots m p stride cnt st) = s_regions st. Proof. reflexivity. Qed.
Lemma s_shadow_add_slots m p stride cnt st : s_shadow (add_slots m p stride cnt st) = s_shadow st. Proof. reflexivity. Qed.
Lemma s_next_rid_add_slots m p stride cnt st : s_next_rid (add_slots m p stride cnt st) = s_next_rid st. Proof. reflexivity. Qed.
Lemma s_metas_add_slots m p stride cnt st : s_metas (add_slots m p stride cnt st) = s_metas st. Proof. reflexivity. Qed.
Lemma s_areas_add_slots m p stride cnt st : s_areas (add_slots m p stride cnt st) = s_areas st. Proof. reflexivity. Qed.
Lemma s_groups_add_slots m p stride cnt st : s_groups (add_slots m p stride cnt st) = s_groups st. Proof. reflexivity. Qed.
Lemma s_tick_add_slots m p stride cnt st : s_tick (add_slots m p stride cnt st) = s_tick st. Proof. reflexivity. Qed.
Lemma s_secret_add_slots m p stride cnt st : s_secret (add_slots m p stride cnt st) = s_secret st. Proof. reflexivity. Qed.
Lemma s_reserved_add_slots m p stride cnt st : s_reserved (add_slots m p stride cnt st) = s_reserved st. Proof. reflexivity. Qed.
Lemma s_ctx_del_slots p stride cnt st : s_ctx (del_slots p stride cnt st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_regions_del_slots p stride cnt st : s_regions (del_slots p stride cnt st) = s_regions st. Proof. reflexivity. Qed.
Lemma s_shadow_del_slots p stride cnt st : s_shadow (del_slots p stride cnt st) = s_shadow st. Proof. reflexivity. Qed.
Lemma s_next_rid_del_slots p stride cnt st : s_next_rid (del_slots p stride cnt st) = s_next_rid st. Proof. reflexivity. Qed.
Lemma s_metas_del_slots p stride cnt st : s_metas (del_slots p stride cnt st) = s_metas st. Proof. reflexivity. Qed.
Lemma s_areas_del_slots p stride cnt st : s_areas (del_slots p stride cnt st) = s_areas st. Proof. reflexivity. Qed.
Lemma s_groups_del_slots p stride cnt st : s_groups (del_slots p stride cnt st) = s_groups st. Proof. reflexivity. Qed.
Lemma s_tick_del_slots p stride cnt st : s_tick (del_slots p stride cnt st) = s_tick st. Proof. reflexivity. Qed.
Lemma s_secret_del_slots p stride cnt st : s_secret (del_slots p stride cnt st) = s_secret st. Proof. reflexivity. Qed.
Lemma s_reserved_del_slots p stride cnt st : s_reserved (del_slots p stride cnt st) = s_reserved st. Proof. reflexivity. Qed.
Lemma s_ctx_upd_shadow rid f st : s_ctx (upd_shadow rid f st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_regions_upd_shadow rid f st : s_regions (upd_shadow rid f st) = s_regions st. Proof. reflexivity. Qed.
Lemma s_next_rid_upd_shadow rid f st : s_next_rid (upd_shadow rid f st) = s_next_rid st. Proof. reflexivity. Qed.
Lemma s_metas_upd_shadow rid f st : s_metas (upd_shadow rid f st) = s_metas st. Proof. reflexivity. Qed.
Lemma s_areas_upd_shadow rid f st : s_areas (upd_shadow rid f st) = s_areas st. Proof. reflexivity. Qed.
Lemma s_groups_upd_shadow rid f st : s_groups (upd_shadow rid f st) = s_groups st. Proof. reflexivity. Qed.
Lemma s_slots_upd_shadow rid f st : s_slots (upd_shadow rid f st) = s_slots st. Proof. reflexivity. Qed.
Lemma s_tick_upd_shadow rid f st : s_tick (upd_shadow rid f st) = s_tick st. Proof. reflexivity. Qed.
Lemma s_secret_upd_shadow rid f st : s_secret (upd_shadow rid f st) = s_secret st. Proof. reflexivity. Qed.
Lemma s_reserved_upd_shadow rid f st : s_reserved (upd_shadow rid f st) = s_reserved st. Proof. reflexivity. Qed.
Lemma s_ctx_wr8 p v st : s_ctx (wr8 p v st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_regions_wr8 p v st : s_regions (wr8 p v st) = s_regions st. Proof. reflexivity. Qed.
Lemma s_next_rid_wr8 p v st : s_next_rid (wr8 p v st) = s_next_rid st. Proof. reflexivity. Qed.
Lemma s_metas_wr8 p v st : s_metas (wr8 p v st) = s_metas st. Proof. reflexivity. Qed.
Lemma s_areas_wr8 p v st : s_areas (wr8 p v st) = s_areas st. Proof. reflexivity. Qed.
Lemma s_groups_wr8 p v st : s_groups (wr8 p v st) = s_groups st. Proof. reflexivity. Qed.
Lemma s_slots_wr8 p v st : s_slots (wr8 p v st) = s_slots st. Proof. reflexivity. Qed.
Lemma s_tick_wr8 p v st : s_tick (wr8 p v st) = s_tick st. Proof. reflexivity. Qed.
Lemma s_secret_wr8 p v st : s_secret (wr8 p v st) = s_secret st. Proof. reflexivity. Qed.
Lemma s_reserved_wr8 p v st : s_reserved (wr8 p v st) = s_reserved st. Proof. reflexivity. Qed.
Lemma s_ctx_wr16 p v st : s_ctx (wr16 p v st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_regions_wr16 p v st : s_regions (wr16 p v st) = s_regions st. Proof. reflexivity. Qed.
Lemma s_next_rid_wr16 p v st : s_next_rid (wr16 p v st) = s_next_rid st. Proof. reflexivity. Qed.
Lemma s_metas_wr16 p v st : s_metas (wr16 p v st) = s_metas st. Proof. reflexivity. Qed.
Lemma s_areas_wr16 p v st : s_areas (wr16 p v st) = s_areas st. Proof. reflexivity. Qed.
Lemma s_groups_wr16 p v st : s_groups (wr16 p v st) = s_groups st. Proof. reflexivity. Qed.
Lemma s_slots_wr16 p v st : s_slots (wr16 p v st) = s_slots st. Proof. reflexivity. Qed.
Lemma s_tick_wr16 p v st : s_tick (wr16 p v st) = s_tick st. Proof. reflexivity. Qed.
Lemma s_secret_wr16 p v st : s_secret (wr16 p v st) = s_secret st. Proof. reflexivity. Qed.
Lemma s_reserved_wr16 p v st : s_reserved (wr16 p v st) = s_reserved st. Proof. reflexivity. Qed.
Lemma s_ctx_wr32 p v st : s_ctx (wr32 p v st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_regions_wr32 p v st : s_regions (wr32 p v st) = s_regions st. Proof. reflexivity. Qed.
Lemma s_next_rid_wr32 p v st : s_next_rid (wr32 p v st) = s_next_rid st. Proof. reflexivity. Qed.
Lemma s_metas_wr32 p v st : s_metas (wr32 p v st) = s_metas st. Proof. reflexivity. Qed.
Lemma s_areas_wr32 p v st : s_areas (wr32 p v st) = s_areas st. Proof. reflexivity. Qed.
Lemma s_groups_wr32 p v st : s_groups (wr32 p v st) = s_groups st. Proof. reflexivity. Qed.
Lemma s_slots_wr32 p v st : s_slots (wr32 p v st) = s_slots st. Proof. reflexivity. Qed.
Lemma s_tick_wr32 p v st : s_tick (wr32 p v st) = s_tick st. Proof. reflexivity. Qed.
Lemma s_secret_wr32 p v st : s_secret (wr32 p v st) = s_secret st. Proof. reflexivity. Qed.
Lemma s_reserved_wr32 p v st : s_reserved (wr32 p v st) = s_reserved st. Proof. reflexivity. Qed.
Lemma s_ctx_havoc p n st : s_ctx (havoc p n st) = s_ctx st. Proof. unfold havoc; destruct (n <=? 0); reflexivity. Qed.
Lemma s_regions_havoc p n st : s_regions (havoc p n st) = s_regions st. Proof. unfold havoc; destruct (n <=? 0); reflexivity. Qed.
Lemma s_next_rid_havoc p n st : s_next_rid (havoc p n st) = s_next_rid st. Proof. unfold havoc; destruct (n <=? 0); reflexivity. Qed.
Lemma s_metas_havoc p n st : s_metas (havoc p n st) = s_metas st. Proof. unfold havoc; destruct (n <=? 0); reflexivity. Qed.
Lemma s_areas_havoc p n st : s_areas (havoc p n st) = s_areas st. Proof. unfold havoc; destruct (n <=? 0); reflexivity. Qed.
Lemma s_groups_havoc p n st : s_groups (havoc p n st) = s_groups st. Proof. unfold havoc; destruct (n <=? 0); reflexivity. Qed.
Lemma s_slots_havoc p n st : s_slots (havoc p n st) = s_slots st. Proof. unfold havoc; destruct (n <=? 0); reflexivity. Qed.
Lemma s_tick_havoc p n st : s_tick (havoc p n st) = s_tick st. Proof. unfold havoc; destruct (n <=? 0); reflexivity. Qed.
Lemma s_secret_havoc p n st : s_secret (havoc p n st) = s_secret st. Proof. unfold havoc; destruct (n <=? 0); reflexivity. Qed.
Lemma s_reserved_havoc p n st : s_reserved (havoc p n st) = s_reserved st. Proof. unfold havoc; destruct (n <=? 0); reflexivity. Qed.
Lemma s_ctx_hdr_havoc b st : s_ctx (hdr_havoc b st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_regions_hdr_havoc b st : s_regions (hdr_havoc b st) = s_regions st. Proof. reflexivity. Qed.
Lemma s_next_rid_hdr_havoc b st : s_next_rid (hdr_havoc b st) = s_next_rid st. Proof. reflexivity. Qed.
Lemma s_metas_hdr_havoc b st : s_metas (hdr_havoc b st) = s_metas st. Proof. reflexivity. Qed.
Lemma s_areas_hdr_havoc b st : s_areas (hdr_havoc b st) = s_areas st. Proof. reflexivity. Qed.
Lemma s_groups_hdr_havoc b st : s_groups (hdr_havoc b st) = s_groups st. Proof. reflexivity. Qed.
Lemma s_slots_hdr_havoc b st : s_slots (hdr_havoc b st) = s_slots st. Proof. reflexivity. Qed.
Lemma s_tick_hdr_havoc b st : s_tick (hdr_havoc b st) = s_tick st. Proof. reflexivity. Qed.
Lemma s_secret_hdr_havoc b st : s_secret (hdr_havoc b st) = s_secret st. Proof. reflexivity. Qed.
Lemma s_reserved_hdr_havoc b st : s_reserved (hdr_havoc b st) = s_reserved st. Proof. reflexivity. Qed.
Lemma s_regions_step_seq st : s_regions (step_seq st) = s_regions st. Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma s_shadow_step_seq st : s_shadow (step_seq st) = s_shadow st. Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma s_next_rid_step_seq st : s_next_rid (step_seq st) = s_next_rid st. Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma s_metas_step_seq st : s_metas (step_seq st) = s_metas st. Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma s_areas_step_seq st : s_areas (step_seq st) = s_areas st. Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma s_groups_step_seq st : s_groups (step_seq st) = s_groups st. Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma s_slots_step_seq st : s_slots (step_seq st) = s_slots st. Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma s_tick_step_seq st : s_tick (step_seq st) = s_tick st. Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma s_secret_step_seq st : s_secret (step_seq st) = s_secret st. Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma s_reserved_step_seq st : s_reserved (step_seq st) = s_reserved st. Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma s_regions_record_seq sc st : s_regions (record_seq sc st) = s_regions st. Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma s_shadow_record_seq sc st : s_shadow (record_seq sc st) = s_shadow st. Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma s_next_rid_record_seq sc st : s_next_rid (record_seq sc st) = s_next_rid st. Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma s_metas_record_seq sc st : s_metas (record_seq sc st) = s_metas st. Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma s_areas_record_seq sc st : s_areas (record_seq sc st) = s_areas st. Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma s_groups_record_seq sc st : s_groups (record_seq sc st) = s_groups st. Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma s_slots_record_seq sc st : s_slots (record_seq sc st) = s_slots st. Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma s_tick_record_seq sc st : s_tick (record_seq sc st) = s_tick st. Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma s_secret_record_seq sc st : s_secret (record_seq sc st) = s_secret st. Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma s_reserved_record_seq sc st : s_reserved (record_seq sc st) = s_reserved st. Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma s_regions_account_bounce sc st : s_regions (account_bounce sc st) = s_regions st. Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma s_shadow_account_bounce sc st : s_shadow (account_bounce sc st) = s_shadow st. Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma s_next_rid_account_bounce sc st : s_next_rid (account_bounce sc st) = s_next_rid st. Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma s_metas_account_bounce sc st : s_metas (account_bounce sc st) = s_metas st. Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma s_areas_account_bounce sc st : s_areas (account_bounce sc st) = s_areas st. Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma s_groups_account_bounce sc st : s_groups (account_bounce sc st) = s_groups st. Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma s_slots_account_bounce sc st : s_slots (account_bounce sc st) = s_slots st. Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma s_tick_account_bounce sc st : s_tick (account_bounce sc st) = s_tick st. Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma s_secret_account_bounce sc st : s_secret (account_bounce sc st) = s_secret st. Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma s_reserved_account_bounce sc st : s_reserved (account_bounce sc st) = s_reserved st. Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma s_regions_decay_bounces sc st : s_regions (decay_bounces sc st) = s_regions st. Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma s_shadow_decay_bounces sc st : s_shadow (decay_bounces sc st) = s_shadow st. Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma s_next_rid_decay_bounces sc st : s_next_rid (decay_bounces sc st) = s_next_rid st. Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma s_metas_decay_bounces sc st : s_metas (decay_bounces sc st) = s_metas st. Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma s_areas_decay_bounces sc st : s_areas (decay_bounces sc st) = s_areas st. Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma s_groups_decay_bounces sc st : s_groups (decay_bounces sc st) = s_groups st. Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma s_slots_decay_bounces sc st : s_slots (decay_bounces sc st) = s_slots st. Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma s_tick_decay_bounces sc st : s_tick (decay_bounces sc st) = s_tick st. Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma s_secret_decay_bounces sc st : s_secret (decay_bounces sc st) = s_secret st. Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma s_reserved_decay_bounces sc st : s_reserved (decay_bounces sc st) = s_reserved st. Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma s_regions_set_head h v st : s_regions (set_head h v st) = s_regions st. Proof. destruct h; reflexivity. Qed.
Lemma s_shadow_set_head h v st : s_shadow (set_head h v st) = s_shadow st. Proof. destruct h; reflexivity. Qed.
Lemma s_next_rid_set_head h v st : s_next_rid (set_head h v st) = s_next_rid st. Proof. destruct h; reflexivity. Qed.
Lemma s_metas_set_head h v st : s_metas (set_head h v st) = s_metas st. Proof. destruct h; reflexivity. Qed.
Lemma s_areas_set_head h v st : s_areas (set_head h v st) = s_areas st. Proof. destruct h; reflexivity. Qed.
Lemma s_groups_set_head h v st : s_groups (set_head h v st) = s_groups st. Proof. destruct h; reflexivity. Qed.
Lemma s_slots_set_head h v st : s_slots (set_head h v st) = s_slots st. Proof. destruct h; reflexivity. Qed.
Lemma s_tick_set_head h v st : s_tick (set_head h v st) = s_tick st. Proof. destruct h; reflexivity. Qed.
Lemma s_secret_set_head h v st : s_secret (set_head h v st) = s_secret st. Proof. destruct h; reflexivity. Qed.
Lemma s_reserved_set_head h v st : s_reserved (set_head h v st) = s_reserved st. Proof. destruct h; reflexivity. Qed.
Lemma s_regions_dequeue h m st : s_regions (dequeue h m st) = s_regions st. Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma s_shadow_dequeue h m st : s_shadow (dequeue h m st) = s_shadow st. Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma s_next_rid_dequeue h m st : s_next_rid (dequeue h m st) = s_next_rid st. Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma s_areas_dequeue h m st : s_areas (dequeue h m st) = s_areas st. Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma s_groups_dequeue h m st : s_groups (dequeue h m st) = s_groups st. Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma s_slots_dequeue h m st : s_slots (dequeue h m st) = s_slots st. Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma s_tick_dequeue h m st : s_tick (dequeue h m st) = s_tick st. Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma s_secret_dequeue h m st : s_secret (dequeue h m st) = s_secret st. Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma s_reserved_dequeue h m st : s_reserved (dequeue h m st) = s_reserved st. Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma s_ctx_set_size p e n b3 st : s_ctx (set_size p e n b3 st) = s_ctx st. Proof. unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
Lemma s_regions_set_size p e n b3 st : s_regions (set_size p e n b3 st) = s_regions st. Proof. unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
Lemma s_next_rid_set_size p e n b3 st : s_next_rid (set_size p e n b3 st) = s_next_rid st. Proof. unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
Lemma s_metas_set_size p e n b3 st : s_metas (set_size p e n b3 st) = s_metas st. Proof. unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
Lemma s_areas_set_size p e n b3 st : s_areas (set_size p e n b3 st) = s_areas st. Proof. unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
Lemma s_groups_set_size p e n b3 st : s_groups (set_size p e n b3 st) = s_groups st. Proof. unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
Lemma s_slots_set_size p e n b3 st : s_slots (set_size p e n b3 st) = s_slots st. Proof. unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
Lemma s_tick_set_size p e n b3 st : s_tick (set_size p e n b3 st) = s_tick st. Proof. unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
Lemma s_secret_set_size p e n b3 st : s_secret (set_size p e n b3 st) = s_secret st. Proof. unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
Lemma s_reserved_set_size p e n b3 st : s_reserved (set_size p e n b3 st) = s_reserved st. Proof. unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
Lemma c_secret_set_active sc v st : c_secret (s_ctx (set_active sc v st)) = c_secret (s_ctx st). Proof. reflexivity. Qed.
Lemma c_init_done_set_active sc v st : c_init_done (s_ctx (set_active sc v st)) = c_init_done (s_ctx st). Proof. reflexivity. Qed.
Lemma c_mmap_counter_set_active sc v st : c_mmap_counter (s_ctx (set_active sc v st)) = c_mmap_counter (s_ctx st). Proof. reflexivity. Qed.
Lemma c_free_meta_head_set_active sc v st : c_free_meta_head (s_ctx (set_active sc v st)) = c_free_meta_head (s_ctx st). Proof. reflexivity. Qed.
Lemma c_avail_meta_set_active sc v st : c_avail_meta (s_ctx (set_active sc v st)) = c_avail_meta (s_ctx st). Proof. reflexivity. Qed.
Lemma c_avail_meta_count_set_active sc v st : c_avail_meta_count (s_ctx (set_active sc v st)) = c_avail_meta_count (s_ctx st). Proof. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_active sc v st : c_avail_meta_area_count (s_ctx (set_active sc v st)) = c_avail_meta_area_count (s_ctx st). Proof. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_active sc v st : c_meta_alloc_shift (s_ctx (set_active sc v st)) = c_meta_alloc_shift (s_ctx st). Proof. reflexivity. Qed.
Lemma c_meta_area_head_set_active sc v st : c_meta_area_head (s_ctx (set_active sc v st)) = c_meta_area_head (s_ctx st). Proof. reflexivity. Qed.
Lemma c_meta_area_tail_set_active sc v st : c_meta_area_tail (s_ctx (set_active sc v st)) = c_meta_area_tail (s_ctx st). Proof. reflexivity. Qed.
Lemma c_avail_meta_areas_set_active sc v st : c_avail_meta_areas (s_ctx (set_active sc v st)) = c_avail_meta_areas (s_ctx st). Proof. reflexivity. Qed.
Lemma c_usage_set_active sc v st : c_usage (s_ctx (set_active sc v st)) = c_usage (s_ctx st). Proof. reflexivity. Qed.
Lemma c_unmap_seq_set_active sc v st : c_unmap_seq (s_ctx (set_active sc v st)) = c_unmap_seq (s_ctx st). Proof. reflexivity. Qed.
Lemma c_bounces_set_active sc v st : c_bounces (s_ctx (set_active sc v st)) = c_bounces (s_ctx st). Proof. reflexivity. Qed.
Lemma c_seq_set_active sc v st : c_seq (s_ctx (set_active sc v st)) = c_seq (s_ctx st). Proof. reflexivity. Qed.
Lemma c_brk_set_active sc v st : c_brk (s_ctx (set_active sc v st)) = c_brk (s_ctx st). Proof. reflexivity. Qed.
Lemma c_secret_set_usage sc v st : c_secret (s_ctx (set_usage sc v st)) = c_secret (s_ctx st). Proof. reflexivity. Qed.
Lemma c_init_done_set_usage sc v st : c_init_done (s_ctx (set_usage sc v st)) = c_init_done (s_ctx st). Proof. reflexivity. Qed.
Lemma c_mmap_counter_set_usage sc v st : c_mmap_counter (s_ctx (set_usage sc v st)) = c_mmap_counter (s_ctx st). Proof. reflexivity. Qed.
Lemma c_free_meta_head_set_usage sc v st : c_free_meta_head (s_ctx (set_usage sc v st)) = c_free_meta_head (s_ctx st). Proof. reflexivity. Qed.
Lemma c_avail_meta_set_usage sc v st : c_avail_meta (s_ctx (set_usage sc v st)) = c_avail_meta (s_ctx st). Proof. reflexivity. Qed.
Lemma c_avail_meta_count_set_usage sc v st : c_avail_meta_count (s_ctx (set_usage sc v st)) = c_avail_meta_count (s_ctx st). Proof. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_usage sc v st : c_avail_meta_area_count (s_ctx (set_usage sc v st)) = c_avail_meta_area_count (s_ctx st). Proof. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_usage sc v st : c_meta_alloc_shift (s_ctx (set_usage sc v st)) = c_meta_alloc_shift (s_ctx st). Proof. reflexivity. Qed.
Lemma c_meta_area_head_set_usage sc v st : c_meta_area_head (s_ctx (set_usage sc v st)) = c_meta_area_head (s_ctx st). Proof. reflexivity. Qed.
Lemma c_meta_area_tail_set_usage sc v st : c_meta_area_tail (s_ctx (set_usage sc v st)) = c_meta_area_tail (s_ctx st). Proof. reflexivity. Qed.
Lemma c_avail_meta_areas_set_usage sc v st : c_avail_meta_areas (s_ctx (set_usage sc v st)) = c_avail_meta_areas (s_ctx st). Proof. reflexivity. Qed.
Lemma c_active_set_usage sc v st : c_active (s_ctx (set_usage sc v st)) = c_active (s_ctx st). Proof. reflexivity. Qed.
Lemma c_unmap_seq_set_usage sc v st : c_unmap_seq (s_ctx (set_usage sc v st)) = c_unmap_seq (s_ctx st). Proof. reflexivity. Qed.
Lemma c_bounces_set_usage sc v st : c_bounces (s_ctx (set_usage sc v st)) = c_bounces (s_ctx st). Proof. reflexivity. Qed.
Lemma c_seq_set_usage sc v st : c_seq (s_ctx (set_usage sc v st)) = c_seq (s_ctx st). Proof. reflexivity. Qed.
Lemma c_brk_set_usage sc v st : c_brk (s_ctx (set_usage sc v st)) = c_brk (s_ctx st). Proof. reflexivity. Qed.
Lemma c_secret_set_bounce i v st : c_secret (s_ctx (set_bounce i v st)) = c_secret (s_ctx st). Proof. reflexivity. Qed.
Lemma c_init_done_set_bounce i v st : c_init_done (s_ctx (set_bounce i v st)) = c_init_done (s_ctx st). Proof. reflexivity. Qed.
Lemma c_mmap_counter_set_bounce i v st : c_mmap_counter (s_ctx (set_bounce i v st)) = c_mmap_counter (s_ctx st). Proof. reflexivity. Qed.
Lemma c_free_meta_head_set_bounce i v st : c_free_meta_head (s_ctx (set_bounce i v st)) = c_free_meta_head (s_ctx st). Proof. reflexivity. Qed.
Lemma c_avail_meta_set_bounce i v st : c_avail_meta (s_ctx (set_bounce i v st)) = c_avail_meta (s_ctx st). Proof. reflexivity. Qed.
Lemma c_avail_meta_count_set_bounce i v st : c_avail_meta_count (s_ctx (set_bounce i v st)) = c_avail_meta_count (s_ctx st). Proof. reflexivity. Qed.
Lemma c_avail_meta_area_count_set_bounce i v st : c_avail_meta_area_count (s_ctx (set_bounce i v st)) = c_avail_meta_area_count (s_ctx st). Proof. reflexivity. Qed.
Lemma c_meta_alloc_shift_set_bounce i v st : c_meta_alloc_shift (s_ctx (set_bounce i v st)) = c_meta_alloc_shift (s_ctx st). Proof. reflexivity. Qed.
Lemma c_meta_area_head_set_bounce i v st : c_meta_area_head (s_ctx (set_bounce i v st)) = c_meta_area_head (s_ctx st). Proof. reflexivity. Qed.
Lemma c_meta_area_tail_set_bounce i v st : c_meta_area_tail (s_ctx (set_bounce i v st)) = c_meta_area_tail (s_ctx st). Proof. reflexivity. Qed.
Lemma c_avail_meta_areas_set_bounce i v st : c_avail_meta_areas (s_ctx (set_bounce i v st)) = c_avail_meta_areas (s_ctx st). Proof. reflexivity. Qed.
Lemma c_active_set_bounce i v st : c_active (s_ctx (set_bounce i v st)) = c_active (s_ctx st). Proof. reflexivity. Qed.
Lemma c_usage_set_bounce i v st : c_usage (s_ctx (set_bounce i v st)) = c_usage (s_ctx st). Proof. reflexivity. Qed.
Lemma c_unmap_seq_set_bounce i v st : c_unmap_seq (s_ctx (set_bounce i v st)) = c_unmap_seq (s_ctx st). Proof. reflexivity. Qed.
Lemma c_seq_set_bounce i v st : c_seq (s_ctx (set_bounce i v st)) = c_seq (s_ctx st). Proof. reflexivity. Qed.
Lemma c_brk_set_bounce i v st : c_brk (s_ctx (set_bounce i v st)) = c_brk (s_ctx st). Proof. reflexivity. Qed.
Lemma c_secret_step_seq st : c_secret (s_ctx (step_seq st)) = c_secret (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_init_done_step_seq st : c_init_done (s_ctx (step_seq st)) = c_init_done (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_mmap_counter_step_seq st : c_mmap_counter (s_ctx (step_seq st)) = c_mmap_counter (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_free_meta_head_step_seq st : c_free_meta_head (s_ctx (step_seq st)) = c_free_meta_head (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_avail_meta_step_seq st : c_avail_meta (s_ctx (step_seq st)) = c_avail_meta (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_avail_meta_count_step_seq st : c_avail_meta_count (s_ctx (step_seq st)) = c_avail_meta_count (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_avail_meta_area_count_step_seq st : c_avail_meta_area_count (s_ctx (step_seq st)) = c_avail_meta_area_count (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_meta_alloc_shift_step_seq st : c_meta_alloc_shift (s_ctx (step_seq st)) = c_meta_alloc_shift (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_meta_area_head_step_seq st : c_meta_area_head (s_ctx (step_seq st)) = c_meta_area_head (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_meta_area_tail_step_seq st : c_meta_area_tail (s_ctx (step_seq st)) = c_meta_area_tail (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_avail_meta_areas_step_seq st : c_avail_meta_areas (s_ctx (step_seq st)) = c_avail_meta_areas (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_active_step_seq st : c_active (s_ctx (step_seq st)) = c_active (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_usage_step_seq st : c_usage (s_ctx (step_seq st)) = c_usage (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_bounces_step_seq st : c_bounces (s_ctx (step_seq st)) = c_bounces (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_brk_step_seq st : c_brk (s_ctx (step_seq st)) = c_brk (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
Lemma c_secret_record_seq sc st : c_secret (s_ctx (record_seq sc st)) = c_secret (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_init_done_record_seq sc st : c_init_done (s_ctx (record_seq sc st)) = c_init_done (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_mmap_counter_record_seq sc st : c_mmap_counter (s_ctx (record_seq sc st)) = c_mmap_counter (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_free_meta_head_record_seq sc st : c_free_meta_head (s_ctx (record_seq sc st)) = c_free_meta_head (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_avail_meta_record_seq sc st : c_avail_meta (s_ctx (record_seq sc st)) = c_avail_meta (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_avail_meta_count_record_seq sc st : c_avail_meta_count (s_ctx (record_seq sc st)) = c_avail_meta_count (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_avail_meta_area_count_record_seq sc st : c_avail_meta_area_count (s_ctx (record_seq sc st)) = c_avail_meta_area_count (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_meta_alloc_shift_record_seq sc st : c_meta_alloc_shift (s_ctx (record_seq sc st)) = c_meta_alloc_shift (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_meta_area_head_record_seq sc st : c_meta_area_head (s_ctx (record_seq sc st)) = c_meta_area_head (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_meta_area_tail_record_seq sc st : c_meta_area_tail (s_ctx (record_seq sc st)) = c_meta_area_tail (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_avail_meta_areas_record_seq sc st : c_avail_meta_areas (s_ctx (record_seq sc st)) = c_avail_meta_areas (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_active_record_seq sc st : c_active (s_ctx (record_seq sc st)) = c_active (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_usage_record_seq sc st : c_usage (s_ctx (record_seq sc st)) = c_usage (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_bounces_record_seq sc st : c_bounces (s_ctx (record_seq sc st)) = c_bounces (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_seq_record_seq sc st : c_seq (s_ctx (record_seq sc st)) = c_seq (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_brk_record_seq sc st : c_brk (s_ctx (record_seq sc st)) = c_brk (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma c_secret_account_bounce sc st : c_secret (s_ctx (account_bounce sc st)) = c_secret (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_init_done_account_bounce sc st : c_init_done (s_ctx (account_bounce sc st)) = c_init_done (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_mmap_counter_account_bounce sc st : c_mmap_counter (s_ctx (account_bounce sc st)) = c_mmap_counter (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_free_meta_head_account_bounce sc st : c_free_meta_head (s_ctx (account_bounce sc st)) = c_free_meta_head (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_avail_meta_account_bounce sc st : c_avail_meta (s_ctx (account_bounce sc st)) = c_avail_meta (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_avail_meta_count_account_bounce sc st : c_avail_meta_count (s_ctx (account_bounce sc st)) = c_avail_meta_count (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_avail_meta_area_count_account_bounce sc st : c_avail_meta_area_count (s_ctx (account_bounce sc st)) = c_avail_meta_area_count (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_meta_alloc_shift_account_bounce sc st : c_meta_alloc_shift (s_ctx (account_bounce sc st)) = c_meta_alloc_shift (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_meta_area_head_account_bounce sc st : c_meta_area_head (s_ctx (account_bounce sc st)) = c_meta_area_head (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_meta_area_tail_account_bounce sc st : c_meta_area_tail (s_ctx (account_bounce sc st)) = c_meta_area_tail (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_avail_meta_areas_account_bounce sc st : c_avail_meta_areas (s_ctx (account_bounce sc st)) = c_avail_meta_areas (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_active_account_bounce sc st : c_active (s_ctx (account_bounce sc st)) = c_active (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_usage_account_bounce sc st : c_usage (s_ctx (account_bounce sc st)) = c_usage (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_unmap_seq_account_bounce sc st : c_unmap_seq (s_ctx (account_bounce sc st)) = c_unmap_seq (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_seq_account_bounce sc st : c_seq (s_ctx (account_bounce sc st)) = c_seq (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_brk_account_bounce sc st : c_brk (s_ctx (account_bounce sc st)) = c_brk (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
Lemma c_secret_decay_bounces sc st : c_secret (s_ctx (decay_bounces sc st)) = c_secret (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_init_done_decay_bounces sc st : c_init_done (s_ctx (decay_bounces sc st)) = c_init_done (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_mmap_counter_decay_bounces sc st : c_mmap_counter (s_ctx (decay_bounces sc st)) = c_mmap_counter (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_free_meta_head_decay_bounces sc st : c_free_meta_head (s_ctx (decay_bounces sc st)) = c_free_meta_head (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_avail_meta_decay_bounces sc st : c_avail_meta (s_ctx (decay_bounces sc st)) = c_avail_meta (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_avail_meta_count_decay_bounces sc st : c_avail_meta_count (s_ctx (decay_bounces sc st)) = c_avail_meta_count (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_avail_meta_area_count_decay_bounces sc st : c_avail_meta_area_count (s_ctx (decay_bounces sc st)) = c_avail_meta_area_count (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_meta_alloc_shift_decay_bounces sc st : c_meta_alloc_shift (s_ctx (decay_bounces sc st)) = c_meta_alloc_shift (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_meta_area_head_decay_bounces sc st : c_meta_area_head (s_ctx (decay_bounces sc st)) = c_meta_area_head (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_meta_area_tail_decay_bounces sc st : c_meta_area_tail (s_ctx (decay_bounces sc st)) = c_meta_area_tail (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_avail_meta_areas_decay_bounces sc st : c_avail_meta_areas (s_ctx (decay_bounces sc st)) = c_avail_meta_areas (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_active_decay_bounces sc st : c_active (s_ctx (decay_bounces sc st)) = c_active (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_usage_decay_bounces sc st : c_usage (s_ctx (decay_bounces sc st)) = c_usage (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_unmap_seq_decay_bounces sc st : c_unmap_seq (s_ctx (decay_bounces sc st)) = c_unmap_seq (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_seq_decay_bounces sc st : c_seq (s_ctx (decay_bounces sc st)) = c_seq (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_brk_decay_bounces sc st : c_brk (s_ctx (decay_bounces sc st)) = c_brk (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
Lemma c_secret_dequeue h m st : c_secret (s_ctx (dequeue h m st)) = c_secret (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma c_init_done_dequeue h m st : c_init_done (s_ctx (dequeue h m st)) = c_init_done (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma c_mmap_counter_dequeue h m st : c_mmap_counter (s_ctx (dequeue h m st)) = c_mmap_counter (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma c_avail_meta_dequeue h m st : c_avail_meta (s_ctx (dequeue h m st)) = c_avail_meta (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma c_avail_meta_count_dequeue h m st : c_avail_meta_count (s_ctx (dequeue h m st)) = c_avail_meta_count (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma c_avail_meta_area_count_dequeue h m st : c_avail_meta_area_count (s_ctx (dequeue h m st)) = c_avail_meta_area_count (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma c_meta_alloc_shift_dequeue h m st : c_meta_alloc_shift (s_ctx (dequeue h m st)) = c_meta_alloc_shift (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma c_meta_area_head_dequeue h m st : c_meta_area_head (s_ctx (dequeue h m st)) = c_meta_area_head (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma c_meta_area_tail_dequeue h m st : c_meta_area_tail (s_ctx (dequeue h m st)) = c_meta_area_tail (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma c_avail_meta_areas_dequeue h m st : c_avail_meta_areas (s_ctx (dequeue h m st)) = c_avail_meta_areas (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma c_usage_dequeue h m st : c_usage (s_ctx (dequeue h m st)) = c_usage (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma c_unmap_seq_dequeue h m st : c_unmap_seq (s_ctx (dequeue h m st)) = c_unmap_seq (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma c_bounces_dequeue h m st : c_bounces (s_ctx (dequeue h m st)) = c_bounces (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma c_seq_dequeue h m st : c_seq (s_ctx (dequeue h m st)) = c_seq (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
Lemma c_brk_dequeue h m st : c_brk (s_ctx (dequeue h m st)) = c_brk (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
End CEIL_WRAP_4.
#[export] Hint Rewrite s_regions_set_active s_shadow_set_active s_next_rid_set_active s_metas_set_active s_areas_set_active s_groups_set_active s_slots_set_active s_tick_set_active s_secret_set_active s_reserved_set_active s_regions_set_usage s_shadow_set_usage s_next_rid_set_usage s_metas_set_usage s_areas_set_usage s_groups_set_usage s_slots_set_usage s_tick_set_usage s_secret_set_usage s_reserved_set_usage s_regions_set_bounce s_shadow_set_bounce s_next_rid_set_bounce s_metas_set_bounce s_areas_set_bounce s_groups_set_bounce s_slots_set_bounce s_tick_set_bounce s_secret_set_bounce s_reserved_set_bounce s_ctx_put_meta s_regions_put_meta s_shadow_put_meta s_next_rid_put_meta s_areas_put_meta s_groups_put_meta s_slots_put_meta s_tick_put_meta s_secret_put_meta s_reserved_put_meta s_ctx_upd_meta s_regions_upd_meta s_shadow_upd_meta s_next_rid_upd_meta s_areas_upd_meta s_groups_upd_meta s_slots_upd_meta s_tick_upd_meta s_secret_upd_meta s_reserved_upd_meta s_ctx_put_group s_regions_put_group s_shadow_put_group s_next_rid_put_group s_metas_put_group s_areas_put_group s_slots_put_group s_tick_put_group s_secret_put_group s_reserved_put_group s_ctx_del_group s_regions_del_group s_shadow_del_group s_next_rid_del_group s_metas_del_group s_areas_del_group s_slots_del_group s_tick_del_group s_secret_del_group s_reserved_del_group s_ctx_set_group_active_idx s_regions_set_group_active_idx s_shadow_set_group_active_idx s_next_rid_set_group_active_idx s_metas_set_group_active_idx s_areas_set_group_active_idx s_slots_set_group_active_idx s_tick_set_group_active_idx s_secret_set_group_active_idx s_reserved_set_group_active_idx s_ctx_drop_region s_next_rid_drop_region s_metas_drop_region s_areas_drop_region s_groups_drop_region s_slots_drop_region s_tick_drop_region s_secret_drop_region s_reserved_drop_region s_ctx_upd_region s_shadow_upd_region s_next_rid_upd_region s_metas_upd_region s_areas_upd_region s_groups_upd_region s_slots_upd_region s_tick_upd_region s_secret_upd_region s_reserved_upd_region s_ctx_add_slots s_regions_add_slots s_shadow_add_slots s_next_rid_add_slots s_metas_add_slots s_areas_add_slots s_groups_add_slots s_tick_add_slots s_secret_add_slots s_reserved_add_slots s_ctx_del_slots s_regions_del_slots s_shadow_del_slots s_next_rid_del_slots s_metas_del_slots s_areas_del_slots s_groups_del_slots s_tick_del_slots s_secret_del_slots s_reserved_del_slots s_ctx_upd_shadow s_regions_upd_shadow s_next_rid_upd_shadow s_metas_upd_shadow s_areas_upd_shadow s_groups_upd_shadow s_slots_upd_shadow s_tick_upd_shadow s_secret_upd_shadow s_reserved_upd_shadow s_ctx_wr8 s_regions_wr8 s_next_rid_wr8 s_metas_wr8 s_areas_wr8 s_groups_wr8 s_slots_wr8 s_tick_wr8 s_secret_wr8 s_reserved_wr8 s_ctx_wr16 s_regions_wr16 s_next_rid_wr16 s_metas_wr16 s_areas_wr16 s_groups_wr16 s_slots_wr16 s_tick_wr16 s_secret_wr16 s_reserved_wr16 s_ctx_wr32 s_regions_wr32 s_next_rid_wr32 s_metas_wr32 s_areas_wr32 s_groups_wr32 s_slots_wr32 s_tick_wr32 s_secret_wr32 s_reserved_wr32 s_ctx_havoc s_regions_havoc s_next_rid_havoc s_metas_havoc s_areas_havoc s_groups_havoc s_slots_havoc s_tick_havoc s_secret_havoc s_reserved_havoc s_ctx_hdr_havoc s_regions_hdr_havoc s_next_rid_hdr_havoc s_metas_hdr_havoc s_areas_hdr_havoc s_groups_hdr_havoc s_slots_hdr_havoc s_tick_hdr_havoc s_secret_hdr_havoc s_reserved_hdr_havoc s_regions_step_seq s_shadow_step_seq s_next_rid_step_seq s_metas_step_seq s_areas_step_seq s_groups_step_seq s_slots_step_seq s_tick_step_seq s_secret_step_seq s_reserved_step_seq s_regions_record_seq s_shadow_record_seq s_next_rid_record_seq s_metas_record_seq s_areas_record_seq s_groups_record_seq s_slots_record_seq s_tick_record_seq s_secret_record_seq s_reserved_record_seq s_regions_account_bounce s_shadow_account_bounce s_next_rid_account_bounce s_metas_account_bounce s_areas_account_bounce s_groups_account_bounce s_slots_account_bounce s_tick_account_bounce s_secret_account_bounce s_reserved_account_bounce s_regions_decay_bounces s_shadow_decay_bounces s_next_rid_decay_bounces s_metas_decay_bounces s_areas_decay_bounces s_groups_decay_bounces s_slots_decay_bounces s_tick_decay_bounces s_secret_decay_bounces s_reserved_decay_bounces s_regions_set_head s_shadow_set_head s_next_rid_set_head s_metas_set_head s_areas_set_head s_groups_set_head s_slots_set_head s_tick_set_head s_secret_set_head s_reserved_set_head s_regions_dequeue s_shadow_dequeue s_next_rid_dequeue s_areas_dequeue s_groups_dequeue s_slots_dequeue s_tick_dequeue s_secret_dequeue s_reserved_dequeue s_ctx_set_size s_regions_set_size s_next_rid_set_size s_metas_set_size s_areas_set_size s_groups_set_size s_slots_set_size s_tick_set_size s_secret_set_size s_reserved_set_size c_secret_set_active c_init_done_set_active c_mmap_counter_set_active c_free_meta_head_set_active c_avail_meta_set_active c_avail_meta_count_set_active c_avail_meta_area_count_set_active c_meta_alloc_shift_set_active c_meta_area_head_set_active c_meta_area_tail_set_active c_avail_meta_areas_set_active c_usage_set_active c_unmap_seq_set_active c_bounces_set_active c_seq_set_active c_brk_set_active c_secret_set_usage c_init_done_set_usage c_mmap_counter_set_usage c_free_meta_head_set_usage c_avail_meta_set_usage c_avail_meta_count_set_usage c_avail_meta_area_count_set_usage c_meta_alloc_shift_set_usage c_meta_area_head_set_usage c_meta_area_tail_set_usage c_avail_meta_areas_set_usage c_active_set_usage c_unmap_seq_set_usage c_bounces_set_usage c_seq_set_usage c_brk_set_usage c_secret_set_bounce c_init_done_set_bounce c_mmap_counter_set_bounce c_free_meta_head_set_bounce c_avail_meta_set_bounce c_avail_meta_count_set_bounce c_avail_meta_area_count_set_bounce c_meta_alloc_shift_set_bounce c_meta_area_head_set_bounce c_meta_area_tail_set_bounce c_avail_meta_areas_set_bounce c_active_set_bounce c_usage_set_bounce c_unmap_seq_set_bounce c_seq_set_bounce c_brk_set_bounce c_secret_step_seq c_init_done_step_seq c_mmap_counter_step_seq c_free_meta_head_step_seq c_avail_meta_step_seq c_avail_meta_count_step_seq c_avail_meta_area_count_step_seq c_meta_alloc_shift_step_seq c_meta_area_head_step_seq c_meta_area_tail_step_seq c_avail_meta_areas_step_seq c_active_step_seq c_usage_step_seq c_bounces_step_seq c_brk_step_seq c_secret_record_seq c_init_done_record_seq c_mmap_counter_record_seq c_free_meta_head_record_seq c_avail_meta_record_seq c_avail_meta_count_record_seq c_avail_meta_area_count_record_seq c_meta_alloc_shift_record_seq c_meta_area_head_record_seq c_meta_area_tail_record_seq c_avail_meta_areas_record_seq c_active_record_seq c_usage_record_seq c_bounces_record_seq c_seq_record_seq c_brk_record_seq c_secret_account_bounce c_init_done_account_bounce c_mmap_counter_account_bounce c_free_meta_head_account_bounce c_avail_meta_account_bounce c_avail_meta_count_account_bounce c_avail_meta_area_count_account_bounce c_meta_alloc_shift_account_bounce c_meta_area_head_account_bounce c_meta_area_tail_account_bounce c_avail_meta_areas_account_bounce c_active_account_bounce c_usage_account_bounce c_unmap_seq_account_bounce c_seq_account_bounce c_brk_account_bounce c_secret_decay_bounces c_init_done_decay_bounces c_mmap_counter_decay_bounces c_free_meta_head_decay_bounces c_avail_meta_decay_bounces c_avail_meta_count_decay_bounces c_avail_meta_area_count_decay_bounces c_meta_alloc_shift_decay_bounces c_meta_area_head_decay_bounces c_meta_area_tail_decay_bounces c_avail_meta_areas_decay_bounces c_active_decay_bounces c_usage_decay_bounces c_unmap_seq_decay_bounces c_seq_decay_bounces c_brk_decay_bounces c_secret_dequeue c_init_done_dequeue c_mmap_counter_dequeue c_avail_meta_dequeue c_avail_meta_count_dequeue c_avail_meta_area_count_dequeue c_meta_alloc_shift_dequeue c_meta_area_head_dequeue c_meta_area_tail_dequeue c_avail_meta_areas_dequeue c_usage_dequeue c_unmap_seq_dequeue c_bounces_dequeue c_seq_dequeue c_brk_dequeue : mst.
Section CEIL_WRAP_5.
Context {RUNp : RunP}.
Lemma strip_fields st :
s_ctx (strip st) = s_ctx st /\ s_regions (strip st) = s_regions st /\ s_next_rid (strip st) = s_next_rid st
/\ s_metas (strip st) = s_metas st /\ s_areas (strip st) = s_areas st /\ s_groups (strip st) = s_groups st
/\ s_slots (strip st) = s_slots st /\ s_secret (strip st) = s_secret st /\ s_reserved (strip st) = s_reserved st.
Proof. repeat split; reflexivity. Qed.
End CEIL_WRAP_5.
Ltac by_strip H :=
first [ apply (f_equal s_ctx) in H | apply (f_equal s_regions) in H | apply (f_equal s_next_rid) in H
| apply (f_equal s_metas) in H | apply (f_equal s_areas) in H | apply (f_equal s_groups) in H
| apply (f_equal s_slots) in H | apply (f_equal s_secret) in H | apply (f_equal s_reserved) in H ]; exact H.
Section CEIL_WRAP_6.
Context {RUNp : RunP}.
Section LAYOUT_FIELDS.
Ltac lay lem := intros; pose proof lem as H; cbn [strip] in H;
match goal with |- ?F _ = _ => apply (f_equal F) in H; cbn in H; exact H end.
Lemma s_ctx_zero_hdrs p size i cnt st : s_ctx (zero_hdrs p size i cnt st) = s_ctx st. Proof. lay (strip_zero_hdrs p size i cnt st). Qed.
Lemma s_regions_zero_hdrs p size i cnt st : s_regions (zero_hdrs p size i cnt st) = s_regions st. Proof. lay (strip_zero_hdrs p size i cnt st). Qed.
Lemma s_next_rid_zero_hdrs p size i cnt st : s_next_rid (zero_hdrs p size i cnt st) = s_next_rid st. Proof. lay (strip_zero_hdrs p size i cnt st). Qed.
Lemma s_metas_zero_hdrs p size i cnt st : s_metas (zero_hdrs p size i cnt st) = s_metas st. Proof. lay (strip_zero_hdrs p size i cnt st). Qed.
Lemma s_areas_zero_hdrs p size i cnt st : s_areas (zero_hdrs p size i cnt st) = s_areas st. Proof. lay (strip_zero_hdrs p size i cnt st). Qed.
Lemma s_groups_zero_hdrs p size i cnt st : s_groups (zero_hdrs p size i cnt st) = s_groups st. Proof. lay (strip_zero_hdrs p size i cnt st). Qed.
Lemma s_slots_zero_hdrs p size i cnt st : s_slots (zero_hdrs p size i cnt st) = s_slots st. Proof. lay (strip_zero_hdrs p size i cnt st). Qed.
Lemma s_secret_zero_hdrs p size i cnt st : s_secret (zero_hdrs p size i cnt st) = s_secret st. Proof. lay (strip_zero_hdrs p size i cnt st). Qed.
Lemma s_reserved_zero_hdrs p size i cnt st : s_reserved (zero_hdrs p size i cnt st) = s_reserved st. Proof. lay (strip_zero_hdrs p size i cnt st). Qed.
Lemma s_tick_zero_hdrs p size i cnt st : s_tick (zero_hdrs p size i cnt st) = s_tick st.
Proof. revert i st; induction cnt; intros; cbn [zero_hdrs]; [reflexivity|]. rewrite IHcnt. reflexivity. Qed.
Lemma s_ctx_enframe_at st g idx n off : s_ctx (fst (enframe_at st g idx n off)) = s_ctx st. Proof. lay (strip_enframe_at st g idx n off). Qed.
Lemma s_regions_enframe_at st g idx n off : s_regions (fst (enframe_at st g idx n off)) = s_regions st. Proof. lay (strip_enframe_at st g idx n off). Qed.
Lemma s_next_rid_enframe_at st g idx n off : s_next_rid (fst (enframe_at st g idx n off)) = s_next_rid st. Proof. lay (strip_enframe_at st g idx n off). Qed.
Lemma s_metas_enframe_at st g idx n off : s_metas (fst (enframe_at st g idx n off)) = s_metas st. Proof. lay (strip_enframe_at st g idx n off). Qed.
Lemma s_areas_enframe_at st g idx n off : s_areas (fst (enframe_at st g idx n off)) = s_areas st. Proof. lay (strip_enframe_at st g idx n off). Qed.
Lemma s_groups_enframe_at st g idx n off : s_groups (fst (enframe_at st g idx n off)) = s_groups st. Proof. lay (strip_enframe_at st g idx n off). Qed.
Lemma s_slots_enframe_at st g idx n off : s_slots (fst (enframe_at st g idx n off)) = s_slots st. Proof. lay (strip_enframe_at st g idx n off). Qed.
Lemma s_secret_enframe_at st g idx n off : s_secret (fst (enframe_at st g idx n off)) = s_secret st. Proof. lay (strip_enframe_at st g idx n off). Qed.
Lemma s_reserved_enframe_at st g idx n off : s_reserved (fst (enframe_at st g idx n off)) = s_reserved st. Proof. lay (strip_enframe_at st g idx n off). Qed.
Lemma s_tick_enframe_at st g idx n off : s_tick (fst (enframe_at st g idx n off)) = s_tick st.
Proof. unfold enframe_at. destruct (negb (off =? 0)); cbn -[set_size wr8 wr16 Z.add Z.sub Z.mul Z.div get_stride];
unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
Lemma s_ctx_nest_layout st g idx j size cnt : s_ctx (nest_layout st g idx j size cnt) = s_ctx st. Proof. lay (strip_nest_layout st g idx j size cnt). Qed.
Lemma s_regions_nest_layout st g idx j size cnt : s_regions (nest_layout st g idx j size cnt) = s_regions st. Proof. lay (strip_nest_layout st g idx j size cnt). Qed.
Lemma s_next_rid_nest_layout st g idx j size cnt : s_next_rid (nest_layout st g idx j size cnt) = s_next_rid st. Proof. lay (strip_nest_layout st g idx j size cnt). Qed.
Lemma s_metas_nest_layout st g idx j size cnt : s_metas (nest_layout st g idx j size cnt) = s_metas st. Proof. lay (strip_nest_layout st g idx j size cnt). Qed.
Lemma s_areas_nest_layout st g idx j size cnt : s_areas (nest_layout st g idx j size cnt) = s_areas st. Proof. lay (strip_nest_layout st g idx j size cnt). Qed.
Lemma s_groups_nest_layout st g idx j size cnt : s_groups (nest_layout st g idx j size cnt) = s_groups st. Proof. lay (strip_nest_layout st g idx j size cnt). Qed.
Lemma s_slots_nest_layout st g idx j size cnt : s_slots (nest_layout st g idx j size cnt) = s_slots st. Proof. lay (strip_nest_layout st g idx j size cnt). Qed.
Lemma s_secret_nest_layout st g idx j size cnt : s_secret (nest_layout st g idx j size cnt) = s_secret st. Proof. lay (strip_nest_layout st g idx j size cnt). Qed.
Lemma s_reserved_nest_layout st g idx j size cnt : s_reserved (nest_layout st g idx j size cnt) = s_reserved st. Proof. lay (strip_nest_layout st g idx j size cnt). Qed.
Lemma s_tick_nest_layout st g idx j size cnt : s_tick (nest_layout st g idx j size cnt) = s_tick st.
Proof. unfold nest_layout. destruct (enframe_at st g idx _ 0) as [st1 p] eqn:E.
rewrite s_tick_zero_hdrs. cbn. pose proof (s_tick_enframe_at st g idx (UNIT * size_class j - IB) 0) as H. rewrite E in H. exact H. Qed.
End LAYOUT_FIELDS.
End CEIL_WRAP_6.
#[export] Hint Rewrite s_ctx_zero_hdrs s_regions_zero_hdrs s_next_rid_zero_hdrs s_metas_zero_hdrs s_areas_zero_hdrs s_groups_zero_hdrs s_slots_zero_hdrs s_secret_zero_hdrs s_reserved_zero_hdrs s_tick_zero_hdrs
s_ctx_enframe_at s_regions_enframe_at s_next_rid_enframe_at s_metas_enframe_at s_areas_enframe_at s_groups_enframe_at s_slots_enframe_at s_secret_enframe_at s_reserved_enframe_at s_tick_enframe_at
s_ctx_nest_layout s_regions_nest_layout s_next_rid_nest_layout s_metas_nest_layout s_areas_nest_layout s_groups_nest_layout s_slots_nest_layout s_secret_nest_layout s_reserved_nest_layout s_tick_nest_layout : mst.
Section CEIL_WRAP_7.
Context {RUNp : RunP}.
Lemma s_regions_new_region k b l st : s_regions (fst (new_region k b l st)) = <[s_next_rid st := mkRegion k b l]> (s_regions st).
Proof. reflexivity. Qed.
Lemma s_next_rid_new_region k b l st : s_next_rid (fst (new_region k b l st)) = N.succ (s_next_rid st).
Proof. reflexivity. Qed.
Lemma snd_new_region k b l st : snd (new_region k b l st) = s_next_rid st.
Proof. reflexivity. Qed.
Lemma s_regions_drop_region rid st : s_regions (drop_region rid st) = delete rid (s_regions st).
Proof. reflexivity. Qed.
Lemma s_shadow_drop_region rid st : s_shadow (drop_region rid st) = delete rid (s_shadow st).
Proof. reflexivity. Qed.
Lemma s_groups_put_group g mo ai st : s_groups (put_group g mo ai st) = <[g := mkGhdr mo (Z.land ai 31)]> (s_groups st).
Proof. reflexivity. Qed.
Lemma s_groups_del_group g st : s_groups (del_group g st) = delete g (s_groups st).
Proof. reflexivity. Qed.
Lemma s_shadow_upd_shadow rid f st : s_shadow (upd_shadow rid f st) = <[rid := f (get_shadow st rid)]> (s_shadow st).
Proof. reflexivity. Qed.
End CEIL_WRAP_7.
#[export] Hint Rewrite s_regions_new_region s_next_rid_new_region snd_new_region s_regions_drop_region s_shadow_drop_region
s_groups_put_group s_groups_del_group s_shadow_upd_shadow : mst.
Section CEIL_WRAP_8.
Context {RUNp : RunP}.
Lemma active_set_active st sc v sc' : active (set_active sc v st) sc' = if sc' =? sc then v else active st sc'.
Proof.
unfold active, set_active, ctx; cbn. destruct (Z.eqb_spec sc' sc) as [->|NE].
- destruct v; [rewrite lookup_insert_eq| rewrite lookup_delete_eq]; reflexivity.
- destruct v; [rewrite lookup_insert_ne by congruence| rewrite lookup_delete_ne by congruence]; reflexivity.
Qed.
Lemma usage_set_usage st sc v sc' : usage (set_usage sc v st) sc' = if sc' =? sc then v else usage st sc'.
Proof.
unfold usage, set_usage, ctx; cbn. destruct (Z.eqb_spec sc' sc) as [->|NE];
[rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
Qed.
Lemma bounces_set_bounce st i v i' : bounces (set_bounce i v st) i' = if i' =? i then v else bounces st i'.
Proof.
unfold bounces, set_bounce, ctx; cbn. destruct (Z.eqb_spec i' i) as [->|NE];
[rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
Qed.
Lemma get_head_set_head st h v : get_head (set_head h v st) h = v.
Proof. destruct h; cbn; [rewrite active_set_active, Z.eqb_refl|]; reflexivity. Qed.
Lemma get_head_set_head_other st h h' v : h' <> h -> get_head (set_head h v st) h' = get_head st h'.
Proof.
intros NE. destruct h as [sc|], h' as [sc'|]; cbn; try reflexivity; try congruence.
rewrite active_set_active. destruct (Z.eqb_spec sc' sc); [congruence| reflexivity].
Qed.
Lemma active_upd_meta st m f sc : active (upd_meta m f st) sc = active st sc. Proof. reflexivity. Qed.
Lemma active_put_meta st m r sc : active (put_meta m r st) sc = active st sc. Proof. reflexivity. Qed.
Lemma usage_upd_meta st m f sc : usage (upd_meta m f st) sc = usage st sc. Proof. reflexivity. Qed.
Lemma get_head_upd_meta st m f h : get_head (upd_meta m f st) h = get_head st h. Proof. destruct h; reflexivity. Qed.
Lemma get_head_put_meta st m r h : get_head (put_meta m r st) h = get_head st h. Proof. destruct h; reflexivity. Qed.
Lemma get_meta_rec_set_head st h v x : get_meta_rec (set_head h v st) x = get_meta_rec st x. Proof. destruct h; reflexivity. Qed.
Lemma get_meta_rec_upd_ctx st f x : get_meta_rec (upd_ctx f st) x = get_meta_rec st x. Proof. reflexivity. Qed.
End CEIL_WRAP_8.
#[export] Hint Rewrite active_set_active usage_set_usage bounces_set_bounce get_head_set_head
active_upd_meta active_put_meta usage_upd_meta get_head_upd_meta get_head_put_meta get_meta_rec_set_head get_meta_rec_upd_ctx : mst.
Section CEIL_WRAP_9.
Context {RUNp : RunP}.
Lemma lookup_new_region k b l st rid :
s_regions (fst (new_region k b l st)) !! rid = if (rid =? s_next_rid st)%N then Some (mkRegion k b l) else s_regions st !! rid.
Proof.
rewrite s_regions_new_region. destruct (N.eqb_spec rid (s_next_rid st)) as [->|NE];
[rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
Qed.
Lemma lookup_drop_region rid st rid' :
s_regions (drop_region rid st) !! rid' = if (rid' =? rid)%N then None else s_regions st !! rid'.
Proof.
rewrite s_regions_drop_region. destruct (N.eqb_spec rid' rid) as [->|NE];
[rewrite lookup_delete_eq| rewrite lookup_delete_ne by congruence]; reflexivity.
Qed.
Lemma lookup_upd_region rid f st rid' :
s_regions (upd_region rid f st) !! rid' =
if (rid' =? rid)%N then option_map f (s_regions st !! rid) else s_regions st !! rid'.
Proof.
unfold upd_region, get_region. destruct (s_regions st !! rid) as [r|] eqn:E; cbn.
- destruct (N.eqb_spec rid' rid) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; [reflexivity|reflexivity].
- destruct (N.eqb_spec rid' rid) as [->|NE]; [rewrite E|]; reflexivity.
Qed.
Lemma conc_eq st p r : s_regions st !! (fst p) = Some r -> conc st p = r_base r + snd p.
Proof. intros H. unfold conc, get_region. rewrite H. reflexivity. Qed.
Lemma lookup_put_group g mo ai st b :
s_groups (put_group g mo ai st) !! b = if aptr_eqb b g then Some (mkGhdr mo (Z.land ai 31)) else s_groups st !! b.
Proof.
rewrite s_groups_put_group. destruct (aptr_eqb_spec b g) as [->|NE];
[rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
Qed.
Lemma lookup_del_group g st b :
s_groups (del_group g st) !! b = if aptr_eqb b g then None else s_groups st !! b.
Proof.
rewrite s_groups_del_group. destruct (aptr_eqb_spec b g) as [->|NE];
[rewrite lookup_delete_eq| rewrite lookup_delete_ne by congruence]; reflexivity.
Qed.
Lemma lookup_set_group_active_idx g ai st b :
s_groups (set_group_active_idx g ai st) !! b =
if aptr_eqb b g then option_map (fun h => mkGhdr (g_meta h) (Z.land ai 31)) (s_groups st !! g) else s_groups st !! b.
Proof.
unfold set_group_active_idx, get_group. destruct (s_groups st !! g) as [h|] eqn:E; cbn.
- destruct (aptr_eqb_spec b g) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
- destruct (aptr_eqb_spec b g) as [->|NE]; [rewrite E|]; reflexivity.
Qed.
Lemma group_active_idx_eq st g m ai : s_groups st !! g = Some (mkGhdr m ai) -> group_active_idx st g = Z.land ai 31.
Proof. intros H. unfold group_active_idx, get_group. rewrite H. reflexivity. Qed.
Lemma Z_iter_ind {A} (f : A -> A) (P : Z -> A -> Prop) x :
P 0 x -> (forall n a, 0 <= n -> P n a -> P (n + 1) (f a)) -> forall n, 0 <= n -> P n (Z.iter n f x).
Proof.
intros H0 HS n Hn. rewrite iter_nat_of_Z by exact Hn.
rewrite <- (Z2Nat.id n) at 1 by exact Hn. rewrite <- Zabs2Nat.abs_nat_nonneg by exact Hn.
induction (Z.abs_nat n) as [|k IH]; [exact H0|].
cbn [nat_rect]. rewrite Nat2Z.inj_succ, <- Z.add_1_r. apply HS; [lia| exact IH].
Qed.
Lemma lookup_add_slots m p stride cnt st s : 0 <= cnt -> 0 < stride ->
s_slots (add_slots m p stride cnt st) !! s =
if (fst s =? fst p)%N && (0 <=? snd s - snd p - UNIT) && ((snd s - snd p - UNIT) mod stride =? 0) && ((snd s - snd p - UNIT) / stride <? cnt)
then Some (m, (snd s - snd p - UNIT) / stride) else s_slots st !! s.
Proof.
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
Lemma lookup_del_slots p stride cnt st s : 0 <= cnt -> 0 < stride ->
s_slots (del_slots p stride cnt st) !! s =
if (fst s =? fst p)%N && (0 <=? snd s - snd p - UNIT) && ((snd s - snd p - UNIT) mod stride =? 0) && ((snd s - snd p - UNIT) / stride <? cnt)
then None else s_slots st !! s.
Proof.
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
Lemma slot_key_test p stride cnt s : 0 < stride ->
((fst s =? fst p)%N && (0 <=? snd s - snd p - UNIT) && ((snd s - snd p - UNIT) mod stride =? 0) && ((snd s - snd p - UNIT) / stride <? cnt)) = true
<-> exists i, 0 <= i < cnt /\ s = aadd p (UNIT + stride * i).
Proof.
intros Hs. rewrite !Bool.andb_true_iff, N.eqb_eq, Z.leb_le, Z.eqb_eq, Z.ltb_lt. split.
- intros [[[E1 E2] E3] E4]. exists ((snd s - snd p - UNIT) / stride). split.
+ split; [apply Z.div_pos; lia| exact E4].
+ unfold aadd. destruct s as [sr so], p as [pr po]; cbn in *. subst sr. f_equal.
pose proof (Z.div_mod (so - po - UNIT) stride ltac:(lia)). lia.
- intros (i & Hi & ->). unfold aadd; cbn. replace (snd p + (UNIT + stride * i) - snd p - UNIT) with (i * stride) by lia.
rewrite Z_mod_mult, Z.div_mul by lia. repeat split; auto; try lia.
Qed.
Lemma get_shadow_eq st rid : get_shadow st rid = default shadow0 (s_shadow st !! rid).
Proof. reflexivity. Qed.
Lemma get_shadow_ext st st' rid : s_shadow st' = s_shadow st -> get_shadow st' rid = get_shadow st rid.
Proof. intros H. unfold get_shadow. rewrite H. reflexivity. Qed.
Lemma get_shadow_upd_shadow rid f st rid' :
get_shadow (upd_shadow rid f st) rid' = if (rid' =? rid)%N then f (get_shadow st rid) else get_shadow st rid'.
Proof.
unfold get_shadow, upd_shadow; cbn. destruct (N.eqb_spec rid' rid) as [->|NE];
[rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
Qed.
Lemma cell_read_wr8 p v st q :
cell_read (get_shadow (wr8 p v st) (fst q)) (snd q) =
if aptr_eqb q p then
(let r := get_shadow st (fst p) in
let hl := default [] (r_hav r !! (snd p / 16)) in
let hp := r_havp r !! (snd p / 4096) in
if stale_pg hp (Some (s_tick st)) || stale hl (snd p mod 16) (Some (s_tick st)) then Unknown (Z.land v 255) else Known (Z.land v 255))
else cell_read (get_shadow st (fst q)) (snd q).
Proof.
unfold wr8. rewrite get_shadow_upd_shadow. destruct (aptr_eqb_spec q p) as [->|NE].
- rewrite N.eqb_refl. unfold cell_read; cbn. rewrite lookup_insert_eq. reflexivity.
- destruct (N.eqb_spec (fst q) (fst p)) as [E|NE2]; [|reflexivity].
unfold cell_read; cbn. rewrite E. rewrite lookup_insert_ne; [reflexivity|].
intros E2. apply NE. destruct q, p; cbn in *; congruence.
Qed.
Definition sh_ticks (r : shadow) (t : N) : Prop :=
(forall u hl ch, r_hav r !! u = Some hl -> In ch hl -> (snd ch <= t)%N)
/\ (forall pg t', r_havp r !! pg = Some t' -> (t' <= t)%N).
Lemma not_stale_cur r t b : sh_ticks r t ->
forall u pg, stale_pg (r_havp r !! pg) (Some t) || stale (default [] (r_hav r !! u)) b (Some t) = false.
Proof.
intros [Hh Hp] u pg. apply Bool.orb_false_iff. split.
- destruct (r_havp r !! pg) as [t'|] eqn:E; cbn; [|reflexivity]. apply N.ltb_ge. eapply Hp; eauto.
- unfold stale. apply Bool.not_true_iff_false. rewrite existsb_exists. intros ([c h] & Hin & Hb). cbn in Hb.
apply Bool.andb_true_iff in Hb as [_ Hb]. apply N.ltb_lt in Hb.
destruct (r_hav r !! u) as [hl|] eqn:E; cbn in Hin; [|contradiction].
pose proof (Hh u hl (c, h) E Hin). cbn in H. lia.
Qed.
Lemma cell_read_wr8_same p v st : sh_ticks (get_shadow st (fst p)) (s_tick st) ->
cell_read (get_shadow (wr8 p v st) (fst p)) (snd p) = Known (Z.land v 255).
Proof.
intros HT. rewrite (cell_read_wr8 p v st p), aptr_eqb_refl. cbn zeta. rewrite (not_stale_cur _ _ _ HT). reflexivity.
Qed.
Lemma cell_read_wr8_other p v st q : q <> p ->
cell_read (get_shadow (wr8 p v st) (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Proof. intros NE. rewrite cell_read_wr8, aptr_eqb_neq by exact NE. reflexivity. Qed.
Lemma sh_ticks_wr8 p v st rid : sh_ticks (get_shadow st rid) (s_tick st) -> sh_ticks (get_shadow (wr8 p v st) rid) (s_tick st).
Proof.
intros H. unfold wr8. rewrite get_shadow_upd_shadow. destruct (N.eqb_spec rid (fst p)) as [->|NE]; [|exact H].
destruct H as [Hh Hp]. split; cbn; eauto.
Qed.
End CEIL_WRAP_9.
