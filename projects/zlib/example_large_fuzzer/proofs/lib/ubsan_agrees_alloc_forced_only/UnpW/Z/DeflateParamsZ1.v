(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface DeflateState Trees DeflateLz DeflateBlk Deflate DeflateParams.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FillWinModel DeflateSafe DeflateOverlay. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflateRel. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeL1 RefDeflSafeZ. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflSafeG RefDeflSafeI1 RefDeflSafeI3.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import DeflateParamsDD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cfunc_id_cases : forall l, 0 <= l <= 9 -> (cfunc_id l = 0 <-> l = 0) /\ (cfunc_id l = 2 <-> 4 <= l) /\ (cfunc_id l = 1 <-> 1 <= l <= 3).
Proof.
  intros l Hl. unfold cfunc_id.
  destruct (Z.eqb_spec l 0) as [E|E]; [subst; repeat split; intros; lia|].
  destruct (Z.leb_spec l 3); repeat split; intros; lia.
Qed.

Lemma dmode_zl : forall s, (ds_strategy s = 0 \/ ds_strategy s = 1) ->
  dmode s = (if ds_level s =? 0 then 0 else if ds_level s <=? 3 then 3 else 4).
Proof.
  intros s Hst. unfold dmode, Z_HUFFMAN_ONLY, Z_RLE.
  destruct (ds_level s =? 0); [reflexivity|].
  destruct Hst as [E|E]; rewrite E; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition pre_st (s : deflate_state) : deflate_state :=
  if Z.eqb (ds_level s) 0 && negb (Z.eqb (ds_matches s) 0) then
    set_matches (if Z.eqb (ds_matches s) 1 then slide_hash s else clear_hash s) 0
  else s.

Lemma dparams_set_level_eq : forall s level,
  dparams_set_level s level
  = (let '(good, lazy, nice, chain) := configuration_table level in
     set_max_chain_length (set_nice_match (set_good_match (set_max_lazy_match (set_level (pre_st s) level) lazy) good) nice) chain).
Proof. intros s level. unfold dparams_set_level, pre_st. reflexivity. Qed.

(* [comment removed for export] *)
Lemma pre_st_shape : forall s, dwf s ->
  exists hd pv,
    pre_st s = (if Z.eqb (ds_level s) 0 && negb (Z.eqb (ds_matches s) 0) then set_matches (set_prev (set_head s hd) pv) 0 else s)
    /\ arr_len hd = ds_hash_size s /\ arr_len pv = ds_w_size s
    /\ (forall i, 0 <= i < ds_hash_size s -> 0 <= arr_get hd i < 65536)
    /\ (forall i, 0 <= i < ds_w_size s -> 0 <= arr_get pv i < 65536).
Proof.
  intros s D. pose proof (df_hl _ D) as Lh. pose proof (df_pl _ D) as Lp. pose proof (df_hb _ D) as Bh. pose proof (df_pb _ D) as Bp.
  pose proof (dwf_sizes s D) as (Sw & Sh & _).
  unfold pre_st. destruct (Z.eqb (ds_level s) 0 && negb (Z.eqb (ds_matches s) 0)).
  - destruct (Z.eqb (ds_matches s) 1).
    + exists (slide_hash_loop (Z.to_nat (ds_hash_size s)) (ds_head s) (ds_hash_size s) (ds_w_size s)),
             (slide_hash_loop (Z.to_nat (ds_w_size s)) (ds_prev s) (ds_w_size s) (ds_w_size s)).
      split; [rewrite slide_hash_eq; reflexivity|].
      split; [rewrite slide_hash_loop_len; exact Lh|]. split; [rewrite slide_hash_loop_len; exact Lp|].
      split; intros i Hi; (apply slide_hash_loop_wf16; [rewrite Z2Nat.id; lia | lia | intros j Hj | lia]); [apply Bh | apply Bp]; lia.
    + exists (arr_fill (arr_set (ds_head s) (ds_hash_size s - 1) NIL) 0 (ds_hash_size s - 1) 0), (ds_prev s).
      split; [rewrite clear_hash_eq; destruct s; reflexivity|].
      split; [rewrite arr_len_fill, arr_len_set; exact Lh|]. split; [exact Lp|].
      split; [|exact Bp]. intros i Hi. rewrite arr_get_fill. unfold arr_inb. rewrite arr_len_set, Lh.
      destruct ((0 <=? i) && (i <? 0 + Z.max 0 (ds_hash_size s - 1)) && ((0 <=? i) && (i <? ds_hash_size s))); [lia|].
      rewrite arr_get_set. unfold arr_inb, NIL. rewrite Lh. destruct (_ && _); [lia | apply Bh; exact Hi].
  - exists (ds_head s), (ds_prev s). repeat split; try assumption. all: try (intros; apply Bh; assumption). all: intros; apply Bp; assumption.
Qed.

(* [comment removed for export] *)
Lemma pre_st_chain : forall s, dwf s -> ZLS s -> ds_level s = 0 ->
  CHAIN (pre_st s) (ds_strstart s - 1) (ds_strstart s - 1) /\ ds_matches (pre_st s) = 0.
Proof.
  intros s D (Z0 & _ & _) Hl0. pose proof (dwf_sizes s D) as (Sw & Sh & _).
  assert (Hm0 : dmode s = 0) by (unfold dmode; rewrite Hl0; reflexivity).
  destruct (Z0 Hm0) as (_ & C0 & C1).
  unfold pre_st. rewrite Hl0. change (0 =? 0) with true. cbn [andb].
  destruct (Z.eqb_spec (ds_matches s) 0) as [M0|M0]; cbn [negb].
  - split; [exact (C0 M0) | exact M0].
  - split; [|reflexivity].
    apply (CHAIN_same (if ds_matches s =? 1 then slide_hash s else clear_hash s)); try reflexivity.
    destruct (Z.eqb_spec (ds_matches s) 1) as [M1|M1].
    + replace (ds_strstart s - 1) with (ds_strstart s + ds_w_size s - 1 - ds_w_size s) by lia.
      apply (CHAIN_slide_hash s _ _ (ds_w_bits s) (C1 M1)).
      * exact (df_wsize _ D).
      * pose proof (df_wbits _ D). lia.
      * exact (df_wmask _ D).
      * exact (df_pl _ D).
      * exact (df_hl _ D).
      * lia.
      * exact (df_hb _ D).
      * exact (df_pb _ D).
    + apply CHAIN_clear_hash; [exact (df_hl _ D) | lia].
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition SWF (s : deflate_state) (level : Z) : Prop :=
  cfunc_id (ds_level s) <> cfunc_id level ->
  (cs_avail_in (ds_strm s) = 0 /\ ds_strstart s - ds_block_start s + ds_lookahead s = 0) \/ ds_last_flush s = -2.

(* [comment removed for export] *)
Lemma restrat_DD : forall s strategy,
  DD s -> ZLS s -> (strategy = 0 \/ strategy = 1) -> zl_modes s ->
  let s' := set_strategy s strategy in DD s' /\ ZLS s' /\ zl_modes s'.
Proof.
  intros s strategy [D X] HZ Hst [Hm Hos] s'.
  assert (Em : dmode s' = dmode s).
  { subst s'. rewrite (dmode_zl s Hos). rewrite dmode_zl by (dsred; exact Hst). dsred. reflexivity. }
  split; [split|split].
  - destruct D; constructor; subst s'; dsred; try assumption. unfold Z_FIXED. lia.
  - destruct X; constructor; rewrite ?Em; subst s'; dsred; try assumption.
  - unfold ZLS, PQ, PRI in *. rewrite Em. subst s'. dsred. exact HZ.
  - split; [rewrite Em; exact Hm | subst s'; dsred; exact Hst].
Qed.

(* [comment removed for export] *)
Lemma zl_level_cases : forall level, 0 <= level <= 9 -> (cfunc_id level = 0 \/ cfunc_id level = 2) -> level = 0 \/ 4 <= level <= 9.
Proof. intros level Hl Hc. destruct (cfunc_id_cases level Hl) as (A & B & _). destruct Hc as [Hc|Hc]; [left; tauto | right]. apply B in Hc. lia. Qed.

(* [comment removed for export] *)
Lemma relevel_slow_DD : forall s level strategy good lazy nice chain,
  DD s -> ZLS s -> 4 <= level <= 9 -> 4 <= ds_level s <= 9 -> (strategy = 0 \/ strategy = 1) -> zl_modes s ->
  configuration_table level = (good, lazy, nice, chain) ->
  let s' := set_strategy (set_max_chain_length (set_nice_match (set_good_match (set_max_lazy_match (set_level s level) lazy) good) nice) chain) strategy in
  DD s' /\ ZLS s' /\ zl_modes s'.
Proof.
  intros s level strategy good lazy nice chain [D X] HZ Hl Hol Hst [Hm Hos] Ecfg s'.
  assert (Em0 : dmode s = 4).
  { rewrite (dmode_zl s Hos). replace (ds_level s =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (ds_level s <=? 3) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
  assert (Em : dmode s' = dmode s).
  { rewrite Em0. subst s'. rewrite dmode_zl by (dsred; exact Hst). dsred.
    replace (level =? 0) with false by (symmetry; apply Z.eqb_neq; lia). replace (level <=? 3) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
  split; [split|split].
  - destruct D; constructor; subst s'; dsred; try assumption; unfold Z_FIXED; lia.
  - destruct X; constructor; rewrite ?Em; subst s'; dsred; try assumption. symmetry. exact Ecfg.
  - unfold ZLS, PQ, PRI in *. rewrite Em. subst s'. dsred. exact HZ.
  - split; [rewrite Em; exact Hm | subst s'; dsred; exact Hst].
Qed.

(* [comment removed for export] *)
Definition SWP (s : deflate_state) : Prop :=
  ds_lookahead s = 0 /\ ds_strstart s - ds_block_start s = 0 /\ ds_sym_next s = 0 /\ ds_match_available s = 0 /\ ds_match_length s = 2.

(* [comment removed for export] *)
Lemma to_stored_DD : forall s strategy good lazy nice chain,
  DD s -> ZLS s -> 4 <= ds_level s <= 9 -> (strategy = 0 \/ strategy = 1) -> zl_modes s -> SWP s ->
  configuration_table 0 = (good, lazy, nice, chain) ->
  let s' := set_strategy (set_max_chain_length (set_nice_match (set_good_match (set_max_lazy_match (set_level s 0) lazy) good) nice) chain) strategy in
  DD s' /\ ZLS s' /\ zl_modes s'.
Proof.
  intros s strategy good lazy nice chain [D X] (_ & HZ4 & HZP) Hol Hst [Hm Hos] (Hl0 & Hdiff & Hsn0 & Hma0 & Eml) Ecfg s'.
  assert (Em0 : dmode s = 4).
  { rewrite (dmode_zl s Hos). replace (ds_level s =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (ds_level s <=? 3) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
  assert (Em : dmode s' = 0) by (subst s'; unfold dmode; dsred; reflexivity).
  pose proof (df_look _ D) as Hlook. pose proof (df_strstart _ D) as Hstr.
  assert (Hn0 : nsym s = 0) by (unfold nsym; rewrite Hsn0; reflexivity).
  pose proof (dx_matches _ X) as Hmt.
  pose proof (dx_chain _ X ltac:(rewrite Em0; discriminate)) as HC.
  pose proof (dwf_sizes s D) as (Sw & _).
  split; [split|split].
  - destruct D; constructor; subst s'; dsred; try assumption; unfold Z_FIXED; lia.
  - destruct X; constructor; rewrite ?Em; subst s'; dsred; try assumption.
    + symmetry. exact Ecfg.
    + intros HH; discriminate HH.
    + intros _. exact Hma0.
    + intros HH; discriminate HH.
    + intros _. split; [exact Hl0|]. split; [clear - Hdiff Hstr; lia|]. split; [exact Hsn0 | clear - Hmt Hn0; lia].
    + intros HH. exfalso. apply HH. reflexivity.
    + intros HH. exfalso. apply HH. reflexivity.
  - unfold ZLS. rewrite Em. split; [intros _ | split; [intros HH; discriminate HH | unfold PRI in *; subst s'; dsred; exact HZP]]. subst s'. dsred.
    split; [exact Eml|]. split; intros _.
    + exact HC.
    + exact (CHAIN_mono s (ds_strstart s - 1) (ds_strstart s - 1) (ds_strstart s + ds_w_size s - 1) (ds_strstart s + ds_w_size s - 1) ltac:(lia) ltac:(lia) HC).
  - split; [rewrite Em; left; reflexivity | subst s'; dsred; exact Hst].
Qed.

(* [comment removed for export] *)
Lemma to_slow_DD : forall s level strategy good lazy nice chain,
  DD s -> ZLS s -> ds_level s = 0 -> 4 <= level <= 9 -> (strategy = 0 \/ strategy = 1) -> zl_modes s -> SWP s ->
  configuration_table level = (good, lazy, nice, chain) ->
  let s' := set_strategy (set_max_chain_length (set_nice_match (set_good_match (set_max_lazy_match (set_level (pre_st s) level) lazy) good) nice) chain) strategy in
  DD s' /\ ZLS s' /\ zl_modes s'.
Proof.
  intros s level strategy good lazy nice chain [D X] HZ Hl0 Hl Hst [Hm Hos] (Hlk0 & Hdiff & Hsn0 & Hma0 & _) Ecfg.
  assert (Em0 : dmode s = 0) by (unfold dmode; rewrite Hl0; reflexivity).
  destruct (pre_st_chain s D HZ Hl0) as [HC1 Hmt1]. destruct HZ as (HZ0 & _ & HZP). destruct (HZ0 Em0) as (Eml & _ & _).
  destruct (pre_st_shape s D) as (hd & pv & Epre & Lh & Lp & Bh & Bp). rewrite Epre in HC1, Hmt1 |- *. clear Epre.
  pose proof (dx_st0 _ X Em0) as (_ & Hbs & _ & Hmt2).
  pose proof (df_strstart _ D) as Hstr. pose proof (dwf_sizes s D) as (Sw & Sh & _).
  rewrite Hl0 in HC1, Hmt1 |- *. change (0 =? 0) with true in HC1, Hmt1 |- *. cbn [andb] in HC1, Hmt1 |- *.
  destruct (ds_matches s =? 0) eqn:M0; cbn [negb] in HC1, Hmt1 |- *; cbv zeta.
  all: match goal with |- DD ?x /\ _ => set (s' := x) end.
  all: assert (Em : dmode s' = 4) by
        (subst s'; rewrite dmode_zl by (dsred; exact Hst); dsred;
         replace (level =? 0) with false by (symmetry; apply Z.eqb_neq; lia); replace (level <=? 3) with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
  all: split; [split|split].
  all: try (destruct D; constructor; subst s'; dsred; try assumption; clear - Hl Hst; unfold Z_FIXED; lia).
  1,4: destruct X; constructor; rewrite ?Em; subst s'; dsred; try assumption.
  all: try (symmetry; exact Ecfg).
  all: try (intros HH; discriminate HH).
  all: try (intros HH; exfalso; apply HH; reflexivity).
  all: try (intros _; exact HC1).
  all: try (intros _; unfold nsym; dsred; rewrite Hsn0, Hma0; change (0 / 3) with 0; clear - Hdiff; lia).
  all: try (unfold nsym; dsred; rewrite Hsn0; change (0 / 3) with 0; clear; lia).
  all: try (intros _; split; [rewrite Eml; clear; lia|]; split;
            [intros HH; exfalso; rewrite Hma0 in HH; clear - HH; lia | intros HH; exfalso; rewrite Eml in HH; unfold MIN_MATCH in HH; clear - HH; lia]).
  (* [comment removed for export] *)
  all: try (unfold ZLS; rewrite Em; split; [intros HH; discriminate HH | split; [intros _; left; subst s'; dsred; split; [exact Hma0 | exact Hsn0] | unfold PRI in *; subst s'; dsred; exact HZP]]).
  all: try (split; [rewrite Em; right; reflexivity | subst s'; dsred; exact Hst]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zl_old_level : forall s, dwf s -> zl_modes s -> ds_level s = 0 \/ 4 <= ds_level s <= 9.
Proof.
  intros s D [Hm Hos]. pose proof (df_level _ D) as Hl. rewrite (dmode_zl s Hos) in Hm.
  destruct (Z.eqb_spec (ds_level s) 0) as [E|E]; [left; exact E | right].
  destruct (Z.leb_spec (ds_level s) 3) as [L|L]; [exfalso; destruct Hm as [Hm|Hm]; discriminate Hm | lia].
Qed.

(* [comment removed for export] *)
Lemma SWP_of : forall s level, DD s -> ZLS s -> zl_modes s -> SWF s level -> cfunc_id (ds_level s) <> cfunc_id level -> SWP s.
Proof.
  intros s level [D X] (HZ0 & HZ4 & HZP) [Hm Hos] HSW NE.
  pose proof (df_look _ D) as Hlook. pose proof (df_strstart _ D) as Hstr.
  destruct (HSW NE) as [[Hai Hsum]|Hlf].
  - destruct Hm as [Em0|Em0].
    + pose proof (dx_st0 _ X Em0) as (Hlk0 & Hbs & Hsn0 & _). pose proof (dx_notslow _ X ltac:(rewrite Em0; discriminate)) as Hma0.
      destruct (HZ0 Em0) as (Eml & _). split; [exact Hlk0|]. split; [clear - Hsum Hlk0; lia|]. split; [exact Hsn0|]. split; [exact Hma0 | exact Eml].
    + pose proof (dx_ext _ X ltac:(rewrite Em0; discriminate)) as Hext.
      assert (Hl0 : ds_lookahead s = 0) by (clear - Hext Hlook Hsum; lia). assert (Hdiff : ds_strstart s - ds_block_start s = 0) by (clear - Hext Hlook Hsum; lia).
      destruct (HZ4 Em0) as [[Hma0 Hsn0]|Hbad]; [|exfalso; clear - Hbad Hdiff; lia].
      pose proof (dx_slow _ X Em0) as (Hml2 & _ & Hml3). pose proof (dx_ml _ X) as Hml.
      assert (Eml : ds_match_length s = 2) by (unfold MIN_MATCH in Hml3; destruct (Z_le_gt_dec 3 (ds_match_length s)); [specialize (Hml3 ltac:(clear - l; lia)); clear - Hml3 Hl0 l; lia | clear - Hml2 g; lia]).
      split; [exact Hl0|]. split; [exact Hdiff|]. split; [exact Hsn0|]. split; [exact Hma0 | exact Eml].
  - destruct (HZP Hlf) as (P1 & P2 & P3 & P4 & P5 & P6). split; [exact P1|]. split; [rewrite P2, P3; reflexivity|]. split; [exact P4|]. split; [exact P5 | exact P6].
Qed.

Theorem set_level_DD : forall s level strategy,
  DD s -> ZLS s -> 0 <= level <= 9 -> (strategy = 0 \/ strategy = 1) -> zl_side s level -> SWF s level ->
  let s' := set_strategy (if negb (ds_level s =? level) then dparams_set_level s level else s) strategy in
  DD s' /\ ZLS s' /\ zl_modes s'.
Proof.
  intros s level strategy HDD HZ Hl Hst [Hmo Hcl] HSW. cbv zeta. pose proof HDD as [D X].
  pose proof (zl_level_cases level Hl Hcl) as Hnew. pose proof (zl_old_level s D Hmo) as Hold.
  pose proof (cfunc_id_cases level Hl) as (N0 & N2 & _). pose proof (cfunc_id_cases (ds_level s) (df_level _ D)) as (O0 & O2 & _).
  destruct (Z.eqb_spec (ds_level s) level) as [EL|NL]; cbn [negb].
  - exact (restrat_DD s strategy HDD HZ Hst Hmo).
  - rewrite dparams_set_level_eq. destruct (configuration_table level) as [[[good lazy] nice] chain] eqn:Ecfg. cbv zeta.
    destruct Hold as [Hold|Hold]; destruct Hnew as [Hnew|Hnew]; [exfalso; lia| | |].
    + (* [comment removed for export] *)
      pose proof (SWP_of s level HDD HZ Hmo HSW ltac:(intros EQ; rewrite (proj2 O0 Hold) in EQ; rewrite (proj2 N2 (proj1 Hnew)) in EQ; discriminate EQ)) as HP.
      exact (to_slow_DD s level strategy good lazy nice chain HDD HZ Hold Hnew Hst Hmo HP Ecfg).
    + (* [comment removed for export] *)
      subst level.
      pose proof (SWP_of s 0 HDD HZ Hmo HSW ltac:(intros EQ; rewrite (proj2 N0 eq_refl) in EQ; rewrite (proj2 O2 (proj1 Hold)) in EQ; discriminate EQ)) as HP.
      replace (pre_st s) with s by (unfold pre_st; replace (ds_level s =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
      exact (to_stored_DD s strategy good lazy nice chain HDD HZ Hold Hst Hmo HP Ecfg).
    + (* [comment removed for export] *)
      replace (pre_st s) with s by (unfold pre_st; replace (ds_level s =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
      exact (relevel_slow_DD s level strategy good lazy nice chain HDD HZ Hnew Hold Hst Hmo Ecfg).
Qed.
