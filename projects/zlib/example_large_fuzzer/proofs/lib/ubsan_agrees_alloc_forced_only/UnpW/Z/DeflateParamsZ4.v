(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface DeflateState Trees DeflateLz DeflateBlk Deflate DeflateSafe DeflateOverlay.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FillWinModel FlushBlockModel. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflateRel. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeL1 RefDeflSafeZ. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflSafeG. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflFastM. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflFast1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflSafeS RefDeflSafeI1 RefDeflSafeI2 RefDeflSafeI3 RefDeflSafeI4 RefDeflSafeL0 RefDeflSafeL2 RefDeflSafeL3 RefDeflSafeL4 RefDeflSafeL5 RefDeflSafeI6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import DeflateParamsDD DeflateParamsZ2 DeflateParamsZ3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition zq (s : deflate_state) :=
  (ds_match_length s, ds_level s, ds_strategy s, ds_strstart s, ds_matches s, ds_block_start s, ds_match_available s, ds_sym_next s,
   (ds_head s, ds_prev s, ds_hash_size s, ds_w_size s, ds_w_mask s), (ds_last_flush s, ds_lookahead s)).

Lemma keeps_zq : keeps zq true false.
Proof. constructor; intros; try discriminate; try match goal with tt : tree_id |- _ => destruct tt end; match goal with ss : deflate_state |- _ => destruct ss; reflexivity end. Qed.

Definition QQ (s : deflate_state) : Prop := ZLS s /\ zl_modes s.
(* [comment removed for export] *)
Definition QQ' (s : deflate_state) : Prop := QQ s /\ ds_last_flush s <> -2.

Lemma zq_fields : forall a b, zq b = zq a ->
  ds_match_length b = ds_match_length a /\ ds_level b = ds_level a /\ ds_strategy b = ds_strategy a /\ ds_strstart b = ds_strstart a
  /\ ds_matches b = ds_matches a /\ ds_block_start b = ds_block_start a /\ ds_match_available b = ds_match_available a /\ ds_sym_next b = ds_sym_next a
  /\ ds_head b = ds_head a /\ ds_prev b = ds_prev a /\ ds_hash_size b = ds_hash_size a /\ ds_w_size b = ds_w_size a /\ ds_w_mask b = ds_w_mask a
  /\ ds_last_flush b = ds_last_flush a /\ ds_lookahead b = ds_lookahead a.
Proof.
  intros a b E. unfold zq in E.
  repeat match type of E with (_, _) = (_, _) => apply pair_equal_spec in E; destruct E as [E ?] end.
  repeat match goal with H : (_, _) = (_, _) |- _ => apply pair_equal_spec in H; destruct H as [H ?] end.
  repeat split; assumption.
Qed.

Lemma QQ_zq : forall a b, zq b = zq a -> QQ a -> QQ b.
Proof.
  intros a b E [HZ HM]. pose proof (zq_fields a b E) as (Eml & Elv & Esy & Estr & Emt & Ebs & Ema & Esn & Ehd & Epv & Ehs & Ews & Ewm & Elf & Elk).
  assert (Em : dmode b = dmode a) by (unfold dmode; rewrite Elv, Esy; reflexivity).
  split.
  - unfold ZLS, PQ, PRI in *. rewrite Em, Eml, Estr, Emt, Ebs, Ema, Esn, Ews, Elf, Elk.
    destruct HZ as (Z0 & Z4 & ZP). split; [| exact (conj Z4 ZP)]. intros M. destruct (Z0 M) as (A & B & C). split; [exact A|].
    split; intros MM; apply (CHAIN_same a b); try assumption; [apply B | apply C]; exact MM.
  - unfold zl_modes in *. rewrite Em, Esy. exact HM.
Qed.

Lemma QQ'_zq : forall a b, zq b = zq a -> QQ' a -> QQ' b.
Proof.
  intros a b E [HQ Hlf]. split; [exact (QQ_zq a b E HQ)|].
  pose proof (zq_fields a b E) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Elf & _). rewrite Elf. exact Hlf.
Qed.

Lemma QQ'_set_last_flush : forall s v, v <> -2 -> QQ s -> QQ' (set_last_flush s v).
Proof.
  intros s v Hv [(Z0 & Z4 & ZP) HM]. split; [| exact Hv]. split; [| exact HM].
  split; [exact Z0|]. split; [exact Z4|]. intros E. exfalso. exact (Hv E).
Qed.

Lemma QQ'_QQ : forall s, QQ' s -> QQ s.
Proof. intros s [H _]. exact H. Qed.

Lemma zq_flush_pending : forall s, zq (flush_pending s) = zq s.
Proof.
  intros s. rewrite flush_pending_eq. cbv zeta.
  pose proof (k_bi_flush zq true false keeps_zq eq_refl s) as EB. unfold tr_flush_bits.
  destruct (fp_len _ =? 0); [exact EB|].
  unfold fp_tail. destruct (_ =? 0); (etransitivity; [|exact EB]); reflexivity.
Qed.

Lemma zq_put_byte : forall s c, zq (put_byte s c) = zq s.
Proof. intros. apply (k_put_byte zq true false keeps_zq eq_refl). Qed.
Lemma zq_set_strm : forall s c, zq (set_strm s c) = zq s. Proof. intros. reflexivity. Qed.
Lemma zq_set_status : forall s v, zq (set_status s v) = zq s. Proof. intros. reflexivity. Qed.
Lemma zq_set_wrap : forall s v, zq (set_wrap s v) = zq s. Proof. intros. reflexivity. Qed.
Lemma zq_err_return : forall s e, zq (fst (err_return s e)) = zq s. Proof. intros. reflexivity. Qed.

Lemma zq_putShortMSB : forall s b, zq (putShortMSB s b) = zq s.
Proof. intros. unfold putShortMSB. rewrite !zq_put_byte. reflexivity. Qed.

Lemma zq_zhdr : forall s, zq (zhdr_st s) = zq s.
Proof.
  intros s. unfold zhdr_st. cbv zeta. rewrite zq_set_status, zq_set_strm.
  destruct (negb _); rewrite ?zq_putShortMSB; reflexivity.
Qed.

Lemma zq_gzhdr : forall s, zq (gzhdr_st s) = zq s.
Proof. intros s. unfold gzhdr_st. rewrite zq_set_status, !zq_put_byte, zq_set_strm. reflexivity. Qed.

Lemma zq_trailer : forall s, zq (trailer_st s) = zq s.
Proof. intros s. unfold trailer_st. cbv zeta. destruct (_ =? 2); rewrite ?zq_put_byte, ?zq_putShortMSB; reflexivity. Qed.

Lemma zq_tr_align : forall s, zq (tr_align s) = zq s.
Proof.
  intros s. unfold tr_align, send_code.
  rewrite (k_bi_flush zq true false keeps_zq eq_refl), !(k_send_bits zq true false keeps_zq eq_refl). reflexivity.
Qed.

Lemma zq_bdone : forall s flush, flush <> Z_FULL_FLUSH -> zq (bdone_st s flush) = zq s.
Proof.
  intros s flush Hf. unfold bdone_st.
  destruct (flush =? Z_PARTIAL_FLUSH); [apply zq_tr_align|].
  destruct (negb (flush =? Z_BLOCK)); [|reflexivity].
  replace (flush =? Z_FULL_FLUSH) with false by (symmetry; apply Z.eqb_neq; exact Hf).
  apply (k_tr_stored_block zq true false keeps_zq eq_refl).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lv_last_flush : forall a b, lv b = lv a -> ds_last_flush b = ds_last_flush a.
Proof. intros a b E. unfold lv in E. injection E as _ _ E3. exact E3. Qed.

Lemma QQ'_bf : forall c0 s flush, BFPRE c0 s flush -> QQ' s -> QQ' (fst (run_compress_func s flush)).
Proof.
  intros c0 s flush PRE [[HZ [Hm Hos]] Hlf]. pose proof PRE as (HC0 & HDC & Hp & Hst & Hfl).
  rewrite run_compress_func_dmode. destruct HZ as (Z0 & Z4 & ZP).
  destruct Hm as [Hm|Hm]; rewrite Hm.
  - (* [comment removed for export] *)
    destruct (Z0 Hm) as (Eml & C0 & C1).
    destruct (stored_ZLS0 c0 s flush PRE Hm (conj Eml (conj C0 C1))) as [Et (Eml' & C0' & C1')].
    pose proof (zt_fields _ _ Et) as (_ & Elv & Esy & Elf & _).
    assert (Elv' : lv (fst (deflate_stored s flush)) = lv s) by (unfold lv; rewrite Elv, Esy, Elf; reflexivity).
    pose proof (dmode_lv _ _ Elv') as Em'. rewrite Hm in Em'.
    split; [| rewrite Elf; exact Hlf].
    split; [| apply (zl_modes_lv s _ Elv'); split; [left; exact Hm | exact Hos]].
    split; [intros _; exact (conj Eml' (conj C0' C1')) |]. split; [intros M; exfalso; rewrite Em' in M; discriminate M|].
    intros E. exfalso. rewrite Elf in E. exact (Hlf E).
  - (* [comment removed for export] *)
    destruct (slow_PQ c0 s flush PRE Hm (Z4 Hm)) as [HP Elv].
    pose proof (dmode_lv _ _ Elv) as Em'. rewrite Hm in Em'. pose proof (lv_last_flush _ _ Elv) as Elf.
    split; [| rewrite Elf; exact Hlf].
    split; [| apply (zl_modes_lv s _ Elv); split; [right; exact Hm | exact Hos]].
    split; [intros M; exfalso; rewrite Em' in M; discriminate M |]. split; [intros _; exact HP|].
    intros E. exfalso. rewrite Elf in E. exact (Hlf E).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Core.
  Variable c0 : cstrm.
  Variable s0 : deflate_state.
  Hypothesis HC0 : C0OK' c0.
  Hypothesis Hs0 : ds_strm s0 = c0.
  Hypothesis D0 : dwf s0.
  Let HC0w : C0OK c0 := c0'_ok _ HC0.

  Local Notation ST := (RefDeflSafeI4.ST c0 s0).

  (* [comment removed for export] *)
  Lemma blocks_QQ : forall s flush, ST s -> ds_pending s = 0 -> (flush = Z_NO_FLUSH \/ flush = Z_FINISH \/ flush = Z_BLOCK) ->
    (ds_status s = FINISH_STATE -> cs_avail_in (ds_strm s) = 0) ->
    QQ' s -> QQ' (fst (deflate_blocks s flush)).
  Proof.
    intros s flush HS Hp Hfl Hfin HQ. pose proof HS as [H K]. pose proof H as [[D X] V].
    assert (Hfl' : 0 <= flush <= 5) by (unfold Z_NO_FLUSH, Z_FINISH, Z_BLOCK in Hfl; lia).
    assert (Hff : flush <> Z_FULL_FLUSH) by (unfold Z_NO_FLUSH, Z_FINISH, Z_BLOCK, Z_FULL_FLUSH in *; lia).
    unfold deflate_blocks.
    match goal with |- context [if ?c then _ else (s, None)] => destruct c eqn:Hcond end; [| cbn [fst]; exact HQ].
    assert (Hst0 : ds_status s <> FINISH_STATE).
    { intros Ef. rewrite (Hfin Ef), (dx_fin _ X Ef), Ef in Hcond. cbn in Hcond. rewrite andb_false_r in Hcond. discriminate Hcond. }
    assert (PRE : BFPRE c0 s flush) by (split; [exact HC0|]; split; [exact H|]; split; [exact Hp|]; split; [exact Hst0 | exact Hfl']).
    pose proof (QQ'_bf c0 s flush PRE HQ) as HQ1.
    assert (EX : exists x, x = run_compress_func s flush) by (eexists; reflexivity). destruct EX as [[s1 bst] Erun]. rewrite <- Erun in *. cbn [fst] in HQ1.
    cbv beta iota zeta.
    assert (EX : exists x, x = (if block_state_eqb bst finish_started || block_state_eqb bst finish_done then set_status s1 FINISH_STATE else s1)) by (eexists; reflexivity).
    destruct EX as [s2 Es2].
    assert (HQ2 : QQ' s2) by (apply (QQ'_zq s1); [subst s2; destruct (block_state_eqb bst finish_started || block_state_eqb bst finish_done); [apply zq_set_status | reflexivity] | exact HQ1]).
    rewrite <- Es2.
    destruct (block_state_eqb bst need_more || block_state_eqb bst finish_started).
    { cbn [fst]. destruct (cs_avail_out (ds_strm s2) =? 0); [apply QQ'_set_last_flush; [clear; lia | exact (QQ'_QQ _ HQ2)] | exact HQ2]. }
    destruct (block_state_eqb bst block_done); [| cbn [fst]; exact HQ2].
    match goal with |- context [flush_pending ?b] => replace b with (bdone_st s2 flush) by (unfold bdone_st; reflexivity) end.
    assert (HQ3 : QQ' (flush_pending (bdone_st s2 flush))).
    { apply (QQ'_zq s2); [| exact HQ2]. rewrite zq_flush_pending. apply zq_bdone. exact Hff. }
    destruct (cs_avail_out (ds_strm (flush_pending (bdone_st s2 flush))) =? 0); cbn [fst]; [| exact HQ3].
    apply QQ'_set_last_flush; [clear; lia | exact (QQ'_QQ _ HQ3)].
  Qed.

  (* [comment removed for export] *)
  Theorem core_QQ : forall flush, ST s0 -> (flush = Z_NO_FLUSH \/ flush = Z_FINISH \/ flush = Z_BLOCK) ->
    QQ s0 -> QQ (fst (deflate_core s0 flush)).
  Proof.
    intros flush HS0 Hfl HQ0. pose proof HS0 as [H K]. pose proof H as [[D X] V].
    assert (Hfl16 : 0 <= flush < 16) by (unfold Z_NO_FLUSH, Z_FINISH, Z_BLOCK in Hfl; lia).
    assert (Hfl5 : 0 <= flush <= 5) by (unfold Z_NO_FLUSH, Z_FINISH, Z_BLOCK in Hfl; lia).
    unfold deflate_core.
    destruct (deflateStateCheck s0 || (Z_BLOCK <? flush) || (flush <? 0)) eqn:Echk; [cbn [fst]; exact HQ0|].
    destruct ((ds_status s0 =? FINISH_STATE) && negb (flush =? Z_FINISH)); [apply (QQ_zq s0); [apply zq_err_return | exact HQ0]|].
    destruct (cs_avail_out (ds_strm s0) =? 0); [apply (QQ_zq s0); [apply zq_err_return | exact HQ0]|].
    cbv zeta.
    pose proof (ST_set_last_flush c0 s0 s0 flush HS0 ltac:(clear - Hfl5; lia)) as HS1.
    assert (HQ1 : QQ' (set_last_flush s0 flush)) by (apply QQ'_set_last_flush; [clear - Hfl5; lia | exact HQ0]).
    assert (EX : exists x, x = set_last_flush s0 flush) by (eexists; reflexivity). destruct EX as [s1 Es1]. rewrite <- Es1 in *.
    match goal with |- QQ (fst (let '(s, r) := ?head in _)) => destruct head as [s2 r2] eqn:Ehead end.
    assert (H2 : ST s2 /\ QQ' s2 /\ (r2 = None -> ds_pending s2 = 0)).
    { destruct (negb (ds_pending s1 =? 0)) eqn:Ep.
      - destruct (ST_flush_pending c0 s0 HC0 s1 HS1) as (HSf & _ & Hor & _).
        assert (HQf : QQ' (flush_pending s1)) by (apply (QQ'_zq s1); [apply zq_flush_pending | exact HQ1]).
        destruct (Z.eqb_spec (cs_avail_out (ds_strm (flush_pending s1))) 0) as [Ea|Ea]; injection Ehead as EhA EhB; subst s2 r2.
        + split; [apply ST_set_last_flush; [exact HSf|lia] |]. split; [apply QQ'_set_last_flush; [clear; lia | exact (QQ'_QQ _ HQf)] | intros HH; discriminate HH].
        + split; [exact HSf|]. split; [exact HQf | intros _; lia].
      - destruct ((cs_avail_in (ds_strm s1) =? 0) && (RANK flush <=? RANK (ds_last_flush s0)) && negb (flush =? Z_FINISH)).
        + unfold err_return in Ehead. injection Ehead as EhA EhB; subst s2 r2. split; [exact (ST_err_return c0 s0 _ Z_BUF_ERROR HS1)|].
          split; [apply (QQ'_zq s1); [apply zq_err_return | exact HQ1] | intros HH; discriminate HH].
        + injection Ehead as EhA EhB; subst s2 r2. split; [exact HS1|]. split; [exact HQ1|]. intros _. destruct (Z.eqb_spec (ds_pending s1) 0); [assumption | discriminate Ep]. }
    clear Ehead. destruct H2 as (HS2 & HQ2 & Hp2).
    destruct r2 as [rc|]; [cbn [fst]; exact (QQ'_QQ _ HQ2)|]. specialize (Hp2 eq_refl).
    destruct ((ds_status s2 =? FINISH_STATE) && negb (cs_avail_in (ds_strm s2) =? 0)) eqn:Efa; [apply (QQ_zq s2); [apply zq_err_return | exact (QQ'_QQ _ HQ2)]|].
    assert (EX : exists x, x = (if (ds_status s2 =? INIT_STATE) && (ds_wrap s2 =? 0) then set_status s2 BUSY_STATE else s2)) by (eexists; reflexivity).
    destruct EX as [s4 Es4].
    assert (HS4 : ST s4 /\ QQ' s4 /\ ds_pending s4 = 0 /\ cs_avail_in (ds_strm s4) = cs_avail_in (ds_strm s2)
                  /\ (ds_status s4 = FINISH_STATE -> ds_status s2 = FINISH_STATE)).
    { subst s4. destruct ((ds_status s2 =? INIT_STATE) && (ds_wrap s2 =? 0)) eqn:E.
      - apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. pose proof HS2 as [H2' _].
        destruct (DC_set_status c0 s2 BUSY_STATE H2' ltac:(unfold BUSY_STATE; lia) ltac:(intros; exfalso; lia) ltac:(unfold BUSY_STATE, FINISH_STATE; intros; lia)) as (H4 & K4 & S4).
        split; [split; [exact H4 | rewrite K4; exact (proj2 HS2)]|]. split; [apply (QQ'_zq s2); [apply zq_set_status | exact HQ2]|].
        unfold set_status; dsred. split; [exact Hp2|]. split; [reflexivity|].
        unfold BUSY_STATE, FINISH_STATE. intros; lia.
      - split; [exact HS2|]. split; [exact HQ2|]. split; [exact Hp2|]. split; [reflexivity | intros E'; exact E']. }
    rewrite <- Es4. clear Es4. destruct HS4 as (HS4 & HQ4 & Hp4 & Ai4 & Fin4).
    rewrite deflate_zlib_header_eq.
    match goal with |- QQ (fst (let '(s, r) := ?head in _)) => destruct head as [s5 r5] eqn:Ehead end.
    assert (H5 : ST s5 /\ QQ' s5 /\ (r5 = None -> ds_pending s5 = 0 /\ cs_avail_in (ds_strm s5) = cs_avail_in (ds_strm s2)
                                        /\ (ds_status s5 = FINISH_STATE -> ds_status s2 = FINISH_STATE))).
    { destruct (Z.eqb_spec (ds_status s4) INIT_STATE) as [E|E].
      - destruct (hdr_zlib c0 s0 HC0 Hs0 D0 s4 HS4 Hp4 E) as (_ & HSz & Stz & Horz & Aiz & _).
        assert (HQz : QQ' (flush_pending (zhdr_st s4))) by (apply (QQ'_zq s4); [rewrite zq_flush_pending; apply zq_zhdr | exact HQ4]).
        cbv zeta in Ehead. destruct (negb (ds_pending (flush_pending (zhdr_st s4)) =? 0)) eqn:Ep; injection Ehead as EhA EhB; subst s5 r5.
        + split; [apply ST_set_last_flush; [exact HSz | lia]|]. split; [apply QQ'_set_last_flush; [clear; lia | exact (QQ'_QQ _ HQz)] | intros HH; discriminate HH].
        + split; [exact HSz|]. split; [exact HQz|]. intros _. rewrite Aiz, Stz. split; [destruct (Z.eqb_spec (ds_pending (flush_pending (zhdr_st s4))) 0); [assumption | discriminate Ep]|].
          split; [exact Ai4 | unfold BUSY_STATE, FINISH_STATE; intros; lia].
      - injection Ehead as EhA EhB; subst s5 r5. split; [exact HS4|]. split; [exact HQ4|]. intros _. split; [exact Hp4|]. split; [exact Ai4 | exact Fin4]. }
    clear Ehead. destruct H5 as (HS5 & HQ5 & Hr5).
    destruct r5 as [rc|]; [cbn [fst]; exact (QQ'_QQ _ HQ5)|]. destruct (Hr5 eq_refl) as (Hp5 & Ai5 & Fin5).
    rewrite deflate_gzip_header_eq.
    match goal with |- QQ (fst (let '(s, r) := ?head in _)) => destruct head as [s6 r6] eqn:Ehead end.
    assert (H6 : ST s6 /\ QQ' s6 /\ (r6 = None -> ds_pending s6 = 0 /\ cs_avail_in (ds_strm s6) = cs_avail_in (ds_strm s2)
                                        /\ (ds_status s6 = FINISH_STATE -> ds_status s2 = FINISH_STATE))).
    { destruct (Z.eqb_spec (ds_status s5) GZIP_STATE) as [E|E].
      - destruct (hdr_gzip c0 s0 HC0 Hs0 D0 s5 HS5 Hp5 E) as (_ & HSz & Stz & Horz & Aiz & _).
        assert (HQz : QQ' (flush_pending (gzhdr_st s5))) by (apply (QQ'_zq s5); [rewrite zq_flush_pending; apply zq_gzhdr | exact HQ5]).
        cbv zeta in Ehead. destruct (negb (ds_pending (flush_pending (gzhdr_st s5)) =? 0)) eqn:Ep; injection Ehead as EhA EhB; subst s6 r6.
        + split; [apply ST_set_last_flush; [exact HSz | lia]|]. split; [apply QQ'_set_last_flush; [clear; lia | exact (QQ'_QQ _ HQz)] | intros HH; discriminate HH].
        + split; [exact HSz|]. split; [exact HQz|]. intros _. rewrite Aiz, Stz. split; [destruct (Z.eqb_spec (ds_pending (flush_pending (gzhdr_st s5))) 0); [assumption | discriminate Ep]|].
          split; [exact Ai5 | unfold BUSY_STATE, FINISH_STATE; intros; lia].
      - injection Ehead as EhA EhB; subst s6 r6. split; [exact HS5|]. split; [exact HQ5|]. intros _. split; [exact Hp5|]. split; [exact Ai5 | exact Fin5]. }
    clear Ehead. destruct H6 as (HS6 & HQ6 & Hr6).
    destruct r6 as [rc|]; [cbn [fst]; exact (QQ'_QQ _ HQ6)|]. destruct (Hr6 eq_refl) as (Hp6 & Ai6 & Fin6).
    assert (Hfin6 : ds_status s6 = FINISH_STATE -> cs_avail_in (ds_strm s6) = 0).
    { intros E. rewrite Ai6. pose proof (Fin6 E) as E2. rewrite E2 in Efa. cbn in Efa.
      destruct (Z.eqb_spec (cs_avail_in (ds_strm s2)) 0); [assumption | discriminate Efa]. }
    pose proof (blocks_QQ s6 flush HS6 Hp6 Hfl Hfin6 HQ6) as HQ7.
    destruct (blocks_stage _ _ _ _ stored_bf_spec (huff_bf_spec FB_CALL_ok) (rle_bf_spec FB_CALL_ok) (fast_bf_spec FB_CALL_ok) (slow_bf_spec FB_CALL_ok) c0 s0 HC0 Hs0 D0 s6 flush HS6 Hp6 ltac:(lia) Hfin6) as (_ & HSr & Hr).
    destruct (deflate_blocks s6 flush) as [s7 r7]. cbn [fst snd] in HSr, Hr, HQ7.
    destruct r7 as [rc|]; [cbn [fst]; exact (QQ'_QQ _ HQ7)|].
    destruct (negb (flush =? Z_FINISH)) eqn:Ef; [cbn [fst]; exact (QQ'_QQ _ HQ7)|].
    destruct (Z.leb_spec (ds_wrap s7) 0); [cbn [fst]; exact (QQ'_QQ _ HQ7)|].
    rewrite deflate_trailer_eq. cbv zeta. cbn [fst].
    apply (QQ_zq s7); [| exact (QQ'_QQ _ HQ7)]. destruct (0 <? _); rewrite ?zq_set_wrap, zq_flush_pending; apply zq_trailer.
  Qed.
End Core.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma QQ_load : forall s c, QQ s -> QQ (set_strm s c).
Proof. intros s c [HZ HM]. split; [exact (ZLS_load s c HZ) | exact HM]. Qed.

(* [comment removed for export] *)
Theorem deflate_core_QQ : forall s zc flush,
  DD s -> dcall_wf zc -> (flush = Z_NO_FLUSH \/ flush = Z_FINISH \/ flush = Z_BLOCK) -> ZLS s -> zl_modes s ->
  let s0 := set_strm s (cstrm_of_call zc) in
  DD (fst (deflate_core s0 flush)) /\ ZLS (fst (deflate_core s0 flush)) /\ zl_modes (fst (deflate_core s0 flush)).
Proof.
  intros s zc flush HDD Hzc Hfl HZ HM s0.
  assert (Hfl16 : 0 <= flush < 16) by (unfold Z_NO_FLUSH, Z_FINISH, Z_BLOCK in Hfl; lia).
  set (c0 := cstrm_of_call zc) in *.
  pose proof (C0OK'_of_call zc Hzc) as HC0. fold c0 in HC0.
  assert (H0 : DC c0 s0) by (split; [apply DD_set_strm; exact HDD | subst s0 c0; apply SV_entry; exact Hzc]).
  pose proof H0 as [[D0 X0] V0].
  assert (HS0 : ST c0 s0 s0) by (split; [exact H0 | reflexivity]).
  pose proof (core_result _ _ _ _ stored_bf_spec (huff_bf_spec FB_CALL_ok) (rle_bf_spec FB_CALL_ok) (fast_bf_spec FB_CALL_ok) (slow_bf_spec FB_CALL_ok)
                c0 s0 HC0 eq_refl D0 flush HS0 Hfl16) as [[HDD' _] _].
  pose proof (core_QQ c0 s0 HC0 eq_refl D0 flush HS0 Hfl (QQ_load s _ (conj HZ HM))) as [HZ' HM'].
  split; [exact HDD' | split; [exact HZ' | exact HM']].
Qed.

Theorem deflate_ZLS : deflate_ZLS_stmt.
Proof.
  intros s zc flush HDD HZ Hzc Hfl HM. unfold deflate_m.
  destruct (deflate_core_QQ s zc flush HDD Hzc Hfl HZ HM) as (_ & HZ' & _).
  destruct (deflate_core (set_strm s (cstrm_of_call zc)) flush) as [s' rc]. cbn [fst] in *. exact HZ'.
Qed.

Theorem deflate_zl_modes : forall s zc flush,
  DD s -> ZLS s -> dcall_wf zc -> (flush = Z_NO_FLUSH \/ flush = Z_FINISH \/ flush = Z_BLOCK) -> zl_modes s ->
  zl_modes (fst (deflate_m s zc flush)).
Proof.
  intros s zc flush HDD HZ Hzc Hfl HM. unfold deflate_m.
  destruct (deflate_core_QQ s zc flush HDD Hzc Hfl HZ HM) as (_ & _ & HM').
  destruct (deflate_core (set_strm s (cstrm_of_call zc)) flush) as [s' rc]. cbn [fst] in *. exact HM'.
Qed.
