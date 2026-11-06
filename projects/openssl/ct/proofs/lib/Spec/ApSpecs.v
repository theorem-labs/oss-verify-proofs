(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim BnModel BnTree BgState ApBase ApState ApLogic ApErr ApCnf ApInv
  ApFmt ApParse ApPrim ApObj ApObjTab ApBn ApParse2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Inv.
Context {ptr : Type}.
Local Notation ST := (ap_st ptr) (only parsing).
Variables rcrit rcritS rcritI : Z -> Z -> Prop.      (* [comment removed for export] *)
Variable spre : sysop -> Prop.
Local Notation awp := (awp (okAp AP_NB AP_TOT) rcrit rcritS rcritI spre) (only parsing).
Hypothesis Hrc_grow : forall m, 0 <= m <= 46 -> rcrit m 1024.
Hypothesis Hrc_shrink : forall n, 1 <= n <= 46 -> rcritS 1024 n.
Hypothesis Hspre : forall o, spre o.

(* [comment removed for export] *)
Ltac nlia := unfold SZ_ASN1_STRING, SZ_ASN1_OBJECT, SZ_BIO, SZ_PREFIX_CTX, SZ_CNF_NAME, SZ_CONF, SZ_MUTEX, SZ_LHASH, SZ_LH_BUCKETS in *;
  unfold R_NB, R_TOT, ST_NB, ST_TOT in *; unfold AP_TOT in *; unfold AP_NB, AP_MAX_INPUT in *; unfold zlength in *; simpl; lia.

Lemma lt62b n : 0 <= n <= 100000000 -> 0 <= n < 2^62.
Proof. intros H. assert (E : 2^62 = 4611686018427387904) by reflexivity. rewrite E. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma print_info_spec : forall offset depth hl len j s R X, rel s R X -> frameR R ->
  0 < hdr_len offset depth hl len (j =? 33) < 128 ->
  awp (print_info (ptr:=ptr) offset depth hl len j s) X (fun r X' => rel (snd r) R X' /\ snd r = s).
Proof.
  intros offset depth hl len j s R X [Hs HP] HF Hn. unfold print_info.
  destruct ((hdr_len offset depth hl len (j =? 33) <=? 0) || (128 <=? hdr_len offset depth hl len (j =? 33))) eqn:E.
  { exfalso. apply Bool.orb_true_iff in E. destruct E as [E|E]; [apply Z.leb_le in E|apply Z.leb_le in E]; lia. }
  cbn -[SZ_BIO SZ_PREFIX_CTX hdr_len Z.add Z.leb Z.eqb orb].
  split; [apply lt62; unfold SZ_BIO; lia|].
  split; [eapply (relL_ok s [] R); [exact Hs|exact HP|exact HF|unfold zlength; cbn; lia|apply Forall_nil|unfold SZ_BIO; lia|rewrite bsum_nil; unfold SZ_BIO; lia]|].
  split; [reflexivity|]. intros bio Hbio.
  split; [apply lt62; unfold SZ_PREFIX_CTX; lia|].
  split.
  { eapply (relL_ok s [(bio, SZ_BIO)] R); [exact Hs|apply perm_skip; exact HP|exact HF|unfold zlength; cbn; lia|unfold bnonneg; apply Forall_cons; [cbn; unfold SZ_BIO; lia|apply Forall_nil]|unfold SZ_PREFIX_CTX; lia|rewrite bsum_cons, bsum_nil; cbn [snd]; unfold SZ_BIO, SZ_PREFIX_CTX; lia]. }
  split; [reflexivity|]. intros ctx Hctx.
  split; [apply lt62; lia|].
  split.
  { eapply (relL_ok s [(ctx, SZ_PREFIX_CTX); (bio, SZ_BIO)] R); [exact Hs|apply perm_skip; apply perm_skip; exact HP|exact HF|unfold zlength; cbn; lia| |lia|rewrite !bsum_cons, bsum_nil; cbn [snd]; unfold SZ_BIO, SZ_PREFIX_CTX; lia].
    unfold bnonneg. apply Forall_cons; [cbn; unfold SZ_PREFIX_CTX; lia|]. apply Forall_cons; [cbn; unfold SZ_BIO; lia|apply Forall_nil]. }
  split; [reflexivity|]. intros pre Hpre.
  eexists _, _. split; [apply Permutation_refl|].
  eexists _, _. split; [apply Permutation_refl|].
  eexists _, _. split; [apply Permutation_refl|].
  split; [|reflexivity]. split; [exact Hs|exact HP].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ok_general : forall (s : ST) L R X n, sinv s -> Permutation X (L ++ st_blocks s ++ R) -> bnonneg L -> bnonneg R -> 0 <= n ->
  zlength L + zlength R + 52 <= AP_NB -> bsum L + bsum R + n + 1712 <= AP_TOT -> okAp AP_NB AP_TOT X n.
Proof.
  intros s L R X n Hs HP HL HR Hn Hc Hb. destruct (st_blocks_bound s Hs) as (B1 & B2 & B3).
  unfold okAp. rewrite (zlen_perm _ _ HP), (bsum_perm _ _ HP), !zlen_app', !bsum_app. unfold ST_NB, ST_TOT in *.
  split; [lia|]. split; [lia|]. split; [|lia]. eapply bnonneg_perm; [apply Permutation_sym; exact HP|]. apply bnonneg_app; [exact HL|apply bnonneg_app; [exact B3|exact HR]].
Qed.

Lemma perm_front2 (a b : ptr * Z) l1 l2 : Permutation (a :: b :: l1 ++ l2) (l1 ++ a :: b :: l2).
Proof. transitivity (a :: l1 ++ b :: l2); [apply perm_skip; apply Permutation_middle|apply Permutation_middle]. Qed.

Definition strb (st : astr ptr) : list (ptr * Z) := (str_blk st, 24) :: optb (str_data st).
Definition objb (o : aobj ptr) : list (ptr * Z) := match o with ODyn blk data alloc _ => [(blk, 40); (data, alloc)] | _ => [] end.

Lemma asn1_string_free_spec : forall st s R X, rel s (strb st ++ R) X ->
  awp (asn1_string_free (Some st) s) X (fun r X' => rel (snd r) R X' /\ snd r = s).
Proof.
  intros [blk [[dp n]|]] s R X [Hs HP]; unfold asn1_string_free, strb in *; cbn -[st_blocks] in *.
  - exists n, ((blk, 24) :: st_blocks s ++ R). split.
    { transitivity (st_blocks s ++ (blk, 24) :: (dp, n) :: R); [exact HP|]. transitivity ((blk,24) :: st_blocks s ++ (dp, n) :: R); [apply Permutation_sym; apply Permutation_middle|].
      transitivity ((blk, 24) :: (dp, n) :: st_blocks s ++ R); [apply perm_skip; apply Permutation_sym; apply Permutation_middle|apply perm_swap]. }
    exists 24, (st_blocks s ++ R). split; [apply Permutation_refl|]. split; [|reflexivity]. split; [exact Hs|apply Permutation_refl].
  - exists 24, (st_blocks s ++ R). split; [transitivity (st_blocks s ++ (blk, 24) :: R); [exact HP|apply Permutation_sym; apply Permutation_middle]|]. split; [|reflexivity]. split; [exact Hs|apply Permutation_refl].
Qed.

Lemma asn1_object_free_spec : forall o s R X, rel s (objb o ++ R) X ->
  awp (asn1_object_free o s) X (fun r X' => rel (snd r) R X' /\ snd r = s).
Proof.
  intros [| nid lnlen | blk data alloc content] s R X [Hs HP]; unfold asn1_object_free, objb in *; cbn -[st_blocks].
  - split; [split; [exact Hs|exact HP]|reflexivity].
  - split; [split; [exact Hs|exact HP]|reflexivity].
  - exists alloc, ((blk, 40) :: st_blocks s ++ R). split.
    { transitivity (st_blocks s ++ (blk, 40) :: (data, alloc) :: R); [exact HP|]. transitivity ((blk,40) :: st_blocks s ++ (data, alloc) :: R); [apply Permutation_sym; apply Permutation_middle|].
      transitivity ((blk, 40) :: (data, alloc) :: st_blocks s ++ R); [apply perm_skip; apply Permutation_sym; apply Permutation_middle|apply perm_swap]. }
    exists 40, (st_blocks s ++ R). split; [apply Permutation_refl|]. split; [|reflexivity]. split; [exact Hs|apply Permutation_refl].
Qed.

Lemma d2i_prim_spec : forall dd op totlen utype s R X, rel s R X ->
  go_err (get_object dd op totlen) = None -> 0 <= go_len (get_object dd op totlen) ->
  frameRk 2 (24 + go_len (get_object dd op totlen)) R ->
  awp (d2i_prim (ptr:=ptr) dd op totlen utype s) X (fun r X' =>
     match fst r with
     | None => rel (snd r) R X'
     | Some st => rel (snd r) (strb st ++ R) X' /\ bsum (strb st) <= 24 + go_len (get_object dd op totlen) /\ bnonneg (strb st) /\ snd r = s
     end /\ as_cnf (snd r) = as_cnf s).
Proof.
  intros dd op totlen utype s R X HR Hg Hlen HFk. pose proof HR as [Hs HP]. unfold d2i_prim, SZ_ASN1_STRING. rewrite Hg.
  set (g := get_object dd op totlen) in *.
  assert (HF : frameR R) by (eapply frameRk_frameR; [exact HFk|lia|lia]).
  destruct HFk as (Hc & Hb & HRn). unfold R_NB, R_TOT, AP_NB, AP_TOT, AP_MAX_INPUT in Hc, Hb. pose proof (bnonneg_sum R HRn) as HR0.
  destruct (utype =? V_ASN1_OCTET_STRING).
  - cbn -[st_blocks go_len go_p Z.eqb g].
    split; [apply lt62; nlia|]. split; [eapply (ok_general s [] R); [exact Hs|exact HP|apply Forall_nil|exact HRn|nlia|nlia|rewrite bsum_nil; nlia]|].
    split; [reflexivity|]. intros blk Hblk.
    destruct (go_len g =? 0) eqn:E0; cbn -[st_blocks go_len g].
    + split; [|reflexivity]. unfold strb; cbn -[st_blocks go_len g]. split; [split; [exact Hs|transitivity ((blk, 24) :: st_blocks s ++ R); [apply perm_skip; exact HP|apply Permutation_middle]]|].
      split; [lia|]. split; [|reflexivity]. apply Forall_cons; [cbn; nlia|apply Forall_nil].
    + split. { assert (E62 : 2^62 = 4611686018427387904) by reflexivity. rewrite E62. apply Z.eqb_neq in E0. lia. }
      split; [eapply (ok_general s [(blk, 24)] R); [exact Hs|apply perm_skip; exact HP|apply Forall_cons; [cbn; nlia|apply Forall_nil]|exact HRn|nlia|nlia|rewrite bsum_cons, bsum_nil; cbn [snd]; nlia]|].
      split; [reflexivity|]. intros dp Hdp. cbn -[st_blocks go_len g]. split; [|reflexivity]. unfold strb; cbn -[st_blocks go_len g]. split.
      { split; [exact Hs|]. transitivity ((dp, go_len g) :: (blk, 24) :: st_blocks s ++ R); [apply perm_skip; apply perm_skip; exact HP|].
        transitivity ((blk, 24) :: (dp, go_len g) :: st_blocks s ++ R); [apply perm_swap|]. apply perm_front2. }
      split; [lia|]. split; [|reflexivity]. apply Forall_cons; [cbn; lia|]. apply Forall_cons; [cbn; lia|apply Forall_nil].
  - destruct (c2i_ibuf_len dd (go_p g) (go_len g)) as [| |r] eqn:Ei.
    + apply awp_abind. eapply awp_mono; [apply err_raise_spec; [exact HR|exact HF|cbn; lia|cbn; lia]|]. intros [u1 s1] X1 (HR1 & HC1 & _). cbn. split; [exact HR1|exact HC1].
    + apply awp_abind. eapply awp_mono; [apply err_raise_spec; [exact HR|exact HF|cbn; lia|cbn; lia]|]. intros [u1 s1] X1 (HR1 & HC1 & _). cbn. split; [exact HR1|exact HC1].
    + assert (Hr : 1 <= r <= go_len g).
      { unfold c2i_ibuf_len in Ei. destruct (go_len g =? 0) eqn:E0; [discriminate|]. destruct (go_len g =? 1) eqn:E1.
        - inversion Ei. apply Z.eqb_eq in E1. lia.
        - apply Z.eqb_neq in E0. apply Z.eqb_neq in E1.
          destruct (negb _ && _); [discriminate|]. inversion Ei. destruct (znth dd (go_p g) =? 0); [lia|]. destruct (znth dd (go_p g) =? 255); [|lia]. destruct (forallb _ _); lia. }
      cbn -[st_blocks go_len g].
      split; [apply lt62; nlia|]. split; [eapply (ok_general s [] R); [exact Hs|exact HP|apply Forall_nil|exact HRn|nlia|nlia|rewrite bsum_nil; nlia]|].
      split; [reflexivity|]. intros blk Hblk.
      split. { assert (E62 : 2^62 = 4611686018427387904) by reflexivity. rewrite E62. lia. }
      split; [eapply (ok_general s [(blk, 24)] R); [exact Hs|apply perm_skip; exact HP|apply Forall_cons; [cbn; nlia|apply Forall_nil]|exact HRn|nlia|nlia|rewrite bsum_cons, bsum_nil; cbn [snd]; nlia]|].
      split; [reflexivity|]. intros dp Hdp. cbn -[st_blocks go_len g]. split; [|reflexivity]. unfold strb; cbn -[st_blocks go_len g]. split.
      { split; [exact Hs|]. transitivity ((dp, r) :: (blk, 24) :: st_blocks s ++ R); [apply perm_skip; apply perm_skip; exact HP|].
        transitivity ((blk, 24) :: (dp, r) :: st_blocks s ++ R); [apply perm_swap|]. apply perm_front2. }
      split; [lia|]. split; [|reflexivity]. apply Forall_cons; [cbn; lia|]. apply Forall_cons; [cbn; lia|apply Forall_nil].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition owf (o : aobj ptr) : Prop :=
  match o with
  | ODyn _ _ alloc content => 1 <= zlength content <= alloc
  | OStatic _ lnlen => 0 <= lnlen <= 55
  | ONone => True
  end.

Lemma tab_lnlen_ok : forallb (fun e : Z * list Z * Z => (0 <=? snd e) && (snd e <=? 55)) ap_obj_table = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ossl_obj_obj2nid_spec : forall key (s : ST) R X, rel s R X -> frameRk 2 75 R ->
  awp (ossl_obj_obj2nid key s) X (fun r X' => rel (snd r) R X' /\ fst r = obj_lookup key).
Proof.
  intros key s R X HR HF. unfold ossl_obj_obj2nid. destruct (obj_lookup key) as [e|].
  - cbn. split; [exact HR|reflexivity].
  - apply awp_abind. eapply awp_mono; [apply (ossl_init_added_api_spec rcrit rcritS rcritI spre Hrc_grow Hrc_shrink Hspre); [exact HR|exact HF]|].
    intros [u1 s1] X1 [HR1 _]. cbn. split; [exact HR1|reflexivity].
Qed.

Lemma tab_entry_lnlen i : 0 <= snd (tab_entry i) <= 55.
Proof.
  unfold tab_entry. pose proof tab_lnlen_ok as H. rewrite forallb_forall in H.
  destruct (nth_in_or_default (Z.to_nat i) ap_obj_table (0, [], 0)) as [Hin|E].
  - specialize (H _ Hin). apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
  - rewrite E. cbn. lia.
Qed.

Lemma obj_bsearch_lnlen f key : forall l h nid lnlen, obj_bsearch_loop f key l h = Some (nid, lnlen) -> 0 <= lnlen <= 55.
Proof.
  induction f as [|f IH]; intros l h nid lnlen E; cbn -[tab_entry obj_cmp Z.ltb Z.div Z.add Z.sub] in E; [discriminate|].
  destruct (l <? h); [|discriminate].
  destruct (tab_entry (l + (h - l) / 2)) as [[nid' content] ln'] eqn:Et.
  destruct (obj_cmp key content <? 0); [eapply IH; exact E|]. destruct (0 <? obj_cmp key content); [eapply IH; exact E|].
  inversion E; subst. pose proof (tab_entry_lnlen (l + (h - l) / 2)) as B. rewrite Et in B. cbn in B. exact B.
Qed.
Lemma obj_lookup_lnlen key nid lnlen : obj_lookup key = Some (nid, lnlen) -> 0 <= lnlen <= 55.
Proof. unfold obj_lookup. apply obj_bsearch_lnlen. Qed.

Definition osum (o : aobj ptr) : Z := bsum (objb o).

Lemma objb_facts o : owf o -> bnonneg (objb o) /\ zlength (objb o) <= 2 /\ 0 <= osum o.
Proof.
  destruct o as [|nid lnlen|blk data alloc content]; unfold owf, objb, osum, bnonneg, zlength; cbn; intros H.
  - split; [constructor|]. unfold bsum; cbn. lia.
  - split; [constructor|]. unfold bsum; cbn. lia.
  - split; [apply Forall_cons; [cbn; lia|apply Forall_cons; [cbn; lia|apply Forall_nil]]|]. unfold bsum; cbn. lia.
Qed.

Lemma c2i_asn1_object_spec : forall o content (s : ST) R X, rel s (objb o ++ R) X -> owf o ->
  zlength R + 6 <= R_NB -> bsum R + osum o + 40 + zlength content + 100 <= R_TOT -> bnonneg R ->
  awp (c2i_asn1_object o content s) X (fun r X' =>
    let o' := fst (fst r) in rel (snd r) (objb o' ++ R) X' /\ owf o' /\ osum o' <= Z.max (osum o) (40 + zlength content)).
Proof.
  intros o content s R X HR Ho Hc Hb HRn. destruct (objb_facts o Ho) as (Hon & Hoz & Ho0). pose proof (bnonneg_sum R HRn) as HR0.
  assert (HF : frameRk 2 75 (objb o ++ R)).
  { unfold frameRk. rewrite zlen_app', bsum_app. unfold osum in *. split; [nlia|]. split; [nlia|]. apply bnonneg_app; assumption. }
  unfold c2i_asn1_object.
  destruct ((zlength content <=? 0) || (2147483647 <? zlength content) || negb (Z.land (znth content (zlength content - 1)) 128 =? 0)) eqn:Echk.
  - (* [comment removed for export] *) apply awp_abind. eapply awp_mono; [apply err_raise_spec; [exact HR|eapply frameRk_frameR; [exact HF|lia|lia]|cbn; lia|cbn; lia]|].
    intros [u1 s1] X1 (HR1 & _). cbn. split; [exact HR1|]. split; [exact Ho|lia].
  - apply awp_abind. eapply awp_mono; [apply ossl_obj_obj2nid_spec; [exact HR|exact HF]|]. intros [r1 s1] X1 [HR1 E1]. cbn [fst snd] in *. subst r1.
    destruct (obj_lookup content) as [[nid lnlen]|] eqn:El.
    + (* [comment removed for export] *)
      apply awp_abind. eapply awp_mono; [apply asn1_object_free_spec; exact HR1|]. intros [u2 s2] X2 [HR2 E2]. cbn.
      split; [exact HR2|]. split; [apply (obj_lookup_lnlen content nid lnlen El)|]. unfold osum at 1. cbn [objb]. unfold bsum at 1; cbn. lia.
    + destruct ((fix bad (prev_cont : bool) (bs : list Z) {struct bs} : bool := match bs with [] => false | c :: bs' => (c =? 128) && negb prev_cont || bad (negb (Z.land c 128 =? 0)) bs' end) false content) eqn:Ebad.
      * (* [comment removed for export] *) apply awp_abind. eapply awp_mono; [apply err_raise_spec; [exact HR1|eapply frameRk_frameR; [exact HF|lia|lia]|cbn; lia|cbn; lia]|].
        intros [u2 s2] X2 (HR2 & _). cbn. split; [exact HR2|]. split; [exact Ho|lia].
      * assert (Hne : 1 <= zlength content).
        { apply Bool.orb_false_iff in Echk as [Echk _]. apply Bool.orb_false_iff in Echk as [Echk _]. apply Z.leb_gt in Echk. lia. }
        clear Echk Ebad El. destruct HR1 as [Hs1 HP1].
        destruct o as [|onid olnlen|oblk odata oalloc oprev]; cbn -[st_blocks SZ_ASN1_OBJECT zlength Z.ltb] in HP1 |- *.
        -- (* [comment removed for export] *)
           split; [apply lt62; nlia|]. split; [apply (ok_general s1 [] R X1 SZ_ASN1_OBJECT); [exact Hs1|exact HP1|apply Forall_nil|exact HRn|nlia|nlia|rewrite bsum_nil; nlia]|].
           split; [reflexivity|]. intros b Hb0. cbn -[st_blocks SZ_ASN1_OBJECT zlength].
           split. { assert (E62 : 2^62 = 4611686018427387904) by reflexivity. rewrite E62. nlia. }
           split; [eapply (ok_general s1 [(b, SZ_ASN1_OBJECT)] R); [exact Hs1|apply perm_skip; exact HP1|apply Forall_cons; [cbn; nlia|apply Forall_nil]|exact HRn|nlia|nlia|rewrite bsum_cons, bsum_nil; cbn [snd]; nlia]|].
           split; [reflexivity|]. intros d' Hd'. cbn -[st_blocks zlength]. unfold osum, objb, owf; cbn -[st_blocks zlength].
           split; [split; [exact Hs1|]|].
           { transitivity ((d', zlength content) :: (b, 40) :: st_blocks s1 ++ R); [apply perm_skip; apply perm_skip; exact HP1|].
             transitivity ((b, 40) :: (d', zlength content) :: st_blocks s1 ++ R); [apply perm_swap|apply perm_front2]. }
           unfold bsum; cbn -[zlength]. split; lia.
        -- (* [comment removed for export] *)
           split; [apply lt62; nlia|]. split; [eapply (ok_general s1 [] R); [exact Hs1|exact HP1|apply Forall_nil|exact HRn|nlia|nlia|rewrite bsum_nil; nlia]|].
           split; [reflexivity|]. intros b Hb0. cbn -[st_blocks SZ_ASN1_OBJECT zlength].
           split. { assert (E62 : 2^62 = 4611686018427387904) by reflexivity. rewrite E62. nlia. }
           split; [eapply (ok_general s1 [(b, SZ_ASN1_OBJECT)] R); [exact Hs1|apply perm_skip; exact HP1|apply Forall_cons; [cbn; nlia|apply Forall_nil]|exact HRn|nlia|nlia|rewrite bsum_cons, bsum_nil; cbn [snd]; nlia]|].
           split; [reflexivity|]. intros d' Hd'. cbn -[st_blocks zlength]. unfold osum, objb, owf; cbn -[st_blocks zlength].
           split; [split; [exact Hs1|]|].
           { transitivity ((d', zlength content) :: (b, 40) :: st_blocks s1 ++ R); [apply perm_skip; apply perm_skip; exact HP1|].
             transitivity ((b, 40) :: (d', zlength content) :: st_blocks s1 ++ R); [apply perm_swap|apply perm_front2]. }
           unfold bsum; cbn -[zlength]. split; lia.
        -- (* [comment removed for export] *)
           unfold owf in Ho. unfold osum in Hb. cbn [objb] in Hb. rewrite !bsum_cons, bsum_nil in Hb. cbn [snd] in Hb.
           destruct (Z.ltb_spec (zlength oprev) (zlength content)) as [Hlt|Hge]; cbn -[st_blocks zlength].
           ++ exists oalloc, ((oblk, 40) :: st_blocks s1 ++ R). split.
              { transitivity (st_blocks s1 ++ (oblk, 40) :: (odata, oalloc) :: R); [exact HP1|]. apply Permutation_sym.
                transitivity ((oblk, 40) :: (odata, oalloc) :: st_blocks s1 ++ R); [apply perm_swap|apply perm_front2]. }
              split. { assert (E62 : 2^62 = 4611686018427387904) by reflexivity. rewrite E62. nlia. }
              split; [eapply (ok_general s1 [(oblk, 40)] R); [exact Hs1|apply Permutation_refl|apply Forall_cons; [cbn; lia|apply Forall_nil]|exact HRn|nlia|nlia|rewrite bsum_cons, bsum_nil; cbn [snd]; nlia]|].
              split; [reflexivity|]. intros d' Hd'. cbn -[st_blocks zlength]. unfold osum, objb, owf; cbn -[st_blocks zlength].
              split; [split; [exact Hs1|]|].
              { transitivity ((oblk, 40) :: (d', zlength content) :: st_blocks s1 ++ R); [apply perm_swap|apply perm_front2]. }
              unfold bsum; cbn -[zlength]. split; lia.
           ++ unfold osum, objb, owf; cbn -[st_blocks zlength]. split; [split; [exact Hs1|exact HP1]|]. unfold bsum; cbn -[zlength]. split; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition OBJ_TXT_MAX : Z := 4096.

(* [comment removed for export] *)
Definition roomy (X : list (ptr * Z)) : Prop :=
  forall L n, zlength L <= 8 -> bnonneg L -> 0 <= n -> bsum L + n <= 16000 -> okAp AP_NB AP_TOT (L ++ X) n.

Hypothesis obj2txt_num_bwp : forall content X,
  roomy X -> 1 <= zlength content <= 586 ->
  bwp (okAp AP_NB AP_TOT) (tbind (obj2txt_num (tree_ops ptr) content abs0) (fun p => TRet (fst p))) X
      (fun n X' => Permutation X' X /\ -1 <= n <= OBJ_TXT_MAX).

Lemma rel_perm (s : ST) (R X X' : list (ptr * Z)) : rel s R X -> Permutation X' X -> rel s R X'.
Proof. intros [Hs HP] HPX. split; [exact Hs|]. transitivity X; [exact HPX|exact HP]. Qed.

Lemma rel_roomy s R X : rel s R X -> frameR R -> roomy X.
Proof.
  intros [Hs HP] (F1 & F2 & F3) L n HL HLn Hn Hb. apply (ok_general s L R (L ++ X) n); [exact Hs| |exact HLn|exact F3|exact Hn|nlia|pose proof (bnonneg_sum R F3); nlia].
  apply Permutation_app_head. exact HP.
Qed.

Lemma obj_obj2txt_spec : forall o (s : ST) R X, rel s (objb o ++ R) X -> owf o -> frameRk 2 75 (objb o ++ R) ->
  awp (obj_obj2txt o s) X (fun r X' => rel (snd r) (objb o ++ R) X' /\ -1 <= fst r <= OBJ_TXT_MAX).
Proof.
  intros o s R X HR Ho HF. unfold obj_obj2txt. destruct o as [|nid lnlen|blk data alloc content].
  - cbn. split; [exact HR|unfold OBJ_TXT_MAX; lia].
  - cbn. split; [exact HR|unfold owf in Ho; unfold OBJ_TXT_MAX; lia].
  - apply awp_abind. eapply awp_mono; [apply ossl_obj_obj2nid_spec; [exact HR|exact HF]|]. intros [r1 s1] X1 [HR1 E1]. cbn [fst snd] in *. subst r1.
    destruct (obj_lookup content) as [[nid lnlen]|] eqn:El.
    + cbn. split; [exact HR1|]. pose proof (obj_lookup_lnlen _ _ _ El). unfold OBJ_TXT_MAX; lia.
    + destruct (Z.ltb_spec 586 (zlength content)) as [Hgt|Hle]; [cbn; split; [exact HR1|unfold OBJ_TXT_MAX; lia]|].
      unfold obj2txt_bn. apply awp_abt. eapply bwp_mono; [apply obj2txt_num_bwp|].
      * eapply rel_roomy; [exact HR1|eapply frameRk_frameR; [exact HF|lia|lia]].
      * unfold owf in Ho. lia.
      * intros n X' [HPX Hn]. cbn. split; [eapply rel_perm; [exact HR1|exact HPX]|lia].
Qed.

Lemma i2a_asn1_object_spec : forall o (s : ST) R X, rel s (objb o ++ R) X -> owf o -> frameRk 3 (75 + OBJ_TXT_MAX + 1) (objb o ++ R) ->
  awp (i2a_asn1_object o s) X (fun r X' => rel (snd r) (objb o ++ R) X').
Proof.
  intros o s R X HR Ho HF.
  assert (HF2 : frameRk 2 75 (objb o ++ R)) by (destruct HF as (A & B & C); unfold frameRk; unfold OBJ_TXT_MAX in *; repeat split; try assumption; lia).
  assert (MAIN : awp ((i <- obj_obj2txt o ;; if 79 <? i then (p <- amalloc (i + 1) ;; obj_obj2txt o ;;; afree p) else aret tt) s) X
                     (fun r X' => rel (snd r) (objb o ++ R) X')).
  2:{ unfold i2a_asn1_object. destruct o; [cbn; exact HR|exact MAIN|exact MAIN]. }
  apply awp_abind. eapply awp_mono; [apply obj_obj2txt_spec; [exact HR|exact Ho|exact HF2]|]. intros [i s1] X1 [HR1 Hi]; cbn [fst snd] in *.
  destruct (Z.ltb_spec 79 i) as [Hgt|Hle]; cbn -[obj_obj2txt Z.add amalloc afree Z.ltb].
  2:{ destruct (79 <? i) eqn:E; [apply Z.ltb_lt in E; lia|]. cbn. exact HR1. }
  replace (79 <? i) with true by (symmetry; apply Z.ltb_lt; exact Hgt).
  destruct HR1 as [Hs1 HP1]. pose proof HF as (A & B & C). pose proof (bnonneg_sum _ C) as C0.
  apply awp_abind. apply awp_amalloc; [apply lt62b; unfold OBJ_TXT_MAX in *; lia| |].
  { apply (ok_general s1 [] (objb o ++ R) X1 (i + 1)); [exact Hs1|exact HP1|apply Forall_nil|exact C|lia|nlia|rewrite bsum_nil; unfold OBJ_TXT_MAX in *; nlia]. }
  intros p Hp; cbn [fst snd].
  apply awp_abind. eapply awp_mono; [apply (obj_obj2txt_spec o s1 ((p, i + 1) :: R))|].
  - split; [exact Hs1|]. transitivity ((p, i + 1) :: st_blocks s1 ++ objb o ++ R); [apply perm_skip; exact HP1|]. rewrite !app_assoc. apply Permutation_middle.
  - exact Ho.
  - unfold frameRk. rewrite zlen_app', bsum_app in *. change ((p, i + 1) :: R) with ([(p, i + 1)] ++ R). rewrite zlen_app', bsum_app.
    unfold zlength in *. cbn [length]. rewrite bsum_cons, bsum_nil. cbn [snd]. unfold OBJ_TXT_MAX in *. split; [lia|]. split; [lia|].
    apply Forall_app in C as [C1 C2]. apply bnonneg_app; [exact C1|]. apply Forall_cons; [cbn; lia|exact C2].
  - intros [i2 s2] X2 [HR2 _]; cbn. destruct HR2 as [Hs2 HP2].
    exists (i + 1), (st_blocks s2 ++ objb o ++ R). split; [|split; [exact Hs2|apply Permutation_refl]].
    transitivity (st_blocks s2 ++ objb o ++ (p, i + 1) :: R); [exact HP2|]. rewrite !app_assoc. apply Permutation_sym. apply Permutation_middle.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma prim_content_spec : forall dd o op omax (s : ST) F X,
  let g := get_object dd op omax in
  Forall (fun b => 0 <= b) dd ->
  go_err g = None -> 0 <= go_len g -> go_cls g = 0 ->
  rel s (objb o ++ F) X -> owf o -> bnonneg F ->
  zlength F + 10 <= R_NB -> bsum (objb o ++ F) + 40 + go_len g + 4300 <= R_TOT ->
  awp (prim_content dd o (go_tag g) op (go_p g - op) (go_len g) s) X (fun r X' =>
    rel (snd r) (objb (fst r) ++ F) X' /\ owf (fst r) /\ osum (fst r) <= Z.max (osum o) (40 + go_len g)).
Proof.
  intros dd o op omax s F X g Hdd Hg Hlen Hcls HR Ho HFn HcF HbF. subst g. set (g := get_object dd op omax) in *.
  destruct (objb_facts o Ho) as (Hon & Hoz & Ho0). pose proof (bnonneg_sum F HFn) as HF0.
  assert (Eomax : go_len g + (go_p g - op) = go_p g - op + go_len g) by lia.
  pose proof (get_object_inner dd op omax Hdd Hg) as GI. fold g in GI.
  unfold prim_content. rewrite Eomax. rewrite !GI. rewrite Hg.
  destruct (is_string_tag (go_tag g)); [cbn; split; [exact HR|split; [exact Ho|lia]]|].
  destruct (go_tag g =? 6) eqn:Et6.
  - cbn -[c2i_asn1_object i2a_asn1_object slice go_p go_len g].
    apply awp_bind. eapply awp_mono; [apply (c2i_asn1_object_spec o (slice dd (go_p g) (go_len g)) s F X); [exact HR|exact Ho|lia| |exact HFn]|].
    { unfold osum. assert (zlength (slice dd (go_p g) (go_len g)) <= go_len g); [|rewrite bsum_app in HbF; lia].
      unfold slice, zlength. rewrite length_firstn. lia. }
    intros [[o' ok] s1] X1 (HR1 & Ho1 & Hsz1). cbn [fst snd] in *.
    assert (Hsl : zlength (slice dd (go_p g) (go_len g)) <= go_len g) by (unfold slice, zlength; rewrite length_firstn; lia).
    destruct ok.
    + apply awp_bind. eapply awp_mono; [apply i2a_asn1_object_spec; [exact HR1|exact Ho1|]|].
      { destruct (objb_facts o' Ho1) as (Hon1 & Hoz1 & _). unfold frameRk. rewrite zlen_app', bsum_app. unfold osum in *. rewrite bsum_app in HbF. unfold OBJ_TXT_MAX.
        split; [lia|]. split; [lia|]. apply bnonneg_app; assumption. }
      intros [u2 s2] X2 HR2. cbn. split; [exact HR2|]. split; [exact Ho1|lia].
    + cbn. split; [exact HR1|]. split; [exact Ho1|lia].
  - destruct (go_tag g =? 4) eqn:Et4; [|destruct (go_tag g =? 2) eqn:Et2; [|destruct (go_tag g =? 10) eqn:Et10; [|cbn; split; [exact HR|split; [exact Ho|lia]]]]].
    all: cbn -[d2i_prim asn1_string_free go_p go_len g V_ASN1_OCTET_STRING V_ASN1_INTEGER V_ASN1_ENUMERATED].
    all: apply awp_bind; (eapply awp_mono; [apply (d2i_prim_spec dd op (go_p g - op + go_len g) _ s (objb o ++ F) X); [exact HR| | | ]|]);
      [rewrite GI; exact Hg
      |rewrite GI; lia
      |rewrite GI; unfold frameRk; rewrite zlen_app'; split; [lia|]; split; [lia|]; apply bnonneg_app; assumption
      |].
    all: intros [r1 s1] X1 [HR1 HC1]; cbn [fst snd] in *; destruct r1 as [st|];
      [destruct HR1 as (HR1 & _ & _ & ->); apply awp_bind; (eapply awp_mono; [apply asn1_string_free_spec; exact HR1|]); intros [u2 s2] X2 [HR2 E2]; cbn [fst snd] in HR2, E2; subst s2; cbn; split; [exact HR2|split; [exact Ho|lia]]
      |cbn; split; [exact HR1|split; [exact Ho|lia]]].
Qed.
End Inv.
