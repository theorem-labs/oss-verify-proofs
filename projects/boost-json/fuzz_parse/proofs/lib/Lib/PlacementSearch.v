(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4list04Npos35stdpp9bitvectorbdefinitionsk12bvhc4prod46Stdlib6ZArith6BinInt1Zma3addk1bbv_unsignedhc4conshc3fsthc3snd37Corelib5Lists7ListDefq93map3h5LinuxProcessSemanticsfLinuxProcessSem5States6fpage_round_up_Zhc4boolhc4andbma3lebk17Z_to_bvs69page_sizes6bregion_free79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3LibfPlacementSearch~~~~~~hjeefit_candidates36Stdlib5Lists4Listhp67existsbma3eqbma6modulo37Corelib4Init5Logichs32eqma2lehp69fold_leftma3maxhp62Inhs32orhc4truema2lts6atwo_pow_64hjechigher_fit_bhc6optionhjeaplace_fitshjeh1search_candidateshp64findhs33andhc4Somehje5placema3subhs32exs66VmMapshc3apps69alloc_tops67vm_mapss6bvm_reservedhjeeplace_in_model" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fit_candidates : ltac2:(zQ "50!h9!j4!jb!le!m3>4maps@1$1@2$4@1$3@1$2#k0@1$3@1$2#k0>2aZ$0>2nZ$0@1$1$0") := ltac2:(zQ "c1!jb!le!h9!m3!o2!o8!p6!pd!j4!q3!s0!v4&@2$3@1$1@1$0#k0@1$1@1$0#k0\4maps@1$8~0\2aZ$2\2nZ$2@3$6$2@2$4^2^1@4$a~0$2\1p~0@1$b@2$4@2$5@1$0#k0@3$7@1$1@1$0#k0@1$1@1$0#k0^1@2$5@1$0#k0@3$9@1$1@1$0#k0@1$1@1$0#k0^1^3").

Definition higher_fit_b : ltac2:(zQ "60!h9!jb!le!hg6!j4!m3>4maps@1$4@2$5@1$2@1$1#k0@1$2@1$1#k0>2aZ$0>2nZ$0>5baseZ$0$3") := ltac2:(zQ "f0!h9!jb!hgd!o2!hh4!hha!le!j4!m3!hi4!hj0!ho4!hq9!hr4!hra\4maps@1$7@2$8@1$6@1$1#k0@1$6@1$1#k0\2aZ$0\2nZ$0\5baseZ$0@3$c$0\1g$0@2$2@2$2@2$2@2$d@2$e^1$9Z@2$4@2$3^4^3^1@2$4@2$3^1^3^2@3$a^5@2$5@1$1#k0^1@2$5@1$1#k0^3@3$b^4^3^2").

Lemma page_round_up_Z_aligned : ltac2:(zQ "50!h9!ht7!v4!hi4!hra>1z$0@3$1$0@2$4@1$2^1$3Z").
Proof. intro z. unfold page_round_up_Z. apply Z_mod_mult. Qed.

Lemma page_round_up_Z_ge : ltac2:(zQ "30!h9!v4!htd>1z$0@2$2^1@1$1^1").
Proof.
  intro z. unfold page_round_up_Z, page_size.
  pose proof (Z.div_mod (z + 4096 - 1) 4096 ltac:(lia)) as H.
  pose proof (Z.mod_pos_bound (z + 4096 - 1) 4096 ltac:(lia)).
  lia.
Qed.

(* [comment removed for export] *)
Lemma page_round_up_Z_le : ltac2:(zQ "60!h9!htd!ht7!v4!hi4!hra>1z$0>1b$0>0@2$1^2^1>0@3$2$0@2$5^2$4Z@2$1@1$3^4^3").
Proof.
  intros z b Hzb Hb. unfold page_round_up_Z, page_size in *.
  pose proof (Z.div_mod b 4096 ltac:(lia)) as Hbm.
  assert (Hq : ((z + 4096 - 1) / 4096 < b / 4096 + 1)%Z)
    by (apply Z.div_lt_upper_bound; lia).
  apply Z.le_trans with (m := (b / 4096 * 4096)%Z); [|lia].
  apply Z.mul_le_mono_nonneg_r; lia.
Qed.

Lemma fold_max_ge_seed : ltac2:(zQ "50!h9!j4!hu2!htd!huf>1l@1$1$0>1s$0@2$3^1@5$2$0$0$4^2^1").
Proof.
  induction l as [|x l IH]; intro s; cbn; [lia|].
  pose proof (IH (Z.max s x)). lia.
Qed.

Lemma fold_max_ge_in : ltac2:(zQ "60!h9!j4!hv5!hu2!htd!huf>1l@1$1$0>1s$0>1x$0>0@3$2$0^1^3@2$4^2@5$3$0$0$5^4^3").
Proof.
  induction l as [|y l IH]; intros s x Hin; [contradiction|].
  destruct Hin as [->|Hin]; cbn.
  - pose proof (fold_max_ge_seed l (Z.max s x)). lia.
  - apply IH; assumption.
Qed.

Lemma fold_max_le : ltac2:(zQ "60!h9!htd!j4!hv5!hu2!huf>1l@1$2$0>1s$0>1b$0>0@2$1^2^1>0>1x$0>0@3$3$0^1^5@2$1^2^4@2$1@5$4$0$0$5^5^4^3").
Proof.
  induction l as [|y l IH]; intros s b Hs Hl; cbn; [exact Hs|].
  apply IH.
  - pose proof (Hl y ltac:(now left)). lia.
  - intros x Hx. apply Hl. now right.
Qed.

Lemma fold_max_in_or_seed : ltac2:(zQ "70!h9!hu2!huf!j4!ht7!hvb!hv5>1l@1$3$0>1s$0@2$5@3$4$0@5$1$0$0$2^2^1^1@3$6$0@5$1$0$0$2^2^1^2").
Proof.
  induction l as [|y l IH]; intro s; cbn; [now left|].
  destruct (IH (Z.max s y)) as [Heq|Hin].
  - rewrite Heq. destruct (Z.max_spec s y) as [[_ ->]|[_ ->]];
      [right; now left | now left].
  - right. now right.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma higher_fit_b_complete : ltac2:(zQ "h10!h9!ht7!jb!hi4!o2!htd!hra!hg6!ig1!ig8!hha!le!j4!m3!hj0!igd!iha>4maps@1$c@2$d@1$b@1$2#k0@1$b@1$2#k0>2aZ$0>2nZ$0>5baseZ$0>1g$0>0@2$5Z@2$4^4^3>0@2$9Z^4>0@3$1$0@2$6^6$3Z>0@3$1$0@2$6^6$3Z>0@2$9^6$f>0@3$1$0@2$6^6$3Z>0@2$5@2$4^a^9^7>0@2$5@2$4^8^a^9>0@3$1$7@3$e^d@2$a@1$2#k0^9@2$a@1$2#k0^b$8@3$1$7@4$h0^e^d^c^b$8").
Proof.
  (* [comment removed for export] *)
  intros maps aZ nZ baseZ g HaPos HnPos HaAl HnAl Hbase HgAl Hglo Hghi
    Hgfree.
  assert (Hmod : two_pow_64 = bv_modulus 64) by reflexivity.
  (* [comment removed for export] *)
  assert (HgW : bv_unsigned (Z_to_bv 64 g) = g)
    by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; clear HaAl HnAl HgAl; lia).
  assert (HnW : bv_unsigned (Z_to_bv 64 nZ) = nZ)
    by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; clear HaAl HnAl HgAl; lia).
  set (cs := List.filter (fun c => (c <=? g)%Z) (fit_candidates maps aZ nZ)).
  set (g' := fold_left Z.max cs (aZ + nZ)%Z).
  assert (Hcs : forall x, In x cs <->
            In x (fit_candidates maps aZ nZ) /\ (x <=? g)%Z = true)
    by (intro x0; unfold cs; exact (filter_In _ x0 _)).
  assert (Hlo : (aZ + nZ <= g')%Z) by (unfold g'; apply fold_max_ge_seed).
  assert (Hhi : (g' <= g)%Z).
  { unfold g'. apply fold_max_le; [lia|]. intros x Hx.
    apply Hcs in Hx. destruct Hx as [_ Hx]. now apply Z.leb_le. }
  assert (Hcand : In g' (fit_candidates maps aZ nZ)).
  { destruct (fold_max_in_or_seed cs (aZ + nZ)%Z) as [Heq|Hin].
    - assert (Heq' : g' = (aZ + nZ)%Z) by exact Heq.
      rewrite Heq'. now left.
    - apply Hcs in Hin. exact (proj1 Hin). }
  assert (Hg'W : bv_unsigned (Z_to_bv 64 g') = g')
    by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; clear HaAl HnAl HgAl; lia).
  assert (Hg'Al : (g' mod page_size = 0)%Z).
  { destruct Hcand as [Heq|Hin].
    - rewrite <- Heq.
      rewrite Z.add_mod, HaAl, HnAl by (unfold page_size; lia).
      reflexivity.
    - apply in_map_iff in Hin. destruct Hin as (p & Heq & _).
      rewrite <- Heq. apply page_round_up_Z_aligned. }
  assert (Hg'free : region_free maps (Z_to_bv 64 g') (Z_to_bv 64 nZ)
                    = true).
  { apply region_free_intro. intros b s Hin.
    pose proof (region_free_In _ _ _ _ _ Hgfree Hin) as Hno.
    unfold iv_overlap in *. rewrite HgW, HnW in Hno.
    rewrite Hg'W, HnW.
    apply andb_false_iff in Hno.
    set (B := bv_unsigned b) in *. set (S := bv_unsigned s) in *.
    destruct (Z.le_gt_cases (B + S) g) as [Hend|Hend].
    - (* [comment removed for export] *)
      assert (Hc : In (page_round_up_Z (B + S)) (fit_candidates maps aZ nZ)).
      { right. apply in_map_iff. exists (b, s).
        split; [reflexivity|assumption]. }
      assert (Hcle : (page_round_up_Z (B + S) <= g)%Z)
        by (apply page_round_up_Z_le; assumption).
      assert (Hcg' : (page_round_up_Z (B + S) <= g')%Z).
      { unfold g'. apply fold_max_ge_in. apply Hcs. split; [assumption|].
        now apply Z.leb_le. }
      pose proof (page_round_up_Z_ge (B + S)) as Hround.
      apply andb_false_iff. left. apply Z.ltb_ge.
      exact (Z.le_trans _ _ _ Hround Hcg').
    - (* [comment removed for export] *)
      destruct Hno as [Hno|Hno].
      + apply Z.ltb_ge in Hno. lia.
      + apply Z.ltb_ge in Hno.
        apply andb_false_iff. right. apply Z.ltb_ge.
        exact (Z.le_trans _ _ _
                 (Z.add_le_mono _ _ _ _ Hhi (Z.le_refl nZ)) Hno). }
  unfold higher_fit_b. apply existsb_exists. exists g'.
  split; [exact Hcand|].
  assert (Hg'base : (g' + nZ <= baseZ)%Z)
    by exact (Z.le_trans _ _ _
                (Z.add_le_mono _ _ _ _ Hhi (Z.le_refl nZ)) Hghi).
  rewrite Hg'free.
  rewrite (proj2 (Z.eqb_eq _ _) Hg'Al).
  rewrite (proj2 (Z.leb_le _ _) Hlo).
  rewrite (proj2 (Z.leb_le _ _) Hg'base).
  reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition search_candidates : ltac2:(zQ "50!j4!jb!h9!le!m3>4maps@1$0@2$4@1$3@1$1#k0@1$3@1$1#k0>3loZ$2@1$0$2") := ltac2:(zQ "c1!jb!le!m3!h9!o8!p6!pd!j4!q3!s0!v4!o2&@2$2@1$1@1$0#k0@1$1@1$0#k0\4maps@1$7~0\3loZ$3@3$5$3^1@4$9~0$3\1p~0@1$a@2$b@2$4@1$0#k0@3$6@1$1@1$0#k0@1$1@1$0#k0^1@2$4@1$0#k0@3$8@1$1@1$0#k0@1$1@1$0#k0^1^2").

(* [comment removed for export] *)
Definition place_fits : ltac2:(zQ "60!h9!jb!le!hg6!j4!m3>4maps@1$4@2$5@1$2@1$1#k0@1$2@1$1#k0>3loZ$0>3hiZ$0>2nZ$0>1g$0$3") := ltac2:(zQ "d0!jb!h9!hgd!hh4!hha!le!j4!m3!hi4!hj0!o2!hr4!hra\4maps@1$6@2$7@1$5@1$0#k0@1$5@1$0#k0\3loZ$1\3hiZ$1\2nZ$1\1g$1@2$2@2$2@2$2@2$b@2$c^1$8Z@2$3^4^1@2$3@2$a^1^2^3@3$9^5@2$4@1$0#k0^1@2$4@1$0#k0^2").

Definition place : ltac2:(zQ "60!h9!jb!le!j4!iia!m3>4maps@1$3@2$5@1$2@1$1#k0@1$2@1$1#k0>3loZ$0>3hiZ$0>2nZ$0@1$4$0") := ltac2:(zQ "80!h9!jb!le!j4!m3!ij3!ik1!il7\4maps@1$3@2$4@1$2@1$1#k0@1$2@1$1#k0\3loZ$0\3hiZ$0\2nZ$0@3$7$0@4$5^4^3^2^1@2$6^4^3").

(* [comment removed for export] *)

Lemma place_sound : ltac2:(zQ "h20!h9!jb!ilf!ht7!htd!hha!le!im6!hg6!j4!iia!m3!ig1!hi4!hj0!imd!o2!hra>4maps@1$9@2$b@1$6@1$1#k0@1$6@1$1#k0>3loZ$0>3hiZ$0>2nZ$0>1a$0>0@3$3@1$a$0@4$f^5^4^3^2@2$7$0^1@2$2@3$3$0@2$h1^2$dZ@2$2@2$4^5^2@2$2@2$4@2$h0^2^3^4@3$3$8@3$e^6@2$5@1$1#k0^2@2$5@1$1#k0^3$c").
Proof.
  intros maps loZ hiZ nZ a H.
  unfold place in H. apply find_some in H as [_ Hf].
  unfold place_fits in Hf.
  apply andb_true_iff in Hf as [Hf Hfree].
  apply andb_true_iff in Hf as [Hf Hhi].
  apply andb_true_iff in Hf as [Hal Hlo].
  repeat split.
  - now apply Z.eqb_eq.
  - now apply Z.leb_le.
  - now apply Z.leb_le.
  - exact Hfree.
Qed.

(* [comment removed for export] *)

Lemma existsb_find : forall {A} (f : A -> bool) l,
  existsb f l = true -> exists x, find f l = Some x.
Proof.
  intros A f l. induction l as [|y l IH]; cbn; [discriminate|].
  destruct (f y) eqn:Hy; [intros _; now exists y|].
  cbn. exact IH.
Qed.

(* [comment removed for export] *)
Lemma higher_fit_b_as_place : ltac2:(zQ "c0!h9!jb!le!hg6!j4!m3!ht7!iha!ij3!ik1!hq9!in6>4maps@1$4@2$5@1$2@1$1#k0@1$2@1$1#k0>3loZ$0>3hiZ$0>2nZ$0@3$6$3@4$7^4@2$b^3^1^1^2@3$a$0@4$8^4^3^2^1@2$9^4^3").
Proof.
  intros maps loZ hiZ nZ.
  unfold higher_fit_b, place_fits, search_candidates, fit_candidates.
  replace (loZ - nZ + nZ)%Z with loZ by lia.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma place_complete : ltac2:(zQ "h40!h9!ht7!jb!hi4!htd!hra!ig8!hha!le!im6!hg6!j4!iia!m3!ig1!inc!hj0!igd!imd!o2>4maps@1$b@2$d@1$8@1$2#k0@1$8@1$2#k0>3loZ$0>3hiZ$0>2nZ$0>1g$0>0@2$4Z^4>0@2$6Z^3>0@3$1$0@2$5^6$3Z>0@3$1$0@2$5^5$3Z>0@2$6^7$h1>0@3$1$0@2$5^6$3Z>0@2$4^a^7>0@2$4@2$h3^8^9^a>0@3$1$a@3$h0^d@2$7@1$2#k0^9@2$7@1$2#k0^a$e@2$f$0\1a$0@3$1@1$c$0@4$h2^f^e^d^c@2$9$0^1").
Proof.
  intros maps loZ hiZ nZ g Hlo0 Hn Hloal Hnal Hhi HgAl Hglo Hghi Hfree.
  apply existsb_find. rewrite <- higher_fit_b_as_place.
  apply (higher_fit_b_complete maps (loZ - nZ) nZ hiZ g).
  - lia.
  - exact Hn.
  - rewrite Zminus_mod, Hloal, Hnal. reflexivity.
  - exact Hnal.
  - exact Hhi.
  - exact HgAl.
  - lia.
  - exact Hghi.
  - exact Hfree.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition place_in_model : ltac2:(zQ "30!h9!iia!io2>1h$2>2nZ$0@1$1$0") := ltac2:(zQ "b0!jb!le!iob!m3!h9!io2!ip1!hi4!ipd!iq7!imd\1h$5\2nZ$4@4$a@3$2@2$3@1$1@1$0#k0@1$1@1$0#k0@1$9^2@1$8^2$7@1$6^2^1").

(* [comment removed for export] *)
Lemma place_in_model_admissible : ltac2:(zQ "h81!jb!h9!hha!ilf!ht7!o8!htd!le!im6!iob!hg6!iia!m3!ig1!io2!ip1!hi4!hj0!ipd!iq7!ir5!o2!ig8!hra&@2$5@1$0#k0@2$2@1$0#k0^3>1h$e>2nZ$1>1a$1>0@2$6Z^2>0@3$4@1$b$1@2$h4^4^3@2$8$1^2@2$3@3$4$1~0^3@2$3@3$4$1@2$h7~0$h0Z@2$3@2$h6Z~0@2$3@2$6@2$h5~0^4@1$f^5@3$4$a@3$h1@3$9@2$c@1$7@1$0#k0@1$7@1$0#k0@1$h3^5@1$h2^5@2$2@1$0#k0^3@2$2@1$0#k0^4$d").
Proof.
  intros h nZ a Hn H. unfold place_in_model in H.
  destruct (place_sound _ _ _ _ _ H) as (Hal & Hlo & Hhi & Hfree).
  pose proof (alloc_top_lt h) as Htop. unfold two_pow_64 in Htop.
  assert (Hrt : bv_unsigned (Z_to_bv 64 a) = a).
  { rewrite Z_to_bv_unsigned. apply bv_wrap_small.
    unfold bv_modulus. unfold page_size in Hlo. cbn. lia. }
  rewrite Hrt. repeat split; try assumption.
  unfold page_size in Hlo. lia.
Qed.

(* [comment removed for export] *)

Lemma place_in_model_complete : ltac2:(zQ "h70!h9!ht7!jb!hi4!htd!hra!hha!le!im6!iob!hg6!iia!m3!ig1!inc!io2!ip1!hj0!ipd!iq7!ir5!o2!ig8>1h$f>2nZ$0>1g$0>0@2$h6Z^2>0@3$1$0@2$5^3$3Z>0@3$1$0@2$5^3$3Z>0@2$4$3^4>0@2$4@2$h5^5^6@1$h0^7>0@3$1$a@3$h1@3$9@2$c@1$7@1$2#k0@1$7@1$2#k0@1$h3^8@1$h2^8@2$6@1$2#k0^6@2$6@1$2#k0^7$d@2$e$0\1a$0@3$1@1$b$0@2$h4^a^9@2$8$0^1").
Proof.
  intros h nZ g Hn Hnal HgAl Hglo Hghi Hfree.
  unfold place_in_model.
  apply (place_complete _ _ _ _ g); try assumption.
  - unfold page_size. lia.
  - unfold page_size. reflexivity.
  - exact (alloc_top_lt h).
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
