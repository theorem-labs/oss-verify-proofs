(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "or"; "@Corelib.Init.Datatypes"; "list"; "app"; "prod"; "nat"; "pair"; "cons"; "bool"; "length"; "nil"; "option"; "Some"; "fst"; "negb"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_live"; "list_upd"; "aa_Kf"; "aa_Km"; "aa_V"; "large_live"; "small_live"; "frames_of"; "sec_room"; "budget_ok_alloc"; "class_fresh"; "prim_room"; "aa_cls"; "aa_cache_inited"; "aa_depot"; "aa_fs_busy"; "aa_fs_hint"; "aa_geom"; "aa_internal_inited"; "aa_ptr_committed"; "aa_q_global"; "aa_q_thread"; "aa_sec"; "class_state"; "cs_empty"; "is_large"; "mkAA"; "remove_pos"; "SEC_SLACK"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "of_nat"; "leb"; "to_nat"; "mul"; "sub"; "pow"; "@Corelib.Lists.ListDef"; "nth"; "map"; "@Stdlib.Lists.List"; "nth_error"; "In"; "filter"; "fold_right"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "limit_ok_alloc"; "BETA_F"; "BETA_M"; "QMAX"; "U0"; "acost"; "limit_ok_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "fs_frame_size"; "ClassID"; "needed"; "@Corelib.Init.Peano"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget.
Import ListNotations.
Local Open Scope Z_scope.

Record ageom := mkAG {
  ag_spacebeg : Z;
  ag_thread : Z;
  ag_ctx : Z;
  ag_fsb : Z;
  ag_pab : Z;
  ag_stack_top : Z;
  ag_stack_bottom : Z;
  ag_sp0 : Z;
  ag_tp : Z;
  ag_dtls : Z;
  ag_nodes0 : Z;
  ag_ss0 : Z;
  ag_top : Z
}.

Definition topG (G : ageom) : Z := top_clamp (ag_top G).
Lemma topG_range : forall G, 140735332483072 <= topG G <= 140737479966720.
Proof. intros G. apply top_clamp_range. Qed.

Record class_state := mkCS {
  cs_mapped_user : Z;
  cs_allocated_user : Z;
  cs_free_array : list Z;
  cs_mapped_free_array : Z;
  cs_cache : list Z;
  cs_n_allocated : Z;
  cs_n_freed : Z
}.
Definition cs_empty : class_state := mkCS 0 0 [] 0 [] 0 0.

Record sec_chunk := mkSC {
  sc_map_beg : Z; sc_map_size : Z; sc_size : Z
}.

Record qbatch := mkQB {
  qb_addr : Z;
  qb_items : list (Z * Z);
  qb_size : Z
}.

Record DG := mkDG {
  dN  : Z;
  dF  : Z;
  dNB : list Z;
  dFB : list Z;
  dFP : list Z
}.
Definition depot_state := DG.

Record AA := mkAA {
  aa_geom : ageom;

  aa_cls : list class_state;
  aa_cache_inited : bool;

  aa_sec : list sec_chunk;
  aa_ptr_committed : Z;

  aa_live : list (Z * Z);

  aa_q_thread : list qbatch;
  aa_q_global : list qbatch;

  aa_depot : depot_state;

  aa_fs_hint : list Z;
  aa_fs_busy : list (list (Z * Z));

  aa_internal_inited : bool;

  aa_V : Z;
  aa_Km : Z;
  aa_Kf : Z
}.

Fixpoint frames_of (c : Z) (B : list (list (Z * Z))) : list (Z * Z) :=
  match B with
  | [] => []
  | b :: B' => map (fun pf => (snd pf, fs_frame_size c)) b ++ frames_of (c + 1) B'
  end.
Definition aa_frames (A : AA) : list (Z * Z) := frames_of 0 (aa_fs_busy A).

Fixpoint list_upd {T} (l : list T) (i : nat) (x : T) : list T :=
  match l, i with
  | [], _ => []
  | _ :: t, O => x :: t
  | h :: t, S i' => h :: list_upd t i' x
  end.
Fixpoint remove_pos (pos : Z) (l : list (Z * Z)) : list (Z * Z) :=
  match l with
  | [] => []
  | pf :: t => if fst pf =? pos then t else pf :: remove_pos pos t
  end.
Definition fs_release (A : AA) (c pos : Z) : AA := ltac2:(tb__ "0|4|
S2fS26VA;A1S21VA;A1S22VA;A1S2bVA;A1S28VA;A1S15VA;A1S2aVA;A1S29VA;A1S23VA;A1S25VA;A1S16S6S8S0S0A2M0A1M1S24VA;A1M2S36Vc;A1M3S30Vpos;S3aG1G3G2SeG0A1A4A2A4S27VA;A1S19VA;A1S18VA;A1S17VA;A1Af").

Definition fs_alloc (A : AA) (c pos f h : Z) : AA := ltac2:(tb__ "0|4|
S2fS26VA;A1S21VA;A1S22VA;A1S2bVA;A1S28VA;A1S15VA;A1S2aVA;A1S29VA;A1S23VA;A1S16S0S25VA;A1S36Vc;A1M0Vh;A4S16S6S8S0S0A2M1A1M2S24VA;A1M3G0SbG1SaS0S0Vpos;Vf;A4S3aG2G0G3SeG1A1A4A3A4S27VA;A1S19VA;A1S18VA;A1S17VA;A1Af").

Lemma frames_of_insert : ltac2:(tb__ "0|2|
S6S6S8S0S0A2M0A1M1A1S0S9G1S0S0S1SfG1A1S3cG1R6R4A3S10G1R3A2A3S3G1G1S3G1G1S2S1G1S1cR8R9A2S7G0R2R1A3A3S1G1S1cR8S16G1R9R7SbG0SaS0S0R5R4A4R6A3A4A2S7G0R2SbG0SaS0S0R4S47S32R8S34R7A1A2A1A4R1A3A3A3A2Ll2;A2Ll1;A2F_;Ff;Fpos;Fb;Fi;Fc0;FB;").
Proof.
  induction B as [|b0 B IH]; intros c0 [|i] b pos f Hn; cbn in Hn; try discriminate.
  - injection Hn as ->. cbn. rewrite Z.add_0_r. exists [], (map (fun pf : Z * Z => (snd pf, fs_frame_size c0)) b ++ frames_of (c0 + 1) B). split; reflexivity.
  - destruct (IH (c0 + 1) i b pos f Hn) as (l1 & l2 & E1 & E2). cbn.
    exists (map (fun pf : Z * Z => (snd pf, fs_frame_size c0)) b0 ++ l1), l2.
    rewrite E1, E2. replace (c0 + 1 + Z.of_nat i) with (c0 + Z.of_nat (S i)) by lia.
    split; rewrite <- app_assoc; reflexivity.
Qed.

Lemma length_list_upd {T} : ltac2:(tb__ "0|0|
S6VT;A1S9VT;S1S9SdVT;S16VT;R3R2R1A4A2SdVT;R3A2A3Fx;Fi;Fl;").
Proof. induction l; intros [|i] x; cbn; auto. Qed.
Lemma nth_list_upd_same {T} : ltac2:(tb__ "0|0|
S6VT;A1S9VT;VT;S4aR3SdVT;R4A2A2S1VT;S3aVT;R4S16VT;R5R4R3A4R2A4R3A3F_;Fd;Fx;Fi;Fl;").
Proof. induction l; intros [|i] x d H; cbn in *; try lia; auto. apply IHl. lia. Qed.
Lemma nth_list_upd_other {T} : ltac2:(tb__ "0|0|
S6VT;A1S9S9VT;VT;S4S1S9R4R3A3A1S1VT;S3aVT;R4S16VT;R6R5R3A4R2A4S3aVT;R4R6R2A4A3F_;Fd;Fx;Fj;Fi;Fl;").
Proof. induction l; intros [|i] [|j] x d H; cbn in *; auto; try congruence. Qed.
Lemma nth_error_list_upd_other {T} : ltac2:(tb__ "0|0|
S6VT;A1S9S9VT;S4S1S9R3R2A3A1S1SfVT;A1S3cVT;S16VT;R5R4R2A4R3A3S3cVT;R5R3A3A3F_;Fx;Fj;Fi;Fl;").
Proof. induction l; intros [|i] [|j] x H; cbn in *; auto; try congruence. Qed.

Lemma remove_pos_split : ltac2:(tb__ "0|2|
S6S8S0S0A2M0A1M1S0S0G1S4S3dS0R3S3bG0S0S11S0S0A2R4A4A3A1S1G1S30R4S7G0R5SbG0SaS0S0R4R3A4R2A3A3A2S7G0R5R2A3A3F_;Fv;Ff;Fpos;Fu;").
Proof.
  induction u as [|[p g] u IH]; intros pos f v Hn; cbn.
  - rewrite Z.eqb_refl. reflexivity.
  - destruct (Z.eqb_spec p pos) as [E|NE]; [exfalso; apply Hn; left; exact E|].
    cbn. f_equal. apply IH. intros Hin. apply Hn. right. exact Hin.
Qed.

Lemma frames_of_in : ltac2:(tb__ "0|2|
S6S6S8S0S0A2M0A1M1A1S0S0S0S3dG0SaS0S0R2R1A4S1cR3R4A2A3S3S9S9S3S0S0S2S4aR2SdG1R7A2A2S2S3dG0SaS0S0R1R5A4S3aG1R2R7SeG0A1A4A3S1S0R4S47S32R6S34R2A1A2A1A3A2A2Lpos;A2Li;A2F_;Fs;Ff;Fc0;FB;").
Proof.
  induction B as [|b B IH]; intros c0 f s Hin; [destruct Hin|].
  cbn in Hin. apply in_app_or in Hin as [Hin|Hin].
  - apply in_map_iff in Hin as ([pos f'] & E & Hin). cbn in E. injection E as <- <-.
    exists 0%nat, pos. cbn. rewrite Z.add_0_r. repeat split; auto; lia.
  - destruct (IH _ _ _ Hin) as (i & pos & Hi & Hb & Hs). exists (S i), pos. cbn. repeat split; auto; try lia.
    rewrite Hs. f_equal. lia.
Qed.

Lemma frames_of_release : ltac2:(tb__ "0|2|
S6S6S8S0S0A2M0A1M1A1S0S9G1S0S0G1S1SfG1A1S3cG1R7R5A3S10G1S7G0R4SbG0SaS0S0R3R2A4R1A3A3A2A3S3G1G1S3G1G1S2S1G1S1cR9RaA2S7G0R2SbG0SaS0S0R5S47S32R9S34R8A1A2A1A4R1A3A3A3S1G1S1cR9S16G1RaR8S7G0R7R4A3A4A2S7G0R2R1A3A3A2Ll2;A2Ll1;A2F_;Fv;Ff;Fpos;Fu;Fi;Fc0;FB;").
Proof.
  induction B as [|b B IH]; intros c0 [|i] u pos f v Hn; cbn in Hn; try discriminate.
  - injection Hn as ->. cbn. rewrite !map_app. cbn. rewrite Z.add_0_r.
    exists (map (fun pf : Z * Z => (snd pf, fs_frame_size c0)) u),
           (map (fun pf : Z * Z => (snd pf, fs_frame_size c0)) v ++ frames_of (c0 + 1) B).
    split; [rewrite <- app_assoc; reflexivity | rewrite <- app_assoc; reflexivity].
  - destruct (IH (c0 + 1) i u pos f v Hn) as (l1 & l2 & E1 & E2). cbn.
    exists (map (fun pf : Z * Z => (snd pf, fs_frame_size c0)) b ++ l1), l2.
    rewrite E1, E2. replace (c0 + 1 + Z.of_nat i) with (c0 + Z.of_nat (S i)) by lia.
    split; rewrite <- app_assoc; reflexivity.
Qed.

Definition aa_L (A : AA) : Z := ltac2:(tb__ "0|1|
S3fS0S8S0S0A2M0G0S0S32S13S0S0R2A3R1A2Lacc;Lpn;Z0S15VA;A1A5").

Definition budget_bound (A : AA) : Z := ltac2:(tb__ "0|0|
S32S32S32S32S44S45S19VA;A1A1A2S37S42S18VA;A1A2A2S37S41S17VA;A1A2A2S43A2").

Definition is_large (bn : Z * Z) : bool := 64513 <=? snd bn.
Definition large_live (A : AA) : Z := ltac2:(tb__ "0|1|
S34SdS8S0S0A2M0S3eG0S2eS15VA;A1A3A2A1").
Definition SEC_SLACK : Z := 4180.
Definition sec_room (A : AA) : Prop := ltac2:(tb__ "0|0|
S33S32S1aVA;A1S31A2S39Z2Z14A2A2").

Definition small_live (A : AA) : Z := ltac2:(tb__ "0|1|
S34SdS8S0S0A2M0S3eG0G0S12S2eR1A1A1Lbn;S15VA;A1A3A2A1").
Definition PRIM_LIVE_MAX : Z := 8192.
Definition prim_room (A : AA) : Prop := small_live A <= PRIM_LIVE_MAX.
Definition budget_ok_alloc (A : AA) (n : Z) : Prop := ltac2:(tb__ "0|0|
S2S40S19VA;A1S18VA;A1S17VA;A1Vn;A4S2S1dVA;A1S20VA;A1A2A2").
Lemma budget_ok_alloc_intro : ltac2:(tb__ "0|0|
S14S0S40S19R2A1S18R2A1S17R2A1R1A4S1dR3A1S20R4A1S1eR5R4A2F_;F_;F_;Fn;FA;").
Proof. intros A n H1 H2 H3. exact (conj H1 (conj H2 H3)). Qed.
Lemma budget_ok_alloc_limit : ltac2:(tb__ "0|0|
S14S0S1eR2R1A2S40S19R3A1S18R3A1S17R3A1R2A4F_;Fn;FA;").
Proof. intros A n [H _]. exact H. Qed.
Lemma budget_ok_alloc_room : ltac2:(tb__ "0|0|
S14S0S1eR2R1A2S1dR3A1F_;Fn;FA;").
Proof. intros A n (_ & H & _). exact H. Qed.
Lemma budget_ok_alloc_prim : ltac2:(tb__ "0|0|
S14S0S1eR2R1A2S20R3A1F_;Fn;FA;").
Proof. intros A n (_ & _ & H). exact H. Qed.
Lemma small_live_nonneg : forall A, 0 <= small_live A.
Proof. intros A. unfold small_live. lia. Qed.
Lemma small_live_same : ltac2:(tb__ "0|0|
S14S14S1S6S8S0S0A2A1S15R1A1S15R2A1A3S1S0S1bR2A1S1bR3A1A3F_;FA';FA;").
Proof. intros A A' E. unfold small_live. rewrite E. reflexivity. Qed.
Lemma prim_room_same : ltac2:(tb__ "0|1|
S14S14S1S6S8S0S0A2A1S15R1A1S15R2A1A3S20R3A1M0G0F_;F_;FA';FA;").
Proof. intros A A' E H. unfold prim_room in *. rewrite (small_live_same A A' E). exact H. Qed.
Lemma large_live_nonneg : forall A, 0 <= large_live A.
Proof. intros A. unfold large_live. lia. Qed.
Lemma large_live_same : ltac2:(tb__ "0|0|
S14S14S1S6S8S0S0A2A1S15R1A1S15R2A1A3S1S0S1aR2A1S1aR3A1A3F_;FA';FA;").
Proof. intros A A' E. unfold large_live. rewrite E. reflexivity. Qed.
Lemma sec_room_same : ltac2:(tb__ "0|1|
S14S14S1S6S8S0S0A2A1S15R1A1S15R2A1A3S1dR3A1M0G0F_;F_;FA';FA;").
Proof. intros A A' E H. unfold sec_room in *. rewrite (large_live_same A A' E). exact H. Qed.

Lemma large_live_insert : ltac2:(tb__ "0|3|
S14S14S6S8S0S0A2M0A1M1G1S0S0S1G1S15R6A1M2S7G0R4R3A3A3S1G1G2S7G0R5SbG0SaS0S0R3R2A4R4A3A3A3S1S0S1aR7A1S32S1aR8A1ScS0L_;S35Zfc01R3A2Z1Z0Xcx2A2A3F_;F_;Fn;Fb;Fl2;Fl1;FA';FA;").
Proof.
  intros A A' l1 l2 b n E E'. unfold large_live. rewrite E, E', !filter_app. cbn [filter]. unfold is_large at 2. cbn [snd].
  destruct (64513 <=? n); rewrite !length_app; cbn [length]; lia.
Qed.
Lemma small_live_insert : ltac2:(tb__ "0|3|
S14S14S6S8S0S0A2M0A1M1G1S0S0S1G1S15R6A1M2S7G0R4R3A3A3S1G1G2S7G0R5SbG0SaS0S0R3R2A4R4A3A3A3S1S0S1bR7A1S32S1bR8A1ScS0L_;S35Zfc01R3A2Z0Z1Xcx2A2A3F_;F_;Fn;Fb;Fl2;Fl1;FA';FA;").
Proof.
  intros A A' l1 l2 b n E E'. unfold small_live. rewrite E, E', !filter_app. cbn [filter]. unfold is_large at 2. cbn [snd].
  destruct (64513 <=? n); cbn [negb]; rewrite !length_app; cbn [length]; lia.
Qed.
Definition budget_ok_free (A : AA) : Prop := ltac2:(tb__ "0|0|
S46S19VA;A1S18VA;A1S17VA;A1A3").

Lemma large_live_remove : ltac2:(tb__ "0|3|
S14S14S6S8S0S0A2M0A1M1G1S0S0S1G1S15R6A1M2S7G0R4SbG0SaS0S0R2R1A4R3A3A3A3S1G1G2S7G0R5R4A3A3S1S0S1aR7A1S38S1aR8A1ScS0L_;S35Zfc01R3A2Z1Z0Xcx2A2A3F_;F_;Fn;Fb;Fl2;Fl1;FA';FA;").
Proof. intros A A' l1 l2 b n E E'. pose proof (large_live_insert A' A l1 l2 b n E' E). lia. Qed.
Lemma small_live_remove : ltac2:(tb__ "0|3|
S14S14S6S8S0S0A2M0A1M1G1S0S0S1G1S15R6A1M2S7G0R4SbG0SaS0S0R2R1A4R3A3A3A3S1G1G2S7G0R5R4A3A3S1S0S1bR7A1S38S1bR8A1ScS0L_;S35Zfc01R3A2Z0Z1Xcx2A2A3F_;F_;Fn;Fb;Fl2;Fl1;FA';FA;").
Proof. intros A A' l1 l2 b n E E'. pose proof (small_live_insert A' A l1 l2 b n E' E). lia. Qed.
Lemma sec_room_remove : ltac2:(tb__ "0|4|
S14S14S6S8S0S0A2M0A1M1G1S0S0S1G1S15R6A1M2S7G0R4SbG0SaS0S0R2R1A4R3A3A3A3S1G1G2S7G0R5R4A3A3S1dR8A1M3G3F_;F_;F_;Fn;Fb;Fl2;Fl1;FA';FA;").
Proof. intros A A' l1 l2 b n E E' H. unfold sec_room in *. rewrite (large_live_remove A A' l1 l2 b n E E'). destruct (64513 <=? n); lia. Qed.

Definition class_fresh (A : AA) (c : Z) : Prop := ltac2:(tb__ "0|0|
S1S2cS3aS2cS36Vc;A1S21VA;A1S2dA4S2dA3").

Definition cls_keptA (A A' : AA) (n : Z) : Prop := ltac2:(tb__ "0|0|
S0S2S33Z1R1A2S33R1Z1eA2A2S5S33Zfc01Vn;A2S4S1S0R2S48S49Vn;A1A1A3A1A2S1fVA;R3A2S1fVA';R4A2F_;F_;F_;Fc;").
Definition cls_kept_freeA (A A' : AA) : Prop := ltac2:(tb__ "0|0|
S0S2S33Z1R1A2S33R1Z1eA2A2S4S1S0R2Z18A3A1S1fVA;R3A2S1fVA';R4A2F_;F_;F_;Fc;").
