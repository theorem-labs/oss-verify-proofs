(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0t YG08.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0l YG0m.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AF0m AF0x AFeq AFeu AFex AFez AFf3.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YFfn.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Open Scope Z_scope.
Local Open Scope am_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma nth_error_removelast_lt : forall {A} (l : list A) j, (S j < length l)%nat -> nth_error (removelast l) j = nth_error l j.
Proof.
intros A l. induction l as [|x t IH]; intros j Hj; [cbn in Hj; lia|].
destruct t as [|y t']; [cbn in Hj; lia|]. cbn [removelast]. destruct j as [|j]; [reflexivity|]. cbn [nth_error]. apply IH. cbn [length] in Hj |- *. lia.
Qed.
Lemma last_nth_error : forall {A} (l : list A) (d : A), l <> [] -> nth_error l (length l - 1) = Some (last l d).
Proof.
intros A l d Hl. induction l as [|x t IH]; [congruence|]. destruct t as [|y t']; [reflexivity|].
specialize (IH ltac:(discriminate)). replace (length (x :: y :: t') - 1)%nat with (S (length (y :: t') - 1))%nat by (cbn [length]; lia).
cbn [nth_error]. rewrite IH. reflexivity.
Qed.
Lemma in_combine_seq_iff : forall {A} (l : list A) s j (x : A),
In (j, x) (combine (seq s (length l)) l) <-> exists j', j = (s + j')%nat /\ nth_error l j' = Some x.
Proof.
intros A l. induction l as [|y t IH]; intros s j x.
- cbn. split; [intros [] | intros (j' & _ & H); destruct j'; discriminate H].
- cbn [length seq combine In]. rewrite IH. split.
+ intros [E | (j' & -> & H)]; [injection E as <- <-; exists 0%nat; split; [lia | reflexivity] | exists (S j'); split; [lia | exact H]].
+ intros (j' & -> & H). destruct j' as [|j']; [left; injection H as ->; f_equal; lia | right; exists j'; split; [lia | exact H]].
Qed.
Lemma in_combine_seq0 : forall {A} (l : list A) j (x : A), In (j, x) (combine (seq 0 (length l)) l) <-> nth_error l j = Some x.
Proof.
intros A l j x. rewrite in_combine_seq_iff. split; [intros (j' & -> & H); exact H | intros H; exists j; split; [lia | exact H]].
Qed.
Lemma index_ofZ_nth : forall l j x, NoDup l -> nth_error l j = Some x -> index_ofZ l x = Z.of_nat j.
Proof.
intros l j x ND H. unfold index_ofZ. destruct (index_of_spec l x 0%nat (nth_error_In _ _ H)) as (j' & E & H'). rewrite Nat.add_0_l in E. rewrite E.
f_equal. apply (proj1 (NoDup_nth_error _) ND); [exact (nth_error_lt _ _ _ H') | rewrite H, H'; reflexivity].
Qed.
Section f.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (X : astate) (rd rd' : reader).
Hypothesis M : ARm B ly X rd.
Variables (k : chunk) (r : nat) (o : Z) (sm : secmap) (i : nat).
Hypothesis Hk : In k (st_chunks X).
Hypothesis Hst : ck_state k = CQuarantined.
Hypothesis Hb : ck_beg k = PSec r o.
Hypothesis Hni : ~ In (ck_beg k) (map ck_beg (q_items X)).
Hypothesis Hci : st_cache_inited X = true.
Hypothesis Hsm : nth_error (st_secs X) r = Some sm.
Hypothesis Hi : nth_error (st_sec_arr X) i = Some r.
Local Notation X1 := (AFf3.X1 X k).
Definition arr : list nat := st_sec_arr X.
Definition lastr : nat := last arr r.
Definition arr' : list nat := removelast (lupd arr i lastr).
Definition X2 : astate := set_sec_arr arr' (set_secs (lupd (st_secs X) r (mkSec (sm_len sm) (sm_size sm) false)) X1).
Local Notation T := (ly_T ly).
Definition MAP : Z := ly_sec ly r.
Definition LEN : Z := sec_map_size (ck_req k).
Definition nA : Z := Z.of_nat (length arr).
Definition idx : Z := Z.of_nat i.
Definition qi : Z := ly_Q ly + 8 * idx.
Definition lst : Z := ly_sec ly lastr.
Definition own : bool := idx =? nA - 1.
Variable sp : Z.
Hypothesis Hsp : ly_stk_lo ly + KSTACK <= sp <= ly_stk_hi ly.
Hypothesis IMG : img_cover ly.
Definition DS (a : Z) : Prop := sp - KSTACK <= a < sp.
Definition DI (a : Z) : Prop :=
(as_inst B + 680 <= a < as_inst B + 684) \/ (as_inst B + 120 <= a < as_inst B + 129) \/ (as_inst B + 144 <= a < as_inst B + 160) \/
(as_inst B + 704 <= a < as_inst B + 720).
Definition DJ (a : Z) : Prop := (T + t_stats + 40 <= a < T + t_stats + 56) \/ (T + t_stats + 88 <= a < T + t_stats + 104).
Definition DQ (a : Z) : Prop := qi <= a < qi + 8.
Definition DL (a : Z) : Prop := own = false /\ lst + 24 <= a < lst + 32.
Definition DH (a : Z) : Prop := shadow_addr MAP <= a < shadow_addr MAP + LEN / 8.
Definition DM (a : Z) : Prop := MAP <= a < MAP + LEN.
Definition D (a : Z) : Prop := DS a \/ DI a \/ DJ a \/ DQ a \/ DL a \/ DH a \/ DM a.
Hypothesis AG : forall a, 0 <= a < 2 ^ 64 -> ~ D a -> rd' a = rd a.
Hypothesis VIS : forall a, 0 <= a < 2 ^ 64 -> rd a <> None -> ~ DM a -> rd' a <> None.
Hypothesis MUT' : forall j, 0 <= j < 4 -> rd' (as_inst B + 680 + j) = Some 0.
Hypothesis NS' : forall kk, (kk < 8)%nat -> rd' (as_inst B + 120 + Z.of_nat kk) = Some (le_byte (nA - 1) 8 kk).
Hypothesis QI' : forall kk, (kk < 8)%nat -> rd' (qi + Z.of_nat kk) = Some (le_byte lst 8 kk).
Hypothesis LST' : own = false -> forall kk, (kk < 8)%nat -> rd' (lst + 24 + Z.of_nat kk) = Some (le_byte idx 8 kk).
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.
Ltac geo := clear AG VIS MUT' NS' QI' LST' HTSD.
Let WF : Wf (as_universe B) X := am_wf B ly X rd M.
Let LO : layout_ok ly := am_layout B ly X rd M.
Lemma SPLIT : exists l1 l2, st_chunks X = l1 ++ k :: l2 /\ st_chunks X1 = l1 ++ l2 /\
~ In (ck_beg k) (map ck_beg l1) /\ ~ In (ck_beg k) (map ck_beg l2).
Proof. geo.
destruct (In_split_beg _ _ Hk (wf_chunks_nodup _ _ _ _ _ WF)) as (l1 & l2 & E & N1 & N2). exists l1, l2.
split; [exact E|]. split; [|split; [exact N1 | exact N2]]. unfold AFf3.X1. cbn [st_chunks set_chunks]. rewrite E. apply del_chunk_present. exact N1.
Qed.
Lemma KF : cfacts B ly X k. Proof. geo. exact (chunk_facts B ly X rd k M Hk). Qed.
Lemma KFACTS : o = kPage /\ sm_live sm = true /\ sm_len sm = LEN /\ sm_size sm = needed_size (ck_req k) /\ 0 <= ck_req k < MALLOC_MAX /\
from_primary (ck_req k) = false /\ In (MAP, LEN) (sec_extents ly X) /\ (r < length (st_secs X))%nat.
Proof. geo.
pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ WF) k Hk) as [Hn CK]. rewrite Hb in CK. destruct CK as (P1 & P2 & sm' & Q1 & Q2 & Q3 & Q4). rewrite Hsm in Q1. injection Q1 as <-.
unfold LEN, MAP. repeat split; try assumption; try lia.
- unfold sec_extents. apply in_flat_map. exists k. split; [exact Hk|]. rewrite Hb. left. reflexivity.
- exact (nth_error_lt _ _ _ Hsm).
Qed.
Lemma ARR : In r arr /\ (i < length arr)%nat /\ NoDup arr /\ 1 <= nA <= 16384 /\ 0 <= idx < nA /\
nth_error arr (length arr - 1) = Some lastr /\ In lastr arr /\ (own = true <-> lastr = r).
Proof. geo.
pose proof (wf_secondary _ _ _ _ _ WF) as XS. destruct XS as [Snd Sac Sal Sres Sral].
assert (Hin : In r (st_sec_arr X)) by (eapply nth_error_In; exact Hi).
assert (Hlt : (i < length (st_sec_arr X))%nat) by (exact (nth_error_lt _ _ _ Hi)).
assert (NE : st_sec_arr X <> []) by (intros E; rewrite E in Hin; destruct Hin).
pose proof (last_nth_error (st_sec_arr X) r NE) as HL.
unfold kPtrArrayEntriesPerCommit in Sres. unfold own, lst, qi, idx, nA, lastr, arr.
repeat split; try assumption; try lia.
- eapply nth_error_In. exact HL.
- intros Ho. apply Z.eqb_eq in Ho. replace i with (length (st_sec_arr X) - 1)%nat in Hi by lia. rewrite HL in Hi. injection Hi as E. exact E.
- intros E. rewrite E in HL. apply Z.eqb_eq. pose proof (proj1 (NoDup_nth_error _) Snd i (length (st_sec_arr X) - 1)%nat Hlt ltac:(rewrite Hi, HL; reflexivity)). lia.
Qed.
Lemma ARR' : length arr' = (length arr - 1)%nat /\ (forall j, (j < length arr')%nat -> j <> i -> nth_error arr' j = nth_error arr j) /\
(own = false -> nth_error arr' i = Some lastr) /\ NoDup arr' /\ ~ In r arr' /\ (forall r', In r' arr' <-> In r' arr /\ r' <> r).
Proof. geo.
pose proof ARR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). unfold arr', nA, idx in *.
assert (NE : lupd arr i lastr <> []) by (intros E; apply (f_equal (@length nat)) in E; rewrite lupd_length in E; cbn in E; lia).
pose proof (swap_remove_perm arr i r Hi) as PA. fold lastr in PA. set (a' := removelast (lupd arr i lastr)) in *.
assert (NDA : NoDup a' /\ ~ In r a').
{ pose proof (NoDup_Permutation _ _ (Permutation_sym PA) A3) as X0. inversion X0; subst. auto. }
destruct NDA as [NDA NIA].
assert (L' : length a' = (length arr - 1)%nat) by (subst a'; rewrite removelast_length by exact NE; rewrite lupd_length; reflexivity).
split; [exact L'|]. split.
{ intros j Hj Hne. subst a'. rewrite nth_error_removelast_lt by (rewrite lupd_length; lia). apply nth_error_lupd_other. congruence. }
split.
{ intros Ho. unfold own in Ho. apply Z.eqb_neq in Ho. unfold nA, idx in Ho. subst a'. rewrite nth_error_removelast_lt by (rewrite lupd_length; lia). apply nth_error_lupd_same. exact A2. }
split; [exact NDA|]. split; [exact NIA|].
intros r'. split.
- intros H. split; [eapply Permutation_in; [exact PA | right; exact H] | intros ->; exact (NIA H)].
- intros [H Hne]. pose proof (Permutation_in _ (Permutation_sym PA) H) as [<-|H']; [congruence | exact H'].
Qed.
Lemma WS2 : Wf (as_universe B) X2.
Proof. geo.
destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2). pose proof KFACTS as (-> & _).
assert (EX : X1 = set_chunks (l1 ++ l2) X) by (unfold AFf3.X1; rewrite <- E1; reflexivity).
unfold X2, arr', lastr, arr. rewrite EX. exact (WfP_del_sec (as_universe B) 0 0 0 X l1 k l2 r sm i WF E Hb Hst Hni Hsm Hi).
Qed.
Lemma X2_chunks : st_chunks X2 = st_chunks X1. Proof. reflexivity. Qed.
Lemma X2_regions : st_regions X2 = st_regions X. Proof. reflexivity. Qed.
Lemma X2_cache : st_cache X2 = st_cache X. Proof. reflexivity. Qed.
Lemma X2_cinit : st_cache_inited X2 = true. Proof. exact Hci. Qed.
Lemma X2_secs : st_secs X2 = lupd (st_secs X) r (mkSec (sm_len sm) (sm_size sm) false). Proof. reflexivity. Qed.
Lemma X2_sec_arr : st_sec_arr X2 = arr'. Proof. reflexivity. Qed.
Lemma X2_sec_res : st_sec_reserved X2 = st_sec_reserved X. Proof. reflexivity. Qed.
Lemma X2_fs : st_fs X2 = st_fs X. Proof. reflexivity. Qed.
Lemma X2_qglobal : st_qglobal X2 = st_qglobal X. Proof. reflexivity. Qed.
Lemma X2_qthread : st_qthread X2 = st_qthread X. Proof. reflexivity. Qed.
Lemma X2_depot : st_depot X2 = st_depot X. Proof. reflexivity. Qed.
Lemma X2_inited : st_internal_inited X2 = st_internal_inited X. Proof. reflexivity. Qed.
Lemma X2_nev : st_nev X2 = st_nev X. Proof. reflexivity. Qed.
Lemma X2_secs_len : length (st_secs X2) = length (st_secs X). Proof. rewrite X2_secs. apply lupd_length. Qed.
Lemma reg' : forall c', reg X2 c' = reg X c'. Proof. reflexivity. Qed.
Lemma cache' : forall c', cache X2 c' = cache X c'. Proof. reflexivity. Qed.
Lemma frames' : frames X2 = frames X. Proof. reflexivity. Qed.
Lemma all_batches' : all_batches X2 = all_batches X. Proof. reflexivity. Qed.
Lemma sec_extents_split : exists E1 E2, sec_extents ly X = E1 ++ (MAP, LEN) :: E2 /\ sec_extents ly X2 = E1 ++ E2.
Proof. geo.
destruct SPLIT as (l1 & l2 & E & E1 & _). unfold sec_extents. rewrite X2_chunks, E1, E, !flat_map_app. cbn [flat_map]. rewrite Hb. cbn [app].
eexists _, _. split; reflexivity.
Qed.
Lemma sec_extents_sub : forall e, In e (sec_extents ly X2) -> In e (sec_extents ly X).
Proof. intros e He. destruct sec_extents_split as (E1 & E2 & A & A'). rewrite A' in He. rewrite A. apply in_app_iff in He as [He|He]; apply in_app_iff; [left | right; right]; exact He. Qed.
Lemma fa_poison' : exists F1 F2, fa_poison_ranges ly X = F1 ++ (MAP, LEN) :: F2 /\ fa_poison_ranges ly X2 = F1 ++ F2.
Proof. geo.
destruct SPLIT as (l1 & l2 & E & E1 & _). unfold fa_poison_ranges, reg. rewrite X2_regions, X2_chunks, E1, E, !flat_map_app. cbn [flat_map]. rewrite Hb. cbn [app].
lazymatch goal with |- exists F1 F2, ?F ++ (?A ++ ?e :: ?C) = _ /\ _ => exists (F ++ A), C end. rewrite <- app_assoc. split; reflexivity.
Qed.
Lemma aareas_split : exists A1 A2, aareas X = A1 ++ (ASec r 0, LEN) :: A2 /\ aareas X2 = A1 ++ A2.
Proof. geo.
destruct SPLIT as (l1 & l2 & E & E1 & _). unfold aareas, reg. rewrite X2_regions, X2_sec_res, X2_chunks, E1, E, !flat_map_app. cbn [flat_map]. rewrite Hb. cbn [app].
lazymatch goal with |- exists F1 F2, ?F ++ ?g :: (?A ++ ?e :: ?C) ++ ?R = _ /\ _ => exists (F ++ g :: A), (C ++ R) end.
rewrite <- !app_assoc. cbn [app]. split; reflexivity.
Qed.
Lemma sec_live' : sec_live_bytes X2 = sec_live_bytes X - LEN.
Proof. geo.
destruct SPLIT as (l1 & l2 & E & E1 & _). unfold sec_live_bytes. rewrite X2_chunks, E1, E. clear E E1.
induction l1 as [|y t IH]; cbn; [rewrite Hb; unfold LEN; lia | rewrite IH; destruct (ck_beg y); lia].
Qed.
Lemma prim_committed' : prim_committed X2 = prim_committed X. Proof. reflexivity. Qed.
Lemma abudget' : abudget X2 = abudget X - LEN. Proof. geo. unfold abudget. rewrite X2_nev, sec_live', (YG0m.sec_hulls_dead X X2 r sm Hsm X2_secs)  . lia. Qed.
Lemma zdisjoint_of_pointwise : forall a s (e : Z * Z), 0 < s -> 0 < snd e -> (forall x, a <= x < a + s -> ~ in_zr x e) -> zdisjoint (a, s) e.
Proof. clear_all. intros a s [c t] Hs Ht H. unfold zdisjoint. unfold in_zr in H. cbn [fst snd] in *.
destruct (Z_lt_le_dec (Z.max a c) (a + s)); [|lia]. destruct (Z_lt_le_dec (Z.max a c) (c + t)); [|lia].
exfalso. apply (H (Z.max a c)); lia.
Qed.
Lemma ZCH : forall ch, In ch (st_chunks X) -> zone3 (ck_base B ly ch) (ck_extent ch).
Proof. geo.
intros ch Hch. pose proof (chunk_facts B ly X rd ch M Hch) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof (req_size_bounds (ck_req ch) ltac:(clear - G7; lia)) as (_ & Q1 & _).
apply (zone3_intro ly (ck_base B ly ch) (ck_extent ch) IMG ltac:(clear - G5 G8 Q1; lia) G1).
apply zdisjoint_of_pointwise; [clear - G5 G8 Q1; lia | exact (proj1 (proj2 (lo_img _ LO))) |].
intros y Hy. exact (proj1 (chunk_apart B ly X rd ch y M Hch Hy)).
Qed.
Lemma ZSEC : forall e, In e (sec_extents ly X) -> zone3 (fst e) (snd e) /\ page_aligned (fst e) /\ fst e + snd e <= ASAN_CEIL.
Proof. geo.
intros [ex esz] He. pose proof (proj1 (Forall_forall _ _) (proj1 (am_placed _ _ _ _ M)) _ He) as (PA & IA & I3). cbn [fst snd] in PA, IA, I3 |- *.
assert (SZ : 0 <= esz).
{ pose proof He as He'. unfold sec_extents in He'. apply in_flat_map in He' as (y & Hy & Hin). pose proof (chunk_facts B ly X rd y M Hy) as (_ & _ & _ & _ & G5 & _ & G7 & G8 & GG).
destruct (ck_beg y) as [|oy|ry oy|cy py]; try solve [destruct Hin as []]. destruct Hin as [E|[]]. injection E as <- <-. destruct GG as (_ & _ & _ & CE & _).
pose proof (req_size_bounds (ck_req y) ltac:(clear - G7; lia)) as (_ & Q1 & _). clear - G5 G8 CE Q1. unfold kPage in CE. lia. }
split; [|split; [exact PA | exact I3]].
apply (zone3_intro ly ex esz IMG SZ IA).
eapply (pairwise_In zdisjoint _ _ _ (sec_extents ly X) (static_extents ly) eq_refl (proj2 (am_placed _ _ _ _ M)) He).
unfold static_extents. apply in_app_iff. right. right. left. reflexivity.
Qed.
Lemma geom : zone3 MAP LEN /\ MAP + LEN <= ASAN_CEIL /\ MAP mod 4096 = 0 /\ 8192 <= LEN < 2 ^ 29 /\ LEN mod 4096 = 0 /\
ck_base B ly k = MAP + kPage /\ ck_extent k = LEN - kPage.
Proof. geo.
pose proof KF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & CK). rewrite Hb in CK. destruct CK as (-> & FP & CB & CE & CI & PA & _).
pose proof (ZSEC _ CI) as (ZM & _ & I3). cbn [fst snd] in ZM, I3. unfold page_aligned in PA.
split; [exact ZM|]. split; [exact I3|].
unfold MAP, LEN. unfold sec_map_size in *. unfold needed_size in *. rewrite FP in *.
unfold from_primary in FP. apply Z.leb_gt in FP.
pose proof (round_up_ge (needed_primary (ck_req k) + rz_size (ck_req k)) kPage ltac:(unfold kPage; lia)) as [R1 R2].
pose proof (needed_primary_bounds (ck_req k) ltac:(lia)) as (N1 & N2 & N3). pose proof (rz_size_bounds (ck_req k)) as [RZ _].
unfold kMaxSize, kPage, MALLOC_MAX in *. repeat split; try assumption; try lia.
all: rewrite Z.add_mod, R2, Z.mod_same by lia; reflexivity.
Qed.
Lemma HIGH : kHighMemBeg <= ly_prim ly /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\ zone3 (ly_Q ly) (kPtrArrayResv) /\ ly_Q ly + kPtrArrayResv <= ASAN_CEIL /\
zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\ zone3 (ly_F ly) (kFakeStackSize) /\ ly_F ly + kFakeStackSize <= ASAN_CEIL /\
zone3 (ly_NB ly) (kNodesBlockSize) /\ ly_NB ly + kNodesBlockSize <= ASAN_CEIL /\ zone3 (ly_SB ly) (kStoreBlockSize) /\ ly_SB ly + kStoreBlockSize <= ASAN_CEIL /\
zone3 (ly_C ly) (256) /\ ly_C ly + 256 <= ASAN_CEIL /\ kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd /\
ly_prim ly <= ly_space ly /\ ly_space ly + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\ 4096 <= as_inst B /\ as_inst B + 3632 <= kLowMemEnd /\
ASAN_CEIL <= ly_stk_lo ly /\ as_inst B = TFIB_INST.
Proof. geo.
pose proof (lo_high _ LO) as IP. unfold in_high in IP. cbn [fst snd] in IP.
pose proof (lo_app _ LO) as HA. pose proof (lo_disj _ LO) as HD.
assert (Z3 : forall i0 x0 sz, nth_error (owned_extents ly) i0 = Some (x0, sz) -> 0 <= sz -> zone3 x0 sz).
{ intros i0 x0 sz He Hsz. apply (zone3_intro ly x0 sz IMG Hsz (Forall_nth_f _ _ i0 _ HA He)).
assert (L : (i0 < 8)%nat) by (destruct (Nat.lt_ge_cases i0 8) as [X0|X0]; [exact X0|]; assert (X' : nth_error (owned_extents ly) i0 = None) by (apply nth_error_None; cbn; lia); rewrite X' in He; discriminate).
exact (pairwise_ij_f _ _ i0 (8 - i0) _ _ HD ltac:(unfold static_extents; rewrite nth_error_app1 by (cbn; lia); exact He)
ltac:(unfold static_extents; rewrite nth_error_app2 by (cbn; lia); replace (i0 + Datatypes.S (8 - i0) - length (owned_extents ly))%nat with 1%nat by (cbn; lia); reflexivity)). }
pose proof (Z3 1%nat _ _ eq_refl ltac:(unfold kPtrArrayResv; lia)) as ZQ. pose proof (Z3 2%nat _ _ eq_refl ltac:(unfold kThreadObjSize; lia)) as ZT.
pose proof (Z3 3%nat _ _ eq_refl ltac:(unfold kFakeStackSize; lia)) as ZF. pose proof (Z3 4%nat _ _ eq_refl ltac:(unfold kNodesBlockSize; lia)) as ZNB.
pose proof (Z3 5%nat _ _ eq_refl ltac:(unfold kStoreBlockSize; lia)) as ZSB. pose proof (Z3 6%nat _ _ eq_refl ltac:(lia)) as ZC. clear Z3 HA HD.
pose proof (lo_top _ LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). pose proof (lo_space_in _ LO) as [S1 S2]. pose proof (lo_stk_ceil _ LO) as CE.
pose proof (aso_cells _ (am_syms B ly X rd M)) as (I1 & I2 & _).
split; [clear - IP; lia|]. split; [clear - IP; lia|]. split; [exact ZQ|]. split; [clear - ZQ; unfold zone3 in ZQ; lia|].
split; [exact ZT|]. split; [clear - ZT; unfold zone3 in ZT; lia|]. split; [exact ZF|]. split; [clear - ZF; unfold zone3 in ZF; lia|].
split; [exact ZNB|]. split; [clear - ZNB; unfold zone3 in ZNB; lia|]. split; [exact ZSB|]. split; [clear - ZSB; unfold zone3 in ZSB; lia|].
split; [exact ZC|]. split; [clear - ZC; unfold zone3 in ZC; lia|]. clear ZQ ZT ZF ZNB ZSB ZC.
repeat split; try assumption; try lia. exact (ts_inst _ TB).
Qed.
Lemma LST : exists y, In y (st_chunks X) /\ ck_beg y = PSec lastr kPage /\ In (lst, sec_map_size (ck_req y)) (sec_extents ly X) /\
zone3 lst (sec_map_size (ck_req y)) /\ lst + sec_map_size (ck_req y) <= ASAN_CEIL /\ lst mod 4096 = 0 /\ 8192 <= sec_map_size (ck_req y) /\
(own = false -> zdisjoint (lst, sec_map_size (ck_req y)) (MAP, LEN)).
Proof. geo.
pose proof ARR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). pose proof (wf_secondary _ _ _ _ _ WF) as XS. destruct XS as [Snd Sac Sal Sres Sral].
destruct (proj1 (Sac lastr) A7) as (y & Hy & Ey). exists y.
pose proof (chunk_facts B ly X rd y M Hy) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & CK). rewrite Ey in CK. destruct CK as (_ & FP & CB & CE & CI & PA & _).
pose proof (ZSEC _ CI) as (I1 & _ & I2). cbn [fst snd] in I1, I2. unfold page_aligned in PA.
assert (SZ : 8192 <= sec_map_size (ck_req y)).
{ unfold sec_map_size, needed_size. rewrite FP. unfold from_primary in FP. apply Z.leb_gt in FP.
pose proof (round_up_ge (needed_primary (ck_req y) + rz_size (ck_req y)) kPage ltac:(unfold kPage; lia)) as [R1 _].
pose proof (rz_size_bounds (ck_req y)) as [RZ _]. unfold kMaxSize, kPage in *. lia. }
unfold lst. splits; try assumption.
intros Ho. assert (Hne : ck_beg y <> ck_beg k).
{ rewrite Ey, Hb. pose proof KFACTS as (-> & _). intros E. injection E as E. apply (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ARR))))))) in E. congruence. }
unfold MAP, LEN. exact (secmaps_disjoint B ly X rd y k lastr kPage r o M Hy Hk Ey Hb Hne).
Qed.
Lemma D_cases : forall a, D a ->
(ly_stk_lo ly <= a < ly_stk_hi ly) \/ (TFIB_IMG_LO <= a < TFIB_IMG_END /\ DI a) \/ (T <= a < T + kThreadObjSize /\ DJ a) \/     (ly_Q ly <= a < ly_Q ly + kPtrArrayResv /\ DQ a) \/
(lst + 24 <= a < lst + 32 /\ own = false) \/
(kLowShadowBeg <= a < kHighMemBeg /\ DH a) \/ (MAP <= a < MAP + LEN /\ DM a).
Proof. geo.
intros a Ha. pose proof HIGH as HI. pose proof geom as GE. pose proof ARR as (A1 & A2 & A3 & A4 & A5 & _).
destruct Ha as [Y|[Y|[Y|[Y|[Y|[Y|Y]]]]]].
- left. unfold DS, KSTACK in *. lia.
- right; left. split; [|exact Y]. unfold DI in Y. rewrite (ts_inst _ TB) in Y. clear - Y. unfold TFIB_INST, TFIB_IMG_LO, TFIB_IMG_END in *. lia.
- do 2 right; left. split; [|exact Y]. unfold DJ, t_stats, kThreadObjSize in *. lia.
- do 3 right; left. split; [|exact Y]. unfold DQ, qi, kPtrArrayResv in *. lia.
- do 4 right; left. destruct Y as [Ho Y]. split; [lia | exact Ho].
- do 5 right; left. split; [|exact Y]. unfold DH in Y. destruct GE as (M1 & M2 & M3 & M4 & _). clear - Y M1 M2 M3 M4. ceil; unfold zone3, shadow_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
split.
+ pose proof (Z.div_pos MAP 8 ltac:(lia) ltac:(lia)). lia.
+ assert (Y' : (MAP + LEN) / 8 <= 140737479966720 / 8) by (apply Z.div_le_mono; lia).
assert (E8 : LEN / 8 + MAP / 8 = (MAP + LEN) / 8).
{ apply Z.mod_divide in M3 as [q Hq]; [|lia]. rewrite Hq. replace (q * 4096) with ((q * 512) * 8) by lia. rewrite Z_div_mult by lia.
replace (q * 512 * 8 + LEN) with (LEN + (q * 512) * 8) by lia. rewrite Z_div_plus by lia. lia. }
change (140737479966720 / 8) with 17592184995840 in Y'. lia.
- do 6 right. split; [exact Y | exact Y].
Qed.
Ltac zget HI x sz Z := assert (Z : zone3cases x sz) by (clear - HI; unfold zone3 in HI; tauto); unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg in Z.
Definition ok (a : Z) : Prop := 0 <= a < 2 ^ 64 /\ ~ D a.
Definition okr (lo len : Z) : Prop := forall a, lo <= a < lo + len -> ok a.
Lemma AGok : forall a, ok a -> rd' a = rd a. Proof. intros a [H1 H2]. apply AG; assumption. Qed.
Ltac hnum := ceil; unfold in_app, zone3, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighShadowEnd, kHighMemEnd, kBatchBytes, kThreadObjSize, kPage, kSpaceSize, kPrimResvSize, kPtrArrayResv, kFakeStackSize, kNodesBlockSize, kStoreBlockSize, kLowMemEnd, KSTACK, TFIB_INST in *; unfold MAP, LEN, lst in *.
Ltac tbnum := rewrite ?(ts_inst B TB), ?(ts_depot B TB), ?(ts_store B TB), ?(ts_ial_lo B TB), ?(ts_ial_hi B TB), ?(ts_ial_w B TB), ?(ts_ial_flag B TB), ?(ts_oom B TB) in *;
unfold TFIB_INST, TFIB_DEPOT, TFIB_STORE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W, TFIB_IAL_FLAG, TFIB_OOM, TFIB_IMG_LO, TFIB_IMG_END in *.
Ltac ztri H Z := pose proof H as (_ & _ & Z); unfold zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg in Z.
Ltac zd H := let Y := fresh "ZD" in pose proof H as Y; unfold zdisjoint in Y; cbn [fst snd] in Y; hnum; lia.
Lemma SX : forall i0 j x0 y, nth_error (static_extents ly) i0 = Some x0 -> nth_error (static_extents ly) j = Some y -> i0 <> j -> zdisjoint x0 y.
Proof. geo.
intros i0 j x0 y Hi0 Hj Hne. destruct (Nat.lt_ge_cases i0 j).
- exact (pairwise_nth zdisjoint _ i0 j x0 y (lo_disj _ LO) Hi0 Hj H).
- apply zdisjoint_sym. apply (pairwise_nth zdisjoint _ j i0 y x0 (lo_disj _ LO) Hj Hi0). lia.
Qed.
Lemma SECX : forall e j y, In e (sec_extents ly X) -> nth_error (static_extents ly) j = Some y -> zdisjoint e y.
Proof. geo.
intros e j y He Hj. eapply (pairwise_In zdisjoint _ e y (sec_extents ly X) (static_extents ly) eq_refl (proj2 (am_placed _ _ _ _ M)) He).
eapply nth_error_In. exact Hj.
Qed.
Lemma MAPX : forall j y, nth_error (static_extents ly) j = Some y -> zdisjoint (MAP, LEN) y.
Proof. intros j y Hj. pose proof KFACTS as (_ & _ & _ & _ & _ & _ & IN & _). exact (SECX _ j y IN Hj). Qed.
Lemma ok_low : forall a, TFIB_IMG_LO <= a < TFIB_IMG_END -> ~ DI a -> ok a.
Proof. geo.
intros a Ha NI. pose proof HIGH as HI. pose proof geom as GE. zget HI (ly_T ly) kThreadObjSize ZT. zget HI (ly_Q ly) kPtrArrayResv ZQ. ztri (proj1 GE) ZM.
split; [hnum; lia|]. intros HD.
destruct LST as (y2 & _ & _ & _ & L1 & _ & _ & SZ2 & _). ztri L1 ZL.
apply D_cases in HD as [Y|[[_ Y]|[[Y _]|[[Y _]|[[Y _]|[[Y _]|[Y _]]]]]]].
- clear - Ha Y HI. hnum. lia.
- exact (NI Y).
- clear - Ha Y ZT. hnum. lia.
- clear - Ha Y ZQ. hnum. lia.
- clear - Ha Y ZL SZ2. hnum. lia.
- clear - Ha Y. hnum. lia.
- clear - Ha Y ZM. hnum. lia.
Qed.
Lemma ok_imgsh : forall a, SHADOW_OFF + TFIB_IMG_LO / 8 <= a < SHADOW_OFF + TFIB_IMG_END / 8 -> ok a.
Proof. geo.
intros a Ha. pose proof HIGH as HI. pose proof geom as GE. zget HI (ly_T ly) kThreadObjSize ZT. zget HI (ly_Q ly) kPtrArrayResv ZQ. ztri (proj1 GE) ZM.
unfold TFIB_IMG_LO, TFIB_IMG_END, SHADOW_OFF in Ha. change (65536 / 8) with 8192 in Ha. change (6270976 / 8) with 783872 in Ha.
split; [clear - Ha; lia|]. intros HD.
destruct LST as (y2 & _ & _ & _ & L1 & _ & _ & SZ2 & _). ztri L1 ZL.
apply D_cases in HD as [Y|[[Y _]|[[Y _]|[[Y _]|[[Y _]|[[_ Y]|[Y _]]]]]]].
- clear - Ha Y HI. hnum. lia.
- clear - Ha Y. hnum. lia.
- clear - Ha Y ZT. hnum. lia.
- clear - Ha Y ZQ. hnum. lia.
- clear - Ha Y ZL SZ2. hnum. lia.
-
unfold DH, shadow_addr in Y. destruct GE as (_ & _ & M3 & M4 & M5 & _). clear - Ha Y ZM M3 M4 M5. ceil. unfold SHADOW_OFF, ASAN_CEIL in *.
assert (E8 : LEN / 8 + MAP / 8 = (MAP + LEN) / 8).
{ pose proof M3 as M3'. apply Z.mod_divide in M3' as [q Hq]; [|lia]. rewrite Hq. replace (q * 4096) with ((q * 512) * 8) by lia. rewrite Z_div_mult by lia.
replace (q * 512 * 8 + LEN) with (LEN + (q * 512) * 8) by lia. rewrite Z_div_plus by lia. lia. }
destruct ZM as [Z1|[Z2|Z3]].
+ assert (Y' : (MAP + LEN) / 8 <= 65536 / 8) by (apply Z.div_le_mono; lia). change (65536 / 8) with 8192 in Y'. lia.
+ assert (Y' : 6270976 / 8 <= MAP / 8) by (apply Z.div_le_mono; lia). change (6270976 / 8) with 783872 in Y'. lia.
+ assert (Y' : 17594333495296 / 8 <= MAP / 8) by (apply Z.div_le_mono; lia). change (17594333495296 / 8) with 2199291686912 in Y'. lia.
- clear - Ha Y ZM. hnum. lia.
Qed.
Lemma ok_hshadow : forall a, kLowShadowBeg <= a < kHighMemBeg -> ~ DH a -> ok a.
Proof. geo.
intros a Ha ND. pose proof HIGH as HI. pose proof geom as GE. zget HI (ly_T ly) kThreadObjSize ZT. zget HI (ly_Q ly) kPtrArrayResv ZQ. ztri (proj1 GE) ZM.
split; [clear - Ha; hnum; lia|]. intros HD.
destruct LST as (y2 & _ & _ & _ & L1 & _ & _ & SZ2 & _). ztri L1 ZL.
apply D_cases in HD as [Y|[[Y _]|[[Y _]|[[Y _]|[[Y _]|[[_ Y]|[Y _]]]]]]].
- clear - Ha Y HI. hnum. lia.
- clear - Ha Y. hnum. lia.
- clear - Ha Y ZT. hnum. lia.
- clear - Ha Y ZQ. hnum. lia.
- clear - Ha Y ZL SZ2. hnum. lia.
- exact (ND Y).
- clear - Ha Y ZM. hnum. lia.
Qed.
Lemma ok_static : forall j e a, nth_error (static_extents ly) j = Some e -> (j <> 1)%nat -> (j <> 2)%nat -> (j < 8)%nat ->
fst e <= a < fst e + snd e -> ok a.
Proof. geo.
intros j [ex esz] a Hj J1 J2 J8 Ha. cbn [fst snd] in Ha. pose proof HIGH as (H1 & H2 & _).
pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) (ex, esz)) as HE.
assert (INO : In (ex, esz) (owned_extents ly)).
{ unfold static_extents in Hj. rewrite nth_error_app1 in Hj by (cbn; lia). eapply nth_error_In. exact Hj. }
specialize (HE INO). cbn beta in HE. cbn [fst snd] in HE.
pose proof (zone3_intro ly ex esz IMG ltac:(lia) HE (SX j 9 _ _ Hj eq_refl ltac:(lia))) as (_ & _ & ZZ).
unfold zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg in ZZ.
unfold in_app in HE. split; [clear - Ha HE; hnum; lia|]. intros HD. destruct LST as (y2 & _ & _ & CI & _ & _ & _ & SZ2 & _).
apply D_cases in HD as [Y|[[Y _]|[[Y _]|[[Y _]|[[Y _]|[[Y _]|[Y _]]]]]]].
- zd (SX j 8 _ _ Hj eq_refl ltac:(lia)).
- clear - Ha Y ZZ. hnum. lia.
- zd (SX j 2 _ _ Hj eq_refl ltac:(lia)).
- zd (SX j 1 _ _ Hj eq_refl ltac:(lia)).
- zd (SECX _ j _ CI Hj).
- clear - Ha Y ZZ. hnum. lia.
- zd (MAPX j _ Hj).
Qed.
Lemma ok_T : forall a, T <= a < T + kThreadObjSize -> ~ DJ a -> ok a.
Proof. geo.
intros a Ha ND. pose proof HIGH as HI. zget HI (ly_T ly) kThreadObjSize ZZ. pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & _). split; [clear - Ha H5 H6; hnum; lia|]. intros HD. destruct LST as (y2 & _ & _ & CI & _ & _ & _ & SZ2 & _).
apply D_cases in HD as [Y|[[Y _]|[[_ Y]|[[Y _]|[[Y _]|[[Y _]|[Y _]]]]]]].
- zd (SX 2 8 _ _ eq_refl eq_refl ltac:(lia)).
- clear - Ha Y ZZ. hnum. lia.
- exact (ND Y).
- zd (SX 1 2 _ _ eq_refl eq_refl ltac:(lia)).
- zd (SECX _ 2 _ CI eq_refl).
- clear - Ha Y ZZ. hnum. lia.
- zd (MAPX 2 _ eq_refl).
Qed.
Lemma ok_Q : forall a, ly_Q ly <= a < ly_Q ly + kPtrArrayResv -> ~ DQ a -> ok a.
Proof. geo.
intros a Ha ND. pose proof HIGH as HI. zget HI (ly_Q ly) kPtrArrayResv ZZ. pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & _). split; [clear - Ha H3 H4; hnum; lia|]. intros HD. destruct LST as (y2 & _ & _ & CI & _ & _ & _ & SZ2 & _).
apply D_cases in HD as [Y|[[Y _]|[[Y _]|[[_ Y]|[[Y _]|[[Y _]|[Y _]]]]]]].
- zd (SX 1 8 _ _ eq_refl eq_refl ltac:(lia)).
- clear - Ha Y ZZ. hnum. lia.
- zd (SX 1 2 _ _ eq_refl eq_refl ltac:(lia)).
- exact (ND Y).
- zd (SECX _ 1 _ CI eq_refl).
- clear - Ha Y ZZ. hnum. lia.
- zd (MAPX 1 _ eq_refl).
Qed.
Lemma ok_prim : forall a, ly_prim ly <= a < ly_prim ly + kPrimResvSize -> ok a.
Proof. geo.
intros a Ha. pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & _). split; [hnum; lia|]. intros HD. destruct LST as (y2 & _ & _ & CI & _ & _ & _ & SZ2 & _).
apply D_cases in HD as [Y|[[Y _]|[[Y _]|[[Y _]|[[Y _]|[[Y _]|[Y _]]]]]]].
- zd (SX 0 8 _ _ eq_refl eq_refl ltac:(lia)).
- hnum. lia.
- zd (SX 0 2 _ _ eq_refl eq_refl ltac:(lia)).
- zd (SX 0 1 _ _ eq_refl eq_refl ltac:(lia)).
- zd (SECX _ 0 _ CI eq_refl).
- hnum. lia.
- zd (MAPX 0 _ eq_refl).
Qed.
Lemma ok_other : forall y a, In y (st_chunks X) -> ck_beg y <> ck_beg k -> ck_base B ly y <= a < ck_base B ly y + ck_extent y -> ok a.
Proof. geo.
intros y a Hy Hne Ha. pose proof (chunk_facts B ly X rd y M Hy) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
destruct (ck_beg y) as [|oy|ry oy|c0 p0] eqn:Eby; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & Gxm & Gxs & Gal).
pose proof (region_in_prim ly (prim_class oy) LO ltac:(lia)) as (R1 & R2 & _). apply ok_prim. lia.
- destruct GG as (-> & _ & Gbase & Gext & Gin & _). pose proof HIGH as HI.
pose proof (ZSEC _ Gin) as (ZY & _ & IY3). cbn [fst snd] in ZY, IY3. ztri ZY ZZ.
split; [clear - Ha ZY Gbase Gext; hnum; lia|]. intros HD.
pose proof (secmaps_disjoint B ly X rd y k ry kPage r o M Hy Hk Eby Hb ltac:(rewrite Eby; exact Hne)) as DJ0. pose proof geom as GE.
destruct LST as (y2 & Hy2 & Ey2 & CI2 & L1 & L2 & L3 & SZ2 & DJL).
apply D_cases in HD as [Y|[[Y _]|[[Y _]|[[Y _]|[[Y Ho]|[[Y _]|[Y _]]]]]]].
+ zd (SECX _ 8 _ Gin eq_refl).
+ clear - Ha Y ZZ Gbase Gext. hnum. lia.
+ zd (SECX _ 2 _ Gin eq_refl).
+ zd (SECX _ 1 _ Gin eq_refl).
+
destruct (sptr_eqb (ck_beg y) (ck_beg y2)) eqn:EQB; [apply sptr_eqb_spec in EQB as Eq | assert (Hne2 : ck_beg y <> ck_beg y2) by (intros EE; apply sptr_eqb_spec in EE; congruence)].
* rewrite Eby, Ey2 in Eq. injection Eq as Er. unfold lst in Y. rewrite <- Er in Y. unfold kPage in *. lia.
* pose proof (secmaps_disjoint B ly X rd y y2 ry kPage lastr kPage M Hy Hy2 Eby Ey2 Hne2) as DJ2. fold lst in DJ2. zd DJ2.
+ clear - Ha Y ZZ Gbase Gext. hnum. lia.
+ zd DJ0.
Qed.
Lemma ok_secpage : forall y ry oy a, In y (st_chunks X) -> ck_beg y = PSec ry oy -> ry <> r -> ly_sec ly ry <= a < ly_sec ly ry + kPage ->
~ (ry = lastr /\ own = false /\ ly_sec ly ry + 24 <= a < ly_sec ly ry + 32) -> ok a.
Proof. geo.
intros y ry oy a Hy Eby Hry Ha NL. pose proof (chunk_facts B ly X rd y M Hy) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG). rewrite Eby in GG.
destruct GG as (-> & _ & Gbase & Gext & Gin & _). pose proof HIGH as HI.
pose proof (ZSEC _ Gin) as (ZY & _ & I2). cbn [fst snd] in ZY, I2. pose proof ZY as (I1 & _ & ZZ). unfold zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg in ZZ.
pose proof (req_size_bounds (ck_req y) ltac:(lia)) as (_ & Q2 & _).
assert (Hne : ck_beg y <> ck_beg k) by (rewrite Eby, Hb; intros E; injection E; intros; exact (Hry ltac:(assumption))).
pose proof (secmaps_disjoint B ly X rd y k ry kPage r o M Hy Hk Eby Hb Hne) as DJ0.
split; [hnum; lia|]. intros HD. destruct LST as (y2 & Hy2 & Ey2 & CI2 & L1 & L2 & L3 & SZ2 & DJL).
apply D_cases in HD as [Y|[[Y _]|[[Y _]|[[Y _]|[[Y Ho]|[[Y _]|[Y _]]]]]]].
- zd (SECX _ 8 _ Gin eq_refl).
- clear - Ha Y ZZ Gext G5 G8 Q2. hnum. lia.
- zd (SECX _ 2 _ Gin eq_refl).
- zd (SECX _ 1 _ Gin eq_refl).
- destruct (Nat.eq_dec ry lastr) as [->|Hne2]; [apply NL; unfold lst in Y; splits; [reflexivity | exact Ho | lia | lia]|].
assert (Hne3 : ck_beg y <> ck_beg y2) by (rewrite Eby, Ey2; intros E; injection E; intros; exact (Hne2 ltac:(assumption))).
pose proof (secmaps_disjoint B ly X rd y y2 ry kPage lastr kPage M Hy Hy2 Eby Ey2 Hne3) as DJ2. zd DJ2.
- clear - Ha Y ZZ Gext G5 G8 Q2. hnum. lia.
- zd DJ0.
Qed.
Lemma ok_batch : forall b2 a, In b2 (all_batches X) -> ly_space ly + b_self b2 <= a < ly_space ly + b_self b2 + kBatchBytes -> ok a.
Proof. geo.
intros b2 a Hb2 Ha. destruct (AFez.batch_geom B ly X rd M b2 Hb2) as (xb & Eb & Pb & _ & Ub & [AU MU] & _) || idtac.
pose proof (region_in_prim ly kBatchClass LO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & _).
pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
assert (INB : In (b_self b2 - region_off kBatchClass) (batch_offs X kBatchClass)) by (rewrite batch_offs_24; apply in_map_iff; exists b2; auto).
pose proof (proj1 (Forall_forall _ _) (wr_elems _ _ _ _ _ _ CL) _ ltac:(rewrite !in_app_iff; right; right; right; exact INB)) as [B1 B2].
pose proof (wr_alloc _ _ _ _ _ _ CL) as AL'. pose proof (mapped_user_bound (as_universe B) 0 0 0 X kBatchClass WF ltac:(unfold kBatchClass; lia)) as MB.
unfold kUserMapSize, EV_MAX, region_base in *. rewrite region_off_eq in * by (unfold kBatchClass; lia). unfold kBatchClass, kBatchBytes in *.
apply ok_prim. lia.
Qed.
Lemma ok_rinfo : okr (ly_rinfo ly) 4096.
Proof. geo. intros a Ha. pose proof HIGH as HI. unfold ly_rinfo in Ha. apply ok_prim. unfold kSpaceSize, kRegionInfoOff, kPrimResvSize in *; lia. Qed.
Lemma ok_fa : forall c', 1 <= c' <= 31 -> okr (fa_base ly c') kFreeArrayMax.
Proof. geo.
intros c' Hc' a Ha. pose proof (region_in_prim ly c' LO Hc') as (R1 & R2 & _). unfold fa_base in Ha. unfold region_base in *.
apply ok_prim. unfold kFreeArrayOffset, kFreeArrayMax in *; lia.
Qed.
Lemma ok_inst : forall a, as_inst B <= a < as_inst B + 3632 -> ~ DI a -> ok a.
Proof. geo. intros a Ha NI. pose proof HIGH as HI. apply ok_low; [hnum; lia | exact NI]. Qed.
Lemma ok_F : okr (ly_F ly) kFakeStackSize. Proof. intros a Ha. exact (ok_static 3 _ a eq_refl ltac:(lia) ltac:(lia) ltac:(lia) Ha). Qed.
Definition low_oks (a w : Z) : bool :=
((TFIB_IMG_LO <=? a) && ((a + w <=? TFIB_INST + 120) || ((TFIB_INST + 129 <=? a) && (a + w <=? TFIB_INST + 144)) || ((TFIB_INST + 160 <=? a) && (a + w <=? TFIB_INST + 680))
|| ((TFIB_INST + 684 <=? a) && (a + w <=? TFIB_INST + 704)) || ((TFIB_INST + 720 <=? a) && (a + w <=? TFIB_IMG_END))))
|| ((SHADOW_OFF + TFIB_IMG_LO / 8 <=? a) && (a + w <=? SHADOW_OFF + TFIB_IMG_END / 8)).
Definition const_loc_oks (ce : acell) : nat :=
let w := Z.max 1 (Z.of_nat (c_w ce)) in
match c_at ce with
| ANum a => if ((a =? TFIB_INST + 681) && (w =? 1)) || ((a =? TFIB_INST + 682) && (w =? 2)) then 5%nat else if low_oks a w then 1%nat else 0%nat
| AT o' => if (0 <=? o') && (o' + w <=? 80) then 2%nat else 0%nat
| AC o' => if (0 <=? o') && (o' + w <=? 256) then 3%nat else 0%nat
| AD o' => if (0 <=? o') && (o' + w <=? 4096) then 4%nat else 0%nat
| ATsd o' => if low_oks (TFIB_TSD + o') w then 1%nat else 0%nat
| ATp o' => if low_oks (TFIB_TP + o') w then 1%nat else 0%nat
| AInst o' => if low_oks (TFIB_INST + o') w then 1%nat else 0%nat
| _ => 0%nat
end.
Lemma Tfib_const_locs : forallb (fun ce => negb (Nat.eqb (const_loc_oks ce) 0)) (Tfib_const ly) = true.
Proof. clear. vm_compute. reflexivity. Qed.
Lemma Tfib_const_pads : forallb (fun ce => negb (Nat.eqb (const_loc_oks ce) 5) || match c_val ce with AV (ANum 0) => true | _ => false end) (Tfib_const ly) = true.
Proof. clear. vm_compute. reflexivity. Qed.
Lemma le_byte_0 : forall w kk, le_byte 0 w kk = 0.
Proof. clear. intros w kk. unfold le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l. reflexivity. Qed.
Lemma CONST' : Forall (cell_holds B ly rd') (as_const B ly).
Proof.
clear VIS NS' QI' LST'.
pose proof HIGH as HI. pose proof (am_const B ly X rd M) as OLDc. rewrite (ts_const _ TB) in OLDc |- *.
apply Forall_forall. intros ce Hce. pose proof (proj1 (Forall_forall _ _) OLDc ce Hce) as Hold.
pose proof (proj1 (forallb_forall _ _) Tfib_const_locs ce Hce) as K. pose proof (proj1 (forallb_forall _ _) Tfib_const_pads ce Hce) as P.
cbn beta in K, P. clear Hce OLDc.
destruct ce as [ca cw cv]. cbv beta zeta delta [const_loc_oks c_at c_w c_val] in K, P.
set (w := Z.max 1 (Z.of_nat cw)) in K, P.
assert (XFER : (forall j, 0 <= j < w -> ok (aeval B ly ca + j)) -> cell_holds B ly rd' (ACell ca cw cv)).
{ intros Hok. eapply (cell_holds_agree B ly rd rd' _ Hold). cbn [c_at c_w]. intros j Hj. apply AGok. apply Hok. subst w. exact Hj. }
assert (LOW : forall a, low_oks a w = true -> forall j, 0 <= j < w -> ok (a + j)).
{ intros a La j Hj. unfold low_oks in La. subst w. apply Bool.orb_true_iff in La as [La|La].
- apply ok_low; [| unfold DI; rewrite (ts_inst _ TB)]; clear - La Hj; unfold TFIB_IMG_LO, TFIB_IMG_END, TFIB_INST in *; lia.
- apply ok_imgsh. clear - La Hj. unfold TFIB_IMG_LO, TFIB_IMG_END, SHADOW_OFF in *. change (65536 / 8) with 8192 in La. change (6270976 / 8) with 783872 in La. cbn -[Z.add Z.leb Z.mul] in La. lia. }
destruct ca; try discriminate K; cbn [aeval] in XFER |- *.
-
destruct (((z =? TFIB_INST + 681) && (w =? 1)) || ((z =? TFIB_INST + 682) && (w =? 2))) eqn:C5.
+
cbn [negb Nat.eqb orb] in P. destruct cv as [e|mk mv]; [|discriminate P]. destruct e; try discriminate P. destruct z0; try discriminate P.
unfold cell_holds. cbn [c_at c_w c_val aeval]. intros kk Hkk. rewrite le_byte_0.
replace (z + Z.of_nat kk) with (as_inst B + 680 + (z - TFIB_INST - 680 + Z.of_nat kk)) by (rewrite (ts_inst _ TB); lia).
apply MUT'. subst w. clear - C5 Hkk. lia.
+ destruct (low_oks z w) eqn:C1; [apply XFER; exact (LOW z C1) | discriminate K].
-
destruct ((0 <=? off) && (off + w <=? 80)) eqn:C2; [|discriminate K].
apply XFER. intros j Hj. subst w. apply ok_T; [| unfold DJ]; clear - C2 Hj; unfold t_stats, kThreadObjSize; lia.
-
destruct ((0 <=? off) && (off + w <=? 256)) eqn:C2; [|discriminate K].
apply XFER. intros j Hj. subst w. apply (ok_static 6 (ly_C ly, 256)); [reflexivity | lia | lia | lia |]. cbn [fst snd]. clear - C2 Hj. lia.
-
destruct (low_oks (TFIB_TSD + off) w) eqn:C1; [|discriminate K]. apply XFER. rewrite HTSD. exact (LOW _ C1).
-
destruct (low_oks (TFIB_INST + off) w) eqn:C1; [|discriminate K]. apply XFER. rewrite (ts_inst _ TB). exact (LOW _ C1).
-
destruct (low_oks (TFIB_TP + off) w) eqn:C1; [|discriminate K]. apply XFER. rewrite (ts_tp _ TB). exact (LOW _ C1).
-
destruct ((0 <=? off) && (off + w <=? 4096)) eqn:C2; [|discriminate K].
apply XFER. intros j Hj. subst w. apply (ok_static 7 (ly_D ly, 4096)); [reflexivity | lia | lia | lia |]. cbn [fst snd]. clear - C2 Hj. lia.
Qed.
Definition cell_in (lo len : Z) (ce : acell) : Prop :=
lo <= aeval B ly (c_at ce) /\ aeval B ly (c_at ce) + Z.max 1 (Z.of_nat (c_w ce)) <= lo + len.
Lemma cell_xfer : forall ce, cell_holds B ly rd ce ->
(forall j, 0 <= j < Z.max 1 (Z.of_nat (c_w ce)) -> ok (aeval B ly (c_at ce) + j)) -> cell_holds B ly rd' ce.
Proof. intros ce Hce Hok. eapply (cell_holds_agree B ly rd rd' ce Hce). intros j Hj. apply AGok, Hok, Hj. Qed.
Lemma cells_xfer : forall Lc lo len, okr lo len -> Forall (cell_in lo len) Lc -> Forall (cell_holds B ly rd) Lc -> Forall (cell_holds B ly rd') Lc.
Proof.
intros Lc lo len OK IN OLD'. apply Forall_forall. intros ce Hce. apply cell_xfer; [exact (proj1 (Forall_forall _ _) OLD' ce Hce)|].
intros j Hj. destruct (proj1 (Forall_forall _ _) IN ce Hce) as [I1 I2]. apply OK. lia.
Qed.
Lemma OLD : forall ce, In ce (acells B ly X) -> cell_holds B ly rd ce.
Proof. intros ce Hce. exact (proj1 (Forall_forall _ _) (am_cells B ly X rd M) ce Hce). Qed.
Ltac old_in := apply Forall_forall; intros ? HIN; apply OLD; unfold acells; rewrite !in_app_iff.
Lemma EA : forall y d, In y (st_chunks X) -> aeval B ly (aoff (sptr_exp (ck_beg y)) d) = ck_base B ly y + d.
Proof. geo.
intros y d Hy. pose proof (chunk_facts B ly X rd y M Hy) as (_ & _ & _ & _ & _ & _ & _ & _ & GG).
unfold ck_base, sptr_addr. destruct (ck_beg y) as [|oy|ry oy|c' p']; try solve [destruct GG]; cbn; lia.
Qed.
Lemma EA2 : forall y d d', In y (st_chunks X) -> aeval B ly (aoff (aoff (sptr_exp (ck_beg y)) d) d') = ck_base B ly y + d + d'.
Proof. geo.
intros y d d' Hy. pose proof (chunk_facts B ly X rd y M Hy) as (_ & _ & _ & _ & _ & _ & _ & _ & GG).
unfold ck_base, sptr_addr. destruct (ck_beg y) as [|oy|ry oy|c' p']; try solve [destruct GG]; cbn; lia.
Qed.
Lemma EA0 : forall y, aeval B ly (sptr_exp (ck_beg y)) = ck_base B ly y. Proof. geo. reflexivity. Qed.
Ltac fcons := apply Forall_cons; [split; cbn; lia|].
Lemma cells_regions : Forall (cell_holds B ly rd') (flat_map (region_cells X2) (zseq 1 31)).
Proof.
apply Forall_flat_map'. intros c' Hc'. apply zseq_In in Hc'. unfold region_cells. rewrite reg'.
apply (cells_xfer _ _ _ ok_rinfo).
- unfold cell_in, ly_rinfo, kRegionInfoOff. repeat fcons. apply Forall_nil.
- old_in. left. apply in_flat_map. exists c'. split; [apply In_zseq; lia | exact HIN].
Qed.
Lemma okr_cache : okr (T + t_cache + 80) (80 * 31).
Proof. geo. intros a Ha. apply ok_T; unfold DJ, t_cache, t_stats, kThreadObjSize in *; lia. Qed.
Lemma cells_caches : Forall (cell_holds B ly rd') (flat_map (cache_cells X2) (zseq 1 31)).
Proof.
apply Forall_flat_map'. intros c' Hc'. apply zseq_In in Hc'. unfold cache_cells. rewrite cache', X2_cinit.
apply (cells_xfer _ _ _ okr_cache).
- pose proof (wf_classes _ _ _ _ _ WF c' ltac:(lia)) as CL. pose proof (wr_cache _ _ _ _ _ _ CL) as WC. pose proof (class_ok c' ltac:(lia)) as (_ & _ & _ & K4 & _).
rewrite Hci in WC. destruct WC as [PM PL]. unfold cell_in, t_cache. repeat fcons.
apply Forall_forall. intros ce Hce. apply in_map_iff in Hce as ([i0 v] & <- & Hiv). cbn [fst snd c_at c_w z4 c4 aeval aoff].
apply in_combine_l in Hiv. apply in_seq in Hiv. cbn. lia.
- old_in. right; left. apply in_flat_map. exists c'. split; [apply In_zseq; lia |]. unfold cache_cells. rewrite Hci. exact HIN.
Qed.
Lemma cells_chunk_other : forall y, In y (st_chunks X) -> ck_beg y <> ck_beg k -> Forall (cell_holds B ly rd') (chunk_cells y).
Proof.
intros y Hy Hne. pose proof (chunk_facts B ly X rd y M Hy) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
apply (cells_xfer _ (ck_base B ly y) (ck_extent y)); [intros a Ha; exact (ok_other y a Hy Hne Ha) | |].
- pose proof (req_size_bounds (ck_req y) ltac:(lia)) as (_ & Q2 & _).
unfold chunk_cells, kChunkHeaderSize, cell_in. apply Forall_app. split.
+ repeat (apply Forall_cons; [cbn [c_at c_w z1 z2 z4 c1 c2 c4]; rewrite ?(EA2 y), ?(EA y), ?EA0 by exact Hy; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.max Pos.max Z.pos_sub]; lia|]). apply Forall_nil.
+ destruct (Z.eqb_spec (ck_rz y) 16); [apply Forall_nil|].
repeat (apply Forall_cons; [cbn [c_at c_w z8 c8]; rewrite ?(EA2 y), ?(EA y), ?EA0 by exact Hy; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.max Pos.max Z.pos_sub]; lia|]). apply Forall_nil.
- old_in. do 2 right; left. apply in_flat_map. exists y. split; [exact Hy | exact HIN].
Qed.
Lemma cells_chunks : Forall (cell_holds B ly rd') (flat_map chunk_cells (st_chunks X2)).
Proof.
destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2). rewrite X2_chunks, E1, flat_map_app, Forall_app. split.
- apply Forall_flat_map'. intros y Hy. apply cells_chunk_other; [rewrite E; apply in_app_iff; left; exact Hy | intros Ey; apply N1; rewrite <- Ey; apply in_map; exact Hy].
- apply Forall_flat_map'. intros y Hy. apply cells_chunk_other; [rewrite E; apply in_app_iff; right; right; exact Hy | intros Ey; apply N2; rewrite <- Ey; apply in_map; exact Hy].
Qed.
Lemma cells_sec : Forall (cell_holds B ly rd') (sec_cells X2).
Proof.
destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2). pose proof (wf_secondary _ _ _ _ _ WF) as XS. destruct XS as [Snd Sac Sal Sres Sral].
pose proof ARR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). pose proof ARR' as (B1 & B2 & B3 & B4 & B5 & B6). pose proof HIGH as HI.
assert (OLDS : Forall (cell_holds B ly rd) (sec_cells X)) by (old_in; do 3 right; left; exact HIN).
unfold sec_cells in OLDS |- *. rewrite X2_sec_res, X2_sec_arr, X2_chunks, E1. fold arr in OLDS. rewrite E in OLDS.
rewrite flat_map_app in OLDS |- *. cbn [flat_map] in OLDS. rewrite Hb in OLDS. cbn [app] in OLDS.
apply Forall_cons_iff in OLDS as [O1 OLDS]. apply Forall_cons_iff in OLDS as [O2 OLDS]. apply Forall_cons_iff in OLDS as [O3 OLDS]. apply Forall_app in OLDS as [O4 O5].
assert (EI : as_inst B = TFIB_INST) by (exact (ts_inst _ TB)).
apply Forall_cons; [apply (cell_xfer _ O1); intros j Hj; apply ok_inst; [cbn in Hj |- *; unfold o_sec_reserved; lia | unfold DI; cbn in Hj |- *; unfold o_sec_reserved; lia]|].
apply Forall_cons.
{   intros kk Hkk. cbn [c_at c_w z8 c8 aeval]. rewrite B1. unfold o_sec_n.
replace (Z.of_nat (length arr - 1)) with (nA - 1) by (unfold nA; lia). exact (NS' kk Hkk). }
apply Forall_cons.
{   intros kk Hkk. cbn [c_at c_w z1 c1 aeval]. unfold o_sec_mutex. destruct kk; [|cbn in Hkk; lia]. cbn [Z.of_nat].
pose proof (MUT' 0 ltac:(lia)) as MU. rewrite !Z.add_0_r in MU |- *. rewrite MU. reflexivity. }
apply Forall_app. split.
-
apply Forall_forall. intros ce Hce. apply in_map_iff in Hce as ([j r'] & <- & Hjr). apply in_combine_seq0 in Hjr. cbn [fst snd].
destruct (Nat.eq_dec j i) as [->|Hne].
+ pose proof (nth_error_lt _ _ _ Hjr) as LT. rewrite B1 in LT.
assert (Ho : own = false) by (unfold own, idx, nA; apply Z.eqb_neq; lia).
rewrite (B3 Ho) in Hjr. injection Hjr as <-. intros kk Hkk. cbn [c_at c_w c8 aeval]. fold lst. rewrite Z.add_0_r. unfold qi, idx in QI'. exact (QI' kk Hkk).
+ rewrite (B2 j (nth_error_lt _ _ _ Hjr) Hne) in Hjr.
assert (OC : cell_holds B ly rd (c8 (AQ (8 * Z.of_nat j)) (ASec r' 0))).
{ apply (proj1 (Forall_forall _ _) O4). apply in_map_iff. exists (j, r'). split; [reflexivity|]. apply in_combine_seq0. exact Hjr. }
apply (cell_xfer _ OC). intros jj Hjj. cbn [c_at c_w c8 aeval] in Hjj |- *. pose proof (nth_error_lt _ _ _ Hjr) as LT.
apply ok_Q; [unfold kPtrArrayResv; unfold nA in A4; lia | unfold DQ, qi, idx; lia].
-
apply Forall_forall. intros ce Hce. rewrite <- flat_map_app in Hce. apply in_flat_map in Hce as (y & Hy & Hce).
assert (Hy' : In y (st_chunks X)) by (rewrite E; apply in_app_iff in Hy as [Hy|Hy]; apply in_app_iff; [left; exact Hy | right; right; exact Hy]).
assert (Hne : ck_beg y <> ck_beg k) by (intros Ey; apply in_app_iff in Hy as [Hy|Hy]; [apply N1 | apply N2]; rewrite <- Ey; apply in_map; exact Hy).
destruct (ck_beg y) as [|oy|ry oy|c' p] eqn:Eby; try solve [destruct Hce].
assert (Hry : ry <> r) by (intros ->; apply Hne; rewrite Hb; pose proof (chunk_facts B ly X rd y M Hy') as (_ & _ & _ & _ & _ & _ & _ & _ & GG); rewrite Eby in GG;
destruct GG as (-> & _); pose proof KFACTS as (-> & _); reflexivity).
assert (OC : forall ce', In ce' [c8 (ASec ry 0) (ASec ry 0); z8 (ASec ry 8) (sec_map_size (ck_req y)); z8 (ASec ry 16) (needed_size (ck_req y)); z8 (ASec ry 24) (index_ofZ arr ry)] ->
cell_holds B ly rd ce').
{ intros ce' H'. apply (proj1 (Forall_forall _ _) O5). destruct (in_app_or _ _ _ Hy) as [Hy1|Hy2].
- apply in_app_iff. left. apply in_flat_map. exists y. split; [exact Hy1|]. rewrite Eby. exact H'.
- apply in_app_iff. right. do 4 right. apply in_flat_map. exists y. split; [exact Hy2|]. rewrite Eby. exact H'. }
assert (INY : In ry arr) by (apply Sac; exists y; split; [exact Hy'|]; rewrite Eby; pose proof (chunk_facts B ly X rd y M Hy') as (_ & _ & _ & _ & _ & _ & _ & _ & GG); rewrite Eby in GG; destruct GG as (-> & _); reflexivity).
assert (OKP : forall a, ly_sec ly ry <= a < ly_sec ly ry + 24 -> ok a).
{ intros a Ha. eapply (ok_secpage y ry oy a Hy' Eby Hry); [unfold kPage; lia | intros (_ & _ & Z3); lia]. }
destruct Hce as [<-|[<-|[<-|[<-|[]]]]].
+ eapply cell_xfer; [apply OC; cbn; tauto | intros j Hj; apply OKP; cbn in Hj |- *; lia].
+ eapply cell_xfer; [apply OC; cbn; tauto | intros j Hj; apply OKP; cbn in Hj |- *; lia].
+ eapply cell_xfer; [apply OC; cbn; tauto | intros j Hj; apply OKP; cbn in Hj |- *; lia].
+
destruct (In_nth_error _ _ INY) as [j Hj].
destruct (Nat.eq_dec ry lastr) as [->|Hnl].
*
assert (Ho : own = false) by (destruct own eqn:Eo; [exfalso; apply Hry; apply A8; reflexivity | reflexivity]).
rewrite (index_ofZ_nth arr' i lastr B4 (B3 Ho)). intros kk Hkk. cbn [c_at c_w z8 c8 aeval]. fold lst. rewrite ?Z.add_0_r. unfold idx in LST'. exact (LST' Ho kk Hkk).
* assert (Hji : j <> i) by (intros ->; unfold arr in Hj; rewrite Hi in Hj; injection Hj as ->; exact (Hry eq_refl)).
assert (Hjl : j <> (length arr - 1)%nat) by (intros ->; rewrite A6 in Hj; injection Hj as EL; exact (Hnl (eq_sym EL))).
pose proof (nth_error_lt _ _ _ Hj) as LT.
rewrite (index_ofZ_nth arr' j ry B4 ltac:(rewrite (B2 j ltac:(lia) Hji); exact Hj)). rewrite <- (index_ofZ_nth arr j ry A3 Hj).
eapply cell_xfer; [apply OC; cbn; tauto |]. intros jj Hjj. cbn [c_at c_w z8 c8 aeval] in Hjj |- *.
eapply (ok_secpage y ry oy _ Hy' Eby Hry); [unfold kPage; lia | intros (Z1 & _ & _); exact (Hnl Z1)].
Qed.
Lemma batch_cells_within : forall l ce, In ce (batch_cells l) ->
exists b2, In b2 l /\ cell_in (ly_space ly + b_self b2) (24 + 8 * Z.of_nat (length (b_items b2))) ce.
Proof. geo.
induction l as [|b2 t IH]; intros ce Hce; [destruct Hce|]. cbn [batch_cells] in Hce.
destruct Hce as [<-|[<-|[<-|Hce]]]; try (exists b2; split; [left; reflexivity | unfold cell_in; cbn; lia]).
apply in_app_iff in Hce as [Hce|Hce].
- apply in_map_iff in Hce as ([i0 y] & <- & Hiy). apply in_combine_l in Hiy. apply in_seq in Hiy. exists b2. split; [left; reflexivity | unfold cell_in; cbn; lia].
- destruct (IH ce Hce) as (b3 & I3 & C3). exists b3. split; [right; exact I3 | exact C3].
Qed.
Lemma okr_batch : forall b2, In b2 (all_batches X) -> okr (ly_space ly + b_self b2) (24 + 8 * Z.of_nat (length (b_items b2))).
Proof. geo.
intros b2 Hb2 a Ha. pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wf_quarantine _ _ _ _ _ WF)) b2 Hb2) as [L1 L2]. unfold kBatchSlots in L2.
apply (ok_batch b2 a Hb2). unfold kBatchBytes. lia.
Qed.
Ltac oki off := apply ok_inst; [cbn in *; unfold off in *; lia | unfold DI; cbn in *; unfold off in *; lia].
Lemma cells_quar : Forall (cell_holds B ly rd') (quar_cells X2).
Proof.
assert (OLDQ : Forall (cell_holds B ly rd) (quar_cells X)) by (old_in; do 4 right; left; exact HIN).
assert (OKQ : okr (T + t_qc) 32) by (intros a Ha; apply ok_T; [unfold t_qc, kThreadObjSize in *; lia|]; unfold DJ, t_qc, t_stats in *; lia).
unfold quar_cells, qc_cells in OLDQ |- *. rewrite X2_qglobal, X2_qthread.
apply Forall_cons_iff in OLDQ as [O1 OLDQ]. apply Forall_cons_iff in OLDQ as [O2 OLDQ]. apply Forall_app in OLDQ as [OT OG].
apply Forall_cons; [apply (cell_xfer _ O1); intros j Hj; oki o_q_cmutex|].
apply Forall_cons; [apply (cell_xfer _ O2); intros j Hj; oki o_q_rmutex|].
apply Forall_app. split.
- apply Forall_cons_iff in OT as [O3 OT]. apply Forall_cons_iff in OT as [O4 OT]. apply Forall_cons_iff in OT as [O5 OT]. apply Forall_cons_iff in OT as [O6 OT].
apply Forall_cons; [apply (cell_xfer _ O3); intros j Hj; apply OKQ; cbn in Hj |- *; lia|].
apply Forall_cons; [apply (cell_xfer _ O4); intros j Hj; apply OKQ; cbn in Hj |- *; lia|].
apply Forall_cons; [apply (cell_xfer _ O5); intros j Hj; apply OKQ; cbn in Hj |- *; lia|].
apply Forall_cons; [apply (cell_xfer _ O6); intros j Hj; apply OKQ; cbn in Hj |- *; lia|].
apply Forall_forall. intros ce Hce. apply (cell_xfer _ (proj1 (Forall_forall _ _) OT ce Hce)).
destruct (batch_cells_within _ ce Hce) as (b2 & I2 & [R1 R2]). intros j Hj. apply (okr_batch b2); [unfold all_batches; apply in_app_iff; left; exact I2 | lia].
- apply Forall_cons_iff in OG as [G1 OG]. apply Forall_cons_iff in OG as [G2 OG]. apply Forall_cons_iff in OG as [G3 OG]. apply Forall_cons_iff in OG as [G4 OG].
apply Forall_cons; [apply (cell_xfer _ G1); intros j Hj; oki o_q_size|].
apply Forall_cons; [apply (cell_xfer _ G2); intros j Hj; oki o_q_size|].
apply Forall_cons; [apply (cell_xfer _ G3); intros j Hj; oki o_q_size|].
apply Forall_cons; [apply (cell_xfer _ G4); intros j Hj; oki o_q_size|].
apply Forall_forall. intros ce Hce. apply (cell_xfer _ (proj1 (Forall_forall _ _) OG ce Hce)).
destruct (batch_cells_within _ ce Hce) as (b2 & I2 & [R1 R2]). intros j Hj. apply (okr_batch b2); [unfold all_batches; apply in_app_iff; right; exact I2 | lia].
Qed.
Lemma cells_fs : Forall (cell_holds B ly rd') (fs_cells X2).
Proof.
assert (OLDF : Forall (cell_holds B ly rd) (fs_cells X)) by (old_in; do 5 right; left; exact HIN).
unfold fs_cells in OLDF |- *. rewrite X2_fs. apply (cells_xfer _ _ _ ok_F); [|exact OLDF].
unfold cell_in, kFakeStackSize. fcons. fcons.
apply Forall_forall. intros ce Hce. apply in_map_iff in Hce as ([i0 h] & <- & Hih). apply in_combine_l in Hih. apply in_seq in Hih. cbn. lia.
Qed.
Lemma cells_depot : Forall (cell_holds B ly rd') (depot_cells ly X2).
Proof.
assert (OLDD : Forall (cell_holds B ly rd) (depot_cells ly X)) by (old_in; do 6 right; left; exact HIN).
unfold depot_cells, depot_ids, depot_frames in OLDD |- *. rewrite X2_depot. pose proof (aso_cells _ (am_syms _ _ _ _ M)) as AC. pose proof HIGH as HI.
pose proof (ts_depot _ TB) as ED. pose proof (ts_store _ TB) as EST.
apply Forall_forall. intros ce Hce. apply (cell_xfer _ (proj1 (Forall_forall _ _) OLDD ce Hce)). intros j Hj.
apply ok_low; [| unfold DI; rewrite (ts_inst _ TB)];
destruct Hce as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hj |- *; rewrite ?ED, ?EST; unfold d_nuniq, d_map1, s_total, s_block0, kLowMemEnd, kHighShadowBeg, TFIB_DEPOT, TFIB_STORE, TFIB_INST, TFIB_IMG_LO, TFIB_IMG_END in *; lia.
Qed.
Lemma cells_ialloc : Forall (cell_holds B ly rd') (ialloc_cells B X2).
Proof.
assert (OLDI : Forall (cell_holds B ly rd) (ialloc_cells B X)) by (old_in; do 7 right; left; exact HIN).
unfold ialloc_cells in OLDI |- *. rewrite X2_inited. pose proof (aso_cells _ (am_syms _ _ _ _ M)) as AC. pose proof (aso_ialloc _ (am_syms _ _ _ _ M)) as [I1 I2].
pose proof (ts_ial_lo _ TB) as E1. pose proof (ts_ial_hi _ TB) as E2. pose proof (ts_ial_w _ TB) as E3. pose proof (ts_ial_flag _ TB) as E4.
apply Forall_forall. intros ce Hce. apply (cell_xfer _ (proj1 (Forall_forall _ _) OLDI ce Hce)). intros j Hj.
apply ok_low; [| unfold DI; rewrite (ts_inst _ TB)];
destruct Hce as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hj |- *; rewrite ?E1, ?E2, ?E3, ?E4 in *; unfold kLowMemEnd, kHighShadowBeg, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W, TFIB_IAL_FLAG, TFIB_INST, TFIB_IMG_LO, TFIB_IMG_END in *; lia.
Qed.
Lemma cells_thread : Forall (cell_holds B ly rd') thread_cells.
Proof.
assert (OLDT : Forall (cell_holds B ly rd) thread_cells) by (old_in; do 8 right; exact HIN).
unfold thread_cells in OLDT |- *. apply Forall_cons_iff in OLDT as [O1 _]. apply Forall_cons; [|apply Forall_nil].
apply (cell_xfer _ O1). intros j Hj. cbn in Hj |- *. apply ok_T; [unfold t_unwinding, kThreadObjSize in *; lia|]. unfold DJ, t_stats, t_unwinding in *; lia.
Qed.
Lemma cells_all : Forall (cell_holds B ly rd') (acells B ly X2).
Proof.
unfold acells. rewrite !Forall_app. splits.
- exact cells_regions.
- exact cells_caches.
- exact cells_chunks.
- exact cells_sec.
- exact cells_quar.
- exact cells_fs.
- exact cells_depot.
- exact cells_ialloc.
- exact cells_thread.
Qed.
Lemma fa' : fa_entries_ok ly rd' X2.
Proof.
intros c' i0 v Hc' Hi0 Hv kk Hkk. rewrite reg' in Hi0, Hv. rewrite AGok; [exact (am_fa B ly X rd M c' i0 v Hc' Hi0 Hv kk Hkk)|].
pose proof (wf_classes _ _ _ _ _ WF c' Hc') as CL. pose proof (wr_fa_len _ _ _ _ _ _ CL) as FL. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as FB.
apply (ok_fa c' Hc'). lia.
Qed.
Lemma flags' : fs_flags_ok ly rd' X2.
Proof.
intros cid pos Hc0 Hp. rewrite frames'. rewrite AGok; [exact (am_flags B ly X rd M cid pos Hc0 Hp)|].
pose proof (flag_off_bounds cid pos Hc0 Hp) as FB. unfold flag_addr, kFakeFlagsOff, kFakeFramesOff in *. apply ok_F. unfold kFakeStackSize. lia.
Qed.
Lemma depot' : depot_ok B ly rd' X2.
Proof.
pose proof (am_depot B ly X rd M) as (heads & links & D1 & D2 & D3). pose proof (aso_cells _ (am_syms _ _ _ _ M)) as AC. pose proof HIGH as HI.
pose proof (ts_depot _ TB) as ED.
unfold depot_ok, depot_ids, depot_traces in *. rewrite X2_depot. exists heads, links. split; [|split; [|exact D3]].
- intros b0 Hb0. destruct (D1 b0 Hb0) as [Y1 Y2]. split; [exact Y1|]. intros kk Hkk. rewrite AGok; [exact (Y2 kk Hkk)|].
apply ok_low; [| unfold DI; rewrite (ts_inst _ TB)]; rewrite ED; unfold d_tab_words, kLowMemEnd, kHighShadowBeg, TFIB_DEPOT, TFIB_INST, TFIB_IMG_LO, TFIB_IMG_END in *; lia.
- intros id Hid. destruct (D2 id Hid) as (Y1 & Y2 & Y3). split; [exact Y1|].
assert (NB : Z.of_nat (length (st_depot X)) <= 4096).
{ pose proof (wf_depot _ _ _ _ _ WF) as [ND INC]. pose proof (NoDup_incl_length ND INC). destruct (am_universe B ly X rd M) as (U1 & _). unfold DEPOT_MAX in U1. lia. }
assert (OKN : forall kk, 0 <= kk < 16 -> ok (ly_NB ly + 16 * id + kk)).
{ intros kk Hkk. apply (ok_static 4 _ _ eq_refl ltac:(lia) ltac:(lia) ltac:(lia)). cbn [fst snd]. unfold kNodesBlockSize. lia. }
split; intros kk Hkk; rewrite AGok; auto; [apply OKN; lia|].
replace (ly_NB ly + 16 * id + 8 + Z.of_nat kk) with (ly_NB ly + 16 * id + (8 + Z.of_nat kk)) by lia. apply OKN. lia.
Qed.
Lemma hs_bounds : forall g, 4096 <= g -> g + 8 <= kHighMemEnd -> kLowShadowBeg <= shadow_addr g < kHighMemBeg.
Proof. geo.
intros g H1 H2. unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, kHighMemEnd in *.
pose proof (Z.div_le_mono 4096 g 8 ltac:(lia) H1) as X0. change (4096 / 8) with 512 in X0.
pose proof (Z.div_le_mono g (140737488355328 - 8) 8 ltac:(lia) ltac:(lia)) as Y. change ((140737488355328 - 8) / 8) with 17592186044415 in Y. lia.
Qed.
Lemma DH_iff : forall g, g mod 8 = 0 -> (DH (shadow_addr g) <-> MAP <= g < MAP + LEN).
Proof. geo.
intros g Hg. pose proof geom as (_ & _ & M3 & _ & M5 & _). unfold DH, shadow_addr.
apply Z.mod_divide in Hg as [c0 Hc0]; [|lia]. apply Z.mod_divide in M3 as [a Ha]; [|lia]. apply Z.mod_divide in M5 as [l Hl]; [|lia]. rewrite Hc0, Ha, Hl.
replace (a * 4096) with ((a * 512) * 8) by lia. replace (l * 4096) with ((l * 512) * 8) by lia. rewrite !Z_div_mult by lia. lia.
Qed.
Lemma ext_off_map : forall y, In y (st_chunks X) -> ck_beg y <> ck_beg k -> zdisjoint (ck_base B ly y, ck_extent y) (MAP, LEN).
Proof. geo.
intros y Hy Hne. pose proof KFACTS as (_ & _ & _ & _ & _ & _ & IN & _).
pose proof (chunk_facts B ly X rd y M Hy) as (G1 & G2 & _ & _ & _ & _ & G7 & G8 & GG).
destruct (ck_beg y) as [|oy|ry oy|c0 p0] eqn:Eby; try solve [destruct GG].
- exact (prim_vs_secmap B ly X rd y oy _ M Hy Eby IN).
- destruct GG as (-> & _ & Gbase & Gext & Gin & _). pose proof (secmaps_disjoint B ly X rd y k ry kPage r o M Hy Hk Eby Hb ltac:(rewrite Eby; exact Hne)) as DJ0.
unfold zdisjoint, MAP, LEN in *. cbn [fst snd] in *. pose proof (req_size_bounds (ck_req y) ltac:(lia)) as (_ & Q2 & _). unfold kPage in *. lia.
Qed.
Lemma fa_off_map : forall lo len, In (lo, len) (fa_poison_ranges ly X2) -> zdisjoint (lo, len) (MAP, LEN) /\ 4096 <= lo /\ lo + len <= ASAN_CEIL.
Proof. geo.
intros lo len Hin. pose proof KFACTS as (_ & _ & _ & _ & _ & _ & IN & _). destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2).
unfold fa_poison_ranges, reg in Hin. rewrite X2_regions, X2_chunks, E1 in Hin. apply in_app_iff in Hin as [Hin|Hin].
- apply in_flat_map in Hin as (c' & Hc' & Hin). apply zseq_In in Hc'. fold (reg X c') in Hin.
pose proof (region_in_prim ly c' LO ltac:(lia)) as (R1 & R2 & R3 & R4 & R5).
pose proof (wf_classes _ _ _ _ _ WF c' ltac:(lia)) as CL.
pose proof (wr_alloc _ _ _ _ _ _ CL) as A1. pose proof (wr_fa _ _ _ _ _ _ CL) as [A2 _]. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as A3.
pose proof (mapped_user_bound (as_universe B) 0 0 0 X c' WF ltac:(lia)) as MB. unfold kUserMapSize, EV_MAX, kFreeArrayMax in *.
pose proof (MAPX 0 _ eq_refl) as DJ0. unfold zdisjoint in DJ0 |- *. cbn [fst snd] in DJ0 |- *. pose proof HIGH as (H1 & H2 & _).
unfold fa_base, kFreeArrayOffset in Hin. unfold region_base in *.
destruct Hin as [EE|[EE|[]]]; injection EE as <- <-; unfold kHighMemBeg, kPrimResvSize in *; lia.
- apply in_flat_map in Hin as (y & Hy & Hin).
assert (Hy' : In y (st_chunks X)) by (rewrite E; apply in_app_iff in Hy as [Hy|Hy]; apply in_app_iff; [left; exact Hy | right; right; exact Hy]).
assert (Hne : ck_beg y <> ck_beg k) by (intros Ey; apply in_app_iff in Hy as [Hy|Hy]; [apply N1 | apply N2]; rewrite <- Ey; apply in_map; exact Hy).
pose proof (chunk_facts B ly X rd y M Hy') as (G1 & G2 & _ & _ & _ & _ & G7 & G8 & GG).
destruct (ck_beg y) as [|oy|ry oy|c0 p0] eqn:Eby; try solve [destruct Hin]. destruct Hin as [EE|[]]. injection EE as <- <-.
destruct GG as (-> & _ & Gbase & Gext & Gin & _).
pose proof (proj1 (Forall_forall _ _) (proj1 (am_placed _ _ _ _ M)) _ Gin) as (_ & [I1 I2] & I3). cbn [fst snd] in I1, I2, I3.
split; [|split; [exact I1 | exact I3]].
pose proof (secmaps_disjoint B ly X rd y k ry kPage r o M Hy' Hk Eby Hb ltac:(rewrite Eby; exact Hne)) as DJ0. unfold MAP, LEN. exact DJ0.
Qed.
Lemma in_rangesb_remove : forall g A Bq lo len, ~ (lo <= g < lo + len) -> in_rangesb g (A ++ (lo, len) :: Bq) = in_rangesb g (A ++ Bq).
Proof. geo.
intros g A Bq lo len Hn. induction A as [|[lo' len'] A IH]; cbn [app in_rangesb].
- replace ((lo <=? g) && (g <? lo + len)) with false; [reflexivity|]. symmetry. apply Bool.andb_false_iff.
destruct (Z_lt_le_dec g lo); [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia].
- rewrite IH. reflexivity.
Qed.
Lemma ashadow_X2 : forall g v, g mod 8 = 0 -> ashadow B ly X2 g = Some v ->
(g + 8 <= MAP \/ MAP + LEN <= g) /\ ashadow B ly X g = Some v /\ 4096 <= g < ASAN_CEIL.
Proof. geo.
intros g v Hg8 HS'. destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2). pose proof geom as (M1 & M2 & M3 & M4 & M5 & CB & CE).
apply Z.mod_divide in Hg8 as [c0 Hc0]; [|lia]. pose proof M3 as M3'. apply Z.mod_divide in M3' as [a0 Ha0]; [|lia].
assert (AL8 : forall lo, lo mod 4096 = 0 -> g < lo -> g + 8 <= lo) by (intros lo Hlo Hlt; apply Z.mod_divide in Hlo as [q Hq]; [|lia]; subst; nia).
assert (AL8' : forall hi, hi mod 8 = 0 -> g < hi -> g + 8 <= hi) by (intros hi Hhi Hlt; apply Z.mod_divide in Hhi as [q Hq]; [|lia]; subst; nia).
unfold ashadow in HS' |- *. rewrite X2_chunks, E1 in HS'. rewrite E. rewrite find_chunk_at_app in HS' |- *. cbn [find_chunk_at].
destruct (find_chunk_at B ly l1 g) as [y|] eqn:F1.
- apply find_chunk_at_In in F1 as [Hy Hgy].
assert (Hy' : In y (st_chunks X)) by (rewrite E; apply in_app_iff; left; exact Hy).
assert (Hne : ck_beg y <> ck_beg k) by (intros Ey; apply N1; rewrite <- Ey; apply in_map; exact Hy).
pose proof (ext_off_map y Hy' Hne) as DJ0. unfold zdisjoint in DJ0. cbn [fst snd] in DJ0.
pose proof (chunk_facts B ly X rd y M Hy') as (G1 & G2 & G3 & _). unfold in_app in G1.
split; [|split; [exact HS' | lia]].
destruct DJ0 as [D0|D0]; [left; apply AL8; [exact M3 | lia] | right; lia].
- destruct ((ck_base B ly k <=? g) && (g <? ck_base B ly k + ck_extent k)) eqn:TK.
+
exfalso. apply andb_prop in TK as [T1 T2]. apply Z.leb_le in T1. apply Z.ltb_lt in T2.
destruct (find_chunk_at B ly l2 g) as [y|] eqn:F2.
* apply find_chunk_at_In in F2 as [Hy Hgy]. assert (Hy' : In y (st_chunks X)) by (rewrite E; apply in_app_iff; right; right; exact Hy).
assert (Hne : ck_beg y <> ck_beg k) by (intros Ey; apply N2; rewrite <- Ey; apply in_map; exact Hy).
pose proof (ext_off_map y Hy' Hne) as DJ0. unfold zdisjoint in DJ0. cbn [fst snd] in DJ0. unfold kPage in *. lia.
* destruct (in_rangesb g (fa_poison_ranges ly X2)) eqn:R; [|discriminate]. apply in_rangesb_true in R as (lo & len & Hin & Hg).
pose proof (fa_off_map lo len Hin) as (DJ0 & _). unfold zdisjoint in DJ0. cbn [fst snd] in DJ0. unfold kPage in *. lia.
+ destruct (find_chunk_at B ly l2 g) as [y|] eqn:F2.
* apply find_chunk_at_In in F2 as [Hy Hgy]. assert (Hy' : In y (st_chunks X)) by (rewrite E; apply in_app_iff; right; right; exact Hy).
assert (Hne : ck_beg y <> ck_beg k) by (intros Ey; apply N2; rewrite <- Ey; apply in_map; exact Hy).
pose proof (ext_off_map y Hy' Hne) as DJ0. unfold zdisjoint in DJ0. cbn [fst snd] in DJ0.
pose proof (chunk_facts B ly X rd y M Hy') as (G1 & G2 & _). unfold in_app in G1.
split; [|split; [exact HS' | lia]].
destruct DJ0 as [D0|D0]; [left; apply AL8; [exact M3 | lia] | right; lia].
* destruct (in_rangesb g (fa_poison_ranges ly X2)) eqn:R; [|discriminate]. pose proof R as R'. apply in_rangesb_true in R as (lo & len & Hin & Hg).
pose proof (fa_off_map lo len Hin) as (DJ0 & I1 & I2). unfold zdisjoint in DJ0. cbn [fst snd] in DJ0.
assert (OFF : g + 8 <= MAP \/ MAP + LEN <= g) by (destruct DJ0 as [D0|D0]; [left; apply AL8; [exact M3 | lia] | right; lia]).
split; [exact OFF|]. split; [| ceil; unfold ASAN_CEIL, kHighMemEnd in *; lia].
destruct fa_poison' as (FP1 & FP2 & EF & EF2). rewrite EF. rewrite EF2 in R'. rewrite in_rangesb_remove by lia. rewrite R'. exact HS'.
Qed.
Lemma shadow' : shadow_ok B ly rd' X2.
Proof.
intros g v Hg8 HS'. destruct (ashadow_X2 g v Hg8 HS') as (OFF & HS & G1 & G2).
rewrite AGok; [exact (am_shadow B ly X rd M g v Hg8 HS)|]. apply ok_hshadow; [apply hs_bounds; ceil; unfold in_app, zone3, kHighMemBeg, ASAN_CEIL, kHighMemEnd in *; lia|].
intros HD. apply (DH_iff g Hg8) in HD. lia.
Qed.
Lemma zshadow' : zshadow_ok B ly rd'.
Proof.
pose proof (am_zshadow B ly X rd M) as ZS. unfold zshadow_ok in ZS |- *. apply Forall_forall. intros r0 Hr i0 Hi0.
pose proof (proj1 (Forall_forall _ _) ZS r0 Hr i0 Hi0) as Z0. unfold shadow_of_addr in Z0 |- *. change (SHADOW_OFF + fst r0 / 8) with (shadow_addr (fst r0)) in Z0 |- *.
rewrite AGok; [exact Z0|]. pose proof HIGH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & hS1 & hS2 & _ & _ & _ & _ & CE & _). pose proof geom as (M1 & M2 & _).
unfold zero_shadow_ranges in Hr. destruct Hr as [<-|Hr]; cbn [fst snd] in Hi0 |- *.
-
pose proof (lo_top _ LO) as (_ & _ & _ & T4 & T5 & _). unfold page_aligned in T5. apply Z.mod_divide in T5 as [s0 Hs0]; [|lia].
assert (E8 : shadow_addr (ly_stk_lo ly) + i0 = shadow_addr (ly_stk_lo ly + 8 * i0)).
{ unfold shadow_addr. rewrite Hs0. replace (s0 * 4096) with ((512 * s0) * 8) by lia. replace (512 * s0 * 8 + 8 * i0) with ((512 * s0 + i0) * 8) by lia. rewrite !Z_div_mult by lia. lia. }
rewrite E8. pose proof (Z.mul_div_le (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(lia)) as MD.
apply ok_hshadow; [apply hs_bounds; clear - hS1 hS2 Hi0 MD; unfold kHighMemBeg, kHighMemEnd in *; lia|].
intros HD. apply (DH_iff (ly_stk_lo ly + 8 * i0) ltac:(rewrite Hs0; replace (s0 * 4096 + 8 * i0) with ((512 * s0 + i0) * 8) by lia; apply Z_mod_mult)) in HD.
clear - HD CE M2 Hi0. lia.
-
rewrite (ts_zsh _ TB) in Hr. unfold Tfib_zero_shadow in Hr.
apply ok_imgsh; unfold shadow_addr, SHADOW_OFF, TFIB_IMG_LO, TFIB_IMG_END;
destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Hi0 |- *.
all: repeat match goal with |- context [?x0 / 8] => let v := eval vm_compute in (x0 / 8) in change (x0 / 8) with v end.
all: match type of Hi0 with context [?x0 / 8] => let v := eval vm_compute in (x0 / 8) in change (x0 / 8) with v in Hi0 end.
all: clear - Hi0; lia.
Qed.
Lemma vis_zone : forall (e : aexp) (len : Z), range_vis B ly rd (e, len) ->
((zdisjoint (aeval B ly e, len) (MAP, LEN) /\ 0 <= aeval B ly e /\ aeval B ly e + len <= 2 ^ 64) \/
((TFIB_IMG_LO <= aeval B ly e /\ aeval B ly e + len <= TFIB_IMG_END) \/ (kLowShadowBeg <= aeval B ly e /\ aeval B ly e + len <= kHighMemBeg))) ->
range_vis B ly rd' (e, len).
Proof.
intros e len V Z i0 Hii. cbn [fst snd] in *. pose proof geom as (M1 & _). ztri M1 ZM. unfold zone3 in M1. unfold zdisjoint in Z. cbn [fst snd] in Z.
ceil. unfold TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
apply VIS; [clear - Z Hii M1 CR; lia | exact (V i0 Hii)|]. unfold DM. clear - Z Hii ZM M1. lia.
Qed.
Lemma vis_prim : forall (e : aexp) (len : Z), range_vis B ly rd (e, len) ->
ly_prim ly <= aeval B ly e -> aeval B ly e + len <= ly_prim ly + kPrimResvSize -> range_vis B ly rd' (e, len).
Proof. intros e len V H1 H2. apply vis_zone; [exact V|]. left. pose proof (MAPX 0 _ eq_refl) as D0. pose proof HIGH as HI. unfold zdisjoint in D0 |- *. cbn [fst snd] in *. hnum. lia. Qed.
Lemma vis_T : forall (e : aexp) (len : Z), range_vis B ly rd (e, len) ->
T <= aeval B ly e -> aeval B ly e + len <= T + kThreadObjSize -> range_vis B ly rd' (e, len).
Proof. intros e len V H1 H2. apply vis_zone; [exact V|]. left. pose proof (MAPX 2 _ eq_refl) as D0. pose proof HIGH as HI. unfold zdisjoint in D0 |- *. cbn [fst snd] in *. hnum. lia. Qed.
Lemma junk' : Forall (range_vis B ly rd') (ajunk B ly X2).
Proof.
destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2). pose proof (am_junk B ly X rd M) as J. pose proof HIGH as HI.
pose proof ARR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). pose proof ARR' as (B1 & _).
pose proof (wf_secondary _ _ _ _ _ WF) as XS. destruct XS as [Snd Sac Sal Sres Sral].
unfold ajunk in J |- *. unfold quar_junk, cache_junk, cache, sec_junk in J |- *. rewrite all_batches', X2_cinit, X2_cache, X2_sec_arr, X2_sec_res, X2_chunks, E1. rewrite Hci, E in J.
fold arr in J.
apply Forall_cons_iff in J as [J1 J]. apply Forall_cons_iff in J as [J2 J].
apply Forall_app in J as [J3 J]. apply Forall_app in J as [J4 J]. apply Forall_app in J as [J5 J]. apply Forall_app in J as [J6 J]. apply Forall_app in J as [J7 J]. apply Forall_app in J as [J8 J].
pose proof (lo_space_in _ LO) as [SP1 SP2].
apply Forall_cons; [apply (vis_prim _ _ J1); cbn; unfold kRegionInfoOff, kSpaceSize, kPrimResvSize in *; lia|].
apply Forall_cons; [apply (vis_prim _ _ J2); cbn; unfold kRegionInfoOff, kSpaceSize, kPrimResvSize in *; lia|].
apply Forall_app. split.
{ apply Forall_forall. intros [e len] Hin. apply (vis_prim _ _ (proj1 (Forall_forall _ _) J3 _ Hin)); apply in_flat_map in Hin as (c' & Hc' & Hin); apply zseq_In in Hc'; unfold region_junk in Hin;
destruct Hin as [EE|[EE|[EE|[]]]]; injection EE as <- <-; cbn; unfold kRegionInfoOff, kSpaceSize, kPrimResvSize in *; lia. }
apply Forall_app. split.
{ apply Forall_forall. intros [e len] Hin. pose proof (proj1 (Forall_forall _ _) J4 _ Hin) as V. apply in_flat_map in Hin as (c' & Hc' & Hin). apply zseq_In in Hc'.
destruct Hin as [EE|[]]. pose proof (wf_classes _ _ _ _ _ WF c' ltac:(lia)) as CL. pose proof (wr_cache _ _ _ _ _ _ CL) as WC. rewrite Hci in WC. destruct WC as [PM PL].
pose proof (class_ok c' ltac:(lia)) as (_ & _ & _ & K4 & _).
injection EE as <- <-. apply (vis_T _ _ V); cbn; unfold t_cache, kThreadObjSize in *; lia. }
apply Forall_app. split.
{
rewrite flat_map_app in J5. cbn [flat_map] in J5. apply Forall_app in J5 as [J5a J5]. apply Forall_app in J5 as [_ J5b].
rewrite flat_map_app. apply Forall_app.
assert (CJ : forall l (N : ~ In (ck_beg k) (map ck_beg l)) (SUB : forall y, In y l -> In y (st_chunks X)),
Forall (range_vis B ly rd) (flat_map chunk_junk l) -> Forall (range_vis B ly rd') (flat_map chunk_junk l)).
{ intros l N SUB JJ. apply Forall_forall. intros [e len] Hin. pose proof (proj1 (Forall_forall _ _) JJ _ Hin) as V. apply in_flat_map in Hin as (y & Hy & Hin).
assert (Hne : ck_beg y <> ck_beg k) by (intros Ey; apply N; rewrite <- Ey; apply in_map; exact Hy).
pose proof (ext_off_map y (SUB y Hy) Hne) as DJ0. pose proof (chunk_facts B ly X rd y M (SUB y Hy)) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof (req_size_bounds (ck_req y) ltac:(lia)) as (_ & Q2 & _).
apply (vis_zone _ _ V). left. unfold zdisjoint in DJ0 |- *. cbn [fst snd] in DJ0 |- *.
unfold chunk_junk in Hin. rewrite !in_app_iff in Hin. unfold kChunkHeaderSize in Hin.
destruct Hin as [Hin|[[EE|[]]|[Hin|[EE|[]]]]]; [destruct (ck_rz y =? 16); [destruct Hin | destruct Hin as [EE|[]]] | | destruct (ck_state y); [destruct Hin | destruct Hin as [EE|[]]] |];
injection EE as <- <-; rewrite ?(EA y), ?EA0 by exact (SUB y Hy); unfold ck_n; hnum; lia. }
split; [apply CJ; [exact N1 | intros y Hy; rewrite E; apply in_app_iff; left; exact Hy | exact J5a] | apply CJ; [exact N2 | intros y Hy; rewrite E; apply in_app_iff; right; right; exact Hy | exact J5b]]. }
apply Forall_app. split.
{
apply Forall_cons_iff in J6 as [J6a J6]. apply Forall_cons_iff in J6 as [J6b J6]. apply Forall_cons_iff in J6 as [J6c J6].
apply Forall_cons; [apply (vis_zone _ _ J6a); right; left; cbn; unfold o_sec_sorted; clear - HI; hnum; lia|].
apply Forall_cons; [apply (vis_zone _ _ J6b); right; left; cbn; unfold o_sec_stats, o_sec_mutex; clear - HI; hnum; lia|].
apply Forall_cons.
{ intros i0 Hi0. cbn [fst snd aeval] in Hi0 |- *. rewrite B1 in Hi0 |- *.
pose proof (MAPX 1 _ eq_refl) as D0. unfold zdisjoint in D0. cbn [fst snd] in D0.
apply VIS; [unfold kPtrArrayResv, kPtrArrayEntriesPerCommit, nA, arr in *; hnum; lia | |].
- destruct (Z_lt_le_dec i0 8) as [LOW|HIGH'].
+
assert (OC : cell_holds B ly rd (c8 (AQ (8 * Z.of_nat (length arr - 1))) (ASec lastr 0))).
{ apply OLD. unfold acells. rewrite !in_app_iff. do 3 right. left. unfold sec_cells. do 3 right. apply in_app_iff. left.
apply in_map_iff. exists ((length arr - 1)%nat, lastr). split; [reflexivity|]. apply in_combine_seq0. exact A6. }
specialize (OC (Z.to_nat i0) ltac:(cbn; lia)). cbn [c_at c_w c8 aeval] in OC. rewrite Z2Nat.id in OC by lia.
replace (ly_Q ly + 8 * Z.of_nat (length arr - 1)%nat + i0) with (ly_Q ly + 8 * Z.of_nat (length arr - 1) + i0) by lia. rewrite OC. discriminate.
+ specialize (J6c (i0 - 8) ltac:(cbn; unfold nA in *; lia)). cbn [fst snd aeval] in J6c.
replace (ly_Q ly + 8 * Z.of_nat (length arr) + (i0 - 8)) with (ly_Q ly + 8 * Z.of_nat (length arr - 1) + i0) in J6c by lia. exact J6c.
- unfold DM. unfold kPtrArrayResv, kPtrArrayEntriesPerCommit, nA, arr in *. lia. }
rewrite flat_map_app in J6 |- *. cbn [flat_map] in J6. rewrite Hb in J6. cbn [app] in J6.
assert (PJ : forall l (N : ~ In (ck_beg k) (map ck_beg l)) (SUB : forall y, In y l -> In y (st_chunks X)),
Forall (range_vis B ly rd) (flat_map (fun y => match ck_beg y with PSec r' _ => [(ASec r' 32, kPage - 32)] | _ => [] end) l) ->
Forall (range_vis B ly rd') (flat_map (fun y => match ck_beg y with PSec r' _ => [(ASec r' 32, kPage - 32)] | _ => [] end) l)).
{ intros l N SUB JJ. apply Forall_forall. intros [e len] Hin. pose proof (proj1 (Forall_forall _ _) JJ _ Hin) as V. apply in_flat_map in Hin as (y & Hy & Hin).
assert (Hne : ck_beg y <> ck_beg k) by (intros Ey; apply N; rewrite <- Ey; apply in_map; exact Hy).
destruct (ck_beg y) as [|oy|ry oy|c0 p0] eqn:Eby; try solve [destruct Hin]. destruct Hin as [EE|[]]. injection EE as <- <-.
pose proof (secmaps_disjoint B ly X rd y k ry oy r o M (SUB y Hy) Hk Eby Hb ltac:(rewrite Eby; exact Hne)) as DJ0.
pose proof (chunk_facts B ly X rd y M (SUB y Hy)) as (_ & _ & _ & _ & _ & _ & G7 & _).
apply (vis_zone _ _ V). left. unfold zdisjoint, MAP, LEN in DJ0 |- *. cbn [fst snd aeval] in DJ0 |- *.
assert (8192 <= sec_map_size (ck_req y)).
{ pose proof (chunk_facts B ly X rd y M (SUB y Hy)) as (_ & _ & _ & _ & _ & _ & _ & _ & GG). rewrite Eby in GG. destruct GG as (_ & FP & _).
unfold sec_map_size, needed_size. rewrite FP. unfold from_primary in FP. apply Z.leb_gt in FP.
pose proof (round_up_ge (needed_primary (ck_req y) + rz_size (ck_req y)) kPage ltac:(unfold kPage; lia)) as [R1 _].
pose proof (rz_size_bounds (ck_req y)) as [RZ _]. unfold kMaxSize, kPage in *. lia. }
pose proof (chunk_facts B ly X rd y M (SUB y Hy)) as (_ & _ & _ & _ & _ & _ & _ & _ & GG). rewrite Eby in GG. destruct GG as (_ & _ & _ & _ & Gin & _).
pose proof (proj1 (Forall_forall _ _) (proj1 (am_placed _ _ _ _ M)) _ Gin) as (_ & [I1 I2] & I3). cbn [fst snd] in I1, I2, I3.
unfold kPage. clear - DJ0 H I1 I3 G7. hnum; lia. }
apply Forall_app in J6 as [J6l J6]. apply Forall_cons_iff in J6 as [_ J6r].
apply Forall_app. split; [apply PJ; [exact N1 | intros y Hy; rewrite E; apply in_app_iff; left; exact Hy | exact J6l] | apply PJ; [exact N2 | intros y Hy; rewrite E; apply in_app_iff; right; right; exact Hy | exact J6r]]. }
apply Forall_app. split.
{
apply Forall_forall. intros [e len] Hin. pose proof (proj1 (Forall_forall _ _) J7 _ Hin) as V. apply in_flat_map in Hin as (b2 & Hb2 & Hin). destruct Hin as [EE|[]]. injection EE as <- <-.
destruct (AFf3.batch_geom B ly X rd M b2 Hb2) as (xb & Eb & Pb & _ & Ub & [AU MU] & _) || idtac.
pose proof (region_in_prim ly kBatchClass LO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & _).
pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
assert (INB : In (b_self b2 - region_off kBatchClass) (batch_offs X kBatchClass)) by (rewrite batch_offs_24; apply in_map_iff; exists b2; auto).
pose proof (proj1 (Forall_forall _ _) (wr_elems _ _ _ _ _ _ CL) _ ltac:(rewrite !in_app_iff; right; right; right; exact INB)) as [Q1 Q2].
pose proof (wr_alloc _ _ _ _ _ _ CL) as AL'. pose proof (mapped_user_bound (as_universe B) 0 0 0 X kBatchClass WF ltac:(unfold kBatchClass; lia)) as MB.
pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wf_quarantine _ _ _ _ _ WF)) b2 Hb2) as [L1 L2]. unfold kBatchSlots in L2.
unfold kUserMapSize, EV_MAX, region_base in *. rewrite region_off_eq in * by (unfold kBatchClass; lia). unfold kBatchClass, kBatchBytes in *.
apply (vis_prim _ _ V); cbn; lia. }
apply Forall_app. split.
{ unfold thread_junk in J8 |- *. apply Forall_cons_iff in J8 as [T1 J8]. apply Forall_cons_iff in J8 as [T2 J8]. apply Forall_cons_iff in J8 as [T3 J8]. apply Forall_cons_iff in J8 as [T4 _].
repeat (apply Forall_cons; [first [apply (vis_T _ _ T1) | apply (vis_T _ _ T2) | apply (vis_T _ _ T3) | apply (vis_T _ _ T4)]; cbn; unfold t_cache, t_cache_stats, t_stats, t_unwinding, kThreadObjSize; lia|]).
apply Forall_nil. }
apply Forall_app. split.
{ apply Forall_cons_iff in J as [K1 J]. apply Forall_cons_iff in J as [K2 J]. apply Forall_cons_iff in J as [K3 J]. apply Forall_cons_iff in J as [K4 J].
pose proof (aso_cells _ (am_syms _ _ _ _ M)) as AC.
repeat (apply Forall_cons; [first [apply (vis_zone _ _ K1) | apply (vis_zone _ _ K2) | apply (vis_zone _ _ K3) | apply (vis_zone _ _ K4)]; right; left; cbn; unfold d_nuniq in *; tbnum; clear; lia|]).
apply Forall_nil. }
apply Forall_forall. intros [e len] Hin. pose proof (proj1 (Forall_forall _ _) (proj2 (proj2 (proj2 (proj2 (proj1 (Forall_app _ _ _) J))))) (e, len)) as V || pose proof I as V.
clear V. do 4 (apply Forall_cons_iff in J as [_ J]). pose proof (proj1 (Forall_forall _ _) J _ Hin) as V.
destruct (ts_junk _ TB ly (e, len) Hin) as (z & Ez & Z1 & Z2). cbn [fst snd] in Ez, Z1, Z2. subst e.
apply (vis_zone _ _ V). right; left. cbn. clear - Z1 Z2. unfold TFIB_IMG_LO, TFIB_IMG_END. lia.
Qed.
Lemma areas' : Forall (range_vis B ly rd') (aareas X2).
Proof.
destruct aareas_split as (A1 & A2 & EA1 & EA2). pose proof (am_areas B ly X rd M) as A. rewrite EA1 in A. rewrite EA2.
apply Forall_app in A as [A1v A]. apply Forall_cons_iff in A as [_ A2v].
assert (GEN : forall el, In el (aareas X2) -> range_vis B ly rd el -> range_vis B ly rd' el).
{ intros [e len] Hin V. pose proof HIGH as HI. pose proof (lo_space_in _ LO) as [SP1 SP2]. destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2).
unfold aareas, reg in Hin. rewrite X2_regions, X2_sec_res, X2_chunks, E1 in Hin. rewrite !in_app_iff in Hin.
destruct Hin as [Hin|[[EE|[]]|[Hin|Hin]]].
- apply in_flat_map in Hin as (c' & Hc' & Hin). apply zseq_In in Hc'. fold (reg X c') in Hin. pose proof (region_in_prim ly c' LO ltac:(lia)) as (R1 & R2 & _).
pose proof (wf_classes _ _ _ _ _ WF c' ltac:(lia)) as CL. pose proof (wr_fa _ _ _ _ _ _ CL) as [F1 _]. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as F2.
pose proof (mapped_user_bound (as_universe B) 0 0 0 X c' WF ltac:(lia)) as MB. unfold region_base in *.
destruct Hin as [EE|[EE|[]]]; injection EE as <- <-; apply (vis_prim _ _ V); cbn; unfold kUserMapSize, EV_MAX, kFreeArrayOffset, kFreeArrayMax in *; lia.
- injection EE as <- <-. pose proof (wf_secondary _ _ _ _ _ WF) as XS. destruct XS as [_ _ _ Sres Sral]. unfold kPtrArrayEntriesPerCommit in Sres.
apply (vis_zone _ _ V). left. pose proof (MAPX 1 _ eq_refl) as D0. unfold zdisjoint in D0 |- *. cbn [fst snd aeval] in *. unfold kPtrArrayResv in *. hnum; lia.
- apply in_flat_map in Hin as (y & Hy & Hin).
assert (Hy' : In y (st_chunks X)) by (rewrite E; apply in_app_iff in Hy as [Hy|Hy]; apply in_app_iff; [left; exact Hy | right; right; exact Hy]).
assert (Hne : ck_beg y <> ck_beg k) by (intros Ey; apply in_app_iff in Hy as [Hy|Hy]; [apply N1 | apply N2]; rewrite <- Ey; apply in_map; exact Hy).
destruct (ck_beg y) as [|oy|ry oy|c0 p0] eqn:Eby; try solve [destruct Hin]. destruct Hin as [EE|[]]. injection EE as <- <-.
pose proof (secmaps_disjoint B ly X rd y k ry oy r o M Hy' Hk Eby Hb ltac:(rewrite Eby; exact Hne)) as DJ0.
pose proof (chunk_facts B ly X rd y M Hy') as (_ & _ & _ & _ & _ & _ & _ & _ & GG). rewrite Eby in GG. destruct GG as (_ & _ & _ & _ & Gin & _).
pose proof (proj1 (Forall_forall _ _) (proj1 (am_placed _ _ _ _ M)) _ Gin) as (_ & [I1 I2] & I3). cbn [fst snd] in I1, I2, I3.
apply (vis_zone _ _ V). left. unfold MAP, LEN, zdisjoint in *. cbn [aeval fst snd] in *. rewrite Z.add_0_r. clear - DJ0 I1 I3. hnum. lia.
- pose proof (MAPX 3 _ eq_refl) as D3. pose proof (MAPX 4 _ eq_refl) as D4. pose proof (MAPX 5 _ eq_refl) as D5. pose proof (MAPX 2 _ eq_refl) as D2. pose proof (MAPX 0 _ eq_refl) as D0.
unfold zdisjoint in D0, D2, D3, D4, D5. cbn [fst snd] in D0, D2, D3, D4, D5.
destruct Hin as [EE|[EE|[EE|[EE|[EE|[EE|[]]]]]]]; injection EE as <- <-; apply (vis_zone _ _ V); cbn [aeval fst snd]; unfold zdisjoint; cbn [fst snd];
[left; hnum; lia | left; hnum; lia | left; hnum; lia | left; hnum; lia | left; unfold kRegionInfoOff, kSpaceSize, kPrimResvSize in *; hnum; lia | right].
right. unfold shadow_addr, kFakeFramesOff, kFakeStackSize, SHADOW_OFF. pose proof HI as (_ & _ & _ & _ & _ & _ & hF1 & hF2 & _). clear - hF1 hF2. hnum.
pose proof (Z.div_pos (ly_F ly + (4096 + 32768)) 8 ltac:(lia) ltac:(lia)) as Y0.
assert (Y' : (ly_F ly + (4096 + 32768)) / 8 <= (140737479966720 - 11534336) / 8) by (apply Z.div_le_mono; lia). change ((140737479966720 - 11534336) / 8) with 17592183554048 in Y'.
change ((11571200 - (4096 + 32768)) / 8) with 1441792. lia. }
apply Forall_forall. intros el Hel. apply GEN; [rewrite EA2; exact Hel|]. apply in_app_iff in Hel as [Hel|Hel]; [exact (proj1 (Forall_forall _ _) A1v el Hel) | exact (proj1 (Forall_forall _ _) A2v el Hel)].
Qed.
Lemma client' : Forall (range_vis B ly rd') (aclient X2).
Proof.
destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2). pose proof (am_client B ly X rd M) as A. pose proof HIGH as HI.
unfold aclient in A |- *. rewrite frames', X2_chunks, E1. rewrite E in A. rewrite flat_map_app in A |- *. cbn [flat_map] in A. unfold chunk_user at 2 in A. rewrite Hst in A. cbn [app] in A.
apply Forall_app in A as [AU AF]. apply Forall_app. split.
- apply Forall_forall. intros [e len] Hin. pose proof (proj1 (Forall_forall _ _) AU _ Hin) as V. rewrite <- flat_map_app in Hin. apply in_flat_map in Hin as (y & Hy & Hin).
assert (Hy' : In y (st_chunks X)) by (rewrite E; apply in_app_iff in Hy as [Hy|Hy]; apply in_app_iff; [left; exact Hy | right; right; exact Hy]).
assert (Hne : ck_beg y <> ck_beg k) by (intros Ey; apply in_app_iff in Hy as [Hy|Hy]; [apply N1 | apply N2]; rewrite <- Ey; apply in_map; exact Hy).
unfold chunk_user in Hin. destruct (ck_state y); [|destruct Hin]. destruct Hin as [EE|[]]. injection EE as <- <-.
pose proof (ext_off_map y Hy' Hne) as DJ0. pose proof (chunk_facts B ly X rd y M Hy') as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof (req_size_bounds (ck_req y) ltac:(lia)) as (_ & Q2 & Q3). apply (vis_zone _ _ V). left.
unfold zdisjoint in DJ0 |- *. cbn [fst snd] in DJ0 |- *. change (aeval B ly (sptr_exp (ck_user y))) with (sptr_addr B ly (ck_user y)). rewrite G4. unfold ck_n. hnum; lia.
- apply Forall_forall. intros [e len] Hin. pose proof (proj1 (Forall_forall _ _) AF _ Hin) as V. pose proof (MAPX 3 _ eq_refl) as D3. unfold zdisjoint in D3. cbn [fst snd] in D3.
apply in_app_iff in Hin as [Hin|Hin]; apply in_map_iff in Hin as ([cid pos] & EE & Hcp); injection EE as <- <-; cbn [fst snd] in *;
pose proof (proj1 (Forall_forall _ _) (wfs_live _ (wf_fakestack _ _ _ _ _ WF)) (cid, pos) Hcp) as [C1 C2]; cbn [fst snd] in C1, C2;
pose proof (frame_off_bounds cid pos C1 C2) as (FB1 & FB2 & FB3 & FB4 & FB5 & FB6); apply (vis_zone _ _ V).
+ left. unfold zdisjoint. cbn [aeval fst snd]. pose proof HI as (_ & _ & _ & _ & _ & _ & hF1 & hF2 & _). clear - D3 hF1 hF2 FB1 FB2 FB6 C1. unfold kFakeStackSize, kFakeFramesOff in *. hnum; lia.
+ right; right. cbn [aeval fst snd]. pose proof HI as (_ & _ & _ & _ & _ & _ & hF1 & hF2 & _). clear - hF1 hF2 FB1 FB2 FB4 FB6 C1. unfold shadow_addr, SHADOW_OFF, kFakeStackSize, kFakeFramesOff in *. hnum.
pose proof (Z.div_pos (ly_F ly + fs_frame_off cid pos) 8 ltac:(lia) ltac:(lia)) as Y0.
assert (Y' : (ly_F ly + fs_frame_off cid pos) / 8 <= (140737479966720 - fs_frame_bytes cid) / 8) by (apply Z.div_le_mono; lia). lia.
Qed.
Lemma pairwise_remove_mid' : forall {Y} (R : Y -> Y -> Prop) l1 x l2, pairwise R (l1 ++ x :: l2) -> pairwise R (l1 ++ l2).
Proof. geo.
intros Y R l1 x l2. induction l1 as [|y t IH]; cbn [app pairwise].
- intros [_ P]. exact P.
- intros [F P]. split; [| exact (IH P)]. apply Forall_forall. intros z Hz. apply (proj1 (Forall_forall _ _) F z).
apply in_app_iff in Hz as [Hz|Hz]; apply in_app_iff; [left | right; right]; exact Hz.
Qed.
Lemma placed' : sec_placed ly X2.
Proof. geo.
destruct (am_placed B ly X rd M) as [PF PD]. destruct sec_extents_split as (E1 & E2 & EX & EX2). split.
- apply Forall_forall. intros e He. apply (proj1 (Forall_forall _ _) PF). apply sec_extents_sub. exact He.
- rewrite EX2. rewrite EX in PD. rewrite <- app_assoc in PD |- *. exact (pairwise_remove_mid' _ _ _ _ PD).
Qed.
Theorem rs_fin_ARm : ARm B ly X2 rd'.
Proof.
constructor.
- exact WS2.
- exact (am_universe B ly X rd M).
- exact (am_syms B ly X rd M).
- exact LO.
- exact placed'.
- exact CONST'.
- exact (am_const_owned B ly X rd M).
- exact cells_all.
- exact fa'.
- exact flags'.
- exact depot'.
- exact shadow'.
- exact zshadow'.
- exact junk'.
- exact areas'.
- exact client'.
- pose proof (am_zero B ly X rd M) as ZR. apply Forall_forall. intros r0 Hr i0 Hi0. rewrite AGok; [exact (proj1 (Forall_forall _ _) ZR r0 Hr i0 Hi0)|].
pose proof (aso_cells _ (am_syms _ _ _ _ M)) as AC. pose proof (aso_ialloc _ (am_syms _ _ _ _ M)) as [I1 I2].
pose proof (ts_ial_lo _ TB) as EL. pose proof (ts_ial_hi _ TB) as EH. pose proof (ts_ial_w _ TB) as EW.
apply ok_low; [| unfold DI; rewrite (ts_inst _ TB)];
unfold ialloc_zero in Hr; destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in Hi0 |- *; rewrite ?EL, ?EH, ?EW in *; unfold kLowMemEnd, kHighShadowBeg, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W, TFIB_INST, TFIB_IMG_LO, TFIB_IMG_END in *; lia.
- exact (am_tsd B ly X rd M).
- exact (am_static_img B ly X rd M).
Qed.
Lemma asecA_X2 : forall A, asecA ly X A -> asecA ly X2 (YFfn.A_drop (MAP, MAP + LEN) A).
Proof. geo.
intros A H e He. destruct (H e (sec_extents_sub e He)) as [HA HH]. split; apply YFfn.A_drop_In; (split; [assumption|]).
2:{
intros EQ. exfalso. pose proof (f_equal fst EQ) as E1. unfold shull in E1. cbn [fst snd] in E1. unfold shadow_addr in E1. pose proof geom as (G1 & _ & _ & G4 & _).
pose proof (proj1 (Forall_forall _ _) (proj1 (am_placed B ly X rd M)) _ (sec_extents_sub e He)) as (_ & [I1 I2] & I3). cbn [fst snd] in I1, I2, I3.
pose proof (proj1 (Forall_forall _ _) (YG08.sec_extents_sizes64 _ ly X (am_wf B ly X rd M)) _ (sec_extents_sub e He)) as SZ. cbn beta in SZ.
assert (D1 : fst e / 8 <= ASAN_CEIL / 8) by (apply Z.div_le_mono; [lia|]; unfold ASAN_CEIL; clear - I3 SZ; lia).
assert (D2 : 4096 * ((SHADOW_OFF + fst e / 8) / 4096) <= SHADOW_OFF + fst e / 8) by (apply Z.mul_div_le; lia).
assert (D3 : ASAN_CEIL / 8 <= 140737479966720 / 8) by (apply Z.div_le_mono; [lia|]; ceil; lia). change (140737479966720 / 8) with 17592184995840 in D3.
clear - E1 G1 G4 D1 D2 D3 I1. ceil; unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, SHADOW_OFF, kHighMemBeg, ASAN_CEIL in *.
pose proof (Z.div_pos (fst e) 8 ltac:(lia) ltac:(lia)). lia. }
destruct sec_extents_split as (E1 & E2 & EX & EX2). destruct (am_placed B ly X rd M) as [PF PD]. rewrite EX in PD. rewrite EX2 in He.
intros EQ. assert (NE : e <> (MAP, LEN)).
{ intros ->. assert (PD' : pairwise zdisjoint (E1 ++ (MAP, LEN) :: (E2 ++ static_extents ly))) by (rewrite <- app_assoc in PD; exact PD). clear PD.
apply in_app_iff in He as [He|He].
- pose proof (pairwise_In zdisjoint _ (MAP, LEN) (MAP, LEN) E1 ((MAP, LEN) :: E2 ++ static_extents ly) eq_refl PD' He ltac:(left; reflexivity)) as DD.
unfold zdisjoint in DD. cbn [fst snd] in DD. pose proof geom as (_ & _ & _ & L4 & _). lia.
- assert (PD2 : pairwise zdisjoint ((MAP, LEN) :: E2 ++ static_extents ly)).
{ clear - PD'. induction E1 as [|z t IH]; [exact PD' | exact (IH (proj2 PD'))]. }
destruct PD2 as [F _]. pose proof (proj1 (Forall_forall _ _) F (MAP, LEN) ltac:(apply in_app_iff; left; exact He)) as DD.
unfold zdisjoint in DD. cbn [fst snd] in DD. pose proof geom as (_ & _ & _ & L4 & _). lia. }
apply NE. destruct e as [m l]. cbn [fst snd] in EQ. injection EQ as E1' E2'. subst m. f_equal. lia.
Qed.
Lemma D_owned : forall a, 0 <= a -> D a -> aowned B ly X a \/ DS a.
Proof. geo.
pose proof geom as (M1 & M2 & M3 & M4 & M5 & _). pose proof HIGH as HI. pose proof KFACTS as (_ & _ & _ & _ & _ & _ & IN & _).
pose proof ARR as (A1 & A2 & A3 & A4 & A5 & _).
intros a Ha0 HD. destruct HD as [Y|[Y|[Y|[Y|[Y|[Y|Y]]]]]]; unfold DI, DJ, DQ, DL, DH, DM in Y.
- right. exact Y.
- left. eapply (own_area B ly X rd (as_inst B, 3632)); [exact M | cbn; tauto | cbn; lia].
- left. eapply (own_core B ly X rd (T, kThreadObjSize) a M); [unfold core_extents; cbn; tauto|]. cbn [fst snd]. unfold DJ, t_stats, kThreadObjSize in *. lia.
- left. eapply (own_core B ly X rd (ly_Q ly, kPtrArrayResv) a M); [unfold core_extents; cbn; tauto|]. cbn [fst snd]. unfold DQ, qi, idx, nA, kPtrArrayResv in *. lia.
- left. destruct Y as [Ho Y]. destruct LST as (y2 & Hy2 & Ey2 & CI2 & L1 & L2 & L3 & SZ2 & _).
apply (own_meta B ly X rd y2 a M Hy2). pose proof (chunk_facts B ly X rd y2 M Hy2) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG). rewrite Ey2 in GG |- *.
destruct GG as (_ & _ & Gbase & _). fold lst in Gbase. unfold kPage in *. lia.
-
left. pose proof M3 as M3'. apply Z.mod_divide in M3' as [a0 Hua]; [|lia].
unfold shadow_addr in Y. rewrite Hua in Y. replace (a0 * 4096) with ((a0 * 512) * 8) in Y by lia. rewrite Z_div_mult in Y by lia.
replace a with (shadow_addr ((a0 * 512 + (a - (SHADOW_OFF + a0 * 512))) * 8)).
2:{ unfold shadow_addr. rewrite Z_div_mult by lia. lia. }
eapply own_shadow_sec; [exact M | exact IN |]. pose proof (Z.div_le_upper_bound LEN 8). pose proof (Z.mul_div_le LEN 8 ltac:(lia)). nia.
-
left. eapply own_ext; [exact M | right; apply Exists_exists; exists (MAP, LEN); split; [exact IN | unfold in_zr; cbn; lia] | |].
+ intros y Hy Hsy [R1 R2].
destruct (sptr_eqb (ck_beg y) (ck_beg k)) eqn:EQB.
* apply sptr_eqb_spec in EQB. destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2). rewrite E in Hy.
apply in_app_iff in Hy as [Hy|[<-|Hy]]; [apply N1; rewrite <- EQB; apply in_map; exact Hy | rewrite Hst in Hsy; discriminate | apply N2; rewrite <- EQB; apply in_map; exact Hy].
* assert (Hne : ck_beg y <> ck_beg k) by (intros EE; apply sptr_eqb_spec in EE; congruence).
pose proof (ext_off_map y Hy Hne) as DD. pose proof (chunk_facts B ly X rd y M Hy) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
unfold zdisjoint in DD. cbn [fst snd] in DD. lia.
+ pose proof (MAPX 3 _ eq_refl) as DD. unfold zdisjoint in DD. cbn [fst snd] in DD. unfold kFakeStackSize, kFakeFramesOff in *. lia.
Qed.
Lemma aowned_X2 : forall a, aowned B ly X2 a -> aowned B ly X a.
Proof. geo.
destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2).
assert (CB : forall a, aclient_byte B ly X2 a <-> aclient_byte B ly X a).
{ intros a. unfold aclient_byte. rewrite frames', X2_chunks, E1, E. split; intros [(y & Hy & Hsy & Hr)|H2].
- left. exists y. split; [|split; [exact Hsy | exact Hr]]. apply in_app_iff in Hy as [Hy|Hy]; apply in_app_iff; [left; exact Hy | right; right; exact Hy].
- right. exact H2.
- left. exists y. split; [|split; [exact Hsy | exact Hr]]. apply in_app_iff in Hy as [Hy|[<-|Hy]]; [apply in_app_iff; left; exact Hy | rewrite Hst in Hsy; discriminate | apply in_app_iff; right; exact Hy].
- right. exact H2. }
intros a [OW NC]. split; [|rewrite <- CB; exact NC].
destruct OW as [O|[O|[O|[O|O]]]]; [left; exact O | right; left; exact O | right; right; left; exact O | |].
- right; right; right; left. apply Exists_exists in O as (e & He & Ha). apply Exists_exists. exists e. split; [exact (sec_extents_sub e He) | exact Ha].
- right; right; right; right. apply Exists_exists in O as (e & He & Ha). apply Exists_exists. exists e. split; [|exact Ha].
rewrite !in_app_iff in He |- *. destruct He as [He|[He|He]]; [left; exact He | right; left; exact (sec_extents_sub e He) | right; right; exact He].
Qed.
Lemma aclient_byte_X2 : forall a, aclient_byte B ly X2 a <-> aclient_byte B ly X a.
Proof. geo.
destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2). intros a. unfold aclient_byte. rewrite frames', X2_chunks, E1, E. split; intros [(y & Hy & Hsy & Hr)|H2].
- left. exists y. split; [|split; [exact Hsy | exact Hr]]. apply in_app_iff in Hy as [Hy|Hy]; apply in_app_iff; [left; exact Hy | right; right; exact Hy].
- right. exact H2.
- left. exists y. split; [|split; [exact Hsy | exact Hr]]. apply in_app_iff in Hy as [Hy|[<-|Hy]]; [apply in_app_iff; left; exact Hy | rewrite Hst in Hsy; discriminate | apply in_app_iff; right; exact Hy].
- right. exact H2.
Qed.
Lemma ahs_X2 : forall (Hh : word -> bool) (m m' : word -> option byte),
ahs B ly X Hh m ->
(forall a, in_band_rw a -> ~ D a -> m' (w64 a) = m (w64 a)) ->
(forall a, DH a -> m' (w64 a) = Some (Z_to_bv 8 0)) ->
ahs B ly X2 Hh m'.
Proof. geo.
intros Hh m m' [HA HZ] EQ ZE. pose proof HIGH as HI. pose proof geom as GE. zget HI (ly_T ly) kThreadObjSize ZT. zget HI (ly_Q ly) kPtrArrayResv ZQ. ztri (proj1 GE) ZM.
assert (BAND : forall a, in_band_rw a -> D a -> DH a).
{ intros a Ha HD. destruct LST as (y2 & _ & _ & _ & L1 & _ & _ & SZ2 & _). ztri L1 ZL. unfold in_band_rw, kLowShadowEnd in Ha.
apply D_cases in HD as [Y|[[Y _]|[[Y _]|[[Y _]|[[Y _]|[[_ Y]|[Y _]]]]]]]; try exact Y; exfalso;
[clear - Ha Y HI | clear - Ha Y | clear - Ha Y ZT | clear - Ha Y ZQ | clear - Ha Y ZL SZ2 | clear - Ha Y ZM]; hnum; lia. }
split.
- intros a Ha NC HH. unfold YG0d.w64, YG0n.w64 in *. assert (Hd : DH a \/ ~ DH a) by (unfold DH; lia). destruct Hd as [Hd|Nd].
+ rewrite (ZE a Hd). discriminate.
+ rewrite (EQ a Ha ltac:(intros HD; exact (Nd (BAND a Ha HD)))). apply (HA a Ha); [|exact HH]. intros C. apply NC. apply (proj2 (aclient_byte_X2 a)). exact C.
- intros g Hg HAPP HF. unfold YG0d.w64, YG0n.w64 in *. assert (Hm : (MAP <= g < MAP + LEN) \/ ~ (MAP <= g < MAP + LEN)) by lia. destruct Hm as [Hin|Hout].
+ apply ZE. apply (proj2 (DH_iff g Hg)). exact Hin.
+ assert (HF0 : hfree ly X g).
{ unfold hfree in *. destruct sec_extents_split as (E1 & E2 & EX & EX2). rewrite EX2 in HF. rewrite EX.
apply Forall_app in HF as [HFs HF]. apply Forall_app in HF as [HFv HF]. apply Forall_app in HF as [HF1 HF2].
apply Forall_app; split; [exact HFs|]. apply Forall_app; split; [exact HFv|]. apply Forall_app; split; [exact HF1|]. constructor; [|exact HF2].
cbn [fst snd]. destruct GE as (_ & _ & M3 & _ & L5 & _). clear - Hout Hg M3 L5. lia. }
rewrite (EQ (shadow_addr g) (shadow_addr_band_rw g HAPP)); [exact (HZ g Hg HAPP HF0)|].
intros HD. apply Hout. apply (proj1 (DH_iff g Hg)). exact (BAND _ (shadow_addr_band_rw g HAPP) HD).
Qed.
End f.
End b.
