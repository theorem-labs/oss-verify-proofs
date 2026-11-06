(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YQ0b YK05 YA0i YA0l.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0h YG10 YG0u YG0d YG0y YG0w YG0z YG0v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF0k YF8t YF0q YF0r YF0w YF0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition next_addr (ly : alayout) (l : list batch) (i : nat) : Z :=
match nth_error l (S i) with Some b3 => ly_space ly + b_self b3 | None => 0 end.
Lemma sum_bytes_cons : forall b l, sum_bytes (b :: l) = b_bytes b + sum_bytes l. Proof. img_refl. Qed.
Lemma sum_bytes_nil : sum_bytes [] = 0. Proof. img_refl. Qed.
Section m. Context {imgk : img}.
Variable B : asyms.
Hypothesis TB : TfxSyms B.
Variables (ly : alayout) (X : astate) (rd rd' : reader).
Hypothesis M : ARm B ly X rd.
Local Notation T := (ly_T ly).
Local Notation G := (qc_list (st_qglobal X)).
Local Notation Tq := (qc_list (st_qthread X)).
Local Notation gb := (qc_bytes (st_qglobal X)).
Local Notation tb := (qc_bytes (st_qthread X)).
Definition addr (b : batch) : Z := ly_space ly + b_self b.
Hypothesis HTB : kQuarantineCacheMax < tb.
Variables (P R : list batch).
Hypothesis HL : G ++ Tq = P ++ R.
Definition XT : astate := set_qglobal (mkQC (G ++ Tq) (gb + tb)) (set_qthread qc0 X).
Definition S' : astate := set_qglobal (mkQC R (qc_bytes (st_qglobal XT) - sum_bytes P)) XT.
Definition GLv : Z := match rev G with [] => 0 | lb :: _ => addr lb end.
Definition TFv : Z := match Tq with [] => 0 | b0 :: _ => addr b0 end.
Definition RFv : Z := match R with [] => 0 | b0 :: _ => addr b0 end.
Definition RLv : Z := match rev R with [] => 0 | lb :: _ => addr lb end.
Variable sp : Z.
Hypothesis Hsp : ly_stk_lo ly + DSTACK <= sp <= ly_stk_hi ly.
Hypothesis IMG : img_cover ly.
Definition DT (a : Z) : Prop := T + t_qc <= a < T + t_qc + 32.
Definition DQ (a : Z) : Prop := (as_inst B + o_q_cmutex <= a < as_inst B + o_q_cmutex + 4) \/ (as_inst B + o_q_size <= a < as_inst B + o_q_size + 32).
Definition DL (a : Z) : Prop := G <> [] /\ GLv <= a < GLv + 8.
Definition DP (a : Z) : Prop := exists b2, In b2 P /\ addr b2 <= a < addr b2 + 8.
Definition DS (a : Z) : Prop := sp - DSTACK <= a < sp.
Definition D (a : Z) : Prop := DT a \/ DQ a \/ DL a \/ DP a \/ DS a.
Hypothesis AG : forall a, 0 <= a < 2 ^ 64 -> ~ D a -> rd' a = rd a.
Hypothesis VIS : forall a, rd a <> None -> rd' a <> None.
Hypothesis NEW_t : forall j i, 0 <= j < 4 -> (i < 8)%nat -> rd' (T + t_qc + 8 * j + Z.of_nat i) = Some (YG0h.le_byte 0 8 i).
Hypothesis NEW_mx : forall i, 0 <= i < 4 -> rd' (as_inst B + o_q_cmutex + i) = Some 0.
Hypothesis NEW_qs : forall i, (i < 8)%nat -> rd' (as_inst B + o_q_size + Z.of_nat i) = Some (YG0h.le_byte (Z.of_nat (length R)) 8 i).
Hypothesis NEW_qf : forall i, (i < 8)%nat -> rd' (as_inst B + o_q_first + Z.of_nat i) = Some (YG0h.le_byte RFv 8 i).
Hypothesis NEW_ql : forall i, (i < 8)%nat -> rd' (as_inst B + o_q_last + Z.of_nat i) = Some (YG0h.le_byte RLv 8 i).
Hypothesis NEW_qb : forall i, (i < 8)%nat -> rd' (as_inst B + o_q_bytes + Z.of_nat i) = Some (YG0h.le_byte (gb + tb - sum_bytes P) 8 i).
Hypothesis NEW_P : forall i b2, nth_error P i = Some b2 -> forall kk, (kk < 8)%nat -> rd' (addr b2 + Z.of_nat kk) = Some (YG0h.le_byte (next_addr ly P i) 8 kk).
Hypothesis NEW_J : forall lb initr, rev G = lb :: initr -> (length P < length G)%nat ->
forall kk, (kk < 8)%nat -> rd' (addr lb + Z.of_nat kk) = Some (YG0h.le_byte TFv 8 kk).
Hypothesis CONST' : Forall (cell_holds B ly rd') (as_const B ly).
Ltac drop_mem := clear AG VIS NEW_t NEW_mx NEW_qs NEW_qf NEW_ql NEW_qb NEW_P NEW_J CONST'.
Ltac geo := drop_mem.
Let WF : Wf (as_universe B) X := am_wf B ly X rd M.
Let LO : layout_ok ly := am_layout B ly X rd M.
Lemma S'_regions : st_regions S' = st_regions X.   Proof. geo. img_refl. Qed.
Lemma S'_chunks : st_chunks S' = st_chunks X.      Proof. geo. img_refl. Qed.
Lemma S'_secs : st_secs S' = st_secs X.            Proof. geo. img_refl. Qed.
Lemma S'_sec_arr : st_sec_arr S' = st_sec_arr X.   Proof. geo. img_refl. Qed.
Lemma S'_sec_res : st_sec_reserved S' = st_sec_reserved X. Proof. geo. img_refl. Qed.
Lemma S'_fs : st_fs S' = st_fs X.                  Proof. geo. img_refl. Qed.
Lemma S'_depot : st_depot S' = st_depot X.         Proof. geo. img_refl. Qed.
Lemma S'_cinit : st_cache_inited S' = st_cache_inited X. Proof. geo. img_refl. Qed.
Lemma S'_inited : st_internal_inited S' = st_internal_inited X. Proof. geo. img_refl. Qed.
Lemma S'_nev : st_nev S' = st_nev X.               Proof. geo. img_refl. Qed.
Lemma S'_cache : st_cache S' = st_cache X.         Proof. geo. img_refl. Qed.
Lemma reg' : forall c, reg S' c = reg X c.         Proof. geo. intros c. img_refl. Qed.
Lemma cache' : forall c, cache S' c = cache X c.   Proof. geo. intros c. img_refl. Qed.
Lemma frames' : frames S' = frames X.              Proof. geo. img_refl. Qed.
Lemma qglist' : qc_list (st_qglobal S') = R.       Proof. geo. img_refl. Qed.
Lemma qgbytes' : qc_bytes (st_qglobal S') = gb + tb - sum_bytes P. Proof. geo. img_refl. Qed.
Lemma qtlist' : qc_list (st_qthread S') = [].      Proof. geo. img_refl. Qed.
Lemma qtbytes' : qc_bytes (st_qthread S') = 0.     Proof. geo. img_refl. Qed.
Lemma all_batches_X : all_batches X = Tq ++ G.     Proof. geo. img_refl. Qed.
Lemma all_batches_S' : all_batches S' = R.         Proof. geo. img_refl. Qed.
Lemma sec_extents' : sec_extents ly S' = sec_extents ly X. Proof. geo. img_refl. Qed.
Lemma asecA_S' : forall A, asecA ly X A -> asecA ly S' A.
Proof. intros A H e He. rewrite sec_extents' in He. img_exact (H e He). Qed.
Lemma fa_poison' : fa_poison_ranges ly S' = fa_poison_ranges ly X. Proof. geo. img_refl. Qed.
Lemma Tq_ne : Tq <> [].
Proof. geo.
intros E. pose proof (wq_bytes_t _ (wf_quarantine _ _ _ _ _ WF)) as QB. rewrite E in QB. cbn in QB. unfold kQuarantineCacheMax in HTB. img_lia.
Qed.
Lemma In_all : forall b2, In b2 (all_batches X) <-> In b2 P \/ In b2 R.
Proof. geo. intros b2. rewrite all_batches_X, <- in_app_iff, <- HL, !in_app_iff. tauto. Qed.
Lemma In_P : forall b2, In b2 P -> In b2 (all_batches X). Proof. intros b2 H. img_apply In_all. left. img_exact H. Qed.
Lemma In_R : forall b2, In b2 R -> In b2 (all_batches X). Proof. intros b2 H. img_apply In_all. right. img_exact H. Qed.
Lemma b_bytes_lb : forall b2, In b2 (all_batches X) -> kBatchBytes <= b_bytes b2.
Proof. geo.
intros b2 Hb2. pose proof (wq_items _ (wf_quarantine _ _ _ _ _ WF)) as QI. unfold b_bytes.
assert (NN : forall L, (forall k, In k L -> In k (st_chunks X)) -> 0 <= fold_right (fun k acc => ck_n k + acc) 0 L).
{ intros L HLL. induction L as [|k L IH]; [img_try (cbn; img_lia)|]. cbn [fold_right].
pose proof (chunk_facts B ly X rd k M (HLL k (or_introl eq_refl))) as (_ & _ & _ & _ & _ & _ & G7 & _).
pose proof (IH ltac:(img_try (intros k3 Hk3; img_apply HLL; right; img_exact Hk3))). unfold ck_n in *. pose proof (req_size_bounds (ck_req k) ltac:(img_lia)). img_lia. }
pose proof (NN (b_items b2) ltac:(img_try (intros k Hk; img_exact (proj1 (proj1 (Forall_forall _ _) QI k ltac:(unfold q_items; img_apply in_flat_map; exists b2; split; [img_try (img_exact Hb2) | img_try (img_exact Hk)])))))). img_lia.
Qed.
Lemma sum_bytes_lb : forall L, (forall b2, In b2 L -> In b2 (all_batches X)) -> 0 <= sum_bytes L.
Proof.
intros L HLL. induction L as [|b2 L IH]; [img_try (cbn; img_lia)|]. rewrite sum_bytes_cons.
pose proof (b_bytes_lb b2 (HLL b2 (or_introl eq_refl))). pose proof (IH ltac:(img_try (intros b3 Hb3; img_apply HLL; right; img_exact Hb3))). unfold kBatchBytes in *. img_lia.
Qed.
Lemma RIS' : RI (as_universe B) 0 0 0 S' P.
Proof. geo.
pose proof (WfP_transfer _ 0 0 0 X WF HTB  ) as WT. cbv zeta in WT.
img_exact (RI_pop _ 0 0 0 XT P R WT HL).
Qed.
Lemma WS' : Wf (as_universe B) S'.
Proof. img_exact (proj1 RIS'). Qed.
Lemma batch_geom : forall b2, In b2 (all_batches X) ->
exists x, addr b2 = region_base ly kBatchClass + x /\ 0 <= x /\ x mod kBatchBytes = 0 /\
x + kBatchBytes <= rg_alloc_user (reg X kBatchClass) /\ rg_alloc_user (reg X kBatchClass) <= rg_mapped_user (reg X kBatchClass) <= 2 ^ 31 /\
In x (batch_offs X kBatchClass).
Proof. geo.
intros b2 Hb2. pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(img_try (unfold kBatchClass; img_lia))) as CL.
set (x := b_self b2 - region_off kBatchClass).
assert (INB : In x (batch_offs X kBatchClass)) by (img_try (rewrite batch_offs_24; img_apply in_map_iff; exists b2; auto)).
pose proof (proj1 (Forall_forall _ _) (wr_elems _ _ _ _ _ _ CL) x ltac:(img_try (rewrite !in_app_iff; tauto))) as [X1 X2].
pose proof (wr_alloc _ _ _ _ _ _ CL) as AL. pose proof (wr_alloc_al _ _ _ _ _ _ CL) as AA.
pose proof (mapped_user_bound (as_universe B) 0 0 0 X kBatchClass WF ltac:(img_try (unfold kBatchClass; img_lia))) as MB.
assert (CS : class_size kBatchClass = 8192) by img_refl. rewrite CS in X2, AA. unfold kUserMapSize, EV_MAX in MB. unfold kBatchBytes.
assert (XB : x + 8192 <= rg_alloc_user (reg X kBatchClass)).
{ apply Z.mod_divide in X2 as [q Hq]; [|img_lia]. apply Z.mod_divide in AA as [q' Hq']; [|img_lia]. assert (q < q') by nia. nia. }
exists x. splits; try assumption; try img_lia. unfold addr, region_base. (subst x; cbv beta). img_lia.
Qed.
Lemma batches_nodup : List.NoDup (map b_self (all_batches X)).
Proof. geo.
pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(img_try (unfold kBatchClass; img_lia))) as CL.
pose proof (wr_nodup _ _ _ _ _ _ CL) as ND. rewrite app_assoc in ND. apply NoDup_app_iff in ND as (_ & ND & _). apply NoDup_app_iff in ND as (_ & ND & _).
rewrite batch_offs_24 in ND.
clear - ND. induction (all_batches X) as [|x t IH]; cbn in *; [img_try (constructor)|].
inversion ND as [|y l N1 N2]; (subst; cbv beta). constructor; [|img_try (img_exact (IH N2))].
intros Hin. img_apply N1. apply in_map_iff in Hin as (x' & E & Hx'). img_apply in_map_iff. exists x'. split; [img_lia | img_try (img_exact Hx')].
Qed.
Lemma PR_nodup : List.NoDup (map b_self (P ++ R)).
Proof. geo.
rewrite <- HL. pose proof batches_nodup as ND. rewrite all_batches_X in ND. rewrite map_app in ND |- *.
apply NoDup_app_iff in ND as (N1 & N2 & N3). img_apply NoDup_app_iff. splits; [img_try (img_exact N2) | img_try (img_exact N1) |]. intros x H1 H2. img_exact (N3 x H2 H1).
Qed.
Lemma batches_apart : forall b1 b2, In b1 (all_batches X) -> In b2 (all_batches X) -> b_self b1 <> b_self b2 ->
zdisjoint (addr b1, kBatchBytes) (addr b2, kBatchBytes).
Proof. geo.
intros b1 b2 H1 H2 NE. destruct (batch_geom b1 H1) as (x1 & E1 & P1 & A1 & _). destruct (batch_geom b2 H2) as (x2 & E2 & P2 & A2 & _).
unfold zdisjoint, kBatchBytes in *. cbn [fst snd]. rewrite E1, E2.
apply Z.mod_divide in A1 as [q1 Hq1]; [|img_lia]. apply Z.mod_divide in A2 as [q2 Hq2]; [|img_lia].
assert (q1 <> q2) by (img_try (intros ->; img_apply NE; unfold addr in *; img_lia)). nia.
Qed.
Lemma batch_vs_chunk : forall b2 x, In b2 (all_batches X) -> In x (st_chunks X) ->
zdisjoint (addr b2, kBatchBytes) (ck_base B ly x, ck_extent x).
Proof. geo.
intros b2 x Hb2 Hx. destruct (batch_geom b2 Hb2) as (xb & Eb & Pb & Ab & Ub & [AU MU] & INB).
pose proof (chunk_facts B ly X rd x M Hx) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(img_try (unfold kBatchClass; img_lia))) as CL.
pose proof (wr_nodup _ _ _ _ _ _ CL) as ND. rewrite app_assoc in ND. apply NoDup_app_iff in ND as (_ & ND & _). apply NoDup_app_iff in ND as (_ & _ & NDx).
unfold zdisjoint. cbn [fst snd]. rewrite Eb.
destruct (ck_beg x) as [|o|r o|c p] eqn:Ebx; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & Gxm & Gxs & Gal).
destruct (Z.eq_dec (prim_class o) kBatchClass) as [Ec|Hc].
+ pose proof (In_chunk_offs X x o Hx Ebx) as IK. rewrite Ec in *. set (xk := o - region_off kBatchClass) in *.
assert (CS : class_size kBatchClass = 8192) by img_refl. rewrite CS in *.
assert (xk <> xb). { intros E. img_apply (NDx xk); [img_try (img_exact IK) | img_try (rewrite E; img_exact INB)]. }
unfold kBatchBytes in *. apply Z.mod_divide in Gxm as [q1 Hq1]; [|img_lia]. apply Z.mod_divide in Ab as [q2 Hq2]; [|img_lia].
assert (q1 <> q2) by (img_try (intros E; (subst; cbv beta); img_lia)). nia.
+ pose proof (region_in_prim ly (prim_class o) LO ltac:(img_lia)) as (R1' & R2' & _).
unfold region_base, kBatchBytes in *. rewrite !region_off_eq in * by (img_try (unfold kBatchClass; img_lia)). unfold kBatchClass in *.
destruct (Z.lt_ge_cases (prim_class o) 24).
* pose proof (Z.mul_le_mono_nonneg_r (prim_class o + 1) 24 (2 ^ 32) ltac:(img_lia) ltac:(img_lia)). img_lia.
* pose proof (Z.mul_le_mono_nonneg_r (24 + 1) (prim_class o) (2 ^ 32) ltac:(img_lia) ltac:(img_lia)). img_lia.
- destruct GG as (-> & _ & Gbase & Gext & Gin & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(img_try (unfold kBatchClass; img_lia))) as (R1 & R2 & _).
pose proof (pairwise_In zdisjoint _ (ly_sec ly r, sec_map_size (ck_req x)) (ly_prim ly, kPrimResvSize) (sec_extents ly X) (static_extents ly) eq_refl (proj2 (am_placed _ _ _ _ M)) Gin
ltac:(img_try (unfold static_extents, owned_extents; cbn; tauto))) as DJ.
unfold zdisjoint, kPage, kBatchBytes in *. cbn [fst snd] in DJ. unfold region_base in *. img_lia.
Qed.
Lemma SX : forall i j x y, nth_error (static_extents ly) i = Some x -> nth_error (static_extents ly) j = Some y -> i <> j -> zdisjoint x y.
Proof. geo.
intros i j x y Hi Hj Hne. destruct (Nat.lt_ge_cases i j).
- img_exact (pairwise_nth zdisjoint _ i j x y (lo_disj _ LO) Hi Hj H).
- img_apply zdisjoint_sym. img_apply (pairwise_nth zdisjoint _ j i y x (lo_disj _ LO) Hj Hi). img_lia.
Qed.
Lemma SECX : forall e j y, In e (sec_extents ly X) -> nth_error (static_extents ly) j = Some y -> zdisjoint e y.
Proof. geo.
intros e j y He Hj. eapply (pairwise_In zdisjoint _ e y (sec_extents ly X) (static_extents ly) eq_refl (proj2 (am_placed _ _ _ _ M)) He).
eapply nth_error_In. img_exact Hj.
Qed.
Lemma ext_zone : forall y, In y (st_chunks X) ->
(exists c, 1 <= c <= 30 /\ region_base ly c <= ck_base B ly y /\ ck_base B ly y + ck_extent y <= region_base ly c + 2 ^ 31 /\
ly_prim ly <= region_base ly c /\ region_base ly c + 2 ^ 32 <= ly_prim ly + kPrimResvSize) \/
(exists r, ck_beg y = PSec r kPage /\ ck_base B ly y = ly_sec ly r + kPage /\ In (ly_sec ly r, ck_extent y + kPage) (sec_extents ly X)).
Proof. geo.
intros y Hy. pose proof (chunk_facts B ly X rd y M Hy) as (G1 & G2 & _ & _ & _ & _ & _ & _ & GG).
destruct (ck_beg y) as [|o|r o|c p]; try solve [destruct GG].
- left. cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal & Gm).
pose proof (region_in_prim ly (prim_class o) LO ltac:(img_lia)) as (R1 & R2 & _). exists (prim_class o). splits; img_lia.
- right. destruct GG as (-> & _ & Gbase & Gext & Gin & _). exists r. splits; [img_refl | img_lia |].
replace (ck_extent y + kPage) with (sec_map_size (ck_req y)) by img_lia. img_exact Gin.
Qed.
Lemma anyX : forall y j e, In y (st_chunks X) -> nth_error (static_extents ly) j = Some e -> (j <> 0)%nat -> zdisjoint (ck_base B ly y, ck_extent y) e.
Proof. geo.
intros y j e Hy Hj Hne. destruct (ext_zone y Hy) as [(c & Hc & X1 & X2 & X3 & X4)|(r & Ebk & Xb & Xin)].
- pose proof (SX 0 j _ e eq_refl Hj ltac:(img_lia)) as DJ. unfold zdisjoint in DJ |- *. cbn [fst snd] in DJ |- *. img_lia.
- pose proof (SECX _ j e Xin Hj) as DJ. unfold zdisjoint, kPage in *. cbn [fst snd] in DJ |- *. img_lia.
Qed.
Lemma glast_in : forall lb initr, rev G = lb :: initr -> In lb (all_batches X) /\ GLv = addr lb /\ G = rev initr ++ [lb].
Proof. geo.
intros lb initr Hrev. assert (E0 : G = rev initr ++ [lb]) by (img_try (rewrite <- (rev_involutive G), Hrev; img_refl)).
splits; [|img_try (unfold GLv; rewrite Hrev; img_refl) | img_try (img_exact E0)].
rewrite all_batches_X. img_apply in_app_iff. right. rewrite E0. img_apply in_app_iff. right. left. img_refl.
Qed.
Lemma zdisjoint_of_pointwise : forall a s (e : Z * Z), 0 < s -> 0 < snd e -> (forall x, a <= x < a + s -> ~ in_zr x e) -> zdisjoint (a, s) e.
Proof. clear_all. intros a s [c t] Hs Ht H. unfold zdisjoint. unfold in_zr in H. cbn [fst snd] in *.
destruct (Z_lt_le_dec (Z.max a c) (a + s)); [|img_lia]. destruct (Z_lt_le_dec (Z.max a c) (c + t)); [|img_lia].
exfalso. img_apply (H (Z.max a c)); img_lia.
Qed.
Lemma HIGH : kHighMemBeg <= ly_prim ly /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\ zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\
kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd /\
ly_prim ly <= ly_space ly /\ ly_space ly + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\
(forall b2, In b2 (all_batches X) -> ly_prim ly <= addr b2 /\ addr b2 + kBatchBytes <= ly_space ly + kSpaceSize) /\
4096 <= as_inst B /\ as_inst B + 3632 <= kLowMemEnd.
Proof. geo.
pose proof (lo_high _ LO) as IP. unfold in_high in IP. cbn [fst snd] in IP.
pose proof (lo_app _ LO) as HA. pose proof (lo_disj _ LO) as HD.
pose proof (Forall_nth_f _ _ 2 _ HA eq_refl) as IT. cbn beta in IT. cbn [fst snd] in IT.
pose proof (zone3_intro ly T kThreadObjSize IMG ltac:(img_try (clear_all; unfold kThreadObjSize; img_lia)) IT (pairwise_ij_f _ _ 2 6 _ _ HD eq_refl eq_refl)) as ZT. clear HA HD IT.
pose proof (lo_top _ LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). pose proof (lo_space_in _ LO) as [S1 S2].
pose proof (region_in_prim ly kBatchClass LO ltac:(img_try (unfold kBatchClass; img_lia))) as (R1 & R2 & R3 & R4 & R5).
pose proof (aso_cells _ (am_syms _ _ _ _ M)) as AC.
assert (RB : region_base ly kBatchClass = ly_space ly + 24 * 2 ^ 32) by (img_try (unfold region_base; rewrite region_off_eq by (unfold kBatchClass; img_lia); img_refl)).
split; [img_try (clear - IP; img_lia)|]. split; [img_try (clear - IP; img_lia)|]. split; [img_try (img_exact ZT)|]. split; [img_try (clear - ZT; unfold zone3 in ZT; img_lia)|]. clear ZT.
splits; try assumption; try (unfold kBatchBytes, kSpaceSize in *; img_lia).
intros b2 Hb2. destruct (batch_geom b2 Hb2) as (xb & Eb' & Pb' & Ab' & Ub' & [AU' MU'] & _). unfold kBatchBytes, kSpaceSize in *. img_lia.
Qed.
Ltac high := pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
Lemma D_cases : forall a, D a ->
(T <= a < T + kThreadObjSize /\ DT a) \/ (as_inst B + o_q_cmutex <= a < as_inst B + o_q_bytes + 8 /\ DQ a) \/
(exists b2, In b2 (all_batches X) /\ addr b2 <= a < addr b2 + 8 /\ (In b2 P \/ (exists initr, rev G = b2 :: initr))) \/
(ly_stk_lo ly <= a < ly_stk_hi ly).
Proof. geo.
intros a Ha. pose proof HIGH as HI. destruct Ha as [Y|[Y|[Y|[Y|Y]]]].
- left. split; [|img_try (img_exact Y)]. unfold DT, t_qc, kThreadObjSize in *. img_lia.
- right; left. split; [|img_try (img_exact Y)]. unfold DQ, o_q_cmutex, o_q_size, o_q_bytes in *. img_lia.
- do 2 right; left. destruct Y as [NE Y]. destruct (rev G) as [|lb initr] eqn:Hrev.
+ exfalso. img_apply NE. rewrite <- (rev_involutive G), Hrev. img_refl.
+ destruct (glast_in lb initr Hrev) as (Hin & EQ & _). exists lb. rewrite <- EQ. splits; [img_try (img_exact Hin) | img_lia | img_lia | img_try (right; exists initr; img_refl)].
- do 2 right; left. destruct Y as (b2 & Hb2 & Y). exists b2. splits; [img_try (img_exact (In_P _ Hb2)) | img_lia | img_lia | img_try (left; img_exact Hb2)].
- do 3 right. unfold DS, DSTACK in *. img_lia.
Qed.
Definition ok (a : Z) : Prop := 0 <= a < 2 ^ 64 /\ ~ D a.
Definition okr (lo len : Z) : Prop := forall a, lo <= a < lo + len -> ok a.
Lemma AGok : forall a, ok a -> rd' a = rd a. Proof. intros a [H1 H2]. img_apply AG; assumption. Qed.
Ltac hnum := ceil; unfold zone3, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighShadowEnd, kHighMemEnd, kLowMemEnd, kBatchBytes, kThreadObjSize, kPage, kSpaceSize,
o_q_cmutex, o_q_rmutex, o_q_size, o_q_first, o_q_last, o_q_bytes in *.
Ltac zd H := let Y := fresh "ZD" in pose proof H as Y; unfold zdisjoint in Y; cbn [fst snd] in Y; hnum; img_lia.
Ltac tbnum := rewrite ?(ts_inst B TB), ?(ts_depot B TB), ?(ts_store B TB), ?(ts_ial_lo B TB), ?(ts_ial_hi B TB), ?(ts_ial_w B TB), ?(ts_ial_flag B TB) in *;
unfold TFX_INST, TFX_DEPOT, TFX_STORE, TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_W, TFX_IAL_FLAG, TFX_IMG_LO, TFX_IMG_END in *.
Ltac zget HI x sz Z := assert (Z : zone3cases x sz) by (img_try (clear - HI; unfold zone3 in HI; tauto)); unfold zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kThreadObjSize, kHighMemBeg in Z.
Lemma ok_below : forall a, TFX_IMG_LO <= a < TFX_IMG_END -> ~ (as_inst B + o_q_cmutex <= a < as_inst B + o_q_bytes + 8) -> ok a.
Proof. geo.
intros a Ha NQ. pose proof HIGH as HI. zget HI (ly_T ly) kThreadObjSize ZZ. high. split; [img_try (hnum; unfold TFX_IMG_LO, TFX_IMG_END in *; img_lia)|]. intros HD.
apply D_cases in HD as [[Y _]|[[Y _]|[(b2 & Hin & Y & _)|Y]]]; [img_try (hnum; unfold TFX_IMG_LO, TFX_IMG_END in *; img_lia) | img_try (img_exact (NQ Y)) | | img_try (hnum; unfold TFX_IMG_LO, TFX_IMG_END in *; img_lia)].
destruct (H9 b2 Hin). hnum. unfold TFX_IMG_LO, TFX_IMG_END in *. img_lia.
Qed.
Lemma ok_shb : forall a, kLowShadowBeg <= a < kHighMemBeg -> ok a.
Proof. geo.
intros a Ha. pose proof HIGH as HI. zget HI (ly_T ly) kThreadObjSize ZZ. high. pose proof (aso_cells _ (am_syms _ _ _ _ M)) as AC.
split; [img_try (hnum; unfold kLowShadowBeg in *; img_lia)|]. intros HD.
apply D_cases in HD as [[Y _]|[[Y _]|[(b2 & Hin & Y & _)|Y]]]; [img_try (hnum; unfold kLowShadowBeg in *; img_lia) | img_try (tbnum; hnum; unfold kLowShadowBeg in *; img_lia) | | img_try (hnum; unfold kLowShadowBeg in *; img_lia)].
destruct (H9 b2 Hin). hnum. unfold kLowShadowBeg in *. img_lia.
Qed.
Lemma ok_inst : forall a, as_inst B <= a < as_inst B + 3632 -> ~ (as_inst B + o_q_cmutex <= a < as_inst B + o_q_bytes + 8) -> ok a.
Proof. intros a Ha NQ. high. img_apply ok_below; [|img_try (img_exact NQ)]. tbnum. img_lia. Qed.
Lemma ok_static : forall j e a, nth_error (static_extents ly) j = Some e -> (j <> 0)%nat -> (j <> 2)%nat -> (j < 8)%nat ->
fst e <= a < fst e + snd e -> ok a.
Proof. geo.
intros j e a Hj J0 J2 J8 Ha. high.
pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) e) as HE.
assert (INO : In e (owned_extents ly)).
{ unfold static_extents in Hj. rewrite nth_error_app1 in Hj by (img_try (cbn; img_lia)). eapply nth_error_In. img_exact Hj. }
specialize (HE INO). unfold in_app in HE. cbn [fst snd] in HE. split; [img_try (hnum; unfold kLowShadowBeg in *; img_lia)|]. intros HD.
apply D_cases in HD as [[Y _]|[[Y _]|[(b2 & Hin & Y & _)|Y]]].
- zd (SX j 2 _ _ Hj eq_refl ltac:(img_lia)).
-
pose proof (SX j 9 _ _ Hj eq_refl ltac:(img_lia)) as ZD. unfold zdisjoint in ZD. cbn [fst snd] in ZD. pose proof IMG as [IM1 IM2]. tbnum. hnum. img_lia.
- destruct (H9 b2 Hin). pose proof (SX 0 j _ _ eq_refl Hj ltac:(img_lia)) as ZD. unfold zdisjoint in ZD. cbn [fst snd] in ZD. hnum. unfold kSpaceSize in *. img_lia.
- zd (SX j 8 _ _ Hj eq_refl ltac:(img_lia)).
Qed.
Lemma ok_T : forall a, T <= a < T + kThreadObjSize -> ~ DT a -> ok a.
Proof. geo.
intros a Ha ND. high. split; [img_try (hnum; img_lia)|]. intros HD.
apply D_cases in HD as [[Y Z0]|[[Y _]|[(b2 & Hin & Y & _)|Y]]].
- img_exact (ND Z0).
- pose proof HIGH as HI. zget HI (ly_T ly) kThreadObjSize ZZ. tbnum. hnum. img_lia.
- destruct (H9 b2 Hin). pose proof (SX 0 2 _ _ eq_refl eq_refl ltac:(img_lia)) as ZD. unfold zdisjoint in ZD. cbn [fst snd] in ZD. hnum. unfold kSpaceSize in *. img_lia.
- zd (SX 2 8 _ _ eq_refl eq_refl ltac:(img_lia)).
Qed.
Lemma ok_prim : forall a, ly_prim ly <= a < ly_prim ly + kPrimResvSize ->
(forall b2, In b2 (all_batches X) -> In b2 P \/ (exists initr, rev G = b2 :: initr) -> ~ (addr b2 <= a < addr b2 + 8)) -> ok a.
Proof. geo.
intros a Ha NB. high. split; [img_try (hnum; img_lia)|]. intros HD.
apply D_cases in HD as [[Y _]|[[Y _]|[(b2 & Hin & Y & W)|Y]]].
- zd (SX 0 2 _ _ eq_refl eq_refl ltac:(img_lia)).
- hnum. img_lia.
- img_exact (NB b2 Hin W Y).
- zd (SX 0 8 _ _ eq_refl eq_refl ltac:(img_lia)).
Qed.
Lemma ok_chunk : forall x a, In x (st_chunks X) -> ck_base B ly x <= a < ck_base B ly x + ck_extent x -> ok a.
Proof. geo.
intros x a Hx Ha.
destruct (ext_zone x Hx) as [(c & Hc & X1 & X2 & X3 & X4)|(r & Ebk & Xb & Xin)].
- img_apply ok_prim; [img_lia |]. intros b2 Hin _ Y. pose proof (batch_vs_chunk b2 x Hin Hx) as D2. zd D2.
- high.
pose proof (proj1 (Forall_forall _ _) (proj1 (am_placed _ _ _ _ M)) _ Xin) as (_ & [I1 I2] & I3). cbn [fst snd] in I1, I2, I3.
split; [img_try (hnum; unfold alloc_ceiling, sp_window_lo, stack_max_size, kPage in *; img_lia)|]. intros HD.
apply D_cases in HD as [[Y _]|[[Y _]|[(b2 & Hin & Y & _)|Y]]].
+ zd (SECX _ 2 _ Xin eq_refl).
+
pose proof (SECX _ 9 _ Xin eq_refl) as ZD9. unfold zdisjoint in ZD9. cbn [fst snd] in ZD9. pose proof IMG as [IM1 IM2]. tbnum. hnum. unfold kPage in *. img_lia.
+ destruct (H9 b2 Hin). pose proof (SECX _ 0 _ Xin eq_refl) as ZD. unfold zdisjoint in ZD. cbn [fst snd] in ZD. hnum. unfold kSpaceSize, kPage in *. img_lia.
+ zd (SECX _ 8 _ Xin eq_refl).
Qed.
Lemma ok_secpage : forall x r o a, In x (st_chunks X) -> ck_beg x = PSec r o -> ly_sec ly r <= a < ly_sec ly r + kPage -> ok a.
Proof. geo.
intros x r o a Hx Ebx Ha. pose proof (chunk_facts B ly X rd x M Hx) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG). rewrite Ebx in GG.
destruct GG as (-> & _ & Gbase & Gext & Gin & _). high.
pose proof (proj1 (Forall_forall _ _) (proj1 (am_placed _ _ _ _ M)) _ Gin) as (_ & [I1 I2] & _). cbn [fst snd] in I1, I2.
pose proof (req_size_bounds (ck_req x) ltac:(img_lia)) as (_ & Q2 & _).
split; [img_try (hnum; unfold kPage in *; img_lia)|]. intros HD.
apply D_cases in HD as [[Y _]|[[Y _]|[(b2 & Hin & Y & _)|Y]]].
- zd (SECX _ 2 _ Gin eq_refl).
- pose proof (SECX _ 9 _ Gin eq_refl) as ZD9. unfold zdisjoint in ZD9. cbn [fst snd] in ZD9. pose proof IMG as [IM1 IM2]. tbnum. hnum. unfold kPage in *. img_lia.
- destruct (H9 b2 Hin). pose proof (SECX _ 0 _ Gin eq_refl) as ZD. unfold zdisjoint in ZD. cbn [fst snd] in ZD. hnum. unfold kSpaceSize, kPage in *. img_lia.
- zd (SECX _ 8 _ Gin eq_refl).
Qed.
Lemma ok_batch : forall b2 a, In b2 (all_batches X) -> addr b2 + 8 <= a < addr b2 + kBatchBytes -> ok a.
Proof. geo.
intros b2 a Hb2 Ha. destruct (batch_geom b2 Hb2) as (x2 & E2 & P2 & A2 & U2 & [AU MU] & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(img_try (unfold kBatchClass; img_lia))) as (R1 & R2 & _).
img_apply ok_prim; [img_try (unfold kBatchBytes in *; img_lia) |].
intros b3 Hin _ Y. destruct (Z.eq_dec (b_self b3) (b_self b2)) as [E|NE].
- unfold addr in *. rewrite E in Y. img_lia.
- pose proof (batches_apart b3 b2 Hin Hb2 NE) as D2. zd D2.
Qed.
Lemma ok_batch_all : forall b2 a, In b2 (all_batches X) -> ~ In b2 P -> (forall initr, rev G <> b2 :: initr) ->
addr b2 <= a < addr b2 + kBatchBytes -> ok a.
Proof. geo.
intros b2 a Hb2 NP NL Ha. destruct (batch_geom b2 Hb2) as (x2 & E2 & P2 & A2 & U2 & [AU MU] & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(img_try (unfold kBatchClass; img_lia))) as (R1 & R2 & _).
img_apply ok_prim; [img_try (unfold kBatchBytes in *; img_lia) |].
intros b3 Hin W Y. destruct (Z.eq_dec (b_self b3) (b_self b2)) as [E|NE].
- assert (b3 = b2) as ->.
{ pose proof batches_nodup as ND. apply in_split in Hb2 as (l1 & l2 & EL). rewrite EL in ND, Hin. rewrite map_app in ND. cbn [map] in ND.
apply NoDup_remove in ND as [_ NI]. apply in_app_iff in Hin as [Hin|[<-|Hin]]; [img_try (exfalso) | img_refl | img_try (exfalso)]; img_apply NI; rewrite <- E; img_apply in_app_iff; [img_try (left)|img_try (right)]; img_apply in_map; img_exact Hin. }
destruct W as [W|[initr W]]; [img_try (img_exact (NP W)) | img_try (img_exact (NL initr W))].
- pose proof (batches_apart b3 b2 Hin Hb2 NE) as D2. zd D2.
Qed.
Lemma ok_rinfo : okr (ly_rinfo ly) 4096.
Proof. geo.
intros a Ha. high. unfold ly_rinfo, kRegionInfoOff in Ha.
img_apply ok_prim; [img_try (unfold kSpaceSize in *; img_lia) |].
intros b2 Hin _ Y. destruct (H9 b2 Hin). unfold kSpaceSize, kBatchBytes in *. img_lia.
Qed.
Lemma ok_fa : forall c, 1 <= c <= 31 -> okr (fa_base ly c) kFreeArrayMax.
Proof. geo.
intros c Hc a Ha. high.
pose proof (region_in_prim ly c LO Hc) as (R1 & R2 & _). pose proof (region_in_prim ly kBatchClass LO ltac:(img_try (unfold kBatchClass; img_lia))) as (Q1 & Q2 & _).
assert (FAR : forall x, 0 <= x -> x + kBatchBytes <= 2 ^ 31 -> ~ (fa_base ly c <= region_base ly kBatchClass + x + kBatchBytes - 1 /\ region_base ly kBatchClass + x < fa_base ly c + kFreeArrayMax)).
{ intros x Hx1 Hx2 [Z1 Z2]. unfold fa_base, region_base, kFreeArrayOffset, kFreeArrayMax, kBatchBytes in *. rewrite !region_off_eq in * by (img_try (unfold kBatchClass in *; img_lia)).
unfold kBatchClass in *. destruct (Z.lt_trichotomy c 24) as [L|[->|L]];
first [ img_lia
| pose proof (Z.mul_le_mono_nonneg_r (c + 1) 24 (2 ^ 32) ltac:(img_lia) ltac:(img_lia)); img_lia
| pose proof (Z.mul_le_mono_nonneg_r (24 + 1) c (2 ^ 32) ltac:(img_lia) ltac:(img_lia)); img_lia ]. }
img_apply ok_prim.
- clear FAR. unfold fa_base, region_base, kFreeArrayOffset, kFreeArrayMax in *. img_lia.
- intros b2 Hin _ Y. destruct (batch_geom b2 Hin) as (xb & Eb' & Pb' & Ab' & Ub' & [AU MU] & _).
rewrite Eb' in Y. img_apply (FAR xb); unfold kBatchBytes in *; img_lia.
Qed.
Definition cell_in (lo len : Z) (c : acell) : Prop :=
lo <= aeval B ly (c_at c) /\ aeval B ly (c_at c) + Z.max 1 (Z.of_nat (c_w c)) <= lo + len.
Lemma cell_xfer : forall c, cell_holds B ly rd c ->
(forall j, 0 <= j < Z.max 1 (Z.of_nat (c_w c)) -> ok (aeval B ly (c_at c) + j)) -> cell_holds B ly rd' c.
Proof. intros c Hc Hok. eapply (cell_holds_agree B ly rd rd' c Hc). intros j Hj. apply AGok, Hok, Hj. Qed.
Lemma cells_xfer : forall L lo len, okr lo len -> Forall (cell_in lo len) L -> Forall (cell_holds B ly rd) L -> Forall (cell_holds B ly rd') L.
Proof.
intros L lo len OK IN OLD. img_apply Forall_forall. intros c Hc. img_apply cell_xfer; [img_try (img_exact (proj1 (Forall_forall _ _) OLD c Hc))|].
intros j Hj. destruct (proj1 (Forall_forall _ _) IN c Hc) as [H1 H2]. img_apply OK. img_lia.
Qed.
Lemma OLD : forall c, In c (acells B ly X) -> cell_holds B ly rd c.
Proof. intros c Hc. img_exact (proj1 (Forall_forall _ _) (am_cells B ly X rd M) c Hc). Qed.
Ltac old_in := img_apply Forall_forall; intros ? HIN; img_apply OLD; unfold acells; rewrite !in_app_iff.
Lemma EA : forall y d, In y (st_chunks X) -> aeval B ly (aoff (sptr_exp (ck_beg y)) d) = ck_base B ly y + d.
Proof. geo.
intros y d Hy. pose proof (chunk_facts B ly X rd y M Hy) as (_ & _ & _ & _ & _ & _ & _ & _ & GG).
unfold ck_base, sptr_addr. destruct (ck_beg y) as [|o|r o|c p]; try solve [destruct GG]; cbn; img_lia.
Qed.
Lemma EA2 : forall y d d', In y (st_chunks X) -> aeval B ly (aoff (aoff (sptr_exp (ck_beg y)) d) d') = ck_base B ly y + d + d'.
Proof. geo.
intros y d d' Hy. pose proof (chunk_facts B ly X rd y M Hy) as (_ & _ & _ & _ & _ & _ & _ & _ & GG).
unfold ck_base, sptr_addr. destruct (ck_beg y) as [|o|r o|c p]; try solve [destruct GG]; cbn; img_lia.
Qed.
Lemma EA0 : forall y, aeval B ly (sptr_exp (ck_beg y)) = ck_base B ly y. Proof. geo. img_refl. Qed.
Ltac fcons := img_apply Forall_cons; [img_try (split; cbn; img_lia)|].
Lemma cells_regions : Forall (cell_holds B ly rd') (flat_map (region_cells S') (zseq 1 31)).
Proof.
img_apply Forall_flat_map'. intros c Hc. apply zseq_In in Hc. unfold region_cells. rewrite reg'.
img_apply (cells_xfer _ _ _ ok_rinfo).
- unfold cell_in, ly_rinfo, kRegionInfoOff. repeat fcons. img_apply Forall_nil.
- old_in. left. img_apply in_flat_map. exists c. split; [img_try (img_apply In_zseq; img_lia) | img_try (img_exact HIN)].
Qed.
Lemma okr_cache : forall c, 1 <= c <= 31 -> okr (T + t_cache + 80 * c) 80.
Proof. geo. intros c Hc a Ha. img_apply ok_T; unfold DT, t_cache, t_qc, kThreadObjSize in *; img_lia. Qed.
Lemma cells_caches : Forall (cell_holds B ly rd') (flat_map (cache_cells S') (zseq 1 31)).
Proof.
img_apply Forall_flat_map'. intros c Hc. apply zseq_In in Hc.
assert (OLDC : Forall (cell_holds B ly rd) (cache_cells X c)).
{ old_in. right; left. img_apply in_flat_map. exists c. split; [img_try (img_apply In_zseq; img_lia) | img_try (img_exact HIN)]. }
unfold cache_cells in OLDC |- *. rewrite S'_cinit, cache'.
img_apply (cells_xfer _ _ _ (okr_cache c ltac:(img_lia))); [|img_try (img_exact OLDC)].
pose proof (wf_classes _ _ _ _ _ WF c ltac:(img_lia)) as CL. pose proof (wr_cache _ _ _ _ _ _ CL) as WC. pose proof (class_ok c ltac:(img_lia)) as (_ & _ & _ & K4 & _).
destruct (st_cache_inited X) eqn:CI.
- destruct WC as [PM PL]. unfold cell_in, t_cache. repeat fcons. img_apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i v] & <- & Hiv). cbn [fst snd c_at c_w z4 c4 aeval aoff].
apply in_combine_l in Hiv. apply in_seq in Hiv. cbn. img_lia.
- unfold cell_in, t_cache. repeat fcons. img_apply Forall_nil.
Qed.
Lemma cells_chunks : Forall (cell_holds B ly rd') (flat_map chunk_cells (st_chunks S')).
Proof.
rewrite S'_chunks. img_apply Forall_flat_map'. intros x Hx. pose proof (chunk_facts B ly X rd x M Hx) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
img_apply (cells_xfer _ (ck_base B ly x) (ck_extent x)); [img_try (intros a Ha; img_exact (ok_chunk x a Hx Ha)) | |].
- pose proof (req_size_bounds (ck_req x) ltac:(img_lia)) as (_ & Q2 & _).
unfold chunk_cells, kChunkHeaderSize, cell_in. img_apply Forall_app. split.
+ repeat (img_apply Forall_cons; [img_try (cbn [c_at c_w z1 z2 z4 c1 c2 c4]; rewrite ?(EA2 x), ?(EA x), ?EA0 by img_exact Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.max Pos.max Z.pos_sub]; img_lia)|]). img_apply Forall_nil.
+ destruct (Z.eqb_spec (ck_rz x) 16); [img_try (img_apply Forall_nil)|].
repeat (img_apply Forall_cons; [img_try (cbn [c_at c_w z8 c8]; rewrite ?(EA2 x), ?(EA x), ?EA0 by img_exact Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.max Pos.max Z.pos_sub]; img_lia)|]). img_apply Forall_nil.
- old_in. do 2 right; left. img_apply in_flat_map. exists x. split; [img_try (img_exact Hx) | img_try (img_exact HIN)].
Qed.
Lemma cells_sec : Forall (cell_holds B ly rd') (sec_cells S').
Proof.
pose proof (wf_secondary _ _ _ _ _ WF) as XS. destruct XS as [Snd Sac Sal Sres Sral].
assert (OLDS : Forall (cell_holds B ly rd) (sec_cells X)) by (img_try (old_in; do 3 right; left; img_exact HIN)).
unfold sec_cells in OLDS |- *. rewrite S'_sec_res, S'_sec_arr, S'_chunks.
apply Forall_cons_iff in OLDS as [O1 OLDS]. apply Forall_cons_iff in OLDS as [O2 OLDS]. apply Forall_cons_iff in OLDS as [O3 OLDS]. apply Forall_app in OLDS as [O4 O5].
pose proof (aso_cells _ (am_syms _ _ _ _ M)) as AC.
assert (OKI : forall a, as_inst B <= a < as_inst B + o_sec_mutex + 1 -> ok a) by (img_try (intros a Ha; img_apply ok_inst; unfold o_sec_mutex, o_q_cmutex, o_q_bytes in *; img_lia)).
img_apply Forall_cons; [img_apply (cell_xfer _ O1); intros j Hj; img_apply OKI; cbn in Hj |- *; unfold o_sec_reserved, o_sec_mutex; img_lia|].
img_apply Forall_cons; [img_apply (cell_xfer _ O2); intros j Hj; img_apply OKI; cbn in Hj |- *; unfold o_sec_n, o_sec_mutex; img_lia|].
img_apply Forall_cons; [img_apply (cell_xfer _ O3); intros j Hj; img_apply OKI; cbn in Hj |- *; unfold o_sec_mutex; img_lia|].
img_apply Forall_app. split.
- refine (cells_xfer _ _ _ (fun a Ha => ok_static 1 _ a eq_refl ltac:(img_lia) ltac:(img_lia) ltac:(img_lia) Ha) _ O4).
img_apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i r] & <- & Hir). apply in_combine_l in Hir. apply in_seq in Hir.
unfold cell_in. cbn. unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *. img_lia.
- img_apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) O5 c Hc) as Oc. apply in_flat_map in Hc as (x & Hx & Hc).
destruct (ck_beg x) as [|o|r o|c' p] eqn:Ebx; try solve [destruct Hc].
assert (OKP : okr (ly_sec ly r) 32) by (img_try (intros a Ha; eapply (ok_secpage x r o a Hx Ebx); unfold kPage; img_lia)).
img_apply (cell_xfer _ Oc). intros j Hj. img_apply OKP. destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hj |- *; img_lia.
Qed.
Lemma batch_own_cells_within : forall b2 nx c, In c (batch_own_cells b2 nx) -> cell_in (addr b2) (24 + 8 * Z.of_nat (length (b_items b2))) c.
Proof. geo.
intros b2 nx c Hc. unfold batch_own_cells, addr in Hc |- *. destruct Hc as [<-|[<-|[<-|Hc]]]; try (unfold cell_in; cbn; img_lia).
apply in_map_iff in Hc as ([i x] & <- & Hix). apply in_combine_l in Hix. apply in_seq in Hix. unfold cell_in; cbn; img_lia.
Qed.
Lemma OLD_batch_cell : forall b2 nx c, In b2 (all_batches X) -> In c (tl (batch_own_cells b2 nx)) -> cell_holds B ly rd c.
Proof. geo.
intros b2 nx c Hb2 Hc.
assert (OLDQ : Forall (cell_holds B ly rd) (quar_cells X)) by (img_try (old_in; do 4 right; left; img_exact HIN)).
unfold quar_cells, qc_cells in OLDQ. apply Forall_cons_iff in OLDQ as [_ OLDQ]. apply Forall_cons_iff in OLDQ as [_ OLDQ]. apply Forall_app in OLDQ as [OT OG].
do 4 (apply Forall_cons_iff in OT as [_ OT]). do 4 (apply Forall_cons_iff in OG as [_ OG]).
cbn [tl batch_own_cells] in Hc.
rewrite all_batches_X in Hb2. apply in_app_iff in Hb2 as [Hb2|Hb2].
- apply In_nth_error in Hb2 as [i Hi]. img_apply (proj1 (Forall_forall _ _) OT). img_apply In_batch_cells. exists i, b2. split; [img_try (img_exact Hi)|]. right. img_exact Hc.
- apply In_nth_error in Hb2 as [i Hi]. img_apply (proj1 (Forall_forall _ _) OG). img_apply In_batch_cells. exists i, b2. split; [img_try (img_exact Hi)|]. right. img_exact Hc.
Qed.
Lemma old_next : forall L1 L2 i b2, (L1 = Tq /\ L2 = G \/ L1 = G /\ L2 = Tq) -> nth_error L1 i = Some b2 ->
cell_holds B ly rd (c8 (batch_exp b2) (next_exp L1 i)).
Proof. geo.
intros L1 L2 i b2 HL12 Hi.
assert (OLDQ : Forall (cell_holds B ly rd) (quar_cells X)) by (img_try (old_in; do 4 right; left; img_exact HIN)).
unfold quar_cells, qc_cells in OLDQ. apply Forall_cons_iff in OLDQ as [_ OLDQ]. apply Forall_cons_iff in OLDQ as [_ OLDQ]. apply Forall_app in OLDQ as [OT OG].
do 4 (apply Forall_cons_iff in OT as [_ OT]). do 4 (apply Forall_cons_iff in OG as [_ OG]).
destruct HL12 as [[-> ->]|[-> ->]].
- img_apply (proj1 (Forall_forall _ _) OT). img_apply In_batch_cells. exists i, b2. split; [img_try (img_exact Hi) | img_try (left; img_refl)].
- img_apply (proj1 (Forall_forall _ _) OG). img_apply In_batch_cells. exists i, b2. split; [img_try (img_exact Hi) | img_try (left; img_refl)].
Qed.

Lemma R_next : forall i b2, nth_error R i = Some b2 ->
next_exp R i = next_exp (G ++ Tq) (length P + i)%nat.
Proof. geo.
intros i b2 Hi. unfold next_exp. rewrite HL. rewrite nth_error_app2 by img_lia. replace (S (length P + i) - length P)%nat with (S i) by img_lia. img_refl.
Qed.
Lemma cat_next : forall j b2, nth_error (G ++ Tq) j = Some b2 ->
(exists i, nth_error Tq i = Some b2 /\ next_exp (G ++ Tq) j = next_exp Tq i) \/
(exists i, nth_error G i = Some b2 /\ (S i < length G)%nat /\ next_exp (G ++ Tq) j = next_exp G i) \/
(exists initr, rev G = b2 :: initr /\ S j = length G /\ next_exp (G ++ Tq) j = match Tq with [] => ANum 0 | b0 :: _ => batch_exp b0 end).
Proof. geo.
intros j b2 Hj. destruct (Nat.lt_ge_cases j (length G)) as [LT|GE].
- rewrite nth_error_app1 in Hj by img_exact LT. destruct (Nat.eq_dec (S j) (length G)) as [EJ|NJ].
+ do 2 right. destruct (nth_error_split _ _ Hj) as (l1 & l2 & E0 & Ll1).
assert (l2 = []) as -> by (img_try (apply (f_equal (@length _)) in E0; rewrite length_app in E0; cbn in E0; destruct l2; [img_refl | img_try (cbn in E0; img_lia)])).
exists (rev l1). splits; [img_try (rewrite E0, rev_app_distr; img_refl) | img_try (img_exact EJ) |].
unfold next_exp. rewrite nth_error_app2 by img_lia. rewrite EJ, Nat.sub_diag. destruct Tq; img_refl.
+ right; left. exists j. splits; [img_try (img_exact Hj) | img_lia |]. unfold next_exp. rewrite nth_error_app1 by img_lia. img_refl.
- left. rewrite nth_error_app2 in Hj by img_exact GE. exists (j - length G)%nat. split; [img_try (img_exact Hj)|].
unfold next_exp. rewrite nth_error_app2 by img_lia. replace (S j - length G)%nat with (S (j - length G)) by img_lia. img_refl.
Qed.
Lemma cells_quar : Forall (cell_holds B ly rd') (quar_cells S').
Proof.
assert (OLDQ : Forall (cell_holds B ly rd) (quar_cells X)) by (img_try (old_in; do 4 right; left; img_exact HIN)).
pose proof (aso_cells _ (am_syms _ _ _ _ M)) as AC. high.
unfold quar_cells, qc_cells in OLDQ |- *. rewrite qglist', qgbytes', qtlist', qtbytes'. cbn [length rev batch_cells Z.of_nat app].
img_apply Forall_cons. { cbn [cell_holds c_at c_val c_w z1 c1 aeval]. intros kk Hkk. replace (as_inst B + o_q_cmutex + Z.of_nat kk) with (as_inst B + o_q_cmutex + 0) by img_lia. rewrite NEW_mx by img_lia. destruct kk; [img_refl | img_lia]. }
img_apply Forall_cons. { cbn [cell_holds c_at c_val c_w z1 c1 aeval]. intros kk Hkk. replace (as_inst B + o_q_rmutex + Z.of_nat kk) with (as_inst B + o_q_cmutex + 1) by (img_try (unfold o_q_rmutex, o_q_cmutex; img_lia)). rewrite NEW_mx by img_lia. destruct kk; [img_refl | img_lia]. }
img_apply Forall_cons. { cbn [cell_holds c_at c_val c_w z8 c8 aeval]. intros kk Hkk. replace (T + t_qc + Z.of_nat kk) with (T + t_qc + 8 * 0 + Z.of_nat kk) by img_lia. img_apply NEW_t; [img_lia | img_try (img_exact Hkk)]. }
img_apply Forall_cons. { cbn [cell_holds c_at c_val c_w z8 c8 aeval aoff]. intros kk Hkk. replace (T + (t_qc + 8) + Z.of_nat kk) with (T + t_qc + 8 * 1 + Z.of_nat kk) by img_lia. rewrite NEW_t by (img_try (img_lia || img_exact Hkk)). img_refl. }
img_apply Forall_cons. { cbn [cell_holds c_at c_val c_w z8 c8 aeval aoff]. intros kk Hkk. replace (T + (t_qc + 16) + Z.of_nat kk) with (T + t_qc + 8 * 2 + Z.of_nat kk) by img_lia. rewrite NEW_t by (img_try (img_lia || img_exact Hkk)). img_refl. }
img_apply Forall_cons. { cbn [cell_holds c_at c_val c_w z8 c8 aeval aoff]. intros kk Hkk. replace (T + (t_qc + 24) + Z.of_nat kk) with (T + t_qc + 8 * 3 + Z.of_nat kk) by img_lia. img_apply NEW_t; [img_lia | img_try (img_exact Hkk)]. }
img_apply Forall_cons. { cbn [cell_holds c_at c_val c_w z8 c8 aeval]. intros kk Hkk. rewrite NEW_qs by img_exact Hkk. img_refl. }
img_apply Forall_cons. { cbn [cell_holds c_at c_val c_w c8 aeval aoff]. intros kk Hkk. replace (as_inst B + (o_q_size + 8)) with (as_inst B + o_q_first) by (img_try (unfold o_q_size, o_q_first; img_lia)).
rewrite NEW_qf by img_exact Hkk. unfold RFv, addr. destruct R; img_refl. }
img_apply Forall_cons. { cbn [cell_holds c_at c_val c_w c8 aeval aoff]. intros kk Hkk. replace (as_inst B + (o_q_size + 16)) with (as_inst B + o_q_last) by (img_try (unfold o_q_size, o_q_last; img_lia)).
rewrite NEW_ql by img_exact Hkk. unfold RLv, addr. destruct (rev R); img_refl. }
img_apply Forall_cons. { cbn [cell_holds c_at c_val c_w z8 c8 aeval aoff]. intros kk Hkk. replace (as_inst B + (o_q_size + 24)) with (as_inst B + o_q_bytes) by (img_try (unfold o_q_size, o_q_bytes; img_lia)).
rewrite NEW_qb by img_exact Hkk. img_refl. }
img_apply Forall_forall. intros c Hc. apply In_batch_cells in Hc as (i & b2 & Hi & Hc).
pose proof (nth_error_In _ _ Hi) as HinR. pose proof (In_R _ HinR) as Hin2.
pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wf_quarantine _ _ _ _ _ WF)) b2 Hin2) as [L1 L2]. unfold kBatchSlots in L2.
assert (NP : ~ In b2 P).
{ intros HP. pose proof PR_nodup as ND. rewrite map_app in ND. apply NoDup_app_iff in ND as (_ & _ & N3). img_exact (N3 (b_self b2) (in_map _ _ _ HP) (in_map _ _ _ HinR)). }
destruct Hc as [<-|Hc].
-
rewrite (R_next i b2 Hi).
assert (Hj : nth_error (G ++ Tq) (length P + i)%nat = Some b2) by (img_try (rewrite HL, nth_error_app2 by img_lia; replace (length P + i - length P)%nat with i by img_lia; img_exact Hi)).
destruct (cat_next _ _ Hj) as [(i' & Hi' & ->)|[(i' & Hi' & Si & ->)|(initr & Hrev & Sj & ->)]].
+   apply (cell_xfer _ (old_next _ _ i' b2 (or_introl (conj eq_refl eq_refl)) Hi')).
intros j Hj'. cbn in Hj'. cbn [c_at c_w c8 batch_exp aeval]. fold (addr b2). img_apply (ok_batch_all b2); [img_try (img_exact Hin2) | img_try (img_exact NP) | | img_try (unfold kBatchBytes; img_lia)].
intros initr Hrev. destruct (glast_in _ _ Hrev) as (_ & _ & EG).
pose proof batches_nodup as ND. rewrite all_batches_X, EG, !map_app in ND. cbn [map] in ND. rewrite app_assoc in ND.
apply NoDup_app_iff in ND as (_ & N2 & N3). img_apply (N3 (b_self b2)); [img_try (img_apply in_app_iff; left; img_apply in_map; eapply nth_error_In; img_exact Hi') | img_try (left; img_refl)].
+   apply (cell_xfer _ (old_next _ _ i' b2 (or_intror (conj eq_refl eq_refl)) Hi')).
intros j Hj'. cbn in Hj'. cbn [c_at c_w c8 batch_exp aeval]. fold (addr b2). img_apply (ok_batch_all b2); [img_try (img_exact Hin2) | img_try (img_exact NP) | | img_try (unfold kBatchBytes; img_lia)].
intros initr Hrev. destruct (glast_in _ _ Hrev) as (_ & _ & EG).
pose proof batches_nodup as ND. rewrite all_batches_X, EG, !map_app in ND. cbn [map] in ND.
apply NoDup_app_iff in ND as (_ & N2 & _). apply NoDup_app_iff in N2 as (N2 & _ & N4).
rewrite EG in Hi', Si. rewrite length_app in Si. cbn [length] in Si. rewrite nth_error_app1 in Hi' by img_lia.
img_apply (N4 (b_self b2)); [img_try (img_apply in_map; eapply nth_error_In; img_exact Hi') | img_try (left; img_refl)].
+
cbn [cell_holds c_at c_val c_w c8 aeval batch_exp]. intros kk Hkk. fold (addr b2). rewrite (NEW_J b2 initr Hrev ltac:(img_lia) kk Hkk).
unfold TFv, addr. destruct Tq; img_refl.
-
img_apply (cell_xfer _ (OLD_batch_cell b2 (next_exp R i) c Hin2 Hc)).
pose proof (batch_own_cells_within b2 (next_exp R i) c (or_intror Hc)) as [W1 W2].
assert (NF : 8 <= aeval B ly (c_at c) - addr b2).
{ unfold batch_own_cells in Hc. destruct Hc as [<-|[<-|Hc]]; [img_try (unfold addr; cbn; img_lia) | img_try (unfold addr; cbn; img_lia) |].
apply in_map_iff in Hc as ([i' x] & <- & Hix). apply in_combine_l in Hix. apply in_seq in Hix. unfold addr. cbn. img_lia. }
intros j Hj'. img_apply (ok_batch b2); [img_try (img_exact Hin2) | img_try (unfold kBatchBytes; img_lia)].
Qed.
Lemma cells_fs : Forall (cell_holds B ly rd') (fs_cells S').
Proof.
assert (OLDF : Forall (cell_holds B ly rd) (fs_cells X)) by (img_try (old_in; do 5 right; left; img_exact HIN)).
unfold fs_cells in OLDF |- *. rewrite S'_fs. high.
refine (cells_xfer _ _ _ (fun a Ha => ok_static 3 _ a eq_refl ltac:(img_lia) ltac:(img_lia) ltac:(img_lia) Ha) _ OLDF).
unfold cell_in. cbn [fst snd]. unfold kFakeStackSize. fcons. fcons.
img_apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i h] & <- & Hih). apply in_combine_l in Hih. apply in_seq in Hih. cbn. img_lia.
Qed.
Lemma cells_depot : Forall (cell_holds B ly rd') (depot_cells ly S').
Proof.
assert (OLDD : Forall (cell_holds B ly rd) (depot_cells ly X)) by (img_try (old_in; do 6 right; left; img_exact HIN)).
unfold depot_cells, depot_ids, depot_frames in OLDD |- *. rewrite S'_depot. pose proof (aso_cells _ (am_syms _ _ _ _ M)) as AC.
img_apply Forall_forall. intros c Hc. img_apply (cell_xfer _ (proj1 (Forall_forall _ _) OLDD c Hc)). intros j Hj. img_apply ok_below;
destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hj |- *; unfold d_nuniq, d_map1, s_total, s_block0, kLowMemEnd, kHighMemBeg, o_q_cmutex, o_q_bytes in *; tbnum; img_lia.
Qed.
Lemma cells_ialloc : Forall (cell_holds B ly rd') (ialloc_cells B S').
Proof.
assert (OLDI : Forall (cell_holds B ly rd) (ialloc_cells B X)) by (img_try (old_in; do 7 right; left; img_exact HIN)).
unfold ialloc_cells in OLDI |- *. rewrite S'_inited. pose proof (aso_cells _ (am_syms _ _ _ _ M)) as AC. pose proof (aso_ialloc _ (am_syms _ _ _ _ M)) as [I1 I2].
img_apply Forall_forall. intros c Hc. img_apply (cell_xfer _ (proj1 (Forall_forall _ _) OLDI c Hc)). intros j Hj. img_apply ok_below;
destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hj |- *; unfold kLowMemEnd, kHighMemBeg, o_q_cmutex, o_q_bytes in *; tbnum; img_lia.
Qed.
Lemma cells_thread : Forall (cell_holds B ly rd') thread_cells.
Proof.
assert (OLDT : Forall (cell_holds B ly rd) thread_cells) by (img_try (old_in; do 8 right; img_exact HIN)).
unfold thread_cells in OLDT |- *. apply Forall_cons_iff in OLDT as [O1 _]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (cell_xfer _ O1). intros j Hj. cbn in Hj |- *. img_apply ok_T; unfold DT, t_qc, t_unwinding, kThreadObjSize in *; img_lia.
Qed.
Lemma cells_all : Forall (cell_holds B ly rd') (acells B ly S').
Proof.
unfold acells. rewrite !Forall_app. splits.
- img_exact cells_regions.
- img_exact cells_caches.
- img_exact cells_chunks.
- img_exact cells_sec.
- img_exact cells_quar.
- img_exact cells_fs.
- img_exact cells_depot.
- img_exact cells_ialloc.
- img_exact cells_thread.
Qed.
Lemma drain_fin_plist : Forall (cell_holds B ly rd') (batch_cells P).
Proof.
img_apply Forall_forall. intros c Hc. apply In_batch_cells in Hc as (i & b2 & Hi & Hc).
pose proof (nth_error_In _ _ Hi) as HinP. pose proof (In_P _ HinP) as Hin2.
pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wf_quarantine _ _ _ _ _ WF)) b2 Hin2) as [L1 L2]. unfold kBatchSlots in L2.
destruct Hc as [<-|Hc].
- cbn [cell_holds c_at c_val c_w c8 aeval batch_exp]. intros kk Hkk. fold (addr b2). rewrite (NEW_P i b2 Hi kk Hkk).
unfold next_addr, next_exp, addr. destruct (nth_error P (S i)); img_refl.
- img_apply (cell_xfer _ (OLD_batch_cell b2 (next_exp P i) c Hin2 Hc)).
pose proof (batch_own_cells_within b2 (next_exp P i) c (or_intror Hc)) as [W1 W2].
assert (NF : 8 <= aeval B ly (c_at c) - addr b2).
{ unfold batch_own_cells in Hc. destruct Hc as [<-|[<-|Hc]]; [img_try (unfold addr; cbn; img_lia) | img_try (unfold addr; cbn; img_lia) |].
apply in_map_iff in Hc as ([i' x] & <- & Hix). apply in_combine_l in Hix. apply in_seq in Hix. unfold addr. cbn. img_lia. }
intros j Hj'. img_apply (ok_batch b2); [img_try (img_exact Hin2) | img_try (unfold kBatchBytes; img_lia)].
Qed.
Lemma fa' : fa_entries_ok ly rd' S'.
Proof.
intros c i v Hc Hi Hv kk Hkk. rewrite reg' in Hi, Hv. rewrite AGok; [img_try (img_exact (am_fa B ly X rd M c i v Hc Hi Hv kk Hkk))|].
pose proof (wf_classes _ _ _ _ _ WF c Hc) as CL. pose proof (wr_fa_len _ _ _ _ _ _ CL) as FL. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as FB.
img_apply (ok_fa c Hc). img_lia.
Qed.
Lemma flags' : fs_flags_ok ly rd' S'.
Proof.
intros cid pos Hc Hp. rewrite frames'. rewrite AGok; [img_try (img_exact (am_flags B ly X rd M cid pos Hc Hp))|].
pose proof (flag_off_bounds cid pos Hc Hp) as FB. unfold flag_addr, kFakeFlagsOff, kFakeFramesOff in *.
img_apply (ok_static 3 _ _ eq_refl ltac:(img_lia) ltac:(img_lia) ltac:(img_lia)). cbn [fst snd]. unfold kFakeStackSize. img_lia.
Qed.
Lemma depot' : depot_ok B ly rd' S'.
Proof.
pose proof (am_depot B ly X rd M) as (heads & links & D1 & D2 & D3). pose proof (aso_cells _ (am_syms _ _ _ _ M)) as AC.
unfold depot_ok, depot_ids, depot_traces in *. rewrite S'_depot. exists heads, links. split; [|img_try (split; [|img_exact D3])].
- intros b0 Hb. destruct (D1 b0 Hb) as [X1 X2]. split; [img_try (img_exact X1)|]. intros kk Hkk. rewrite AGok; [img_try (img_exact (X2 kk Hkk))|].
img_apply ok_below; unfold d_tab_words, kLowMemEnd, kHighMemBeg, o_q_cmutex, o_q_bytes in *; tbnum; img_lia.
- intros id Hid. destruct (D2 id Hid) as (X1 & X2 & X3). split; [img_try (img_exact X1)|].
assert (NB : Z.of_nat (length (st_depot X)) <= 4096).
{ pose proof (wf_depot _ _ _ _ _ WF) as [ND INC]. pose proof (NoDup_incl_length ND INC). destruct (am_universe B ly X rd M) as (U1 & _). unfold DEPOT_MAX in U1. img_lia. }
high.
pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) (ly_NB ly, kNodesBlockSize) ltac:(img_try (unfold owned_extents; cbn; tauto))) as [N1 N2]. cbn [fst snd] in N1, N2.
assert (OKN : forall kk, 0 <= kk < 16 -> ok (ly_NB ly + 16 * id + kk)).
{ intros kk Hkk. img_apply (ok_static 4 _ _ eq_refl ltac:(img_lia) ltac:(img_lia) ltac:(img_lia)). cbn [fst snd]. unfold kNodesBlockSize. img_lia. }
split; intros kk Hkk; rewrite AGok; auto; [img_try (img_apply OKN; img_lia)|].
replace (ly_NB ly + 16 * id + 8 + Z.of_nat kk) with (ly_NB ly + 16 * id + (8 + Z.of_nat kk)) by img_lia. img_apply OKN. img_lia.
Qed.
Lemma fa_poison_high : forall lo len g, In (lo, len) (fa_poison_ranges ly X) -> lo <= g < lo + len -> 4096 <= g /\ g < ASAN_CEIL.
Proof. geo.
intros lo len g Hin Hg. unfold fa_poison_ranges in Hin. apply in_app_iff in Hin as [Hin|Hin].
- apply in_flat_map in Hin as (c & Hc & Hin). apply zseq_In in Hc.
pose proof (region_in_prim ly c LO ltac:(img_lia)) as (R1 & R2 & R3 & R4 & R5).
pose proof (wf_classes _ _ _ _ _ WF c ltac:(img_lia)) as CL.
pose proof (wr_alloc _ _ _ _ _ _ CL) as A1. pose proof (wr_fa _ _ _ _ _ _ CL) as [A2 _]. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as A3.
pose proof (mapped_user_bound (as_universe B) 0 0 0 X c WF ltac:(img_lia)) as MB. unfold kUserMapSize, EV_MAX, kFreeArrayMax in *.
unfold fa_base, kFreeArrayOffset in Hin. unfold region_base in *.
unfold kHighMemBeg in *. destruct Hin as [E|[E|[]]]; injection E as <- <-; img_lia.
- pose proof (proj1 (Forall_forall _ _) (proj1 (am_placed _ _ _ _ M)) (lo, len) Hin) as (_ & [I1 I2] & I3). cbn [fst snd] in I1, I2, I3. ceil. unfold ASAN_CEIL, kHighMemBeg, kLowShadowBeg in *. img_lia.
Qed.
Lemma shadow' : shadow_ok B ly rd' S'.
Proof.
intros g v Hg8 HS'. unfold ashadow in HS'. rewrite S'_chunks, fa_poison' in HS'. fold (ashadow B ly X g) in HS'.
rewrite AGok; [img_try (img_exact (am_shadow B ly X rd M g v Hg8 HS'))|].
pose proof (YG0z.ashadow_low B ly X rd g v M HS') as [LO1 LO2].
img_apply ok_shb. split; [|img_try (img_exact LO2)]. clear - LO1. unfold SHADOW_OFF, kLowShadowBeg in *. img_lia.
Qed.
Lemma zshadow' : zshadow_ok B ly rd'.
Proof.
pose proof (am_zshadow B ly X rd M) as ZS. unfold zshadow_ok in ZS |- *. img_apply Forall_forall. intros r Hr i Hi.
pose proof (proj1 (Forall_forall _ _) ZS r Hr i Hi) as Z0. unfold shadow_of_addr in Z0 |- *. change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)) in Z0 |- *.
rewrite AGok; [img_try (img_exact Z0)|]. pose proof (aso_cells _ (am_syms _ _ _ _ M)) as AC.
pose proof (proj1 (Forall_forall _ _) (owned_shadow_ranges B ly X rd M) r ltac:(img_try (rewrite !in_app_iff; tauto))) as (K1 & K2 & K3).
assert (DM : i < (snd r + 7) / 8). { pose proof (Z.div_le_mono (8 * i + 8) (snd r + 7) 8 ltac:(img_lia) ltac:(img_lia)) as DX. replace (8 * i + 8) with ((i + 1) * 8) in DX by img_lia. rewrite Z_div_mult in DX by img_lia. img_lia. }
pose proof (owned_shadow_bound B ly X rd (shadow_addr (fst r) + i) M ltac:(img_try (img_apply Exists_exists; exists r; split; [img_try (rewrite !in_app_iff; tauto) | img_try (unfold in_zr; cbn [fst snd]; img_lia)]))) as [OB1 OB2].
img_apply ok_shb. split; [img_try (clear - OB1; unfold SHADOW_OFF, kLowShadowBeg in *; img_lia) | img_try (img_exact OB2)].
Qed.
Lemma vis_keep : forall L, Forall (range_vis B ly rd) L -> Forall (range_vis B ly rd') L.
Proof. intros L H. img_exact (Forall_range_vis_keep B ly rd rd' L VIS H). Qed.
Lemma junk' : Forall (range_vis B ly rd') (ajunk B ly S').
Proof.
pose proof (am_junk B ly X rd M) as J.
unfold ajunk in J |- *. unfold quar_junk in J |- *. rewrite all_batches_S'. rewrite all_batches_X in J.
unfold sec_junk in J |- *. rewrite S'_sec_arr, S'_sec_res, S'_chunks. unfold cache_junk in J |- *. rewrite S'_cinit.
replace (flat_map (fun c : Z => if st_cache_inited X then [(AT (t_cache + 80 * c + 16 + 4 * Z.of_nat (length (pc_chunks (cache S' c)))), 64 - 4 * Z.of_nat (length (pc_chunks (cache S' c))))] else []) (zseq 1 31))
with (flat_map (fun c : Z => if st_cache_inited X then [(AT (t_cache + 80 * c + 16 + 4 * Z.of_nat (length (pc_chunks (cache X c)))), 64 - 4 * Z.of_nat (length (pc_chunks (cache X c))))] else []) (zseq 1 31))
by img_refl.
apply Forall_cons_iff in J as [J1 J]. apply Forall_cons_iff in J as [J2 J].
apply Forall_app in J as [J3 J]. apply Forall_app in J as [J4 J]. apply Forall_app in J as [J5 J]. apply Forall_app in J as [J6 J]. apply Forall_app in J as [J7 J].
img_apply Forall_cons; [img_try (intros i Hi; img_apply VIS; img_exact (J1 i Hi))|].
img_apply Forall_cons; [img_try (intros i Hi; img_apply VIS; img_exact (J2 i Hi))|].
img_apply Forall_app. split; [img_try (img_exact (vis_keep _ J3))|].
img_apply Forall_app. split; [img_try (img_exact (vis_keep _ J4))|].
img_apply Forall_app. split; [img_try (img_exact (vis_keep _ J5))|].
img_apply Forall_app. split; [img_try (img_exact (vis_keep _ J6))|].
img_apply Forall_app. split.
{
img_apply vis_keep. img_apply Forall_forall. intros r Hr. img_apply (proj1 (Forall_forall _ _) J7). apply in_flat_map in Hr as (b2 & Hb2 & Hr).
img_apply in_flat_map. exists b2. split; [img_try (rewrite <- all_batches_X; img_exact (In_R _ Hb2)) | img_try (img_exact Hr)]. }
img_exact (vis_keep _ J).
Qed.
Lemma areas' : Forall (range_vis B ly rd') (aareas S').
Proof. pose proof (am_areas B ly X rd M) as A. unfold aareas, reg in A |- *. rewrite S'_regions, S'_sec_res, S'_chunks. img_exact (vis_keep _ A). Qed.
Lemma client' : Forall (range_vis B ly rd') (aclient S').
Proof. pose proof (am_client B ly X rd M) as A. unfold aclient in A |- *. rewrite frames', S'_chunks. img_exact (vis_keep _ A). Qed.
Lemma placed' : sec_placed ly S'.
Proof. unfold sec_placed. rewrite sec_extents'. img_exact (am_placed B ly X rd M). Qed.
Theorem drain_fin_ARm : ARm B ly S' rd'.
Proof.
constructor.
- img_exact WS'.
- img_exact (am_universe B ly X rd M).
- img_exact (am_syms B ly X rd M).
- img_exact LO.
- img_exact placed'.
- img_exact CONST'.
- img_exact (am_const_owned B ly X rd M).
- img_exact cells_all.
- img_exact fa'.
- img_exact flags'.
- img_exact depot'.
- img_exact shadow'.
- img_exact zshadow'.
- img_exact junk'.
- img_exact areas'.
- img_exact client'.
- pose proof (am_zero B ly X rd M) as ZR. img_apply Forall_forall. intros r Hr i Hi. rewrite AGok; [img_try (img_exact (proj1 (Forall_forall _ _) ZR r Hr i Hi))|].
pose proof (aso_cells _ (am_syms _ _ _ _ M)) as AC. pose proof (aso_ialloc _ (am_syms _ _ _ _ M)) as [I1 I2]. img_apply ok_below;
unfold ialloc_zero in Hr; destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in Hi |- *; unfold kLowMemEnd, kHighMemBeg, o_q_cmutex, o_q_bytes in *; tbnum; img_lia.
- img_exact (am_tsd B ly X rd M).
- img_exact (am_static_img B ly X rd M).
Qed.
Lemma sec_live' : sec_live_bytes S' = sec_live_bytes X. Proof. geo. img_refl. Qed.
Lemma prim_committed' : prim_committed S' = prim_committed X. Proof. geo. img_refl. Qed.
Lemma ALedger_S' : forall segs md, ALedger segs ly X md -> ALedger segs ly S' md.
Proof. geo. intros segs md L. destruct L as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10]. constructor; assumption. Qed.
Lemma abudget_S' : abudget S' = abudget X. Proof. geo. img_refl. Qed.

Lemma D_owned : forall a, 0 <= a -> D a -> aowned B ly X a \/ DS a.
Proof. geo.
intros a Ha0 HD. high. destruct HD as [Y|[Y|[[NE Y]|[(b2 & Hb2 & Y)|Y]]]].
- left. eapply (own_core B ly X rd (T, kThreadObjSize) a M); [img_try (unfold core_extents; cbn; tauto)|]. cbn [fst snd]. unfold DT, t_qc, kThreadObjSize in *. img_lia.
- left. img_apply (inst_owned_range B ly X rd M). unfold DQ, o_q_cmutex, o_q_size in *. img_lia.
- left. destruct (rev G) as [|lb initr] eqn:Hrev.
+ exfalso. img_apply NE. rewrite <- (rev_involutive G), Hrev. img_refl.
+ destruct (glast_in lb initr Hrev) as (Hin & EQ & _). rewrite EQ in Y. unfold addr in Y. eapply own_batch; [img_try (img_exact M) | img_try (img_exact Hin) | img_try (unfold kBatchBytes; img_lia)].
- left. unfold addr in Y. eapply own_batch; [img_try (img_exact M) | img_try (img_exact (In_P _ Hb2)) | img_try (unfold kBatchBytes; img_lia)].
- right. img_exact Y.
Qed.
End m.
End f.
