(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YP09 YK04 YA0i YA0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0t YG0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AF0m AF0x AFl0 AFeq AFew AFex.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition batch_own_cells (b2 : batch) (nx : aexp) : list acell :=
c8 (batch_exp b2) nx :: z8 (aoff (batch_exp b2) 8) (b_bytes b2) :: z8 (aoff (batch_exp b2) 16) (Z.of_nat (length (b_items b2)))
:: map (fun iv => c8 (aoff (batch_exp b2) (24 + 8 * Z.of_nat (fst iv))) (sptr_exp (ck_hdr (snd iv)))) (combine (seq 0 (length (b_items b2))) (b_items b2)).
Definition next_exp (l : list batch) (i : nat) : aexp := match nth_error l (S i) with Some b3 => batch_exp b3 | None => ANum 0 end.
Lemma In_batch_cells : forall l c, In c (batch_cells l) <-> exists i b2, nth_error l i = Some b2 /\ In c (batch_own_cells b2 (next_exp l i)).
Proof.
induction l as [|b t IH]; intros c.
- cbn. split; [intros [] | intros (i & b2 & H & _)]. destruct i; discriminate.
- cbn [batch_cells]. assert (NX : next_exp (b :: t) 0 = match t with [] => ANum 0 | b' :: _ => batch_exp b' end) by (unfold next_exp; destruct t; reflexivity).
split.
+ intros H. change (In c (batch_own_cells b (match t with [] => ANum 0 | b' :: _ => batch_exp b' end) ++ batch_cells t)) in H.
apply in_app_iff in H as [H|H].
* exists 0%nat, b. split; [reflexivity|]. rewrite NX. exact H.
* apply IH in H as (i & b2 & H1 & H2). exists (S i), b2. split; [exact H1|]. unfold next_exp in H2 |- *. cbn [nth_error]. exact H2.
+ intros (i & b2 & H1 & H2). change (In c (batch_own_cells b (match t with [] => ANum 0 | b' :: _ => batch_exp b' end) ++ batch_cells t)).
apply in_app_iff. destruct i as [|i].
* cbn in H1. injection H1 as <-. left. rewrite <- NX. exact H2.
* right. apply IH. exists i, b2. split; [exact H1|]. unfold next_exp in H2 |- *. exact H2.
Qed.
Lemma next_exp_app_lt : forall l bn i, (S i < length l)%nat -> next_exp (l ++ [bn]) i = next_exp l i.
Proof. intros l bn i Hi. unfold next_exp. rewrite nth_error_app1 by exact Hi. reflexivity. Qed.
Lemma next_exp_app_last : forall l bn i, (S i = length l)%nat -> next_exp (l ++ [bn]) i = batch_exp bn.
Proof. intros l bn i Hi. unfold next_exp. rewrite nth_error_app2 by lia. rewrite Hi, Nat.sub_diag. reflexivity. Qed.
Lemma next_exp_app_new : forall l bn, next_exp (l ++ [bn]) (length l) = ANum 0.
Proof. intros l bn. unfold next_exp. rewrite nth_error_app2 by lia. replace (S (length l) - length l)%nat with 1%nat by lia. reflexivity. Qed.
Lemma next_exp_last : forall l i, (S i = length l)%nat -> next_exp l i = ANum 0.
Proof. intros l i Hi. unfold next_exp. rewrite (proj2 (nth_error_None l (S i))) by lia. reflexivity. Qed.
Section n.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (X : astate) (rd rd' : reader).
Hypothesis M : ARm B ly X rd.
Variable k : chunk.
Hypothesis Hk : In k (st_chunks X).
Hypothesis Hst : ck_state k = CQuarantined.
Hypothesis Hnq : ~ In (ck_beg k) (map ck_beg (q_items X)).
Hypothesis Hnb : need_new_batch (st_qthread X) = true.
Hypothesis Hci : st_cache_inited X = true.
Variable l : list Z.
Hypothesis Hl : pc_chunks (cache X kBatchClass) = l.
Hypothesis Hlne : l <> [].
Let coff : Z := last l 0.
Let nb : Z := region_off kBatchClass + coff.
Let bn : batch := mkBatch nb [k].
Let Xp : astate := upd_pc kBatchClass (mkPC (pc_max (cache X kBatchClass)) (removelast l)) X.
Definition S' : astate := set_qthread (qc_push (st_qthread X) k (Some nb)) Xp.
Local Notation T := (ly_T ly).
Local Notation u := (sptr_addr B ly (ck_user k)).
Local Notation nn := (ck_n k).
Local Notation NBv := (ly_space ly + nb).
Definition QLv : Z := match rev (qc_list (st_qthread X)) with [] => 0 | lb :: _ => ly_space ly + b_self lb end.
Variable sp : Z.
Hypothesis Hsp : ly_stk_lo ly + QSTACK <= sp <= ly_stk_hi ly.
Hypothesis IMG : img_cover ly.
Definition DT (a : Z) : Prop :=
(T + t_qc <= a < T + t_qc + 32) \/ (T + t_cache + 1920 <= a < T + t_cache + 1924) \/ (T + t_cache_stats + 16 <= a < T + t_cache_stats + 24).
Definition DN (a : Z) : Prop := NBv <= a < NBv + 32.
Definition DL (a : Z) : Prop := qc_list (st_qthread X) <> [] /\ QLv <= a < QLv + 8.
Definition DS (a : Z) : Prop := sp - QSTACK <= a < sp.
Definition D (a : Z) : Prop := DT a \/ DN a \/ DL a \/ DS a.
Hypothesis AG : forall a, 0 <= a < 2 ^ 64 -> ~ D a -> rd' a = rd a.
Hypothesis VIS : forall a, rd a <> None -> rd' a <> None.
Hypothesis NEW_qs : forall i, (i < 8)%nat -> rd' (T + t_qc + Z.of_nat i) = Some (YG0f.le_byte (Z.of_nat (length (qc_list (st_qthread X))) + 1) 8 i).
Hypothesis NEW_qf : forall i, (i < 8)%nat -> rd' (T + t_qc + 8 + Z.of_nat i) =
Some (YG0f.le_byte (match qc_list (st_qthread X) with [] => NBv | b0 :: _ => ly_space ly + b_self b0 end) 8 i).
Hypothesis NEW_ql : forall i, (i < 8)%nat -> rd' (T + t_qc + 16 + Z.of_nat i) = Some (YG0f.le_byte NBv 8 i).
Hypothesis NEW_qb : forall i, (i < 8)%nat -> rd' (T + t_qc + 24 + Z.of_nat i) = Some (YG0f.le_byte (qc_bytes (st_qthread X) + nn + kBatchBytes) 8 i).
Hypothesis NEW_cnt : forall i, (i < 4)%nat -> rd' (T + t_cache + 1920 + Z.of_nat i) = Some (YG0f.le_byte (Z.of_nat (length l) - 1) 4 i).
Hypothesis NEW_n0 : forall i, (i < 8)%nat -> rd' (NBv + Z.of_nat i) = Some (YG0f.le_byte 0 8 i).
Hypothesis NEW_n8 : forall i, (i < 8)%nat -> rd' (NBv + 8 + Z.of_nat i) = Some (YG0f.le_byte (nn + kBatchBytes) 8 i).
Hypothesis NEW_n16 : forall i, (i < 8)%nat -> rd' (NBv + 16 + Z.of_nat i) = Some (YG0f.le_byte 1 8 i).
Hypothesis NEW_n24 : forall i, (i < 8)%nat -> rd' (NBv + 24 + Z.of_nat i) = Some (YG0f.le_byte (u - 16) 8 i).
Hypothesis NEW_lnext : forall lb initr, rev (qc_list (st_qthread X)) = lb :: initr ->
forall i, (i < 8)%nat -> rd' (ly_space ly + b_self lb + Z.of_nat i) = Some (YG0f.le_byte NBv 8 i).
Hypothesis CONST' : Forall (cell_holds B ly rd') (as_const B ly).
Ltac drop_mem := clear AG VIS NEW_qs NEW_qf NEW_ql NEW_qb NEW_cnt NEW_n0 NEW_n8 NEW_n16 NEW_n24 NEW_lnext CONST'.
Ltac geo := drop_mem.
Let WF : Wf (as_universe B) X := am_wf B ly X rd M.
Let LO : layout_ok ly := am_layout B ly X rd M.
Lemma S'_regions : st_regions S' = st_regions X.   Proof. geo. reflexivity. Qed.
Lemma S'_chunks : st_chunks S' = st_chunks X.      Proof. geo. reflexivity. Qed.
Lemma S'_secs : st_secs S' = st_secs X.            Proof. geo. reflexivity. Qed.
Lemma S'_sec_arr : st_sec_arr S' = st_sec_arr X.   Proof. geo. reflexivity. Qed.
Lemma S'_sec_res : st_sec_reserved S' = st_sec_reserved X. Proof. geo. reflexivity. Qed.
Lemma S'_fs : st_fs S' = st_fs X.                  Proof. geo. reflexivity. Qed.
Lemma S'_qglobal : st_qglobal S' = st_qglobal X.   Proof. geo. reflexivity. Qed.
Lemma S'_depot : st_depot S' = st_depot X.         Proof. geo. reflexivity. Qed.
Lemma S'_cinit : st_cache_inited S' = true.        Proof. geo. cbn. exact Hci. Qed.
Lemma S'_inited : st_internal_inited S' = st_internal_inited X. Proof. geo. reflexivity. Qed.
Lemma S'_nev : st_nev S' = st_nev X.               Proof. geo. reflexivity. Qed.
Lemma S'_qthread : st_qthread S' = qc_push (st_qthread X) k (Some nb). Proof. geo. reflexivity. Qed.
Lemma reg' : forall c, reg S' c = reg X c.         Proof. geo. intros c. reflexivity. Qed.
Lemma frames' : frames S' = frames X.              Proof. geo. reflexivity. Qed.
Lemma HLc : (Z.to_nat kBatchClass < length (st_cache X))%nat.
Proof. geo. rewrite (wf_len_cache _ _ _ _ _ WF). unfold kBatchClass. cbn. lia. Qed.
Lemma cache' : forall c, 0 <= c -> c <> kBatchClass -> cache S' c = cache X c.
Proof. geo. intros c Hc Hne'. unfold S'. cbn [cache set_qthread]. unfold Xp, upd_pc. apply cache_upd_other; [unfold kBatchClass; lia | exact Hc | intros E; exact (Hne' (eq_sym E))]. Qed.
Lemma cache24' : cache S' kBatchClass = mkPC (pc_max (cache X kBatchClass)) (removelast l).
Proof. geo. unfold S'. cbn [cache set_qthread]. unfold Xp. apply cache_upd_pc; [unfold kBatchClass; lia | exact HLc]. Qed.
Lemma qlist' : qc_list (st_qthread S') = qc_list (st_qthread X) ++ [bn]. Proof. geo. reflexivity. Qed.
Lemma qbytes' : qc_bytes (st_qthread S') = qc_bytes (st_qthread X) + nn + kBatchBytes. Proof. geo. reflexivity. Qed.
Lemma all_batches_S' : all_batches S' = (qc_list (st_qthread X) ++ [bn]) ++ qc_list (st_qglobal X).
Proof. geo. unfold all_batches. rewrite qlist', S'_qglobal. reflexivity. Qed.
Lemma sec_extents' : sec_extents ly S' = sec_extents ly X. Proof. geo. reflexivity. Qed.
Lemma asecA_S' : forall A, asecA ly X A -> asecA ly S' A.
Proof. intros A H e He. rewrite sec_extents' in He. exact (H e He). Qed.
Lemma fa_poison' : fa_poison_ranges ly S' = fa_poison_ranges ly X. Proof. geo. reflexivity. Qed.
Lemma POP : WfP (as_universe B) 0 0 0 Xp /\ 0 <= coff < rg_alloc_user (reg X kBatchClass) /\ coff mod class_size kBatchClass = 0 /\
~ In coff (class_elems Xp kBatchClass).
Proof. geo. exact (pop_ok _ 0 0 0 X kBatchClass l WF ltac:(unfold kBatchClass; lia) Hci Hl Hlne). Qed.
Hypothesis Hbev : Z.of_nat (length (all_batches X)) + 1 <= st_nev X.
Hypothesis Hpev : prim_user_mapped X + kUserMapSize <= kUserMapSize * st_nev X.
Lemma WfP_reslack : forall U pp cc bb pp' bb' s, WfP U pp cc bb s -> 0 <= pp' -> 0 <= bb' ->
prim_user_mapped s + kUserMapSize * pp' <= kUserMapSize * st_nev s -> Z.of_nat (length (all_batches s)) + bb' <= st_nev s ->
(forall c, 1 <= c <= 31 -> fa_room (rg_alloc_user (reg s c)) (length (class_elems s c)) (cc + bslack c bb' + 2 * (EV_MAX - st_nev s)) (rg_mapped_fa (reg s c))) ->
WfP U pp' cc bb' s.
Proof. clear. intros U pp cc bb pp' bb' s W H1 H2 H3 H4 H5. wf_fields W. constructor; wf_easy; try lia; try exact H5. Qed.
Lemma WS' : Wf (as_universe B) S'.
Proof. geo.
pose proof POP as (W1 & C1 & C2 & C3).
assert (W1' : WfP (as_universe B) 0 0 1 Xp).
{ apply (WfP_reslack _ 0 0 0 0 1 Xp W1 ltac:(lia) ltac:(lia)); [pose proof (wf_prim_ev _ _ _ _ _ W1); lia| |].
- change (all_batches Xp) with (all_batches X). change (st_nev Xp) with (st_nev X). exact Hbev.
-
intros c Hc. change (reg Xp c) with (reg X c). change (st_nev Xp) with (st_nev X).
assert (HLc : (Z.to_nat kBatchClass < length (st_cache X))%nat) by (rewrite (wf_len_cache _ _ _ _ _ WF); unfold kBatchClass; lia).
destruct (Z.eq_dec kBatchClass c) as [<-|Hne].
+ eapply fa_room_xfer; [exact (wf_fa_room _ _ _ _ _ WF kBatchClass Hc) | | apply Z.le_refl].
unfold Xp. rewrite (class_elems_upd_pc_same kBatchClass _ X ltac:(unfold kBatchClass; lia) HLc). cbn [pc_chunks].
unfold class_elems. rewrite Hl, !length_app, (removelast_length l Hlne), !bslack_24.
assert (1 <= length l)%nat by (destruct l; [congruence | cbn; lia]). lia.
+ eapply fa_room_xfer; [exact (wf_fa_room _ _ _ _ _ W1 c Hc) | | apply Z.le_refl].
change (reg Xp c) with (reg X c). change (st_nev Xp) with (st_nev X). rewrite !bslack_other by lia. lia. }
pose proof (WfP_qpush _ 0 0 1 Xp k (Some nb) W1' ltac:(lia) Hk Hst Hnq
ltac:(exists coff; repeat split; [exact (proj1 C1) | exact (proj2 C1) | exact C2 | exact C3]) Hci (fun _ => Hnb)  ) as W2.
unfold Wf, S'. replace (1 - 1) with 0 in W2 by lia. exact W2.
Qed.
Lemma nb_geom : ly_space ly + nb = region_base ly kBatchClass + coff /\ 0 <= coff /\ coff mod kBatchBytes = 0 /\
coff + kBatchBytes <= rg_alloc_user (reg X kBatchClass) /\
rg_alloc_user (reg X kBatchClass) <= rg_mapped_user (reg X kBatchClass) <= 2 ^ 31 /\
In coff (pc_chunks (cache X kBatchClass)) /\ ~ In coff (batch_offs X kBatchClass) /\ ~ In coff (chunk_offs X kBatchClass).
Proof. geo.
pose proof POP as (W1 & [C0 C1] & C2 & C3). pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
pose proof (wr_alloc _ _ _ _ _ _ CL) as AL. pose proof (wr_alloc_al _ _ _ _ _ _ CL) as AA.
pose proof (mapped_user_bound (as_universe B) 0 0 0 X kBatchClass WF ltac:(unfold kBatchClass; lia)) as MB.
assert (CS : class_size kBatchClass = 8192) by reflexivity. rewrite CS in C2, AA. unfold kUserMapSize, EV_MAX in MB. unfold kBatchBytes.
assert (XB : coff + 8192 <= rg_alloc_user (reg X kBatchClass)).
{ apply Z.mod_divide in C2 as [q1 Hq1]; [|lia]. apply Z.mod_divide in AA as [q2 Hq2]; [|lia]. assert (q1 < q2) by nia. nia. }
pose proof (wr_nodup _ _ _ _ _ _ CL) as ND.
splits; try lia; try (unfold region_base; subst nb; lia).
+ rewrite Hl. subst coff. rewrite <- (removelast_app_last l 0 Hlne) at 2. apply in_app_iff. right. left. reflexivity.
+ intros Hin. apply C3. unfold class_elems. rewrite !in_app_iff. right. right. right. exact Hin.
+ intros Hin. apply C3. unfold class_elems. rewrite !in_app_iff. right. right. left. exact Hin.
Qed.
Lemma batch_geom : forall b2, In b2 (all_batches X) ->
exists x, ly_space ly + b_self b2 = region_base ly kBatchClass + x /\ 0 <= x /\ x mod kBatchBytes = 0 /\
x + kBatchBytes <= rg_alloc_user (reg X kBatchClass) /\ rg_alloc_user (reg X kBatchClass) <= rg_mapped_user (reg X kBatchClass) <= 2 ^ 31 /\
In x (batch_offs X kBatchClass).
Proof. geo.
intros b2 Hb2. pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
set (x := b_self b2 - region_off kBatchClass).
assert (INB : In x (batch_offs X kBatchClass)) by (rewrite batch_offs_24; apply in_map_iff; exists b2; auto).
pose proof (proj1 (Forall_forall _ _) (wr_elems _ _ _ _ _ _ CL) x ltac:(rewrite !in_app_iff; tauto)) as [X1 X2].
pose proof (wr_alloc _ _ _ _ _ _ CL) as AL. pose proof (wr_alloc_al _ _ _ _ _ _ CL) as AA.
pose proof (mapped_user_bound (as_universe B) 0 0 0 X kBatchClass WF ltac:(unfold kBatchClass; lia)) as MB.
assert (CS : class_size kBatchClass = 8192) by reflexivity. rewrite CS in X2, AA. unfold kUserMapSize, EV_MAX in MB. unfold kBatchBytes.
assert (XB : x + 8192 <= rg_alloc_user (reg X kBatchClass)).
{ apply Z.mod_divide in X2 as [q Hq]; [|lia]. apply Z.mod_divide in AA as [q' Hq']; [|lia]. assert (q < q') by nia. nia. }
exists x. splits; try assumption; try lia. unfold region_base. subst x. lia.
Qed.
Lemma batches_nodup : List.NoDup (map b_self (all_batches X)).
Proof. geo.
pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
pose proof (wr_nodup _ _ _ _ _ _ CL) as ND. rewrite app_assoc in ND. apply NoDup_app_iff in ND as (_ & ND & _). apply NoDup_app_iff in ND as (_ & ND & _).
rewrite batch_offs_24 in ND.
clear - ND. induction (all_batches X) as [|x t IH]; cbn in *; [constructor|].
inversion ND as [|y l N1 N2]; subst. constructor; [|exact (IH N2)].
intros Hin. apply N1. apply in_map_iff in Hin as (x' & E & Hx'). apply in_map_iff. exists x'. split; [lia | exact Hx'].
Qed.
Lemma batches_apart : forall b1 b2, In b1 (all_batches X) -> In b2 (all_batches X) -> b_self b1 <> b_self b2 ->
zdisjoint (ly_space ly + b_self b1, kBatchBytes) (ly_space ly + b_self b2, kBatchBytes).
Proof. geo.
intros b1 b2 H1 H2 NE. destruct (batch_geom b1 H1) as (x1 & E1 & P1 & A1 & _). destruct (batch_geom b2 H2) as (x2 & E2 & P2 & A2 & _).
unfold zdisjoint, kBatchBytes in *. cbn [fst snd]. rewrite E1, E2.
apply Z.mod_divide in A1 as [q1 Hq1]; [|lia]. apply Z.mod_divide in A2 as [q2 Hq2]; [|lia].
assert (q1 <> q2) by (intros ->; apply NE; lia). nia.
Qed.
Lemma batch_vs_chunk : forall b2 x, In b2 (all_batches X) -> In x (st_chunks X) ->
zdisjoint (ly_space ly + b_self b2, kBatchBytes) (ck_base B ly x, ck_extent x).
Proof. geo.
intros b2 x Hb2 Hx. destruct (batch_geom b2 Hb2) as (xb & Eb & Pb & Ab & Ub & [AU MU] & INB).
pose proof (chunk_facts B ly X rd x M Hx) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
pose proof (wr_nodup _ _ _ _ _ _ CL) as ND. rewrite app_assoc in ND. apply NoDup_app_iff in ND as (_ & ND & _). apply NoDup_app_iff in ND as (_ & _ & NDx).
unfold zdisjoint. cbn [fst snd]. rewrite Eb.
destruct (ck_beg x) as [|o|r o|c p] eqn:Ebx; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & Gxm & Gxs & Gal).
destruct (Z.eq_dec (prim_class o) kBatchClass) as [Ec|Hc].
+ pose proof (In_chunk_offs X x o Hx Ebx) as IK. rewrite Ec in *. set (xk := o - region_off kBatchClass) in *.
assert (CS : class_size kBatchClass = 8192) by reflexivity. rewrite CS in *.
assert (xk <> xb). { intros E. apply (NDx xk); [exact IK | rewrite E; exact INB]. }
unfold kBatchBytes in *. apply Z.mod_divide in Gxm as [q1 Hq1]; [|lia]. apply Z.mod_divide in Ab as [q2 Hq2]; [|lia].
assert (q1 <> q2) by (intros E; subst; lia). nia.
+ pose proof (region_in_prim ly (prim_class o) LO ltac:(lia)) as (R1' & R2' & _).
unfold region_base, kBatchBytes in *. rewrite !region_off_eq in * by (unfold kBatchClass; lia). unfold kBatchClass in *.
destruct (Z.lt_ge_cases (prim_class o) 24).
* pose proof (Z.mul_le_mono_nonneg_r (prim_class o + 1) 24 (2 ^ 32) ltac:(lia) ltac:(lia)). lia.
* pose proof (Z.mul_le_mono_nonneg_r (24 + 1) (prim_class o) (2 ^ 32) ltac:(lia) ltac:(lia)). lia.
- destruct GG as (-> & _ & Gbase & Gext & Gin & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & _).
pose proof (pairwise_In zdisjoint _ (ly_sec ly r, sec_map_size (ck_req x)) (ly_prim ly, kPrimResvSize) (sec_extents ly X) (static_extents ly) eq_refl (proj2 (am_placed _ _ _ _ M)) Gin
ltac:(unfold static_extents, owned_extents; cbn; tauto)) as DJ.
unfold zdisjoint, kPage, kBatchBytes in *. cbn [fst snd] in DJ. unfold region_base in *. lia.
Qed.
Lemma SX : forall i j x y, nth_error (static_extents ly) i = Some x -> nth_error (static_extents ly) j = Some y -> i <> j -> zdisjoint x y.
Proof. geo.
intros i j x y Hi Hj Hne. destruct (Nat.lt_ge_cases i j).
- exact (pairwise_nth zdisjoint _ i j x y (lo_disj _ LO) Hi Hj H).
- apply zdisjoint_sym. apply (pairwise_nth zdisjoint _ j i y x (lo_disj _ LO) Hj Hi). lia.
Qed.
Lemma SECX : forall e j y, In e (sec_extents ly X) -> nth_error (static_extents ly) j = Some y -> zdisjoint e y.
Proof. geo.
intros e j y He Hj. eapply (pairwise_In zdisjoint _ e y (sec_extents ly X) (static_extents ly) eq_refl (proj2 (am_placed _ _ _ _ M)) He).
eapply nth_error_In. exact Hj.
Qed.
Lemma ext_zone : forall y, In y (st_chunks X) ->
(exists c, 1 <= c <= 30 /\ region_base ly c <= ck_base B ly y /\ ck_base B ly y + ck_extent y <= region_base ly c + 2 ^ 31 /\
ly_prim ly <= region_base ly c /\ region_base ly c + 2 ^ 32 <= ly_prim ly + kPrimResvSize) \/
(exists r, ck_beg y = PSec r kPage /\ ck_base B ly y = ly_sec ly r + kPage /\ In (ly_sec ly r, ck_extent y + kPage) (sec_extents ly X)).
Proof. geo.
intros y Hy. pose proof (chunk_facts B ly X rd y M Hy) as (G1 & G2 & _ & _ & _ & _ & _ & _ & GG).
destruct (ck_beg y) as [|o|r o|c p]; try solve [destruct GG].
- left. cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal & Gm).
pose proof (region_in_prim ly (prim_class o) LO ltac:(lia)) as (R1 & R2 & _). exists (prim_class o). splits; lia.
- right. destruct GG as (-> & _ & Gbase & Gext & Gin & _). exists r. splits; [reflexivity | lia |].
replace (ck_extent y + kPage) with (sec_map_size (ck_req y)) by lia. exact Gin.
Qed.
Lemma anyX : forall y j e, In y (st_chunks X) -> nth_error (static_extents ly) j = Some e -> (j <> 0)%nat -> zdisjoint (ck_base B ly y, ck_extent y) e.
Proof. geo.
intros y j e Hy Hj Hne. destruct (ext_zone y Hy) as [(c & Hc & X1 & X2 & X3 & X4)|(r & Ebk & Xb & Xin)].
- pose proof (SX 0 j _ e eq_refl Hj ltac:(lia)) as DJ. unfold zdisjoint in DJ |- *. cbn [fst snd] in DJ |- *. lia.
- pose proof (SECX _ j e Xin Hj) as DJ. unfold zdisjoint, kPage in *. cbn [fst snd] in DJ |- *. lia.
Qed.
Lemma KX : forall j y, nth_error (static_extents ly) j = Some y -> (j <> 0)%nat -> zdisjoint (ck_base B ly k, ck_extent k) y.
Proof. geo. intros j y Hj Hne. exact (anyX k j y Hk Hj Hne). Qed.
Lemma secmap_vs_chunk : forall x y r o, In x (st_chunks X) -> In y (st_chunks X) -> ck_beg x = PSec r o -> ck_beg x <> ck_beg y ->
zdisjoint (ly_sec ly r, sec_map_size (ck_req x)) (ck_base B ly y, ck_extent y).
Proof. geo.
intros x y r o Hx Hy Ebx Hne.
pose proof (chunk_facts B ly X rd x M Hx) as (_ & _ & _ & _ & _ & _ & _ & _ & GG). rewrite Ebx in GG. destruct GG as (-> & _ & Gbase & Gext & Gin & _).
pose proof (chunk_facts B ly X rd y M Hy) as (_ & _ & _ & _ & _ & _ & _ & _ & GK).
destruct (ck_beg y) as [|o'|r' o'|c' p'] eqn:Eby; try solve [destruct GK].
- apply zdisjoint_sym. exact (prim_vs_secmap B ly X rd y o' _ M Hy Eby Gin).
- destruct GK as (-> & _ & Kbase & Kext & Kin & _).
pose proof (secmaps_disjoint B ly X rd x y r kPage r' kPage M Hx Hy Ebx Eby ltac:(rewrite Eby; exact Hne)) as DJ. unfold zdisjoint, kPage in *. cbn [fst snd] in DJ |- *. lia.
Qed.
Lemma last_in : forall lb initr, rev (qc_list (st_qthread X)) = lb :: initr -> In lb (all_batches X) /\ QLv = ly_space ly + b_self lb.
Proof. geo.
intros lb initr Hrev. split; [|unfold QLv; rewrite Hrev; reflexivity].
unfold all_batches. apply in_app_iff. left. rewrite <- (rev_involutive (qc_list (st_qthread X))), Hrev. cbn. apply in_app_iff. right. left. reflexivity.
Qed.
Lemma nb_vs_chunk : forall x, In x (st_chunks X) -> zdisjoint (NBv, kBatchBytes) (ck_base B ly x, ck_extent x).
Proof. geo.
intros x Hx. destruct nb_geom as (Eb & Pb & Ab & Ub & [AU MU] & INP & NIB & NIC).
pose proof (chunk_facts B ly X rd x M Hx) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
unfold zdisjoint. cbn [fst snd]. rewrite Eb.
destruct (ck_beg x) as [|o|r o|c p] eqn:Ebx; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & Gxm & Gxs & Gal).
destruct (Z.eq_dec (prim_class o) kBatchClass) as [Ec|Hc].
+ pose proof (In_chunk_offs X x o Hx Ebx) as IK. rewrite Ec in *. set (xk := o - region_off kBatchClass) in *.
assert (CS : class_size kBatchClass = 8192) by reflexivity. rewrite CS in *.
assert (xk <> coff). { intros E. apply NIC. rewrite <- E. exact IK. }
unfold kBatchBytes in *. apply Z.mod_divide in Gxm as [q1 Hq1]; [|lia]. apply Z.mod_divide in Ab as [q2 Hq2]; [|lia].
assert (q1 <> q2) by (intros E; subst; lia). nia.
+ pose proof (region_in_prim ly (prim_class o) LO ltac:(lia)) as (R1' & R2' & _).
unfold region_base, kBatchBytes in *. rewrite !region_off_eq in * by (unfold kBatchClass; lia). unfold kBatchClass in *.
destruct (Z.lt_ge_cases (prim_class o) 24).
* pose proof (Z.mul_le_mono_nonneg_r (prim_class o + 1) 24 (2 ^ 32) ltac:(lia) ltac:(lia)). lia.
* pose proof (Z.mul_le_mono_nonneg_r (24 + 1) (prim_class o) (2 ^ 32) ltac:(lia) ltac:(lia)). lia.
- destruct GG as (-> & _ & Gbase & Gext & Gin & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & _).
pose proof (pairwise_In zdisjoint _ (ly_sec ly r, sec_map_size (ck_req x)) (ly_prim ly, kPrimResvSize) (sec_extents ly X) (static_extents ly) eq_refl (proj2 (am_placed _ _ _ _ M)) Gin
ltac:(unfold static_extents, owned_extents; cbn; tauto)) as DJ.
unfold zdisjoint, kPage, kBatchBytes in *. cbn [fst snd] in DJ. unfold region_base in *. lia.
Qed.
Lemma nb_vs_batch : forall b2, In b2 (all_batches X) -> zdisjoint (NBv, kBatchBytes) (ly_space ly + b_self b2, kBatchBytes).
Proof. geo.
intros b2 Hb2. destruct nb_geom as (Eb & Pb & Ab & Ub & [AU MU] & INP & NIB & NIC). destruct (batch_geom b2 Hb2) as (x2 & E2 & P2 & A2 & U2 & _ & IN2).
assert (NE : x2 <> coff) by (intros E; apply NIB; rewrite <- E; exact IN2).
unfold zdisjoint, kBatchBytes in *. cbn [fst snd]. rewrite Eb, E2.
apply Z.mod_divide in Ab as [q1 Hq1]; [|lia]. apply Z.mod_divide in A2 as [q2 Hq2]; [|lia].
assert (q1 <> q2) by (intros ->; apply NE; lia). nia.
Qed.
Lemma zdisjoint_of_pointwise : forall a s (e : Z * Z), 0 < s -> 0 < snd e -> (forall x, a <= x < a + s -> ~ in_zr x e) -> zdisjoint (a, s) e.
Proof. clear_all. intros a s [c t] Hs Ht H. unfold zdisjoint. unfold in_zr in H. cbn [fst snd] in *.
destruct (Z_lt_le_dec (Z.max a c) (a + s)); [|lia]. destruct (Z_lt_le_dec (Z.max a c) (c + t)); [|lia].
exfalso. apply (H (Z.max a c)); lia.
Qed.
Lemma HIGH : kHighMemBeg <= ly_prim ly /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\ zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\
kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd /\
ly_prim ly <= ly_space ly /\ ly_space ly + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\
ly_prim ly <= NBv /\ NBv + kBatchBytes <= ly_space ly + kSpaceSize /\
(forall lb initr, rev (qc_list (st_qthread X)) = lb :: initr -> ly_prim ly <= QLv /\ QLv + kBatchBytes <= ly_space ly + kSpaceSize).
Proof. geo.
pose proof (lo_high _ LO) as IP. unfold in_high in IP. cbn [fst snd] in IP.
pose proof (lo_app _ LO) as HA. pose proof (lo_disj _ LO) as HD.
pose proof (Forall_nth_f _ _ 2 _ HA eq_refl) as IT. cbn beta in IT. cbn [fst snd] in IT.
pose proof (zone3_intro ly T kThreadObjSize IMG ltac:(clear_all; unfold kThreadObjSize; lia) IT (pairwise_ij_f _ _ 2 6 _ _ HD eq_refl eq_refl)) as ZT. clear HA HD IT.
pose proof (lo_top _ LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). pose proof (lo_space_in _ LO) as [S1 S2].
destruct nb_geom as (Eb & Pb & Ab & Ub & [AU MU] & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & R3 & R4 & R5).
assert (RB : region_base ly kBatchClass = ly_space ly + 24 * 2 ^ 32) by (unfold region_base; rewrite region_off_eq by (unfold kBatchClass; lia); reflexivity).
split; [clear - IP; lia|]. split; [clear - IP; lia|]. split; [exact ZT|]. split; [clear - ZT; unfold zone3 in ZT; lia|].
clear ZT. splits; try assumption; try (unfold kBatchBytes, kSpaceSize in *; lia).
intros lb initr Hrev. destruct (last_in lb initr Hrev) as [Hin ->]. destruct (batch_geom lb Hin) as (xb & Eb' & Pb' & Ab' & Ub' & [AU' MU'] & _).
unfold kBatchBytes, kSpaceSize in *. lia.
Qed.
Lemma D_cases : forall a, D a ->
(T <= a < T + kThreadObjSize /\ DT a) \/ (NBv <= a < NBv + kBatchBytes /\ DN a) \/
(exists lb initr, rev (qc_list (st_qthread X)) = lb :: initr /\ QLv <= a < QLv + 8) \/ (ly_stk_lo ly <= a < ly_stk_hi ly).
Proof. geo.
intros a Ha. pose proof HIGH as HI. destruct Ha as [Y|[Y|[Y|Y]]].
- left. split; [|exact Y]. unfold DT, t_qc, t_cache, t_cache_stats, kThreadObjSize in *. lia.
- right; left. split; [|exact Y]. unfold DN, kBatchBytes in *. lia.
- do 2 right; left. destruct Y as [NE Y]. destruct (rev (qc_list (st_qthread X))) as [|lb initr] eqn:Hrev.
+ exfalso. apply NE. rewrite <- (rev_involutive (qc_list (st_qthread X))), Hrev. reflexivity.
+ exists lb, initr. auto.
- do 3 right. unfold DS, QSTACK in *. lia.
Qed.
Ltac zget HI x sz Z := assert (Z : zone3cases x sz) by (clear - HI; unfold zone3 in HI; tauto); unfold zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg in Z.
Definition ok (a : Z) : Prop := 0 <= a < 2 ^ 64 /\ ~ D a.
Definition okr (lo len : Z) : Prop := forall a, lo <= a < lo + len -> ok a.
Lemma AGok : forall a, ok a -> rd' a = rd a. Proof. intros a [H1 H2]. apply AG; assumption. Qed.
Ltac hnum := ceil; unfold zone3, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighShadowEnd, kHighMemEnd, kBatchBytes, kThreadObjSize, kPage, kSpaceSize in *.
Ltac zd H := let Y := fresh "ZD" in pose proof H as Y; unfold zdisjoint in Y; cbn [fst snd] in Y; hnum; lia.
Lemma ok_img : forall a, TFIB_IMG_LO <= a < TFIB_IMG_END -> ok a.
Proof. geo.
intros a Ha. pose proof HIGH as HI. pose proof HI as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11). zget HI (ly_T ly) kThreadObjSize ZZ.
split; [hnum; unfold TFIB_IMG_LO, TFIB_IMG_END in *; lia|]. intros HD.
apply D_cases in HD as [[Y _]|[[Y _]|[(lb & initr & Hrev & Y)|Y]]]; [hnum; unfold TFIB_IMG_LO, TFIB_IMG_END in *; lia | hnum; unfold TFIB_IMG_LO, TFIB_IMG_END in *; lia | | hnum; unfold TFIB_IMG_LO, TFIB_IMG_END in *; lia].
destruct (H11 lb initr Hrev). hnum. unfold TFIB_IMG_LO, TFIB_IMG_END in *. lia.
Qed.
Lemma ok_shb : forall a, kLowShadowBeg <= a < kHighMemBeg -> ok a.
Proof. geo.
intros a Ha. pose proof HIGH as HI. pose proof HI as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11). zget HI (ly_T ly) kThreadObjSize ZZ.
split; [hnum; unfold kLowShadowBeg in *; lia|]. intros HD.
apply D_cases in HD as [[Y _]|[[Y _]|[(lb & initr & Hrev & Y)|Y]]]; [hnum; unfold kLowShadowBeg in *; lia | hnum; unfold kLowShadowBeg in *; lia | | hnum; unfold kLowShadowBeg in *; lia].
destruct (H11 lb initr Hrev). hnum. unfold kLowShadowBeg in *. lia.
Qed.
Ltac tsyms := rewrite ?(ts_inst _ TB), ?(ts_depot _ TB), ?(ts_store _ TB), ?(ts_ial_lo _ TB), ?(ts_ial_hi _ TB), ?(ts_ial_w _ TB), ?(ts_ial_flag _ TB), ?(ts_tp _ TB) in *;
unfold TFIB_INST, TFIB_DEPOT, TFIB_STORE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W, TFIB_IAL_FLAG, TFIB_TP, TFIB_IMG_LO, TFIB_IMG_END in *.
Lemma ok_static : forall j e a, nth_error (static_extents ly) j = Some e -> (j <> 0)%nat -> (j <> 2)%nat -> (j < 8)%nat ->
fst e <= a < fst e + snd e -> ok a.
Proof. geo.
intros j e a Hj J0 J2 J8 Ha. pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) e) as HE.
assert (INO : In e (owned_extents ly)).
{ unfold static_extents in Hj. rewrite nth_error_app1 in Hj by (cbn; lia). eapply nth_error_In. exact Hj. }
specialize (HE INO). unfold in_app in HE. cbn [fst snd] in HE. split; [hnum; unfold kLowShadowBeg in *; lia|]. intros HD.
apply D_cases in HD as [[Y _]|[[Y _]|[(lb & initr & Hrev & Y)|Y]]].
- zd (SX j 2 _ _ Hj eq_refl ltac:(lia)).
- pose proof (SX 0 j _ _ eq_refl Hj ltac:(lia)) as ZD. unfold zdisjoint in ZD. cbn [fst snd] in ZD. hnum. unfold kSpaceSize in *. lia.
- destruct (H11 lb initr Hrev). pose proof (SX 0 j _ _ eq_refl Hj ltac:(lia)) as ZD. unfold zdisjoint in ZD. cbn [fst snd] in ZD. hnum. unfold kSpaceSize in *. lia.
- zd (SX j 8 _ _ Hj eq_refl ltac:(lia)).
Qed.
Lemma ok_T : forall a, T <= a < T + kThreadObjSize -> ~ DT a -> ok a.
Proof. geo.
intros a Ha ND. pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11). split; [hnum; lia|]. intros HD.
apply D_cases in HD as [[Y Z0]|[[Y _]|[(lb & initr & Hrev & Y)|Y]]].
- exact (ND Z0).
- pose proof (SX 0 2 _ _ eq_refl eq_refl ltac:(lia)) as ZD. unfold zdisjoint in ZD. cbn [fst snd] in ZD. hnum. unfold kSpaceSize in *. lia.
- destruct (H11 lb initr Hrev). pose proof (SX 0 2 _ _ eq_refl eq_refl ltac:(lia)) as ZD. unfold zdisjoint in ZD. cbn [fst snd] in ZD. hnum. unfold kSpaceSize in *. lia.
- zd (SX 2 8 _ _ eq_refl eq_refl ltac:(lia)).
Qed.
Lemma ok_prim : forall a, ly_prim ly <= a < ly_prim ly + kPrimResvSize -> ~ DN a ->
(forall lb initr, rev (qc_list (st_qthread X)) = lb :: initr -> ~ (QLv <= a < QLv + 8)) -> ok a.
Proof. geo.
intros a Ha NN NL. pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11). split; [hnum; lia|]. intros HD.
apply D_cases in HD as [[Y _]|[[Y Z0]|[(lb & initr & Hrev & Y)|Y]]].
- zd (SX 0 2 _ _ eq_refl eq_refl ltac:(lia)).
- exact (NN Z0).
- exact (NL lb initr Hrev Y).
- zd (SX 0 8 _ _ eq_refl eq_refl ltac:(lia)).
Qed.
Lemma ok_chunk : forall x a, In x (st_chunks X) -> ck_base B ly x <= a < ck_base B ly x + ck_extent x -> ok a.
Proof. geo.
intros x a Hx Ha. pose proof (nb_vs_chunk x Hx) as D1.
destruct (ext_zone x Hx) as [(c & Hc & X1 & X2 & X3 & X4)|(r & Ebk & Xb & Xin)].
- apply ok_prim; [lia | unfold DN; zd D1 |]. intros lb initr Hrev Y. destruct (last_in lb initr Hrev) as [Hin EQ].
pose proof (batch_vs_chunk lb x Hin Hx) as D2. rewrite <- EQ in D2. zd D2.
- pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
pose proof (proj1 (Forall_forall _ _) (proj1 (am_placed _ _ _ _ M)) _ Xin) as (_ & [I1 I2] & I3). cbn [fst snd] in I1, I2, I3.
split; [hnum; unfold alloc_ceiling, sp_window_lo, stack_max_size, kPage in *; lia|]. intros HD.
apply D_cases in HD as [[Y _]|[[Y _]|[(lb & initr & Hrev & Y)|Y]]].
+ zd (SECX _ 2 _ Xin eq_refl).
+ pose proof (SECX _ 0 _ Xin eq_refl) as ZD. unfold zdisjoint in ZD. cbn [fst snd] in ZD. hnum. unfold kSpaceSize, kPage in *. lia.
+ destruct (H11 lb initr Hrev). pose proof (SECX _ 0 _ Xin eq_refl) as ZD. unfold zdisjoint in ZD. cbn [fst snd] in ZD. hnum. unfold kSpaceSize, kPage in *. lia.
+ zd (SECX _ 8 _ Xin eq_refl).
Qed.
Lemma ok_secpage : forall x r o a, In x (st_chunks X) -> ck_beg x = PSec r o -> ly_sec ly r <= a < ly_sec ly r + kPage -> ok a.
Proof. geo.
intros x r o a Hx Ebx Ha. pose proof (chunk_facts B ly X rd x M Hx) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG). rewrite Ebx in GG.
destruct GG as (-> & _ & Gbase & Gext & Gin & _). pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
pose proof (proj1 (Forall_forall _ _) (proj1 (am_placed _ _ _ _ M)) _ Gin) as (_ & IA & _).
pose proof (req_size_bounds (ck_req x) ltac:(lia)) as (_ & Q2 & _).
pose proof (zone3_intro ly (ly_sec ly r) (sec_map_size (ck_req x)) IMG ltac:(clear - Gext G5 G8 Q2; unfold kPage in *; lia) IA (SECX _ 9 _ Gin eq_refl)) as (_ & _ & ZZ).
cbn [fst snd] in ZZ, IA. destruct IA as [I1 I2]. unfold zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg in ZZ.
split; [hnum; unfold kPage in *; lia|]. intros HD.
apply D_cases in HD as [[Y _]|[[Y _]|[(lb & initr & Hrev & Y)|Y]]].
- zd (SECX _ 2 _ Gin eq_refl).
- pose proof (SECX _ 0 _ Gin eq_refl) as ZD. unfold zdisjoint in ZD. cbn [fst snd] in ZD. hnum. unfold kSpaceSize, kPage in *. lia.
- destruct (H11 lb initr Hrev). pose proof (SECX _ 0 _ Gin eq_refl) as ZD. unfold zdisjoint in ZD. cbn [fst snd] in ZD. hnum. unfold kSpaceSize, kPage in *. lia.
- zd (SECX _ 8 _ Gin eq_refl).
Qed.
Lemma ok_batch : forall b2 a, In b2 (all_batches X) -> ly_space ly + b_self b2 <= a < ly_space ly + b_self b2 + kBatchBytes ->
(forall lb initr, rev (qc_list (st_qthread X)) = lb :: initr -> b_self b2 = b_self lb -> ly_space ly + b_self b2 + 8 <= a) -> ok a.
Proof. geo.
intros b2 a Hb2 Ha NL. destruct (batch_geom b2 Hb2) as (x2 & E2 & P2 & A2 & U2 & [AU MU] & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & _).
apply ok_prim; [unfold kBatchBytes in *; lia | unfold DN; zd (nb_vs_batch b2 Hb2) |].
intros lb initr Hrev Y. destruct (last_in lb initr Hrev) as [Hin EQ].
destruct (Z.eq_dec (b_self b2) (b_self lb)) as [E|NE].
- pose proof (NL lb initr Hrev E). rewrite EQ, <- E in Y. lia.
- pose proof (batches_apart b2 lb Hb2 Hin NE) as D2. rewrite <- EQ in D2. zd D2.
Qed.
Lemma ok_nb : forall a, NBv + 32 <= a < NBv + kBatchBytes -> ok a.
Proof. geo.
intros a Ha. pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
apply ok_prim; [unfold kSpaceSize, kBatchBytes in *; lia | unfold DN; lia |].
intros lb initr Hrev Y. destruct (last_in lb initr Hrev) as [Hin EQ]. pose proof (nb_vs_batch lb Hin) as D2. rewrite <- EQ in D2. zd D2.
Qed.
Lemma ok_rinfo : okr (ly_rinfo ly) 4096.
Proof. geo.
intros a Ha. pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11). unfold ly_rinfo, kRegionInfoOff in Ha.
apply ok_prim; [unfold kSpaceSize in *; lia | unfold DN; unfold kSpaceSize, kBatchBytes in *; lia |].
intros lb initr Hrev Y. destruct (H11 lb initr Hrev). unfold kSpaceSize, kBatchBytes in *. lia.
Qed.
Lemma ok_fa : forall c, 1 <= c <= 31 -> okr (fa_base ly c) kFreeArrayMax.
Proof. geo.
intros c Hc a Ha. pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
pose proof (region_in_prim ly c LO Hc) as (R1 & R2 & _). pose proof (region_in_prim ly kBatchClass LO ltac:(unfold kBatchClass; lia)) as (Q1 & Q2 & _).
destruct nb_geom as (Eb & Pb & Ab & Ub & [AU MU] & _).
assert (FAR : forall x, 0 <= x -> x + kBatchBytes <= 2 ^ 31 -> ~ (fa_base ly c <= region_base ly kBatchClass + x + kBatchBytes - 1 /\ region_base ly kBatchClass + x < fa_base ly c + kFreeArrayMax)).
{ intros x Hx1 Hx2 [Z1 Z2]. unfold fa_base, region_base, kFreeArrayOffset, kFreeArrayMax, kBatchBytes in *. rewrite !region_off_eq in * by (unfold kBatchClass in *; lia).
unfold kBatchClass in *. destruct (Z.lt_trichotomy c 24) as [L|[->|L]];
first [ lia
| pose proof (Z.mul_le_mono_nonneg_r (c + 1) 24 (2 ^ 32) ltac:(lia) ltac:(lia)); lia
| pose proof (Z.mul_le_mono_nonneg_r (24 + 1) c (2 ^ 32) ltac:(lia) ltac:(lia)); lia ]. }
apply ok_prim.
- clear FAR. unfold fa_base, region_base, kFreeArrayOffset, kFreeArrayMax in *. lia.
- unfold DN. intros Y. apply (FAR coff); unfold kBatchBytes in *; try lia.
- intros lb initr Hrev Y. destruct (last_in lb initr Hrev) as [Hin EQ]. destruct (batch_geom lb Hin) as (xb & Eb' & Pb' & Ab' & Ub' & _).
rewrite EQ, Eb' in Y. apply (FAR xb); unfold kBatchBytes in *; lia.
Qed.
Definition cell_in (lo len : Z) (c : acell) : Prop :=
lo <= aeval B ly (c_at c) /\ aeval B ly (c_at c) + Z.max 1 (Z.of_nat (c_w c)) <= lo + len.
Lemma cell_xfer : forall c, cell_holds B ly rd c ->
(forall j, 0 <= j < Z.max 1 (Z.of_nat (c_w c)) -> ok (aeval B ly (c_at c) + j)) -> cell_holds B ly rd' c.
Proof. intros c Hc Hok. eapply (cell_holds_agree B ly rd rd' c Hc). intros j Hj. apply AGok, Hok, Hj. Qed.
Lemma cells_xfer : forall L lo len, okr lo len -> Forall (cell_in lo len) L -> Forall (cell_holds B ly rd) L -> Forall (cell_holds B ly rd') L.
Proof.
intros L lo len OK IN OLD. apply Forall_forall. intros c Hc. apply cell_xfer; [exact (proj1 (Forall_forall _ _) OLD c Hc)|].
intros j Hj. destruct (proj1 (Forall_forall _ _) IN c Hc) as [H1 H2]. apply OK. lia.
Qed.
Lemma OLD : forall c, In c (acells B ly X) -> cell_holds B ly rd c.
Proof. intros c Hc. exact (proj1 (Forall_forall _ _) (am_cells B ly X rd M) c Hc). Qed.
Ltac old_in := apply Forall_forall; intros ? HIN; apply OLD; unfold acells; rewrite !in_app_iff.
Lemma EA : forall y d, In y (st_chunks X) -> aeval B ly (aoff (sptr_exp (ck_beg y)) d) = ck_base B ly y + d.
Proof. geo.
intros y d Hy. pose proof (chunk_facts B ly X rd y M Hy) as (_ & _ & _ & _ & _ & _ & _ & _ & GG).
unfold ck_base, sptr_addr. destruct (ck_beg y) as [|o|r o|c p]; try solve [destruct GG]; cbn; lia.
Qed.
Lemma EA2 : forall y d d', In y (st_chunks X) -> aeval B ly (aoff (aoff (sptr_exp (ck_beg y)) d) d') = ck_base B ly y + d + d'.
Proof. geo.
intros y d d' Hy. pose proof (chunk_facts B ly X rd y M Hy) as (_ & _ & _ & _ & _ & _ & _ & _ & GG).
unfold ck_base, sptr_addr. destruct (ck_beg y) as [|o|r o|c p]; try solve [destruct GG]; cbn; lia.
Qed.
Lemma EA0 : forall y, aeval B ly (sptr_exp (ck_beg y)) = ck_base B ly y. Proof. geo. reflexivity. Qed.
Lemma hdr_addr : forall y, In y (st_chunks X) -> aeval B ly (sptr_exp (ck_hdr y)) = ck_base B ly y + ck_rz y - kChunkHeaderSize.
Proof. geo.
intros y Hy. pose proof (chunk_facts B ly X rd y M Hy) as (_ & _ & _ & _ & _ & _ & _ & _ & GG).
unfold ck_hdr, ck_base, sptr_addr. destruct (ck_beg y) as [|o|r o|c p]; try solve [destruct GG]; cbn; lia.
Qed.
Lemma Hu : u = ck_base B ly k + ck_rz k. Proof. geo. pose proof (chunk_facts B ly X rd k M Hk) as (_ & _ & _ & G4 & _). exact G4. Qed.
Ltac fcons := apply Forall_cons; [split; cbn; lia|].
Lemma cells_regions : Forall (cell_holds B ly rd') (flat_map (region_cells S') (zseq 1 31)).
Proof.
apply Forall_flat_map'. intros c Hc. apply zseq_In in Hc. unfold region_cells. rewrite reg'.
apply (cells_xfer _ _ _ ok_rinfo).
- unfold cell_in, ly_rinfo, kRegionInfoOff. repeat fcons. apply Forall_nil.
- old_in. left. apply in_flat_map. exists c. split; [apply In_zseq; lia | exact HIN].
Qed.
Lemma okr_cache_other : forall c, 1 <= c <= 31 -> c <> kBatchClass -> okr (T + t_cache + 80 * c) 80.
Proof. geo. intros c Hc Hne' a Ha. apply ok_T; unfold DT, t_cache, t_qc, t_cache_stats, kThreadObjSize, kBatchClass in *; lia. Qed.
Lemma cells_caches : Forall (cell_holds B ly rd') (flat_map (cache_cells S') (zseq 1 31)).
Proof.
apply Forall_flat_map'. intros c Hc. apply zseq_In in Hc.
assert (OLDC : Forall (cell_holds B ly rd) (cache_cells X c)).
{ old_in. right; left. apply in_flat_map. exists c. split; [apply In_zseq; lia | exact HIN]. }
pose proof (wf_classes _ _ _ _ _ WF c ltac:(lia)) as CL. pose proof (wr_cache _ _ _ _ _ _ CL) as WC. pose proof (class_ok c ltac:(lia)) as (_ & _ & _ & K4 & _).
unfold cache_cells in OLDC |- *. rewrite S'_cinit. rewrite Hci in OLDC, WC. destruct WC as [PM PL].
destruct (Z.eq_dec c kBatchClass) as [->|NE].
-
rewrite cache24'. cbn [pc_chunks pc_max]. rewrite Hl in OLDC, PL.
apply Forall_cons_iff in OLDC as [_ OLDC]. apply Forall_cons_iff in OLDC as [O2 OLDC]. apply Forall_cons_iff in OLDC as [O3 OLDC].
assert (OKC : forall a, T + t_cache + 80 * kBatchClass + 4 <= a < T + t_cache + 80 * kBatchClass + 80 -> ok a).
{ intros a Ha. apply ok_T; unfold DT, t_cache, t_qc, t_cache_stats, kThreadObjSize, kBatchClass in *; lia. }
apply Forall_cons. { cbn [cell_holds c_at c_val c_w z4 c4 aeval]. intros kk Hkk. unfold kBatchClass at 1.
replace (T + (t_cache + 80 * 24) + Z.of_nat kk) with (T + t_cache + 1920 + Z.of_nat kk) by lia. rewrite NEW_cnt by exact Hkk.
assert (LZ : length l <> 0%nat) by (intros E0; apply Hlne, length_zero_iff_nil; exact E0). rewrite removelast_length by exact Hlne. do 2 f_equal. lia. }
apply Forall_cons. { apply (cell_xfer _ O2). intros j Hj. apply OKC. cbn in Hj |- *. unfold kBatchClass in *. lia. }
apply Forall_cons. { apply (cell_xfer _ O3). intros j Hj. apply OKC. cbn in Hj |- *. unfold kBatchClass in *. lia. }
apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i v] & <- & Hiv).
assert (Hiv' : In (i, v) (combine (seq 0 (length l)) l)).
{ rewrite <- (removelast_app_last l 0 Hlne). rewrite length_app. cbn [length]. rewrite Nat.add_1_r, (combine_snoc _ _ _ eq_refl). apply in_app_iff. left. exact Hiv. }
apply (cell_xfer _ (proj1 (Forall_forall _ _) OLDC _ ltac:(apply in_map_iff; exists (i, v); split; [reflexivity | exact Hiv']))).
apply in_combine_l in Hiv. apply in_seq in Hiv. rewrite removelast_length in Hiv by exact Hlne.
intros j Hj. apply OKC. cbn in Hj |- *. unfold kBatchClass in *. lia.
- rewrite cache' by (lia || exact NE). apply (cells_xfer _ _ _ (okr_cache_other c ltac:(lia) NE)); [|exact OLDC].
unfold cell_in, t_cache. repeat fcons. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i v] & <- & Hiv). cbn [fst snd c_at c_w z4 c4 aeval aoff].
apply in_combine_l in Hiv. apply in_seq in Hiv. cbn. lia.
Qed.
Lemma cells_chunks : Forall (cell_holds B ly rd') (flat_map chunk_cells (st_chunks S')).
Proof.
rewrite S'_chunks. apply Forall_flat_map'. intros x Hx. pose proof (chunk_facts B ly X rd x M Hx) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
apply (cells_xfer _ (ck_base B ly x) (ck_extent x)); [intros a Ha; exact (ok_chunk x a Hx Ha) | |].
- pose proof (req_size_bounds (ck_req x) ltac:(lia)) as (_ & Q2 & _).
unfold chunk_cells, kChunkHeaderSize, cell_in. apply Forall_app. split.
+ repeat (apply Forall_cons; [cbn [c_at c_w z1 z2 z4 c1 c2 c4]; rewrite ?(EA2 x), ?(EA x), ?EA0 by exact Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.max Pos.max Z.pos_sub]; lia|]). apply Forall_nil.
+ destruct (Z.eqb_spec (ck_rz x) 16); [apply Forall_nil|].
repeat (apply Forall_cons; [cbn [c_at c_w z8 c8]; rewrite ?(EA2 x), ?(EA x), ?EA0 by exact Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.max Pos.max Z.pos_sub]; lia|]). apply Forall_nil.
- old_in. do 2 right; left. apply in_flat_map. exists x. split; [exact Hx | exact HIN].
Qed.
Lemma cells_sec : Forall (cell_holds B ly rd') (sec_cells S').
Proof.
pose proof (wf_secondary _ _ _ _ _ WF) as XS. destruct XS as [Snd Sac Sal Sres Sral].
assert (OLDS : Forall (cell_holds B ly rd) (sec_cells X)) by (old_in; do 3 right; left; exact HIN).
unfold sec_cells in OLDS |- *. rewrite S'_sec_res, S'_sec_arr, S'_chunks.
apply Forall_cons_iff in OLDS as [O1 OLDS]. apply Forall_cons_iff in OLDS as [O2 OLDS]. apply Forall_cons_iff in OLDS as [O3 OLDS]. apply Forall_app in OLDS as [O4 O5].
pose proof (aso_cells _ (am_syms _ _ _ _ M)) as AC.
assert (OKI : okr (as_inst B) 3632) by (intros a Ha; apply ok_img; tsyms; lia).
apply Forall_cons; [apply (cell_xfer _ O1); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_sec_reserved; lia|].
apply Forall_cons; [apply (cell_xfer _ O2); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_sec_n; lia|].
apply Forall_cons; [apply (cell_xfer _ O3); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_sec_mutex; lia|].
apply Forall_app. split.
- refine (cells_xfer _ _ _ (fun a Ha => ok_static 1 _ a eq_refl ltac:(lia) ltac:(lia) ltac:(lia) Ha) _ O4).
apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i r] & <- & Hir). apply in_combine_l in Hir. apply in_seq in Hir.
unfold cell_in. cbn. unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *. lia.
- apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) O5 c Hc) as Oc. apply in_flat_map in Hc as (x & Hx & Hc).
destruct (ck_beg x) as [|o|r o|c' p] eqn:Ebx; try solve [destruct Hc].
assert (OKP : okr (ly_sec ly r) 32) by (intros a Ha; eapply (ok_secpage x r o a Hx Ebx); unfold kPage; lia).
apply (cell_xfer _ Oc). intros j Hj. apply OKP. destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hj |- *; lia.
Qed.
Lemma batch_own_cells_within : forall b2 nx c, In c (batch_own_cells b2 nx) -> cell_in (ly_space ly + b_self b2) (24 + 8 * Z.of_nat (length (b_items b2))) c.
Proof. geo.
intros b2 nx c Hc. unfold batch_own_cells in Hc. destruct Hc as [<-|[<-|[<-|Hc]]]; try (unfold cell_in; cbn; lia).
apply in_map_iff in Hc as ([i x] & <- & Hix). apply in_combine_l in Hix. apply in_seq in Hix. unfold cell_in; cbn; lia.
Qed.
Lemma cells_quar : Forall (cell_holds B ly rd') (quar_cells S').
Proof.
assert (OLDQ : Forall (cell_holds B ly rd) (quar_cells X)) by (old_in; do 4 right; left; exact HIN).
pose proof (aso_cells _ (am_syms _ _ _ _ M)) as AC. pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
assert (OKI : okr (as_inst B) 3632) by (intros a Ha; apply ok_img; tsyms; lia).
unfold quar_cells, qc_cells in OLDQ |- *. rewrite S'_qglobal, qlist', qbytes'.
apply Forall_cons_iff in OLDQ as [O1 OLDQ]. apply Forall_cons_iff in OLDQ as [O2 OLDQ]. apply Forall_app in OLDQ as [OT OG].
apply Forall_cons_iff in OT as [O3 OT]. apply Forall_cons_iff in OT as [O4 OT]. apply Forall_cons_iff in OT as [O5 OT]. apply Forall_cons_iff in OT as [O6 OT].
apply Forall_cons; [apply (cell_xfer _ O1); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_cmutex; lia|].
apply Forall_cons; [apply (cell_xfer _ O2); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_rmutex; lia|].
apply Forall_app. split.
-
apply Forall_cons. { cbn [cell_holds c_at c_val c_w z8 c8]. intros kk Hkk. cbn [aeval]. rewrite NEW_qs by exact Hkk. rewrite length_app. cbn [length]. do 2 f_equal. lia. }
apply Forall_cons. { cbn [cell_holds c_at c_val c_w c8]. intros kk Hkk. cbn [aeval aoff].
replace (T + (t_qc + 8)) with (T + t_qc + 8) by lia. rewrite NEW_qf by exact Hkk. do 2 f_equal. destruct (qc_list (st_qthread X)); reflexivity. }
apply Forall_cons. { rewrite rev_app_distr. cbn [rev app cell_holds c_at c_val c_w c8 aeval aoff batch_exp b_self bn]. intros kk Hkk.
replace (T + (t_qc + 16)) with (T + t_qc + 16) by lia. rewrite NEW_ql by exact Hkk. reflexivity. }
apply Forall_cons. { cbn [cell_holds c_at c_val c_w z8 c8 aeval aoff]. intros kk Hkk.
replace (T + (t_qc + 24)) with (T + t_qc + 24) by lia. rewrite NEW_qb by exact Hkk. reflexivity. }
apply Forall_forall. intros c Hc. apply In_batch_cells in Hc as (i & b2 & Hi & Hc).
destruct (Nat.lt_ge_cases i (length (qc_list (st_qthread X)))) as [LT|GE].
+
rewrite nth_error_app1 in Hi by exact LT. pose proof (nth_error_In _ _ Hi) as Hin.
assert (Hin2 : In b2 (all_batches X)) by (unfold all_batches; apply in_app_iff; left; exact Hin).
pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wf_quarantine _ _ _ _ _ WF)) b2 Hin2) as [L1 L2]. unfold kBatchSlots in L2.
destruct (Nat.eq_dec (S i) (length (qc_list (st_qthread X)))) as [LAST|NL].
*
rewrite (next_exp_app_last _ _ _ LAST) in Hc.
assert (Hrev : exists initr, rev (qc_list (st_qthread X)) = b2 :: initr).
{ destruct (nth_error_split _ _ Hi) as (l1 & l2 & E0 & Ll1).
assert (l2 = []) as -> by (apply (f_equal (@length _)) in E0; rewrite length_app in E0; cbn in E0; destruct l2; [reflexivity | cbn in E0; lia]).
exists (rev l1). rewrite E0, rev_app_distr. reflexivity. }
destruct Hrev as (initr & Hrev).
destruct Hc as [<-|Hc].
-- cbn [cell_holds c_at c_val c_w c8 aeval batch_exp b_self bn]. intros kk Hkk. rewrite (NEW_lnext b2 initr Hrev kk Hkk). reflexivity.
-- assert (OLDc : cell_holds B ly rd c).
{ apply (proj1 (Forall_forall _ _) OT). apply In_batch_cells. exists i, b2. split; [exact Hi|]. right. exact Hc. }
apply (cell_xfer _ OLDc). pose proof (batch_own_cells_within b2 (ANum 0) c (or_intror Hc)) as [R1 R2].
assert (NF : 8 <= aeval B ly (c_at c) - (ly_space ly + b_self b2)).
{ unfold batch_own_cells in Hc. destruct Hc as [<-|[<-|Hc]]; [cbn; lia | cbn; lia |].
apply in_map_iff in Hc as ([i' x] & <- & Hix). apply in_combine_l in Hix. apply in_seq in Hix. cbn. lia. }
intros j Hj. apply (ok_batch b2); [exact Hin2 | unfold kBatchBytes; lia | intros; lia].
*
assert (SI : (S i < length (qc_list (st_qthread X)))%nat) by (clear - LT NL; lia). rewrite (next_exp_app_lt _ _ _ SI) in Hc.
assert (OLDc : cell_holds B ly rd c).
{ apply (proj1 (Forall_forall _ _) OT). apply In_batch_cells. exists i, b2. split; [exact Hi | exact Hc]. }
apply (cell_xfer _ OLDc). pose proof (batch_own_cells_within b2 _ c Hc) as [R1 R2].
intros j Hj. apply (ok_batch b2); [exact Hin2 | unfold kBatchBytes; lia |].
intros lb initr Hrev E. exfalso. apply NL.
assert (E0 : qc_list (st_qthread X) = rev initr ++ [lb]) by (rewrite <- (rev_involutive (qc_list (st_qthread X))), Hrev; reflexivity).
pose proof batches_nodup as ND. unfold all_batches in ND. rewrite E0, !map_app in ND. cbn [map] in ND.
rewrite E0 in Hi, LT |- *. rewrite length_app. cbn [length]. rewrite length_app in LT. cbn [length] in LT.
destruct (Nat.lt_ge_cases i (length (rev initr))) as [LT'|GE']; [|lia]. exfalso.
rewrite nth_error_app1 in Hi by exact LT'. pose proof (nth_error_In _ _ Hi) as Hin'.
rewrite <- app_assoc in ND. apply NoDup_app_iff in ND as (N1 & N2 & N3). apply (N3 (b_self b2)); [apply in_map; exact Hin' | left; symmetry; exact E].
+
rewrite nth_error_app2 in Hi by exact GE. destruct (i - length (qc_list (st_qthread X)))%nat as [|m] eqn:Em; [|cbn in Hi; destruct m; discriminate].
cbn in Hi. injection Hi as <-. assert (EI : i = length (qc_list (st_qthread X))) by lia. subst i. rewrite next_exp_app_new in Hc.
unfold batch_own_cells in Hc. cbn [b_items b_self bn length seq combine map fst snd] in Hc.
destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; cbn [cell_holds c_at c_val c_w c8 z8 aeval aoff batch_exp b_self bn]; intros kk Hkk.
* rewrite NEW_n0 by exact Hkk. reflexivity.
* replace (ly_space ly + (nb + 8)) with (ly_space ly + nb + 8) by lia. rewrite NEW_n8 by exact Hkk. unfold b_bytes. cbn [b_items bn fold_right]. do 2 f_equal. lia.
* replace (ly_space ly + (nb + 16)) with (ly_space ly + nb + 16) by lia. rewrite NEW_n16 by exact Hkk. reflexivity.
* replace (ly_space ly + (nb + (24 + 8 * Z.of_nat 0)) + Z.of_nat kk) with (ly_space ly + nb + 24 + Z.of_nat kk) by lia. rewrite NEW_n24 by exact Hkk. rewrite (hdr_addr k Hk), Hu. unfold kChunkHeaderSize. do 2 f_equal; lia.
-
apply Forall_cons_iff in OG as [G1 OG]. apply Forall_cons_iff in OG as [G2 OG]. apply Forall_cons_iff in OG as [G3 OG]. apply Forall_cons_iff in OG as [G4 OG].
apply Forall_cons; [apply (cell_xfer _ G1); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_size; lia|].
apply Forall_cons; [apply (cell_xfer _ G2); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_size; lia|].
apply Forall_cons; [apply (cell_xfer _ G3); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_size; lia|].
apply Forall_cons; [apply (cell_xfer _ G4); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_size; lia|].
apply Forall_forall. intros c Hc. apply (cell_xfer _ (proj1 (Forall_forall _ _) OG c Hc)).
apply In_batch_cells in Hc as (i & b2 & Hi & Hc). pose proof (nth_error_In _ _ Hi) as Hin.
assert (Hin2 : In b2 (all_batches X)) by (unfold all_batches; apply in_app_iff; right; exact Hin).
pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wf_quarantine _ _ _ _ _ WF)) b2 Hin2) as [L1 L2]. unfold kBatchSlots in L2.
pose proof (batch_own_cells_within b2 _ c Hc) as [R1 R2].
intros j Hj. apply (ok_batch b2); [exact Hin2 | unfold kBatchBytes; lia |].
intros lb initr Hrev E. exfalso.
assert (E0 : qc_list (st_qthread X) = rev initr ++ [lb]) by (rewrite <- (rev_involutive (qc_list (st_qthread X))), Hrev; reflexivity).
pose proof batches_nodup as ND. unfold all_batches in ND. rewrite E0, !map_app in ND. cbn [map] in ND.
rewrite <- app_assoc in ND. apply NoDup_app_iff in ND as (N1 & N2 & N3). cbn in N2. inversion N2 as [|y l' N4 N5]; subst.
apply N4. rewrite <- E. apply in_map. exact Hin.
Qed.
Lemma cells_fs : Forall (cell_holds B ly rd') (fs_cells S').
Proof.
assert (OLDF : Forall (cell_holds B ly rd) (fs_cells X)) by (old_in; do 5 right; left; exact HIN).
unfold fs_cells in OLDF |- *. rewrite S'_fs. pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
refine (cells_xfer _ _ _ (fun a Ha => ok_static 3 _ a eq_refl ltac:(lia) ltac:(lia) ltac:(lia) Ha) _ OLDF).
unfold cell_in. cbn [fst snd]. unfold kFakeStackSize. fcons. fcons.
apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i h] & <- & Hih). apply in_combine_l in Hih. apply in_seq in Hih. cbn. lia.
Qed.
Lemma cells_depot : Forall (cell_holds B ly rd') (depot_cells ly S').
Proof.
assert (OLDD : Forall (cell_holds B ly rd) (depot_cells ly X)) by (old_in; do 6 right; left; exact HIN).
unfold depot_cells, depot_ids, depot_frames in OLDD |- *. rewrite S'_depot. pose proof (aso_cells _ (am_syms _ _ _ _ M)) as AC.
apply Forall_forall. intros c Hc. apply (cell_xfer _ (proj1 (Forall_forall _ _) OLDD c Hc)). intros j Hj. apply ok_img.
destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hj |- *; unfold d_nuniq, d_map1, s_total, s_block0 in *; tsyms; lia.
Qed.
Lemma cells_ialloc : Forall (cell_holds B ly rd') (ialloc_cells B S').
Proof.
assert (OLDI : Forall (cell_holds B ly rd) (ialloc_cells B X)) by (old_in; do 7 right; left; exact HIN).
unfold ialloc_cells in OLDI |- *. rewrite S'_inited. pose proof (aso_cells _ (am_syms _ _ _ _ M)) as AC. pose proof (aso_ialloc _ (am_syms _ _ _ _ M)) as [I1 I2].
apply Forall_forall. intros c Hc. apply (cell_xfer _ (proj1 (Forall_forall _ _) OLDI c Hc)). intros j Hj. apply ok_img.
destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hj |- *; tsyms; lia.
Qed.
Lemma cells_thread : Forall (cell_holds B ly rd') thread_cells.
Proof.
assert (OLDT : Forall (cell_holds B ly rd) thread_cells) by (old_in; do 8 right; exact HIN).
unfold thread_cells in OLDT |- *. apply Forall_cons_iff in OLDT as [O1 _]. apply Forall_cons; [|apply Forall_nil].
apply (cell_xfer _ O1). intros j Hj. cbn in Hj |- *. apply ok_T; unfold DT, t_qc, t_cache, t_cache_stats, t_unwinding, kThreadObjSize in *; lia.
Qed.
Lemma cells_all : Forall (cell_holds B ly rd') (acells B ly S').
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
Lemma fa' : fa_entries_ok ly rd' S'.
Proof.
intros c i v Hc Hi Hv kk Hkk. rewrite reg' in Hi, Hv. rewrite AGok; [exact (am_fa B ly X rd M c i v Hc Hi Hv kk Hkk)|].
pose proof (wf_classes _ _ _ _ _ WF c Hc) as CL. pose proof (wr_fa_len _ _ _ _ _ _ CL) as FL. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as FB.
apply (ok_fa c Hc). lia.
Qed.
Lemma flags' : fs_flags_ok ly rd' S'.
Proof.
intros cid pos Hc Hp. rewrite frames'. rewrite AGok; [exact (am_flags B ly X rd M cid pos Hc Hp)|].
pose proof (flag_off_bounds cid pos Hc Hp) as FB. unfold flag_addr, kFakeFlagsOff, kFakeFramesOff in *.
apply (ok_static 3 _ _ eq_refl ltac:(lia) ltac:(lia) ltac:(lia)). cbn [fst snd]. unfold kFakeStackSize. lia.
Qed.
Lemma depot' : depot_ok B ly rd' S'.
Proof.
pose proof (am_depot B ly X rd M) as (heads & links & D1 & D2 & D3). pose proof (aso_cells _ (am_syms _ _ _ _ M)) as AC.
unfold depot_ok, depot_ids, depot_traces in *. rewrite S'_depot. exists heads, links. split; [|split; [|exact D3]].
- intros b0 Hb. destruct (D1 b0 Hb) as [X1 X2]. split; [exact X1|]. intros kk Hkk. rewrite AGok; [exact (X2 kk Hkk)|].
apply ok_img. unfold d_tab_words in *. tsyms. lia.
- intros id Hid. destruct (D2 id Hid) as (X1 & X2 & X3). split; [exact X1|].
assert (NB : Z.of_nat (length (st_depot X)) <= 4096).
{ pose proof (wf_depot _ _ _ _ _ WF) as [ND INC]. pose proof (NoDup_incl_length ND INC). destruct (am_universe B ly X rd M) as (U1 & _). unfold DEPOT_MAX in U1. lia. }
pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) (ly_NB ly, kNodesBlockSize) ltac:(unfold owned_extents; cbn; tauto)) as [N1 N2]. cbn [fst snd] in N1, N2.
assert (OKN : forall kk, 0 <= kk < 16 -> ok (ly_NB ly + 16 * id + kk)).
{ intros kk Hkk. apply (ok_static 4 _ _ eq_refl ltac:(lia) ltac:(lia) ltac:(lia)). cbn [fst snd]. unfold kNodesBlockSize. lia. }
split; intros kk Hkk; rewrite AGok; auto; [apply OKN; lia|].
replace (ly_NB ly + 16 * id + 8 + Z.of_nat kk) with (ly_NB ly + 16 * id + (8 + Z.of_nat kk)) by lia. apply OKN. lia.
Qed.
Lemma fa_poison_high : forall lo len g, In (lo, len) (fa_poison_ranges ly X) -> lo <= g < lo + len -> 4096 <= g /\ g < ASAN_CEIL.
Proof. geo.
intros lo len g Hin Hg. unfold fa_poison_ranges in Hin. apply in_app_iff in Hin as [Hin|Hin].
- apply in_flat_map in Hin as (c & Hc & Hin). apply zseq_In in Hc.
pose proof (region_in_prim ly c LO ltac:(lia)) as (R1 & R2 & R3 & R4 & R5).
pose proof (wf_classes _ _ _ _ _ WF c ltac:(lia)) as CL.
pose proof (wr_alloc _ _ _ _ _ _ CL) as A1. pose proof (wr_fa _ _ _ _ _ _ CL) as [A2 _]. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as A3.
pose proof (mapped_user_bound (as_universe B) 0 0 0 X c WF ltac:(lia)) as MB. unfold kUserMapSize, EV_MAX, kFreeArrayMax in *.
unfold fa_base, kFreeArrayOffset in Hin. unfold region_base in *.
unfold kHighMemBeg in *. destruct Hin as [E|[E|[]]]; injection E as <- <-; lia.
- pose proof (proj1 (Forall_forall _ _) (proj1 (am_placed _ _ _ _ M)) (lo, len) Hin) as (_ & [I1 I2] & I3). cbn [fst snd] in I1, I2, I3. ceil. unfold ASAN_CEIL, kHighMemBeg, kLowShadowBeg in *. lia.
Qed.
Lemma shadow' : shadow_ok B ly rd' S'.
Proof.
intros g v Hg8 HS'. unfold ashadow in HS'. rewrite S'_chunks, fa_poison' in HS'. fold (ashadow B ly X g) in HS'.
rewrite AGok; [exact (am_shadow B ly X rd M g v Hg8 HS')|].
pose proof (YG0t.ashadow_low B ly X rd g v M HS') as [LO1 LO2]. apply ok_shb. split; [|exact LO2].
clear - LO1. unfold SHADOW_OFF, kLowShadowBeg in *. lia.
Qed.
Lemma zshadow' : zshadow_ok B ly rd'.
Proof.
pose proof (am_zshadow B ly X rd M) as ZS. unfold zshadow_ok in ZS |- *. apply Forall_forall. intros r Hr i Hi.
pose proof (proj1 (Forall_forall _ _) ZS r Hr i Hi) as Z0. unfold shadow_of_addr in Z0 |- *. change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)) in Z0 |- *.
rewrite AGok; [exact Z0|]. apply ok_shb.
pose proof (proj1 (Forall_forall _ _) (owned_shadow_ranges B ly X rd M) r ltac:(rewrite !in_app_iff; tauto)) as (K1 & K2 & K3).
assert (DM : i < (snd r + 7) / 8). { pose proof (Z.div_le_mono (8 * i + 8) (snd r + 7) 8 ltac:(lia) ltac:(lia)) as DX. replace (8 * i + 8) with ((i + 1) * 8) in DX by lia. rewrite Z_div_mult in DX by lia. lia. }
split; [unfold shadow_addr, SHADOW_OFF, kLowShadowBeg; pose proof (Z.div_pos (fst r) 8); lia|].
apply (proj2 (owned_shadow_bound B ly X rd (shadow_addr (fst r) + i) M ltac:(apply Exists_exists; exists r; split; [rewrite !in_app_iff; tauto | unfold in_zr; cbn [fst snd]; lia]))).
Qed.
Lemma vis_keep : forall L, Forall (range_vis B ly rd) L -> Forall (range_vis B ly rd') L.
Proof. intros L H. exact (Forall_range_vis_keep B ly rd rd' L VIS H). Qed.
Lemma vis_sub : forall r r', range_vis B ly rd r' -> aeval B ly (fst r') <= aeval B ly (fst r) ->
aeval B ly (fst r) + snd r <= aeval B ly (fst r') + snd r' -> range_vis B ly rd' r.
Proof.
intros r r' V H1 H2 i Hi. apply VIS. replace (aeval B ly (fst r) + i) with (aeval B ly (fst r') + (aeval B ly (fst r) + i - aeval B ly (fst r'))) by lia.
apply V. lia.
Qed.
Lemma junk' : Forall (range_vis B ly rd') (ajunk B ly S').
Proof.
pose proof (am_junk B ly X rd M) as J. pose proof (am_areas B ly X rd M) as AR0.
unfold ajunk in J |- *. unfold quar_junk in J |- *. rewrite all_batches_S'. unfold all_batches in J.
unfold sec_junk in J |- *. rewrite S'_sec_arr, S'_sec_res, S'_chunks.
apply Forall_cons_iff in J as [J1 J]. apply Forall_cons_iff in J as [J2 J].
apply Forall_app in J as [J3 J]. apply Forall_app in J as [J4 J]. apply Forall_app in J as [J5 J]. apply Forall_app in J as [J6 J]. apply Forall_app in J as [J7 J].
apply Forall_cons; [intros i Hi; apply VIS; exact (J1 i Hi)|].
apply Forall_cons; [intros i Hi; apply VIS; exact (J2 i Hi)|].
apply Forall_app. split; [exact (vis_keep _ J3)|].
apply Forall_app. split.
{
apply Forall_flat_map'. intros c Hc. pose proof (zseq_In _ _ _ Hc) as Hc'. unfold cache_junk. rewrite S'_cinit.
destruct (Z.eq_dec c kBatchClass) as [->|NE].
- rewrite cache24'. cbn [pc_chunks]. rewrite removelast_length by exact Hlne.
assert (LZ : length l <> 0%nat) by (intros E0; apply Hlne, length_zero_iff_nil; exact E0).
pose proof (proj1 (Forall_forall _ _) J4 (AT (t_cache + 80 * kBatchClass + 16 + 4 * Z.of_nat (length l)), 64 - 4 * Z.of_nat (length l))
ltac:(apply in_flat_map; exists kBatchClass; split; [exact Hc|]; unfold cache_junk; rewrite Hci, Hl; left; reflexivity)) as JO.
assert (SL : cell_holds B ly rd (z4 (aoff (AT (t_cache + 80 * kBatchClass)) (16 + 4 * Z.of_nat (length l - 1))) (last l 0 / 16))).
{ apply OLD. unfold acells. rewrite !in_app_iff. right; left. apply in_flat_map. exists kBatchClass. split; [exact Hc|].
unfold cache_cells. rewrite Hci, Hl. right; right; right. apply in_map_iff. exists ((length l - 1)%nat, last l 0). split; [reflexivity|].
set (x0 := last l 0). replace (length l - 1)%nat with (length (removelast l)) by (rewrite removelast_length by exact Hlne; lia).
rewrite <- (removelast_app_last l 0 Hlne) at 2 3. fold x0. rewrite length_app. cbn [length]. rewrite Nat.add_1_r, (combine_snoc _ _ _ eq_refl).
apply in_app_iff. right. left. reflexivity. }
apply Forall_cons; [|apply Forall_nil]. intros i Hi. cbn [fst snd aeval] in Hi |- *. rewrite Nat2Z.inj_sub in Hi |- * by lia. cbn [Z.of_nat] in Hi |- *.
destruct (Z_lt_le_dec i 4) as [L4|L4].
+ pose proof (SL (Z.to_nat i) ltac:(cbn; lia)) as SX0. cbn [c_at c_w aeval aoff z4 c4] in SX0. rewrite Z2Nat.id in SX0 by lia.
rewrite Nat2Z.inj_sub in SX0 by lia. cbn [Z.of_nat] in SX0.
apply VIS. match type of SX0 with rd ?a = _ => match goal with |- rd ?b <> None => replace b with a by (cbn; lia) end end.
rewrite SX0. discriminate.
+ pose proof (JO (i - 4) ltac:(cbn [snd]; lia)) as JX0. cbn [fst aeval] in JX0.
apply VIS. match type of JX0 with rd ?a <> None => match goal with |- rd ?b <> None => replace b with a by (cbn; lia) end end. exact JX0.
- rewrite cache' by (lia || exact NE). apply (vis_keep _). apply Forall_forall. intros r Hr. apply (proj1 (Forall_forall _ _) J4).
apply in_flat_map. exists c. split; [exact Hc|]. unfold cache_junk. rewrite Hci. exact Hr. }
apply Forall_app. split; [exact (vis_keep _ J5)|].
apply Forall_app. split; [exact (vis_keep _ J6)|].
apply Forall_app. split.
{
rewrite !flat_map_app. cbn [flat_map]. rewrite app_nil_r. rewrite flat_map_app in J7. apply Forall_app in J7 as [J7a J7b].
apply Forall_app. split; [apply Forall_app; split; [exact (vis_keep _ J7a)|] | exact (vis_keep _ J7b)].
unfold batch_junk. apply Forall_cons; [|apply Forall_nil]. cbn [b_items bn length Z.of_nat b_self batch_exp].
destruct nb_geom as (Eb & Pb & Ab & Ub & [AU MU] & _).
apply (vis_sub _ (ASp (region_off kBatchClass), rg_mapped_user (reg X kBatchClass))).
- apply (proj1 (Forall_forall _ _) AR0). unfold aareas. rewrite !in_app_iff. left. apply in_flat_map. exists kBatchClass. split; [apply In_zseq; unfold kBatchClass; lia | left; reflexivity].
- unfold batch_exp. cbn [fst snd aeval aoff b_self bn]. unfold nb, region_base in *. lia.
- unfold batch_exp. cbn [fst snd aeval aoff b_self bn]. unfold nb, region_base, kBatchBytes in *. lia. }
exact (vis_keep _ J).
Qed.
Lemma areas' : Forall (range_vis B ly rd') (aareas S').
Proof. pose proof (am_areas B ly X rd M) as A. unfold aareas, reg in A |- *. rewrite S'_regions, S'_sec_res, S'_chunks. exact (vis_keep _ A). Qed.
Lemma client' : Forall (range_vis B ly rd') (aclient S').
Proof. pose proof (am_client B ly X rd M) as A. unfold aclient in A |- *. rewrite frames', S'_chunks. exact (vis_keep _ A). Qed.
Lemma placed' : sec_placed ly S'.
Proof. unfold sec_placed. rewrite sec_extents'. exact (am_placed B ly X rd M). Qed.
Theorem enq_fin_ARm : ARm B ly S' rd'.
Proof.
constructor.
- exact WS'.
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
- pose proof (am_zero B ly X rd M) as ZR. apply Forall_forall. intros r Hr i Hi. rewrite AGok; [exact (proj1 (Forall_forall _ _) ZR r Hr i Hi)|].
pose proof (aso_cells _ (am_syms _ _ _ _ M)) as AC. pose proof (aso_ialloc _ (am_syms _ _ _ _ M)) as [I1 I2]. apply ok_img.
unfold ialloc_zero in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in Hi |- *; tsyms; lia.
- exact (am_tsd B ly X rd M).
- exact (am_static_img B ly X rd M).
Qed.
Lemma sec_live' : sec_live_bytes S' = sec_live_bytes X. Proof. geo. reflexivity. Qed.
Lemma prim_committed' : prim_committed S' = prim_committed X. Proof. geo. reflexivity. Qed.
Lemma ALedger_S' : forall segs md, ALedger segs ly X md -> ALedger segs ly S' md.
Proof. geo. intros segs md L. destruct L as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10]. constructor; assumption. Qed.
Lemma abudget_S' : abudget S' = abudget X. Proof. geo. reflexivity. Qed.
Lemma all_batches_len' : Z.of_nat (length (all_batches S')) = Z.of_nat (length (all_batches X)) + 1.
Proof. geo. rewrite all_batches_S'. unfold all_batches. rewrite !length_app. cbn [length]. lia. Qed.
Lemma qloose_S' : qc_bytes (st_qthread X) + nn + kBatchBytes <= 2 ^ 29 -> qloose X -> qloose S'.
Proof. geo.
intros Hb (T1 & T2 & T3). unfold qloose. rewrite qbytes', S'_qglobal. split; [exact Hb|]. split; [exact T2|].
unfold quar_n in *. rewrite S'_chunks. rewrite queued_n_eq in *. rewrite qlist', S'_qglobal.
rewrite !items_n_flat_app. cbn [flat_map b_items bn]. rewrite app_nil_r, items_n_cons, items_n_nil.
assert (NN : 0 <= nn); [|lia]. clear - M Hk. pose proof (chunk_facts B ly X rd k M Hk) as (_ & _ & _ & _ & _ & _ & G7 & _).
unfold ck_n. pose proof (req_size_bounds (ck_req k) ltac:(lia)). lia.
Qed.
Lemma own_nb : forall a, NBv <= a < NBv + kBatchBytes -> aowned B ly X a.
Proof. geo.
intros a Ha. destruct nb_geom as (Eb & Pb & Ab & Ub & [AU MU] & INP & NIB & NIC).
pose proof (region_in_prim ly kBatchClass LO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & _).
eapply own_prim_nonuser; [exact M | unfold kBatchBytes in *; lia |].
intros y Hy Hsy Hr. pose proof (nb_vs_chunk y Hy) as D1. pose proof (chunk_facts B ly X rd y M Hy) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
unfold zdisjoint in D1. cbn [fst snd] in D1. lia.
Qed.
Lemma D_owned : forall a, 0 <= a -> D a -> aowned B ly X a \/ DS a.
Proof. geo.
intros a Ha0 HD. destruct HD as [Y|[Y|[[NE Y]|Y]]].
- left. eapply (own_core B ly X rd (T, kThreadObjSize) a M); [unfold core_extents; cbn; tauto|]. cbn [fst snd]. unfold DT, t_qc, t_cache, t_cache_stats, kThreadObjSize in *. lia.
- left. apply own_nb. unfold DN, kBatchBytes in *. lia.
- left. destruct (rev (qc_list (st_qthread X))) as [|lb initr] eqn:Hrev.
+ exfalso. apply NE. rewrite <- (rev_involutive (qc_list (st_qthread X))), Hrev. reflexivity.
+ destruct (last_in lb initr Hrev) as [Hin EQ]. rewrite EQ in Y. eapply own_batch; [exact M | exact Hin | unfold kBatchBytes; lia].
- right. exact Y.
Qed.
End n.
End f.
