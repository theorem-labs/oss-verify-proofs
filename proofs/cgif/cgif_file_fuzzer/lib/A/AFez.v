(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YP09 YK04 YA0i YA0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0t YG0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0l YG0m.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AF0m AF0x AFl0 AFeq AFew AFex AFf2 AFeu.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YFfh.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section n. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma nth_error_run_elems : forall m lo sz j, (j < m)%nat -> nth_error (run_elems lo sz m) j = Some (lo + Z.of_nat j * sz).
Proof.
induction m as [|m IH]; intros lo sz j Hj; [lia|]. cbn [run_elems]. destruct j as [|j]; cbn [nth_error]; [f_equal; lia|].
rewrite IH by lia. f_equal. lia.
Qed.
Lemma fa_nth_elems : forall sz fl j, runs_ok fl -> 0 <= j -> fa_nth sz fl j = nth_error (fa_elems sz fl) (Z.to_nat j).
Proof.
intros sz fl. induction fl as [|[lo k|o] t IH]; intros j Hr Hj.
- cbn. destruct (Z.to_nat j); reflexivity.
- inversion Hr as [|x y Hk Ht]; subst. cbn [fa_nth]. rewrite fa_elems_cons_run.
destruct (Z.ltb_spec j k).
+ rewrite nth_error_app1 by (rewrite run_elems_length; lia). rewrite nth_error_run_elems by lia. f_equal. rewrite Z2Nat.id by lia. reflexivity.
+ rewrite nth_error_app2 by (rewrite run_elems_length; lia). rewrite run_elems_length. rewrite IH by (assumption || lia). f_equal. lia.
- inversion Hr as [|x y Hk Ht]; subst. cbn [fa_nth]. rewrite fa_elems_cons_one. destruct (Z.eqb_spec j 0) as [->|Hne]; [reflexivity|].
replace (Z.to_nat j) with (Datatypes.S (Z.to_nat (j - 1))) by lia. cbn [nth_error]. apply IH; [assumption | lia].
Qed.
Lemma in_combine_seq : forall (l0 : list Z) (s i : nat) vv, In (i, vv) (combine (seq s (length l0)) l0) -> (s <= i)%nat /\ nth_error l0 (i - s) = Some vv.
Proof.
induction l0 as [|y t IH]; intros s i vv H; [destruct H|]. cbn [length combine seq] in H. destruct H as [H|H].
- injection H as <- <-. split; [lia|]. rewrite Nat.sub_diag. reflexivity.
- destruct (IH _ _ _ H) as [H1 H2]. split; [lia|]. replace (i - s)%nat with (Datatypes.S (i - Datatypes.S s)) by lia. cbn [nth_error]. exact H2.
Qed.
Lemma nth_error_combine_seq : forall (l0 : list Z) (s i : nat) vv, nth_error l0 i = Some vv -> In ((s + i)%nat, vv) (combine (seq s (length l0)) l0).
Proof.
induction l0 as [|y t IH]; intros s i vv H; [destruct i; discriminate|]. cbn [length combine seq]. destruct i as [|i].
- cbn in H. injection H as <-. left. f_equal. lia.
- right. replace (s + Datatypes.S i)%nat with (Datatypes.S s + i)%nat by lia. apply IH. exact H.
Qed.
Section u.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (X : astate) (rd rd' : reader).
Hypothesis M : ARm B ly X rd.
Variables (c off : Z).
Hypothesis Hci : st_cache_inited X = true.
Hypothesis Hc : 1 <= c <= 30.
Let x : Z := off - region_off c.
Hypothesis Hx : 0 <= x < rg_alloc_user (reg X c).
Hypothesis Hxm : x mod class_size c = 0.
Hypothesis Hxni : ~ In x (class_elems X c).
Hypothesis HROOM : 4 * (Z.of_nat (length (class_elems X c)) + 1 + (0 + bslack c 0 + 2 * (EV_MAX - st_nev X))) <= rg_mapped_fa (reg X c).
Let p : pclass := cache X c.
Let l : list Z := pc_chunks (cache X c).
Let cnt : Z := Z.of_nat (length (pc_chunks (cache X c))).
Let N : Z := max_cached c / 2.
Let old : Z := fa_len (rg_free (reg X c)).
Definition full : bool := Z.of_nat (length (pc_chunks (cache X c))) =? max_cached c.
Definition X1 : astate := if full then XK_drain c X else X.
Definition S' : astate := XK_push c off X1.
Definition CNTP : Z := if full then cnt - N else cnt.
Let L : list Z := kdrained c X.
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Definition PCv : Z := T + t_cache + 80 * c.
Definition RGv : Z := SB + kRegionInfoOff + 128 * c.
Definition FAv : Z := fa_base ly c.
Definition SLOTv : Z := PCv + 16 + 4 * CNTP.
Definition DSTv : Z := FAv + 4 * old.
Variable sp : Z.
Hypothesis Hsp : ly_stk_lo ly + KSTACK <= sp <= ly_stk_hi ly.
Hypothesis IMG : img_cover ly.
Definition DT (a : Z) : Prop := (PCv <= a < PCv + 4) \/ (SLOTv <= a < SLOTv + 4) \/ (T + t_cache + 2576 <= a < T + t_cache + 2584).
Definition DR (a : Z) : Prop := full = true /\ ((RGv <= a < RGv + 8) \/ (RGv + 16 <= a < RGv + 24) \/ (RGv + 80 <= a < RGv + 88)).
Definition DF (a : Z) : Prop := full = true /\ DSTv <= a < DSTv + 4 * N.
Definition DS (a : Z) : Prop := sp - KSTACK <= a < sp.
Definition D (a : Z) : Prop := DT a \/ DR a \/ DF a \/ DS a.
Hypothesis AG : forall a, 0 <= a < 2 ^ 64 -> ~ D a -> rd' a = rd a.
Hypothesis VIS : forall a, rd a <> None -> rd' a <> None.
Hypothesis NEW_cnt : forall i, (i < 4)%nat -> rd' (PCv + Z.of_nat i) = Some (YG0f.le_byte (CNTP + 1) 4 i).
Hypothesis NEW_slot : forall i, (i < 4)%nat -> rd' (SLOTv + Z.of_nat i) = Some (YG0f.le_byte (x / 16) 4 i).
Hypothesis NEW_rg0 : full = true -> forall i, (i < 8)%nat -> rd' (RGv + Z.of_nat i) = Some (YG0f.le_byte 0 8 i).
Hypothesis NEW_rg16 : full = true -> forall i, (i < 8)%nat -> rd' (RGv + 16 + Z.of_nat i) = Some (YG0f.le_byte (old + N) 8 i).
Hypothesis NEW_fa : full = true -> forall (j : nat) v, (Z.of_nat j < N) -> nth_error l (Z.to_nat (cnt - N) + j)%nat = Some v ->
forall i, (i < 4)%nat -> rd' (DSTv + 4 * Z.of_nat j + Z.of_nat i) = Some (YG0f.le_byte (v / 16) 4 i).
Hypothesis CONST' : Forall (cell_holds B ly rd') (as_const B ly).
Ltac drop_mem := clear AG VIS NEW_cnt NEW_slot NEW_rg0 NEW_rg16 NEW_fa CONST'.
Ltac geo := drop_mem.
Let WF : Wf (as_universe B) X := am_wf B ly X rd M.
Let LO : layout_ok ly := am_layout B ly X rd M.
Lemma HLc : (Z.to_nat c < length (st_cache X))%nat.
Proof. geo. rewrite (wf_len_cache _ _ _ _ _ WF). lia. Qed.
Lemma HLr : (Z.to_nat c < length (st_regions X))%nat.
Proof. geo. rewrite (wf_len_regions _ _ _ _ _ WF). lia. Qed.
Lemma CLS : cls_ok c (reg X c) (cache X c) true (chunk_offs X c) (batch_offs X c).
Proof. geo. pose proof (wf_classes _ _ _ _ _ WF c ltac:(lia)) as C. unfold wf_class in C. rewrite Hci in C. exact C. Qed.
Lemma class_facts : 32 <= class_size c <= kMaxSize /\ class_size c mod 32 = 0 /\ 2 <= max_cached c <= 16 /\ max_cached c mod 2 = 0 /\ 1 <= N <= 8 /\ max_cached c = 2 * N.
Proof. geo.
pose proof (class_ok c ltac:(lia)) as (K1 & K2 & K3 & K4 & K5 & K6). unfold N.
assert (32 <= class_size c) by (apply Z.mod_divide in K2 as [q Hq]; [|lia]; nia).
assert (D1 : 1 <= max_cached c / 2) by (apply Z.div_le_lower_bound; lia).
assert (D2 : max_cached c / 2 <= 8) by (apply Z.div_le_upper_bound; lia).
assert (D3 : max_cached c = 2 * (max_cached c / 2)) by (pose proof (Z.div_mod (max_cached c) 2 ltac:(lia)); lia).
repeat split; lia.
Qed.
Lemma reg_facts : 0 <= old /\ 4 * old <= rg_mapped_fa (reg X c) /\ 0 <= rg_mapped_fa (reg X c) <= kFreeArrayMax /\
0 <= rg_alloc_user (reg X c) <= rg_mapped_user (reg X c) /\ rg_mapped_user (reg X c) <= kFreeArrayOffset /\
rg_alloc_user (reg X c) mod class_size c = 0 /\ 0 <= cnt <= max_cached c /\ pc_max p = max_cached c /\ runs_ok (rg_free (reg X c)).
Proof. geo.
pose proof CLS as CL.
pose proof (wr_alloc _ _ _ _ _ _ CL) as A1. pose proof (wr_alloc_al _ _ _ _ _ _ CL) as A3.
pose proof (wr_fa _ _ _ _ _ _ CL) as [F1 F2]. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as F3. pose proof (wr_fa_len _ _ _ _ _ _ CL) as F4.
pose proof (wr_runs _ _ _ _ _ _ CL) as RU. pose proof (fa_len_nonneg _ RU) as F0. pose proof (wr_cache _ _ _ _ _ _ CL) as [C1 C2].
pose proof (mapped_user_bound (as_universe B) 0 0 0 X c WF ltac:(lia)) as MB.
unfold old, cnt, p. unfold kUserMapSize, EV_MAX, kFreeArrayOffset in *. repeat split; try assumption; lia.
Qed.
Lemma L_facts : full = true -> length L = Z.to_nat N /\ l = kkeep c X ++ L /\ Z.of_nat (length (kkeep c X)) = cnt - N /\ cnt = 2 * N.
Proof. geo.
intros Hf. unfold full in Hf. apply Z.eqb_eq in Hf. pose proof class_facts as (_ & _ & _ & _ & K5 & K6). pose proof reg_facts as (_ & _ & _ & _ & _ & _ & _ & PM & _).
unfold L, kdrained, kkeep, l, cnt, N, p in *. rewrite PM. rewrite length_skipn, length_firstn, firstn_skipn. repeat split; lia.
Qed.
Lemma X1_eq : forall f, full = f -> X1 = (if f then XK_drain c X else X). Proof. intros f <-. reflexivity. Qed.
Lemma S'_regions : st_regions S' = st_regions X1.   Proof. geo. reflexivity. Qed.
Lemma X1_chunks : st_chunks X1 = st_chunks X.      Proof. geo. unfold X1. destruct full; reflexivity. Qed.
Lemma S'_chunks : st_chunks S' = st_chunks X.      Proof. geo. unfold S'. cbn. exact X1_chunks. Qed.
Lemma S'_secs : st_secs S' = st_secs X.            Proof. geo. unfold S', X1. destruct full; reflexivity. Qed.
Lemma S'_sec_arr : st_sec_arr S' = st_sec_arr X.   Proof. geo. unfold S', X1. destruct full; reflexivity. Qed.
Lemma S'_sec_res : st_sec_reserved S' = st_sec_reserved X. Proof. geo. unfold S', X1. destruct full; reflexivity. Qed.
Lemma S'_fs : st_fs S' = st_fs X.                  Proof. geo. unfold S', X1. destruct full; reflexivity. Qed.
Lemma S'_qglobal : st_qglobal S' = st_qglobal X.   Proof. geo. unfold S', X1. destruct full; reflexivity. Qed.
Lemma S'_qthread : st_qthread S' = st_qthread X.   Proof. geo. unfold S', X1. destruct full; reflexivity. Qed.
Lemma S'_depot : st_depot S' = st_depot X.         Proof. geo. unfold S', X1. destruct full; reflexivity. Qed.
Lemma S'_cinit : st_cache_inited S' = true.        Proof. geo. unfold S', X1. destruct full; cbn; exact Hci. Qed.
Lemma S'_inited : st_internal_inited S' = st_internal_inited X. Proof. geo. unfold S', X1. destruct full; reflexivity. Qed.
Lemma S'_nev : st_nev S' = st_nev X.               Proof. geo. unfold S', X1. destruct full; reflexivity. Qed.
Lemma S'_len_cache : length (st_cache X1) = length (st_cache X). Proof. geo. unfold X1, XK_drain, upd_pc, upd_reg. destruct full; cbn; [apply zupd_length | reflexivity]. Qed.
Lemma S'_len_regions : length (st_regions X1) = length (st_regions X). Proof. geo. unfold X1, XK_drain, upd_pc, upd_reg. destruct full; cbn; [apply zupd_length | reflexivity]. Qed.
Lemma frames' : frames S' = frames X.              Proof. geo. unfold frames. rewrite S'_fs. reflexivity. Qed.
Lemma all_batches_S' : all_batches S' = all_batches X. Proof. geo. unfold all_batches. rewrite S'_qthread, S'_qglobal. reflexivity. Qed.
Lemma q_items_S' : q_items S' = q_items X. Proof. geo. unfold q_items. rewrite all_batches_S'. reflexivity. Qed.
Lemma reg_other' : forall c', 0 <= c' -> c' <> c -> reg S' c' = reg X c'.
Proof. geo. intros c' H1 H2. unfold S', XK_push. rewrite reg_upd_pc. unfold X1, XK_drain. destruct full; [|reflexivity]. rewrite reg_upd_pc. apply reg_upd_reg_other; lia. Qed.
Definition regc' : region := let r := reg X c in
if full then mkRegion (rg_mapped_user r) (rg_alloc_user r) (rg_mapped_fa r) (fa_push_list (rg_free r) L) (rg_holes r) else r.
Lemma reg_c' : reg S' c = regc'.
Proof. geo. unfold S', XK_push, regc'. rewrite reg_upd_pc. unfold X1, XK_drain. destruct full; [|reflexivity]. rewrite reg_upd_pc. apply reg_upd_reg; [lia | exact HLr]. Qed.
Lemma reg_c_fields : rg_mapped_user (reg S' c) = rg_mapped_user (reg X c) /\ rg_alloc_user (reg S' c) = rg_alloc_user (reg X c) /\
rg_mapped_fa (reg S' c) = rg_mapped_fa (reg X c) /\ rg_holes (reg S' c) = rg_holes (reg X c) /\
rg_free (reg S' c) = (if full then fa_push_list (rg_free (reg X c)) L else rg_free (reg X c)).
Proof. geo. rewrite reg_c'. unfold regc'. destruct full; cbn; repeat split; reflexivity. Qed.
Lemma reg_fields' : forall c', 0 <= c' -> rg_mapped_user (reg S' c') = rg_mapped_user (reg X c') /\ rg_alloc_user (reg S' c') = rg_alloc_user (reg X c') /\
rg_mapped_fa (reg S' c') = rg_mapped_fa (reg X c') /\ rg_holes (reg S' c') = rg_holes (reg X c').
Proof. geo. intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [pose proof reg_c_fields; tauto | rewrite reg_other' by lia; repeat split; reflexivity]. Qed.
Lemma cache_other' : forall c', 0 <= c' -> c' <> c -> cache S' c' = cache X c'.
Proof. geo. intros c' H1 H2. unfold S', XK_push. cbv zeta. rewrite cache_upd_pc_other by lia. unfold X1, XK_drain. destruct full; [|reflexivity]. cbv zeta. rewrite cache_upd_pc_other by lia. rewrite cache_upd_reg. reflexivity. Qed.
Definition keptl : list Z := if full then kkeep c X else l.
Lemma cache_X1 : cache X1 c = mkPC (pc_max p) keptl /\ (Z.to_nat c < length (st_cache X1))%nat.
Proof. geo.
unfold X1, keptl, XK_drain. destruct full.
- cbv zeta. split; [rewrite cache_upd_pc; [reflexivity | lia | cbn; exact HLc]|]. unfold upd_pc, upd_reg. cbn [st_cache set_cache set_regions]. rewrite zupd_length. exact HLc.
- split; [unfold p, l; destruct (cache X c); reflexivity | exact HLc].
Qed.
Lemma cache_c' : cache S' c = mkPC (pc_max p) (keptl ++ [x]).
Proof. geo. destruct cache_X1 as [E Lc]. unfold S', XK_push. cbv zeta. rewrite cache_upd_pc; [|lia|exact Lc]. rewrite E. reflexivity. Qed.
Lemma keptl_len : Z.of_nat (length keptl) = CNTP.
Proof. geo. unfold keptl, CNTP. destruct full eqn:Hf; [|reflexivity]. destruct (L_facts Hf) as (_ & _ & E & _). exact E. Qed.
Lemma chunk_offs' : forall c', chunk_offs S' c' = chunk_offs X c'. Proof. geo. intros c'. unfold chunk_offs. rewrite S'_chunks. reflexivity. Qed.
Lemma batch_offs' : forall c', batch_offs S' c' = batch_offs X c'. Proof. geo. intros c'. unfold batch_offs. rewrite all_batches_S'. reflexivity. Qed.
Lemma sec_extents' : sec_extents ly S' = sec_extents ly X. Proof. geo. unfold sec_extents. rewrite S'_chunks. reflexivity. Qed.
Lemma asecA_S' : forall A, asecA ly X A -> asecA ly S' A.
Proof. intros A H e He. rewrite sec_extents' in He. exact (H e He). Qed.
Lemma flat_map_ext_in {U V} : forall (f g : U -> list V) (l0 : list U), (forall y, In y l0 -> f y = g y) -> flat_map f l0 = flat_map g l0.
Proof. clear. intros f g l0. induction l0 as [|y t IH]; intros H; cbn; [reflexivity|]. rewrite H by (left; reflexivity). rewrite IH; [reflexivity|]. intros z Hz. apply H. right. exact Hz. Qed.
Lemma fa_poison' : fa_poison_ranges ly S' = fa_poison_ranges ly X.
Proof. geo.
unfold fa_poison_ranges. rewrite S'_chunks. f_equal. apply flat_map_ext_in. intros c' Hc'. apply zseq_In in Hc'.
destruct (reg_fields' c' ltac:(lia)) as (E1 & E2 & E3 & E4). rewrite E1, E3. reflexivity.
Qed.
Lemma aareas' : aareas S' = aareas X.
Proof. geo.
unfold aareas. rewrite S'_chunks, S'_sec_res. f_equal. apply flat_map_ext_in. intros c' Hc'. apply zseq_In in Hc'.
destruct (reg_fields' c' ltac:(lia)) as (E1 & E2 & E3 & E4). rewrite E1, E3. reflexivity.
Qed.
Lemma prim_committed' : prim_committed S' = prim_committed X.
Proof. geo.
unfold S', XK_push. cbv zeta. change (prim_committed (upd_pc c ?[pp] X1)) with (prim_committed X1).
unfold X1, XK_drain. destruct full; [|reflexivity]. cbv zeta.
match goal with |- prim_committed (upd_pc c ?pp ?XX) = _ => change (prim_committed (upd_pc c pp XX)) with (prim_committed XX) end.
unfold upd_reg. rewrite prim_committed_set_region by (lia || exact HLr). cbn [rg_mapped_user rg_mapped_fa]. unfold reg. lia.
Qed.
Lemma prim_user_mapped' : prim_user_mapped S' = prim_user_mapped X.
Proof. geo.
unfold S', XK_push. cbv zeta. change (prim_user_mapped (upd_pc c ?[pp] X1)) with (prim_user_mapped X1).
unfold X1, XK_drain. destruct full; [|reflexivity]. cbv zeta.
match goal with |- prim_user_mapped (upd_pc c ?pp ?XX) = _ => change (prim_user_mapped (upd_pc c pp XX)) with (prim_user_mapped XX) end.
unfold upd_reg. rewrite prim_user_mapped_set_region by (lia || exact HLr). cbn [rg_mapped_user]. unfold reg. lia.
Qed.
Lemma sec_live' : sec_live_bytes S' = sec_live_bytes X. Proof. geo. unfold sec_live_bytes. rewrite S'_chunks. reflexivity. Qed.
Lemma abudget_S' : abudget S' = abudget X. Proof. geo. unfold abudget, sec_hulls. rewrite S'_nev, sec_live', S'_secs  . reflexivity. Qed.
Lemma cache_dealloc_S' : cache_dealloc c off X = IRet (tt, S').
Proof. geo.
pose proof reg_facts as (F0 & F4 & _ & _ & _ & _ & _ & PM & _). unfold S', X1, full.
destruct (Z.eqb_spec (Z.of_nat (length (pc_chunks (cache X c)))) (max_cached c)) as [E|NE].
- apply cache_dealloc_eq_full; [exact Hci | lia | exact HLc | unfold p in PM; rewrite PM; exact E |].
destruct (L_facts ltac:(unfold full; apply Z.eqb_eq; exact E)) as (LL & _ & _ & C2). fold (kdrained c X). fold L. rewrite LL.
pose proof class_facts as (_ & _ & _ & _ & K5 & K6). rewrite Z2Nat.id by lia.
assert (LEN : old + cnt <= Z.of_nat (length (class_elems X c))).
{ rewrite class_elems_eq, !length_app, !Nat2Z.inj_add, (fa_elems_length (class_size c) (rg_free (reg X c)) (wr_runs _ _ _ _ _ _ CLS)). unfold old, cnt. clear. lia. }
pose proof (bslack_le c 0 ltac:(lia)) as BS. pose proof (YG0l.return_room _ _ _ _ X c WF ltac:(lia) HROOM) as NEV  . unfold old, cnt in *. clear - HROOM LEN BS NEV F0 F4 K5 C2. unfold EV_MAX in *. lia.
- apply cache_dealloc_eq_push; [exact Hci | unfold p in PM; rewrite PM; exact NE].
Qed.
Lemma WS'_post : cache_dealloc_post (as_universe B) 0 0 0 X c x true (tt, S').
Proof. geo.
pose proof (cache_dealloc_ok (as_universe B) 0 0 0 X c off true WF ltac:(lia) Hx Hxm Hxni HROOM) as OK.
rewrite cache_dealloc_S' in OK. exact OK.
Qed.
Lemma WS' : Wf (as_universe B) S'. Proof. exact (proj1 WS'_post). Qed.
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
Lemma HIGH : kHighMemBeg <= ly_prim ly /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\ zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\
kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd /\
ly_prim ly <= SB /\ SB + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\
region_off c = c * 2 ^ 32 /\ FAv = SB + c * 2 ^ 32 + kFreeArrayOffset /\ RGv = SB + kRegionInfoOff + 128 * c /\
0 <= old /\ 4 * (old + (if full then N else 0)) <= rg_mapped_fa (reg X c) /\ rg_mapped_fa (reg X c) <= kFreeArrayMax /\ 1 <= N <= 8 /\
T + t_cache + 80 <= PCv /\ PCv + 80 <= T + t_cache + 2480 /\ 0 <= CNTP /\ CNTP + 1 <= max_cached c /\ max_cached c <= 16 /\
(T + kThreadObjSize <= ly_stk_lo ly \/ ly_stk_hi ly <= T) /\ (ly_prim ly + kPrimResvSize <= ly_stk_lo ly \/ ly_stk_hi ly <= ly_prim ly) /\
(T + kThreadObjSize <= ly_prim ly \/ ly_prim ly + kPrimResvSize <= T).
Proof. geo.
pose proof (lo_high _ LO) as IP. unfold in_high in IP. cbn [fst snd] in IP.
pose proof (lo_app _ LO) as HA. pose proof (lo_disj _ LO) as HD0.
pose proof (Forall_nth_f _ _ 2 _ HA eq_refl) as IT. cbn beta in IT. cbn [fst snd] in IT.
pose proof (zone3_intro ly T kThreadObjSize IMG ltac:(clear_all; unfold kThreadObjSize; lia) IT (pairwise_ij_f _ _ 2 6 _ _ HD0 eq_refl eq_refl)) as ZT. clear HA IT.
pose proof (lo_top _ LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). pose proof (lo_space_in _ LO) as [S1 S2].
pose proof HD0 as HD. clear HD0. unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD.
destruct HD as (DP & DQ & DT' & _).
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PT DP]. apply Forall_cons_iff in DP as [_ DP].
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PSTK _].
apply Forall_cons_iff in DT' as [_ DT']. apply Forall_cons_iff in DT' as [_ DT']. apply Forall_cons_iff in DT' as [_ DT']. apply Forall_cons_iff in DT' as [_ DT'].
apply Forall_cons_iff in DT' as [_ DT']. apply Forall_cons_iff in DT' as [TSTK _].
unfold zdisjoint in PT, PSTK, TSTK. cbn [fst snd] in PT, PSTK, TSTK.
pose proof class_facts as (K1 & K2 & K3 & K4 & K5 & K6). pose proof reg_facts as (F0 & F4 & [F1 F3] & A1 & MU & AL & [C1 C2] & PM & RU).
assert (ROFF : region_off c = c * 2 ^ 32) by (unfold region_off; rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
assert (ROOM : 4 * (old + (if full then N else 0)) <= rg_mapped_fa (reg X c)).
{ destruct full eqn:Hf; [|lia]. destruct (L_facts Hf) as (_ & _ & _ & CC).
assert (LEN : old + cnt <= Z.of_nat (length (class_elems X c))).
{ rewrite class_elems_eq, !length_app, !Nat2Z.inj_add, (fa_elems_length (class_size c) (rg_free (reg X c)) (wr_runs _ _ _ _ _ _ CLS)). unfold old, cnt. clear. lia. }
pose proof (bslack_le c 0 ltac:(lia)) as BS. pose proof (YG0l.return_room _ _ _ _ X c WF ltac:(lia) HROOM) as NEV  . unfold old, cnt in *. clear - HROOM LEN BS NEV F0 F4 K5 CC. unfold EV_MAX in *. lia. }
assert (CN : 0 <= CNTP /\ CNTP + 1 <= max_cached c).
{ unfold CNTP. destruct full eqn:Hf.
- destruct (L_facts Hf) as (_ & _ & _ & CC). lia.
- unfold full in Hf. apply Z.eqb_neq in Hf. unfold cnt in *. lia. }
unfold FAv, RGv, PCv, fa_base. rewrite ROFF. unfold t_cache, kSpaceSize in *.
split; [clear - IP; lia|]. split; [clear - IP; lia|]. split; [exact ZT|]. split; [clear - ZT; unfold zone3 in ZT; lia|].
assert (ZT' : 4096 <= T) by (clear - ZT; unfold zone3 in ZT; lia). clear ZT.
repeat split; try assumption; try lia.
Qed.
Lemma D_cases : forall a, D a ->
(T <= a < T + kThreadObjSize /\ DT a) \/ (ly_prim ly <= a < ly_prim ly + kPrimResvSize /\ (DR a \/ DF a)) \/ (ly_stk_lo ly <= a < ly_stk_hi ly).
Proof. geo.
intros a Ha. pose proof HIGH as HI. unfold kThreadObjSize, kSpaceSize, kPrimResvSize, kFreeArrayOffset, kRegionInfoOff, kFreeArrayMax, t_cache in *.
destruct Ha as [Y|[Y|[Y|Y]]].
- left. split; [|exact Y]. unfold DT, SLOTv, t_cache in Y. lia.
- right; left. split; [|left; exact Y]. destruct Y as [_ Y]. lia.
- right; left. split; [|right; exact Y]. destruct Y as [Hf Y]. unfold DSTv in Y. rewrite Hf in HI. lia.
- do 2 right. unfold DS, KSTACK in *. lia.
Qed.
Ltac zget HI x sz Z := assert (Z : zone3cases x sz) by (clear - HI; unfold zone3 in HI; tauto); unfold zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg in Z.
Definition ok (a : Z) : Prop := 0 <= a < 2 ^ 64 /\ ~ D a.
Definition okr (lo len : Z) : Prop := forall a, lo <= a < lo + len -> ok a.
Lemma AGok : forall a, ok a -> rd' a = rd a. Proof. intros a [H1 H2]. apply AG; assumption. Qed.
Ltac hnum := ceil; unfold zone3, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighShadowEnd, kHighMemEnd, kBatchBytes, kThreadObjSize, kPage, kSpaceSize, kPrimResvSize, KSTACK in *.
Ltac tbnum := rewrite ?(ts_inst B TB), ?(ts_depot B TB), ?(ts_store B TB), ?(ts_ial_lo B TB), ?(ts_ial_hi B TB), ?(ts_ial_w B TB), ?(ts_ial_flag B TB) in *;
unfold TFIB_INST, TFIB_DEPOT, TFIB_STORE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W, TFIB_IAL_FLAG, TFIB_IMG_LO, TFIB_IMG_END in *.
Ltac zd H := let Y := fresh "ZD" in pose proof H as Y; unfold zdisjoint in Y; cbn [fst snd] in Y; hnum; lia.
Lemma ok_below : forall a, TFIB_IMG_LO <= a < TFIB_IMG_END -> ok a.
Proof. geo.
intros a Ha. pose proof HIGH as HI. zget HI (ly_T ly) kThreadObjSize ZZ. pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & _).
split; [hnum; unfold TFIB_IMG_LO, TFIB_IMG_END in *; lia|]. intros HD.
apply D_cases in HD as [[Y _]|[[Y _]|Y]]; hnum; unfold TFIB_IMG_LO, TFIB_IMG_END in *; lia.
Qed.
Lemma ok_shb : forall a, kLowShadowBeg <= a < kHighMemBeg -> ok a.
Proof. geo.
intros a Ha. pose proof HIGH as HI. zget HI (ly_T ly) kThreadObjSize ZZ. pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & _).
split; [hnum; unfold kLowShadowBeg in *; lia|]. intros HD.
apply D_cases in HD as [[Y _]|[[Y _]|Y]]; hnum; unfold kLowShadowBeg in *; lia.
Qed.
Lemma SX : forall i j x0 y, nth_error (static_extents ly) i = Some x0 -> nth_error (static_extents ly) j = Some y -> i <> j -> zdisjoint x0 y.
Proof. geo.
intros i j x0 y Hi Hj Hne. destruct (Nat.lt_ge_cases i j).
- exact (pairwise_nth zdisjoint _ i j x0 y (lo_disj _ LO) Hi Hj H).
- apply zdisjoint_sym. apply (pairwise_nth zdisjoint _ j i y x0 (lo_disj _ LO) Hj Hi). lia.
Qed.
Lemma SECX : forall e j y, In e (sec_extents ly X) -> nth_error (static_extents ly) j = Some y -> zdisjoint e y.
Proof. geo.
intros e j y He Hj. eapply (pairwise_In zdisjoint _ e y (sec_extents ly X) (static_extents ly) eq_refl (proj2 (am_placed _ _ _ _ M)) He).
eapply nth_error_In. exact Hj.
Qed.
Lemma ok_static : forall j e a, nth_error (static_extents ly) j = Some e -> (j <> 0)%nat -> (j <> 2)%nat -> (j < 8)%nat ->
fst e <= a < fst e + snd e -> ok a.
Proof. geo.
intros j e a Hj J0 J2 J8 Ha. pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & _).
pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) e) as HE.
assert (INO : In e (owned_extents ly)).
{ unfold static_extents in Hj. rewrite nth_error_app1 in Hj by (cbn; lia). eapply nth_error_In. exact Hj. }
specialize (HE INO). unfold in_app in HE. cbn [fst snd] in HE. split; [hnum; unfold kLowShadowBeg in *; lia|]. intros HD.
apply D_cases in HD as [[Y _]|[[Y _]|Y]].
- zd (SX j 2 _ _ Hj eq_refl ltac:(lia)).
- zd (SX 0 j _ _ eq_refl Hj ltac:(lia)).
- zd (SX j 8 _ _ Hj eq_refl ltac:(lia)).
Qed.
Lemma ok_T : forall a, T <= a < T + kThreadObjSize -> ~ DT a -> ok a.
Proof. geo.
intros a Ha ND. pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & _). split; [hnum; lia|]. intros HD.
apply D_cases in HD as [[Y Z0]|[[Y _]|Y]].
- exact (ND Z0).
- zd (SX 0 2 _ _ eq_refl eq_refl ltac:(lia)).
- zd (SX 2 8 _ _ eq_refl eq_refl ltac:(lia)).
Qed.
Lemma ok_prim : forall a, ly_prim ly <= a < ly_prim ly + kPrimResvSize -> ~ DR a -> ~ DF a -> ok a.
Proof. geo.
intros a Ha NR NF. pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & _). split; [hnum; lia|]. intros HD.
apply D_cases in HD as [[Y _]|[[_ [Z0|Z0]]|Y]].
- zd (SX 0 2 _ _ eq_refl eq_refl ltac:(lia)).
- exact (NR Z0).
- exact (NF Z0).
- zd (SX 0 8 _ _ eq_refl eq_refl ltac:(lia)).
Qed.
Lemma ext_zone : forall y, In y (st_chunks X) ->
(exists c', 1 <= c' <= 30 /\ region_base ly c' <= ck_base B ly y /\ ck_base B ly y + ck_extent y <= region_base ly c' + 2 ^ 31 /\
ly_prim ly <= region_base ly c' /\ region_base ly c' + 2 ^ 32 <= ly_prim ly + kPrimResvSize) \/
(exists r, ck_beg y = PSec r kPage /\ ck_base B ly y = ly_sec ly r + kPage /\ In (ly_sec ly r, ck_extent y + kPage) (sec_extents ly X)).
Proof. geo.
intros y Hy. pose proof (chunk_facts B ly X rd y M Hy) as (G1 & G2 & _ & _ & _ & _ & _ & _ & GG).
destruct (ck_beg y) as [|o|r o|c' p'] eqn:Eby; try solve [destruct GG].
- left. cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal & Gm).
pose proof (region_in_prim ly (prim_class o) LO ltac:(lia)) as (R1 & R2 & _). exists (prim_class o). splits; lia.
- right. destruct GG as (-> & _ & Gbase & Gext & Gin & _). exists r. splits; [reflexivity | lia |].
replace (ck_extent y + kPage) with (sec_map_size (ck_req y)) by lia. exact Gin.
Qed.
Lemma user_vs_D : forall c' a, 1 <= c' <= 31 -> region_base ly c' <= a < region_base ly c' + 2 ^ 31 -> ~ DR a /\ ~ DF a.
Proof. geo.
intros c' a Hc' Ha. pose proof HIGH as (_ & _ & _ & _ & _ & _ & S1 & S2 & ROFF & EFA & ERG & F0 & ROOM & FMX & K5 & _).
unfold region_base in Ha. rewrite region_off_eq in Ha by lia. unfold DR, DF, DSTv. rewrite EFA, ERG.
unfold kRegionInfoOff, kFreeArrayOffset, kFreeArrayMax in *.
split; intros [Hf Y]; rewrite Hf in ROOM.
- assert (c' * 2 ^ 32 + 2 ^ 31 <= 2 ^ 37) by nia. lia.
- destruct (Z.lt_trichotomy c' c) as [L'|[->|L']]; [| lia |].
+ pose proof (Z.mul_le_mono_nonneg_r (c' + 1) c (2 ^ 32) ltac:(lia) ltac:(lia)). lia.
+ pose proof (Z.mul_le_mono_nonneg_r (c + 1) c' (2 ^ 32) ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma ok_chunk : forall y a, In y (st_chunks X) -> ck_base B ly y <= a < ck_base B ly y + ck_extent y -> ok a.
Proof. geo.
intros y a Hy Ha. destruct (ext_zone y Hy) as [(c' & Hc' & X1' & X2 & X3 & X4)|(r & Ebk & Xb & Xin)].
- destruct (user_vs_D c' a ltac:(lia) ltac:(lia)) as [N1 N2]. apply ok_prim; [lia | exact N1 | exact N2].
- pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & _).
pose proof (proj1 (Forall_forall _ _) (proj1 (am_placed _ _ _ _ M)) _ Xin) as (_ & [I1 I2] & I3). cbn [fst snd] in I1, I2, I3.
split; [hnum; unfold alloc_ceiling, sp_window_lo, stack_max_size, kPage in *; lia|]. intros HD.
apply D_cases in HD as [[Y _]|[[Y _]|Y]].
+ zd (SECX _ 2 _ Xin eq_refl).
+ zd (SECX _ 0 _ Xin eq_refl).
+ zd (SECX _ 8 _ Xin eq_refl).
Qed.
Lemma ok_secpage : forall y r o a, In y (st_chunks X) -> ck_beg y = PSec r o -> ly_sec ly r <= a < ly_sec ly r + kPage -> ok a.
Proof. geo.
intros y r o a Hy Eby Ha. pose proof (chunk_facts B ly X rd y M Hy) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG). rewrite Eby in GG.
destruct GG as (-> & _ & Gbase & Gext & Gin & _). pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & _).
pose proof (proj1 (Forall_forall _ _) (proj1 (am_placed _ _ _ _ M)) _ Gin) as (_ & [I1 I2] & _). cbn [fst snd] in I1, I2.
pose proof (req_size_bounds (ck_req y) ltac:(lia)) as (_ & Q2 & _).
split; [hnum; unfold kPage in *; lia|]. intros HD.
apply D_cases in HD as [[Y _]|[[Y _]|Y]].
- zd (SECX _ 2 _ Gin eq_refl).
- zd (SECX _ 0 _ Gin eq_refl).
- zd (SECX _ 8 _ Gin eq_refl).
Qed.
Lemma batch_geom : forall b2, In b2 (all_batches X) ->
exists xb, ly_space ly + b_self b2 = region_base ly kBatchClass + xb /\ 0 <= xb /\ xb + kBatchBytes <= 2 ^ 31.
Proof. geo.
intros b2 Hb2. pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
set (xb := b_self b2 - region_off kBatchClass).
assert (INB : In xb (batch_offs X kBatchClass)) by (rewrite batch_offs_24; apply in_map_iff; exists b2; auto).
pose proof (proj1 (Forall_forall _ _) (wr_elems _ _ _ _ _ _ CL) xb ltac:(rewrite !in_app_iff; tauto)) as [B1 B2].
pose proof (wr_alloc _ _ _ _ _ _ CL) as AL'. pose proof (wr_alloc_al _ _ _ _ _ _ CL) as AA.
pose proof (mapped_user_bound (as_universe B) 0 0 0 X kBatchClass WF ltac:(unfold kBatchClass; lia)) as MB.
assert (CS : class_size kBatchClass = 8192) by reflexivity. rewrite CS in B2, AA. unfold kUserMapSize, EV_MAX in MB. unfold kBatchBytes.
assert (XB : xb + 8192 <= rg_alloc_user (reg X kBatchClass)).
{ apply Z.mod_divide in B2 as [q Hq]; [|lia]. apply Z.mod_divide in AA as [q' Hq']; [|lia]. assert (q < q') by nia. nia. }
exists xb. splits; try lia. unfold region_base. subst xb. lia.
Qed.
Lemma ok_batch : forall b2 a, In b2 (all_batches X) -> ly_space ly + b_self b2 <= a < ly_space ly + b_self b2 + kBatchBytes -> ok a.
Proof. geo.
intros b2 a Hb2 Ha. destruct (batch_geom b2 Hb2) as (xb & Eb & Pb & Ub).
pose proof (region_in_prim ly kBatchClass LO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & _).
destruct (user_vs_D kBatchClass a ltac:(unfold kBatchClass; lia) ltac:(unfold kBatchBytes in *; lia)) as [N1 N2].
apply ok_prim; [unfold kBatchBytes in *; lia | exact N1 | exact N2].
Qed.
Lemma ok_rinfo_at : forall a, ly_rinfo ly <= a < ly_rinfo ly + 4096 ->
~ (full = true /\ ((RGv <= a < RGv + 8) \/ (RGv + 16 <= a < RGv + 24) \/ (RGv + 80 <= a < RGv + 88))) -> ok a.
Proof. geo.
intros a Ha NW. pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & S1 & S2 & ROFF & EFA & ERG & F0 & ROOM & FMX & _). unfold ly_rinfo in Ha.
apply ok_prim; [unfold kSpaceSize, kRegionInfoOff, kPrimResvSize in *; lia | exact NW |].
unfold DF, DSTv. rewrite EFA. intros [Hf Y]. rewrite Hf in ROOM. unfold kRegionInfoOff, kFreeArrayOffset, kFreeArrayMax in *.
assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by nia. lia.
Qed.
Lemma ok_fa : forall c' i, 1 <= c' <= 31 -> 0 <= i -> 4 * i + 4 <= kFreeArrayMax -> (c' = c -> full = true -> i < old) -> okr (fa_base ly c' + 4 * i) 4.
Proof. geo.
intros c' i Hc' Hi Hi2 LOW a Ha. pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & S1 & S2 & ROFF & EFA & ERG & F0 & ROOM & FMX & _).
pose proof (region_in_prim ly c' LO Hc') as (R1 & R2 & _). unfold fa_base in Ha. unfold region_base in R1, R2. rewrite region_off_eq in Ha, R1, R2 by lia.
apply ok_prim.
- unfold kFreeArrayOffset, kFreeArrayMax in *. lia.
- unfold DR. rewrite ERG. intros [_ Y]. unfold kRegionInfoOff, kFreeArrayOffset, kFreeArrayMax in *. assert (c' * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by nia. lia.
- unfold DF, DSTv. rewrite EFA. intros [Hf Y]. destruct (Z.eq_dec c' c) as [->|NE].
+ pose proof (LOW eq_refl Hf). lia.
+ unfold kFreeArrayOffset, kFreeArrayMax in *. rewrite Hf in ROOM. destruct (Z.lt_trichotomy c' c) as [L'|[->|L']]; [| lia |].
* pose proof (Z.mul_le_mono_nonneg_r (c' + 1) c (2 ^ 32) ltac:(lia) ltac:(lia)). lia.
* pose proof (Z.mul_le_mono_nonneg_r (c + 1) c' (2 ^ 32) ltac:(lia) ltac:(lia)). lia.
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
unfold ck_base, sptr_addr. destruct (ck_beg y) as [|o|r o|c' p']; try solve [destruct GG]; cbn; lia.
Qed.
Lemma EA2 : forall y d d', In y (st_chunks X) -> aeval B ly (aoff (aoff (sptr_exp (ck_beg y)) d) d') = ck_base B ly y + d + d'.
Proof. geo.
intros y d d' Hy. pose proof (chunk_facts B ly X rd y M Hy) as (_ & _ & _ & _ & _ & _ & _ & _ & GG).
unfold ck_base, sptr_addr. destruct (ck_beg y) as [|o|r o|c' p']; try solve [destruct GG]; cbn; lia.
Qed.
Lemma EA0 : forall y, aeval B ly (sptr_exp (ck_beg y)) = ck_base B ly y. Proof. geo. reflexivity. Qed.
Ltac fcons := apply Forall_cons; [split; cbn; lia|].
Lemma cells_regions : Forall (cell_holds B ly rd') (flat_map (region_cells S') (zseq 1 31)).
Proof.
pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & S1 & S2 & ROFF & EFA & ERG & F0 & ROOM & FMX & K5 & _).
apply Forall_flat_map'. intros c' Hc'. apply zseq_In in Hc'.
assert (OLDR : Forall (cell_holds B ly rd) (region_cells X c')) by (old_in; left; apply in_flat_map; exists c'; split; [apply In_zseq; lia | exact HIN]).
assert (ER : forall d, aeval B ly (aoff (ASp (kRegionInfoOff + 128 * c')) d) = SB + kRegionInfoOff + 128 * c' + d) by (intros d; cbn; lia).
assert (ER0 : aeval B ly (ASp (kRegionInfoOff + 128 * c')) = SB + kRegionInfoOff + 128 * c') by (cbn; lia).
destruct (Z.eq_dec c' c) as [->|NE].
-
unfold region_cells. cbv zeta. unfold region_cells in OLDR. cbv zeta in OLDR.
destruct reg_c_fields as (E1 & E2 & E3 & E4 & E5). rewrite E1, E2, E3, E5.
apply Forall_cons_iff in OLDR as [O0 OLDR]. apply Forall_cons_iff in OLDR as [O8 OLDR]. apply Forall_cons_iff in OLDR as [O16 OLDR]. apply Forall_cons_iff in OLDR as [O24 OLDR].
apply Forall_cons_iff in OLDR as [O32 OLDR]. apply Forall_cons_iff in OLDR as [O40 OLDR]. apply Forall_cons_iff in OLDR as [O48 OLDR]. apply Forall_cons_iff in OLDR as [O56 OLDR].
apply Forall_cons_iff in OLDR as [O68 _].
assert (OKX : forall d, 0 <= d < 128 -> ~ (full = true /\ (d < 8 \/ 16 <= d < 24 \/ 80 <= d < 88)) -> ok (SB + kRegionInfoOff + 128 * c + d)).
{ intros d Hd NW. apply ok_rinfo_at; [unfold ly_rinfo; lia|]. unfold RGv. intros [Hf Y]. apply NW. split; [exact Hf | lia]. }
Ltac rcell O ER OKX := apply (cell_xfer _ O); intros j Hj; cbn [c_at c_w z8 z1 c8 c1] in Hj |- *; rewrite ?ER; match goal with |- ok ?a => replace a with (SB + kRegionInfoOff + 128 * c + (a - (SB + kRegionInfoOff + 128 * c))) by lia end; apply OKX; [lia | intros [_ Y]; lia].
destruct full eqn:Hf.
+ apply Forall_cons. { cbn [cell_holds c_at c_val c_w z8 c8]. intros kk Hkk. rewrite ER0. fold RGv. rewrite (NEW_rg0 eq_refl kk Hkk). reflexivity. }
apply Forall_cons. { rcell O8 ER OKX. }
apply Forall_cons. { cbn [cell_holds c_at c_val c_w z8 c8]. intros kk Hkk. rewrite ER. fold RGv. replace (SB + kRegionInfoOff + 128 * c + 16) with (RGv + 16) by (rewrite ERG; lia).
rewrite (NEW_rg16 eq_refl kk Hkk). cbn [aeval]. do 2 f_equal. destruct (L_facts Hf) as (LL & _). pose proof (fa_push_list_spec (class_size c) (rg_free (reg X c)) L) as (_ & EL & _).
rewrite EL, LL, Z2Nat.id by lia. unfold old. lia. }
apply Forall_cons. { rcell O24 ER OKX. }
apply Forall_cons. { rcell O32 ER OKX. }
apply Forall_cons. { rcell O40 ER OKX. }
apply Forall_cons. { rcell O48 ER OKX. }
apply Forall_cons. { rcell O56 ER OKX. }
apply Forall_cons; [|apply Forall_nil]. { rcell O68 ER OKX. }
+ assert (OKA : forall d, 0 <= d < 128 -> ok (SB + kRegionInfoOff + 128 * c + d)) by (intros d Hd; apply OKX; [exact Hd | intros [Hf' _]; discriminate]).
repeat (apply Forall_cons; [match goal with |- cell_holds _ _ _ ?ce => apply (cell_xfer ce); [assumption|]; intros j Hj; cbn [c_at c_w z8 z1 c8 c1] in Hj |- *; rewrite ?ER, ?ER0; match goal with |- ok ?a => replace a with (SB + kRegionInfoOff + 128 * c + (a - (SB + kRegionInfoOff + 128 * c))) by lia end; apply OKA; lia end|]).
apply Forall_nil.
- unfold region_cells. rewrite (reg_other' c') by lia. unfold region_cells in OLDR. refine (cells_xfer _ (SB + kRegionInfoOff + 128 * c') 128 _ _ OLDR).
+ intros a Ha. apply ok_rinfo_at; [unfold ly_rinfo; lia|]. unfold RGv. intros [_ Y].
destruct (Z.lt_trichotomy c' c) as [L'|[->|L']]; [| exact (NE eq_refl) |]; nia.
+ unfold cell_in. cbv zeta. repeat (apply Forall_cons; [cbn [c_at c_w z8 z1 c8 c1]; rewrite ?ER, ?ER0; cbn; lia|]). apply Forall_nil.
Qed.
Lemma okr_cache_other : forall c', 1 <= c' <= 31 -> c' <> c -> okr (T + t_cache + 80 * c') 80.
Proof. geo.
pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & S1 & S2 & ROFF & EFA & ERG & F0 & ROOM & FMX & K5 & P1 & P2 & CN1 & CN2 & MX & _).
intros c' Hc' Hne' a Ha. apply ok_T; [unfold t_cache, kThreadObjSize in *; lia|]. unfold DT, SLOTv, PCv, t_cache in *. intros [Y|[Y|Y]]; [nia | nia | lia].
Qed.
Lemma keptl_prefix : forall (i : nat) v, In (i, v) (combine (seq 0 (length keptl)) keptl) -> In (i, v) (combine (seq 0 (length l)) l).
Proof. geo.
intros i v Hiv. apply in_combine_seq in Hiv as [_ Hiv]. rewrite Nat.sub_0_r in Hiv. apply (nth_error_combine_seq l 0 i v).
unfold keptl in Hiv. destruct full eqn:Hf; [|exact Hiv]. destruct (L_facts Hf) as (_ & EL & _). rewrite EL.
rewrite nth_error_app1; [exact Hiv|]. apply (proj1 (nth_error_Some _ _)). rewrite Hiv. discriminate.
Qed.
Lemma cells_caches : Forall (cell_holds B ly rd') (flat_map (cache_cells S') (zseq 1 31)).
Proof.
pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & S1 & S2 & ROFF & EFA & ERG & F0 & ROOM & FMX & K5 & P1 & P2 & CN1 & CN2 & MX & _).
apply Forall_flat_map'. intros c' Hc'. apply zseq_In in Hc'.
assert (OLDC : Forall (cell_holds B ly rd) (cache_cells X c')).
{ old_in. right; left. apply in_flat_map. exists c'. split; [apply In_zseq; lia | exact HIN]. }
unfold cache_cells in OLDC |- *. rewrite S'_cinit. rewrite Hci in OLDC.
destruct (Z.eq_dec c' c) as [->|NE].
-
rewrite cache_c'. cbn [pc_chunks pc_max]. pose proof keptl_len as KL.
apply Forall_cons_iff in OLDC as [_ OLDC]. apply Forall_cons_iff in OLDC as [O2 OLDC]. apply Forall_cons_iff in OLDC as [O3 OLDC].
assert (OKC : forall a, PCv + 4 <= a < PCv + 16 + 4 * CNTP -> ok a).
{ intros a Ha. apply ok_T; [unfold PCv, t_cache, kThreadObjSize in *; lia|]. unfold DT, SLOTv, PCv, t_cache in *. lia. }
apply Forall_cons. { cbn [cell_holds c_at c_val c_w z4 c4 aeval]. intros kk Hkk. fold PCv. replace (T + (t_cache + 80 * c)) with PCv by (unfold PCv; lia).
rewrite NEW_cnt by exact Hkk. rewrite length_app. cbn [length]. do 2 f_equal. lia. }
apply Forall_cons. { apply (cell_xfer _ O2). intros j Hj. cbn in Hj |- *. apply OKC. unfold PCv in *. lia. }
apply Forall_cons. { apply (cell_xfer _ O3). intros j Hj. cbn in Hj |- *. apply OKC. unfold PCv in *. lia. }
rewrite length_app. cbn [length]. rewrite Nat.add_1_r, (combine_snoc _ _ _ eq_refl), map_app. apply Forall_app. split.
+ apply Forall_forall. intros ce Hce. apply in_map_iff in Hce as ([i v] & <- & Hiv).
pose proof (keptl_prefix i v Hiv) as Hiv'. apply in_combine_l in Hiv. apply in_seq in Hiv.
apply (cell_xfer _ (proj1 (Forall_forall _ _) OLDC _ ltac:(apply in_map_iff; exists (i, v); split; [reflexivity | exact Hiv']))).
intros j Hj. cbn in Hj |- *. apply OKC. unfold PCv in *. lia.
+ apply Forall_cons; [|apply Forall_nil]. cbn [fst snd cell_holds c_at c_val c_w z4 c4 aeval aoff]. intros kk Hkk.
replace (T + (t_cache + 80 * c + (16 + 4 * Z.of_nat (length keptl))) + Z.of_nat kk) with (SLOTv + Z.of_nat kk) by (unfold SLOTv, PCv; lia).
rewrite NEW_slot by exact Hkk. reflexivity.
- rewrite cache_other' by (lia || exact NE). apply (cells_xfer _ _ _ (okr_cache_other c' ltac:(lia) NE)); [|exact OLDC].
unfold cell_in, t_cache. repeat fcons. apply Forall_forall. intros ce Hce. apply in_map_iff in Hce as ([i v] & <- & Hiv). cbn [fst snd c_at c_w z4 c4 aeval aoff].
apply in_combine_l in Hiv. apply in_seq in Hiv.
pose proof (wr_cache _ _ _ _ _ _ (wf_classes _ _ _ _ _ WF c' ltac:(lia))) as WC. rewrite Hci in WC. destruct WC as [_ PL].
pose proof (class_ok c' ltac:(lia)) as (_ & _ & _ & K4' & _). cbn. lia.
Qed.
Lemma cells_chunks : Forall (cell_holds B ly rd') (flat_map chunk_cells (st_chunks S')).
Proof.
rewrite S'_chunks. apply Forall_flat_map'. intros y Hy. pose proof (chunk_facts B ly X rd y M Hy) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
apply (cells_xfer _ (ck_base B ly y) (ck_extent y)); [intros a Ha; exact (ok_chunk y a Hy Ha) | |].
- pose proof (req_size_bounds (ck_req y) ltac:(lia)) as (_ & Q2 & _).
unfold chunk_cells, kChunkHeaderSize, cell_in. apply Forall_app. split.
+ repeat (apply Forall_cons; [cbn [c_at c_w z1 z2 z4 c1 c2 c4]; rewrite ?(EA2 y), ?(EA y), ?EA0 by exact Hy; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.max Pos.max Z.pos_sub]; lia|]). apply Forall_nil.
+ destruct (Z.eqb_spec (ck_rz y) 16); [apply Forall_nil|].
repeat (apply Forall_cons; [cbn [c_at c_w z8 c8]; rewrite ?(EA2 y), ?(EA y), ?EA0 by exact Hy; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.max Pos.max Z.pos_sub]; lia|]). apply Forall_nil.
- old_in. do 2 right; left. apply in_flat_map. exists y. split; [exact Hy | exact HIN].
Qed.
Lemma cells_sec : Forall (cell_holds B ly rd') (sec_cells S').
Proof.
pose proof (wf_secondary _ _ _ _ _ WF) as XS. destruct XS as [Snd Sac Sal Sres Sral].
assert (OLDS : Forall (cell_holds B ly rd) (sec_cells X)) by (old_in; do 3 right; left; exact HIN).
unfold sec_cells in OLDS |- *. rewrite S'_sec_res, S'_sec_arr, S'_chunks.
apply Forall_cons_iff in OLDS as [O1 OLDS]. apply Forall_cons_iff in OLDS as [O2 OLDS]. apply Forall_cons_iff in OLDS as [O3 OLDS]. apply Forall_app in OLDS as [O4 O5].
pose proof (aso_cells _ (am_syms _ _ _ _ M)) as AC.
assert (OKI : okr (as_inst B) 3632) by (intros a Ha; apply ok_below; tbnum; lia).
apply Forall_cons; [apply (cell_xfer _ O1); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_sec_reserved; lia|].
apply Forall_cons; [apply (cell_xfer _ O2); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_sec_n; lia|].
apply Forall_cons; [apply (cell_xfer _ O3); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_sec_mutex; lia|].
apply Forall_app. split.
- refine (cells_xfer _ _ _ (fun a Ha => ok_static 1 _ a eq_refl ltac:(lia) ltac:(lia) ltac:(lia) Ha) _ O4).
apply Forall_forall. intros ce Hce. apply in_map_iff in Hce as ([i r] & <- & Hir). apply in_combine_l in Hir. apply in_seq in Hir.
unfold cell_in. cbn. unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *. lia.
- apply Forall_forall. intros ce Hce. pose proof (proj1 (Forall_forall _ _) O5 ce Hce) as Oc. apply in_flat_map in Hce as (y & Hy & Hce).
destruct (ck_beg y) as [|o|r o|c' p'] eqn:Eby; try solve [destruct Hce].
assert (OKP : okr (ly_sec ly r) 32) by (intros a Ha; eapply (ok_secpage y r o a Hy Eby); unfold kPage; lia).
apply (cell_xfer _ Oc). intros j Hj. apply OKP. destruct Hce as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hj |- *; lia.
Qed.
Lemma batch_own_cells_within : forall b2 nx ce, In ce (batch_own_cells b2 nx) -> cell_in (ly_space ly + b_self b2) (24 + 8 * Z.of_nat (length (b_items b2))) ce.
Proof. geo.
intros b2 nx ce Hce. unfold batch_own_cells in Hce. destruct Hce as [<-|[<-|[<-|Hce]]]; try (unfold cell_in; cbn; lia).
apply in_map_iff in Hce as ([i y] & <- & Hix). apply in_combine_l in Hix. apply in_seq in Hix. unfold cell_in; cbn; lia.
Qed.
Lemma cells_quar : Forall (cell_holds B ly rd') (quar_cells S').
Proof.
assert (OLDQ : Forall (cell_holds B ly rd) (quar_cells X)) by (old_in; do 4 right; left; exact HIN).
pose proof (aso_cells _ (am_syms _ _ _ _ M)) as AC. pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & S1 & S2 & ROFF & EFA & ERG & F0 & ROOM & FMX & K5 & P1 & P2 & CN1 & CN2 & MX & _).
assert (OKI : okr (as_inst B) 3632) by (intros a Ha; apply ok_below; tbnum; lia).
assert (OKQ : okr (T + t_qc) 32) by (intros a Ha; apply ok_T; [unfold t_qc, kThreadObjSize in *; lia|]; unfold DT, SLOTv, PCv, t_qc, t_cache in *; lia).
unfold quar_cells, qc_cells in OLDQ |- *. rewrite S'_qglobal, S'_qthread.
apply Forall_cons_iff in OLDQ as [O1 OLDQ]. apply Forall_cons_iff in OLDQ as [O2 OLDQ]. apply Forall_app in OLDQ as [OT OG].
apply Forall_cons; [apply (cell_xfer _ O1); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_cmutex; lia|].
apply Forall_cons; [apply (cell_xfer _ O2); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_rmutex; lia|].
assert (BAT : forall lst ce, (forall b2, In b2 lst -> In b2 (all_batches X)) -> In ce (batch_cells lst) -> cell_holds B ly rd ce -> cell_holds B ly rd' ce).
{ intros lst ce Hlst Hce Oc. apply In_batch_cells in Hce as (i & b2 & Hi & Hce). pose proof (nth_error_In _ _ Hi) as Hin.
pose proof (Hlst b2 Hin) as Hin2.
pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wf_quarantine _ _ _ _ _ WF)) b2 Hin2) as [L1 L2]. unfold kBatchSlots in L2.
pose proof (batch_own_cells_within b2 _ ce Hce) as [R1 R2].
apply (cell_xfer _ Oc). intros j Hj. apply (ok_batch b2); [exact Hin2 | unfold kBatchBytes; lia]. }
apply Forall_app. split.
- apply Forall_cons_iff in OT as [O3 OT]. apply Forall_cons_iff in OT as [O4 OT]. apply Forall_cons_iff in OT as [O5 OT]. apply Forall_cons_iff in OT as [O6 OT].
apply Forall_cons; [apply (cell_xfer _ O3); intros j Hj; apply OKQ; cbn in Hj |- *; lia|].
apply Forall_cons; [apply (cell_xfer _ O4); intros j Hj; apply OKQ; cbn in Hj |- *; lia|].
apply Forall_cons; [apply (cell_xfer _ O5); intros j Hj; apply OKQ; cbn in Hj |- *; lia|].
apply Forall_cons; [apply (cell_xfer _ O6); intros j Hj; apply OKQ; cbn in Hj |- *; lia|].
apply Forall_forall. intros ce Hce. apply (BAT (qc_list (st_qthread X)) ce); [intros b2 Hb2; unfold all_batches; apply in_app_iff; left; exact Hb2 | exact Hce | exact (proj1 (Forall_forall _ _) OT ce Hce)].
- apply Forall_cons_iff in OG as [G1 OG]. apply Forall_cons_iff in OG as [G2 OG]. apply Forall_cons_iff in OG as [G3 OG]. apply Forall_cons_iff in OG as [G4 OG].
apply Forall_cons; [apply (cell_xfer _ G1); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_size; lia|].
apply Forall_cons; [apply (cell_xfer _ G2); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_size; lia|].
apply Forall_cons; [apply (cell_xfer _ G3); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_size; lia|].
apply Forall_cons; [apply (cell_xfer _ G4); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_size; lia|].
apply Forall_forall. intros ce Hce. apply (BAT (qc_list (st_qglobal X)) ce); [intros b2 Hb2; unfold all_batches; apply in_app_iff; right; exact Hb2 | exact Hce | exact (proj1 (Forall_forall _ _) OG ce Hce)].
Qed.
Lemma cells_fs : Forall (cell_holds B ly rd') (fs_cells S').
Proof.
assert (OLDF : Forall (cell_holds B ly rd) (fs_cells X)) by (old_in; do 5 right; left; exact HIN).
unfold fs_cells in OLDF |- *. rewrite S'_fs.
refine (cells_xfer _ _ _ (fun a Ha => ok_static 3 _ a eq_refl ltac:(lia) ltac:(lia) ltac:(lia) Ha) _ OLDF).
unfold cell_in. cbn [fst snd]. unfold kFakeStackSize. fcons. fcons.
apply Forall_forall. intros ce Hce. apply in_map_iff in Hce as ([i h] & <- & Hih). apply in_combine_l in Hih. apply in_seq in Hih. cbn. lia.
Qed.
Lemma cells_depot : Forall (cell_holds B ly rd') (depot_cells ly S').
Proof.
assert (OLDD : Forall (cell_holds B ly rd) (depot_cells ly X)) by (old_in; do 6 right; left; exact HIN).
unfold depot_cells, depot_ids, depot_frames in OLDD |- *. rewrite S'_depot. pose proof (aso_cells _ (am_syms _ _ _ _ M)) as AC.
apply Forall_forall. intros ce Hce. apply (cell_xfer _ (proj1 (Forall_forall _ _) OLDD ce Hce)). intros j Hj. apply ok_below.
destruct Hce as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hj |- *; unfold d_nuniq, d_map1, s_total, s_block0, kLowMemEnd, kHighMemBeg in *; tbnum; lia.
Qed.
Lemma cells_ialloc : Forall (cell_holds B ly rd') (ialloc_cells B S').
Proof.
assert (OLDI : Forall (cell_holds B ly rd) (ialloc_cells B X)) by (old_in; do 7 right; left; exact HIN).
unfold ialloc_cells in OLDI |- *. rewrite S'_inited. pose proof (aso_cells _ (am_syms _ _ _ _ M)) as AC. pose proof (aso_ialloc _ (am_syms _ _ _ _ M)) as [I1 I2].
apply Forall_forall. intros ce Hce. apply (cell_xfer _ (proj1 (Forall_forall _ _) OLDI ce Hce)). intros j Hj. apply ok_below.
destruct Hce as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hj |- *; unfold kLowMemEnd, kHighMemBeg in *; tbnum; lia.
Qed.
Lemma cells_thread : Forall (cell_holds B ly rd') thread_cells.
Proof.
pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & S1 & S2 & ROFF & EFA & ERG & F0 & ROOM & FMX & K5 & P1 & P2 & CN1 & CN2 & MX & _).
assert (OLDT : Forall (cell_holds B ly rd) thread_cells) by (old_in; do 8 right; exact HIN).
unfold thread_cells in OLDT |- *. apply Forall_cons_iff in OLDT as [O1 _]. apply Forall_cons; [|apply Forall_nil].
apply (cell_xfer _ O1). intros j Hj. cbn in Hj |- *. apply ok_T; [unfold t_unwinding, kThreadObjSize in *; lia|]. unfold DT, SLOTv, PCv, t_cache, t_unwinding in *; lia.
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
pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & S1 & S2 & ROFF & EFA & ERG & F0 & ROOM & FMX & K5 & _).
intros c' i v Hc' Hi Hv kk Hkk.
pose proof (wf_classes _ _ _ _ _ WF c' Hc') as CL. pose proof (wr_fa_len _ _ _ _ _ _ CL) as FL. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as FB.
pose proof (fa_len_nonneg _ (wr_runs _ _ _ _ _ _ CL)) as FN.
destruct (Z.eq_dec c' c) as [->|NE].
- destruct reg_c_fields as (E1 & E2 & E3 & E4 & E5). rewrite E5 in Hi, Hv. destruct full eqn:Hf.
+ destruct (L_facts Hf) as (LL & EL & EK & CC). pose proof (fa_push_list_spec (class_size c) (rg_free (reg X c)) L) as (PE & PL & PR).
rewrite PL, LL, Z2Nat.id in Hi, Hv by lia. pose proof reg_facts as (_ & _ & _ & _ & _ & _ & _ & _ & RU).
rewrite (fa_nth_elems _ _ _ (PR RU)) in Hv by lia. rewrite PE in Hv. fold old in Hi, Hv, FL.
destruct (Z_lt_le_dec i old) as [LOWi|HIi].
*
rewrite nth_error_app2 in Hv by (rewrite length_rev, LL; lia). rewrite length_rev, LL in Hv.
rewrite AGok.
-- apply (am_fa B ly X rd M c i v ltac:(lia) ltac:(unfold old in LOWi; lia)); [|exact Hkk]. rewrite (fa_nth_elems _ _ _ RU) by (unfold old in LOWi; lia). rewrite <- Hv. f_equal. unfold old. lia.
-- apply (ok_fa c i ltac:(lia) ltac:(lia) ltac:(unfold old in *; lia) ltac:(intros _ _; exact LOWi)). lia.
*
rewrite nth_error_app1 in Hv by (rewrite length_rev, LL; lia). rewrite nth_error_rev, LL in Hv.
replace (PeanoNat.Nat.ltb (Z.to_nat (old + N - 1 - i)) (Z.to_nat N)) with true in Hv by (symmetry; apply PeanoNat.Nat.ltb_lt; lia).
set (jj := Z.to_nat (i - old)) in *.
assert (Ej : (Z.to_nat N - S (Z.to_nat (old + N - 1 - i)))%nat = jj) by (subst jj; lia). rewrite Ej in Hv.
replace (fa_base ly c + 4 * i + Z.of_nat kk) with (DSTv + 4 * Z.of_nat jj + Z.of_nat kk) by (unfold DSTv, FAv; subst jj; rewrite Z2Nat.id by lia; lia).
apply (NEW_fa eq_refl jj v); [subst jj; rewrite Z2Nat.id by lia; lia | | exact Hkk].
rewrite EL, nth_error_app2 by lia. rewrite <- Hv. f_equal. lia.
+ rewrite AGok; [exact (am_fa B ly X rd M c i v ltac:(lia) Hi Hv kk Hkk)|].
apply (ok_fa c i ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros _ E; rewrite Hf in E; discriminate)). lia.
- rewrite (reg_other' c') in Hi, Hv by lia. rewrite AGok; [exact (am_fa B ly X rd M c' i v Hc' Hi Hv kk Hkk)|].
apply (ok_fa c' i Hc' ltac:(lia) ltac:(lia) ltac:(intros E; exfalso; exact (NE E))). lia.
Qed.
Lemma flags' : fs_flags_ok ly rd' S'.
Proof.
intros cid pos Hcid Hp. rewrite frames'. rewrite AGok; [exact (am_flags B ly X rd M cid pos Hcid Hp)|].
pose proof (flag_off_bounds cid pos Hcid Hp) as FB. unfold flag_addr, kFakeFlagsOff, kFakeFramesOff in *.
apply (ok_static 3 _ _ eq_refl ltac:(lia) ltac:(lia) ltac:(lia)). cbn [fst snd]. unfold kFakeStackSize. lia.
Qed.
Lemma depot' : depot_ok B ly rd' S'.
Proof.
pose proof (am_depot B ly X rd M) as (heads & links & D1 & D2 & D3). pose proof (aso_cells _ (am_syms _ _ _ _ M)) as AC.
unfold depot_ok, depot_ids, depot_traces in *. rewrite S'_depot. exists heads, links. split; [|split; [|exact D3]].
- intros b0 Hb. destruct (D1 b0 Hb) as [X1' X2]. split; [exact X1'|]. intros kk Hkk. rewrite AGok; [exact (X2 kk Hkk)|].
apply ok_below. unfold d_tab_words, kLowMemEnd, kHighMemBeg in *. tbnum. lia.
- intros id Hid. destruct (D2 id Hid) as (X1' & X2 & X3). split; [exact X1'|].
assert (NB : Z.of_nat (length (st_depot X)) <= 4096).
{ pose proof (wf_depot _ _ _ _ _ WF) as [ND INC]. pose proof (NoDup_incl_length ND INC). destruct (am_universe B ly X rd M) as (U1 & _). unfold DEPOT_MAX in U1. lia. }
pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) (ly_NB ly, kNodesBlockSize) ltac:(unfold owned_extents; cbn; tauto)) as [N1 N2]. cbn [fst snd] in N1, N2.
assert (OKN : forall kk, 0 <= kk < 16 -> ok (ly_NB ly + 16 * id + kk)).
{ intros kk Hkk. apply (ok_static 4 _ _ eq_refl ltac:(lia) ltac:(lia) ltac:(lia)). cbn [fst snd]. unfold kNodesBlockSize. lia. }
split; intros kk Hkk; rewrite AGok; auto; [apply OKN; lia|].
replace (ly_NB ly + 16 * id + 8 + Z.of_nat kk) with (ly_NB ly + 16 * id + (8 + Z.of_nat kk)) by lia. apply OKN. lia.
Qed.
Lemma fa_poison_high : forall lo len g, In (lo, len) (fa_poison_ranges ly X) -> lo <= g < lo + len -> 4096 <= g /\ g < ASAN_CEIL.
Proof. geo.
intros lo len g Hin Hg. unfold fa_poison_ranges in Hin. apply in_app_iff in Hin as [Hin|Hin].
- apply in_flat_map in Hin as (c' & Hc' & Hin). apply zseq_In in Hc'.
pose proof (region_in_prim ly c' LO ltac:(lia)) as (R1 & R2 & R3 & R4 & R5).
pose proof (wf_classes _ _ _ _ _ WF c' ltac:(lia)) as CL.
pose proof (wr_alloc _ _ _ _ _ _ CL) as A1. pose proof (wr_fa _ _ _ _ _ _ CL) as [A2 _]. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as A3.
pose proof (mapped_user_bound (as_universe B) 0 0 0 X c' WF ltac:(lia)) as MB. unfold kUserMapSize, EV_MAX, kFreeArrayMax in *.
unfold fa_base, kFreeArrayOffset in Hin. unfold region_base in *.
unfold kHighMemBeg in *. destruct Hin as [E|[E|[]]]; injection E as <- <-; lia.
- pose proof (proj1 (Forall_forall _ _) (proj1 (am_placed _ _ _ _ M)) (lo, len) Hin) as (_ & [I1 I2] & I3). cbn [fst snd] in I1, I2, I3. ceil. unfold ASAN_CEIL, kHighMemBeg, kLowShadowBeg in *. lia.
Qed.
Lemma shadow' : shadow_ok B ly rd' S'.
Proof.
intros g v Hg8 HS'. unfold ashadow in HS'. rewrite S'_chunks, fa_poison' in HS'. fold (ashadow B ly X g) in HS'.
rewrite AGok; [exact (am_shadow B ly X rd M g v Hg8 HS')|].
pose proof (YG0t.ashadow_low B ly X rd g v M HS') as [LO1 LO2].
apply ok_shb. split; [|exact LO2]. clear - LO1. unfold SHADOW_OFF, kLowShadowBeg in *. lia.
Qed.
Lemma zshadow' : zshadow_ok B ly rd'.
Proof.
pose proof (am_zshadow B ly X rd M) as ZS. unfold zshadow_ok in ZS |- *. apply Forall_forall. intros r Hr i Hi.
pose proof (proj1 (Forall_forall _ _) ZS r Hr i Hi) as Z0. unfold shadow_of_addr in Z0 |- *. change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)) in Z0 |- *.
rewrite AGok; [exact Z0|].
pose proof (proj1 (Forall_forall _ _) (owned_shadow_ranges B ly X rd M) r ltac:(rewrite !in_app_iff; tauto)) as (K1 & K2 & K3).
assert (DM : i < (snd r + 7) / 8). { pose proof (Z.div_le_mono (8 * i + 8) (snd r + 7) 8 ltac:(lia) ltac:(lia)) as DX. replace (8 * i + 8) with ((i + 1) * 8) in DX by lia. rewrite Z_div_mult in DX by lia. lia. }
pose proof (owned_shadow_bound B ly X rd (shadow_addr (fst r) + i) M ltac:(apply Exists_exists; exists r; split; [rewrite !in_app_iff; tauto | unfold in_zr; cbn [fst snd]; lia])) as [OB1 OB2].
apply ok_shb. split; [clear - OB1; unfold SHADOW_OFF, kLowShadowBeg in *; lia | exact OB2].
Qed.
Lemma vis_keep : forall Lr, Forall (range_vis B ly rd) Lr -> Forall (range_vis B ly rd') Lr.
Proof. intros Lr H. exact (Forall_range_vis_keep B ly rd rd' Lr VIS H). Qed.
Lemma junk' : Forall (range_vis B ly rd') (ajunk B ly S').
Proof.
pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & S1 & S2 & ROFF & EFA & ERG & F0 & ROOM & FMX & K5 & P1 & P2 & CN1 & CN2 & MX & _).
pose proof (am_junk B ly X rd M) as J.
unfold ajunk in J |- *. unfold quar_junk in J |- *. rewrite all_batches_S'. unfold sec_junk in J |- *. rewrite S'_sec_arr, S'_sec_res, S'_chunks.
apply Forall_cons_iff in J as [J1 J]. apply Forall_cons_iff in J as [J2 J].
apply Forall_app in J as [J3 J]. apply Forall_app in J as [J4 J].
apply Forall_cons; [intros i Hi; apply VIS; exact (J1 i Hi)|].
apply Forall_cons; [intros i Hi; apply VIS; exact (J2 i Hi)|].
apply Forall_app. split; [exact (vis_keep _ J3)|].
apply Forall_app. split; [|exact (vis_keep _ J)].
apply Forall_flat_map'. intros c' Hc'. pose proof (zseq_In _ _ _ Hc') as Hc''. unfold cache_junk. rewrite S'_cinit.
destruct (Z.eq_dec c' c) as [->|NE].
- rewrite cache_c'. cbn [pc_chunks]. rewrite length_app, Nat2Z.inj_add, keptl_len. cbn [length Z.of_nat Pos.of_succ_nat].
pose proof (proj1 (Forall_forall _ _) J4 (AT (t_cache + 80 * c + 16 + 4 * cnt), 64 - 4 * cnt)
ltac:(apply in_flat_map; exists c; split; [exact Hc'|]; unfold cache_junk; rewrite Hci; left; reflexivity)) as JO.
apply Forall_cons; [|apply Forall_nil]. intros i Hi. cbn [fst snd aeval] in Hi |- *.
destruct (Z_lt_le_dec (4 * (CNTP + 1) + i) (4 * cnt)) as [LS|LS].
+
set (jj := Z.to_nat ((4 * (CNTP + 1) + i) / 4)).
assert (JJ : Z.of_nat jj < cnt /\ 0 <= 4 * (CNTP + 1) + i - 4 * Z.of_nat jj < 4).
{ subst jj. rewrite Z2Nat.id by (apply Z.div_pos; lia). pose proof (Z.div_mod (4 * (CNTP + 1) + i) 4 ltac:(lia)). pose proof (Z.mod_pos_bound (4 * (CNTP + 1) + i) 4 ltac:(lia)).
split; [apply Z.div_lt_upper_bound; lia | lia]. }
destruct (nth_error l jj) as [v|] eqn:Hv; [|exfalso; apply (proj2 (nth_error_Some l jj)); [assert (LEN : Z.of_nat (length l) = cnt) by reflexivity; clear - JJ LEN; lia | exact Hv]].
assert (SL : cell_holds B ly rd (z4 (aoff (AT (t_cache + 80 * c)) (16 + 4 * Z.of_nat jj)) (v / 16))).
{ apply OLD. unfold acells. rewrite !in_app_iff. right; left. apply in_flat_map. exists c. split; [exact Hc'|].
unfold cache_cells. rewrite Hci. right; right; right. apply in_map_iff. exists (jj, v). split; [reflexivity|]. apply (nth_error_combine_seq l 0 jj v Hv). }
pose proof (SL (Z.to_nat (4 * (CNTP + 1) + i - 4 * Z.of_nat jj)) ltac:(cbn; lia)) as SX0. cbn [c_at c_w aeval aoff z4 c4] in SX0. rewrite Z2Nat.id in SX0 by lia.
apply VIS. match type of SX0 with rd ?a = _ => match goal with |- rd ?b <> None => replace b with a by lia end end. rewrite SX0. discriminate.
+
pose proof (JO (4 * (CNTP + 1) + i - 4 * cnt) ltac:(cbn [snd]; lia)) as JX0. cbn [fst aeval] in JX0.
apply VIS. match type of JX0 with rd ?a <> None => match goal with |- rd ?b <> None => replace b with a by lia end end. exact JX0.
- rewrite cache_other' by (lia || exact NE). apply (vis_keep _). apply Forall_forall. intros r Hr. apply (proj1 (Forall_forall _ _) J4).
apply in_flat_map. exists c'. split; [exact Hc'|]. unfold cache_junk. rewrite Hci. exact Hr.
Qed.
Lemma areas' : Forall (range_vis B ly rd') (aareas S').
Proof. rewrite aareas'. exact (vis_keep _ (am_areas B ly X rd M)). Qed.
Lemma client' : Forall (range_vis B ly rd') (aclient S').
Proof. pose proof (am_client B ly X rd M) as A. unfold aclient in A |- *. rewrite frames', S'_chunks. exact (vis_keep _ A). Qed.
Lemma placed' : sec_placed ly S'.
Proof. unfold sec_placed. rewrite sec_extents'. exact (am_placed B ly X rd M). Qed.
Theorem cd_fin_ARm : ARm B ly S' rd'.
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
pose proof (aso_cells _ (am_syms _ _ _ _ M)) as AC. pose proof (aso_ialloc _ (am_syms _ _ _ _ M)) as [I1 I2]. apply ok_below.
unfold ialloc_zero in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in Hi |- *; unfold kLowMemEnd, kHighMemBeg in *; tbnum; lia.
- exact (am_tsd B ly X rd M).
- exact (am_static_img B ly X rd M).
Qed.
Lemma ALedger_S' : forall segs md, ALedger segs ly X md -> ALedger segs ly S' md.
Proof. geo.
intros segs md L'. destruct L' as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14]. constructor; try assumption.
- destruct L4 as (pieces & P1 & P2). exists pieces. split; [|exact P2].
destruct P1 as (Q1 & Q2 & Q3). split; [|split; [exact Q2|]].
+ eapply Forall_impl; [|exact Q1]. intros pc (Y1 & Y2 & Y3). cbv beta.
assert (CUT : forall z, cut_ok ly X z -> cut_ok ly S' z).
{ intros z Hz. unfold cut_ok in *. destruct Hz as [Hz|[Hz|(c' & Hc' & Hz)]]; [left; exact Hz | right; left; exact Hz | do 2 right].
exists c'. split; [exact Hc'|]. destruct (reg_fields' c' ltac:(lia)) as (E1 & _ & E3 & _). rewrite E1, E3. exact Hz. }
split; [exact Y1 | split; apply CUT; assumption].
+ intros a Ha. rewrite (Q3 a Ha). unfold prim_hole_at. split; intros NH (c' & h & Hc' & Hin & Hz); apply NH; exists c', h;
destruct (reg_fields' c' ltac:(lia)) as (_ & _ & _ & E4); [rewrite E4 in Hin | rewrite E4]; (split; [exact Hc' | split; [exact Hin | exact Hz]]).
- rewrite sec_extents'. exact L7.
- rewrite sec_extents'. exact L8.
- rewrite prim_committed', sec_extents', S'_sec_res. exact L9.
- rewrite sec_extents'. exact L12.
Qed.
Lemma D_owned : forall a, 0 <= a -> D a -> aowned B ly X a \/ DS a.
Proof. geo.
pose proof HIGH as (H1 & H2 & H3 & H4 & H5 & H6 & S1 & S2 & ROFF & EFA & ERG & F0 & ROOM & FMX & K5 & P1 & P2 & CN1 & CN2 & MX & _).
assert (PRIMCASE : forall a, ly_prim ly <= a < ly_prim ly + kPrimResvSize -> (DR a \/ DF a) -> aowned B ly X a).
{ intros a Y Z0. eapply own_prim_nonuser; [exact M | exact Y |]. intros y Hy Hsy Hr.
destruct (ext_zone y Hy) as [(c' & Hc' & X1' & X2 & X3 & X4)|(r & Ebk & Xb & Xin)].
+ pose proof (chunk_facts B ly X rd y M Hy) as (_ & _ & _ & _ & G5 & _ & _ & G8 & _).
destruct (user_vs_D c' a ltac:(lia) ltac:(lia)) as [N1 N2]. destruct Z0 as [Z0|Z0]; [exact (N1 Z0) | exact (N2 Z0)].
+ pose proof (SECX _ 0 _ Xin eq_refl) as DJ. pose proof (chunk_facts B ly X rd y M Hy) as (_ & _ & _ & _ & G5 & _ & _ & G8 & _).
unfold zdisjoint, kPage in *. cbn [fst snd] in DJ. clear - DJ G5 G8 Hr Y Xb. lia. }
intros a Ha0 HD. destruct HD as [Y|[Y|[Y|Y]]].
- left. eapply (own_core B ly X rd (T, kThreadObjSize) a M); [unfold core_extents; cbn; tauto|]. cbn [fst snd]. unfold DT, SLOTv, PCv, t_cache, kThreadObjSize in *. lia.
- left. apply PRIMCASE; [|left; exact Y]. destruct Y as [_ Y]. rewrite ERG in Y. unfold kSpaceSize, kRegionInfoOff, kPrimResvSize in *. lia.
- left. apply PRIMCASE; [|right; exact Y]. destruct Y as [Hf Y]. unfold DSTv in Y. rewrite EFA in Y. rewrite Hf in ROOM.
unfold kSpaceSize, kFreeArrayOffset, kFreeArrayMax, kPrimResvSize in *. assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by nia. lia.
- right. exact Y.
Qed.
End u.
End n.
