(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeE2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeE3.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflSafeE5.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeO2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflSafeO6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateOverlay.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import OverlayIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import OverlayHuff1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import OverlayBlock.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import OverlayTF.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import OverlayScan.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import OverlayFacts.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import CompressModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import GenBitlenModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma forallb_zrange : forall (f : Z -> bool) lo n, forallb f (zrange lo n) = true ->
  forall i, lo <= i < lo + Z.of_nat n -> f i = true.
Proof.
  intros f lo n H i Hi. rewrite forallb_forall in H. apply H. unfold zrange.
  apply in_map_iff. exists (Z.to_nat (i - lo)). split; [lia|]. apply in_seq. lia.
Qed.

(* [comment removed for export] *)
Lemma xl_table : forall lc, 0 <= lc < 256 -> xl_of_lcode (arr_get length_code_a lc + LITERALS + 1) = arr_get extra_lbits_a (arr_get length_code_a lc).
Proof.
  pose proof (forallb_zrange (fun lc => xl_of_lcode (arr_get length_code_a lc + LITERALS + 1) =? arr_get extra_lbits_a (arr_get length_code_a lc)) 0 256
                ltac:(vm_compute; reflexivity)) as H.
  intros lc Hlc. apply Z.eqb_eq. apply H. cbn [Z.of_nat Pos.of_succ_nat]. lia.
Qed.

Lemma xd_table : forall d, 0 <= d < 30 -> xd_of_dcode d = arr_get extra_dbits_a d.
Proof.
  pose proof (forallb_zrange (fun d => xd_of_dcode d =? arr_get extra_dbits_a d) 0 30 ltac:(vm_compute; reflexivity)) as H.
  intros d Hd. apply Z.eqb_eq. apply H. cbn. lia.
Qed.

Lemma sl_table : forall c, 0 <= c < 286 -> sl_of_code c = arr_get static_ltree_dl c.
Proof.
  pose proof (forallb_zrange (fun c => sl_of_code c =? arr_get static_ltree_dl c) 0 286 ltac:(vm_compute; reflexivity)) as H.
  intros c Hc. apply Z.eqb_eq. apply H. cbn. lia.
Qed.

Lemma sd_table : forall d, 0 <= d < 30 -> arr_get static_dtree_dl d = 5.
Proof.
  pose proof (forallb_zrange (fun d => arr_get static_dtree_dl d =? 5) 0 30 ltac:(vm_compute; reflexivity)) as H.
  intros d Hd. apply Z.eqb_eq. apply H. cbn. lia.
Qed.

Lemma xb_table : forall b, 0 <= b < 19 -> xb_of_bl b = arr_get extra_blbits_a b.
Proof.
  pose proof (forallb_zrange (fun b => xb_of_bl b =? arr_get extra_blbits_a b) 0 19 ltac:(vm_compute; reflexivity)) as H.
  intros b Hb. apply Z.eqb_eq. apply H. cbn. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lsum_zrange : forall f lo n, lsum f (zrange lo n) = zsum f lo n.
Proof.
  intros f lo n. unfold zrange. revert lo. induction n as [|n IH]; intros lo; [reflexivity|].
  cbn [seq map lsum]. rewrite zsum_shift, Z.add_0_r. f_equal.
  rewrite <- seq_shift, map_map. rewrite <- (IH (lo + 1)). f_equal. apply map_ext. intros; lia.
Qed.

Lemma countZ_zrange : forall P lo n, countZ P (zrange lo n) = zsum (fun i => zind (P i)) lo n.
Proof. intros. unfold countZ. rewrite lsum_zrange. apply zsum_ext. intros. unfold zind. reflexivity. Qed.

(* [comment removed for export] *)
Lemma lmax_filter_zrange : forall (P : Z -> bool) lo n m,
  0 <= lo -> lo <= m < lo + Z.of_nat n -> P m = true -> (forall i, lo <= i < lo + Z.of_nat n -> P i = true -> i <= m) ->
  lmax (fun c => c) (filter P (zrange lo n)) = m.
Proof.
  intros P lo n m Hlo Hm Pm Hmax.
  assert (IN : In m (filter P (zrange lo n))).
  { apply filter_In. split; [| exact Pm]. unfold zrange. apply in_map_iff. exists (Z.to_nat (m - lo)). split; [lia|]. apply in_seq. lia. }
  pose proof (lmax_ge (fun c => c) _ m IN) as A. cbv beta in A.
  destruct (lmax_in (fun c => c) (filter P (zrange lo n)) ltac:(intros E; rewrite E in IN; exact IN)
              ltac:(intros x Hx; apply filter_In in Hx; destruct Hx as [Hx _]; unfold zrange in Hx; apply in_map_iff in Hx; destruct Hx as (k & <- & _); lia)) as (x & Hx & Ex).
  cbv beta in Ex. apply filter_In in Hx. destruct Hx as [Hx Px]. unfold zrange in Hx. apply in_map_iff in Hx. destruct Hx as (k & Ek & Hk). apply in_seq in Hk.
  pose proof (Hmax x ltac:(lia) Px). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition osym_of (s : deflate_state) (j : Z) : osym :=
  if sym_isdist s j then OPair (sym_lcode s j) (sym_dcode s j) else OLit (sym_lcode s j).

Definition osyms (s : deflate_state) : list osym := map (fun k => osym_of s (Z.of_nat k)) (seq 0 (Z.to_nat (nsym s))).

Lemma ssum_map : forall (f : osym -> Z) (g : nat -> osym) st n,
  ssum f (map g (seq st n)) = zsum (fun j => f (g (Z.to_nat j))) (Z.of_nat st) n.
Proof.
  intros f g st n. revert st. induction n as [|n IH]; intros st; [reflexivity|].
  cbn [seq map ssum]. rewrite zsum_shift, IH, Nat2Z.id. f_equal. f_equal. lia.
Qed.

Lemma ssum_osyms : forall s f, 0 <= nsym s -> ssum f (osyms s) = zsum (fun j => f (osym_of s j)) 0 (Z.to_nat (nsym s)).
Proof.
  intros s f Hn. unfold osyms. rewrite ssum_map. apply zsum_ext. intros j Hj. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma length_osyms : forall s, 0 <= nsym s -> Z.of_nat (length (osyms s)) = nsym s.
Proof. intros. unfold osyms. rewrite length_map, length_seq. lia. Qed.

Section Block.
Variable s : deflate_state.
Hypothesis OP : overlay_pre s.
Let N := nsym s.
Let RN : 0 <= N <= ds_lit_bufsize s - 1 := op_nsym _ OP.

(* [comment removed for export] *)
Lemma fL_osyms : forall b, ob_syms b = osyms s -> forall c, 0 <= c < 286 -> fL b c = arr_get (ds_dyn_ltree_fc s) c.
Proof.
  intros b Hb c Hc. destruct (op_hist _ OP) as (HL & _ & _). rewrite (HL c) by (unfold L_CODES; lia).
  unfold fL, scount. rewrite Hb, ssum_osyms by lia. unfold END_BLOCK. f_equal.
  apply zsum_ext. intros j Hj. unfold osym_of. destruct (sym_isdist s j); reflexivity.
Qed.

Lemma gD_osyms : forall b, ob_syms b = osyms s -> forall d, 0 <= d < 30 -> gD b d = arr_get (ds_dyn_dtree_fc s) d.
Proof.
  intros b Hb d Hd. destruct (op_hist _ OP) as (_ & HD & _). rewrite (HD d) by (unfold D_CODES; lia).
  unfold gD, scount. rewrite Hb, ssum_osyms by lia.
  apply zsum_ext. intros j Hj. unfold osym_of. destruct (sym_isdist s j); reflexivity.
Qed.

Lemma NSYM_osyms : forall b, ob_syms b = osyms s -> NSYM b = N.
Proof. intros b Hb. unfold NSYM. rewrite Hb. apply length_osyms. lia. Qed.

(* [comment removed for export] *)
Lemma dcostS_osym : forall b j, 0 <= j < N ->
  dcostS b (osym_of s j) = (if sym_isdist s j then ob_lenL b (sym_lcode s j) + sym_xl s j + ob_lenD b (sym_dcode s j) + sym_xd s j else ob_lenL b (sym_lcode s j)).
Proof.
  intros b j Hj. pose proof (sym_codes s OP j Hj) as (A & B & C & Lit & M).
  unfold osym_of, dcostS. destruct (sym_isdist s j) eqn:ISD; [|reflexivity].
  destruct (M eq_refl) as (M1 & M2 & M3). unfold sym_xl, sym_xd. rewrite xd_table by (unfold D_CODES in M2; lia).
  unfold sym_lcode in *. unfold sym_isdist in ISD. destruct (sym_dist s (3 * j) =? 0); [discriminate|].
  rewrite xl_table by lia. reflexivity.
Qed.

Lemma scostS_osym : forall j, 0 <= j < N -> scostS (osym_of s j) = scost s j.
Proof.
  intros j Hj. pose proof (sym_codes s OP j Hj) as (A & B & C & Lit & M).
  unfold osym_of, scostS, scost, dcost. unfold L_CODES in A.
  destruct (sym_isdist s j) eqn:ISD.
  - destruct (M eq_refl) as (M1 & M2 & M3). unfold D_CODES in M2. unfold sym_xl, sym_xd.
    rewrite xd_table, sd_table, sl_table by lia.
    unfold sym_lcode in *. unfold sym_isdist in ISD. destruct (sym_dist s (3 * j) =? 0); [discriminate|].
    rewrite xl_table by lia. lia.
  - rewrite sl_table by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Let TP : TPF s := tree_phase s OP.

(* [comment removed for export] *)
Lemma prefix_from_core :
  (ov_hdr s - 3) + zsum (fun j => Z.max 0 (dcost (ov_LD s) (ov_DD s) s j - 24)) 0 (Z.to_nat N) <= 8 * ds_lit_bufsize s - 10 ->
  forall k, 0 <= k < N -> ov_wpos s k <= ov_rpos s k.
Proof.
  intros CORE k Hk. pose proof (op_biv _ OP) as Rbv.
  unfold ov_wpos, ov_rpos.
  assert (EXk : zsum (dcost (ov_LD s) (ov_DD s) s) 0 (Z.to_nat k) <= 24 * k + zsum (fun j => Z.max 0 (dcost (ov_LD s) (ov_DD s) s j - 24)) 0 (Z.to_nat N)).
  { pose proof (zsum_mono (dcost (ov_LD s) (ov_DD s) s) (fun j => 24 + Z.max 0 (dcost (ov_LD s) (ov_DD s) s j - 24)) 0 (Z.to_nat k) ltac:(intros; cbv beta; lia)) as M.
    rewrite zsum_add in M. change (zsum (fun _ : Z => 24) 0 (Z.to_nat k)) with (zsum (fun i : Z => 24) 0 (Z.to_nat k)) in M.
    assert (C24 : forall m lo, zsum (fun _ : Z => 24) lo m = 24 * Z.of_nat m) by (induction m; intros; [reflexivity | rewrite zsum_snoc, IHm; lia]).
    rewrite C24, Z2Nat.id in M by lia.
    replace (Z.to_nat N) with (Z.to_nat k + Z.to_nat (N - k))%nat by lia. rewrite zsum_split.
    pose proof (zsum_nonneg (fun j => Z.max 0 (dcost (ov_LD s) (ov_DD s) s j - 24)) (0 + Z.of_nat (Z.to_nat k)) (Z.to_nat (N - k)) ltac:(intros; cbv beta; lia)).
    lia. }
  lia.
Qed.

(* [comment removed for export] *)
Lemma bbl_step : forall f X mb, build_bl_tree_loop (S f) X mb =
  (if 3 <=? mb then if negb (Len X TB (arr_get bl_order_a mb) =? 0) then mb else build_bl_tree_loop f X (mb - 1) else mb).
Proof. reflexivity. Qed.

Lemma mb_le_17 : Len (ov_X5 s) TB 15 = 0 -> ov_mb s <= 17.
Proof.
  intros H. rewrite ov_mb_eq. unfold tfb_mb. rewrite bbl_step.
  change (3 <=? 18) with true. change (arr_get bl_order_a 18) with 15. rewrite H. cbn [Z.eqb negb].
  pose proof (build_bl_tree_loop_range 16 (ov_X5 s) (18 - 1) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Hypothesis HN : 1 <= N.
Hypothesis HB : tfb_branch (ov_X6 s) (fb_buf s) (fb_len s) = 1.

Let lmax := ds_l_max_code (ov_X6 s).
Let dmax := ds_d_max_code (ov_X6 s).
(* [comment removed for export] *)
Let LX : Z -> Z := fun i => Len (ov_X6 s) TL i.
Let DX : Z -> Z := fun i => Len (ov_X6 s) TD i.

Definition mkblock (FlD FlB : list Z) : oblock := {|
  ob_syms := osyms s;
  ob_lenL := fun c => arr_get (tree_dl (ov_X1 s) TL) c;
  ob_lenD := fun d => arr_get (tree_dl (ov_X2 s) TD) d;
  ob_forced := FlD;
  ob_BC := fun x => arr_get (ov_BC s) x;
  ob_BD := fun x => arr_get (tree_dl (ov_X5 s) TB) x;
  ob_bforced := FlB;
  ob_blcodes := ov_mb s + 1;
  ob_Hc1 := ov_hdr s - 3 |}.

Lemma zruns_ext : forall (L L' : Z -> Z) lo n, (forall i, lo <= i < lo + Z.of_nat n -> L i = L' i) -> zruns L lo n = zruns L' lo n.
Proof.
  intros L L' lo n H. unfold zruns.
  assert (G : forall m i cur acc, (forall j, i <= j < i + Z.of_nat m -> L j = L' j) -> zruns_go L i m cur acc = zruns_go L' i m cur acc).
  { induction m as [|m IH]; intros i cur acc Hm; cbn [zruns_go]; [reflexivity|].
    rewrite (Hm i) by lia. destruct (L' i =? 0); apply IH; intros; apply Hm; lia. }
  apply G. exact H.
Qed.

Lemma zruns_nil : forall L lo, zruns L lo 0 = [].
Proof. reflexivity. Qed.

Lemma Forall_osyms : Forall (fun x => match x with OLit c => 0 <= c < 256 | OPair lc dc => 257 <= lc <= 285 /\ 0 <= dc <= 29 end) (osyms s).
Proof.
  unfold osyms. apply Forall_forall. intros x Hx. apply in_map_iff in Hx. destruct Hx as (k & <- & Hk). apply in_seq in Hk.
  pose proof (sym_codes s OP (Z.of_nat k) ltac:(lia)) as (A & B & C & Lit & M). unfold L_CODES, D_CODES in *.
  unfold osym_of. destruct (sym_isdist s (Z.of_nat k)).
  - destruct (M eq_refl) as (M1 & M2 & M3). lia.
  - pose proof (Lit eq_refl). lia.
Qed.

Section WithTrees.
Variable zL : ztree.
Variable zD : ztree.
Variable zB : ztree.
Variable FlL : list Z.
Variable FlD : list Z.
Variable FlB : list Z.
Hypothesis TFL : tree_facts zL 286 15 (fun c => arr_get (ds_dyn_ltree_fc s) c) FlL.
Hypothesis TFD : tree_facts zD 30 15 (fun d => arr_get (ds_dyn_dtree_fc s) d) FlD.
Hypothesis TFB : tree_facts zB 19 7 (fun x => arr_get (ov_BC s) x) FlB.
Hypothesis ZL1 : forall c, zt_len zL c = arr_get (tree_dl (ov_X1 s) TL) c.
Hypothesis ZL2 : forall d, zt_len zD d = arr_get (tree_dl (ov_X2 s) TD) d.
Hypothesis ZL5 : forall x, zt_len zB x = arr_get (tree_dl (ov_X5 s) TB) x.
Hypothesis LK1 : forall c, c <> lmax + 1 -> LX c = zt_len zL c.
Hypothesis LK2 : forall d, d <> dmax + 1 -> DX d = zt_len zD d.
Hypothesis LK5 : forall x, Len (ov_X6 s) TB x = zt_len zB x.
Hypothesis G1 : LX (lmax + 1) = 65535.
Hypothesis G2 : DX (dmax + 1) = 65535.
Hypothesis MXL : ffreq (fun c => arr_get (ds_dyn_ltree_fc s) c) FlL lmax <> 0 /\ forall c, 0 <= c < 286 -> ffreq (fun c => arr_get (ds_dyn_ltree_fc s) c) FlL c <> 0 -> c <= lmax.
Hypothesis MXD : ffreq (fun d => arr_get (ds_dyn_dtree_fc s) d) FlD dmax <> 0 /\ forall d, 0 <= d < 30 -> ffreq (fun d => arr_get (ds_dyn_dtree_fc s) d) FlD d <> 0 -> d <= dmax.
Hypothesis NOFL : FlL = [].

Let b := mkblock FlD FlB.
Let RL : 0 <= lmax < 286 := ltac:(pose proof (tp_lmax _ TP); unfold L_CODES in *; exact H).
Let RD : 0 <= dmax < 30 := ltac:(pose proof (tp_dmax _ TP); unfold D_CODES in *; exact H).

(* [comment removed for export] *)
Lemma fL_freq : forall c, 0 <= c < 286 -> fL b c = arr_get (ds_dyn_ltree_fc s) c.
Proof. intros c Hc. apply fL_osyms; [reflexivity | exact Hc]. Qed.

Lemma gD_freq : forall d, 0 <= d < 30 -> gD b d = arr_get (ds_dyn_dtree_fc s) d.
Proof. intros d Hd. apply gD_osyms; [reflexivity | exact Hd]. Qed.

Lemma TFL' : tree_facts zL 286 15 (fL b) [].
Proof. rewrite <- NOFL. apply (tree_facts_ext zL 286 15 (fun c => arr_get (ds_dyn_ltree_fc s) c)); [intros c Hc; symmetry; apply fL_freq; exact Hc | exact TFL]. Qed.

Lemma TFD' : tree_facts zD 30 15 (gD b) FlD.
Proof. apply (tree_facts_ext zD 30 15 (fun d => arr_get (ds_dyn_dtree_fc s) d)); [intros d Hd; symmetry; apply gD_freq; exact Hd | exact TFD]. Qed.

(* [comment removed for export] *)
Lemma lenL_used : forall c, 0 <= c < 286 -> ob_lenL b c <> 0 -> 0 < fL b c.
Proof.
  intros c Hc Hl. cbn [ob_lenL b mkblock] in Hl.
  destruct (Z.eq_dec (fL b c) 0) as [Z0|NZ]; [| pose proof (fL_freq c Hc); pose proof (op_fc _ OP TL c); rewrite tree_fc_TL in *; lia].
  exfalso. apply Hl. rewrite <- ZL1. apply (zo_len_unused _ (tf_ok _ _ _ _ _ TFL')); [rewrite (tf_E _ _ _ _ _ TFL'); exact Hc|].
  intros U. apply (proj1 (tf_used _ _ _ _ _ TFL' c Hc)) in U. unfold ffreq in U. cbn [existsb] in U. exact (U Z0).
Qed.

Lemma lenD_used : forall d, 0 <= d < 30 -> ob_lenD b d <> 0 -> (0 <? gD b d) || forcedD b d = true.
Proof.
  intros d Hd Hl. cbn [ob_lenD b mkblock] in Hl. unfold forcedD. cbn [ob_forced b mkblock].
  destruct ((0 <? gD b d) || existsb (Z.eqb d) FlD) eqn:X; [reflexivity|]. exfalso.
  apply Bool.orb_false_iff in X. destruct X as [X1 X2]. apply Z.ltb_ge in X1.
  apply Hl. rewrite <- ZL2. apply (zo_len_unused _ (tf_ok _ _ _ _ _ TFD')); [rewrite (tf_E _ _ _ _ _ TFD'); exact Hd|].
  intros U. apply (proj1 (tf_used _ _ _ _ _ TFD' d Hd)) in U. unfold ffreq in U. rewrite X2 in U.
  pose proof (gD_freq d Hd). pose proof (op_fc _ OP TD d). rewrite tree_fc_TD in *. lia.
Qed.

(* [comment removed for export] *)
Lemma lmax_ge_256 : 256 <= lmax.
Proof.
  destruct MXL as [_ M]. apply (M 256 ltac:(lia)). rewrite NOFL. unfold ffreq. cbn [existsb].
  destruct (op_hist _ OP) as (FHL & _). rewrite (FHL 256) by (unfold L_CODES; lia). rewrite Z.eqb_refl. cbn [zind].
  pose proof (zsum_nonneg (fun j => zind (sym_lcode s j =? 256)) 0 (Z.to_nat (nsym s)) ltac:(intros; apply (proj1 (zind_le1 _)))). unfold END_BLOCK. lia.
Qed.

(* [comment removed for export] *)
Lemma LX_ok : forall i, 0 <= i <= lmax -> 0 <= LX i <= 15.
Proof. intros i Hi. exact (tp_LD _ TP i Hi). Qed.
Lemma DX_ok : forall i, 0 <= i <= dmax -> 0 <= DX i <= 15.
Proof. intros i Hi. exact (tp_DD _ TP i Hi). Qed.
Lemma LX_guard : 15 < LX (lmax + 1). Proof. rewrite G1. lia. Qed.
Lemma DX_guard : 15 < DX (dmax + 1). Proof. rewrite G2. lia. Qed.

Lemma BC_split : forall x, 0 <= x < 19 -> ob_BC b x = TDcnt LX lmax x + TDcnt DX dmax x.
Proof. intros x Hx. cbn [ob_BC b mkblock]. exact (tp_BC _ TP x Hx). Qed.

(* [comment removed for export] *)
Lemma gl_WB : zsum (ob_BC b) 0 19 <= 316.
Proof.
  rewrite (zsum_ext (ob_BC b) (fun x => TDcnt LX lmax x + TDcnt DX dmax x)) by (intros; apply BC_split; lia).
  rewrite zsum_add. pose proof (scan_total LX lmax ltac:(lia) LX_ok LX_guard). pose proof (scan_total DX dmax ltac:(lia) DX_ok DX_guard).
  change (zsum (fun i : Z => TDcnt LX lmax i) 0 19) with (zsum (TDcnt LX lmax) 0 19). change (zsum (fun i : Z => TDcnt DX dmax i) 0 19) with (zsum (TDcnt DX dmax) 0 19). lia.
Qed.

(* [comment removed for export] *)
Lemma gl_blc : 3 <= ob_blcodes b <= 19 /\ (ob_BD b 15 = 0 -> ob_blcodes b <= 18).
Proof.
  cbn [ob_blcodes ob_BD b mkblock]. pose proof (tp_mb _ TP). split; [lia|].
  intros H15. pose proof (mb_le_17 ltac:(unfold Len; exact H15)). lia.
Qed.

(* [comment removed for export] *)
Lemma gl_Hc1 : ob_Hc1 b = 14 + 3 * ob_blcodes b + zsum (fun x => ob_BC b x * (ob_BD b x + xb_of_bl x)) 0 19.
Proof.
  cbn [ob_Hc1 ob_blcodes ob_BC ob_BD b mkblock]. unfold ov_hdr.
  rewrite (zsum_ext (fun x => arr_get (ov_BC s) x * (arr_get (ov_BD s) x + arr_get extra_blbits_a x)) (fun x => arr_get (ov_BC s) x * (arr_get (tree_dl (ov_X5 s) TB) x + xb_of_bl x))); [lia|].
  intros x Hx. rewrite xb_table by lia. unfold ov_BD. rewrite <- (tree_dl_TB (ov_X6 s)), <- (Len_eq (ov_X6 s) TB x), (tp_len5 _ TP x). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma usedL_count : forall (P : Z -> Z -> bool),
  (forall i, 0 <= i <= lmax -> P i (LX i) = true -> 0 < fL b i /\ P i (ob_lenL b i) = true) ->
  zsum (fun i => zind (P i (LX i))) 0 (Z.to_nat (lmax + 1)) <= countZ (fun c => (0 <? fL b c) && P c (ob_lenL b c)) (zrange 0 286).
Proof.
  intros P HP. rewrite countZ_zrange.
  replace 286%nat with (Z.to_nat (lmax + 1) + Z.to_nat (286 - (lmax + 1)))%nat by lia. rewrite zsum_split.
  pose proof (zsum_nonneg (fun i => zind ((0 <? fL b i) && P i (ob_lenL b i))) (0 + Z.of_nat (Z.to_nat (lmax + 1))) (Z.to_nat (286 - (lmax + 1))) ltac:(intros; apply (proj1 (zind_le1 _)))).
  assert (zsum (fun i => zind (P i (LX i))) 0 (Z.to_nat (lmax + 1)) <= zsum (fun i => zind ((0 <? fL b i) && P i (ob_lenL b i))) 0 (Z.to_nat (lmax + 1))); [|lia].
  apply zsum_mono. intros i Hi. destruct (P i (LX i)) eqn:E; [| apply (proj1 (zind_le1 _))].
  destruct (HP i ltac:(lia) E) as [A B]. rewrite B. replace (0 <? fL b i) with true by (symmetry; apply Z.ltb_lt; exact A). cbn. lia.
Qed.

Lemma usedD_count : forall (P : Z -> Z -> bool),
  (forall i, 0 <= i <= dmax -> P i (DX i) = true -> ((0 <? gD b i) || forcedD b i = true) /\ P i (ob_lenD b i) = true) ->
  zsum (fun i => zind (P i (DX i))) 0 (Z.to_nat (dmax + 1)) <= countZ (fun d => ((0 <? gD b d) || forcedD b d) && P d (ob_lenD b d)) (zrange 0 30).
Proof.
  intros P HP. rewrite countZ_zrange.
  replace 30%nat with (Z.to_nat (dmax + 1) + Z.to_nat (30 - (dmax + 1)))%nat by lia. rewrite zsum_split.
  pose proof (zsum_nonneg (fun i => zind (((0 <? gD b i) || forcedD b i) && P i (ob_lenD b i))) (0 + Z.of_nat (Z.to_nat (dmax + 1))) (Z.to_nat (30 - (dmax + 1))) ltac:(intros; apply (proj1 (zind_le1 _)))).
  assert (zsum (fun i => zind (P i (DX i))) 0 (Z.to_nat (dmax + 1)) <= zsum (fun i => zind (((0 <? gD b i) || forcedD b i) && P i (ob_lenD b i))) 0 (Z.to_nat (dmax + 1))); [|lia].
  apply zsum_mono. intros i Hi. destruct (P i (DX i)) eqn:E; [| apply (proj1 (zind_le1 _))].
  destruct (HP i ltac:(lia) E) as [A B]. rewrite A, B. cbn. lia.
Qed.

(* [comment removed for export] *)
Lemma LX_lenL : forall i, 0 <= i <= lmax -> LX i = ob_lenL b i.
Proof. intros i Hi. cbn [ob_lenL b mkblock]. rewrite <- ZL1. apply LK1. lia. Qed.
Lemma DX_lenD : forall i, 0 <= i <= dmax -> DX i = ob_lenD b i.
Proof. intros i Hi. cbn [ob_lenD b mkblock]. rewrite <- ZL2. apply LK2. lia. Qed.

(* [comment removed for export] *)
Lemma gl_sc1 : forall j, 1 <= j <= 15 ->
  ob_BC b j <= countZ (fun c => (0 <? fL b c) && (ob_lenL b c =? j)) (zrange 0 286) + countZ (fun d => ((0 <? gD b d) || forcedD b d) && (ob_lenD b d =? j)) (zrange 0 30).
Proof.
  intros j Hj. rewrite BC_split by lia.
  destruct (scan_facts LX lmax ltac:(lia) LX_ok LX_guard) as (S1 & _). destruct (scan_facts DX dmax ltac:(lia) DX_ok DX_guard) as (T1 & _).
  pose proof (S1 j Hj) as A. pose proof (T1 j Hj) as B. cbv zeta in A, B.
  pose proof (usedL_count (fun _ v => v =? j)) as C. cbv beta in C.
  pose proof (usedD_count (fun _ v => v =? j)) as D. cbv beta in D.
  assert (HC : forall i, 0 <= i <= lmax -> (LX i =? j) = true -> 0 < fL b i /\ (ob_lenL b i =? j) = true).
  { intros i Hi E. rewrite <- LX_lenL by exact Hi. split; [| exact E]. apply lenL_used; [lia|]. rewrite <- LX_lenL by exact Hi. apply Z.eqb_eq in E. lia. }
  assert (HD : forall i, 0 <= i <= dmax -> (DX i =? j) = true -> ((0 <? gD b i) || forcedD b i = true) /\ (ob_lenD b i =? j) = true).
  { intros i Hi E. rewrite <- DX_lenD by exact Hi. split; [| exact E]. apply lenD_used; [lia|]. rewrite <- DX_lenD by exact Hi. apply Z.eqb_eq in E. lia. }
  specialize (C HC). specialize (D HD). lia.
Qed.

(* [comment removed for export] *)
Lemma nz_le_UV :
  zsum (fun i => zind (negb (LX i =? 0))) 0 (Z.to_nat (lmax + 1)) + zsum (fun i => zind (negb (DX i =? 0))) 0 (Z.to_nat (dmax + 1)) <= vU b + vV b.
Proof.
  unfold vU, vV.
  pose proof (usedL_count (fun _ v => negb (v =? 0))) as C. cbv beta in C.
  assert (HC : forall i, 0 <= i <= lmax -> negb (LX i =? 0) = true -> 0 < fL b i /\ negb (ob_lenL b i =? 0) = true).
  { intros i Hi E. rewrite <- LX_lenL by exact Hi. split; [| exact E]. apply lenL_used; [lia|]. rewrite <- LX_lenL by exact Hi. apply Bool.negb_true_iff in E. apply Z.eqb_neq in E. exact E. }
  specialize (C HC).
  assert (C' : countZ (fun c => (0 <? fL b c) && negb (ob_lenL b c =? 0)) (zrange 0 286) <= countZ (fun c => 0 <? fL b c) (zrange 0 286)).
  { rewrite !countZ_zrange. apply zsum_mono. intros. destruct (0 <? fL b i), (negb _); cbn; lia. }
  (* [comment removed for export] *)
  assert (D : zsum (fun i => zind (negb (DX i =? 0))) 0 (Z.to_nat (dmax + 1)) <= countZ (fun d => 0 <? gD b d) (zrange 0 30) + Z.of_nat (length (ob_forced b))).
  { rewrite countZ_zrange.
    replace 30%nat with (Z.to_nat (dmax + 1) + Z.to_nat (30 - (dmax + 1)))%nat by lia. rewrite zsum_split.
    pose proof (zsum_nonneg (fun i => zind (0 <? gD b i)) (0 + Z.of_nat (Z.to_nat (dmax + 1))) (Z.to_nat (30 - (dmax + 1))) ltac:(intros; apply (proj1 (zind_le1 _)))).
    pose proof (zsum_existsb_le (ob_forced b) 0 (Z.to_nat (dmax + 1))) as F.
    assert (zsum (fun i => zind (negb (DX i =? 0))) 0 (Z.to_nat (dmax + 1)) <= zsum (fun i => zind (0 <? gD b i)) 0 (Z.to_nat (dmax + 1)) + zsum (fun u => zind (existsb (Z.eqb u) (ob_forced b))) 0 (Z.to_nat (dmax + 1))); [|lia].
    rewrite <- zsum_add. apply zsum_mono. intros i Hi. destruct (Z.eqb_spec (DX i) 0) as [E|NE]; cbn [negb]; [pose proof (zind_le1 (0 <? gD b i)); pose proof (zind_le1 (existsb (Z.eqb i) (ob_forced b))); cbn [zind]; lia|].
    pose proof (lenD_used i ltac:(lia) ltac:(rewrite <- DX_lenD by lia; exact NE)) as U. unfold forcedD in U.
    destruct (0 <? gD b i), (existsb (Z.eqb i) (ob_forced b)); cbn in U |- *; lia. }
  lia.
Qed.

Lemma gl_sc23 : zsum (ob_BC b) 1 15 + 3 * ob_BC b 16 <= vU b + vV b /\ 4 * ob_BC b 16 <= vU b + vV b.
Proof.
  destruct (scan_facts LX lmax ltac:(lia) LX_ok LX_guard) as (_ & S2 & S3 & _). destruct (scan_facts DX dmax ltac:(lia) DX_ok DX_guard) as (_ & T2 & T3 & _).
  cbv zeta in S2, S3, T2, T3. pose proof nz_le_UV.
  rewrite (zsum_ext (ob_BC b) (fun x => TDcnt LX lmax x + TDcnt DX dmax x) 1 15) by (intros; apply BC_split; lia). rewrite zsum_add.
  change (zsum (fun i : Z => TDcnt LX lmax i) 1 15) with (zsum (TDcnt LX lmax) 1 15). change (zsum (fun i : Z => TDcnt DX dmax i) 1 15) with (zsum (TDcnt DX dmax) 1 15).
  rewrite (BC_split 16) by lia. unfold REP_3_6 in *. lia.
Qed.

(* [comment removed for export] *)
Lemma lmaxc_eq : lmaxc b = lmax.
Proof.
  unfold lmaxc. destruct MXL as [M1 M2]. rewrite NOFL in M1, M2. unfold ffreq in M1, M2. cbn [existsb] in M1, M2.
  apply (lmax_filter_zrange (fun c => 0 <? fL b c) 0 286 lmax); [lia | change (0 + Z.of_nat 286) with 286; lia | |].
  - apply Z.ltb_lt. rewrite fL_freq by lia. pose proof (op_fc _ OP TL lmax) as R. rewrite tree_fc_TL in R. lia.
  - intros i Hi Pi. change (0 + Z.of_nat 286) with 286 in Hi. apply Z.ltb_lt in Pi. rewrite fL_freq in Pi by lia. apply M2; lia.
Qed.

Lemma dmaxc_eq : dmaxc b = dmax.
Proof.
  unfold dmaxc. destruct MXD as [M1 M2].
  assert (FE : forall d, 0 <= d < 30 -> ((0 <? gD b d) || forcedD b d = true <-> ffreq (fun d => arr_get (ds_dyn_dtree_fc s) d) FlD d <> 0)).
  { intros d Hd. unfold forcedD, ffreq. cbn [ob_forced b mkblock]. rewrite gD_freq by exact Hd. pose proof (op_fc _ OP TD d) as R. rewrite tree_fc_TD in R.
    destruct (existsb (Z.eqb d) FlD); [rewrite Bool.orb_true_r; split; [lia | reflexivity]|]. rewrite Bool.orb_false_r, Z.ltb_lt. lia. }
  apply (lmax_filter_zrange (fun d => (0 <? gD b d) || forcedD b d) 0 30 dmax); [lia | change (0 + Z.of_nat 30) with 30; lia | |].
  - apply (proj2 (FE dmax ltac:(lia))). exact M1.
  - intros i Hi Pi. change (0 + Z.of_nat 30) with 30 in Hi. apply M2; [lia|]. apply (proj1 (FE i ltac:(lia))). exact Pi.
Qed.

(* [comment removed for export] *)
Lemma runs_L : forall f, lsum f (zruns LX 0 (Z.to_nat (lmax + 1))) = lsum f (runs1 b) + lsum f (runs2 b)
  /\ (forall r, In r (runs1 b) -> 1 <= r <= 257) /\ (forall r, In r (runs2 b) -> 1 <= r <= 29).
Proof.
  intros f. unfold runs1, runs2. rewrite lmaxc_eq. pose proof lmax_ge_256 as G256.
  assert (E256 : ob_lenL b 256 <> 0).
  { rewrite <- LX_lenL by lia. intros Z0. pose proof (tp_LDu _ TP 256 ltac:(unfold L_CODES; lia)) as U.
    destruct (op_hist _ OP) as (FHL & _). specialize (U ltac:(rewrite (FHL 256) by (unfold L_CODES; lia); rewrite Z.eqb_refl; cbn [zind];
      pose proof (zsum_nonneg (fun j => zind (sym_lcode s j =? 256)) 0 (Z.to_nat (nsym s)) ltac:(intros; apply (proj1 (zind_le1 _)))); unfold END_BLOCK; lia)).
    unfold LX in Z0. lia. }
  rewrite (zruns_ext LX (ob_lenL b) 0 (Z.to_nat (lmax + 1))) by (intros; apply LX_lenL; lia).
  replace (Z.to_nat (lmax + 1)) with (256 + S (Z.to_nat (lmax - 256)))%nat by lia.
  rewrite (zruns_split f (ob_lenL b) 0 256 (Z.to_nat (lmax - 256))) by exact E256.
  change 257%nat with (256 + S 0)%nat. rewrite (zruns_split f (ob_lenL b) 0 256 0) by exact E256. rewrite zruns_nil. cbn [lsum].
  change (0 + Z.of_nat 256 + 1) with 257.
  split; [lia|]. split.
  - intros r Hr. change (256 + S 0)%nat with 257%nat in Hr. pose proof (zruns_pos _ _ _ r Hr). lia.
  - intros r Hr. pose proof (zruns_pos _ _ _ r Hr). lia.
Qed.

Lemma runs_D : zruns DX 0 (Z.to_nat (dmax + 1)) = runs3 b /\ (forall r, In r (runs3 b) -> 1 <= r <= 30).
Proof.
  unfold runs3. rewrite dmaxc_eq. split.
  - apply zruns_ext. intros; apply DX_lenD; lia.
  - intros r Hr. pose proof (zruns_pos _ _ _ r Hr). lia.
Qed.

Lemma gl_sc4 : ob_BC b 0 = vR1 b 1 + vR1 b 2 + vR1 b 3 + 2 * (vR2 b 1 + vR2 b 2 + vR2 b 3)
  /\ ob_BC b 17 = vRA b 1 + vRA b 2 + vRA b 3
  /\ ob_BC b 18 = vRB b 1 + vRB b 2 + vRB b 3 + vRLONG b.
Proof.
  destruct (scan_facts LX lmax ltac:(lia) LX_ok LX_guard) as (_ & _ & _ & S4a & S4b & S4c & _).
  destruct (scan_facts DX dmax ltac:(lia) DX_ok DX_guard) as (_ & _ & _ & T4a & T4b & T4c & _).
  cbv zeta in S4a, S4b, S4c, T4a, T4b, T4c.
  unfold vR1, vR2, vRA, vRB, vRLONG, runs_of. cbn [Z.eqb Pos.eqb].
  destruct runs_D as [RD3 B3]. rewrite <- RD3 in *.
  pose proof (runs_L e0) as (L0 & B1 & B2). pose proof (proj1 (runs_L e17)) as L17. pose proof (proj1 (runs_L e18)) as L18.
  pose proof (proj1 (runs_L is1)) as Li1. pose proof (proj1 (runs_L is2)) as Li2. pose proof (proj1 (runs_L isa)) as Lia. pose proof (proj1 (runs_L isb)) as Lib. pose proof (proj1 (runs_L nlong)) as Lnl.
  assert (C0 : forall l, (forall r, In r l -> 1 <= r <= 276) -> lsum e0 l = lsum is1 l + 2 * lsum is2 l).
  { intros l Hl. rewrite <- lsum_scale, <- lsum_add. apply lsum_ext. intros r Hr. rewrite e0_is12 by exact (Hl r Hr). lia. }
  assert (C17 : forall l, (forall r, In r l -> 1 <= r <= 276) -> lsum e17 l = lsum isa l).
  { intros l Hl. apply lsum_ext. intros r Hr. apply e17_isa. exact (Hl r Hr). }
  assert (C18 : forall l, (forall r, In r l -> 1 <= r <= 276) -> lsum e18 l = lsum isb l + lsum nlong l).
  { intros l Hl. rewrite <- lsum_add. apply lsum_ext. intros r Hr. apply e18_isb. exact (Hl r Hr). }
  assert (H1 : forall r, In r (runs1 b) -> 1 <= r <= 276) by (intros r Hr; pose proof (B1 r Hr); lia).
  assert (H2 : forall r, In r (runs2 b) -> 1 <= r <= 276) by (intros r Hr; pose proof (B2 r Hr); lia).
  assert (H3 : forall r, In r (zruns DX 0 (Z.to_nat (dmax + 1))) -> 1 <= r <= 276) by (intros r Hr; pose proof (B3 r Hr); lia).
  rewrite (BC_split 0), (BC_split 17), (BC_split 18) by lia.
  unfold REPZ_3_10, REPZ_11_138 in *. rewrite S4a, S4b, S4c, T4a, T4b, T4c.
  rewrite L0, L17, L18. rewrite (C0 _ H1), (C0 _ H2), (C0 _ H3), (C17 _ H1), (C17 _ H2), (C17 _ H3), (C18 _ H1), (C18 _ H2), (C18 _ H3). lia.
Qed.

(* [comment removed for export] *)
Hypothesis KZL : zt_kraft zL.
Hypothesis KZD : zt_kraft zD.
Hypothesis KZB : zt_kraft zB.

Lemma gl_TL : exists z, tree_facts z 286 15 (fL b) [] /\ zt_kraft z /\ (forall c, 0 <= c < 286 -> ob_lenL b c = zt_len z c).
Proof. exists zL. split; [exact TFL'|]. split; [exact KZL|]. intros c Hc. cbn [ob_lenL b mkblock]. symmetry. apply ZL1. Qed.

Lemma gl_TD : exists z, tree_facts z 30 15 (gD b) (ob_forced b) /\ zt_kraft z /\ (forall d, 0 <= d < 30 -> ob_lenD b d = zt_len z d).
Proof. exists zD. split; [exact TFD'|]. split; [exact KZD|]. intros d Hd. cbn [ob_lenD b mkblock]. symmetry. apply ZL2. Qed.

Lemma gl_TB : exists z, tree_facts z 19 7 (ob_BC b) (ob_bforced b) /\ zt_kraft z /\ (forall x, 0 <= x < 19 -> ob_BD b x = zt_len z x).
Proof. exists zB. split; [exact TFB|]. split; [exact KZB|]. intros x Hx. cbn [ob_BD b mkblock]. symmetry. apply ZL5. Qed.

(* [comment removed for export] *)
Lemma lcode_used : forall j, 0 <= j < N -> 0 <= sym_lcode s j <= lmax /\ sym_lcode s j <> lmax + 1.
Proof.
  intros j Hj. pose proof (sym_codes s OP j Hj) as (A & _). unfold L_CODES in A. destruct MXL as [_ M].
  assert (sym_lcode s j <= lmax); [|lia]. apply M; [lia|]. rewrite NOFL. unfold ffreq. cbn [existsb].
  destruct (op_hist _ OP) as (FHL & _). rewrite (FHL (sym_lcode s j)) by (unfold L_CODES; lia).
  pose proof (zsum_ge_point (fun i => zind (sym_lcode s i =? sym_lcode s j)) 0 (Z.to_nat (nsym s)) j ltac:(intros; apply (proj1 (zind_le1 _))) ltac:(subst N; lia)) as X.
  cbv beta in X. rewrite Z.eqb_refl in X. cbn [zind] in X. pose proof (zind_le1 (sym_lcode s j =? END_BLOCK)). lia.
Qed.

Lemma dcode_used : forall j, 0 <= j < N -> sym_isdist s j = true -> 0 <= sym_dcode s j <= dmax /\ sym_dcode s j <> dmax + 1.
Proof.
  intros j Hj Hd. pose proof (sym_codes s OP j Hj) as (_ & _ & _ & _ & M). destruct (M Hd) as (_ & A & _). unfold D_CODES in A. destruct MXD as [_ MX].
  assert (sym_dcode s j <= dmax); [|lia]. apply MX; [lia|]. unfold ffreq. destruct (existsb _ _); [lia|].
  destruct (op_hist _ OP) as (_ & FHD & _). rewrite (FHD (sym_dcode s j)) by (unfold D_CODES; lia).
  pose proof (zsum_ge_point (fun i => zind (sym_isdist s i && (sym_dcode s i =? sym_dcode s j))) 0 (Z.to_nat (nsym s)) j ltac:(intros; apply (proj1 (zind_le1 _))) ltac:(subst N; lia)) as X.
  cbv beta in X. rewrite Hd, Z.eqb_refl in X. cbn [zind andb] in X. lia.
Qed.

Lemma dcost_link : forall j, 0 <= j < N -> dcostS b (osym_of s j) = dcost (ov_LD s) (ov_DD s) s j.
Proof.
  intros j Hj. rewrite dcostS_osym by exact Hj. unfold dcost, ov_LD, ov_DD. cbn [ob_lenL ob_lenD b mkblock].
  pose proof (lcode_used j Hj) as [A B].
  rewrite <- (ZL1 (sym_lcode s j)), <- (LK1 (sym_lcode s j)) by exact B. unfold LX, Len. rewrite tree_dl_TL.
  destruct (sym_isdist s j) eqn:Hd; [|reflexivity].
  pose proof (dcode_used j Hj Hd) as [C D].
  rewrite <- (ZL2 (sym_dcode s j)), <- (LK2 (sym_dcode s j)) by exact D. unfold DX, Len. rewrite tree_dl_TD. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma gl_dyn : ob_Hc1 b + ssum (dcostS b) (ob_syms b) + ob_lenL b 256 <= ssum scostS (ob_syms b) + 6.
Proof.
  cbn [ob_Hc1 ob_syms b mkblock].
  rewrite !ssum_osyms by lia. fold N.
  rewrite (zsum_ext (fun j => dcostS b (osym_of s j)) (dcost (ov_LD s) (ov_DD s) s)) by (intros; apply dcost_link; lia).
  rewrite (zsum_ext (fun j => scostS (osym_of s j)) (scost s)) by (intros; apply scostS_osym; lia).
  assert (E256 : ob_lenL b 256 = arr_get (ov_LD s) END_BLOCK).
  { cbn [ob_lenL b mkblock]. rewrite <- ZL1, <- LK1 by (pose proof lmax_ge_256; lia). unfold LX, Len, ov_LD, END_BLOCK. rewrite tree_dl_TL. reflexivity. }
  rewrite E256.
  (* [comment removed for export] *)
  pose proof (tp_opt_ge _ TP) as G. pose proof (data_dyn s OP (ov_LD s) (ov_DD s)) as Dd. fold N in Dd.
  pose proof (tp_stat _ TP) as ST. pose proof (static_by_syms s OP) as SB. fold N in SB.
  pose proof (branch1_lt (ov_X6 s) (fb_buf s) (fb_len s) (tp_opt _ TP) (tp_stat_range _ TP) HB) as LT.
  unfold ov_LD, ov_DD in *.
  rewrite (zsum_ext (fun c => arr_get (ds_dyn_ltree_fc s) c * (Len (ov_X6 s) TL c + xbits TL c))
                    (fun c => arr_get (ds_dyn_ltree_fc s) c * (arr_get (ds_dyn_ltree_dl (ov_X6 s)) c + xbits TL c))) in G
    by (intros; rewrite Len_eq, tree_dl_TL; reflexivity).
  rewrite (zsum_ext (fun d => arr_get (ds_dyn_dtree_fc s) d * (Len (ov_X6 s) TD d + xbits TD d))
                    (fun d => arr_get (ds_dyn_dtree_fc s) d * (arr_get (ds_dyn_dtree_dl (ov_X6 s)) d + xbits TD d))) in G
    by (intros; rewrite Len_eq, tree_dl_TD; reflexivity).
  rewrite (zsum_ext (fun x => arr_get (ov_BC s) x * (Len (ov_X6 s) TB x + arr_get extra_blbits_a x))
                    (fun x => arr_get (ov_BC s) x * (arr_get (ov_BD s) x + arr_get extra_blbits_a x))) in G
    by (intros; unfold ov_BD; rewrite Len_eq, tree_dl_TB; reflexivity).
  unfold ov_hdr.
  match goal with |- context [zsum ?f 0 19] => set (A := zsum f 0 19) in * end.
  match type of Dd with context [zsum ?f 0 (Z.to_nat L_CODES)] => set (B := zsum f 0 (Z.to_nat L_CODES)) in * end.
  match type of Dd with context [zsum ?f 0 (Z.to_nat D_CODES)] => set (C := zsum f 0 (Z.to_nat D_CODES)) in * end.
  match type of SB with ?x + ?y = _ => set (SBL := x) in *; set (SBD := y) in * end.
  match goal with |- context [zsum (dcost ?u ?v s) 0 (Z.to_nat N)] => set (Dsum := zsum (dcost u v s) 0 (Z.to_nat N)) in * end.
  clearbody A B C SBL SBD Dsum. lia.
Qed.

(* [comment removed for export] *)
Lemma gl_EX : vEX b = zsum (fun j => Z.max 0 (dcost (ov_LD s) (ov_DD s) s j - 24)) 0 (Z.to_nat N).
Proof.
  unfold vEX. cbn [ob_syms b mkblock]. rewrite ssum_osyms by lia. fold N. apply zsum_ext. intros j Hj. unfold exS. rewrite dcost_link by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma gl_ok : oblock_ok b (ds_lit_bufsize s).
Proof.
  pose proof gl_sc23 as [S2 S3]. pose proof gl_sc4 as (S4a & S4b & S4c).
  constructor.
  - cbn [ob_syms b mkblock]. eapply Forall_impl; [| apply Forall_osyms]. intros [c|lc dc]; cbn; lia.
  - rewrite (NSYM_osyms b) by reflexivity. fold N. lia.
  - pose proof (op_lbs _ OP). lia.
  - exact gl_TL.
  - exact gl_TD.
  - exact gl_TB.
  - exact gl_WB.
  - exact gl_blc.
  - exact gl_Hc1.
  - exact gl_sc1.
  - exact S2.
  - exact S3.
  - exact S4a.
  - exact S4b.
  - exact S4c.
  - exact gl_dyn.
Qed.

End WithTrees.

(* [comment removed for export] *)
Theorem block_ok : exists b, oblock_ok b (ds_lit_bufsize s) /\ ob_syms b = osyms s /\ ob_Hc1 b = ov_hdr s - 3
  /\ vEX b = zsum (fun j => Z.max 0 (dcost (ov_LD s) (ov_DD s) s j - 24)) 0 (Z.to_nat N).
Proof.
  destruct (ot_facts s OP) as (zL & zD & zB & FlL & FlD & FlB & TF1 & TF2 & TF5 & K1 & K2 & K5 & ZL1 & ZL2 & ZL5 & LK1 & LK2 & LK5 & G1 & G2 & MX1 & MX2 & NOF).
  specialize (NOF HN).
  exists (mkblock FlD FlB). split; [| split; [reflexivity | split; [reflexivity|]]].
  - apply (gl_ok zL zD zB FlL FlD FlB); assumption.
  - apply (gl_EX zL zD FlL FlD); assumption.
Qed.

(* [comment removed for export] *)
Corollary overlay_from_bound :
  (forall b, oblock_ok b (ds_lit_bufsize s) -> ob_Hc1 b + vEX b <= 8 * ds_lit_bufsize s - 10) ->
  forall k, 0 <= k < N -> ov_wpos s k <= ov_rpos s k.
Proof.
  intros BOUND. destruct block_ok as (b & OK & _ & H1 & H2).
  apply prefix_from_core. rewrite <- H1, <- H2. apply BOUND. exact OK.
Qed.

End Block.

(* [comment removed for export] *)
Theorem OVERLAY_CORE_from_bound :
  (forall s b, overlay_pre s -> oblock_ok b (ds_lit_bufsize s) -> ob_Hc1 b + vEX b <= 8 * ds_lit_bufsize s - 10) ->
  OVERLAY_CORE.
Proof.
  intros BOUND s OP HB k Hk.
  apply (overlay_from_bound s OP ltac:(lia) HB); [| exact Hk]. intros b OK. apply (BOUND s b OP OK).
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

