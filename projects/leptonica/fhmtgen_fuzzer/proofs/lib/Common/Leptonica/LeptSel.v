(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import WalksLib LeptDefs LeptStructs LeptRecs LeptSlots.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition hm_names : list (list Z) :=
  [ [115; 101; 108; 95; 51; 104; 109]       (* [comment removed for export] *)
  ; [115; 101; 108; 95; 51; 100; 101]       (* [comment removed for export] *)
  ; [115; 101; 108; 95; 51; 117; 101]       (* [comment removed for export] *)
  ; [115; 101; 108; 95; 51; 114; 101]       (* [comment removed for export] *)
  ; [115; 101; 108; 95; 51; 108; 101]       (* [comment removed for export] *)
  ; [115; 101; 108; 95; 115; 108; 49]       (* [comment removed for export] *)
  ; [115; 101; 108; 95; 117; 108; 99]       (* [comment removed for export] *)
  ; [115; 101; 108; 95; 117; 114; 99]       (* [comment removed for export] *)
  ; [115; 101; 108; 95; 108; 108; 99]       (* [comment removed for export] *)
  ; [115; 101; 108; 95; 108; 114; 99] ].    (* [comment removed for export] *)
Definition hm_sy : list Z := [3; 2; 2; 3; 3; 13; 4; 4; 4; 4].
Definition hm_sx : list Z := [3; 3; 3; 2; 2; 6; 4; 4; 4; 4].
Definition hm_cy : list Z := [1; 0; 1; 1; 1; 6; 1; 1; 2; 2].
Definition hm_cx : list Z := [1; 1; 1; 0; 1; 2; 1; 2; 1; 2].
(* [comment removed for export] *)
Definition hm_name (i : Z) : list byte := map (Z_to_bv 8) (nth (Z.to_nat i) hm_names []).

(* [comment removed for export] *)
Definition cstr (l : list byte) : Prop := exists s, l = s ++ [Z_to_bv 8 0] /\ Forall (fun b => b <> Z_to_bv 8 0) s.

(* [comment removed for export] *)
Fixpoint strcmp_Z (la lb : list byte) : Z :=
  match la, lb with
  | a :: ta, b :: tb =>
      if (bv_unsigned a =? 0) then bv_unsigned a - bv_unsigned b
      else if (bv_unsigned a =? bv_unsigned b) then strcmp_Z ta tb else bv_unsigned a - bv_unsigned b
  | a :: _, [] => bv_unsigned a
  | [], b :: _ => - bv_unsigned b
  | [], [] => 0
  end.

(* [comment removed for export] *)
Definition rd_str (segs : list Segment) (m : word -> option byte) (a : Z) (l : list byte) : Prop :=
  forall i, 0 <= i < Z.of_nat (length l) -> rdn segs m (Z_to_bv 64 (a + i)) 1 = Some [nth (Z.to_nat i) l (Z_to_bv 8 0)].

Lemma rd_str_rdn : forall segs m l a, rdn segs m (Z_to_bv 64 a) (length l) = Some l -> rd_str segs m a l.
Proof.
  intros segs m l. induction l as [|b t IH]; intros a R i Hi; [cbn [length] in Hi; lia|].
  cbn [length rdn] in R.
  destruct (match m (Z_to_bv 64 a) with Some b0 => Some b0 | None => seg_rom segs (Z_to_bv 64 a) end) as [b0|] eqn:Eb; [|discriminate].
  destruct (rdn segs m (Z_to_bv 64 a + 1) (length t)) as [rest|] eqn:Er; [|discriminate].
  injection R as -> ->.
  destruct (Z.eq_dec i 0) as [->|Ni].
  - rewrite Z.add_0_r. cbn [rdn Z.to_nat nth]. rewrite Eb. reflexivity.
  - rewrite zbv_plus1 in Er. cbn [length] in Hi.
    replace (a + i) with (a + 1 + (i - 1)) by lia. rewrite (IH (a + 1) Er (i - 1)) by lia.
    replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) by lia. reflexivity.
Qed.

Lemma rd_str_tl : forall segs m a b t, rd_str segs m a (b :: t) -> rd_str segs m (a + 1) t.
Proof.
  intros segs m a b t R i Hi. replace (a + 1 + i) with (a + (i + 1)) by lia. rewrite (R (i + 1)) by (cbn [length]; lia).
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. reflexivity.
Qed.

Lemma rd_str_hd : forall segs m a b t, rd_str segs m a (b :: t) -> rdn segs m (Z_to_bv 64 a) 1 = Some [b].
Proof. intros segs m a b t R. pose proof (R 0 ltac:(cbn [length]; lia)) as H. rewrite Z.add_0_r in H. exact H. Qed.

Lemma cstr_name : forall i, cstr (hm_name i ++ [Z_to_bv 8 0]) \/ ~ (0 <= i < 10).
Proof.
  intros i. destruct (Z_lt_ge_dec i 0) as [|H0]; [right; lia|]. destruct (Z_lt_ge_dec i 10) as [H1|]; [left | right; lia].
  exists (hm_name i). split; [reflexivity|].
  assert (E : exists k : nat, (k < 10)%nat /\ i = Z.of_nat k) by (exists (Z.to_nat i); lia). destruct E as (k & Hk & ->).
  unfold hm_name. rewrite Nat2Z.id.
  do 10 (destruct k as [|k]; [repeat constructor; intros E; apply (f_equal bv_unsigned) in E; vm_compute in E; discriminate|]). lia.
Qed.

Section Sel.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {AIC : AllocCalloc} {LL : LeptLayout}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition sel_flds (sy sx cy cx data name : Z) : list fld :=
  [(4%nat, sy); (4%nat, sx); (4%nat, cy); (4%nat, cx); (8%nat, data); (8%nat, name)].
Definition sela_flds (n na arr : Z) : list fld := [(4%nat, n); (4%nat, na); (8%nat, arr)].

(* [comment removed for export] *)
Definition bok (T p n : Z) : Prop := 1 <= p /\ p + n <= T /\ p mod 16 = 0.

(* [comment removed for export] *)
Record selv := SELV { v_sy : Z; v_sx : Z; v_cy : Z; v_cx : Z; v_data : Z; v_name : Z; v_rows : Z -> Z }.

Definition set_cyx (v : selv) (cy cx : Z) : selv := SELV (v_sy v) (v_sx v) cy cx (v_data v) (v_name v) (v_rows v).
Definition set_name (v : selv) (nm : Z) : selv := SELV (v_sy v) (v_sx v) (v_cy v) (v_cx v) (v_data v) nm (v_rows v).

(* [comment removed for export] *)
Definition sel_blk (sel : Z) (v : selv) (p : Z) : Prop :=
  p = sel \/ p = v_data v \/ exists i, 0 <= i < v_sy v /\ p = v_rows v i.

(* [comment removed for export] *)
Definition sel_at (T : Z) (A : AS) (m : word -> option byte) (sel : Z) (v : selv) : Prop :=
  1 <= v_sy v <= 10000 /\ 1 <= v_sx v <= 10000 /\
  bok T sel 32 /\ live A (Z_to_bv 64 sel) = Some 32 /\
  RECat m sel (sel_flds (v_sy v) (v_sx v) (v_cy v) (v_cx v) (v_data v) (v_name v)) /\
  bok T (v_data v) (8 * v_sy v) /\ live A (Z_to_bv 64 (v_data v)) = Some (8 * v_sy v) /\ v_data v <> sel /\
  (forall i, 0 <= i < v_sy v ->
      bok T (v_rows v i) (4 * v_sx v) /\ live A (Z_to_bv 64 (v_rows v i)) = Some (4 * v_sx v) /\
      v_rows v i <> v_data v /\ v_rows v i <> sel /\
      bytes_at m (v_data v + 8 * i) (Z_to_le_bytes 8 (v_rows v i))) /\
  (forall i j, 0 <= i < v_sy v -> 0 <= j < v_sy v -> i <> j -> v_rows v i <> v_rows v j).

(* [comment removed for export] *)
Definition selname_at (T : Z) (A : AS) (m : word -> option byte) (name : Z) (nm : list byte) : Prop :=
  bok T name (Z.of_nat (length nm) + 1) /\ live A (Z_to_bv 64 name) = Some (Z.of_nat (length nm) + 1) /\
  Forall (fun b => b <> Z_to_bv 8 0) nm /\ bytes_at m name (nm ++ [Z_to_bv 8 0]).

(* [comment removed for export] *)
Definition sel_off (X : AS) (sel : Z) (v : selv) : Prop := forall p, sel_blk sel v p -> live X (Z_to_bv 64 p) = None.

(* [comment removed for export] *)
Definition sel_only (A A' : AS) (sel : Z) (v : selv) : Prop :=
  forall q, (forall p, sel_blk sel v p -> q <> Z_to_bv 64 p) -> live A' q = live A q.

(* [comment removed for export] *)
Definition seln_blk (sel : Z) (v : selv) (p : Z) : Prop := sel_blk sel v p \/ p = v_name v.

(* [comment removed for export] *)
Definition sela_at (T : Z) (A : AS) (m : word -> option byte) (sela arr n : Z) (sels : Z -> Z) (vs : Z -> selv)
                   (nms : Z -> list byte) : Prop :=
  0 <= n <= 50 /\
  bok T sela 16 /\ live A (Z_to_bv 64 sela) = Some 16 /\ RECat m sela (sela_flds n 50 arr) /\
  bok T arr 400 /\ live A (Z_to_bv 64 arr) = Some 400 /\ arr <> sela /\
  (forall i, 0 <= i < n ->
      bytes_at m (arr + 8 * i) (Z_to_le_bytes 8 (sels i)) /\
      sel_at T A m (sels i) (vs i) /\ selname_at T A m (v_name (vs i)) (nms i) /\
      (forall p, seln_blk (sels i) (vs i) p -> p <> sela /\ p <> arr) /\
      (forall p, sel_blk (sels i) (vs i) p -> p <> v_name (vs i))) /\
  (forall i j p q, 0 <= i < n -> 0 <= j < n -> i <> j -> seln_blk (sels i) (vs i) p -> seln_blk (sels j) (vs j) q -> p <> q).

(* [comment removed for export] *)
Definition sela_blk (sela arr n : Z) (sels : Z -> Z) (vs : Z -> selv) (p : Z) : Prop :=
  p = sela \/ p = arr \/ exists i, 0 <= i < n /\ seln_blk (sels i) (vs i) p.
Definition sela_off (X : AS) (sela arr n : Z) (sels : Z -> Z) (vs : Z -> selv) : Prop :=
  forall p, sela_blk sela arr n sels vs p -> live X (Z_to_bv 64 p) = None.
Definition sela_only (A A' : AS) (sela arr n : Z) (sels : Z -> Z) (vs : Z -> selv) : Prop :=
  forall q, (forall p, sela_blk sela arr n sels vs p -> q <> Z_to_bv 64 p) -> live A' q = live A q.

(* [comment removed for export] *)
Definition sela_hm (T : Z) (A : AS) (m : word -> option byte) (sela arr : Z) (sels : Z -> Z) (vs : Z -> selv) : Prop :=
  sela_at T A m sela arr 10 sels vs hm_name /\
  (forall i, 0 <= i < 10 -> v_sy (vs i) = nth (Z.to_nat i) hm_sy 0 /\ v_sx (vs i) = nth (Z.to_nat i) hm_sx 0).

Lemma rd_str_bytes_at : forall segs m a l, bytes_at m a l -> 0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 -> rd_str segs m a l.
Proof.
  intros segs m a l HB Ha Hn. apply rd_str_rdn. exact (bytes_at_rdn segs m a l Ha Hn HB).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bok_range : forall T p n, bok T p n -> 0 <= n -> T < 2 ^ 64 -> 0 <= p < 2 ^ 64 /\ p + n < 2 ^ 64.
Proof. intros T p n (H1 & H2 & _) Hn HT. lia. Qed.

Lemma bok_mod8 : forall T p n, bok T p n -> p mod 8 = 0.
Proof. intros T p n (_ & _ & H). pose proof (Z.div_mod p 16 ltac:(lia)) as E. rewrite H in E.
  rewrite E. replace (16 * (p / 16) + 0) with ((2 * (p / 16)) * 8) by lia. apply Z_mod_mult. Qed.

Lemma bok_mod4 : forall T p n, bok T p n -> p mod 4 = 0.
Proof. intros T p n (_ & _ & H). pose proof (Z.div_mod p 16 ltac:(lia)) as E. rewrite H in E.
  rewrite E. replace (16 * (p / 16) + 0) with ((4 * (p / 16)) * 4) by lia. apply Z_mod_mult. Qed.

(* [comment removed for export] *)
Lemma LIVK_in : forall A M M' (p k : Z) (x : word), LIVK A M M' -> live A (Z_to_bv 64 p) = Some k ->
  0 <= p -> p + k < 2 ^ 64 -> p <= u x < p + k -> M' x = M x.
Proof.
  intros A M M' p k x L Lp G0 TP Hx.
  pose proof (L (Z_to_bv 64 p) k (u x - p) Lp ltac:(lia)) as E.
  replace (at_ (Z_to_bv 64 p) (u x - p)) with x in E
    by (unfold at_; apply bv_eq; rewrite !u_Z2bv; rewrite ?u_Z2bv; pose proof (u64_range x); lia).
  exact E.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sel_at_keep : forall T A A' m m' sel v, T < 2 ^ 64 ->
  sel_at T A m sel v -> sub_live A A' -> LIVK A m m' -> sel_at T A' m' sel v.
Proof.
  intros T A A' m m' sel v HT (Hsy & Hsx & Bs & Ls & Rs & Bd & Ld & NEd & ROWS & DIST) SUB LK.
  destruct (bok_range T sel 32 Bs ltac:(lia) HT) as [Gs Ts].
  destruct (bok_range T (v_data v) (8 * v_sy v) Bd ltac:(lia) HT) as [Gd Td].
  split; [exact Hsy|]. split; [exact Hsx|]. split; [exact Bs|]. split; [exact (SUB _ _ Ls)|].
  split.
  { apply (RECat_frame m); [exact Rs|]. intros x Hx. cbn in Hx. apply (LIVK_in A m m' sel 32 x LK Ls); lia. }
  split; [exact Bd|]. split; [exact (SUB _ _ Ld)|]. split; [exact NEd|]. split; [|exact DIST].
  intros i Hi. destruct (ROWS i Hi) as (Br & Lr & N1 & N2 & Bi).
  split; [exact Br|]. split; [exact (SUB _ _ Lr)|]. split; [exact N1|]. split; [exact N2|].
  apply (bytes_at_frame m); [exact Bi | | lia | rewrite length_Z_to_le_bytes; lia].
  rewrite length_Z_to_le_bytes. intros x Hx. apply (LIVK_in A m m' (v_data v) (8 * v_sy v) x LK Ld); lia.
Qed.

Lemma selname_at_keep : forall T A A' m m' name nm, T < 2 ^ 64 ->
  selname_at T A m name nm -> sub_live A A' -> LIVK A m m' -> selname_at T A' m' name nm.
Proof.
  intros T A A' m m' name nm HT (Bn & Ln & NZ & Bs) SUB LK.
  destruct (bok_range T name _ Bn ltac:(lia) HT) as [Gn Tn].
  split; [exact Bn|]. split; [exact (SUB _ _ Ln)|]. split; [exact NZ|].
  assert (EL : Z.of_nat (length (nm ++ [Z_to_bv 8 0])) = Z.of_nat (length nm) + 1) by (rewrite length_app; cbn [length]; lia).
  apply (bytes_at_frame m); [exact Bs | | lia | lia].
  intros x Hx. apply (LIVK_in A m m' name _ x LK Ln); lia.
Qed.

Lemma sela_at_keep : forall T A A' m m' sela arr n sels vs nms, T < 2 ^ 64 ->
  sela_at T A m sela arr n sels vs nms -> sub_live A A' -> LIVK A m m' -> sela_at T A' m' sela arr n sels vs nms.
Proof.
  intros T A A' m m' sela arr n sels vs nms HT (Hn & Bs & Ls & Rs & Ba & La & NEa & CELLS & DIST) SUB LK.
  destruct (bok_range T sela 16 Bs ltac:(lia) HT) as [Gs Ts].
  destruct (bok_range T arr 400 Ba ltac:(lia) HT) as [Ga Ta].
  split; [exact Hn|]. split; [exact Bs|]. split; [exact (SUB _ _ Ls)|].
  split.
  { apply (RECat_frame m); [exact Rs|]. intros x Hx. cbn in Hx. apply (LIVK_in A m m' sela 16 x LK Ls); lia. }
  split; [exact Ba|]. split; [exact (SUB _ _ La)|]. split; [exact NEa|]. split; [|exact DIST].
  intros i Hi. destruct (CELLS i Hi) as (Bi & SA & NA & N1 & N2).
  split.
  { apply (bytes_at_frame m); [exact Bi | | lia | rewrite length_Z_to_le_bytes; lia].
    rewrite length_Z_to_le_bytes. intros x Hx. apply (LIVK_in A m m' arr 400 x LK La); lia. }
  split; [exact (sel_at_keep T A A' m m' _ _ HT SA SUB LK)|].
  split; [exact (selname_at_keep T A A' m m' _ _ HT NA SUB LK)|]. split; assumption.
Qed.

Lemma sela_hm_keep : forall T A A' m m' sela arr sels vs, T < 2 ^ 64 ->
  sela_hm T A m sela arr sels vs -> sub_live A A' -> LIVK A m m' -> sela_hm T A' m' sela arr sels vs.
Proof. intros T A A' m m' sela arr sels vs HT [S D] SUB LK. split; [exact (sela_at_keep T A A' m m' _ _ _ _ _ _ HT S SUB LK) | exact D]. Qed.

(* [comment removed for export] *)
Context {PINS : LeptPins}.
Lemma live_apart : forall C A m md (p q : word) (n k : Z), Cok C -> W C A m md ->
  live A p = Some n -> live A q = Some k -> p <> q -> 0 <= n -> 0 <= k ->
  u p + n <= u q \/ u q + k <= u p.
Proof.
  intros C A m md p q n k CK HW Lp Lq NE Hn Hk.
  destruct (ai_live_disjoint A m (m_vmmaps md) p n q k (w_inv _ _ _ _ HW) Lp Lq NE) as [X|X];
    [left; pose proof (round16_ge n Hn); lia | right; pose proof (round16_ge k Hk); lia].
Qed.

Lemma zbv_ne : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> a <> b -> Z_to_bv 64 a <> Z_to_bv 64 b.
Proof. intros a b Ha Hb NE E. apply NE. apply (f_equal bv_unsigned) in E. rewrite !u_Z2bv in E by lia. exact E. Qed.

(* [comment removed for export] *)
Lemma sel_at_rows_frame : forall C A m md m' T sel v, Cok C -> W C A m md -> T < 2 ^ 64 ->
  sel_at T A m sel v ->
  (forall x : word, (forall i, 0 <= i < v_sy v -> ~ (v_rows v i <= u x < v_rows v i + 4 * v_sx v)) -> m' x = m x) ->
  sel_at T A m' sel v.
Proof.
  intros C A m md m' T sel v CK HW HT (Hsy & Hsx & Bs & Ls & Rs & Bd & Ld & NEd & ROWS & DIST) FR.
  destruct (bok_range T sel 32 Bs ltac:(lia) HT) as [Gs Ts].
  destruct (bok_range T (v_data v) (8 * v_sy v) Bd ltac:(lia) HT) as [Gd Td].
  split; [exact Hsy|]. split; [exact Hsx|]. split; [exact Bs|]. split; [exact Ls|].
  split.
  { apply (RECat_frame m); [exact Rs|]. intros x Hx. cbn in Hx. apply FR. intros i Hi Hin.
    destruct (ROWS i Hi) as (Br & Lr & N1 & N2 & _). destruct (bok_range T _ _ Br ltac:(lia) HT) as [Gr Tr].
    pose proof (live_apart C A m md _ _ _ _ CK HW Ls Lr ltac:(apply zbv_ne; lia) ltac:(lia) ltac:(lia)) as AP.
    rewrite !u_Z2bv in AP by lia. lia. }
  split; [exact Bd|]. split; [exact Ld|]. split; [exact NEd|]. split; [|exact DIST].
  intros i Hi. destruct (ROWS i Hi) as (Br & Lr & N1 & N2 & Bi).
  split; [exact Br|]. split; [exact Lr|]. split; [exact N1|]. split; [exact N2|].
  apply (bytes_at_frame m); [exact Bi | | lia | rewrite length_Z_to_le_bytes; lia].
  rewrite length_Z_to_le_bytes. intros x Hx. apply FR. intros j Hj Hin.
  destruct (ROWS j Hj) as (Brj & Lrj & N1j & _). destruct (bok_range T _ _ Brj ltac:(lia) HT) as [Grj Trj].
  pose proof (live_apart C A m md _ _ _ _ CK HW Ld Lrj ltac:(apply zbv_ne; lia) ltac:(lia) ltac:(lia)) as AP.
  rewrite !u_Z2bv in AP by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma sel_at_frame_blk : forall C A m md m' T sel v (p n : Z), Cok C -> W C A m md -> T < 2 ^ 64 ->
  sel_at T A m sel v -> live A (Z_to_bv 64 p) = Some n -> 0 <= p < 2 ^ 64 -> 0 <= n ->
  (forall q, sel_blk sel v q -> q <> p) ->
  (forall x : word, ~ (p <= u x < p + n) -> m' x = m x) ->
  sel_at T A m' sel v.
Proof.
  intros C A m md m' T sel v p n CK HW HT (Hsy & Hsx & Bs & Ls & Rs & Bd & Ld & NEd & ROWS & DIST) Lp Hp Hn NB FR.
  destruct (bok_range T sel 32 Bs ltac:(lia) HT) as [Gs Ts].
  destruct (bok_range T (v_data v) (8 * v_sy v) Bd ltac:(lia) HT) as [Gd Td].
  assert (NEs : sel <> p) by (apply NB; left; reflexivity).
  assert (NEdp : v_data v <> p) by (apply NB; right; left; reflexivity).
  pose proof (live_apart C A m md _ _ _ _ CK HW Ls Lp ltac:(apply zbv_ne; lia) ltac:(lia) Hn) as APs. rewrite !u_Z2bv in APs by lia.
  pose proof (live_apart C A m md _ _ _ _ CK HW Ld Lp ltac:(apply zbv_ne; lia) ltac:(lia) Hn) as APd. rewrite !u_Z2bv in APd by lia.
  split; [exact Hsy|]. split; [exact Hsx|]. split; [exact Bs|]. split; [exact Ls|].
  split; [apply (RECat_frame m); [exact Rs|]; intros x Hx; cbn in Hx; apply FR; lia|].
  split; [exact Bd|]. split; [exact Ld|]. split; [exact NEd|]. split; [|exact DIST].
  intros i Hi. destruct (ROWS i Hi) as (Br & Lr & N1 & N2 & Bi).
  split; [exact Br|]. split; [exact Lr|]. split; [exact N1|]. split; [exact N2|].
  apply (bytes_at_frame m); [exact Bi | | lia | rewrite length_Z_to_le_bytes; lia].
  rewrite length_Z_to_le_bytes. intros x Hx. apply FR. lia.
Qed.

Lemma selname_at_frame_blk : forall C A m md m' T name nm (p n : Z), Cok C -> W C A m md -> T < 2 ^ 64 ->
  selname_at T A m name nm -> live A (Z_to_bv 64 p) = Some n -> 0 <= p < 2 ^ 64 -> 0 <= n -> name <> p ->
  (forall x : word, ~ (p <= u x < p + n) -> m' x = m x) ->
  selname_at T A m' name nm.
Proof.
  intros C A m md m' T name nm p n CK HW HT (Bn & Ln & NZ & Bs) Lp Hp Hn NE FR.
  destruct (bok_range T name _ Bn ltac:(lia) HT) as [Gn Tn].
  pose proof (live_apart C A m md _ _ _ _ CK HW Ln Lp ltac:(apply zbv_ne; lia) ltac:(lia) Hn) as AP. rewrite !u_Z2bv in AP by lia.
  split; [exact Bn|]. split; [exact Ln|]. split; [exact NZ|].
  assert (EL : Z.of_nat (length (nm ++ [Z_to_bv 8 0])) = Z.of_nat (length nm) + 1) by (rewrite length_app; cbn [length]; lia).
  apply (bytes_at_frame m); [exact Bs | | lia | lia]. intros x Hx. apply FR. lia.
Qed.

(* [comment removed for export] *)
Definition upd {X : Type} (f : Z -> X) (k : Z) (x : X) : Z -> X := fun i => if (i =? k)%Z then x else f i.
Lemma upd_same : forall X (f : Z -> X) k x, upd f k x k = x. Proof. intros. unfold upd. rewrite Z.eqb_refl. reflexivity. Qed.
Lemma upd_other : forall X (f : Z -> X) k x i, i <> k -> upd f k x i = f i.
Proof. intros X f k x i H. unfold upd. destruct (Z.eqb_spec i k); [contradiction | reflexivity]. Qed.

(* [comment removed for export] *)
Lemma sel_blk_live : forall T A m sel v p, sel_at T A m sel v -> sel_blk sel v p -> exists n, live A (Z_to_bv 64 p) = Some n /\ 0 <= n /\ 1 <= p /\ p + n <= T.
Proof.
  intros T A m sel v p (Hsy & Hsx & (G1 & G2 & _) & Ls & _ & (G3 & G4 & _) & Ld & _ & ROWS & _) [->|[->|(i & Hi & ->)]].
  - exists 32. repeat split; [exact Ls | lia | lia | lia].
  - exists (8 * v_sy v). repeat split; [exact Ld | lia | lia | lia].
  - destruct (ROWS i Hi) as ((G5 & G6 & _) & Lr & _). exists (4 * v_sx v). repeat split; [exact Lr | lia | lia | lia].
Qed.

Lemma sela_blk_live : forall T A m sela arr n sels vs nms i p, sela_at T A m sela arr n sels vs nms -> 0 <= i < n ->
  seln_blk (sels i) (vs i) p -> exists k, live A (Z_to_bv 64 p) = Some k /\ 0 <= k /\ 1 <= p /\ p + k <= T.
Proof.
  intros T A m sela arr n sels vs nms i p (_ & _ & _ & _ & _ & _ & _ & CELLS & _) Hi [HB| ->].
  - destruct (CELLS i Hi) as (_ & SA & _). exact (sel_blk_live T A m _ _ p SA HB).
  - destruct (CELLS i Hi) as (_ & _ & ((G1 & G2 & _) & Ln & _) & _). exists (Z.of_nat (length (nms i)) + 1). repeat split; [exact Ln | lia | lia | lia].
Qed.

(* [comment removed for export] *)
Lemma sel_at_set_name : forall C A m md T sel v name, Cok C -> W C A m md -> T < 2 ^ 64 -> 0 <= name < 2 ^ 64 ->
  sel_at T A m sel v ->
  sel_at T A (wbytes m (Z_to_bv 64 (sel + 24)) (word_to_le_bytes 8 (Z_to_bv 64 name))) sel (set_name v name).
Proof.
  intros C A m md T sel v name CK HW HT Hname (Hsy & Hsx & Bs & Ls & Rs & Bd & Ld & NEd & ROWS & DIST).
  destruct (bok_range T sel 32 Bs ltac:(lia) HT) as [Gs Ts].
  destruct (bok_range T (v_data v) (8 * v_sy v) Bd ltac:(lia) HT) as [Gd Td].
  pose proof (live_apart C A m md _ _ _ _ CK HW Ls Ld ltac:(apply zbv_ne; lia) ltac:(lia) ltac:(lia)) as AP. rewrite !u_Z2bv in AP by lia.
  unfold sel_at, set_name. cbn [v_sy v_sx v_cy v_cx v_data v_name v_rows].
  split; [exact Hsy|]. split; [exact Hsx|]. split; [exact Bs|]. split; [exact Ls|].
  split.
  { unfold sel_flds. eapply (REC_wr' _ _ _ _ 5 8); [ exact Rs | cbn; lia | cbn; lia | reflexivity | reflexivity | reflexivity ]. }
  split; [exact Bd|]. split; [exact Ld|]. split; [exact NEd|]. split; [|exact DIST].
  intros i Hi. destruct (ROWS i Hi) as (Br & Lr & N1 & N2 & Bi). do 4 (split; [assumption|]).
  apply bytes_at_wbytes_out; [exact Bi | lia | rewrite length_Z_to_le_bytes; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia
                              | rewrite length_Z_to_le_bytes, length_N_to_le_bytes, u_Z2bv by lia; cbn; lia].
Qed.

Lemma bytes_at_wbytes_same : forall m (a : Z) bs, 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  bytes_at (wbytes m (Z_to_bv 64 a) bs) a bs.
Proof.
  intros m a bs Ha Hn i Hi. rewrite wbytes_inside; rewrite ?u_Z2bv by lia; [| lia | lia]. f_equal. f_equal. lia.
Qed.

Lemma sela_at_add : forall C A m md T sela arr k sels vs nms sel v name bs Ma Mb M3,
  Cok C -> W C A m md -> T < 2 ^ 64 ->
  sela_at T A m sela arr k sels vs nms -> 0 <= k < 50 ->
  sel_at T A m sel v -> selname_at T A m name bs ->
  (forall q, sel_blk sel v q -> q <> sela /\ q <> arr /\ q <> name /\ forall i p', 0 <= i < k -> seln_blk (sels i) (vs i) p' -> p' <> q) ->
  name <> sela -> name <> arr -> (forall i p', 0 <= i < k -> seln_blk (sels i) (vs i) p' -> p' <> name) ->
  Ma = wbytes m (Z_to_bv 64 (sel + 24)) (word_to_le_bytes 8 (Z_to_bv 64 name)) ->
  Mb = wbytes Ma (Z_to_bv 64 (arr + 8 * k)) (word_to_le_bytes 8 (Z_to_bv 64 sel)) ->
  M3 = wbytes Mb (Z_to_bv 64 sela) (word_to_le_bytes 4 (Z_to_bv 64 (k + 1))) ->
  W C A Ma md -> W C A Mb md ->
  sela_at T A M3 sela arr (k + 1) (upd sels k sel) (upd vs k (set_name v name)) (upd nms k bs).
Proof.
  intros C A m md T sela arr k sels vs nms sel v name bs Ma Mb M3 CK HW HT (Hn & Bs & Ls & Rs & Ba & La & NEa & CELLS & DIST) Hk SA NA NB NNs NNa NNo EMa EMb EM3 HWa HWb.
  destruct (bok_range T sela 16 Bs ltac:(lia) HT) as [Gs Ts].
  destruct (bok_range T arr 400 Ba ltac:(lia) HT) as [Ga Ta].
  pose proof SA as (_ & _ & Bsel & Lsel & _).
  destruct (bok_range T sel 32 Bsel ltac:(lia) HT) as [Gsel Tsel].
  pose proof NA as (Bnm & Lnm & _). destruct (bok_range T name _ Bnm ltac:(lia) HT) as [Gnm Tnm].
  destruct (NB sel (or_introl eq_refl)) as (NEss & NEsa & NEsn & NEso).
  pose proof (live_apart C A m md _ _ _ _ CK HW Ls Lsel ltac:(apply zbv_ne; lia) ltac:(lia) ltac:(lia)) as AP1. rewrite !u_Z2bv in AP1 by lia.
  pose proof (live_apart C A m md _ _ _ _ CK HW La Lsel ltac:(apply zbv_ne; lia) ltac:(lia) ltac:(lia)) as AP2. rewrite !u_Z2bv in AP2 by lia.
  pose proof (live_apart C A m md _ _ _ _ CK HW Ls La ltac:(apply zbv_ne; lia) ltac:(lia) ltac:(lia)) as AP3. rewrite !u_Z2bv in AP3 by lia.
  assert (Hname : 0 <= name < 2 ^ 64) by lia.
  assert (F1 : forall x : word, ~ (sel <= u x < sel + 32) -> Ma x = m x).
  { intros x Hx. subst Ma. apply wbytes_outside; rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
  assert (F2 : forall x : word, ~ (arr <= u x < arr + 400) -> Mb x = Ma x).
  { intros x Hx. subst Mb. apply wbytes_outside; rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
  assert (F3 : forall x : word, ~ (sela <= u x < sela + 16) -> M3 x = Mb x).
  { intros x Hx. subst M3. apply wbytes_outside; rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
  (* [comment removed for export] *)
  assert (OLD : forall i, 0 <= i < k ->
            bytes_at M3 (arr + 8 * i) (Z_to_le_bytes 8 (sels i)) /\ sel_at T A M3 (sels i) (vs i) /\ selname_at T A M3 (v_name (vs i)) (nms i)).
  { intros i Hi. destruct (CELLS i Hi) as (Bi & SAi & NAi & N1 & N2).
    split; [|split].
    - apply (bytes_at_frame Mb); [| intros x Hx; rewrite length_Z_to_le_bytes in Hx; apply F3; lia | lia | rewrite length_Z_to_le_bytes; lia].
      subst Mb. apply bytes_at_wbytes_out; [| lia | rewrite length_Z_to_le_bytes; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia
                                           | rewrite length_Z_to_le_bytes, length_N_to_le_bytes, u_Z2bv by lia; cbn; lia].
      apply (bytes_at_frame m); [exact Bi | intros x Hx; rewrite length_Z_to_le_bytes in Hx; apply F1; lia | lia | rewrite length_Z_to_le_bytes; lia].
    - assert (Q1 : forall q, sel_blk (sels i) (vs i) q -> q <> sel) by (intros q Hq; exact (NEso i q Hi (or_introl Hq))).
      assert (Q2 : forall q, sel_blk (sels i) (vs i) q -> q <> arr) by (intros q Hq; exact (proj2 (N1 q (or_introl Hq)))).
      assert (Q3 : forall q, sel_blk (sels i) (vs i) q -> q <> sela) by (intros q Hq; exact (proj1 (N1 q (or_introl Hq)))).
      pose proof (sel_at_frame_blk C A m md Ma T _ _ sel 32 CK HW HT SAi Lsel ltac:(lia) ltac:(lia) Q1 F1) as S1.
      pose proof (sel_at_frame_blk C A Ma md Mb T _ _ arr 400 CK HWa HT S1 La ltac:(lia) ltac:(lia) Q2 F2) as S2.
      exact (sel_at_frame_blk C A Mb md M3 T _ _ sela 16 CK HWb HT S2 Ls ltac:(lia) ltac:(lia) Q3 F3).
    - assert (Q1 : v_name (vs i) <> sel) by (exact (NEso i _ Hi (or_intror eq_refl))).
      assert (Q2 : v_name (vs i) <> arr) by (exact (proj2 (N1 _ (or_intror eq_refl)))).
      assert (Q3 : v_name (vs i) <> sela) by (exact (proj1 (N1 _ (or_intror eq_refl)))).
      pose proof (selname_at_frame_blk C A m md Ma T _ _ sel 32 CK HW HT NAi Lsel ltac:(lia) ltac:(lia) Q1 F1) as S1.
      pose proof (selname_at_frame_blk C A Ma md Mb T _ _ arr 400 CK HWa HT S1 La ltac:(lia) ltac:(lia) Q2 F2) as S2.
      exact (selname_at_frame_blk C A Mb md M3 T _ _ sela 16 CK HWb HT S2 Ls ltac:(lia) ltac:(lia) Q3 F3). }
  assert (NEW : bytes_at M3 (arr + 8 * k) (Z_to_le_bytes 8 sel) /\ sel_at T A M3 sel (set_name v name) /\ selname_at T A M3 name bs).
  { split; [|split].
    - apply (bytes_at_frame Mb); [| intros x Hx; rewrite length_Z_to_le_bytes in Hx; apply F3; lia | lia | rewrite length_Z_to_le_bytes; lia].
      subst Mb. rewrite (w2b_Z 8 sel) by lia. apply bytes_at_wbytes_same; [lia | rewrite length_Z_to_le_bytes; lia].
    - pose proof (sel_at_set_name C A m md T sel v name CK HW HT Hname SA) as S1. rewrite <- EMa in S1.
      assert (Q2 : forall q, sel_blk sel (set_name v name) q -> q <> arr) by (intros q Hq; exact (proj1 (proj2 (NB q Hq)))).
      assert (Q3 : forall q, sel_blk sel (set_name v name) q -> q <> sela) by (intros q Hq; exact (proj1 (NB q Hq))).
      pose proof (sel_at_frame_blk C A Ma md Mb T _ _ arr 400 CK HWa HT S1 La ltac:(lia) ltac:(lia) Q2 F2) as S2.
      exact (sel_at_frame_blk C A Mb md M3 T _ _ sela 16 CK HWb HT S2 Ls ltac:(lia) ltac:(lia) Q3 F3).
    - pose proof (selname_at_frame_blk C A m md Ma T _ _ sel 32 CK HW HT NA Lsel ltac:(lia) ltac:(lia) ltac:(intros E; apply NEsn; symmetry; exact E) F1) as S1.
      pose proof (selname_at_frame_blk C A Ma md Mb T _ _ arr 400 CK HWa HT S1 La ltac:(lia) ltac:(lia) NNa F2) as S2.
      exact (selname_at_frame_blk C A Mb md M3 T _ _ sela 16 CK HWb HT S2 Ls ltac:(lia) ltac:(lia) NNs F3). }
  split; [lia|]. split; [exact Bs|]. split; [exact Ls|].
  split.
  { assert (R2 : RECat Mb sela (sela_flds k 50 arr)).
    { apply (RECat_frame Ma); [apply (RECat_frame m); [exact Rs|]; intros x Hx; cbn in Hx; apply F1; lia|]. intros x Hx. cbn in Hx. apply F2. lia. }
    subst M3. unfold sela_flds.
    eapply (REC_wr' _ _ [(4%nat, k); (4%nat, 50); (8%nat, arr)] _ 0 4);
      [ exact R2 | cbn; lia | cbn; lia | reflexivity | cbn [fld_off Z.of_nat]; f_equal; lia | reflexivity ]. }
  split; [exact Ba|]. split; [exact La|]. split; [exact NEa|].
  split.
  - intros i Hi. destruct (Z.eq_dec i k) as [->|NEi].
    + rewrite !upd_same. destruct NEW as (B1 & S1 & N1). split; [exact B1|]. split; [exact S1|]. split; [exact N1|].
      split.
      * intros p [HB| ->]; [destruct (NB p HB) as (X1 & X2 & _); split; assumption | split; assumption].
      * intros p HB. exact (proj1 (proj2 (proj2 (NB p HB)))).
    + rewrite !upd_other by exact NEi. destruct (OLD i ltac:(lia)) as (B1 & S1 & N1). destruct (CELLS i ltac:(lia)) as (_ & _ & _ & X1 & X2).
      split; [exact B1|]. split; [exact S1|]. split; [exact N1|]. split; assumption.
  - intros i j p q Hi Hj NE HP HQ.
    destruct (Z.eq_dec i k) as [->|NEi]; destruct (Z.eq_dec j k) as [->|NEj]; [lia | | |].
    + rewrite !upd_same in HP. rewrite !upd_other in HQ by exact NEj.
      destruct HP as [HB| ->]; [exact (not_eq_sym (proj2 (proj2 (proj2 (NB p HB))) j q ltac:(lia) HQ)) | exact (not_eq_sym (NNo j q ltac:(lia) HQ))].
    + rewrite !upd_other in HP by exact NEi. rewrite !upd_same in HQ.
      destruct HQ as [HB| ->]; [exact (proj2 (proj2 (proj2 (NB q HB))) i p ltac:(lia) HP) | exact (NNo i p ltac:(lia) HP)].
    + rewrite !upd_other in HP by exact NEi. rewrite !upd_other in HQ by exact NEj. exact (DIST i j p q ltac:(lia) ltac:(lia) NE HP HQ).
Qed.

(* [comment removed for export] *)
Lemma sela_at_ext : forall T A m sela arr n sels vs nms sels' vs' nms',
  (forall i, 0 <= i < n -> sels' i = sels i /\ vs' i = vs i /\ nms' i = nms i) ->
  sela_at T A m sela arr n sels vs nms -> sela_at T A m sela arr n sels' vs' nms'.
Proof.
  intros T A m sela arr n sels vs nms sels' vs' nms' E (Hn & Bs & Ls & Rs & Ba & La & NEa & CELLS & DIST).
  do 7 (split; [assumption|]). split.
  - intros i Hi. destruct (E i Hi) as (E1 & E2 & E3). rewrite E1, E2, E3. exact (CELLS i Hi).
  - intros i j p q Hi Hj NE. destruct (E i Hi) as (E1 & E2 & _). destruct (E j Hj) as (E3 & E4 & _). rewrite E1, E2, E3, E4. exact (DIST i j p q Hi Hj NE).
Qed.

(* [comment removed for export] *)
Lemma sel_off_sub : forall X Y sel v, sub_live X Y -> sel_off Y sel v -> sel_off X sel v.
Proof. intros X Y sel v SUB SO p Hp. destruct (live X (Z_to_bv 64 p)) as [n|] eqn:E; [|reflexivity]. pose proof (SO p Hp) as H. rewrite (SUB _ _ E) in H. discriminate. Qed.

(* [comment removed for export] *)
Lemma sel_at_keep_blk : forall T A A' Ax m m' sel v, T < 2 ^ 64 -> sel_at T A m sel v ->
  (forall p, sel_blk sel v p -> live A' (Z_to_bv 64 p) = live A (Z_to_bv 64 p)) ->
  (forall p, sel_blk sel v p -> live Ax (Z_to_bv 64 p) = live A (Z_to_bv 64 p)) -> LIVK Ax m m' -> sel_at T A' m' sel v.
Proof.
  intros T A A' Ax m m' sel v HT (Hsy & Hsx & Bs & Ls & Rs & Bd & Ld & NEd & ROWS & DIST) E1 E2 LK.
  destruct (bok_range T sel 32 Bs ltac:(lia) HT) as [Gs Ts].
  destruct (bok_range T (v_data v) (8 * v_sy v) Bd ltac:(lia) HT) as [Gd Td].
  assert (Lsx : live Ax (Z_to_bv 64 sel) = Some 32) by (rewrite (E2 sel (or_introl eq_refl)); exact Ls).
  assert (Ldx : live Ax (Z_to_bv 64 (v_data v)) = Some (8 * v_sy v)) by (rewrite (E2 _ (or_intror (or_introl eq_refl))); exact Ld).
  split; [exact Hsy|]. split; [exact Hsx|]. split; [exact Bs|]. split; [rewrite (E1 sel (or_introl eq_refl)); exact Ls|].
  split; [apply (RECat_frame m); [exact Rs|]; intros x Hx; cbn in Hx; apply (LIVK_in Ax m m' sel 32 x LK Lsx); lia|].
  split; [exact Bd|]. split; [rewrite (E1 _ (or_intror (or_introl eq_refl))); exact Ld|]. split; [exact NEd|]. split; [|exact DIST].
  intros i Hi. destruct (ROWS i Hi) as (Br & Lr & N1 & N2 & Bi).
  split; [exact Br|]. split; [rewrite (E1 _ (or_intror (or_intror (ex_intro _ i (conj Hi eq_refl))))); exact Lr|]. split; [exact N1|]. split; [exact N2|].
  apply (bytes_at_frame m); [exact Bi | | lia | rewrite length_Z_to_le_bytes; lia].
  rewrite length_Z_to_le_bytes. intros x Hx. apply (LIVK_in Ax m m' (v_data v) (8 * v_sy v) x LK Ldx); lia.
Qed.

Lemma selname_at_keep_blk : forall T A A' Ax m m' name nm, T < 2 ^ 64 -> selname_at T A m name nm ->
  live A' (Z_to_bv 64 name) = live A (Z_to_bv 64 name) -> live Ax (Z_to_bv 64 name) = live A (Z_to_bv 64 name) -> LIVK Ax m m' ->
  selname_at T A' m' name nm.
Proof.
  intros T A A' Ax m m' name nm HT (Bn & Ln & NZ & Bs) E1 E2 LK.
  destruct (bok_range T name _ Bn ltac:(lia) HT) as [Gn Tn].
  split; [exact Bn|]. split; [rewrite E1; exact Ln|]. split; [exact NZ|].
  assert (EL : Z.of_nat (length (nm ++ [Z_to_bv 8 0])) = Z.of_nat (length nm) + 1) by (rewrite length_app; cbn [length]; lia).
  apply (bytes_at_frame m); [exact Bs | | lia | lia].
  intros x Hx. apply (LIVK_in Ax m m' name _ x LK ltac:(rewrite E2; exact Ln)); lia.
Qed.

Lemma sela_at_keep_blk : forall T A A' Ax m m' sela arr n sels vs nms, T < 2 ^ 64 -> sela_at T A m sela arr n sels vs nms ->
  (forall p, sela_blk sela arr n sels vs p -> live A' (Z_to_bv 64 p) = live A (Z_to_bv 64 p)) ->
  (forall p, sela_blk sela arr n sels vs p -> live Ax (Z_to_bv 64 p) = live A (Z_to_bv 64 p)) -> LIVK Ax m m' ->
  sela_at T A' m' sela arr n sels vs nms.
Proof.
  intros T A A' Ax m m' sela arr n sels vs nms HT (Hn & Bs & Ls & Rs & Ba & La & NEa & CELLS & DIST) E1 E2 LK.
  destruct (bok_range T sela 16 Bs ltac:(lia) HT) as [Gs Ts].
  destruct (bok_range T arr 400 Ba ltac:(lia) HT) as [Ga Ta].
  assert (Lsx : live Ax (Z_to_bv 64 sela) = Some 16) by (rewrite (E2 sela (or_introl eq_refl)); exact Ls).
  assert (Lax : live Ax (Z_to_bv 64 arr) = Some 400) by (rewrite (E2 arr (or_intror (or_introl eq_refl))); exact La).
  split; [exact Hn|]. split; [exact Bs|]. split; [rewrite (E1 sela (or_introl eq_refl)); exact Ls|].
  split; [apply (RECat_frame m); [exact Rs|]; intros x Hx; cbn in Hx; apply (LIVK_in Ax m m' sela 16 x LK Lsx); lia|].
  split; [exact Ba|]. split; [rewrite (E1 arr (or_intror (or_introl eq_refl))); exact La|]. split; [exact NEa|]. split; [|exact DIST].
  intros i Hi. destruct (CELLS i Hi) as (Bi & SA & NA & N1 & N2).
  assert (IN : forall p, seln_blk (sels i) (vs i) p -> sela_blk sela arr n sels vs p) by (intros p Hp; right; right; exists i; split; assumption).
  split.
  { apply (bytes_at_frame m); [exact Bi | | lia | rewrite length_Z_to_le_bytes; lia].
    rewrite length_Z_to_le_bytes. intros x Hx. apply (LIVK_in Ax m m' arr 400 x LK Lax); lia. }
  split; [apply (sel_at_keep_blk T A A' Ax m m' _ _ HT SA); [intros p Hp; apply E1, IN; left; exact Hp | intros p Hp; apply E2, IN; left; exact Hp | exact LK]|].
  split; [apply (selname_at_keep_blk T A A' Ax m m' _ _ HT NA); [apply E1, IN; right; reflexivity | apply E2, IN; right; reflexivity | exact LK]|].
  split; assumption.
Qed.

Lemma sela_hm_keep_blk : forall T A A' Ax m m' sela arr sels vs, T < 2 ^ 64 -> sela_hm T A m sela arr sels vs ->
  (forall p, sela_blk sela arr 10 sels vs p -> live A' (Z_to_bv 64 p) = live A (Z_to_bv 64 p)) ->
  (forall p, sela_blk sela arr 10 sels vs p -> live Ax (Z_to_bv 64 p) = live A (Z_to_bv 64 p)) -> LIVK Ax m m' ->
  sela_hm T A' m' sela arr sels vs.
Proof. intros T A A' Ax m m' sela arr sels vs HT [S D] E1 E2 LK. split; [exact (sela_at_keep_blk T A A' Ax m m' _ _ _ _ _ _ HT S E1 E2 LK) | exact D]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sel_at_keep_pw : forall T A A' m m' sel v, T < 2 ^ 64 -> sel_at T A m sel v ->
  (forall p, sel_blk sel v p -> live A' (Z_to_bv 64 p) = live A (Z_to_bv 64 p)) ->
  (forall p n (x : word), sel_blk sel v p -> live A (Z_to_bv 64 p) = Some n -> p <= u x < p + n -> m' x = m x) ->
  sel_at T A' m' sel v.
Proof.
  intros T A A' m m' sel v HT (Hsy & Hsx & Bs & Ls & Rs & Bd & Ld & NEd & ROWS & DIST) E1 PW.
  destruct (bok_range T sel 32 Bs ltac:(lia) HT) as [Gs Ts].
  destruct (bok_range T (v_data v) (8 * v_sy v) Bd ltac:(lia) HT) as [Gd Td].
  split; [exact Hsy|]. split; [exact Hsx|]. split; [exact Bs|]. split; [rewrite (E1 sel (or_introl eq_refl)); exact Ls|].
  split; [apply (RECat_frame m); [exact Rs|]; intros x Hx; cbn in Hx; apply (PW sel 32 x (or_introl eq_refl) Ls); lia|].
  split; [exact Bd|]. split; [rewrite (E1 _ (or_intror (or_introl eq_refl))); exact Ld|]. split; [exact NEd|]. split; [|exact DIST].
  intros i Hi. destruct (ROWS i Hi) as (Br & Lr & N1 & N2 & Bi).
  split; [exact Br|]. split; [rewrite (E1 _ (or_intror (or_intror (ex_intro _ i (conj Hi eq_refl))))); exact Lr|]. split; [exact N1|]. split; [exact N2|].
  apply (bytes_at_frame m); [exact Bi | | lia | rewrite length_Z_to_le_bytes; lia].
  rewrite length_Z_to_le_bytes. intros x Hx. apply (PW (v_data v) (8 * v_sy v) x (or_intror (or_introl eq_refl)) Ld); lia.
Qed.

Lemma selname_at_keep_pw : forall T A A' m m' name nm, T < 2 ^ 64 -> selname_at T A m name nm ->
  live A' (Z_to_bv 64 name) = live A (Z_to_bv 64 name) ->
  (forall x : word, name <= u x < name + (Z.of_nat (length nm) + 1) -> m' x = m x) -> selname_at T A' m' name nm.
Proof.
  intros T A A' m m' name nm HT (Bn & Ln & NZ & Bs) E1 PW.
  destruct (bok_range T name _ Bn ltac:(lia) HT) as [Gn Tn].
  split; [exact Bn|]. split; [rewrite E1; exact Ln|]. split; [exact NZ|].
  assert (EL : Z.of_nat (length (nm ++ [Z_to_bv 8 0])) = Z.of_nat (length nm) + 1) by (rewrite length_app; cbn [length]; lia).
  apply (bytes_at_frame m); [exact Bs | | lia | lia].
  intros x Hx. apply PW. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition POSTR (C : lctx) (A : AS) (s lo hi : Z) (m m' : word -> option byte) : Prop :=
  (forall a : word, ~ heap_gap C a -> ~ al_globals a -> ~ al_errno_slot a -> ~ hcell a -> ~ scratch C s a ->
                    ~ (lo <= u a < hi) -> m' a = m a) /\
  (forall q k i, live A q = Some k -> 0 <= i < k -> ~ (lo <= u (at_ q i) < hi) -> m' (at_ q i) = m (at_ q i)).

Lemma POSTR_of_POSTM : forall C A A' s lo hi m m', POSTM C A s m m' -> sub_live A' A -> POSTR C A' s lo hi m m'.
Proof.
  intros C A A' s lo hi m m' [F L] SUB. split.
  - intros a H1 H2 H3 H4 H5 _. exact (F a H1 H2 H3 H4 H5).
  - intros q k i Lq Hi _. exact (L q k i (SUB q k Lq) Hi).
Qed.

(* [comment removed for export] *)
Lemma POSTR_POSTD : forall C A A' s s' lo hi hi' pp m m1 m2,
  POSTR C A s lo hi m m1 -> sub_live A' A -> POSTD C A' s' pp m1 m2 -> s' <= s -> lo <= pp -> pp + 8 <= hi' -> hi <= hi' ->
  POSTR C A' s lo hi' m m2.
Proof.
  intros C A A' s s' lo hi hi' pp m m1 m2 [F1 L1] SUB [F2 L2] Hs Hlo Hpp Hhi. split.
  - intros a H1 H2 H3 H4 H5 H6.
    assert (N5 : ~ scratch C s' a) by (unfold scratch in *; lia).
    assert (N6 : ~ inslot pp a) by (unfold inslot; lia).
    rewrite (F2 a H1 H2 H3 H4 N5 N6). apply F1; try assumption. lia.
  - intros q k i Lq Hi H6.
    assert (N6 : ~ inslot pp (at_ q i)) by (unfold inslot; lia).
    rewrite (L2 q k i Lq Hi N6). apply (L1 q k i (SUB q k Lq) Hi). lia.
Qed.

Lemma POSTR_POSTM : forall C A A' s s' lo hi m m1 m2,
  POSTR C A s lo hi m m1 -> sub_live A' A -> POSTM C A' s' m1 m2 -> s' <= s -> POSTR C A' s lo hi m m2.
Proof.
  intros C A A' s s' lo hi m m1 m2 [F1 L1] SUB [F2 L2] Hs. split.
  - intros a H1 H2 H3 H4 H5 H6.
    assert (N5 : ~ scratch C s' a) by (unfold scratch in *; lia).
    rewrite (F2 a H1 H2 H3 H4 N5). apply F1; assumption.
  - intros q k i Lq Hi H6. rewrite (L2 q k i Lq Hi). exact (L1 q k i (SUB q k Lq) Hi H6).
Qed.

(* [comment removed for export] *)
Lemma POSTR_dead : forall C Ar A1 m1 md1 (q : word) (n s lo hi : Z) m m', Cok C -> W C A1 m1 md1 ->
  live A1 q = Some n -> u q <= lo -> hi <= u q + n -> live Ar q = None -> sub_live Ar A1 ->
  POSTR C Ar s lo hi m m' -> POSTM C Ar s m m'.
Proof.
  intros C Ar A1 m1 md1 q n s lo hi m m' CK HW Lq Q1 Q2 Lr SUB [F L]. split.
  - intros a H1 H2 H3 H4 H5. apply F; try assumption. intros IN. apply H1.
    destruct (blk_byte C A1 m1 md1 q n a CK HW Lq ltac:(lia)) as (G & _). exact G.
  - intros q' k i Lq' Hi. apply (L q' k i Lq' Hi). intros IN.
    pose proof (SUB q' k Lq') as L1. assert (NE : q <> q') by (intros ->; congruence).
    pose proof (ai_live_disjoint A1 m1 (m_vmmaps md1) q n q' k (w_inv _ _ _ _ HW) Lq L1 NE) as D.
    pose proof (ai_live_hull A1 m1 (m_vmmaps md1) q' k (w_inv _ _ _ _ HW) L1) as (Hk0 & _ & TOPq & _). pose proof (round16_ge k Hk0).
    pose proof (ai_live_hull A1 m1 (m_vmmaps md1) q n (w_inv _ _ _ _ HW) Lq) as (Hn0 & _ & TOPn & _). pose proof (round16_ge n Hn0).
    pose proof (alloc_top_lt (m_vmmaps md1)) as T. unfold two_pow_64 in T.
    assert (R : u q' <= u (at_ q' i) < u q' + k) by (unfold at_; rewrite u_Z2bv by (pose proof (u64_range q'); lia); lia).
    lia.
Qed.

(* [comment removed for export] *)
Lemma POSTR_byte : forall C A s lo hi m m' (q : word) k (x : word), POSTR C A s lo hi m m' -> live A q = Some k ->
  u q <= u x < u q + k -> ~ (lo <= u x < hi) -> m' x = m x.
Proof.
  intros C A s lo hi m m' q k x [_ L] Lq R NS.
  assert (E : at_ q (u x - u q) = x) by (unfold at_; apply bv_eq; rewrite u_Z2bv by (pose proof (u64_range x); pose proof (u64_range q); lia); lia).
  rewrite <- E. rewrite <- E in NS. exact (L q k (u x - u q) Lq ltac:(lia) NS).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sela_dst (C : lctx) (A : AS) (m : word -> option byte) (s arr : Z) (sels : Z -> Z) (vs : Z -> selv) (i : Z)
                    (A1 : AS) (M1 : word -> option byte) : Prop :=
  POSTR C A1 s arr (arr + 8 * i) m M1 /\ sub_live A1 A /\
  (forall j p, 0 <= j < i -> seln_blk (sels j) (vs j) p -> live A1 (Z_to_bv 64 p) = None) /\
  (forall q, (forall j p, 0 <= j < i -> seln_blk (sels j) (vs j) p -> q <> Z_to_bv 64 p) -> live A1 q = live A q).

Lemma sela_dst_0 : forall C A m s arr sels vs M1, POSTM C A s m M1 -> sela_dst C A m s arr sels vs 0 A M1.
Proof.
  intros C A m s arr sels vs M1 PM.
  split; [exact (POSTR_of_POSTM C A A s arr (arr + 8 * 0) m M1 PM (sub_live_refl A))|]. split; [apply sub_live_refl|].
  split; [intros j p Hj; lia | intros q _; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma sela_blk_w : forall T A m sela arr n sels vs nms j p, T < 2 ^ 64 -> sela_at T A m sela arr n sels vs nms -> 0 <= j < n ->
  seln_blk (sels j) (vs j) p ->
  0 <= p < 2 ^ 64 /\ Z_to_bv 64 p <> Z_to_bv 64 sela /\ Z_to_bv 64 p <> Z_to_bv 64 arr /\
  (forall j' p', 0 <= j' < n -> j' <> j -> seln_blk (sels j') (vs j') p' -> Z_to_bv 64 p <> Z_to_bv 64 p').
Proof.
  intros T A m sela arr n sels vs nms j p HT SA Hj HB.
  destruct (sela_blk_live T A m sela arr n sels vs nms j p SA Hj HB) as (k & _ & Hk & G1 & G2).
  pose proof SA as (Hn & Bs & _ & _ & Ba & _ & _ & CELLS & DIST).
  destruct (bok_range T sela 16 Bs ltac:(lia) HT) as [Gs _]. destruct (bok_range T arr 400 Ba ltac:(lia) HT) as [Ga _].
  destruct (CELLS j Hj) as (_ & _ & _ & N1 & _). destruct (N1 p HB) as [NEs NEa].
  split; [lia|]. split; [apply zbv_ne; [lia | lia | exact NEs]|]. split; [apply zbv_ne; [lia | lia | exact NEa]|].
  intros j' p' Hj' NE HB'.
  destruct (sela_blk_live T A m sela arr n sels vs nms j' p' SA Hj' HB') as (k' & _ & Hk' & G1' & G2').
  apply zbv_ne; [lia | lia |]. exact (DIST j j' p p' Hj Hj' (not_eq_sym NE) HB HB').
Qed.

(* [comment removed for export] *)
Lemma sela_dst_live : forall C A m s T sela arr n sels vs nms i A1 M1, T < 2 ^ 64 ->
  sela_at T A m sela arr n sels vs nms -> 0 <= i <= n -> sela_dst C A m s arr sels vs i A1 M1 ->
  live A1 (Z_to_bv 64 sela) = Some 16 /\ live A1 (Z_to_bv 64 arr) = Some 400 /\
  (forall j p, i <= j < n -> seln_blk (sels j) (vs j) p -> live A1 (Z_to_bv 64 p) = live A (Z_to_bv 64 p)).
Proof.
  intros C A m s T sela arr n sels vs nms i A1 M1 HT SA Hi (_ & _ & _ & OTH).
  pose proof SA as (_ & _ & Ls & _ & _ & La & _).
  split; [rewrite OTH; [exact Ls|]; intros j p Hj HB; destruct (sela_blk_w T A m sela arr n sels vs nms j p HT SA ltac:(lia) HB) as (_ & X & _);
          intros E; apply X; symmetry; exact E|].
  split; [rewrite OTH; [exact La|]; intros j p Hj HB; destruct (sela_blk_w T A m sela arr n sels vs nms j p HT SA ltac:(lia) HB) as (_ & _ & X & _);
          intros E; apply X; symmetry; exact E|].
  intros j p Hj HB. apply OTH. intros j' p' Hj' HB'.
  destruct (sela_blk_w T A m sela arr n sels vs nms j p HT SA ltac:(lia) HB) as (_ & _ & _ & X). exact (X j' p' ltac:(lia) ltac:(lia) HB').
Qed.

(* [comment removed for export] *)
Lemma sela_dst_mem : forall C A m md s T sela arr n sels vs nms i A1 M1 (p k : Z) (x : word), Cok C -> W C A m md -> T < 2 ^ 64 ->
  sela_at T A m sela arr n sels vs nms -> 0 <= i <= n -> sela_dst C A m s arr sels vs i A1 M1 ->
  live A (Z_to_bv 64 p) = Some k -> live A1 (Z_to_bv 64 p) = Some k -> p <> arr -> 0 <= p -> p + k < 2 ^ 64 -> 0 <= k ->
  p <= u x < p + k -> M1 x = m x.
Proof.
  intros C A m md s T sela arr n sels vs nms i A1 M1 p k x CK HW HT SA Hi (PR & _) Lp Lp1 NE Hp Hpk Hk Hx.
  pose proof SA as (Hn & _ & _ & _ & Ba & La & _). destruct (bok_range T arr 400 Ba ltac:(lia) HT) as [Ga Ta].
  pose proof (live_apart C A m md _ _ _ _ CK HW Lp La ltac:(apply zbv_ne; lia) Hk ltac:(lia)) as AP. rewrite !u_Z2bv in AP by lia.
  apply (POSTR_byte C A1 s arr (arr + 8 * i) m M1 (Z_to_bv 64 p) k x PR Lp1); rewrite ?u_Z2bv by lia; lia.
Qed.

(* [comment removed for export] *)
Lemma sela_dst_hdr : forall C A m md s T sela arr n sels vs nms i A1 M1, Cok C -> W C A m md -> T < 2 ^ 64 ->
  sela_at T A m sela arr n sels vs nms -> 0 <= i <= n -> sela_dst C A m s arr sels vs i A1 M1 ->
  RECat M1 sela (sela_flds n 50 arr).
Proof.
  intros C A m md s T sela arr n sels vs nms i A1 M1 CK HW HT SA Hi SD.
  destruct (sela_dst_live C A m s T sela arr n sels vs nms i A1 M1 HT SA Hi SD) as (Ls1 & _ & _).
  pose proof SA as (_ & Bs & Ls & Rs & _ & _ & NEa & _). destruct (bok_range T sela 16 Bs ltac:(lia) HT) as [Gs Ts].
  apply (RECat_frame m); [exact Rs|]. intros x Hx. cbn in Hx.
  apply (sela_dst_mem C A m md s T sela arr n sels vs nms i A1 M1 sela 16 x CK HW HT SA Hi SD Ls Ls1); first [lia | intros E; apply NEa; symmetry; exact E].
Qed.

(* [comment removed for export] *)
Lemma sela_dst_cell : forall C A m md s T sela arr n sels vs nms i A1 M1 j, Cok C -> W C A m md -> T < 2 ^ 64 ->
  sela_at T A m sela arr n sels vs nms -> 0 <= i <= n -> sela_dst C A m s arr sels vs i A1 M1 -> i <= j < n ->
  bytes_at M1 (arr + 8 * j) (Z_to_le_bytes 8 (sels j)) /\ sel_at T A1 M1 (sels j) (vs j) /\ selname_at T A1 M1 (v_name (vs j)) (nms j).
Proof.
  intros C A m md s T sela arr n sels vs nms i A1 M1 j CK HW HT SA Hi SD Hj.
  destruct (sela_dst_live C A m s T sela arr n sels vs nms i A1 M1 HT SA Hi SD) as (_ & La1 & LIVE).
  pose proof SD as (PR & _).
  pose proof SA as (Hn & _ & _ & _ & Ba & La & _ & CELLS & _). destruct (bok_range T arr 400 Ba ltac:(lia) HT) as [Ga Ta].
  destruct (CELLS j ltac:(lia)) as (Bj & SAj & NAj & N1 & _).
  split; [|split].
  - apply (bytes_at_frame m); [exact Bj | | lia | rewrite length_Z_to_le_bytes; lia].
    rewrite length_Z_to_le_bytes. intros x Hx.
    apply (POSTR_byte C A1 s arr (arr + 8 * i) m M1 (Z_to_bv 64 arr) 400 x PR La1); rewrite ?u_Z2bv by lia; lia.
  - apply (sel_at_keep_pw T A A1 m M1 _ _ HT SAj).
    + intros p HB. exact (LIVE j p Hj (or_introl HB)).
    + intros p k x HB Lp Hx. destruct (sel_blk_live T A m _ _ p SAj HB) as (k' & Lp' & Hk' & G1 & G2).
      rewrite Lp in Lp'. injection Lp' as <-.
      apply (sela_dst_mem C A m md s T sela arr n sels vs nms i A1 M1 p k x CK HW HT SA Hi SD Lp); try lia.
      * rewrite (LIVE j p Hj (or_introl HB)). exact Lp.
      * exact (proj2 (N1 p (or_introl HB))).
  - pose proof NAj as ((G1 & G2 & _) & Ln & _).
    apply (selname_at_keep_pw T A A1 m M1 _ _ HT NAj).
    + exact (LIVE j _ Hj (or_intror eq_refl)).
    + intros x Hx.
      apply (sela_dst_mem C A m md s T sela arr n sels vs nms i A1 M1 (v_name (vs j)) _ x CK HW HT SA Hi SD Ln); try lia.
      * rewrite (LIVE j _ Hj (or_intror eq_refl)). exact Ln.
      * exact (proj2 (N1 _ (or_intror eq_refl))).
Qed.

(* [comment removed for export] *)
Lemma sela_dst_step : forall C A m s s' T sela arr n sels vs nms i A1 M1 A2 M2, T < 2 ^ 64 ->
  sela_at T A m sela arr n sels vs nms -> 0 <= i < n -> s' <= s -> sela_dst C A m s arr sels vs i A1 M1 ->
  (forall q, seln_blk (sels i) (vs i) q -> live A2 (Z_to_bv 64 q) = None) ->
  (forall q, (forall p, seln_blk (sels i) (vs i) p -> q <> Z_to_bv 64 p) -> live A2 q = live A1 q) -> sub_live A2 A1 ->
  POSTD C A2 s' (arr + 8 * i) M1 M2 ->
  sela_dst C A m s arr sels vs (i + 1) A2 M2.
Proof.
  intros C A m s s' T sela arr n sels vs nms i A1 M1 A2 M2 HT SA Hi Hs (PR & SUB & DEAD & OTH) D2 O2 SUB2 PD.
  split; [apply (POSTR_POSTD C A1 A2 s s' arr (arr + 8 * i) (arr + 8 * (i + 1)) (arr + 8 * i) m M1 M2 PR SUB2 PD); lia|].
  split; [exact (sub_live_trans _ _ _ SUB2 SUB)|].
  split.
  - intros j p Hj HB. destruct (Z.eq_dec j i) as [->|NE]; [exact (D2 p HB)|].
    rewrite O2; [apply (DEAD j p); [lia | exact HB]|].
    intros p' HB'. destruct (sela_blk_w T A m sela arr n sels vs nms j p HT SA ltac:(lia) HB) as (_ & _ & _ & X).
    exact (X i p' ltac:(lia) ltac:(lia) HB').
  - intros q NQ. rewrite O2; [apply OTH; intros j p Hj HB; apply (NQ j p); [lia | exact HB] | intros p HB; apply (NQ i p); [lia | exact HB]].
Qed.

(* [comment removed for export] *)
Lemma sela_dst_off : forall C A m s T sela arr n sels vs nms A3 M3 A4 A5, T < 2 ^ 64 ->
  sela_at T A m sela arr n sels vs nms -> sela_dst C A m s arr sels vs n A3 M3 ->
  live A4 (Z_to_bv 64 arr) = None -> (forall q, q <> Z_to_bv 64 arr -> live A4 q = live A3 q) ->
  live A5 (Z_to_bv 64 sela) = None -> (forall q, q <> Z_to_bv 64 sela -> live A5 q = live A4 q) ->
  sela_off A5 sela arr n sels vs /\ sela_only A A5 sela arr n sels vs /\ sub_live A5 A3.
Proof.
  intros C A m s T sela arr n sels vs nms A3 M3 A4 A5 HT SA (_ & _ & DEAD & OTH) La4 LEQ4 Ls5 LEQ5.
  pose proof SA as (Hn & Bs & _ & _ & Ba & _ & NEa & _).
  destruct (bok_range T sela 16 Bs ltac:(lia) HT) as [Gs _]. destruct (bok_range T arr 400 Ba ltac:(lia) HT) as [Ga _].
  split; [|split].
  - intros p [->|[->|(j & Hj & HB)]].
    + exact Ls5.
    + rewrite (LEQ5 (Z_to_bv 64 arr) ltac:(apply zbv_ne; [lia | lia | exact NEa])). exact La4.
    + destruct (sela_blk_w T A m sela arr n sels vs nms j p HT SA Hj HB) as (_ & X1 & X2 & _).
      rewrite (LEQ5 _ X1), (LEQ4 _ X2). exact (DEAD j p Hj HB).
  - intros q NQ. rewrite (LEQ5 q (NQ sela (or_introl eq_refl))), (LEQ4 q (NQ arr (or_intror (or_introl eq_refl)))).
    apply OTH. intros j p Hj HB. apply NQ. right; right. exists j. split; assumption.
  - intros q k Lq. destruct (bv_eq_dec _ q (Z_to_bv 64 sela)) as [->|NE]; [rewrite Ls5 in Lq; discriminate|]. rewrite (LEQ5 q NE) in Lq.
    destruct (bv_eq_dec _ q (Z_to_bv 64 arr)) as [->|NE2]; [rewrite La4 in Lq; discriminate|]. rewrite (LEQ4 q NE2) in Lq. exact Lq.
Qed.

(* [comment removed for export] *)
Lemma sela_dst_POSTM : forall C A m s T sela arr n sels vs nms A3 M3 md3 A5 M5, Cok C -> W C A3 M3 md3 -> T < 2 ^ 64 ->
  sela_at T A m sela arr n sels vs nms -> sela_dst C A m s arr sels vs n A3 M3 ->
  sub_live A5 A3 -> live A5 (Z_to_bv 64 arr) = None -> POSTM C A5 s M3 M5 -> POSTM C A5 s m M5.
Proof.
  intros C A m s T sela arr n sels vs nms A3 M3 md3 A5 M5 CK HW3 HT SA SD SUB La5 PM.
  assert (Hn0 : 0 <= n <= n) by (destruct SA as [Hn0 _]; lia).
  destruct (sela_dst_live C A m s T sela arr n sels vs nms n A3 M3 HT SA Hn0 SD) as (_ & La3 & _).
  pose proof SD as (PR & _). pose proof SA as (Hn & _ & _ & _ & Ba & _). destruct (bok_range T arr 400 Ba ltac:(lia) HT) as [Ga Ta].
  pose proof (POSTR_POSTM C A3 A5 s s arr (arr + 8 * n) m M3 M5 PR SUB PM ltac:(lia)) as PR5.
  apply (POSTR_dead C A5 A3 M3 md3 (Z_to_bv 64 arr) 400 s arr (arr + 8 * n) m M5 CK HW3 La3); try assumption; rewrite u_Z2bv by lia; lia.
Qed.

End Sel.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
