(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare MemSplit BnZX BnZXTac BnMem BnDefs LibIface.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import ZX BM. Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u_w64 : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (w64 a) = a.
Proof. intros a Ha. unfold w64. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. Qed.

Lemma w64_succ : forall a, (w64 a + 1)%bv = w64 (a + 1).
Proof.
  intros a. unfold w64. rewrite <- (Z_to_bv_bv_unsigned 64 (Z_to_bv 64 a + 1)). apply Z2bv_eqm.
  rewrite bv_add_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616.
  change (bv_unsigned (1%bv : word)) with 1. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with 18446744073709551616.
  rewrite Z.mod_mod by lia. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma w64_of_word : forall x : word, w64 (bv_unsigned x) = x.
Proof. intros x. unfold w64. apply Z_to_bv_bv_unsigned. Qed.

Lemma byte_eq8 : forall z, Z_to_bv 8 z = Z_to_bv 8 (z mod 256).
Proof.
  intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Glue.
Variable segs : list Segment.

Lemma rdn_of_mem_bytes : forall mem bs a,
  mem_bytes mem a bs -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  rdn segs mem (w64 a) (length bs) = Some (map (Z_to_bv 8) bs).
Proof.
  intros mem bs. induction bs as [|z t IH]; intros a H Ha Hb; [reflexivity|].
  cbn [rdn length map]. cbn [length] in Hb.
  pose proof (H 0%nat ltac:(cbn; lia)) as H0. cbn [nth Z.of_nat] in H0. unfold mem_byte in H0. rewrite Z.add_0_r in H0.
  rewrite H0. rewrite w64_succ.
  rewrite (IH (a + 1)); [reflexivity| |lia|lia].
  intros i Hi. specialize (H (S i) ltac:(cbn; lia)). cbn [nth] in H.
  unfold mem_byte in *. replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (S i)) by lia. exact H.
Qed.

Lemma cellN_of_mem_bytes : forall mem bs a,
  mem_bytes mem a bs -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  cellN segs mem a (length bs) (bytes_le_to_Z (map (Z_to_bv 8) bs)).
Proof.
  intros mem bs a H Ha Hb. exists (map (Z_to_bv 8) bs). split; [|reflexivity].
  unfold w64 in *. apply rdn_of_mem_bytes; assumption.
Qed.

(* [comment removed for export] *)
Lemma le_bytes_S : forall n v, le_bytes (S n) v = (v mod 256) :: le_bytes n (v / 256).
Proof.
  intros n v. unfold le_bytes. cbn [seq map]. f_equal.
  - rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r. reflexivity.
  - rewrite <- seq_shift, map_map. apply map_ext_in. intros i _.
    rewrite Zdiv_Zdiv by lia. f_equal. f_equal.
    replace (8 * Z.of_nat (S i)) with (8 + 8 * Z.of_nat i) by lia. rewrite Z.pow_add_r by lia. reflexivity.
Qed.

Lemma length_le_bytes : forall n v, length (le_bytes n v) = n.
Proof. intros. unfold le_bytes. rewrite length_map, length_seq. reflexivity. Qed.

Lemma map_le_bytes : forall n v, map (Z_to_bv 8) (le_bytes n v) = Z_to_le_bytes n v.
Proof.
  induction n as [|n IH]; intros v; [reflexivity|].
  rewrite le_bytes_S. cbn [map Z_to_le_bytes]. f_equal.
  - symmetry. apply byte_eq8.
  - rewrite IH. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma cellN_u64 : forall mem a v,
  mem_u64 mem a v -> 0 <= v -> 0 <= a -> a + 8 <= 2 ^ 64 -> cellN segs mem a 8 (v mod 2 ^ 64).
Proof.
  intros mem a v H Hv Ha Hb. unfold mem_u64 in H.
  pose proof (cellN_of_mem_bytes mem (le_bytes 8 v) a H Ha ltac:(rewrite length_le_bytes; change (Z.of_nat 8) with 8; lia)) as C.
  rewrite length_le_bytes, map_le_bytes, bytes_le_Z_to_le in C by exact Hv. exact C.
Qed.

Lemma cellN_u64' : forall mem a v,
  mem_u64 mem a v -> 0 <= v < 2 ^ 64 -> 0 <= a -> a + 8 <= 2 ^ 64 -> cellN segs mem a 8 v.
Proof. intros mem a v H Hv Ha Hb. rewrite <- (Z.mod_small v (2 ^ 64)) by lia. apply cellN_u64; [exact H|lia..]. Qed.

Lemma cellN_byte : forall mem a b,
  mem_byte mem a b -> 0 <= b < 256 -> 0 <= a -> a + 1 <= 2 ^ 64 -> cellN segs mem a 1 b.
Proof.
  intros mem a b H Hb Ha Hb'.
  pose proof (cellN_of_mem_bytes mem [b] a) as C. cbn [length map Z.of_nat] in C.
  rewrite bytes_le_single, Z_to_bv_unsigned in C. unfold bv_wrap in C. change (bv_modulus 8) with 256 in C.
  rewrite Z.mod_small in C by lia. apply C; [|lia|lia].
  intros i Hi. cbn in Hi. destruct i; [|lia]. cbn [nth Z.of_nat]. rewrite Z.add_0_r. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition tbl_get (L : list (Z * Z)) (a : Z) : option Z :=
  match find (fun p => fst p =? a) L with Some p => Some (snd p) | None => None end.

Fixpoint tbl_bytes (L : list (Z * Z)) (a : Z) (n : nat) : option (list Z) :=
  match n with
  | O => Some []
  | S n' => match tbl_get L a, tbl_bytes L (a + 1) n' with
            | Some b, Some r => Some (b :: r)
            | _, _ => None
            end
  end.

Definition tbl_val (L : list (Z * Z)) (a : Z) (n : nat) : option Z :=
  match tbl_bytes L a n with Some bs => Some (bytes_le_to_Z (map (Z_to_bv 8) bs)) | None => None end.

Lemma tbl_get_In : forall L a b, tbl_get L a = Some b -> In (a, b) L.
Proof.
  intros L a b H. unfold tbl_get in H. destruct (find _ L) as [[a' b']|] eqn:E; [|discriminate].
  injection H as <-. apply find_some in E as [Hin Heq]. cbn in Heq. apply Z.eqb_eq in Heq. subst a'. exact Hin.
Qed.

Lemma mem_bytes_of_tbl : forall L mem n a bs,
  cells_ok L mem -> tbl_bytes L a n = Some bs -> mem_bytes mem a bs /\ length bs = n.
Proof.
  intros L mem n. induction n as [|n IH]; intros a bs HL H.
  - cbn in H. injection H as <-. split; [intros i Hi; cbn in Hi; lia | reflexivity].
  - cbn [tbl_bytes] in H. destruct (tbl_get L a) as [b|] eqn:Eg; [|discriminate].
    destruct (tbl_bytes L (a + 1) n) as [r|] eqn:Er; [|discriminate]. injection H as <-.
    destruct (IH (a + 1) r HL Er) as [Hr Hlen]. split; [|cbn; lia].
    intros i Hi. destruct i as [|i].
    + cbn [nth Z.of_nat]. rewrite Z.add_0_r. unfold mem_byte. apply HL. apply tbl_get_In. exact Eg.
    + cbn [nth]. replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia. apply Hr. cbn in Hi. lia.
Qed.

Lemma cellN_of_tbl : forall L mem a n v,
  cells_ok L mem -> tbl_val L a n = Some v -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> cellN segs mem a n v.
Proof.
  intros L mem a n v HL H Ha Hb. unfold tbl_val in H.
  destruct (tbl_bytes L a n) as [bs|] eqn:E; [|discriminate]. injection H as <-.
  destruct (mem_bytes_of_tbl L mem n a bs HL E) as [Hm <-]. apply cellN_of_mem_bytes; assumption.
Qed.

(* [comment removed for export] *)
Lemma rdn_of_cells1 : forall mem bs a,
  (forall i, (i < length bs)%nat -> cellN segs mem (a + Z.of_nat i) 1 (nth i bs 0)) ->
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  rdn segs mem (w64 a) (length bs) = Some (map (Z_to_bv 8) bs).
Proof.
  intros mem bs. induction bs as [|z t IH]; intros a H Ha Hb; [reflexivity|].
  cbn [length] in Hb. cbn [length map].
  destruct (H 0%nat ltac:(cbn; lia)) as (bs0 & R0 & V0). cbn [nth] in V0. rewrite Z.add_0_r in R0.
  unfold w64. cbn [rdn] in R0 |- *.
  destruct (match mem (Z_to_bv 64 a) with Some b => Some b | None => seg_rom segs (Z_to_bv 64 a) end) as [x|]; [|discriminate].
  injection R0 as <-. rewrite bytes_le_single in V0.
  change (Z_to_bv 64 a) with (w64 a). rewrite w64_succ.
  rewrite (IH (a + 1)); [| |lia|lia].
  - f_equal. f_equal. rewrite <- V0. symmetry. apply Z_to_bv_bv_unsigned.
  - intros i Hi. specialize (H (S i) ltac:(cbn; lia)). cbn [nth] in H.
    replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (S i)) by lia. exact H.
Qed.

Lemma cellN_of_rdtbl : forall L mem a n v,
  (forall x b, In (x, b) L -> cellN segs mem x 1 b) -> tbl_val L a n = Some v -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  cellN segs mem a n v.
Proof.
  intros L mem a n v HL H Ha Hb. unfold tbl_val in H.
  destruct (tbl_bytes L a n) as [bs|] eqn:E; [|discriminate]. injection H as <-.
  assert (GEN : forall k a' bs', tbl_bytes L a' k = Some bs' ->
            length bs' = k /\ forall i, (i < length bs')%nat -> cellN segs mem (a' + Z.of_nat i) 1 (nth i bs' 0)).
  { induction k as [|k IH]; intros a' bs' Hk.
    - cbn in Hk. injection Hk as <-. split; [reflexivity | intros i Hi; cbn in Hi; lia].
    - cbn [tbl_bytes] in Hk. destruct (tbl_get L a') as [b|] eqn:Eg; [|discriminate].
      destruct (tbl_bytes L (a' + 1) k) as [r|] eqn:Er; [|discriminate]. injection Hk as <-.
      destruct (IH (a' + 1) r Er) as [Hlen Hr]. split; [cbn; lia|].
      intros i Hi. destruct i as [|i].
      + cbn [nth Z.of_nat]. rewrite Z.add_0_r. apply HL. apply tbl_get_In. exact Eg.
      + cbn [nth]. replace (a' + Z.of_nat (S i)) with (a' + 1 + Z.of_nat i) by lia. apply Hr. cbn in Hi. lia. }
  destruct (GEN n a bs E) as [Hlen Hbs]. subst n.
  exists (map (Z_to_bv 8) bs). split; [|reflexivity]. unfold w64. apply rdn_of_cells1; assumption.
Qed.

(* [comment removed for export] *)
Lemma mem_byte_of_tbl : forall L mem a b, cells_ok L mem -> tbl_get L a = Some b -> mem_byte mem a b.
Proof. intros L mem a b HL H. unfold mem_byte. apply HL. apply tbl_get_In. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rdn_rom : forall k m (a : word),
  bv_unsigned a + Z.of_nat k <= 2 ^ 64 ->
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat k ->
     forall b, m x = Some b -> memory_read segs x 1 = Some [b]) ->
  rdn segs m a k = rdn segs (fun _ => None) a k.
Proof.
  induction k as [|k IH]; intros m a Hnw Hro; [reflexivity|].
  cbn [rdn].
  assert (E1 : match m a with Some b => Some b | None => seg_rom segs a end = seg_rom segs a).
  { destruct (m a) as [b|] eqn:E; [|reflexivity].
    unfold seg_rom. rewrite (Hro a ltac:(pose proof (u64_range a); lia) b E). reflexivity. }
  rewrite E1. destruct (seg_rom segs a) as [b|]; [|reflexivity].
  destruct k as [|k']; [reflexivity|].
  assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1) by (apply u_add1; lia).
  rewrite (IH m (a + 1)%bv ltac:(lia) ltac:(intros x Hx; apply Hro; lia)). reflexivity.
Qed.

(* [comment removed for export] *)
Definition in_ro (RO : list (Z * Z)) (a : Z) (n : nat) : bool :=
  existsb (fun r => (fst r <=? a) && (a + Z.of_nat n <=? snd r)) RO.

Definition rom_val (a : Z) (n : nat) : option Z :=
  match rdn segs (fun _ => None) (w64 a) n with Some bs => Some (bytes_le_to_Z bs) | None => None end.

Lemma cellN_ro : forall RO mem a n v,
  ro_ok segs RO mem -> in_ro RO a n = true -> rom_val a n = Some v ->
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> cellN segs mem a n v.
Proof.
  intros RO mem a n v Hro Hin Hv Ha Hb. unfold rom_val in Hv.
  destruct (rdn segs (fun _ => None) (w64 a) n) as [bs|] eqn:E; [|discriminate]. injection Hv as <-.
  exists bs. split; [|reflexivity]. unfold w64 in E. rewrite <- E.
  destruct n as [|n']; [cbn [rdn] in E |- *; reflexivity|].
  apply rdn_rom.
  - rewrite u_Z2bv64, Z.mod_small by lia. lia.
  - intros x Hx b Hm. rewrite u_Z2bv64, Z.mod_small in Hx by lia.
    rewrite <- (Z_to_bv_bv_unsigned 64 x) in Hm |- *. apply (Hro (bv_unsigned x) b); [|exact Hm].
    unfold in_ro in Hin. apply existsb_exists in Hin as (r & Hr & Hc).
    apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    exists r. split; [exact Hr|]. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma store_ok_of_def_nat : forall mem k a,
  mem_def mem a (Z.of_nat k) -> 0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
  RiscvSemantics.store_ok segs mem (w64 a) k = true.
Proof.
  intros mem k. induction k as [|k IH]; intros a H Ha Hb; [reflexivity|].
  cbn [RiscvSemantics.store_ok]. unfold wview.
  destruct (H 0 ltac:(lia)) as [b Hb0]. rewrite Z.add_0_r in Hb0. rewrite Hb0.
  rewrite w64_succ. apply IH; [|lia|lia].
  intros i Hi. replace (a + 1 + i) with (a + (1 + i)) by lia. apply H. lia.
Qed.

Lemma store_ok_of_def : forall mem a n,
  mem_def mem a n -> 0 <= a -> 0 <= n -> a + n <= 2 ^ 64 ->
  RiscvSemantics.store_ok segs mem (Z_to_bv 64 a) (Z.to_nat n) = true.
Proof.
  intros mem a n H Ha Hn Hb. change (Z_to_bv 64 a) with (w64 a). apply store_ok_of_def_nat; [|lia|lia].
  rewrite Z2Nat.id by lia. exact H.
Qed.

(* [comment removed for export] *)
Lemma store_ok_of_def_in : forall mem base len a n,
  mem_def mem base len -> (0 <= base /\ base + len <= 2 ^ 64 /\ base <= a /\ a + Z.of_nat n <= base + len) ->
  RiscvSemantics.store_ok segs mem (Z_to_bv 64 a) n = true.
Proof.
  intros mem base len a n H (H1 & H2 & H3 & H4). change (Z_to_bv 64 a) with (w64 a). apply store_ok_of_def_nat; [|lia|lia].
  intros i Hi. replace (a + i) with (base + (a - base + i)) by lia. apply H. lia.
Qed.

(* [comment removed for export] *)
Lemma rdn_ex_of_def : forall mem n a, mem_def mem a (Z.of_nat n) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  exists bs, rdn segs mem (w64 a) n = Some bs.
Proof.
  intros mem n. induction n as [|n IH]; intros a H Ha Hb; [exists []; reflexivity|].
  cbn [rdn]. destruct (H 0 ltac:(lia)) as [b Hb0]. rewrite Z.add_0_r in Hb0. rewrite Hb0, w64_succ.
  destruct (IH (a + 1)) as [bs Hbs]; [|lia|lia|]. 
  { intros i Hi. replace (a + 1 + i) with (a + (1 + i)) by lia. apply H. lia. }
  rewrite Hbs. eexists; reflexivity.
Qed.

Lemma cellN_ex_of_def : forall mem a n, mem_def mem a (Z.of_nat n) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  exists v, cellN segs mem a n v /\ 0 <= v < 2 ^ (8 * Z.of_nat n).
Proof.
  intros mem a n H Ha Hb. destruct (rdn_ex_of_def mem n a H Ha Hb) as [bs Hbs].
  exists (bytes_le_to_Z bs). assert (C : cellN segs mem a n (bytes_le_to_Z bs)) by (exists bs; split; [exact Hbs|reflexivity]).
  split; [exact C | exact (cellN_range _ _ _ _ _ C)].
Qed.

(* [comment removed for export] *)
Lemma mem_def_sub : forall mem a n a' n', mem_def mem a n -> a <= a' -> a' + n' <= a + n -> mem_def mem a' n'.
Proof. intros mem a n a' n' H H1 H2 i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply H. lia. Qed.

(* [comment removed for export] *)
Lemma mem_def_of_u64 : forall mem a v, mem_u64 mem a v -> mem_def mem a 8.
Proof.
  intros mem a v H i Hi. specialize (H (Z.to_nat i) ltac:(rewrite length_le_bytes; lia)).
  unfold mem_byte in H. rewrite Z2Nat.id in H by lia. eexists. exact H.
Qed.

Lemma mem_def_of_byte : forall mem a b, mem_byte mem a b -> mem_def mem a 1.
Proof. intros mem a b H i Hi. replace (a + i) with a by lia. eexists. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mem_frame_of_unch : forall m m' rs, unch m m' rs -> mem_grows m m' -> mem_frame m m' rs.
Proof.
  intros m m' rs Hu Hg. split.
  - intros a Ha. apply Hu. exact Ha.
  - intros a b Hb. destruct (m' a) as [b'|] eqn:E; [exists b'; reflexivity|].
    exfalso. apply (Hg a); [rewrite Hb; discriminate | exact E].
Qed.

(* [comment removed for export] *)
Lemma wb_out : forall M a (bs : list byte) x,
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 -> 0 <= x < 2 ^ 64 ->
  (x < a \/ a + Z.of_nat (length bs) <= x) ->
  wbytes M (Z_to_bv 64 a) bs (w64 x) = M (w64 x).
Proof.
  intros M a bs x Ha Hb Hx Hd. apply wbytes_outside; rewrite ?u_Z2bv64, ?Z.mod_small by lia; unfold w64;
    rewrite ?u_Z2bv64, ?Z.mod_small by lia; lia.
Qed.

Lemma wb_in : forall M a (bs : list byte) x,
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 -> a <= x < a + Z.of_nat (length bs) ->
  wbytes M (Z_to_bv 64 a) bs (w64 x) = Some (nth (Z.to_nat (x - a)) bs (Z_to_bv 8 0)).
Proof.
  intros M a bs x Ha Hb Hx. unfold w64. rewrite wbytes_inside; rewrite ?u_Z2bv64, ?Z.mod_small by lia; [|lia|lia].
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma nth_le_bytes : forall n v i, (i < n)%nat -> nth i (le_bytes n v) 0 = (v / 2 ^ (8 * Z.of_nat i)) mod 256.
Proof.
  induction n as [|n IH]; intros v i Hi; [lia|].
  rewrite le_bytes_S. destruct i as [|i].
  - cbn [nth]. rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r. reflexivity.
  - cbn [nth]. rewrite IH by lia. rewrite Zdiv_Zdiv by lia. f_equal. f_equal.
    replace (8 * Z.of_nat (S i)) with (8 + 8 * Z.of_nat i) by lia. rewrite Z.pow_add_r by lia. reflexivity.
Qed.

Lemma nth_w2lb : forall n (w : word) i, (i < n)%nat ->
  nth i (word_to_le_bytes n w) (Z_to_bv 8 0) = Z_to_bv 8 ((bv_unsigned w / 2 ^ (8 * Z.of_nat i)) mod 256).
Proof.
  intros n w i Hi. unfold word_to_le_bytes. rewrite <- map_le_bytes.
  rewrite map_nth, nth_le_bytes by exact Hi. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mem_byte_wb_in : forall M a n (w : word) x b,
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> a <= x < a + Z.of_nat n ->
  (bv_unsigned w / 2 ^ (8 * (x - a))) mod 256 = b mod 256 ->
  mem_byte (wbytes M (Z_to_bv 64 a) (word_to_le_bytes n w)) x b.
Proof.
  intros M a n w x b Ha Hb Hx Hv. unfold mem_byte.
  rewrite wb_in by (rewrite ?length_N_to_le_bytes; lia).
  rewrite nth_w2lb by lia. rewrite Z2Nat.id by lia. rewrite Hv. f_equal. symmetry. apply byte_eq8.
Qed.

(* [comment removed for export] *)
Lemma mem_byte_wb_out : forall M a n (w : word) x b,
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> 0 <= x < 2 ^ 64 -> (x < a \/ a + Z.of_nat n <= x) ->
  mem_byte M x b -> mem_byte (wbytes M (Z_to_bv 64 a) (word_to_le_bytes n w)) x b.
Proof.
  intros M a n w x b Ha Hb Hx Hd H. unfold mem_byte. rewrite wb_out by (rewrite ?length_N_to_le_bytes; lia). exact H.
Qed.

(* [comment removed for export] *)
Lemma mem_byte_wbs_out : forall M a (bs : list byte) x b,
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 -> 0 <= x < 2 ^ 64 -> (x < a \/ a + Z.of_nat (length bs) <= x) ->
  mem_byte M x b -> mem_byte (wbytes M (Z_to_bv 64 a) bs) x b.
Proof. intros M a bs x b Ha Hb Hx Hd H. unfold mem_byte. rewrite wb_out by lia. exact H. Qed.

Lemma mem_byte_repeat_in : forall M a k (c : byte) x b,
  0 <= a -> a + Z.of_nat k <= 2 ^ 64 -> a <= x < a + Z.of_nat k -> c = Z_to_bv 8 b ->
  mem_byte (wbytes M (Z_to_bv 64 a) (repeat c k)) x b.
Proof.
  intros M a k c x b Ha Hb Hx ->. unfold mem_byte. rewrite wb_in by (rewrite ?repeat_length; lia).
  rewrite nth_repeat_lt by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mod64_div_mod256 : forall v (i : nat), (i < 8)%nat ->
  ((v mod 2 ^ 64) / 2 ^ (8 * Z.of_nat i)) mod 256 = (v / 2 ^ (8 * Z.of_nat i)) mod 256.
Proof.
  intros v i Hi.
  do 8 (destruct i as [|i]; [cbn -[Z.modulo Z.div]; lia|]). lia.
Qed.

Lemma mem_u64_wb_same : forall M a (w : word) v,
  0 <= a -> a + 8 <= 2 ^ 64 -> bv_unsigned w = v mod 2 ^ 64 ->
  mem_u64 (wbytes M (Z_to_bv 64 a) (word_to_le_bytes 8 w)) a v.
Proof.
  intros M a w v Ha Hb Hv i Hi. rewrite length_le_bytes in Hi.
  apply mem_byte_wb_in; [lia | change (Z.of_nat 8) with 8; lia | lia |].
  replace (a + Z.of_nat i - a) with (Z.of_nat i) by lia. rewrite Hv.
  rewrite nth_le_bytes by exact Hi. rewrite Z.mod_mod by lia. apply mod64_div_mod256. exact Hi.
Qed.

Lemma mem_u64_wb_out : forall M a n (w : word) x v,
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> 0 <= x -> x + 8 <= 2 ^ 64 -> (x + 8 <= a \/ a + Z.of_nat n <= x) ->
  mem_u64 M x v -> mem_u64 (wbytes M (Z_to_bv 64 a) (word_to_le_bytes n w)) x v.
Proof.
  intros M a n w x v Ha Hb Hx Hx8 Hd H i Hi. rewrite length_le_bytes in Hi.
  apply mem_byte_wb_out; try lia. apply H. rewrite length_le_bytes. exact Hi.
Qed.

Lemma mem_u64_wbs_out : forall M a (bs : list byte) x v,
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 -> 0 <= x -> x + 8 <= 2 ^ 64 -> (x + 8 <= a \/ a + Z.of_nat (length bs) <= x) ->
  mem_u64 M x v -> mem_u64 (wbytes M (Z_to_bv 64 a) bs) x v.
Proof.
  intros M a bs x v Ha Hb Hx Hx8 Hd H i Hi. rewrite length_le_bytes in Hi.
  apply mem_byte_wbs_out; try lia. apply H. rewrite length_le_bytes. exact Hi.
Qed.

(* [comment removed for export] *)
Lemma mem_def_wbs : forall M (a : word) bs x n, mem_def M x n -> mem_def (wbytes M a bs) x n.
Proof.
  intros M a bs x n H i Hi. destruct (H i Hi) as [b Hb].
  destruct (wbytes M a bs (w64 (x + i))) as [b'|] eqn:E; [exists b'; reflexivity|].
  exfalso. apply (wbytes_grows bs M a (w64 (x + i))); [rewrite Hb; discriminate | exact E].
Qed.

(* [comment removed for export] *)
Lemma mem_byte_unch : forall m m' rs x b,
  unch m m' rs -> 0 <= x < 2 ^ 64 -> (forall r, In r rs -> x < fst r \/ snd r <= x) -> mem_byte m x b -> mem_byte m' x b.
Proof.
  intros m m' rs x b Hu Hx Hd H. unfold mem_byte in *. rewrite <- H. apply Hu.
  intros (r & Hin & Hr). rewrite u_w64 in Hr by lia. specialize (Hd r Hin). lia.
Qed.

Lemma mem_u64_unch : forall m m' rs x v,
  unch m m' rs -> 0 <= x -> x + 8 <= 2 ^ 64 -> (forall r, In r rs -> x + 8 <= fst r \/ snd r <= x) -> mem_u64 m x v -> mem_u64 m' x v.
Proof.
  intros m m' rs x v Hu Hx Hx8 Hd H i Hi. rewrite length_le_bytes in Hi.
  eapply mem_byte_unch; [exact Hu | lia | | apply H; rewrite length_le_bytes; exact Hi].
  intros r Hr. specialize (Hd r Hr). lia.
Qed.

Lemma mem_def_grows : forall m m' x n, mem_grows m m' -> mem_def m x n -> mem_def m' x n.
Proof.
  intros m m' x n Hg H i Hi. destruct (H i Hi) as [b Hb].
  destruct (m' (w64 (x + i))) as [b'|] eqn:E; [exists b'; reflexivity|].
  exfalso. apply (Hg (w64 (x + i))); [rewrite Hb; discriminate | exact E].
Qed.

Lemma cells_ok_unch : forall L m m' rs,
  unch m m' rs -> (forall a b, In (a, b) L -> 0 <= a < 2 ^ 64 /\ forall r, In r rs -> a < fst r \/ snd r <= a) ->
  cells_ok L m -> cells_ok L m'.
Proof.
  intros L m m' rs Hu Hd H a b Hin. destruct (Hd a b Hin) as [Ha Hr].
  pose proof (mem_byte_unch m m' rs a b Hu Ha Hr) as X. unfold mem_byte, w64 in X. apply X. apply H. exact Hin.
Qed.

Lemma ro_ok_unch : forall RO m m' rs,
  unch m m' rs -> (forall a, LibIface.in_ranges a RO -> 0 <= a < 2 ^ 64 /\ forall r, In r rs -> a < fst r \/ snd r <= a) ->
  ro_ok segs RO m -> ro_ok segs RO m'.
Proof.
  intros RO m m' rs Hu Hd H a b Hin Hm. destruct (Hd a Hin) as [Ha Hr]. apply H; [exact Hin|].
  rewrite <- Hm. symmetry. apply Hu. intros (r & Hr1 & Hr2). rewrite u_Z2bv64, Z.mod_small in Hr2 by lia.
  specialize (Hr r Hr1). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma keeps_cs_of_keeps : forall regs regs', keeps CS regs regs' -> keeps_cs regs regs'.
Proof. intros regs regs' K r Hr. apply K. exact Hr. Qed.

Lemma keeps_cs_trans : forall r1 r2 r3, keeps_cs r1 r2 -> keeps_cs r2 r3 -> keeps_cs r1 r3.
Proof. intros r1 r2 r3 A B r Hr. rewrite (B r Hr). apply A, Hr. Qed.

Lemma ret_ok_of_mod4 : forall ret : word, bv_unsigned ret mod 4 = 0 -> ret_ok ret.
Proof. intros ret H. apply ret_ok_even. lia. Qed.

End Glue.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hide (P : Prop) : Prop := P.
Ltac hide H := lazymatch type of H with ?P => change P with (hide P) in H end.
Ltac unhide := unfold hide in *.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma cellN_rt_A : forall mem a n v,
  rt_ok mem -> tbl_val RT_A a n = Some v -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> cellN SEGS_A mem a n v.
Proof. intros mem a n v Hrt Hv Ha Hb. apply (cellN_of_rdtbl SEGS_A RT_A); [exact Hrt | exact Hv | exact Ha | exact Hb]. Qed.

Lemma cellN_ro_A : forall mem a n v,
  ro_ok SEGS_A RO_A mem -> in_ro RO_A a n = true -> rom_val SEGS_A a n = Some v ->
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> cellN SEGS_A mem a n v.
Proof. intros. eapply cellN_ro; eauto. Qed.
