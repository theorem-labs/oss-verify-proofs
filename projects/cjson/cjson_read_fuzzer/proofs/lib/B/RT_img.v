(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.cjson.cjson_read_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import InitMem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AHandoffLib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_defs RT_data RT_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanHexZero.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ABSS_LO : Z := 0xa62e0.     (* [comment removed for export] *)
Definition ASEG3_LO : Z := 0xa3000.    (* [comment removed for export] *)
Definition ASEG2_LO : Z := 0xa1000.    (* [comment removed for export] *)
Definition seg3 : Segment := AsanUbsan_segment_003.
Definition seg2 : Segment := AsanUbsan_segment_002.
Definition s3 : PrimString.string := AsanUbsan_seg_bytes_003.
Definition s2 : PrimString.string := AsanUbsan_seg_bytes_002.

(* [comment removed for export] *)
Fixpoint bss_chk (s : PrimString.string) (n : nat) (off : N) : bool :=
  match n with
  | O => true
  | S n' => match hex_byte_at s off with
            | Some b => Z.eqb (bv_unsigned b) 0 && bss_chk s n' (off + 1)%N
            | None => false
            end
  end.
(* [comment removed for export] *)
Fixpoint def_chk (s : PrimString.string) (n : nat) (off : N) : bool :=
  match n with
  | O => true
  | S n' => match hex_byte_at s off with Some _ => def_chk s n' (off + 1)%N | None => false end
  end.

(* [comment removed for export] *)
Lemma bss_chk_complete : forall s n off,
  (forall k, (k < n)%nat -> hex_byte_at s (off + N.of_nat k)%N = Some (Z_to_bv 8 0)) -> bss_chk s n off = true.
Proof.
  intros s n. induction n as [|n IH]; intros off H; [reflexivity|].
  cbn [bss_chk]. pose proof (H 0%nat ltac:(lia)) as H0. rewrite N.add_0_r in H0. rewrite H0.
  change (Z.eqb (bv_unsigned (Z_to_bv 8 0)) 0) with true. cbn [andb]. apply IH. intros k Hk.
  replace (off + 1 + N.of_nat k)%N with (off + N.of_nat (S k))%N by lia. apply H. lia.
Qed.
Lemma bss_zwin : AsanHexZero.zwin s3 (Uint63.of_Z 26048) (Uint63.of_Z 11213376) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma bss_chk_ok : bss_chk s3 (Z.to_nat (AIMG_HI - ABSS_LO)) (Z.to_N (ABSS_LO - ASEG3_LO)) = true.
Proof.
  apply bss_chk_complete. intros k Hk.
  apply (AsanHexZero.zwin_hex_byte_at s3 (Uint63.of_Z 26048) (Uint63.of_Z 11213376) _ bss_zwin).
  - vm_compute. discriminate.
  - change (Uint63.to_Z (Uint63.of_Z 26048)) with 26048. unfold ABSS_LO, ASEG3_LO. lia.
  - change (Uint63.to_Z (Uint63.of_Z 26048)) with 26048. change (Uint63.to_Z (Uint63.of_Z 11213376)) with 11213376.
    unfold AIMG_HI, ABSS_LO, ASEG3_LO in *. lia.
Qed.
Lemma def_chk3_ok : def_chk s3 (Z.to_nat (ABSS_LO - ASEG3_LO)) 0%N = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma def_chk2_ok : def_chk s2 (Z.to_nat (ASEG3_LO - ASEG2_LO)) 0%N = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma bss_chk_sound : forall s n off, bss_chk s n off = true ->
  forall k, (k < n)%nat -> hex_byte_at s (off + N.of_nat k)%N = Some (zb 0).
Proof.
  intros s n. induction n as [|n IH]; intros off H k Hk; [lia|].
  cbn [bss_chk] in H. destruct (hex_byte_at s off) as [b|] eqn:E; [|discriminate].
  apply andb_prop in H as [Hb H]. destruct k as [|k].
  - rewrite N.add_0_r. rewrite E. f_equal. apply Z.eqb_eq in Hb. apply bv_eq. rewrite Hb. reflexivity.
  - replace (off + N.of_nat (S k))%N with (off + 1 + N.of_nat k)%N by lia. apply (IH _ H). lia.
Qed.
Lemma def_chk_sound : forall s n off, def_chk s n off = true ->
  forall k, (k < n)%nat -> exists b, hex_byte_at s (off + N.of_nat k)%N = Some b.
Proof.
  intros s n. induction n as [|n IH]; intros off H k Hk; [lia|].
  cbn [def_chk] in H. destruct (hex_byte_at s off) as [b|] eqn:E; [|discriminate]. destruct k as [|k].
  - rewrite N.add_0_r. exists b. exact E.
  - replace (off + N.of_nat (S k))%N with (off + 1 + N.of_nat k)%N by lia. apply (IH _ H). lia.
Qed.

(* [comment removed for export] *)
Lemma find_seg3 : forall a, ASEG3_LO <= a < AIMG_HI -> find_segment bsegs a 1 = Some seg3.
Proof.
  intros a Ha. unfold ASEG3_LO, AIMG_HI in Ha.
  cbn [find_segment bsegs AsanUbsan.M.loaded_segments AsanUbsan_loaded_segments
       seg_base seg_size AsanUbsan_segment_000 AsanUbsan_segment_001
       AsanUbsan_segment_002 AsanUbsan_segment_003 Z.of_N].
  repeat match goal with |- context [if ?c then _ else _] =>
    let e := fresh in destruct c eqn:e; [apply andb_prop in e as [?X ?Y]; apply Z.leb_le in X; apply Z.leb_le in Y; cbn in X, Y; try lia
                                       | apply andb_false_iff in e as [e|e]; apply Z.leb_gt in e; cbn in e; try lia] end.
  reflexivity.
Qed.
Lemma find_seg2 : forall a, ASEG2_LO <= a < ASEG3_LO -> find_segment bsegs a 1 = Some seg2.
Proof.
  intros a Ha. unfold ASEG2_LO, ASEG3_LO in Ha.
  cbn [find_segment bsegs AsanUbsan.M.loaded_segments AsanUbsan_loaded_segments
       seg_base seg_size AsanUbsan_segment_000 AsanUbsan_segment_001
       AsanUbsan_segment_002 AsanUbsan_segment_003 Z.of_N].
  repeat match goal with |- context [if ?c then _ else _] =>
    let e := fresh in destruct c eqn:e; [apply andb_prop in e as [?X ?Y]; apply Z.leb_le in X; apply Z.leb_le in Y; cbn in X, Y; try lia
                                       | apply andb_false_iff in e as [e|e]; apply Z.leb_gt in e; cbn in e; try lia] end.
  reflexivity.
Qed.

Lemma s3_chunk : Z.to_N (Uint63.to_Z (PrimString.length s3) / 2) = 0x55c000%N.
Proof. vm_compute. reflexivity. Qed.
Lemma s2_chunk : Z.to_N (Uint63.to_Z (PrimString.length s2) / 2) = 0x2000%N.
Proof. vm_compute. reflexivity. Qed.

Lemma seg3_byte_at : forall a, ASEG3_LO <= a < AIMG_HI ->
  segment_byte_at (seg_bytes seg3) (Z.to_N (a - ASEG3_LO)) = hex_byte_at s3 (Z.to_N (a - ASEG3_LO)).
Proof.
  intros a Ha. unfold ASEG3_LO, AIMG_HI in *. cbn [seg_bytes seg3 AsanUbsan_segment_003 segment_byte_at].
  fold s3. rewrite s3_chunk. destruct (N.ltb_spec0 (Z.to_N (a - 667648)) 0x55c000%N); [reflexivity| exfalso; lia].
Qed.
Lemma seg2_byte_at : forall a, ASEG2_LO <= a < ASEG3_LO ->
  segment_byte_at (seg_bytes seg2) (Z.to_N (a - ASEG2_LO)) = hex_byte_at s2 (Z.to_N (a - ASEG2_LO)).
Proof.
  intros a Ha. unfold ASEG2_LO, ASEG3_LO in *. cbn [seg_bytes seg2 AsanUbsan_segment_002 segment_byte_at].
  fold s2. rewrite s2_chunk. destruct (N.ltb_spec0 (Z.to_N (a - 659456)) 0x2000%N); [reflexivity| exfalso; lia].
Qed.

(* [comment removed for export] *)
Lemma seg_rom3 : forall a, ASEG3_LO <= a < AIMG_HI -> seg_rom bsegs (wa a) = hex_byte_at s3 (Z.to_N (a - ASEG3_LO)).
Proof.
  intros a Ha. unfold seg_rom, memory_read. rewrite wa_unsigned by (unfold ASEG3_LO, AIMG_HI in Ha; lia).
  change (Z.of_N 1) with 1. rewrite (find_seg3 a Ha).
  change (seg_readable seg3) with true. cbn iota. change (N.to_nat 1) with 1%nat. change (Z.of_N (seg_base seg3)) with ASEG3_LO.
  cbn [segment_read_bytes]. rewrite (seg3_byte_at a Ha). destruct (hex_byte_at s3 (Z.to_N (a - ASEG3_LO))); reflexivity.
Qed.
Lemma seg_rom2 : forall a, ASEG2_LO <= a < ASEG3_LO -> seg_rom bsegs (wa a) = hex_byte_at s2 (Z.to_N (a - ASEG2_LO)).
Proof.
  intros a Ha. unfold seg_rom, memory_read. rewrite wa_unsigned by (unfold ASEG2_LO, ASEG3_LO in Ha; lia).
  change (Z.of_N 1) with 1. rewrite (find_seg2 a Ha).
  change (seg_readable seg2) with true. cbn iota. change (N.to_nat 1) with 1%nat. change (Z.of_N (seg_base seg2)) with ASEG2_LO.
  cbn [segment_read_bytes]. rewrite (seg2_byte_at a Ha). destruct (hex_byte_at s2 (Z.to_N (a - ASEG2_LO))); reflexivity.
Qed.

(* [comment removed for export] *)
Theorem bss_rom : forall a, ABSS_LO <= a < AIMG_HI -> seg_rom bsegs (wa a) = Some (zb 0).
Proof.
  intros a Ha. unfold ABSS_LO, AIMG_HI in Ha. rewrite seg_rom3 by (unfold ASEG3_LO, AIMG_HI; lia).
  pose proof (bss_chk_sound _ _ _ bss_chk_ok (Z.to_nat (a - ABSS_LO)) ltac:(unfold ABSS_LO, AIMG_HI; lia)) as E.
  rewrite <- E. f_equal. unfold ABSS_LO, ASEG3_LO. lia.
Qed.
(* [comment removed for export] *)
Theorem img_rw_rom : forall a, ASEG2_LO <= a < AIMG_HI -> exists b, seg_rom bsegs (wa a) = Some b.
Proof.
  intros a Ha. unfold ASEG2_LO, AIMG_HI in Ha.
  destruct (Z.ltb_spec0 a ASEG3_LO) as [L|L]; unfold ASEG3_LO in L.
  - rewrite seg_rom2 by (unfold ASEG2_LO, ASEG3_LO; lia).
    destruct (def_chk_sound _ _ _ def_chk2_ok (Z.to_nat (a - ASEG2_LO)) ltac:(unfold ASEG2_LO, ASEG3_LO; lia)) as [b E].
    exists b. rewrite <- E. f_equal. unfold ASEG2_LO. lia.
  - destruct (Z.ltb_spec0 a ABSS_LO) as [B|B]; unfold ABSS_LO in B.
    + rewrite seg_rom3 by (unfold ASEG3_LO, AIMG_HI; lia).
      destruct (def_chk_sound _ _ _ def_chk3_ok (Z.to_nat (a - ASEG3_LO)) ltac:(unfold ABSS_LO, ASEG3_LO; lia)) as [b E].
      exists b. rewrite <- E. f_equal. unfold ASEG3_LO. lia.
    + exists (zb 0). apply bss_rom. unfold ABSS_LO, AIMG_HI. lia.
Qed.
Theorem img_rw_wview : forall m a, ASEG2_LO <= a < AIMG_HI -> wview bsegs m (wa a) <> None.
Proof.
  intros m a Ha. unfold ASEG2_LO, AIMG_HI in Ha. unfold wview. destruct (m (wa a)); [discriminate|].
  rewrite wa_unsigned by lia.
  destruct (Z.ltb_spec0 a ASEG3_LO) as [L|L]; unfold ASEG3_LO in L.
  - rewrite find_seg2 by (unfold ASEG2_LO, ASEG3_LO; lia). change (seg_writable seg2) with true. cbn iota.
    change (Z.of_N (seg_base seg2)) with ASEG2_LO. rewrite (seg2_byte_at a ltac:(unfold ASEG2_LO, ASEG3_LO; lia)).
    rewrite <- seg_rom2 by (unfold ASEG2_LO, ASEG3_LO; lia). destruct (img_rw_rom a ltac:(unfold ASEG2_LO, AIMG_HI; lia)) as [b ->]. discriminate.
  - rewrite find_seg3 by (unfold ASEG3_LO, AIMG_HI; lia). change (seg_writable seg3) with true. cbn iota.
    change (Z.of_N (seg_base seg3)) with ASEG3_LO. rewrite (seg3_byte_at a ltac:(unfold ASEG3_LO, AIMG_HI; lia)).
    rewrite <- seg_rom3 by (unfold ASEG3_LO, AIMG_HI; lia). destruct (img_rw_rom a ltac:(unfold ASEG2_LO, AIMG_HI; lia)) as [b ->]. discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pristine_sub : forall m lo hi lo' hi', pristine m lo hi -> lo <= lo' -> hi' <= hi -> pristine m lo' hi'.
Proof. intros m lo hi lo' hi' H H1 H2 x Hx. apply H. lia. Qed.
Lemma pristine_noneW : forall m lo hi (a : word), pristine m lo hi -> lo <= bv_unsigned a < hi -> m a = None.
Proof.
  intros m lo hi a H Ha. rewrite <- (Z_to_bv_bv_unsigned a). change (Z_to_bv 64 (bv_unsigned a)) with (wa (bv_unsigned a)). apply H. exact Ha.
Qed.

(* [comment removed for export] *)
Lemma img_rw_stk : forall m lo hi, ASEG2_LO <= lo -> hi <= AIMG_HI -> lo <= hi -> stk bsegs m lo hi.
Proof.
  intros m lo hi H1 H2 H3. unfold ASEG2_LO, AIMG_HI in *. split; [lia|]. split; [lia|]. intros a Ha. split.
  - apply img_rw_wview. unfold ASEG2_LO, AIMG_HI. lia.
  - unfold mrd. destruct (m (wa a)) as [b|]; [exists b; reflexivity|]. apply img_rw_rom. unfold ASEG2_LO, AIMG_HI. lia.
Qed.

(* [comment removed for export] *)
Lemma bss_zero_chunk : forall m a n, pristine m a (a + n) -> ABSS_LO <= a -> a + n <= AIMG_HI -> 0 <= n ->
  rw_cells bsegs m a [CB (Z.to_nat n) (repeat (zb 0) (Z.to_nat n))].
Proof.
  intros m a n P H1 H2 Hn. unfold ABSS_LO, AIMG_HI in *.
  split; [split|].
  - cbn. rewrite repeat_length. split; [reflexivity| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. unfold bytes_at. rewrite repeat_length. split; [lia|]. split; [lia|].
    intros i Hi. unfold mrd. rewrite (P (a + Z.of_nat i)) by lia. rewrite bss_rom by (unfold ABSS_LO, AIMG_HI; lia).
    symmetry. apply nth_error_repeat. exact Hi.
  - cbn [cells_size Cells.csize]. rewrite Nat.add_0_r. unfold wr_at. split; [lia|]. split; [lia|]. intros i Hi. apply img_rw_wview. unfold ASEG2_LO, AIMG_HI. lia.
Qed.
(* [comment removed for export] *)
Lemma bss_zero_cells : forall m a cs, pristine m a (a + Z.of_nat (cells_size cs)) -> ABSS_LO <= a ->
  a + Z.of_nat (cells_size cs) <= AIMG_HI -> cells_wf cs -> cells_bytes cs = repeat (zb 0) (cells_size cs) ->
  rw_cells bsegs m a cs.
Proof.
  intros m a cs P H1 H2 Hwf Hb.
  pose proof (bss_zero_chunk m a (Z.of_nat (cells_size cs)) P H1 H2 ltac:(lia)) as R. rewrite Nat2Z.id in R.
  eapply rw_cells_recast; [exact R| exact Hwf| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact Hb| cbn; lia].
Qed.
Lemma bss_w8 : forall m a, pristine m a (a + 8) -> ABSS_LO <= a -> a + 8 <= AIMG_HI -> rw_cells bsegs m a [C8 (wz 0)].
Proof. intros m a P H1 H2. apply bss_zero_cells; [exact P| exact H1| exact H2| cbn; tauto| reflexivity]. Qed.
Lemma bss_w4 : forall m a, pristine m a (a + 4) -> ABSS_LO <= a -> a + 4 <= AIMG_HI -> rw_cells bsegs m a [C4 (wz 0)].
Proof. intros m a P H1 H2. apply bss_zero_cells; [exact P| exact H1| exact H2| cbn; tauto| reflexivity]. Qed.
Lemma bss_w1 : forall m a, pristine m a (a + 1) -> ABSS_LO <= a -> a + 1 <= AIMG_HI -> rw_cells bsegs m a [C1 (zb 0)].
Proof. intros m a P H1 H2. apply bss_zero_cells; [exact P| exact H1| exact H2| cbn; tauto| reflexivity]. Qed.
(* [comment removed for export] *)
Lemma bss_junk : forall m a n, pristine m a (a + n) -> ABSS_LO <= a -> a + n <= AIMG_HI -> 0 <= n ->
  exists j, rw_cells bsegs m a [CB (Z.to_nat n) j].
Proof. intros m a n P H1 H2 Hn. eexists. apply bss_zero_chunk; assumption. Qed.

(* [comment removed for export] *)
Lemma img_lit : forall m a bs, pristine m a (a + Z.of_nat (length bs)) -> rw_bytes_b bsegs a bs = true ->
  0 <= a -> a + Z.of_nat (length bs) <= 2^64 -> rw_cells bsegs m a [CB (length bs) bs].
Proof.
  intros m a bs P Hb H1 H2. apply rw_cells_image0; [| exact Hb| exact H1| exact H2].
  intros x Hx. eapply pristine_noneW; [exact P| lia].
Qed.
Lemma img_lit_cells : forall m a cs, pristine m a (a + Z.of_nat (cells_size cs)) ->
  rw_bytes_b bsegs a (cells_bytes cs) = true -> cells_wf cs -> 0 <= a -> a + Z.of_nat (cells_size cs) <= 2^64 ->
  rw_cells bsegs m a cs.
Proof.
  intros m a cs P Hb Hwf H1 H2. pose proof (cells_bytes_length cs Hwf) as L.
  pose proof (img_lit m a (cells_bytes cs) ltac:(rewrite L; exact P) Hb H1 ltac:(rewrite L; exact H2)) as R.
  eapply rw_cells_recast; [exact R| exact Hwf| cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity| cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma img_junk : forall m a n, pristine m a (a + n) -> ASEG2_LO <= a -> a + n <= AIMG_HI -> 0 <= n ->
  exists j, rw_cells bsegs m a [CB (Z.to_nat n) j].
Proof.
  intros m a n P H1 H2 Hn. unfold ASEG2_LO, AIMG_HI in *.
  assert (G : forall k, (k <= Z.to_nat n)%nat -> exists bs, length bs = k /\ forall i, (i < k)%nat -> seg_rom bsegs (wa (a + Z.of_nat i)) = nth_error bs i).
  { induction k as [|k IH]; intros Hk.
    - exists []. split; [reflexivity|]. intros i Hi; lia.
    - destruct (IH ltac:(lia)) as (bs & Hlen & Hbs). destruct (img_rw_rom (a + Z.of_nat k) ltac:(unfold ASEG2_LO, AIMG_HI; lia)) as [b Hb].
      exists (bs ++ [b]). split. { rewrite length_app; cbn; lia. }
      intros i Hi. destruct (Nat.eqb_spec i k).
      + subst i. rewrite nth_error_app2 by lia. rewrite Hlen, Nat.sub_diag. exact Hb.
      + rewrite nth_error_app1 by lia. apply Hbs. lia. }
  destruct (G (Z.to_nat n) ltac:(lia)) as (bs & Hlen & Hbs). exists bs. split; [split|].
  - cbn. rewrite Hlen. split; [reflexivity| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. unfold bytes_at. rewrite Hlen. split; [lia|]. split; [lia|].
    intros i Hi. unfold mrd. rewrite (P (a + Z.of_nat i)) by lia. apply Hbs. exact Hi.
  - cbn [cells_size Cells.csize]. rewrite Nat.add_0_r. unfold wr_at. split; [lia|]. split; [lia|]. intros i Hi. apply img_rw_wview. unfold ASEG2_LO, AIMG_HI. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition alink_lo1 : Z := 0xa1138.  Definition alink_hi1 : Z := 0xa23f8.
Definition alink_lo2 : Z := 0xa3400.  Definition alink_hi2 : Z := 0xa35c8.
Definition alink_ok (p : Z * Z) : bool :=
  (((alink_lo1 <=? fst p) && (fst p + 8 <=? alink_hi1)) || ((alink_lo2 <=? fst p) && (fst p + 8 <=? alink_hi2)))
  && rw_bytes_b bsegs (fst p) (le8 (wz (snd p))).
Lemma alink_chk : forallb alink_ok ALINK_WORDS = true.
Proof. vm_compute. reflexivity. Qed.

Lemma alink_cells : forall m, pristine m alink_lo1 alink_hi1 -> pristine m alink_lo2 alink_hi2 ->
  forall a v, In (a, v) ALINK_WORDS -> cells_at bsegs m a [C8 (wz v)].
Proof.
  intros m P1 P2 a v Hin.
  pose proof (proj1 (forallb_forall _ _) alink_chk (a, v) Hin) as H. unfold alink_ok in H. cbn [fst snd] in H.
  apply andb_prop in H as [Hr Hb].
  assert (P : pristine m a (a + 8)).
  { apply orb_prop in Hr. destruct Hr as [Hr|Hr]; apply andb_prop in Hr as [X Y]; apply Z.leb_le in X; apply Z.leb_le in Y;
      [eapply (pristine_sub _ _ _ _ _ P1)| eapply (pristine_sub _ _ _ _ _ P2)]; lia. }
  assert (R : rw_cells bsegs m a [C8 (wz v)]).
  { apply img_lit_cells; [exact P| exact Hb| cbn; tauto| |]; unfold alink_lo1, alink_hi1, alink_lo2, alink_hi2 in *.
    - apply orb_prop in Hr. destruct Hr as [Hr|Hr]; apply andb_prop in Hr as [X Y]; apply Z.leb_le in X; lia.
    - apply orb_prop in Hr. destruct Hr as [Hr|Hr]; apply andb_prop in Hr as [X Y]; apply Z.leb_le in Y; cbn; lia. }
  exact (proj1 R).
Qed.


End CeilWrap.
