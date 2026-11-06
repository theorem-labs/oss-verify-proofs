From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells codec_img codec_agree
  codec_main_inv codec_main_oweb_lib LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.

(** Facts shared by the segments OWE9 (SCRIBBLE) and OWE10 (COUNTER) of the walk of LLVMFuzzerTestOneInput
    in the plain image: the frame cut around k.bytes, cutting a cell into pieces, the seven_bit test byte
    by byte, the bytes and keys owe_sysex writes. *)

(** ---- the frame cut around k.bytes (FP + 0x38, 24 bytes) ----
    The two cases read k.bytes byte by byte while they store into the want fields and pl[]; with k.bytes
    held as bytes_at (and its write permission as wr_at) the stores leave its cell alone. *)

Lemma body_cut : forall e m k c rem tl,
  rw_cells rsegs m (bv_unsigned (e_sp e) + -400) (body_cells e k c rem tl) ->
  rw_cells rsegs m (bv_unsigned (e_sp e) + -400)
    [C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0x13f0);
     C4 (Z_to_bv 64 (k_kind k)); CB 4 (k_pad k); C8 (Z_to_bv 64 (k_p k)); C8 (Z_to_bv 64 (k_desk k));
     C4 (Z_to_bv 64 (k_a k)); C4 (Z_to_bv 64 (k_b k)); C4 (Z_to_bv 64 (k_c k)); C4 (Z_to_bv 64 (k_delta k))] /\
  bytes_at rsegs m (bv_unsigned (e_sp e) + -344) (k_bytes k) /\
  wr_at rsegs m (bv_unsigned (e_sp e) + -344) 24 /\
  rw_cells rsegs m (bv_unsigned (e_sp e) + -320)
    [C8 (Z_to_bv 64 (k_n k)); C4 (Z_to_bv 64 (k_rc k)); CB 32 (k_before k); CB 32 (k_out k);
     C4 (Z_to_bv 64 (k_want_rc k)); CB 24 (k_want k); C8 (Z_to_bv 64 (k_want_len k));
     C4 (Z_to_bv 64 (k_want_key k)); C4 (Z_to_bv 64 (k_want_display k));
     C8 (Z_to_bv 64 (bv_unsigned (e_p e) + c)); C8 (Z_to_bv 64 rem); CB 80 tl].
Proof.
  intros e m k c rem tl H.
  change (body_cells e k c rem tl) with
    ([C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0x13f0);
      C4 (Z_to_bv 64 (k_kind k)); CB 4 (k_pad k); C8 (Z_to_bv 64 (k_p k)); C8 (Z_to_bv 64 (k_desk k));
      C4 (Z_to_bv 64 (k_a k)); C4 (Z_to_bv 64 (k_b k)); C4 (Z_to_bv 64 (k_c k)); C4 (Z_to_bv 64 (k_delta k))] ++
     [CB 24 (k_bytes k)] ++
     [C8 (Z_to_bv 64 (k_n k)); C4 (Z_to_bv 64 (k_rc k)); CB 32 (k_before k); CB 32 (k_out k);
      C4 (Z_to_bv 64 (k_want_rc k)); CB 24 (k_want k); C8 (Z_to_bv 64 (k_want_len k));
      C4 (Z_to_bv 64 (k_want_key k)); C4 (Z_to_bv 64 (k_want_display k));
      C8 (Z_to_bv 64 (bv_unsigned (e_p e) + c)); C8 (Z_to_bv 64 rem); CB 80 tl]) in H.
  destruct (rw_cells_app_split _ _ _ _ H) as [H1 H23].
  destruct (rw_cells_app_split _ _ _ _ H23) as [H2 H3].
  cbn [cells_size csize Nat.add] in H2, H3.
  replace (bv_unsigned (e_sp e) + -400 + Z.of_nat 56) with (bv_unsigned (e_sp e) + -344) in H2, H3 by lia.
  replace (bv_unsigned (e_sp e) + -344 + Z.of_nat 24) with (bv_unsigned (e_sp e) + -320) in H3 by lia.
  destruct H2 as [[_ B] Wr]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  split; [exact H1 | split; [exact B | split; [exact Wr | exact H3]]].
Qed.

(** The frame back, with owe()'s five want fields and pl[] in the tail. *)
Lemma body_glue : forall e m k c rem wrc W wl wk wd T,
  rw_cells rsegs m (bv_unsigned (e_sp e) + -400)
    [C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0x13f0);
     C4 (Z_to_bv 64 (k_kind k)); CB 4 (k_pad k); C8 (Z_to_bv 64 (k_p k)); C8 (Z_to_bv 64 (k_desk k));
     C4 (Z_to_bv 64 (k_a k)); C4 (Z_to_bv 64 (k_b k)); C4 (Z_to_bv 64 (k_c k)); C4 (Z_to_bv 64 (k_delta k))] ->
  bytes_at rsegs m (bv_unsigned (e_sp e) + -344) (k_bytes k) ->
  wr_at rsegs m (bv_unsigned (e_sp e) + -344) 24 ->
  length (k_bytes k) = 24%nat ->
  rw_cells rsegs m (bv_unsigned (e_sp e) + -320)
    [C8 (Z_to_bv 64 (k_n k)); C4 (Z_to_bv 64 (k_rc k)); CB 32 (k_before k); CB 32 (k_out k);
     C4 (Z_to_bv 64 wrc); CB 24 W; C8 (Z_to_bv 64 wl); C4 (Z_to_bv 64 wk); C4 (Z_to_bv 64 wd);
     C8 (Z_to_bv 64 (bv_unsigned (e_p e) + c)); C8 (Z_to_bv 64 rem); CB 80 T] ->
  rw_cells rsegs m (bv_unsigned (e_sp e) + -400) (body_cells e (set_owe k wrc W wl wk wd) c rem T).
Proof.
  intros e m k c rem wrc W wl wk wd T H1 B Wr HL H3.
  change (body_cells e (set_owe k wrc W wl wk wd) c rem T) with
    ([C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0x13f0);
      C4 (Z_to_bv 64 (k_kind k)); CB 4 (k_pad k); C8 (Z_to_bv 64 (k_p k)); C8 (Z_to_bv 64 (k_desk k));
      C4 (Z_to_bv 64 (k_a k)); C4 (Z_to_bv 64 (k_b k)); C4 (Z_to_bv 64 (k_c k)); C4 (Z_to_bv 64 (k_delta k))] ++
     [CB 24 (k_bytes k)] ++
     [C8 (Z_to_bv 64 (k_n k)); C4 (Z_to_bv 64 (k_rc k)); CB 32 (k_before k); CB 32 (k_out k);
      C4 (Z_to_bv 64 wrc); CB 24 W; C8 (Z_to_bv 64 wl); C4 (Z_to_bv 64 wk); C4 (Z_to_bv 64 wd);
      C8 (Z_to_bv 64 (bv_unsigned (e_p e) + c)); C8 (Z_to_bv 64 rem); CB 80 T]).
  apply rw_cells_app_join; [exact H1|]. cbn [cells_size csize Nat.add].
  replace (bv_unsigned (e_sp e) + -400 + Z.of_nat 56) with (bv_unsigned (e_sp e) + -344) by lia.
  apply rw_cells_app_join.
  - split; [split; [cbn [cells_wf cell_wf]; split; [exact HL | exact I] |] | exact Wr].
    cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B.
  - cbn [cells_size csize Nat.add].
    replace (bv_unsigned (e_sp e) + -344 + Z.of_nat 24) with (bv_unsigned (e_sp e) + -320) by lia.
    exact H3.
Qed.

(** ---- cutting one CB cell of a list into pieces ---- *)

Lemma nth_error_cut : forall (cs : list cell) i c, nth_error cs i = Some c -> cs = firstn i cs ++ c :: skipn (S i) cs.
Proof.
  induction cs as [|x cs IH]; intros [|i] c H; cbn in H; try discriminate.
  - injection H as ->. reflexivity.
  - cbn [firstn skipn app]. f_equal. apply IH. exact H.
Qed.

Lemma rw_cells_split_at : forall m A cs i n junk sizes,
  nth_error cs i = Some (CB n junk) -> sum_nat sizes = n ->
  rw_cells rsegs m A cs -> rw_cells rsegs m A (firstn i cs ++ mk_CB_cells sizes junk ++ skipn (S i) cs).
Proof.
  intros m A cs i n junk sizes Hn Hs H.
  apply (rw_cells_split_CB rsegs m A (firstn i cs) n junk (skipn (S i) cs) sizes); [| exact Hs].
  rewrite <- (nth_error_cut cs i (CB n junk) Hn). exact H.
Qed.

(** ---- seven_bit byte by byte ---- *)

Lemma nth_zb : forall bs j, nth j (zb bs) 0 = bv_unsigned (nth j bs (b8 0)).
Proof. intros bs j. unfold zb. exact (map_nth (fun b : byte => bv_unsigned b) bs (b8 0) j). Qed.

Lemma nth_firstn_lt : forall (l : list Z) n j d, (j < n)%nat -> nth j (firstn n l) d = nth j l d.
Proof.
  induction l as [|x l IH]; intros n j d H; destruct n as [|n]; destruct j as [|j]; cbn; try reflexivity; try lia.
  apply IH. lia.
Qed.

Lemma seven_bit_firstn_false : forall l n j, (j < n)%nat -> (j < length l)%nat ->
  Z.testbit (nth j l 0) 7 = true -> seven_bit (firstn n l) = false.
Proof.
  intros l n j Hjn Hjl H. unfold seven_bit. apply not_true_iff_false. intro F.
  rewrite forallb_forall in F.
  assert (I : In (nth j l 0) (firstn n l)).
  { rewrite <- (nth_firstn_lt l n j 0 Hjn). apply nth_In. rewrite length_firstn. lia. }
  specialize (F _ I). rewrite H in F. discriminate F.
Qed.

Lemma seven_bit_firstn_true : forall l n, (n <= length l)%nat ->
  (forall j, (j < n)%nat -> Z.testbit (nth j l 0) 7 = false) -> seven_bit (firstn n l) = true.
Proof.
  intros l n Hn H. unfold seven_bit. apply forallb_forall. intros x Hx.
  apply In_nth with (d := 0) in Hx. destruct Hx as (j & Hj & <-).
  rewrite length_firstn in Hj. rewrite nth_firstn_lt by lia. rewrite H by lia. reflexivity.
Qed.

Lemma testbit7 : forall x, 0 <= x < 256 -> Z.testbit x 7 = (128 <=? x).
Proof.
  intros x H. apply Bool.eqb_prop.
  refine (zall_range (fun y => Bool.eqb (Z.testbit y 7) (128 <=? y)) 0 256 _ x H).
  vm_compute. reflexivity.
Qed.

(** The bytes of the record as the spec reads them, back as bytes. *)
Lemma bz_zb : forall bs, bz (zb bs) = bs.
Proof.
  induction bs as [|x bs IH]; [reflexivity|]. cbn [zb bz map] in *. f_equal; [| exact IH].
  unfold b8. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma bz_firstn_zb : forall n bs, bz (firstn n (zb bs)) = firstn n bs.
Proof. intros n bs. unfold zb. rewrite firstn_map. fold (zb (firstn n bs)). apply bz_zb. Qed.

(** ---- bytes ---- *)

Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. exact R. Qed.

(** bltz on the word lb loads: bit 7 of the byte. *)
Lemma lts_sxb : forall b : byte, bv_lts (sxb b) (Z_to_bv 64 0) = (128 <=? bv_unsigned b).
Proof.
  intros b. pose proof (byte_range b) as R.
  assert (E : b = Z_to_bv 8 (bv_unsigned b)).
  { apply bv_eq. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. unfold bv_modulus. cbn. lia. }
  rewrite E. revert R. generalize (bv_unsigned b). intros x Hx.
  apply Bool.eqb_prop.
  refine (zall_range (fun y => Bool.eqb (bv_lts (sxb (Z_to_bv 8 y)) (Z_to_bv 64 0)) (128 <=? bv_unsigned (Z_to_bv 8 y)))
            0 256 _ x Hx).
  vm_compute. reflexivity.
Qed.

Lemma sb_neg_nth : forall bs (j : nat), (128 <=? bv_unsigned (nth j bs (b8 0))) = true ->
  Z.testbit (nth j (zb bs) 0) 7 = true.
Proof. intros bs j H. rewrite nth_zb, testbit7 by apply byte_range. exact H. Qed.

Lemma sb_pos_nth : forall bs (j : nat), (128 <=? bv_unsigned (nth j bs (b8 0))) = false ->
  Z.testbit (nth j (zb bs) 0) 7 = false.
Proof. intros bs j H. rewrite nth_zb, testbit7 by apply byte_range. exact H. Qed.

Lemma b8_byte : forall b : byte, b8 (bv_unsigned b) = b.
Proof.
  intros b. unfold b8. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma b8_F7 : b8 (-9) = b8 0xf7.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(** sh of the frame constant 0x13f0: the sysex head F0 13. *)
Lemma le2_f013 : le2 (Z_to_bv 64 5104) = [b8 0xf0; b8 0x13].
Proof. apply bytes_eq_of_unsigned. vm_compute. reflexivity. Qed.

(** lui + or of a byte value: the key. *)
Lemma key_or : forall kind a, 0 <= a < 65536 -> 0 <= kind < 65536 -> KEY kind a = Z.lor a (kind * 65536).
Proof.
  intros kind a Ha Hk. unfold KEY. change 0xffff with (Z.ones 16). rewrite Z.land_ones by lia.
  rewrite (Z.mod_small a) by lia. apply Z.lor_comm.
Qed.

(** ---- gluing a memcpy target back ---- *)

Lemma rw_cells_join3n : forall m A cs1 n bs cs3 B C,
  rw_cells rsegs m A cs1 -> rw_cells rsegs m B [CB n bs] -> rw_cells rsegs m C cs3 ->
  B = A + Z.of_nat (cells_size cs1) -> C = B + Z.of_nat n ->
  rw_cells rsegs m A (cs1 ++ CB n bs :: cs3).
Proof. intros m A cs1 n bs cs3 B C H1 H2 H3 -> ->. apply rw_cells_join3; assumption. Qed.

(** The prefix of k.bytes a copy reads. *)
Lemma bytes_at_firstn : forall m A bs n, bytes_at rsegs m A bs -> bytes_at rsegs m A (firstn n bs).
Proof.
  intros m A bs n H. rewrite <- (firstn_skipn n bs) in H. apply bytes_at_app in H. exact (proj1 H).
Qed.
