(** Segment OWE10 (the COUNTER case of owe()) of the walk of LLVMFuzzerTestOneInput in the UBSan
    image: the range test, the seven_bit loop, the pl[] buffer with its reverse copy loop, the
    inlined owe_sysex with its memcpy, and the want_key store. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes Arr.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_agree.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells codec_img memcpy_c
  codec_main_inv codec_main_lib.
Import ListNotations.
Open Scope Z_scope.

Local Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  end.

Ltac zc G := zify_cond G; repeat (rewrite Z.mod_small in G by lia).

(** ---- list and byte facts ---- *)

Lemma firstn_S_nth : forall (A : Type) (l : list A) j d, (j < length l)%nat ->
  firstn (S j) l = firstn j l ++ [nth j l d].
Proof.
  intros A l. induction l as [|x l IH]; intros j d H; cbn in H; [lia|].
  destruct j as [|j]; [reflexivity|]. cbn [firstn nth app]. rewrite (IH j d) by lia. reflexivity.
Qed.

Lemma nth_firstn_lt : forall (A : Type) (l : list A) n i d, (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
  intros A l. induction l as [|x l IH]; intros n i d H.
  - rewrite firstn_nil. destruct i; reflexivity.
  - destruct n as [|n]; [lia|]. destruct i as [|i]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.

Lemma upd_mid : forall (A : Type) (l1 l2 : list A) x y, upd (l1 ++ x :: l2) (length l1) y = l1 ++ y :: l2.
Proof. intros A l1. induction l1 as [|z l1 IH]; intros l2 x y; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

Lemma seven_bit_snoc : forall l x, seven_bit (l ++ [x]) = seven_bit l && negb (Z.testbit x 7).
Proof. intros l x. unfold seven_bit. rewrite forallb_app. cbn [forallb]. rewrite andb_true_r. reflexivity. Qed.

Lemma In_nth_firstn : forall (l : list Z) j n d, (j < n)%nat -> (j < length l)%nat -> In (nth j l d) (firstn n l).
Proof.
  induction l as [|x l IH]; intros j n d Hn Hl; cbn in Hl; [lia|].
  destruct n as [|n]; [lia|]. destruct j as [|j]; cbn [firstn nth]; [left; reflexivity | right; apply IH; lia].
Qed.

Lemma seven_bit_bad : forall l j, (j < 8)%nat -> (j < length l)%nat -> Z.testbit (nth j l 0) 7 = true ->
  seven_bit (firstn 8 l) = false.
Proof.
  intros l j Hj Hl Ht. destruct (seven_bit (firstn 8 l)) eqn:E; [|reflexivity].
  unfold seven_bit in E. rewrite forallb_forall in E. specialize (E _ (In_nth_firstn l j 8 0 Hj Hl)).
  rewrite Ht in E. discriminate E.
Qed.

Lemma zb_nth : forall l j, nth j (zb l) 0 = bv_unsigned (nth j l (Z_to_bv 8 0)).
Proof. intros l j. exact (map_nth (fun b : byte => bv_unsigned b) l (Z_to_bv 8 0) j). Qed.

Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. exact H. Qed.

Lemma b8_unsigned : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma b8_zxb : forall x, 0 <= x < 256 -> Z_to_bv 8 (bv_unsigned (zxb (Z_to_bv 8 x))) = b8 x.
Proof.
  intros x Hx. unfold zxb. pose proof (byte_range (Z_to_bv 8 x)). rewrite unsigned_lit by lia.
  apply b8_unsigned.
Qed.

Lemma b8_lit64 : forall x, 0 <= x < 2 ^ 64 -> Z_to_bv 8 (bv_unsigned (Z_to_bv 64 x)) = b8 x.
Proof. intros x Hx. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma le1_zxb : forall b : byte, le1 (zxb b) = [b].
Proof.
  intros b. unfold le1, zxb. pose proof (byte_range b).
  rewrite unsigned_lit by lia. cbn [Z_to_le_bytes]. rewrite b8_unsigned. reflexivity.
Qed.

Lemma b8_u8 : forall x, b8 (u8 x) = b8 x.
Proof.
  intros x. unfold b8, u8. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  replace (bv_modulus 8) with 256 by reflexivity. apply Z.mod_mod. lia.
Qed.

Lemma bz_zb : forall l, bz (zb l) = l.
Proof.
  intros l. unfold bz, zb. rewrite map_map. rewrite <- (map_id l) at 2. apply map_ext.
  intros b. unfold b8. apply b8_unsigned.
Qed.

Lemma sxb_lts0 : forall b : byte, bv_lts (sxb b) (Z_to_bv 64 0) = Z.testbit (bv_unsigned b) 7.
Proof.
  intros b. rewrite bv_lts_zero_r. unfold sxb. pose proof (byte_range b) as Hb.
  rewrite tb7_byte by lia. rewrite unsigned_lit_wrap.
  unfold bv_signed, bv_swrap, bv_wrap.
  replace (bv_half_modulus 8) with 128 by reflexivity. replace (bv_modulus 8) with 256 by reflexivity.
  change (2 ^ 64) with 18446744073709551616. change (2 ^ 63) with 9223372036854775808.
  remember (bv_unsigned b) as u eqn:Eu. clear Eu.
  destruct (Z.ltb_spec 127 u) as [H|H].
  - rewrite <- (Z.mod_unique (u + 128) 256 1 (u - 128)) by lia.
    rewrite <- (Z.mod_unique (u - 128 - 128) 18446744073709551616 (-1) (u - 256 + 18446744073709551616)) by lia.
    apply Z.leb_le. lia.
  - rewrite (Z.mod_small (u + 128) 256) by lia.
    rewrite (Z.mod_small (u + 128 - 128) 18446744073709551616) by lia.
    apply Z.leb_gt. lia.
Qed.

Lemma firstn_len_app : forall (X : Type) (A B : list X) n, length A = n -> firstn n (A ++ B) = A.
Proof. intros X A B n <-. apply firstn_app_exact. Qed.

Lemma bz_rev_zb : forall bs, bz (rev (firstn 8 (zb bs))) = rev (firstn 8 bs).
Proof.
  intros bs. unfold bz, zb. rewrite map_rev, firstn_map, map_map. f_equal.
  rewrite <- (map_id (firstn 8 bs)) at 2. apply map_ext. intros b. unfold b8. apply b8_unsigned.
Qed.

Lemma bytes_eq_map : forall xs ys : list byte, map bv_unsigned xs = map bv_unsigned ys -> xs = ys.
Proof.
  induction xs as [|x xs IH]; intros [|y ys] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

(** The 15 bytes the inlined owe_sysex leaves in want[] (fuzz_codec.c:103-108). *)
Lemma want10 : forall (dv cv bv : Z) (c0 c1 z0 : byte) (bs Y : list byte),
  0 <= dv < 256 -> 0 <= bv < 256 -> length bs = 24%nat -> c0 = b8 cv -> c1 = b8 bv ->
  firstn 15 (cells_bytes [C2 (Z_to_bv 64 5104); C1 (Z_to_bv 8 (bv_unsigned (zxb (Z_to_bv 8 dv))));
                          C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 48)));
                          CB 10 ([c0; c1] ++ firstn 8 (rev (firstn 8 bs)) ++ repeat z0 (8 - 8));
                          C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-9)))); CB 9 Y])
  = bz ([0xf0; 0x13; u8 dv; u8 0x30] ++ ([cv; u8 bv] ++ rev (firstn 8 (zb bs))) ++ [0xf7]).
Proof.
  intros dv cv bv c0 c1 z0 bs Y Hdv Hbv Hl -> ->.
  cbn [cells_bytes cbytes repeat Nat.sub]. rewrite !app_nil_r.
  replace (le2 (Z_to_bv 64 5104)) with [b8 0xf0; b8 0x13] by (apply bytes_eq_map; vm_compute; reflexivity).
  rewrite b8_zxb by lia.
  replace (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 48))) with (b8 0x30) by (apply bv_eq; vm_compute; reflexivity).
  replace (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-9)))) with (b8 0xf7) by (apply bv_eq; vm_compute; reflexivity).
  assert (LF : length (rev (firstn 8 bs)) = 8%nat) by (rewrite length_rev, length_firstn; lia).
  rewrite (firstn_all2 (rev (firstn 8 bs))) by lia.
  rewrite !app_assoc. rewrite firstn_len_app by (rewrite !length_app, LF; reflexivity).
  unfold bz at 1. rewrite !map_app. fold (bz (rev (firstn 8 (zb bs)))). rewrite bz_rev_zb.
  cbn [map]. rewrite !b8_u8. rewrite <- !app_assoc. reflexivity.
Qed.

(** ---- the record ---- *)

Lemma desk10 : forall k, desk_at k -> k_desk k <> 0 ->
  exists d, od_of k = Some d /\ ((k_desk k = SDESK_C24 /\ d = c24) \/ (k_desk k = SDESK_PC /\ d = pc)).
Proof.
  intros k [[_ E]|[[_ E]|[_ E]]] H; [contradiction | exists c24 | exists pc];
    (split; [unfold od_of; rewrite E; reflexivity | auto]).
Qed.

Lemma desk_rd : forall m2 k d, relro_img m2 ->
  ((k_desk k = SDESK_C24 /\ d = c24) \/ (k_desk k = SDESK_PC /\ d = pc)) ->
  ov_read_bytes rsegs m2 (Z_to_bv 64 (k_desk k + 8)) 1 = Some [Z_to_bv 8 (d_dev d)] /\
  ov_read_bytes rsegs m2 (Z_to_bv 64 (k_desk k + 11)) 1 = Some [Z_to_bv 8 (d_counter d)].
Proof.
  intros m2 k d HR [[E ->] | [E ->]]; rewrite E; unfold SDESK_C24, SDESK_PC.
  - pose proof (codec_SPEC_C24_at m2 HR) as DK. unfold codec_SPEC_C24_cells in DK. split.
    + exact (ro_cells_read_at rsegs m2 0x1f690 _ 8 (C1 (Z_to_bv 8 1)) 1 _ DK eq_refl eq_refl eq_refl).
    + exact (ro_cells_read_at rsegs m2 0x1f690 _ 11 (C1 (Z_to_bv 8 0x19)) 1 _ DK eq_refl eq_refl eq_refl).
  - pose proof (codec_SPEC_PC_at m2 HR) as DK. unfold codec_SPEC_PC_cells in DK. split.
    + exact (ro_cells_read_at rsegs m2 0x1f6a0 _ 8 (C1 (Z_to_bv 8 0)) 1 _ DK eq_refl eq_refl eq_refl).
    + exact (ro_cells_read_at rsegs m2 0x1f6a0 _ 11 (C1 (Z_to_bv 8 9)) 1 _ DK eq_refl eq_refl eq_refl).
Qed.

Lemma owe_k10 : forall k d, k_kind k = 10 -> od_of k = Some d ->
  owe_k k = if (0x7f <? k_b k) || negb (seven_bit (firstn 8 (zb (k_bytes k)))) then (E_RANGE, noc)
            else (0, ([0xf0; 0x13; u8 (d_dev d); u8 0x30] ++
                      ([d_counter d; u8 (k_b k)] ++ rev (firstn 8 (zb (k_bytes k)))) ++ [0xf7],
                      KEY 6 (d_counter d), 1)).
Proof. intros k d HK HO. unfold owe_k. rewrite HK, HO. reflexivity. Qed.

Lemma enc_rc10 : forall k d, rec_wf k -> od_of k = Some d -> (d = c24 \/ d = pc) ->
  fst (enc_k k) = fst (owe_k k).
Proof.
  intros k d (HK & _ & _ & _ & _ & _ & _ & _ & _ & HRD) HO Hd.
  assert (OD : od_ok (od_of k)) by (unfold od_ok; rewrite HO; destruct Hd as [-> | ->]; auto).
  pose proof (agree_all (k_kind k) (od_of k) (k_a k) (k_b k) (k_c k) (k_delta k) (zb (k_bytes k)) (k_n k)
                HK OD HRD) as A.
  unfold agrees in A. revert A. unfold enc_k, owe_k.
  destruct (enc_of_call (k_kind k) (od_of k) (k_a k) (k_b k) (k_c k) (k_delta k) (zb (k_bytes k)) (k_n k))
    as [rc o].
  intros [A _]. cbn [fst]. symmetry. exact A.
Qed.

Lemma desk_range : forall k, desk_at k -> 0 <= k_p k < 2 ^ 64 /\ 0 <= k_desk k < 2 ^ 64.
Proof.
  intros k [[E1 E2]|[[E1 E2]|[E1 E2]]]; rewrite E1, E2; unfold PERS, SDESK_C24, SDESK_PC; lia.
Qed.

Ltac kproj := cbn [with_want_rc with_want_key set_want k_run with_rc with_out
                   k_kind k_pad k_p k_desk k_a k_b k_c k_delta k_bytes k_n k_rc k_before k_out k_want_rc k_want
                   k_want_len k_want_key k_want_display].

Lemma chk_wf_err : forall k d, rec_wf k -> k_kind k = 10 -> od_of k = Some d -> (d = c24 \/ d = pc) ->
  (0x7f < k_b k \/ seven_bit (firstn 8 (zb (k_bytes k))) = false) ->
  chk_wf (with_want_rc (k_run k) E_RANGE).
Proof.
  intros k d WF HK HO Hd Hbad.
  pose proof WF as (HK' & HDA & HBF & HOUT & HRC0 & HWRC0 & HWL0 & HWK0 & HWD0 & HRD).
  assert (OW : owe_k k = (E_RANGE, noc)).
  { rewrite (owe_k10 k d HK HO). destruct Hbad as [Hb | Hs].
    - replace (0x7f <? k_b k) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
    - rewrite Hs. rewrite orb_true_r. reflexivity. }
  pose proof (enc_rc10 k d WF HO Hd) as EC. rewrite OW in EC. cbn [fst] in EC.
  assert (E1 : enc_k (with_want_rc (k_run k) E_RANGE) = enc_k k) by reflexivity.
  assert (E2 : owe_k (with_want_rc (k_run k) E_RANGE) = owe_k k) by reflexivity.
  unfold chk_wf. rewrite E1, E2, OW. kproj.
  pose proof (desk_range k HDA) as [Rp Rd].
  pose proof HRD as (Ra & Rb & Rc & Rdl & _ & _ & Rn & _).
  split; [lia|]. split; [exact HDA|]. split.
  { unfold kcall_wf. kproj. rewrite HK, EC, HWL0, HWK0, HWD0. unfold E_RANGE. lia. }
  split; [exact HBF|]. split; [exact HRD|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. cbn [fst]. unfold E_RANGE. intros H. discriminate H.
Qed.

Lemma chk_wf_ok : forall k d W, rec_wf k -> k_kind k = 10 -> od_of k = Some d -> (d = c24 \/ d = pc) ->
  k_b k <= 0x7f -> seven_bit (firstn 8 (zb (k_bytes k))) = true ->
  firstn 15 W = bz ([0xf0; 0x13; u8 (d_dev d); u8 0x30] ++
                    ([d_counter d; u8 (k_b k)] ++ rev (firstn 8 (zb (k_bytes k)))) ++ [0xf7]) ->
  chk_wf (with_want_key (set_want (k_run k) W 15 1) (KEY 6 (d_counter d))).
Proof.
  intros k d W WF HK HO Hd Hb H7 HW.
  pose proof WF as (HK' & HDA & HBF & HOUT & HRC0 & HWRC0 & HWL0 & HWK0 & HWD0 & HRD).
  pose proof HRD as (Ra & Rb & Rc & Rdl & Rlen & _ & Rn & _).
  assert (OW : owe_k k = (0, ([0xf0; 0x13; u8 (d_dev d); u8 0x30] ++
                      ([d_counter d; u8 (k_b k)] ++ rev (firstn 8 (zb (k_bytes k)))) ++ [0xf7],
                      KEY 6 (d_counter d), 1))).
  { rewrite (owe_k10 k d HK HO).
    replace (0x7f <? k_b k) with false by (symmetry; apply Z.ltb_ge; lia). rewrite H7. reflexivity. }
  pose proof (enc_rc10 k d WF HO Hd) as EC. rewrite OW in EC. cbn [fst] in EC.
  assert (E1 : enc_k (with_want_key (set_want (k_run k) W 15 1) (KEY 6 (d_counter d))) = enc_k k)
    by reflexivity.
  assert (E2 : owe_k (with_want_key (set_want (k_run k) W 15 1) (KEY 6 (d_counter d))) = owe_k k)
    by reflexivity.
  assert (LW : length ([0xf0; 0x13; u8 (d_dev d); u8 0x30] ++
                      ([d_counter d; u8 (k_b k)] ++ rev (firstn 8 (zb (k_bytes k)))) ++ [0xf7]) = 15%nat).
  { rewrite !length_app, length_rev, length_firstn, Rlen. reflexivity. }
  assert (KR : 0 <= KEY 6 (d_counter d) < 2 ^ 32) by (apply KEY_range; lia).
  unfold chk_wf. rewrite E1, E2, OW. kproj.
  pose proof (desk_range k HDA) as [Rp Rd].
  split; [lia|]. split; [exact HDA|]. split.
  { unfold kcall_wf. kproj. rewrite HK, EC, HWRC0. lia. }
  split; [exact HBF|]. split; [exact HRD|]. split; [reflexivity|]. split; [reflexivity|].
  split; [cbn [fst]; exact HWRC0|]. intros _. cbn [snd]. rewrite LW.
  split; [exact HW|]. split; [reflexivity|]. split; [lia|]. split; reflexivity.
Qed.

(** ---- the frame while owe() writes pl[] ---- *)

Definition fr10 (E : cenv) (m2 : word -> option byte) (kcs : list cell) (cur rem : word)
                (u0 pj tj PL bys : list byte) : Prop :=
  rw_cells rsegs m2 (bv_unsigned (c_sp E) + -416) [CB 8 u0] /\
  rw_cells rsegs m2 (bv_unsigned (c_sp E) + -408)
    [C8 (Z_to_bv 64 0x990); C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0xffff)] /\
  rw_cells rsegs m2 (bv_unsigned (c_sp E) + -384) kcs /\
  rw_cells rsegs m2 (bv_unsigned (c_sp E) + -200) [C8 cur; C8 rem] /\
  rw_cells rsegs m2 (bv_unsigned (c_sp E) + -184) [CB 5 pj] /\
  rw_cells rsegs m2 (bv_unsigned (c_sp E) + -179) [CB 65 tj] /\
  u8arr rsegs m2 (bv_unsigned (c_sp E) + -114) PL /\
  rw_cells rsegs m2 (bv_unsigned (c_sp E) + -104) (saved E) /\
  bytes_at rsegs m2 (bv_unsigned (c_sp E) + -344) bys /\
  stk rsegs m2 (c_lo E) (bv_unsigned (c_sp E) + -416) /\
  munch [(bv_unsigned (c_sp E) - 640, bv_unsigned (c_sp E))] (c_m E) m2 /\
  wmono rsegs (c_m E) m2 /\
  mem_inv rsegs m2.

Lemma fr10_pl_store : forall E m2 kcs cur rem u0 pj tj PL bys (i : Z) (b : byte),
  0 <= c_lo E -> c_lo E + 640 <= bv_unsigned (c_sp E) ->
  cells_size kcs = 184%nat -> length bys = 24%nat -> 0 <= i < Z.of_nat (length PL) -> length PL = 10%nat ->
  fr10 E m2 kcs cur rem u0 pj tj PL bys ->
  fr10 E (write_to_mem m2 (wa (bv_unsigned (c_sp E) + -114 + i)) [b]) kcs cur rem u0 pj tj
       (upd PL (Z.to_nat i) b) bys.
Proof.
  intros E m2 kcs cur rem u0 pj tj PL bys i b HLo HLO HKS HBY Hi HPL
    (F0 & F8 & FK & FIN & FPD & FTX & PLU & FSV & BY & ST & MU & WM & HMI).
  pose proof (bv_unsigned_in_range 64 (c_sp E)) as Rsp. unfold bv_modulus in Rsp.
  rewrite HPL in Hi.
  assert (Ha1 : bv_unsigned (c_sp E) + -114 + i + Z.of_nat (length [b]) <= 2 ^ 64) by (cbn [length]; lia).
  unfold fr10.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))))).
  - apply (rw_cells_frame rsegs); [exact F0 | lia | exact Ha1 | cbn [cells_size csize length Nat.add]; lia].
  - apply (rw_cells_frame rsegs); [exact F8 | lia | exact Ha1 | cbn [cells_size csize length Nat.add]; lia].
  - apply (rw_cells_frame rsegs); [exact FK | lia | exact Ha1 | rewrite HKS; cbn [length]; lia].
  - apply (rw_cells_frame rsegs); [exact FIN | lia | exact Ha1 | cbn [cells_size csize length Nat.add]; lia].
  - apply (rw_cells_frame rsegs); [exact FPD | lia | exact Ha1 | cbn [cells_size csize length Nat.add]; lia].
  - apply (rw_cells_frame rsegs); [exact FTX | lia | exact Ha1 | cbn [cells_size csize length Nat.add]; lia].
  - apply (u8arr_write rsegs); [exact PLU | rewrite HPL; lia].
  - apply (rw_cells_frame rsegs); [exact FSV | lia | exact Ha1 |].
    unfold saved. cbn [cells_size csize length Nat.add]. lia.
  - eapply (bytes_at_write_other rsegs); [exact BY | lia | exact Ha1 | rewrite HBY; cbn [length]; lia].
  - apply (stk_write rsegs); [exact ST | lia | exact Ha1].
  - apply munch_write; [exact MU | lia | exact Ha1 | cbn [inside length]; left; lia].
  - apply (wmono_write rsegs). exact WM.
  - apply (mem_inv_store rsegs); [exact HMI |].
    apply (u8arr_store_ok rsegs m2 (bv_unsigned (c_sp E) + -114) PL i); [exact PLU | rewrite HPL; lia | reflexivity].
Qed.

Lemma pl_len : forall (c0 c1 z0 : byte) bs j, length bs = 24%nat -> (j <= 8)%nat ->
  length ([c0; c1] ++ firstn j (rev (firstn 8 bs)) ++ repeat z0 (8 - j)) = 10%nat.
Proof.
  intros c0 c1 z0 bs j Hl Hj. rewrite !length_app, length_firstn, length_rev, length_firstn, repeat_length.
  cbn [length]. lia.
Qed.

Lemma pl_step : forall (c0 c1 z0 : byte) bs j, length bs = 24%nat -> (j < 8)%nat ->
  upd ([c0; c1] ++ firstn j (rev (firstn 8 bs)) ++ repeat z0 (8 - j)) (Z.to_nat (2 + Z.of_nat j))
      (nth (7 - j) bs (Z_to_bv 8 0)) =
  [c0; c1] ++ firstn (S j) (rev (firstn 8 bs)) ++ repeat z0 (8 - S j).
Proof.
  intros c0 c1 z0 bs j Hl Hj.
  assert (LF : length (rev (firstn 8 bs)) = 8%nat) by (rewrite length_rev, length_firstn; lia).
  replace (Z.to_nat (2 + Z.of_nat j)) with (length ([c0; c1] ++ firstn j (rev (firstn 8 bs))))
    by (rewrite length_app, length_firstn, LF; cbn [length]; lia).
  replace (8 - j)%nat with (S (8 - S j)) by lia. cbn [repeat].
  rewrite app_assoc, upd_mid, <- app_assoc.
  rewrite (firstn_S_nth _ (rev (firstn 8 bs)) j (Z_to_bv 8 0)) by lia.
  rewrite rev_nth by (rewrite length_firstn; lia). rewrite length_firstn.
  replace (Nat.min 8 (length bs) - S j)%nat with (7 - j)%nat by lia.
  rewrite nth_firstn_lt by lia. rewrite <- app_assoc. reflexivity.
Qed.

Lemma rw_cells_pick : forall m A cs (i : nat), rw_cells rsegs m A cs ->
  rw_cells rsegs m A (firstn i cs) /\ rw_cells rsegs m (A + Z.of_nat (cells_size (firstn i cs))) (skipn i cs).
Proof. intros m A cs i H. apply rw_cells_app_split. rewrite firstn_skipn. exact H. Qed.

Ltac unfold_kc H :=
  unfold kcall_cells, k_run, with_rc, with_out in H;
  cbn [k_kind k_pad k_p k_desk k_a k_b k_c k_delta k_bytes k_n k_rc k_before k_out k_want_rc k_want
       k_want_len k_want_key k_want_display] in H.

(** ---- the machine state of the segment ---- *)

Definition st10 (E : cenv) (ra' t0' t1' t2' a0 a1 a2 a3 a4 a5 a6 a7 s5' s7' t3' t4' t5' t6' : word)
  (ops pcv : Z) (m1 : word -> option byte) : machine_state :=
  MS (mkR ra' (Z_to_bv 64 (bv_unsigned (c_sp E) + -416)) (c_gp E) (c_tp E) t0' t1' t2'
          (Z_to_bv 64 (bv_unsigned (c_sp E) + -308)) (Z_to_bv 64 0x1f678)
          a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 0x104d4) (Z_to_bv 64 254) (Z_to_bv 64 18446744073709422983)
          s5' (Z_to_bv 64 ops) s7' (Z_to_bv 64 (bv_unsigned (c_sp E) + -216)) (Z_to_bv 64 1)
          (Z_to_bv 64 18446744073709484843) (Z_to_bv 64 10) t3' t4' t5' t6')
     (c_F E) (Z_to_bv 64 pcv) (c_fc E) None m1 (seg_rom rsegs).

Lemma codec_main_owe10 : seg_owe10_stmt.
Proof.
  unfold seg_owe10_stmt.
  intros E n ENV MEMCPY CHK k WF K10.
  unfold owe_ok.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' s5' t3' t4' t5' t6' cur rem u0 pj tj plj c ops m1
    _ ND HN HOPS HCUR HC0 HREM FR ST MU WM HMI.
  destruct (ND ltac:(rewrite K10; reflexivity)) as [-> HD0]. clear ND.
  rewrite K10. change (pc_owe 10) with 0x14928.
  pose proof (bv_unsigned_in_range 64 (c_sp E)) as Rsp. unfold bv_modulus in Rsp.
  pose proof ENV as (_ & _ & _ & HLO & _).
  pose proof ST as (Hlo0 & _).
  unfold fr in FR. destruct FR as (HS & F0 & F8 & FK & FIN & FPD & FTX & FPL & FSV).
  pose proof WF as (HK & HDA & HBF & HOUT & HRC0 & HWRC0 & HWL0 & HWK0 & HWD0 & HRD).
  pose proof HRD as (Ra & Rb & Rc & Rd & Rlen & Rby & Rn & _ & R10 & _).
  specialize (R10 K10).
  assert (LBY : length (k_bytes k) = 24%nat) by (unfold zb in Rlen; rewrite length_map in Rlen; exact Rlen).
  destruct (desk10 k HDA HD0) as (d & HOD & HDK).
  assert (Hd : d = c24 \/ d = pc) by (destruct HDK as [[_ ->] | [_ ->]]; auto).
  assert (HDV : 0 <= d_dev d < 128 /\ 0 <= d_counter d < 128) by (destruct Hd as [-> | ->]; cbn; lia).
  assert (LAND7 : Z.land (k_desk k) 7 = 0) by (destruct HDK as [[-> _] | [-> _]]; reflexivity).
  assert (KDR : 0 <= k_desk k < 2 ^ 63) by (destruct HDK as [[-> _] | [-> _]]; unfold SDESK_C24, SDESK_PC; lia).
  assert (UDK : bv_unsigned (Z_to_bv 64 (k_desk k)) = k_desk k) by (apply unsigned_lit; lia).
  assert (BY : bytes_at rsegs m1 (bv_unsigned (c_sp E) + -344) (k_bytes k)).
  { unfold_kc FK. pose proof (rw_cells_pick _ _ _ 8 FK) as [_ X]. cbn [firstn skipn cells_size csize Nat.add] in X.
    apply rw_cells_app_split with (cs1 := [CB 24 (k_bytes k)]) in X. destruct X as [X _].
    apply rw_cells_bytes_at in X. replace (bv_unsigned (c_sp E) + -344) with (bv_unsigned (c_sp E) + -384 + Z.of_nat 40) by lia.
    exact X. }
  (* 0x14a2c-0x14a30: want_rc = E_RANGE, then the checks *)
  assert (ERANGE : forall a0v a1v a2v a3v a4v,
    (0x7f < k_b k \/ seven_bit (firstn 8 (zb (k_bytes k))) = false) ->
    evt rsegs (Qk E) (st10 E ra' t0' t1' t2' a0v a1v a2v a3v a4v a5' a6'
      (Z_to_bv 64 (bv_unsigned (c_sp E) + -114)) s5' (Z_to_bv 64 (k_desk k)) t3' t4' t5' t6' ops 0x14a2c m1)).
  { intros a0v a1v a2v a3v a4v Hbad. unfold_kc FK. clear BY. unfold st10. step. step.
    eapply (CHK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (with_want_rc (k_run k) E_RANGE) cur rem u0 pj tj plj c ops);
      [ exact (chk_wf_err k d WF K10 HOD Hd Hbad) | exact HN | exact HOPS | exact HCUR | exact HC0 | exact HREM
      | | eassumption | eassumption | eassumption | eassumption ].
    exact (conj (kcall_cells_size _) (conj F0 (conj F8 (conj FK (conj FIN (conj FPD (conj FTX (conj FPL FSV)))))))). }
  (* 0x149ac-0x14a08: owe_sysex inlined, its memcpy, want_key, then the checks *)
  assert (POST2 : forall (c0 c1 z0 : byte), c0 = b8 (d_counter d) -> c1 = b8 (k_b k) ->
    k_b k <= 0x7f -> seven_bit (firstn 8 (zb (k_bytes k))) = true ->
    forall (m2 : word -> option byte) (a0v a1v a2v a4v : word),
    fr10 E m2 (kcall_cells (k_run k)) cur rem u0 pj tj
      ([c0; c1] ++ firstn 8 (rev (firstn 8 (k_bytes k))) ++ repeat z0 (8 - 8)) (k_bytes k) ->
    evt rsegs (Qk E) (st10 E ra' t0' t1' t2' a0v a1v a2v (Z_to_bv 64 (bv_unsigned (c_sp E) + -104)) a4v a5' a6'
      (Z_to_bv 64 (bv_unsigned (c_sp E) + -114)) s5' (Z_to_bv 64 (k_desk k)) t3' t4' t5' t6' ops 0x149ac m2)).
  { intros c0 c1 z0 Ec0 Ec1 Hb H7 m2 a0v a1v a2v a4v FR2.
    destruct FR2 as (F0' & F8' & FK' & FIN' & FPD' & FTX' & PLU & FSV' & BY' & ST' & MU' & WM' & HMI').
    unfold_kc FK'.
    pose proof (desk_rd m2 k d (relro_at E m2 ENV MU') HDK) as [HRD2 _].
    unfold st10. step. clear HRD2.
    step. step. step. step. step. step.
    step. step. step. step.
    lazymatch type of FK' with rw_cells _ ?mm ?A ?cs => split_for_access FK' rsegs mm A cs 148%nat 10%nat end.
    destruct (rw_cells_pick _ _ _ 17 FK') as [FKa FKr].
    cbn [firstn skipn cells_size csize Nat.add] in FKa, FKr.
    destruct (rw_cells_pick _ _ _ 1 FKr) as [FKj FKc].
    cbn [firstn skipn cells_size csize Nat.add] in FKj, FKc.
    replace (bv_unsigned (c_sp E) + -384 + Z.of_nat 148) with (bv_unsigned (c_sp E) + -236) in FKj, FKc by lia.
    replace (bv_unsigned (c_sp E) + -236 + Z.of_nat 10) with (bv_unsigned (c_sp E) + -226) in FKc by lia.
    clear FK' FKr.
    assert (U236 : bv_unsigned (Z_to_bv 64 (bv_unsigned (c_sp E) + -236)) = bv_unsigned (c_sp E) + -236)
      by (apply unsigned_lit; lia).
    assert (U114 : bv_unsigned (Z_to_bv 64 (bv_unsigned (c_sp E) + -114)) = bv_unsigned (c_sp E) + -114)
      by (apply unsigned_lit; lia).
    assert (U10 : bv_unsigned (Z_to_bv 64 10) = 10) by reflexivity.
    assert (LPLF : length ([c0; c1] ++ firstn 8 (rev (firstn 8 (k_bytes k))) ++ repeat z0 (8 - 8)) = 10%nat)
      by (apply pl_len; lia).
    lazymatch type of FKj with rw_cells _ _ _ [CB _ ?junk] =>
      call (MEMCPY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              ([c0; c1] ++ firstn 8 (rev (firstn 8 (k_bytes k))) ++ repeat z0 (8 - 8)) junk) end.
    1: (rewrite U114; exact (proj1 PLU)).
    1: (rewrite U10; exact LPLF).
    1: (rewrite U236, U10; exact FKj).
    1: (rewrite U236, U114, U10; lia).
    1: assumption.
    match goal with H : rw_cells _ _ (bv_unsigned (Z_to_bv 64 _)) _ |- _ => rename H into FKj end.
    rewrite U236, U10 in FKj. change (Z.to_nat 10) with 10%nat in FKj.
    step. step. step.
    if_cases T; [refute_trap T|].
    step. step. step. step. step.
    pose proof (desk_rd _ k d (relro_at E _ ENV MU') HDK) as [_ HRC2].
    step. clear HRC2.
    step. step. step. step.
    replace (bv_unsigned (c_sp E) + -226) with (bv_unsigned (c_sp E) + -236 + Z.of_nat 10) in FKc by lia.
    pose proof (rw_cells_app_join _ _ _ _ FKj FKc) as J2.
    replace (bv_unsigned (c_sp E) + -236) with (bv_unsigned (c_sp E) + -384 + Z.of_nat 148) in J2 by lia.
    pose proof (rw_cells_app_join _ _ _ _ FKa J2) as J. clear FKa FKj FKc J2.
    cbn [app] in J.
    lazymatch type of J with rw_cells _ ?mm ?A ?l =>
      let pre := eval cbn [firstn] in (firstn 14 l) in
      let mid := eval cbn [firstn skipn] in (firstn 6 (skipn 14 l)) in
      let post := eval cbn [skipn] in (skipn 20 l) in
      pose proof (rw_cells_merge rsegs mm A pre mid post J) as J' end.
    clear J. cbn [app cells_size csize Nat.add] in J'.
    replace (Z.lor (bv_unsigned (zxb (Z_to_bv 8 (d_counter d)))) 393216) with (KEY 6 (d_counter d)) in J'
      by (destruct Hd as [-> | ->]; reflexivity).
    pose proof (rw_cells_of_u8arr rsegs _ _ _ PLU) as PLR. rewrite LPLF in PLR.
    lazymatch type of J' with context [CB 24 (cells_bytes ?mid)] =>
      eapply (CHK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                (with_want_key (set_want (k_run k) (cells_bytes mid) 15 1) (KEY 6 (d_counter d)))
                cur rem u0 pj tj _ c ops) end;
      [ | exact HN | exact HOPS | exact HCUR | exact HC0 | exact HREM | | eassumption | eassumption
      | eassumption | eassumption ].
    - apply (chk_wf_ok k d _ WF K10 HOD Hd Hb H7).
      apply (want10 (d_dev d) (d_counter d) (k_b k)); [lia | lia | exact LBY | exact Ec0 | exact Ec1].
    - exact (conj (kcall_cells_size _) (conj F0' (conj F8' (conj J' (conj FIN' (conj FPD' (conj FTX'
               (conj PLR FSV')))))))). }
  (* 0x14998-0x149a8: the reverse copy loop, pl[2 + j] = k.bytes[7 - j] *)
  assert (LOOP2 : forall (c0 c1 z0 : byte),
    (forall m2 a0v a1v a2v a4v,
       fr10 E m2 (kcall_cells (k_run k)) cur rem u0 pj tj
         ([c0; c1] ++ firstn 8 (rev (firstn 8 (k_bytes k))) ++ repeat z0 (8 - 8)) (k_bytes k) ->
       evt rsegs (Qk E) (st10 E ra' t0' t1' t2' a0v a1v a2v (Z_to_bv 64 (bv_unsigned (c_sp E) + -104)) a4v a5' a6'
         (Z_to_bv 64 (bv_unsigned (c_sp E) + -114)) s5' (Z_to_bv 64 (k_desk k)) t3' t4' t5' t6' ops 0x149ac m2)) ->
    forall (dd j : nat) m2 a0v a1v a2v a4v, dd = (8 - j)%nat -> (j < 8)%nat ->
    bv_unsigned a0v = bv_unsigned (c_sp E) + -337 - Z.of_nat j ->
    bv_unsigned a1v = bv_unsigned (c_sp E) + -112 + Z.of_nat j ->
    fr10 E m2 (kcall_cells (k_run k)) cur rem u0 pj tj
      ([c0; c1] ++ firstn j (rev (firstn 8 (k_bytes k))) ++ repeat z0 (8 - j)) (k_bytes k) ->
    evt rsegs (Qk E) (st10 E ra' t0' t1' t2' a0v a1v a2v (Z_to_bv 64 (bv_unsigned (c_sp E) + -104)) a4v a5' a6'
      (Z_to_bv 64 (bv_unsigned (c_sp E) + -114)) s5' (Z_to_bv 64 (k_desk k)) t3' t4' t5' t6' ops 0x14998 m2)).
  { intros c0 c1 z0 K dd. induction dd as [|dd IH]; intros j m2 a0v a1v a2v a4v Hdd Hj HA0 HA1 FR2; [lia|].
    pose proof FR2 as (_ & _ & _ & _ & _ & _ & PLU & _ & BY2 & _).
    pose proof (bytes_at_byte m2 (bv_unsigned (c_sp E) + -344) (k_bytes k) (Z.of_nat (7 - j)) BY2
                  ltac:(rewrite LBY; lia)) as HR.
    rewrite Nat2Z.id in HR.
    rewrite (wa_of_var a0v (bv_unsigned (c_sp E) + -344 + Z.of_nat (7 - j)) ltac:(lia)) in HR.
    assert (HSO : store_ok rsegs m2 a1v 1 = true).
    { apply (u8arr_store_ok rsegs m2 (bv_unsigned (c_sp E) + -114)
               ([c0; c1] ++ firstn j (rev (firstn 8 (k_bytes k))) ++ repeat z0 (8 - j)) (2 + Z.of_nat j));
        [exact PLU | rewrite pl_len by lia; lia | symmetry; apply wa_of_var; lia]. }
    clear PLU BY2.
    unfold st10. step. step.
    replace (write_to_mem m2 a1v (le1 (zxb (nth (7 - j) (k_bytes k) (Z_to_bv 8 0)))))
      with (write_to_mem m2 (wa (bv_unsigned (c_sp E) + -114 + (2 + Z.of_nat j)))
              [nth (7 - j) (k_bytes k) (Z_to_bv 8 0)])
      by (rewrite le1_zxb; f_equal; apply wa_of_var; lia).
    assert (FR3 : fr10 E (write_to_mem m2 (wa (bv_unsigned (c_sp E) + -114 + (2 + Z.of_nat j)))
                            [nth (7 - j) (k_bytes k) (Z_to_bv 8 0)])
                    (kcall_cells (k_run k)) cur rem u0 pj tj
                    ([c0; c1] ++ firstn (S j) (rev (firstn 8 (k_bytes k))) ++ repeat z0 (8 - S j)) (k_bytes k)).
    { rewrite <- pl_step by lia.
      apply fr10_pl_store; [lia | lia | apply kcall_cells_size | exact LBY | rewrite pl_len by lia; lia
        | apply pl_len; lia | exact FR2]. }
    step. step. step.
    if_cases G.
    - zc G.
      eapply (IH (S j)); [lia | lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | exact FR3].
    - zc G. assert (j = 7)%nat by lia. subst j. apply K. exact FR3. }
  (* 0x14950-0x14994: the alignment trap, pl[0] = d->counter, pl[1] = b, the rest 0 *)
  assert (AFTER : forall a2v a3v a4v, k_b k <= 0x7f -> seven_bit (firstn 8 (zb (k_bytes k))) = true ->
    evt rsegs (Qk E) (st10 E ra' t0' t1' t2' (Z_to_bv 64 1) (Z_to_bv 64 (k_b k)) a2v a3v a4v a5' a6'
      (Z_to_bv 64 (bv_unsigned (c_sp E) + -114)) s5' (Z_to_bv 64 (k_desk k)) t3' t4' t5' t6' ops 0x14950 m1)).
  { intros a2v a3v a4v Hb H7. unfold_kc FK.
    pose proof (desk_rd m1 k d (relro_at E m1 ENV MU) HDK) as [_ HRC1].
    unfold st10. step. rewrite UDK, LAND7. step.
    replace (v_sltiu (Z_to_bv 64 0) 1) with (Z_to_bv 64 1) by (vm_compute; reflexivity).
    step. step.
    if_cases T; [refute_trap T|].
    step. clear HRC1.
    do 10 step.
    step. step. step.
    lazymatch type of FPL with rw_cells _ ?mm ?A ?l =>
      pose proof (rw_cells_merge rsegs mm A [] l [] FPL) as PL1 end.
    cbn [app cells_size cells_bytes csize cbytes Nat.add] in PL1.
    apply (u8arr_of_rw_cells rsegs) in PL1.
    lazymatch type of PL1 with u8arr _ _ _ (?x0 :: ?x1 :: ?z :: _) =>
      apply (LOOP2 x0 x1 z (POST2 x0 x1 z ltac:(apply b8_zxb; lia) ltac:(apply b8_lit64; lia) Hb H7) 8%nat 0%nat)
    end;
      [ reflexivity | lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | ].
    exact (conj F0 (conj F8 (conj FK (conj FIN (conj FPD (conj FTX (conj PL1 (conj FSV (conj BY
             (conj ST (conj MU (conj WM HMI)))))))))))). }
  (* 0x1493c-0x1494c: seven_bit(k->bytes, 8) *)
  assert (LOOP1 : forall (dd j : nat) (a2v a3v a4v : word), dd = (8 - j)%nat -> (j < 8)%nat -> k_b k <= 0x7f ->
    bv_unsigned a2v = 8 - Z.of_nat j -> bv_unsigned a3v = bv_unsigned (c_sp E) + -344 + Z.of_nat j ->
    seven_bit (firstn j (zb (k_bytes k))) = true ->
    evt rsegs (Qk E) (st10 E ra' t0' t1' t2' (Z_to_bv 64 1) (Z_to_bv 64 (k_b k)) a2v a3v a4v a5' a6'
      (Z_to_bv 64 (bv_unsigned (c_sp E) + -114)) s5' (Z_to_bv 64 (k_desk k)) t3' t4' t5' t6' ops 0x1493c m1)).
  { induction dd as [|dd IH]; intros j a2v a3v a4v Hdd Hj Hb HA2 HA3 H7; [lia|].
    pose proof (bytes_at_byte m1 (bv_unsigned (c_sp E) + -344) (k_bytes k) (Z.of_nat j) BY
                  ltac:(rewrite LBY; lia)) as HR.
    rewrite Nat2Z.id in HR.
    rewrite (wa_of_var a3v (bv_unsigned (c_sp E) + -344 + Z.of_nat j) ltac:(lia)) in HR.
    unfold st10. step. step.
    if_cases G.
    - rewrite sxb_lts0 in G. apply ERANGE. right.
      apply (seven_bit_bad _ j); [lia | unfold zb; rewrite length_map; lia | rewrite zb_nth; exact G].
    - rewrite sxb_lts0 in G. step. step. step.
      if_cases G2.
      + zc G2. eapply (IH (S j)); [lia | lia | exact Hb | rewrite unsigned_lit by lia; lia
          | rewrite unsigned_lit by lia; lia | ].
        rewrite (firstn_S_nth _ _ j 0) by (unfold zb; rewrite length_map; lia).
        rewrite seven_bit_snoc, H7, zb_nth, G. reflexivity.
      + zc G2. assert (j = 7)%nat by lia. subst j. apply AFTER; [exact Hb|].
        change 8%nat with (S 7). rewrite (firstn_S_nth _ _ 7 0) by (unfold zb; rewrite length_map; lia).
        rewrite seven_bit_snoc, H7, zb_nth, G. reflexivity. }
  unfold_kc FK. step. rewrite (sx32_small (k_b k)) by lia. step. step.
  if_cases G1.
  - zc G1. apply ERANGE. left. lia.
  - zc G1. step. step.
    apply (LOOP1 8%nat 0%nat); [reflexivity | lia | lia | reflexivity | rewrite unsigned_lit by lia; lia | reflexivity].
Qed.
