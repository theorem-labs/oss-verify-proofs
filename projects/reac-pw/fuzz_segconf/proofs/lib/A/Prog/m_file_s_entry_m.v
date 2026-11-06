(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan, m_file at 0x85ebc): the model and byte-encoding facts of
   m_file's prologue, for the segment S_MF_ENTRY (lib/A/Prog/m_file_m.v) that is proved in
   lib/A/Prog/m_file_s_entry.v. Proves no function of the binary.

   m_file's first two writes to the block are `snprintf(c->reading, 96, "%s", label ? label : "reac-pw.conf")`
   (0x86014) and `c->gen++` (0x86048); SegModel.m_file starts its line loop from exactly that state, mf_c1 below.
   - mf_file_lines, mf_file_nil: SegModel.m_file is the line loop from mf_c1.
   - mf_fmt_s, mf_reading_bytes, mf_sn_bytes: the reading text that snprintf stores, in SegModel's and in the
     released snprintf post's (lib/A/Rt/RtPFShared.v sn_bytes / sn_len) terms.
   - mf_c1_counters: mf_c1 keeps every counter and adds 1 to gen.
   - mf_mconf_gen: the gen field read back from the encoding (what seeds the walk's symbolic region of c->gen).
   - mf_mconf_gen_reading: the re-encoding of struct mconf after the two writes. The new byte list is the old one
     with [MC_GEN, MC_GEN + 4) and [MC_READING, MC_READING + 96) = [MC_GEN + 4, SEG_M_SIZE) spliced in; every other
     field lies below MC_GEN (seg_spec.v: the segs end at 0x2000, n_kept at 0x23ac + 4 = 0x23b0), so ONE splice
     lemma (mf_fld_prefix) gives each of them.
     ONE HYPOTHESIS beyond the brief's: the 96 bytes of c->reading that rd' reads are byte values (0 <= z < 256).
     Without it the lemma is false, because a [reader] is any Z -> option Z, so rd' could read Some 300 at an
     unwritten reading byte after the NUL and no byte list then satisfies sa_bytes. A walk always has it: its
     reader is `aview segs H mem`, and mf_aview_byte below discharges the hypothesis for every aview reader. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Mem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtPFShared.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ===================================== the model ===================================== *)
Definition mf_lab_text (lab : option (list Z)) : list Z := match lab with Some l => l | None => S_base end.
(* the block after snprintf(c->reading, ...) and c->gen++ *)
Definition mf_c1 (mc : mconf) (lab : option (list Z)) : mconf :=
  MConf (mc_seg mc) (mc_overflow mc) (mc_refused mc) (mc_kept mc) (mc_gen mc + 1)
        (snprintf_s 96 F_s [AS (mf_lab_text lab)]).

(* 1 *)
Lemma mf_file_lines : forall mc s lab, SegModel.m_file mc s lab = fst (m_lines (mf_c1 mc lab, None) 0 (lines s)).
Proof. intros mc s lab. reflexivity. Qed.

(* 2 *)
Lemma mf_file_nil : forall mc lab, SegModel.m_file mc [] lab = mf_c1 mc lab.
Proof. intros mc lab. rewrite mf_file_lines. reflexivity. Qed.

(* 3 *)
Lemma mf_fmt_s : forall txt, ~ In 0 txt -> SegModel.fmt F_s [AS txt] = txt.
Proof. intros txt H. rewrite fmt_s1. apply cut_nul_id. exact H. Qed.

(* 4 *)
Lemma mf_reading_bytes : forall txt, ~ In 0 txt ->
  snprintf_s 96 F_s [AS txt] = firstn 95 txt /\ (length (snprintf_s 96 F_s [AS txt]) < 96)%nat /\
  ~ In 0 (snprintf_s 96 F_s [AS txt]).
Proof.
intros txt H. unfold snprintf_s. rewrite fmt_s1, cut_nul_id by exact H.
change (Z.to_nat (96 - 1)) with 95%nat.
split; [reflexivity|]. split.
- rewrite length_firstn. lia.
- intros Hin. apply H. rewrite <- (firstn_skipn 95 txt). apply in_or_app. left. exact Hin.
Qed.

(* 5 *)
Lemma mf_sn_bytes : forall txt, ~ In 0 txt ->
  RtPFShared.sn_bytes (96 - 1) txt = snprintf_s 96 F_s [AS txt] ++ [0] /\
  RtPFShared.sn_len (96 - 1) txt = Z.of_nat (length (snprintf_s 96 F_s [AS txt])) + 1.
Proof.
intros txt H. destruct (mf_reading_bytes txt H) as [E _]. rewrite E.
unfold RtPFShared.sn_len, RtPFShared.sn_bytes. change (Z.to_nat (96 - 1)) with 95%nat.
split; [reflexivity|]. rewrite length_app. cbn [length]. lia.
Qed.

(* 6 *)
Lemma mf_c1_counters : forall mc lab,
  mc_seg (mf_c1 mc lab) = mc_seg mc /\ mc_overflow (mf_c1 mc lab) = mc_overflow mc /\
  mc_refused (mf_c1 mc lab) = mc_refused mc /\ mc_kept (mf_c1 mc lab) = mc_kept mc /\
  mc_gen (mf_c1 mc lab) = mc_gen mc + 1.
Proof. intros mc lab. exact (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl eq_refl)))). Qed.

(* ===================================== list and byte facts ===================================== *)
Lemma mf_nth_firstn : forall {A} (l : list A) n i d, (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
intros A l. induction l as [|x l IH]; intros n i d H; destruct n as [|n]; try lia.
- reflexivity.
- destruct i as [|i]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.
Lemma mf_nth_skipn : forall {A} (l : list A) m n d, nth n (skipn m l) d = nth (m + n) l d.
Proof.
intros A l m. revert l. induction m as [|m IH]; intros l n d; [reflexivity|].
destruct l as [|x l]; [destruct n; reflexivity|].
change (nth n (skipn m l) d = nth (S m + n) (x :: l) d). rewrite IH. reflexivity.
Qed.
Lemma mf_skipn_app : forall {A} (l1 l2 : list A) n, length l1 = n -> skipn n (l1 ++ l2) = l2.
Proof. intros A l1 l2 n <-. induction l1 as [|x l1 IH]; [reflexivity|]. exact IH. Qed.
Lemma mf_firstn_app : forall {A} (l1 l2 : list A) n, length l1 = n -> firstn n (l1 ++ l2) = l1.
Proof.
intros A l1 l2 n <-. induction l1 as [|x l1 IH]; [reflexivity|].
change (x :: firstn (length l1) (l1 ++ l2) = x :: l1). rewrite IH. reflexivity.
Qed.
Lemma mf_firstn_all : forall {A} (l : list A) n, length l = n -> firstn n l = l.
Proof. intros A l n <-. apply firstn_all. Qed.
Lemma mf_nth_map_seq : forall {A} (f : nat -> A) n j d, (j < n)%nat -> nth j (map f (seq 0 n)) d = f j.
Proof.
intros A f n j d Hj. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; exact Hj).
rewrite map_nth, seq_nth by exact Hj. reflexivity.
Qed.
Lemma mf_firstn_skipn_cut : forall {A} (l : list A) off n K, (off + n <= K)%nat ->
  firstn n (skipn off (firstn K l)) = firstn n (skipn off l).
Proof.
intros A l off. revert l. induction off as [|off IH]; intros l n K H.
- change (firstn n (firstn K l) = firstn n l). rewrite firstn_firstn. replace (Nat.min n K) with n by lia.
  reflexivity.
- destruct K as [|K]; [lia|]. destruct l as [|x l]; [reflexivity|].
  change (firstn n (skipn off (firstn K l)) = firstn n (skipn off l)). apply IH. lia.
Qed.
(* THE splice lemma: a field that lies in the first K bytes is the same in two lists that agree there *)
Lemma mf_fld_prefix : forall (l1 l2 : list byte) (K off n : nat), firstn K l1 = firstn K l2 ->
  (off + n <= K)%nat -> seg_spec.fld off n l1 = seg_spec.fld off n l2.
Proof.
intros l1 l2 K off n E H. unfold seg_spec.fld.
rewrite <- (mf_firstn_skipn_cut l1 off n K H), <- (mf_firstn_skipn_cut l2 off n K H), E. reflexivity.
Qed.
Lemma mf_nth_zs : forall (bs : list byte) j, (j < length bs)%nat -> nth j (seg_spec.zs bs) 0 = bv_unsigned (nth j bs ZB0).
Proof.
induction bs as [|b bs IH]; intros j H; cbn [length] in H; [lia|].
destruct j as [|j]; [reflexivity|]. exact (IH j ltac:(lia)).
Qed.

(* byte k of the 4 little-endian bytes of v is le_byte v 4 k *)
Lemma mf_Z_to_le_bytes_nth : forall n z k, (k < n)%nat ->
  bv_unsigned (nth k (Z_to_le_bytes n z) ZB0) = Z.shiftr z (8 * Z.of_nat k) mod 256.
Proof.
induction n as [|n IH]; intros z k Hk; [lia|].
destruct k as [|k].
- change (bv_unsigned (Z_to_bv 8 z) = Z.shiftr z (8 * Z.of_nat 0) mod 256).
  rewrite Z_to_bv_unsigned. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
- change (bv_unsigned (nth k (Z_to_le_bytes n (Z.shiftr z 8)) ZB0) = Z.shiftr z (8 * Z.of_nat (S k)) mod 256).
  rewrite IH by lia. rewrite Z.shiftr_shiftr by lia.
  replace (8 * Z.of_nat (S k)) with (8 + 8 * Z.of_nat k) by lia. reflexivity.
Qed.
Lemma mf_le4_byte : forall v k, 0 <= v < 2 ^ 32 -> (k < 4)%nat ->
  bv_unsigned (nth k (le4 (Z_to_bv 64 v)) ZB0) = le_byte v 4 k.
Proof.
intros v k Hv Hk.
assert (Hu : bv_unsigned (Z_to_bv 64 v) = v).
{ rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616. change (2 ^ 32) with 4294967296 in Hv. lia. }
unfold le4. rewrite Hu, mf_Z_to_le_bytes_nth by exact Hk.
unfold le_byte. change (8 * Z.of_nat 4) with 32. rewrite (Z.mod_small v (2 ^ 32)) by exact Hv. reflexivity.
Qed.

(* a reader's byte as a Z, 0 where nothing is mapped; the 96 bytes at a as a byte list *)
Definition mf_rdz (rd : reader) (a : Z) : Z := match rd a with Some z => z | None => 0 end.
Definition mf_rb (rd : reader) (a : Z) : list byte := map (fun j => Z_to_bv 8 (mf_rdz rd (a + Z.of_nat j))) (seq 0 96).
Lemma mf_rb_length : forall rd a, length (mf_rb rd a) = 96%nat.
Proof. intros rd a. unfold mf_rb. rewrite length_map, length_seq. reflexivity. Qed.
Lemma mf_rb_val : forall (rd : reader) a j z, (j < 96)%nat -> rd (a + Z.of_nat j) = Some z -> 0 <= z < 256 ->
  bv_unsigned (nth j (mf_rb rd a) ZB0) = z.
Proof.
intros rd a j z Hj E Hz. unfold mf_rb. rewrite mf_nth_map_seq by exact Hj. cbv beta.
unfold mf_rdz. rewrite E. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus.
change (2 ^ Z.of_N 8) with 256. exact Hz.
Qed.

(* every byte an aview reader reads is a byte value: the walk's discharge of mf_mconf_gen_reading's range premise *)
Lemma mf_omap_byte : forall (o : option byte) z, option_map (fun b : byte => bv_unsigned b) o = Some z -> 0 <= z < 256.
Proof.
intros [b|] z E; [|discriminate E]. cbn [option_map] in E. injection E as E'. subst z.
pose proof (bv_unsigned_in_range 8 b) as Hr. unfold bv_modulus in Hr. change (2 ^ Z.of_N 8) with 256 in Hr. exact Hr.
Qed.
Lemma mf_aview_byte : forall segs H mem a z, YG0n.aview segs H mem a = Some z -> 0 <= z < 256.
Proof. intros segs H mem a z E. unfold YG0n.aview in E. exact (mf_omap_byte _ z E). Qed.

Local Ltac mf_lia :=
  unfold seg_spec.SEG_M_SIZE, seg_spec.MC_N, seg_spec.MC_OVERFLOW, seg_spec.MC_REFUSED, seg_spec.MC_KEPT,
    seg_spec.MC_KNOCK, seg_spec.MC_NKEPT, seg_spec.MC_GEN, seg_spec.MC_READING in *; lia.

(* ===================================== the struct after the two writes ===================================== *)
(* 8 *)
Lemma mf_mconf_gen : forall (rd : reader) (c : Z) (mc : mconf),
  SegABase.sa_mconf rd c mc -> SegABase.sa_val rd (c + seg_spec.MC_GEN) 4%nat (mc_gen mc) /\ 0 <= mc_gen mc < 2 ^ 32.
Proof.
intros rd c mc Hmc. unfold SegABase.sa_mconf, SegABase.sa_mconfp in Hmc. destruct Hmc as [bs [Hb Henc]].
unfold SegABase.sa_bytes in Hb. unfold seg_spec.mconf_encp in Henc.
destruct Henc as (Hlen & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hg0 & _). destruct Hg0 as [Hgr Hgf].
split; [|exact Hgr]. intros k Hk.
replace (c + seg_spec.MC_GEN + Z.of_nat k) with (c + Z.of_nat (Z.to_nat seg_spec.MC_GEN + k)) by mf_lia.
rewrite Hb by mf_lia. f_equal.
rewrite <- mf_nth_skipn.
rewrite <- (mf_nth_firstn (skipn (Z.to_nat seg_spec.MC_GEN) bs) (Z.to_nat 4) k ZB0) by lia.
change (firstn (Z.to_nat 4) (skipn (Z.to_nat seg_spec.MC_GEN) bs)) with (seg_spec.fldz seg_spec.MC_GEN 4 bs).
rewrite Hgf. apply mf_le4_byte; [exact Hgr | exact Hk].
Qed.

(* 7 *)
Lemma mf_mconf_gen_reading : forall (rd rd' : reader) (c : Z) (mc : mconf) (txt : list Z),
  SegABase.sa_mconf rd c mc ->
  (* every byte of the block outside c->gen and c->reading is unchanged *)
  (forall a, c <= a < c + seg_spec.SEG_M_SIZE ->
     ~ (c + seg_spec.MC_GEN <= a < c + seg_spec.MC_GEN + 4) ->
     ~ (c + seg_spec.MC_READING <= a < c + seg_spec.MC_READING + 96) -> rd' a = rd a) ->
  (* c->gen holds gen + 1 *)
  SegABase.sa_val rd' (c + seg_spec.MC_GEN) 4%nat (mc_gen mc + 1) -> 0 <= mc_gen mc + 1 < 2 ^ 32 ->
  (* c->reading holds txt and its NUL, and all 96 bytes are readable *)
  (length txt < 96)%nat -> ~ In 0 txt ->
  (forall i, (i < S (length txt))%nat ->
     rd' (c + seg_spec.MC_READING + Z.of_nat i) = Some (nth i (txt ++ [0]) 0)) ->
  (forall i, (i < 96)%nat -> rd' (c + seg_spec.MC_READING + Z.of_nat i) <> None) ->
  (* and are byte values (an aview reader's: mf_aview_byte) *)
  (forall i, (i < 96)%nat -> forall z, rd' (c + seg_spec.MC_READING + Z.of_nat i) = Some z -> 0 <= z < 256) ->
  SegABase.sa_mconf rd' c (MConf (mc_seg mc) (mc_overflow mc) (mc_refused mc) (mc_kept mc) (mc_gen mc + 1) txt).
Proof.
intros rd rd' c mc txt Hmc Hkeep Hgv Hgr Htl Htz Htx Hrn Hrr.
unfold SegABase.sa_mconf, SegABase.sa_mconfp in *. destruct Hmc as [bs [Hb Henc]].
unfold SegABase.sa_bytes in Hb. unfold SegABase.sa_val in Hgv. unfold seg_spec.mconf_encp in Henc.
destruct Henc as (Hlen & Hsl & Hseg & Hn & Hov & Href & Hkl & Hkept & Hknock & Hnk & _ & _).
assert (Hfl : length (firstn (Z.to_nat seg_spec.MC_GEN) bs) = Z.to_nat seg_spec.MC_GEN)
  by (rewrite length_firstn; mf_lia).
pose proof (mf_rb_length rd' (c + seg_spec.MC_READING)) as Hrbl.
exists (firstn (Z.to_nat seg_spec.MC_GEN) bs ++ le4 (Z_to_bv 64 (mc_gen mc + 1)) ++ mf_rb rd' (c + seg_spec.MC_READING)).
split.
- (* the bytes through rd' *)
  unfold SegABase.sa_bytes. intros i Hi. rewrite !length_app, Hfl, length_le4, Hrbl in Hi.
  destruct (Nat.lt_ge_cases i (Z.to_nat seg_spec.MC_GEN)) as [H1|H1].
  + rewrite app_nth1 by (rewrite Hfl; exact H1). rewrite mf_nth_firstn by exact H1.
    rewrite Hkeep; [apply Hb; mf_lia | mf_lia | mf_lia | mf_lia].
  + rewrite app_nth2 by (rewrite Hfl; lia). rewrite Hfl.
    destruct (Nat.lt_ge_cases i (Z.to_nat seg_spec.MC_GEN + 4)) as [H2|H2].
    * rewrite app_nth1 by (rewrite length_le4; lia).
      replace (c + Z.of_nat i) with (c + seg_spec.MC_GEN + Z.of_nat (i - Z.to_nat seg_spec.MC_GEN)) by mf_lia.
      rewrite Hgv by lia. f_equal. symmetry. apply mf_le4_byte; [exact Hgr | lia].
    * rewrite app_nth2 by (rewrite length_le4; lia). rewrite length_le4.
      replace (c + Z.of_nat i)
        with (c + seg_spec.MC_READING + Z.of_nat (i - Z.to_nat seg_spec.MC_GEN - 4)) by mf_lia.
      destruct (rd' (c + seg_spec.MC_READING + Z.of_nat (i - Z.to_nat seg_spec.MC_GEN - 4))) as [z|] eqn:E.
      -- assert (Hj : (i - Z.to_nat seg_spec.MC_GEN - 4 < 96)%nat) by mf_lia.
         rewrite (mf_rb_val rd' (c + seg_spec.MC_READING) (i - Z.to_nat seg_spec.MC_GEN - 4)%nat z Hj E
                    (Hrr (i - Z.to_nat seg_spec.MC_GEN - 4)%nat Hj z E)).
         reflexivity.
      -- exfalso. assert (Hj : (i - Z.to_nat seg_spec.MC_GEN - 4 < 96)%nat) by mf_lia.
         exact (Hrn (i - Z.to_nat seg_spec.MC_GEN - 4)%nat Hj E).
- (* the encoding *)
  assert (Hfld : forall off n, (off + n <= Z.to_nat seg_spec.MC_GEN)%nat ->
    seg_spec.fld off n (firstn (Z.to_nat seg_spec.MC_GEN) bs ++ le4 (Z_to_bv 64 (mc_gen mc + 1)) ++
                        mf_rb rd' (c + seg_spec.MC_READING)) = seg_spec.fld off n bs).
  { intros off n Hon. apply (mf_fld_prefix _ _ (Z.to_nat seg_spec.MC_GEN)); [|exact Hon].
    apply mf_firstn_app. exact Hfl. }
  unfold seg_spec.mconf_encp. cbn [mc_seg mc_overflow mc_refused mc_kept mc_gen mc_reading].
  refine (conj _ (conj Hsl (conj _ (conj _ (conj _ (conj _ (conj Hkl (conj _ (conj _ (conj _ (conj _ _))))))))))).
  + rewrite !length_app, Hfl, length_le4, Hrbl. mf_lia.
  + intros i Hi. rewrite Hfld by mf_lia. exact (Hseg i Hi).
  + unfold seg_spec.fldz. rewrite Hfld by mf_lia. exact Hn.
  + unfold seg_spec.fldz. rewrite Hfld by mf_lia. exact Hov.
  + unfold seg_spec.fldz. rewrite Hfld by mf_lia. exact Href.
  + intros i Hi. destruct (Hkept i Hi) as [Hk1 Hk2].
    split; rewrite Hfld by mf_lia; assumption.
  + intros i Hi. rewrite Hfld by mf_lia. exact (Hknock i Hi).
  + unfold seg_spec.fldz. rewrite Hfld by mf_lia. exact Hnk.
  + split; [exact Hgr|]. unfold seg_spec.fldz, seg_spec.fld.
    rewrite (mf_skipn_app (firstn (Z.to_nat seg_spec.MC_GEN) bs) _ _ Hfl).
    apply mf_firstn_app. apply length_le4.
  + unfold seg_spec.fldz, seg_spec.fld. rewrite app_assoc.
    rewrite (mf_skipn_app (firstn (Z.to_nat seg_spec.MC_GEN) bs ++ le4 (Z_to_bv 64 (mc_gen mc + 1))) _
               (Z.to_nat seg_spec.MC_READING)) by (rewrite length_app, Hfl, length_le4; mf_lia).
    rewrite (mf_firstn_all _ (Z.to_nat 96) Hrbl).
    unfold seg_spec.cstr_enc. refine (conj Hrbl (conj Htl (conj Htz _))).
    apply (nth_ext _ _ 0 0).
    * rewrite length_firstn, length_app. unfold seg_spec.zs. rewrite length_map, Hrbl. cbn [length]. lia.
    * intros j Hj. rewrite length_firstn in Hj. unfold seg_spec.zs in Hj. rewrite length_map, Hrbl in Hj.
      rewrite mf_nth_firstn by lia. rewrite mf_nth_zs by (rewrite Hrbl; lia).
      apply (mf_rb_val rd' (c + seg_spec.MC_READING) j); [lia | apply Htx; lia |].
      apply (Hrr j); [lia | apply Htx; lia].
Qed.
