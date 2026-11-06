(* m_file, segment S_MF_KIGNP of m_file's walk (fuzz_segconf.asan, image A), the KIGNP segment lane: the model lemma for
   the hit path of the ignore key (0x869e8-0x86a34). With g = c + 256 * gi the gi-th entry of the struct mconf at c,
   that path stores g->ignore = b (the 4 bytes at g + 24, 0x869fc), g->ignore_set = 1 (the 4 bytes at g + 28,
   0x86a1c), and its snprintf (0x86a34) writes c->reading's text f and its NUL at g->ignore_file (g + 156).

   This file proves no function of the binary. It is a PURE lemma over readers (no machine, no executor):
   - [ki_e_bytes_patch]: a byte list read at a through rd, patched at off with ys, is read at a through rd' when
     rd' agrees with rd outside [a + off, a + off + |ys|) and holds ys there.
   - [ki_e_mconf_ign]: the struct mconf at c, read through rd' after those three writes, encodes
     m_upd mc gi (ms_with_ignore b f) (seg_spec.mconf_encp false). Its last premise (every value rd' returns is a
     byte) is what makes the snprintf's bytes, given as the list of Z f ++ [0], a list of bytes: without it the
     lemma is false (f = [300]). The ASan reader aview gives it (a byte as a Z in [0, 256)).
   Every field of mconf_encp outside entry gi, and every field of entry gi outside [24, 32) and [156, 157 + |f|),
   is the old field; ignore and ignore_set are the stored words (flag_enc b, flag_enc true); ignore_file holds
   f and its NUL (cstr_enc 96 f fixes only the first |f| + 1 bytes). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Local Notation le4 := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Mem.le4.

(* ---------------------------------------------- lists ---------------------------------------------- *)
Lemma ki_e_nth_firstn : forall {A} n i (l : list A) d, (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
  intros A n; induction n as [|n IH]; intros i l d Hi; [lia|].
  destruct l as [|x l]; [reflexivity|]. destruct i as [|i]; [reflexivity|].
  cbn [firstn nth]. apply IH. lia.
Qed.

Lemma ki_e_nth_skipn : forall {A} n i (l : list A) d, nth i (skipn n l) d = nth (n + i) l d.
Proof.
  intros A n; induction n as [|n IH]; intros i l d; [reflexivity|].
  destruct l as [|x l]; [destruct i; reflexivity|]. cbn [skipn Nat.add nth]. apply IH.
Qed.

Lemma ki_e_upd_len : forall {A} i (f : A -> A) l, length (upd_nth i f l) = length l.
Proof.
  intros A i f l; revert i; induction l as [|x l IH]; intros [|i]; cbn [upd_nth length]; try reflexivity.
  rewrite IH. reflexivity.
Qed.

Lemma ki_e_upd_nth_eq : forall {A} i (f : A -> A) l d, (i < length l)%nat -> nth i (upd_nth i f l) d = f (nth i l d).
Proof.
  intros A i f l d; revert i; induction l as [|x l IH]; intros [|i] Hi; cbn [length] in Hi.
  - lia.
  - lia.
  - reflexivity.
  - cbn [upd_nth nth]. apply IH. lia.
Qed.

Lemma ki_e_upd_nth_ne : forall {A} i j (f : A -> A) l d, i <> j -> nth j (upd_nth i f l) d = nth j l d.
Proof.
  intros A i j f l d; revert i j; induction l as [|x l IH]; intros [|i] [|j] Hij; cbn [upd_nth nth];
    try reflexivity; try lia.
  apply IH. lia.
Qed.

(* ------------------------------------------ fields of a byte list ------------------------------------------ *)
Lemma ki_e_fld_len : forall off n (l : list byte), length (seg_spec.fld off n l) = Nat.min n (length l - off).
Proof. intros. unfold seg_spec.fld. rewrite length_firstn, length_skipn. reflexivity. Qed.

Lemma ki_e_fld_nth : forall off n (l : list byte) i d, (i < n)%nat ->
  nth i (seg_spec.fld off n l) d = nth (off + i) l d.
Proof. intros off n l i d Hi. unfold seg_spec.fld. rewrite ki_e_nth_firstn by exact Hi. apply ki_e_nth_skipn. Qed.

Lemma ki_e_fld_ext : forall (l1 l2 : list byte) off n, length l1 = length l2 ->
  (forall i, (i < n)%nat -> (off + i < length l1)%nat -> nth (off + i) l1 ZB0 = nth (off + i) l2 ZB0) ->
  seg_spec.fld off n l1 = seg_spec.fld off n l2.
Proof.
  intros l1 l2 off n HL H. apply nth_ext with (d := ZB0) (d' := ZB0).
  - rewrite !ki_e_fld_len, HL. reflexivity.
  - intros i Hi. rewrite ki_e_fld_len in Hi. rewrite !ki_e_fld_nth by lia. apply H; lia.
Qed.

Lemma ki_e_fld_fld : forall (l : list byte) a m o n, (o + n <= m)%nat ->
  seg_spec.fld o n (seg_spec.fld a m l) = seg_spec.fld (a + o) n l.
Proof.
  intros l a m o n H. apply nth_ext with (d := ZB0) (d' := ZB0).
  - rewrite !ki_e_fld_len. lia.
  - intros i Hi. rewrite !ki_e_fld_len in Hi. rewrite !ki_e_fld_nth by lia. f_equal. lia.
Qed.

Lemma ki_e_firstn_fld : forall (l : list byte) off n k, (k <= n)%nat ->
  firstn k (seg_spec.fld off n l) = seg_spec.fld off k l.
Proof. intros l off n k H. unfold seg_spec.fld. rewrite firstn_firstn. f_equal. lia. Qed.

Lemma ki_e_fld_all : forall (l : list byte), seg_spec.fld 0 (length l) l = l.
Proof. intros l. unfold seg_spec.fld. cbn [skipn]. apply firstn_all. Qed.

Lemma ki_e_fld_app_l : forall (X Y : list byte) n, length X = n -> seg_spec.fld 0 n (X ++ Y) = X.
Proof.
  intros X Y n <-. apply nth_ext with (d := ZB0) (d' := ZB0).
  - rewrite ki_e_fld_len, length_app. lia.
  - intros i Hi. rewrite ki_e_fld_len, length_app in Hi. rewrite ki_e_fld_nth by lia. cbn [Nat.add].
    apply app_nth1. lia.
Qed.

Lemma ki_e_fld_app_r : forall (X Y : list byte) o n, length X = o -> length Y = n ->
  seg_spec.fld o n (X ++ Y) = Y.
Proof.
  intros X Y o n <- <-. apply nth_ext with (d := ZB0) (d' := ZB0).
  - rewrite ki_e_fld_len, length_app. lia.
  - intros i Hi. rewrite ki_e_fld_len, length_app in Hi. rewrite ki_e_fld_nth by lia.
    rewrite app_nth2 by lia. f_equal. lia.
Qed.

Lemma ki_e_firstn_zs : forall n (l : list byte), firstn n (seg_spec.zs l) = seg_spec.zs (firstn n l).
Proof.
  unfold seg_spec.zs. induction n as [|n IH]; intros [|x l]; cbn [firstn map]; try reflexivity.
  f_equal. apply IH.
Qed.

Lemma ki_e_bu8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hz.
Qed.

Lemma ki_e_zs_zb : forall l, Forall (fun z => 0 <= z < 256) l -> seg_spec.zs (seg_spec.zb l) = l.
Proof.
  induction l as [|z l IH]; intros H; [reflexivity|].
  pose proof (Forall_inv H) as Hz. pose proof (Forall_inv_tail H) as Hl. cbv beta in Hz.
  unfold seg_spec.zs, seg_spec.zb in *. cbn [map]. rewrite ki_e_bu8 by exact Hz. f_equal. apply IH. exact Hl.
Qed.

Lemma ki_e_len_le4 : forall v, length (le4 v) = 4%nat.
Proof. exact OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Mem.length_le4. Qed.

(* the 8 bytes the two stores write: ignore = b at +0, ignore_set = 1 at +4 *)
Lemma ki_e_ys1_bytes : forall (b : bool) k, (k < 8)%nat ->
  bv_unsigned (nth k (le4 (Z_to_bv 64 (seg_spec.b2z b)) ++ le4 (Z_to_bv 64 1)) ZB0) =
  if (k <? 4)%nat then le_byte (seg_spec.b2z b) 4 k else le_byte 1 4 (k - 4).
Proof. intros b k Hk. destruct b; do 8 (destruct k as [|k]; [vm_compute; reflexivity|]); lia. Qed.

(* --------------------------------------------- the patch --------------------------------------------- *)
(* bs with the bytes [p, p + |ys|) replaced by ys *)
Definition ki_e_patch (bs ys : list byte) (p : nat) : list byte := firstn p bs ++ ys ++ skipn (p + length ys) bs.

Lemma ki_e_patch_len : forall bs ys p, (p + length ys <= length bs)%nat -> length (ki_e_patch bs ys p) = length bs.
Proof. intros bs ys p H. unfold ki_e_patch. rewrite !length_app, length_firstn, length_skipn. lia. Qed.

Lemma ki_e_patch_out : forall bs ys p i d, (p + length ys <= length bs)%nat -> (i < p \/ p + length ys <= i)%nat ->
  nth i (ki_e_patch bs ys p) d = nth i bs d.
Proof.
  intros bs ys p i d HL Hi. unfold ki_e_patch.
  assert (Lf : length (firstn p bs) = p) by (rewrite length_firstn; lia).
  destruct Hi as [Hi|Hi].
  - rewrite app_nth1 by lia. apply ki_e_nth_firstn. exact Hi.
  - rewrite app_nth2 by lia. rewrite Lf. rewrite app_nth2 by lia. rewrite ki_e_nth_skipn. f_equal. lia.
Qed.

Lemma ki_e_patch_in : forall bs ys p i d, (p + length ys <= length bs)%nat -> (p <= i < p + length ys)%nat ->
  nth i (ki_e_patch bs ys p) d = nth (i - p) ys d.
Proof.
  intros bs ys p i d HL Hi. unfold ki_e_patch.
  assert (Lf : length (firstn p bs) = p) by (rewrite length_firstn; lia).
  rewrite app_nth2 by lia. rewrite Lf. apply app_nth1. lia.
Qed.

Lemma ki_e_fld_patch_out : forall bs ys p off n, (p + length ys <= length bs)%nat ->
  (off + n <= p \/ p + length ys <= off)%nat ->
  seg_spec.fld off n (ki_e_patch bs ys p) = seg_spec.fld off n bs.
Proof.
  intros bs ys p off n HL Hd. apply ki_e_fld_ext; [apply ki_e_patch_len; exact HL|].
  intros i Hi _. apply ki_e_patch_out; [exact HL | lia].
Qed.

Lemma ki_e_fld_patch_at : forall o bs ys p off n, (p + length ys <= length bs)%nat -> off = (p + o)%nat ->
  (o + n <= length ys)%nat -> seg_spec.fld off n (ki_e_patch bs ys p) = seg_spec.fld o n ys.
Proof.
  intros o bs ys p off n HL -> Ho. apply nth_ext with (d := ZB0) (d' := ZB0).
  - rewrite !ki_e_fld_len, ki_e_patch_len by exact HL. lia.
  - intros i Hi. rewrite ki_e_fld_len, ki_e_patch_len in Hi by exact HL.
    rewrite !ki_e_fld_nth by lia. rewrite ki_e_patch_in by lia. f_equal. lia.
Qed.

Lemma ki_e_bytes_patch : forall (rd rd' : reader) (a : Z) (bs ys : list byte) (off : nat),
  sa_bytes rd a bs -> (off + length ys <= length bs)%nat ->
  (forall i, (i < length bs)%nat -> ~ (off <= i < off + length ys)%nat -> rd' (a + Z.of_nat i) = rd (a + Z.of_nat i)) ->
  sa_bytes rd' (a + Z.of_nat off) ys ->
  sa_bytes rd' a (firstn off bs ++ ys ++ skipn (off + length ys) bs).
Proof.
  intros rd rd' a bs ys off HB HL HO HY.
  change (firstn off bs ++ ys ++ skipn (off + length ys) bs) with (ki_e_patch bs ys off).
  intros i Hi. rewrite ki_e_patch_len in Hi by exact HL.
  destruct (Nat.lt_ge_cases i off) as [H1|H1].
  - rewrite ki_e_patch_out by lia. rewrite HO by lia. exact (HB i Hi).
  - destruct (Nat.lt_ge_cases i (off + length ys)) as [H2|H2].
    + rewrite ki_e_patch_in by lia.
      replace (a + Z.of_nat i) with (a + Z.of_nat off + Z.of_nat (i - off)) by lia.
      exact (HY (i - off)%nat ltac:(lia)).
    + rewrite ki_e_patch_out by lia. rewrite HO by lia. exact (HB i Hi).
Qed.

(* ------------------------------------- a reader between the two writes ------------------------------------- *)
(* rd' on [lo, hi), rd elsewhere *)
Definition ki_e_ovl (rd' rd : reader) (lo hi : Z) : reader :=
  fun x => if (lo <=? x) && (x <? hi) then rd' x else rd x.

Lemma ki_e_ovl_in : forall rd' rd lo hi x, lo <= x < hi -> ki_e_ovl rd' rd lo hi x = rd' x.
Proof.
  intros rd' rd lo hi x Hx. unfold ki_e_ovl.
  replace ((lo <=? x) && (x <? hi)) with true; [reflexivity|].
  symmetry. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma ki_e_ovl_out : forall rd' rd lo hi x, ~ (lo <= x < hi) -> ki_e_ovl rd' rd lo hi x = rd x.
Proof.
  intros rd' rd lo hi x Hx. unfold ki_e_ovl.
  replace ((lo <=? x) && (x <? hi)) with false; [reflexivity|].
  symmetry. apply andb_false_iff. destruct (Z.le_gt_cases lo x).
  - right. apply Z.ltb_ge. lia.
  - left. apply Z.leb_gt. lia.
Qed.

Lemma ki_e_ovl_cases : forall rd' rd lo hi x,
  ki_e_ovl rd' rd lo hi x = rd' x \/ (~ (lo <= x < hi) /\ ki_e_ovl rd' rd lo hi x = rd x).
Proof.
  intros rd' rd lo hi x. destruct (Z.le_gt_cases lo x) as [L|L]; [destruct (Z.le_gt_cases hi x) as [M|M]|].
  - right. split; [lia|]. apply ki_e_ovl_out. lia.
  - left. apply ki_e_ovl_in. lia.
  - right. split; [lia|]. apply ki_e_ovl_out. lia.
Qed.

(* --------------------------------------- the mconf after the writes --------------------------------------- *)
Lemma ki_e_mconf_ign : forall (rd rd' : reader) (c : Z) (mc : mconf) (gi : nat) (b : bool) (f : list Z),
  sa_mconf rd c mc -> (gi < length (mc_seg mc))%nat ->
  (length f < 96)%nat -> ~ In 0 f ->
  (forall x, c <= x < c + seg_spec.SEG_M_SIZE ->
     ~ (seg_spec.mseg_addr c gi + 24 <= x < seg_spec.mseg_addr c gi + 32) ->
     ~ (seg_spec.mseg_addr c gi + 156 <= x < seg_spec.mseg_addr c gi + 156 + Z.of_nat (length f) + 1) ->
     rd' x = rd x) ->
  sa_val rd' (seg_spec.mseg_addr c gi + 24) 4 (seg_spec.b2z b) ->
  sa_val rd' (seg_spec.mseg_addr c gi + 28) 4 1 ->
  sa_zs rd' (seg_spec.mseg_addr c gi + 156) (f ++ [0]) ->
  (forall x v, rd' x = Some v -> 0 <= v < 256) ->
  sa_mconf rd' c (m_upd mc gi (ms_with_ignore b f)).
Proof.
  intros rd rd' c mc gi b f HM Hgi Hf Hf0 HO HV1 HV2 HZ HR.
  destruct HM as (bs & HB & HE).
  pose proof HE as (HL & H32 & HS & HN & HOV & HRF & HK8 & HK & HKP & HNK & HG & HRD).
  unfold seg_spec.SEG_M_SIZE in HL, HO.
  assert (Hg32 : (gi < 32)%nat) by lia.
  assert (HA : seg_spec.mseg_addr c gi = c + Z.of_nat (256 * gi)).
  { unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE. lia. }
  rewrite HA in HO, HV1, HV2, HZ.
  (* the bytes of f and its NUL *)
  assert (HfB : Forall (fun z => 0 <= z < 256) (f ++ [0])).
  { apply Forall_forall. intros z Hz. apply (In_nth _ _ 0) in Hz as (k & Hk & Ek). subst z. cbv beta.
    apply (HR (c + Z.of_nat (256 * gi) + 156 + Z.of_nat k)). exact (HZ k Hk). }
  (* the new bytes: bs patched at 256 gi + 24 with the two words, then at 256 gi + 156 with f and its NUL *)
  set (ys1 := le4 (Z_to_bv 64 (seg_spec.b2z b)) ++ le4 (Z_to_bv 64 1)).
  assert (Ly1 : length ys1 = 8%nat) by (unfold ys1; rewrite length_app, !ki_e_len_le4; reflexivity).
  set (ys2 := seg_spec.zb (f ++ [0])).
  assert (Ly2 : length ys2 = S (length f)).
  { unfold ys2, seg_spec.zb. rewrite length_map, length_app. cbn [length]. lia. }
  assert (P1 : (256 * gi + 24 + length ys1 <= length bs)%nat) by lia.
  set (bs1 := ki_e_patch bs ys1 (256 * gi + 24)).
  assert (Lb1 : length bs1 = length bs) by (unfold bs1; apply ki_e_patch_len; exact P1).
  assert (P2 : (256 * gi + 156 + length ys2 <= length bs1)%nat) by lia.
  set (bs2 := ki_e_patch bs1 ys2 (256 * gi + 156)).
  assert (Lb2 : length bs2 = length bs) by (unfold bs2; rewrite ki_e_patch_len by exact P2; exact Lb1).
  (* rd' reads bs2 at c *)
  assert (HB1 : sa_bytes (ki_e_ovl rd' rd (c + Z.of_nat (256 * gi) + 24) (c + Z.of_nat (256 * gi) + 32)) c bs1).
  { unfold bs1, ki_e_patch. apply ki_e_bytes_patch with (rd := rd).
    - exact HB.
    - exact P1.
    - intros i Hi Hn. apply ki_e_ovl_out. lia.
    - intros k Hk. rewrite Ly1 in Hk. rewrite ki_e_ovl_in by lia.
      destruct (Nat.lt_ge_cases k 4) as [K|K].
      + replace (c + Z.of_nat (256 * gi + 24) + Z.of_nat k) with (c + Z.of_nat (256 * gi) + 24 + Z.of_nat k) by lia.
        rewrite (HV1 k K). unfold ys1. rewrite ki_e_ys1_bytes by lia. rewrite (proj2 (Nat.ltb_lt k 4) K).
        reflexivity.
      + replace (c + Z.of_nat (256 * gi + 24) + Z.of_nat k)
          with (c + Z.of_nat (256 * gi) + 28 + Z.of_nat (k - 4)) by lia.
        rewrite (HV2 (k - 4)%nat) by lia. unfold ys1. rewrite ki_e_ys1_bytes by lia.
        rewrite (proj2 (Nat.ltb_ge k 4) K). reflexivity. }
  assert (HB2 : sa_bytes rd' c bs2).
  { unfold bs2, ki_e_patch.
    apply ki_e_bytes_patch with (rd := ki_e_ovl rd' rd (c + Z.of_nat (256 * gi) + 24) (c + Z.of_nat (256 * gi) + 32)).
    - exact HB1.
    - exact P2.
    - intros i Hi Hn. rewrite Lb1 in Hi.
      destruct (ki_e_ovl_cases rd' rd (c + Z.of_nat (256 * gi) + 24) (c + Z.of_nat (256 * gi) + 32) (c + Z.of_nat i))
        as [E|[Hn' E]]; rewrite E; [reflexivity|].
      apply HO; [lia | exact Hn' | lia].
    - intros k Hk. rewrite Ly2 in Hk.
      replace (c + Z.of_nat (256 * gi + 156) + Z.of_nat k) with (c + Z.of_nat (256 * gi) + 156 + Z.of_nat k) by lia.
      rewrite (HZ k) by (rewrite length_app; cbn [length]; lia).
      f_equal. unfold ys2, seg_spec.zb. change ZB0 with (Z_to_bv 8 0). rewrite map_nth.
      rewrite ki_e_bu8; [reflexivity|].
      apply (proj1 (Forall_forall _ _) HfB). apply nth_In. rewrite length_app. cbn [length]. lia. }
  (* the fields: away from the two patches, bs2 is bs *)
  assert (Fout : forall off n,
    (off + n <= 256 * gi + 24 \/ (256 * gi + 32 <= off /\ off + n <= 256 * gi + 156) \/
     256 * gi + 157 + length f <= off)%nat ->
    seg_spec.fld off n bs2 = seg_spec.fld off n bs).
  { intros off n Hd. unfold bs2. rewrite ki_e_fld_patch_out by lia. unfold bs1. apply ki_e_fld_patch_out; lia. }
  assert (Un : forall o n,
    (o + n <= 24 \/ (32 <= o /\ o + n <= 156) \/ (157 + length f <= o /\ o + n <= 256))%nat ->
    seg_spec.fld o n (seg_spec.fld (256 * gi) 256 bs2) = seg_spec.fld o n (seg_spec.fld (256 * gi) 256 bs)).
  { intros o n Ho. rewrite !ki_e_fld_fld by lia. apply Fout. lia. }
  unfold sa_mconf, sa_mconfp. exists bs2. split; [exact HB2|].
  unfold m_upd, m_set_segs, seg_spec.mconf_encp.
  cbn [mc_seg mc_overflow mc_refused mc_kept mc_gen mc_reading].
  rewrite ki_e_upd_len.
  unfold seg_spec.fldz, seg_spec.MC_N, seg_spec.MC_OVERFLOW, seg_spec.MC_REFUSED, seg_spec.MC_KEPT,
    seg_spec.MC_KNOCK, seg_spec.MC_NKEPT, seg_spec.MC_GEN, seg_spec.MC_READING.
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]].
  - rewrite Lb2. unfold seg_spec.SEG_M_SIZE. exact HL.
  - exact H32.
  - intros i Hi. destruct (Nat.eq_dec i gi) as [->|Hne].
    + (* entry gi: ignore, ignore_set and ignore_file are the new ones, every other field is the old one *)
      rewrite ki_e_upd_nth_eq by exact Hgi.
      destruct (HS gi Hgi) as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10).
      unfold ms_with_ignore, seg_spec.mseg_enc.
      cbn [ms_name ms_role ms_role_set ms_ignore ms_ignore_set ms_model_set ms_model ms_role_file ms_ignore_file
        ms_gen].
      unfold seg_spec.fldz, seg_spec.MS_ROLE, seg_spec.MS_ROLE_SET, seg_spec.MS_IGNORE, seg_spec.MS_IGNORE_SET,
        seg_spec.MS_MODEL_SET, seg_spec.MS_MODEL, seg_spec.MS_ROLE_FILE, seg_spec.MS_IGNORE_FILE, seg_spec.MS_GEN.
      split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
      * rewrite !ki_e_fld_len. lia.
      * rewrite Un by lia. exact E1.
      * rewrite Un by lia. exact E2.
      * rewrite Un by lia. exact E3.
      * unfold seg_spec.flag_enc. rewrite ki_e_fld_fld by lia. unfold bs2. rewrite ki_e_fld_patch_out by lia.
        unfold bs1. rewrite (ki_e_fld_patch_at 0) by lia. unfold ys1.
        etransitivity; [apply ki_e_fld_app_l; rewrite ki_e_len_le4; reflexivity | reflexivity].
      * unfold seg_spec.flag_enc. rewrite ki_e_fld_fld by lia. unfold bs2. rewrite ki_e_fld_patch_out by lia.
        unfold bs1. rewrite (ki_e_fld_patch_at 4) by lia. unfold ys1.
        etransitivity; [apply ki_e_fld_app_r; rewrite ki_e_len_le4; reflexivity | reflexivity].
      * rewrite Un by lia. exact E6.
      * rewrite Un by lia. exact E7.
      * rewrite Un by lia. exact E8.
      * unfold seg_spec.cstr_enc. split; [|split; [exact Hf|split; [exact Hf0|]]].
        -- rewrite !ki_e_fld_len. lia.
        -- rewrite ki_e_firstn_zs, ki_e_firstn_fld by lia. rewrite ki_e_fld_fld by lia.
           unfold bs2. rewrite (ki_e_fld_patch_at 0) by lia. rewrite <- Ly2, ki_e_fld_all.
           unfold ys2. apply ki_e_zs_zb. exact HfB.
      * rewrite Un by lia. exact E10.
    + (* entry i <> gi: untouched *)
      rewrite ki_e_upd_nth_ne by lia. rewrite Fout by lia. exact (HS i Hi).
  - rewrite Fout by lia. exact HN.
  - rewrite Fout by lia. exact HOV.
  - rewrite Fout by lia. exact HRF.
  - exact HK8.
  - intros i Hi. rewrite !Fout by lia. exact (HK i Hi).
  - intros i Hi. rewrite Fout by lia. exact (HKP i Hi).
  - rewrite Fout by lia. exact HNK.
  - rewrite Fout by lia. exact HG.
  - rewrite Fout by lia. exact HRD.
Qed.
