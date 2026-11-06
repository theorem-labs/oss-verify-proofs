(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3), segment S_MF_KROLE: the mconf block after the
   hit's three stores. A word of m_key.words matched (KR_HIT 0x868c8): the code stores g->role = role[i] (sw 0x86928,
   4 bytes at g + 0x10), g->role_set = 1 (sw 0x86948, 4 bytes at g + 0x14) and snprintf(g->role_file, 96, "%s",
   c->reading) (0x86960, the C string and its NUL at g + 0x3c), g = &c->seg[gi] = c + 256 gi. This file says: when
   the block held mc (sa_mconf) and the three ranges now hold those bytes, every other byte of the block kept, the
   block holds m_upd mc gi (ms_with_role r file) (SegModel's role branch of m_key). Gallina over readers only; no
   instruction is executed here, no image number appears. A walk lane of the image-B m_file-family owner's G2B. Image A's
   lib/A/Prog/m_file_s_krole_enc.v (the image-A m_file-family lane, commit e8a825b42b08)
   word for word; only this comment and the Require lines (image B's kit copies YA0n YG0f YG0n YG0d YCbq from
   lib.B, SegPgBase / SegABase from lib.B.Prog) differ: the struct offsets are seg_spec's, the same in both images. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* the three stores of the hit on the block at c: g->role holds r, g->role_set holds 1, g->role_file holds file and
   its NUL; every other byte of the block [c, c + 9236) kept *)
Definition kr_role_bytes (rd rd' : reader) (c : Z) (gi : nat) (r : Z) (file : list Z) : Prop :=
let g := seg_spec.mseg_addr c gi in
sa_val rd' (g + seg_spec.MS_ROLE) 4 r /\ sa_val rd' (g + seg_spec.MS_ROLE_SET) 4 1 /\
sa_zs rd' (g + seg_spec.MS_ROLE_FILE) (file ++ [0]) /\
(forall a, c <= a < c + seg_spec.SEG_M_SIZE ->
 ~ (g + seg_spec.MS_ROLE <= a < g + seg_spec.MS_ROLE_SET + 4) ->
 ~ (g + seg_spec.MS_ROLE_FILE <= a < g + seg_spec.MS_ROLE_FILE + Z.of_nat (length file) + 1) ->
 rd' a = rd a).

(* ============================== helpers: bytes, lists, fields ============================== *)
Lemma kre_byte_eq : forall b b' : byte, bv_unsigned b = bv_unsigned b' -> b = b'.
Proof. intros b b' H. apply bv_eq. exact H. Qed.

Lemma kre_byte_rng : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
intros b. pose proof (bv_unsigned_in_range _ b) as R. change (bv_modulus 8) with 256 in R. exact R.
Qed.

Lemma kre_unsigned_small : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof.
intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. exact Hz.
Qed.

Lemma kre_u64 : forall v, 0 <= v < 2 ^ 32 -> bv_unsigned (Z_to_bv 64 v) = v.
Proof.
intros v Hv. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
change (bv_modulus 64) with 18446744073709551616. change (2 ^ 32) with 4294967296 in Hv. lia.
Qed.

Lemma kre_le_byte_rng : forall v w k, 0 <= YG0f.le_byte v w k < 256.
Proof. intros v w k. unfold YG0f.le_byte. apply Z.mod_pos_bound. lia. Qed.

Lemma kre_rd_eq : forall (rd : reader) a a' (x y : Z), rd a = Some x -> rd a' = Some y -> a = a' -> x = y.
Proof. intros rd a a' x y E E' Ha. subst a'. rewrite E in E'. injection E' as E'. exact E'. Qed.

Lemma kre_nth_firstn : forall (A : Type) (l : list A) n k d, (k < n)%nat -> nth k (firstn n l) d = nth k l d.
Proof.
intros A l. induction l as [|x l IH]; intros n k d Hk; destruct n as [|n]; try lia.
- destruct k; reflexivity.
- destruct k as [|k]; cbn [firstn nth]; [reflexivity|]. apply IH. lia.
Qed.

Lemma kre_nth_skipn : forall (A : Type) (l : list A) off k d, nth k (skipn off l) d = nth (off + k) l d.
Proof.
intros A l off. revert l. induction off as [|off IH]; intros l k d; [reflexivity|].
destruct l as [|x l]; cbn [skipn].
- destruct k; reflexivity.
- change (nth (S off + k) (x :: l) d) with (nth (off + k) l d). apply IH.
Qed.

Lemma kre_fld_nth : forall off n (L : list byte) k, (k < n)%nat ->
  nth k (seg_spec.fld off n L) ZB0 = nth (off + k) L ZB0.
Proof. intros off n L k Hk. unfold seg_spec.fld. rewrite kre_nth_firstn by exact Hk. apply kre_nth_skipn. Qed.

Lemma kre_fld_length : forall off n (L : list byte), (off + n <= length L)%nat -> length (seg_spec.fld off n L) = n.
Proof. intros off n L H. unfold seg_spec.fld. rewrite length_firstn, length_skipn. lia. Qed.

(* a field none of whose bytes changed is unchanged *)
Lemma kre_fld_ext : forall (L L' : list byte) off n, length L' = length L ->
  (forall j, (off <= j < off + n)%nat -> (j < length L)%nat -> nth j L' ZB0 = nth j L ZB0) ->
  seg_spec.fld off n L' = seg_spec.fld off n L.
Proof.
intros L L' off n HL H. unfold seg_spec.fld. apply (nth_ext _ _ ZB0 ZB0).
- rewrite !length_firstn, !length_skipn, HL. reflexivity.
- intros k Hk. rewrite length_firstn, length_skipn in Hk.
  rewrite !kre_nth_firstn by lia. rewrite !kre_nth_skipn. apply H; lia.
Qed.

Lemma kre_nth_zs : forall (L : list byte) k, (k < length L)%nat -> nth k (seg_spec.zs L) 0 = bv_unsigned (nth k L ZB0).
Proof.
intros L. unfold seg_spec.zs. induction L as [|b L IH]; intros k Hk; [cbn in Hk; lia|].
destruct k as [|k]; cbn [map nth]; [reflexivity|]. apply IH. cbn in Hk. lia.
Qed.

Lemma kre_nth_map_seq : forall (f : nat -> byte) n s i, (i < n)%nat -> nth i (map f (seq s n)) ZB0 = f (s + i)%nat.
Proof.
intros f n. induction n as [|n IH]; intros s i Hi; [lia|].
destruct i as [|i]; cbn [seq map nth]; [f_equal; lia|].
rewrite IH by lia. f_equal. lia.
Qed.

Lemma kre_nth_map_seq0 : forall (f : nat -> byte) n i, (i < n)%nat -> nth i (map f (seq 0 n)) ZB0 = f i.
Proof. intros f n i Hi. exact (kre_nth_map_seq f n 0 i Hi). Qed.

(* little-endian bytes *)
Lemma kre_len_le_bytes : forall n z, length (Z_to_le_bytes n z) = n.
Proof. induction n as [|n IH]; intros z; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma kre_nth_le_bytes : forall n z k, (k < n)%nat ->
  nth k (Z_to_le_bytes n z) ZB0 = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros z k Hk; [lia|].
destruct k as [|k]; cbn [Z_to_le_bytes nth].
- change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
- rewrite IH by lia. rewrite Z.shiftr_shiftr by lia.
  replace (8 + 8 * Z.of_nat k) with (8 * Z.of_nat (S k)) by lia. reflexivity.
Qed.

Lemma kre_le_bytes : forall (L : list byte) n v, length L = n -> 0 <= v < 2 ^ (8 * Z.of_nat n) ->
  (forall k, (k < n)%nat -> bv_unsigned (nth k L ZB0) = YG0f.le_byte v n k) -> L = Z_to_le_bytes n v.
Proof.
intros L n v HL Hv H. apply (nth_ext _ _ ZB0 ZB0).
- rewrite HL, kre_len_le_bytes. reflexivity.
- intros k Hk. rewrite HL in Hk. rewrite kre_nth_le_bytes by exact Hk.
  apply bv_eq. rewrite (H k Hk), Z_to_bv_unsigned. unfold YG0f.le_byte, bv_wrap.
  rewrite (Z.mod_small v (2 ^ (8 * Z.of_nat n)) Hv). change (bv_modulus 8) with 256. reflexivity.
Qed.

Lemma kre_u32 : forall (L : list byte) v, length L = 4%nat -> 0 <= v < 2 ^ 32 ->
  (forall k, (k < 4)%nat -> bv_unsigned (nth k L ZB0) = YG0f.le_byte v 4 k) -> seg_spec.u32_enc v L.
Proof.
intros L v HL Hv H. unfold seg_spec.u32_enc. split; [exact Hv|].
change (L = Z_to_le_bytes 4 (bv_unsigned (Z_to_bv 64 v))).
rewrite (kre_u64 v Hv). apply kre_le_bytes; [exact HL | exact Hv | exact H].
Qed.

Lemma kre_flag1 : forall (L : list byte), length L = 4%nat ->
  (forall k, (k < 4)%nat -> bv_unsigned (nth k L ZB0) = YG0f.le_byte 1 4 k) -> seg_spec.flag_enc true L.
Proof.
intros L HL H. assert (H1 : 0 <= 1 < 2 ^ 32) by (change (2 ^ 32) with 4294967296; lia).
exact (proj2 (kre_u32 L 1 HL H1 H)).
Qed.

(* SegModel's upd_nth *)
Lemma kre_upd_len : forall (A : Type) i (f : A -> A) l, length (upd_nth i f l) = length l.
Proof.
intros A i f l. revert i. induction l as [|x l IH]; intros [|i]; cbn [upd_nth length]; try reflexivity.
rewrite IH. reflexivity.
Qed.

Lemma kre_upd_nth_ne : forall (A : Type) i j (f : A -> A) l d, i <> j -> nth j (upd_nth i f l) d = nth j l d.
Proof.
intros A i j f l d. revert i j. induction l as [|x l IH]; intros i j Hij; [destruct i; reflexivity|].
destruct i as [|i], j as [|j]; cbn [upd_nth nth]; try reflexivity.
- exfalso. apply Hij. reflexivity.
- apply IH. intros E. apply Hij. rewrite E. reflexivity.
Qed.

Lemma kre_upd_nth_eq : forall (A : Type) i (f : A -> A) l d, (i < length l)%nat -> nth i (upd_nth i f l) d = f (nth i l d).
Proof.
intros A i f l d. revert i. induction l as [|x l IH]; intros i Hi; [cbn in Hi; lia|].
destruct i as [|i]; cbn [upd_nth nth]; [reflexivity|]. apply IH. cbn in Hi. lia.
Qed.

(* ============================== the segment the hit wrote ============================== *)
(* F is seg[gi]'s 256 bytes before, F' after: bytes [16, 24) hold role and role_set, bytes [60, 61 + |file|) the
   file and its NUL, every other byte is F's. *)
Lemma kre_mseg : forall (F F' : list byte) s r file,
  seg_spec.mseg_enc s F -> length F' = 256%nat ->
  (forall k, (k < 256)%nat -> (k < 16 \/ 24 <= k < 60 \/ 61 + length file <= k)%nat -> nth k F' ZB0 = nth k F ZB0) ->
  (forall k, (k < 4)%nat -> bv_unsigned (nth (16 + k) F' ZB0) = YG0f.le_byte r 4 k) ->
  (forall k, (k < 4)%nat -> bv_unsigned (nth (20 + k) F' ZB0) = YG0f.le_byte 1 4 k) ->
  (forall k, (k < S (length file))%nat -> bv_unsigned (nth (60 + k) F' ZB0) = nth k (file ++ [0]) 0) ->
  0 <= r < 2 ^ 31 -> ~ In 0 file -> (length file < 96)%nat ->
  seg_spec.mseg_enc (ms_with_role r file s) F'.
Proof.
intros F F' s r file Hs HL' Hsame Hr Hrs Hf Hr31 Hn0 Hlen.
destruct Hs as (HL & Hname & Hrole0 & Hrs0 & Hig & Higs & Hms & Hmodel & Hrf & Hif & Hgen).
assert (Hfe : forall off n, (off + n <= 256)%nat ->
  (forall j, (off <= j < off + n)%nat -> (j < 16 \/ 24 <= j < 60 \/ 61 + length file <= j)%nat) ->
  seg_spec.fld off n F' = seg_spec.fld off n F).
{ intros off n Hon Hj. apply kre_fld_ext; [lia|]. intros j Hj1 Hj2. apply Hsame; [lia | exact (Hj j Hj1)]. }
assert (Hr32 : 0 <= r < 2 ^ 32).
{ change (2 ^ 32) with 4294967296. change (2 ^ 31) with 2147483648 in Hr31. lia. }
unfold seg_spec.mseg_enc, seg_spec.role_enc. unfold ms_with_role.
cbn [ms_name ms_role ms_role_set ms_ignore ms_ignore_set ms_model_set ms_model ms_role_file ms_ignore_file ms_gen].
change (seg_spec.fldz seg_spec.MS_ROLE 4 F') with (seg_spec.fld 16 4 F').
change (seg_spec.fldz seg_spec.MS_ROLE_SET 4 F') with (seg_spec.fld 20 4 F').
change (seg_spec.fldz seg_spec.MS_ROLE_FILE 96 F') with (seg_spec.fld 60 96 F').
unfold seg_spec.fldz in *.
split; [exact HL'|].
split; [rewrite (Hfe 0%nat 16%nat) by (intros; lia); exact Hname|].
split.
{ split; [|exact (proj2 Hr31)]. apply kre_u32; [apply kre_fld_length; lia | exact Hr32 |].
  intros k Hk. rewrite kre_fld_nth by exact Hk. exact (Hr k Hk). }
split.
{ apply kre_flag1; [apply kre_fld_length; lia|].
  intros k Hk. rewrite kre_fld_nth by exact Hk. exact (Hrs k Hk). }
split; [rewrite (Hfe (Z.to_nat seg_spec.MS_IGNORE) (Z.to_nat 4)) by (cbv [seg_spec.MS_IGNORE]; intros; lia);
  exact Hig|].
split; [rewrite (Hfe (Z.to_nat seg_spec.MS_IGNORE_SET) (Z.to_nat 4)) by (cbv [seg_spec.MS_IGNORE_SET]; intros; lia);
  exact Higs|].
split; [rewrite (Hfe (Z.to_nat seg_spec.MS_MODEL_SET) (Z.to_nat 4)) by (cbv [seg_spec.MS_MODEL_SET]; intros; lia);
  exact Hms|].
split; [rewrite (Hfe (Z.to_nat seg_spec.MS_MODEL) (Z.to_nat 24)) by (cbv [seg_spec.MS_MODEL]; intros; lia);
  exact Hmodel|].
split.
{ unfold seg_spec.cstr_enc. split; [apply kre_fld_length; lia|]. split; [exact Hlen|]. split; [exact Hn0|].
  apply (nth_ext _ _ 0 0).
  - rewrite length_firstn. unfold seg_spec.zs. rewrite length_map, kre_fld_length by lia.
    rewrite length_app. cbn [length]. lia.
  - intros k Hk. rewrite length_firstn in Hk. unfold seg_spec.zs in Hk. rewrite length_map, kre_fld_length in Hk by lia.
    rewrite kre_nth_firstn by lia. rewrite kre_nth_zs by (rewrite kre_fld_length; lia).
    rewrite kre_fld_nth by lia. apply Hf. lia. }
split; [rewrite (Hfe (Z.to_nat seg_spec.MS_IGNORE_FILE) (Z.to_nat 96))
  by (cbv [seg_spec.MS_IGNORE_FILE]; intros; lia); exact Hif|].
rewrite (Hfe (Z.to_nat seg_spec.MS_GEN) (Z.to_nat 4)) by (cbv [seg_spec.MS_GEN]; intros; lia). exact Hgen.
Qed.

Ltac kre_lia := unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE, seg_spec.MS_ROLE, seg_spec.MS_ROLE_SET,
  seg_spec.MS_ROLE_FILE, seg_spec.SEG_M_SIZE in *; lia.

Lemma kr_mconf_role : forall rd rd' c mc gi r file,
  sa_mconf rd c mc -> (gi < length (mc_seg mc))%nat -> 0 <= r < 2 ^ 31 ->
  ~ In 0 file -> Forall (fun x => 0 <= x < 256) file -> (length file < 96)%nat ->
  kr_role_bytes rd rd' c gi r file ->
  sa_mconf rd' c (m_upd mc gi (ms_with_role r file)).
Proof.
intros rd rd' c mc gi r file Hmc Hgi Hr Hn0 Hrng Hlen Hkr.
destruct Hmc as [bs [Hbs Henc]].
destruct Henc as (HL & H32 & Hsegs & HN & HOv & HRef & HK8 & HKept & HKnock & HNK & HGen & HRd).
destruct Hkr as (Hrole & Hset & Hfile & Hkeep).
assert (HLn : Z.of_nat (length bs) = 9236) by exact HL.
assert (Hfr : Forall (fun x => 0 <= x < 256) (file ++ [0]))
  by (apply Forall_app; split; [exact Hrng | constructor; [cbv beta; lia | constructor]]).
(* every byte of the block is mapped under rd' and is a byte value *)
assert (Hsome : forall j, (j < length bs)%nat -> exists z, rd' (c + Z.of_nat j) = Some z /\ 0 <= z < 256).
{ intros j Hj.
  destruct (Nat.lt_ge_cases j (256 * gi + 16)) as [J1|J1].
  { exists (bv_unsigned (nth j bs ZB0)). split; [|apply kre_byte_rng].
    rewrite Hkeep by kre_lia. exact (Hbs j Hj). }
  destruct (Nat.lt_ge_cases j (256 * gi + 20)) as [J2|J2].
  { exists (YG0f.le_byte r 4 (j - (256 * gi + 16))). split; [|apply kre_le_byte_rng].
    rewrite <- (Hrole (j - (256 * gi + 16))%nat) by lia. f_equal. kre_lia. }
  destruct (Nat.lt_ge_cases j (256 * gi + 24)) as [J3|J3].
  { exists (YG0f.le_byte 1 4 (j - (256 * gi + 20))). split; [|apply kre_le_byte_rng].
    rewrite <- (Hset (j - (256 * gi + 20))%nat) by lia. f_equal. kre_lia. }
  destruct (Nat.lt_ge_cases j (256 * gi + 60)) as [J4|J4].
  { exists (bv_unsigned (nth j bs ZB0)). split; [|apply kre_byte_rng].
    rewrite Hkeep by kre_lia. exact (Hbs j Hj). }
  destruct (Nat.lt_ge_cases j (256 * gi + 61 + length file)) as [J5|J5].
  { exists (nth (j - (256 * gi + 60)) (file ++ [0]) 0). split.
    - rewrite <- (Hfile (j - (256 * gi + 60))%nat) by (rewrite length_app; cbn [length]; lia). f_equal. kre_lia.
    - rewrite Forall_forall in Hfr. apply Hfr. apply nth_In. rewrite length_app. cbn [length]. lia. }
  exists (bv_unsigned (nth j bs ZB0)). split; [|apply kre_byte_rng].
  rewrite Hkeep by kre_lia. exact (Hbs j Hj). }
(* the block's bytes under rd' *)
assert (Hb' : exists bs', length bs' = length bs /\ sa_bytes rd' c bs').
{ exists (map (fun j => Z_to_bv 8 (match rd' (c + Z.of_nat j) with Some z => z | None => 0 end)) (seq 0 (length bs))).
  split; [rewrite length_map, length_seq; reflexivity|].
  intros j Hj. rewrite length_map, length_seq in Hj.
  rewrite kre_nth_map_seq0 by exact Hj. cbv beta.
  destruct (Hsome j Hj) as [z [E R]]. rewrite E. cbv beta iota.
  rewrite kre_unsigned_small by exact R. reflexivity. }
destruct Hb' as [bs' [HL' Hbs']].
(* outside the three stores the bytes are the old ones *)
assert (Hsame : forall j, (j < length bs)%nat ->
  (Z.of_nat j < 256 * Z.of_nat gi + 16 \/ 256 * Z.of_nat gi + 24 <= Z.of_nat j < 256 * Z.of_nat gi + 60 \/
   256 * Z.of_nat gi + 61 + Z.of_nat (length file) <= Z.of_nat j) ->
  nth j bs' ZB0 = nth j bs ZB0).
{ intros j Hj Hc. apply kre_byte_eq.
  assert (Hj' : (j < length bs')%nat) by lia.
  pose proof (Hbs' j Hj') as E'. rewrite Hkeep in E' by kre_lia. rewrite (Hbs j Hj) in E'.
  injection E' as E'. symmetry. exact E'. }
assert (Hfar : forall off n, 8192 <= Z.of_nat off -> seg_spec.fld off n bs' = seg_spec.fld off n bs).
{ intros off n Ho. apply kre_fld_ext; [lia|]. intros j Hj1 Hj2. apply Hsame; [exact Hj2|]. lia. }
exists bs'. split; [exact Hbs'|].
unfold seg_spec.mconf_encp, m_upd, m_set_segs.
cbn [mc_seg mc_overflow mc_refused mc_kept mc_gen mc_reading].
rewrite !kre_upd_len.
split; [rewrite HL'; exact HL|].
split; [exact H32|].
split.
{ intros i Hi.
  destruct (Nat.eq_dec i gi) as [->|Hne].
  - rewrite kre_upd_nth_eq by exact Hi.
    apply kre_mseg with (F := seg_spec.fld (256 * gi) 256 bs).
    + exact (Hsegs gi Hi).
    + apply kre_fld_length. lia.
    + intros k Hk Hc. rewrite !kre_fld_nth by exact Hk. apply Hsame; lia.
    + intros k Hk. rewrite kre_fld_nth by lia.
      apply (kre_rd_eq rd' _ _ _ _ (Hbs' (256 * gi + (16 + k))%nat ltac:(lia)) (Hrole k Hk)). kre_lia.
    + intros k Hk. rewrite kre_fld_nth by lia.
      apply (kre_rd_eq rd' _ _ _ _ (Hbs' (256 * gi + (20 + k))%nat ltac:(lia)) (Hset k Hk)). kre_lia.
    + intros k Hk. rewrite kre_fld_nth by lia.
      apply (kre_rd_eq rd' _ _ _ _ (Hbs' (256 * gi + (60 + k))%nat ltac:(lia))
        (Hfile k ltac:(rewrite length_app; cbn [length]; lia))). kre_lia.
    + exact Hr.
    + exact Hn0.
    + exact Hlen.
  - rewrite kre_upd_nth_ne by lia.
    rewrite (kre_fld_ext bs bs'); [exact (Hsegs i Hi) | lia |].
    intros j Hj1 Hj2. apply Hsame; [exact Hj2|]. lia. }
split; [unfold seg_spec.fldz; rewrite Hfar by (cbv [seg_spec.MC_N]; lia); exact HN|].
split; [unfold seg_spec.fldz; rewrite Hfar by (cbv [seg_spec.MC_OVERFLOW]; lia); exact HOv|].
split; [unfold seg_spec.fldz; rewrite Hfar by (cbv [seg_spec.MC_REFUSED]; lia); exact HRef|].
split; [exact HK8|].
split; [intros i Hi; rewrite !Hfar by (cbv [seg_spec.MC_KEPT seg_spec.MC_KNOCK]; lia); exact (HKept i Hi)|].
split; [intros i Hi; rewrite Hfar by (cbv [seg_spec.MC_KNOCK]; lia); exact (HKnock i Hi)|].
split; [unfold seg_spec.fldz; rewrite Hfar by (cbv [seg_spec.MC_NKEPT]; lia); exact HNK|].
split; [unfold seg_spec.fldz; rewrite Hfar by (cbv [seg_spec.MC_GEN]; lia); exact HGen|].
unfold seg_spec.fldz. rewrite Hfar by (cbv [seg_spec.MC_READING]; lia). exact HRd.
Qed.

Print Assumptions kr_mconf_role.
