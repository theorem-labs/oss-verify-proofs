(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): reac_segconf_parse_file, segment B3 of
   the walk (the B3 segment lane of the image-B G3 walk owner, 2026-10-30). The PURE facts the segment needs: no PAImg, no symbolic
   executor, no machine state. ADAPTED (a copy, module paths to image B's kit) from the image-A G3 walk owner's image-A file
   lib/A/Prog/pf_a3_f.v (commit 0ce74e7a4f39, the image-A A3 segment lane), whose lemmas are image-independent:
   1. the format "%s" and what snprintf(dst, 96, "%s", L) stores (b3f_F_s, b3f_reading);
   2. a C string read through a byte-valued reader has byte range and no NUL (b3f_str_range, b3f_str_pos);
   3. the gen field read out of the record encoding (b3f_rconf_gen_val);
   4. the record after snprintf wrote the reading field (b3f_rconf_reading);
   5. the record after the inline c->gen++ (b3f_rconf_gen);
   6. the two together are pf_start (b3f_pf_start_eq);
   7. the empty text (b3f_s_nil, b3f_lines_nil);
   8. r_parse_file through pf_start (b3f_parse_fst, b3f_parse_snd, b3f_parse_done);
   9. the counters at the loop head (b3f_cnt_start);
   10. the empty cur_name buffer (b3f_nm_nil).
   4 and 5 follow the unit owner's plain lane lib/Prog/pf_p1.v (pf1_fld_* and pf1_enc_reading / pf1_enc_gen), as the A
   file says; L_parse_start_holds and pf_cnt_start come from lib/Prog/pfA_facts.v (Required, not re-proved).
   Requires: Lib/Mem.v (le4) and image B's kit copy lib/B/YG0f.v (reader, le_byte); SegABase is image B's copy
   lib/B/Prog/SegABase.v. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Mem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import seg_spec pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegABase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

(* ========================================= list helpers ========================================= *)
Lemma b3f_app_nth1 {A} : forall (l l' : list A) (d : A) (n : nat), (n < length l)%nat ->
  nth n (l ++ l') d = nth n l d.
Proof. intros l l' d n H. apply app_nth1. exact H. Qed.

Lemma b3f_app_nth2 {A} : forall (l l' : list A) (d : A) (n : nat), (length l <= n)%nat ->
  nth n (l ++ l') d = nth (n - length l) l' d.
Proof. intros l l' d n H. apply app_nth2. lia. Qed.

Lemma b3f_nth_skipn {A} : forall (k n : nat) (l : list A) (d : A), nth n (skipn k l) d = nth (k + n) l d.
Proof.
  induction k as [|k IH]; intros n l d; [reflexivity|].
  destruct l as [|x l].
  - destruct n; reflexivity.
  - exact (IH n l d).
Qed.

Lemma b3f_nth_firstn {A} : forall (n k : nat) (l : list A) (d : A), (k < n)%nat ->
  nth k (firstn n l) d = nth k l d.
Proof.
  induction n as [|n IH]; intros k l d Hk; [lia|].
  destruct l as [|x l]; [reflexivity|].
  destruct k as [|k]; [reflexivity|].
  cbn [firstn nth]. apply IH. lia.
Qed.

Lemma b3f_nth_repeat {A} : forall (x : A) (n i : nat), nth i (repeat x n) x = x.
Proof. intros x n. induction n as [|n IH]; intros [|i]; cbn; auto. Qed.

Lemma b3f_app_split {A} : forall (l : list A) (k : nat), (k <= length l)%nat ->
  exists l1 l2, l = l1 ++ l2 /\ length l1 = k.
Proof.
  intros l k H. exists (firstn k l), (skipn k l).
  split; [symmetry; apply firstn_skipn | rewrite length_firstn; lia].
Qed.

(* the byte i of P ++ R' ++ T, where R' replaces R of the same length *)
Lemma b3f_nth_mid {A} : forall (P R R' T : list A) (i : nat) (d : A), length R' = length R ->
  nth i (P ++ R' ++ T) d =
  if (length P <=? i)%nat && (i <? length P + length R)%nat then nth (i - length P) R' d
  else nth i (P ++ R ++ T) d.
Proof.
  intros P R R' T i d LR.
  destruct (Nat.leb_spec (length P) i) as [H1|H1]; cbn [andb].
  - rewrite (b3f_app_nth2 P (R' ++ T) d i H1), (b3f_app_nth2 P (R ++ T) d i H1).
    destruct (Nat.ltb_spec i (length P + length R)) as [H2|H2].
    + rewrite (b3f_app_nth1 R' T d) by lia. reflexivity.
    + rewrite (b3f_app_nth2 R' T d) by lia. rewrite (b3f_app_nth2 R T d) by lia. rewrite LR. reflexivity.
  - rewrite (b3f_app_nth1 P (R' ++ T) d i H1), (b3f_app_nth1 P (R ++ T) d i H1). reflexivity.
Qed.

(* the byte i of P ++ (W ++ skipn k R) ++ T: W written over the first k bytes of R *)
Lemma b3f_nth_splice {A} : forall (P R W T : list A) (k i : nat) (d : A),
  length W = k -> (k <= length R)%nat ->
  nth i (P ++ (W ++ skipn k R) ++ T) d =
  if (length P <=? i)%nat && (i <? length P + k)%nat then nth (i - length P) W d
  else nth i (P ++ R ++ T) d.
Proof.
  intros P R W T k i d LW Hk.
  assert (LM : length (W ++ skipn k R) = length R) by (rewrite length_app, length_skipn; lia).
  destruct (Nat.leb_spec (length P) i) as [H1|H1]; cbn [andb].
  - rewrite (b3f_app_nth2 P ((W ++ skipn k R) ++ T) d i H1), (b3f_app_nth2 P (R ++ T) d i H1).
    destruct (Nat.ltb_spec i (length P + k)) as [H2|H2].
    + rewrite (b3f_app_nth1 (W ++ skipn k R) T d) by (rewrite LM; lia).
      rewrite (b3f_app_nth1 W (skipn k R) d) by (rewrite LW; lia). reflexivity.
    + destruct (Nat.ltb_spec (i - length P) (length R)) as [H3|H3].
      * rewrite (b3f_app_nth1 (W ++ skipn k R) T d) by (rewrite LM; lia).
        rewrite (b3f_app_nth1 R T d) by lia.
        rewrite (b3f_app_nth2 W (skipn k R) d) by (rewrite LW; lia). rewrite LW.
        rewrite b3f_nth_skipn. f_equal. lia.
      * rewrite (b3f_app_nth2 (W ++ skipn k R) T d) by (rewrite LM; lia).
        rewrite (b3f_app_nth2 R T d) by lia. rewrite LM. reflexivity.
  - rewrite (b3f_app_nth1 P ((W ++ skipn k R) ++ T) d i H1), (b3f_app_nth1 P (R ++ T) d i H1). reflexivity.
Qed.

Lemma b3f_nth_range : forall (l : list Z) (j : nat), Forall (fun x => 0 <= x < 256) l -> 0 <= nth j l 0 < 256.
Proof.
  induction l as [|x l IH]; intros j H; [destruct j; cbn; lia|].
  inversion H as [|? ? Hx Hl]; subst. destruct j as [|j]; [exact Hx|]. cbn [nth]. apply IH. exact Hl.
Qed.

(* ========================================= byte helpers ========================================= *)
Lemma b3f_u8 : forall z, bv_unsigned (Z_to_bv 8 z) = z mod 256.
Proof. intros z. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. reflexivity. Qed.

Lemma b3f_u8_small : forall x, 0 <= x < 256 -> bv_unsigned (Z_to_bv 8 x) = x.
Proof. intros x Hx. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia. Qed.

Lemma b3f_zs_zb : forall l : list Z, Forall (fun x => 0 <= x < 256) l ->
  map bv_unsigned (map (Z_to_bv 8) l) = l.
Proof.
  induction l as [|x l IH]; intros H; [reflexivity|]. inversion H as [|? ? Hx Hl]; subst.
  cbn [map]. rewrite (IH Hl). f_equal. apply b3f_u8_small. exact Hx.
Qed.

Lemma b3f_Z_to_le_bytes_nth : forall (n : nat) (z : Z) (k : nat), 0 <= z -> (k < n)%nat ->
  bv_unsigned (nth k (Z_to_le_bytes n z) ZB0) = Z.shiftr z (8 * Z.of_nat k) mod 256.
Proof.
  induction n as [|n IH]; intros z k Hz Hk; [lia|].
  cbn [Z_to_le_bytes]. destruct k as [|k].
  - cbn [nth]. rewrite b3f_u8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
  - cbn [nth]. rewrite IH by (try apply Z.shiftr_nonneg; lia).
    rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.

(* the 4 little-endian bytes of a u32 field (seg_spec.u32_enc) are le_byte's (SegABase.sa_val) *)
Lemma b3f_le4_nth : forall (v : Z) (k : nat), 0 <= v < 2 ^ 32 -> (k < 4)%nat ->
  bv_unsigned (nth k (le4 (Z_to_bv 64 v)) ZB0) = le_byte v 4 k.
Proof.
  intros v k Hv Hk. unfold le4.
  rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia).
  rewrite b3f_Z_to_le_bytes_nth by lia.
  unfold le_byte. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32).
  rewrite (Z.mod_small v (2 ^ 32)) by lia. reflexivity.
Qed.

(* ===================================== fields of struct reac_segconf ===================================== *)
Lemma b3f_fld_nth : forall (off n k : nat) (bs : list byte) (d : byte), (k < n)%nat ->
  nth k (fld off n bs) d = nth (off + k) bs d.
Proof. intros off n k bs d Hk. unfold fld. rewrite b3f_nth_firstn by exact Hk. apply b3f_nth_skipn. Qed.

Lemma b3f_fld_app_l : forall (l1 l2 : list byte) off n, (off + n <= length l1)%nat ->
  fld off n (l1 ++ l2) = fld off n l1.
Proof.
  intros l1 l2 off n H. unfold fld. rewrite skipn_app, firstn_app, length_skipn.
  replace (n - (length l1 - off))%nat with 0%nat by lia. rewrite firstn_O, app_nil_r. reflexivity.
Qed.

Lemma b3f_fld_app_r : forall (l1 l2 : list byte) off n, (length l1 <= off)%nat ->
  fld off n (l1 ++ l2) = fld (off - length l1) n l2.
Proof. intros l1 l2 off n H. unfold fld. rewrite skipn_app, (skipn_all2 l1) by lia. reflexivity. Qed.

Lemma b3f_fld_full : forall (l : list byte) off n, off = 0%nat -> length l = n -> fld off n l = l.
Proof. intros l off n -> <-. unfold fld. rewrite skipn_O. apply firstn_all. Qed.

Lemma b3f_fld_lo : forall (P A B : list byte) off n, (off + n <= length P)%nat ->
  fld off n (P ++ A) = fld off n (P ++ B).
Proof. intros. rewrite !b3f_fld_app_l by lia. reflexivity. Qed.

Lemma b3f_fld_rd : forall (P Y G Q : list byte), Z.of_nat (length P) = 16512 -> length Y = 96%nat ->
  fld (Z.to_nat 16512) (Z.to_nat 96) (P ++ Y ++ G ++ Q) = Y.
Proof.
  intros P Y G Q LP LY. rewrite b3f_fld_app_r by lia. rewrite b3f_fld_app_l by lia. apply b3f_fld_full; lia.
Qed.

Lemma b3f_fld_gen : forall (P Y G Q : list byte), Z.of_nat (length P) = 16512 -> length Y = 96%nat ->
  length G = 4%nat -> fld (Z.to_nat 16608) (Z.to_nat 4) (P ++ Y ++ G ++ Q) = G.
Proof.
  intros P Y G Q LP LY LG. rewrite b3f_fld_app_r by lia. rewrite b3f_fld_app_r by lia.
  rewrite b3f_fld_app_l by lia. apply b3f_fld_full; lia.
Qed.

Lemma b3f_fld_at : forall (P' G Q : list byte), Z.of_nat (length P') = 16608 -> length G = 4%nat ->
  fld (Z.to_nat 16608) (Z.to_nat 4) (P' ++ G ++ Q) = G.
Proof.
  intros P' G Q LP LG. rewrite b3f_fld_app_r by lia. rewrite b3f_fld_app_l by lia. apply b3f_fld_full; lia.
Qed.

Ltac b3f_rcn := unfold RC_N, RC_REFUSAL, RC_NREF, RC_REFUSED, RC_OVERFLOW, RC_READING, RC_GEN, SEG_C_SIZE in *.

(* snprintf's text at c->reading: the reading field holds it, every other field is the old one *)
Lemma b3f_enc_reading : forall rc P R G Q Tw, rconf_enc rc (P ++ R ++ G ++ Q) ->
  Z.of_nat (length P) = 16512 -> length R = 96%nat -> length G = 4%nat -> length Q = 4%nat ->
  (length Tw < 96)%nat -> ~ In 0 Tw -> Forall (fun x => 0 <= x < 256) Tw ->
  rconf_enc (RConf (rc_seg rc) (rc_refusal rc) (rc_refused rc) (rc_overflow rc) Tw (rc_gen rc))
    (P ++ (zb (Tw ++ [0]) ++ skipn (S (length Tw)) R) ++ G ++ Q).
Proof.
  intros rc P R G Q Tw (HL & HS & HSeg & HN & HR & HRef & HNR & HRd & HOv & HRead & HG) LP LR LG LQ LT NT BT.
  set (X := zb (Tw ++ [0]) ++ skipn (S (length Tw)) R).
  assert (LX : length X = 96%nat).
  { unfold X, zb. rewrite length_app, length_map, length_app, length_skipn. cbn [length]. lia. }
  unfold rconf_enc, fldz in *. cbn [rc_seg rc_refusal rc_refused rc_overflow rc_reading rc_gen]. b3f_rcn.
  rewrite !length_app in HL.
  split; [rewrite !length_app; lia|].
  split; [exact HS|].
  split; [intros i Hi; rewrite (b3f_fld_lo P _ (R ++ G ++ Q)) by lia; exact (HSeg i Hi)|].
  split; [rewrite (b3f_fld_lo P _ (R ++ G ++ Q)) by lia; exact HN|].
  split; [exact HR|].
  split; [intros i Hi; rewrite (b3f_fld_lo P _ (R ++ G ++ Q)) by lia; exact (HRef i Hi)|].
  split; [rewrite (b3f_fld_lo P _ (R ++ G ++ Q)) by lia; exact HNR|].
  split; [rewrite (b3f_fld_lo P _ (R ++ G ++ Q)) by lia; exact HRd|].
  split; [rewrite (b3f_fld_lo P _ (R ++ G ++ Q)) by lia; exact HOv|].
  split.
  - rewrite (b3f_fld_rd P X G Q LP LX). unfold cstr_enc.
    split; [exact LX|]. split; [exact LT|]. split; [exact NT|].
    unfold X, zs, zb. rewrite map_app, b3f_zs_zb.
    + rewrite firstn_app, length_app. cbn [length].
      replace (S (length Tw) - (length Tw + 1))%nat with 0%nat by lia.
      rewrite firstn_O, app_nil_r. apply firstn_all2. rewrite length_app. cbn [length]. lia.
    + apply Forall_app. split; [exact BT | constructor; [lia | constructor]].
  - rewrite (b3f_fld_gen P X G Q LP LX LG). rewrite (b3f_fld_gen P R G Q LP LR LG) in HG. exact HG.
Qed.

(* c->gen++: the gen field holds gen + 1, every other field is the old one *)
Lemma b3f_enc_gen : forall rcA P' G Q, rconf_enc rcA (P' ++ G ++ Q) ->
  Z.of_nat (length P') = 16608 -> length G = 4%nat -> length Q = 4%nat -> rc_gen rcA + 1 < 2 ^ 32 ->
  rconf_enc (RConf (rc_seg rcA) (rc_refusal rcA) (rc_refused rcA) (rc_overflow rcA) (rc_reading rcA) (rc_gen rcA + 1))
    (P' ++ le4 (Z_to_bv 64 (rc_gen rcA + 1)) ++ Q).
Proof.
  intros rcA P' G Q (HL & HS & HSeg & HN & HR & HRef & HNR & HRd & HOv & HRead & HG) LP LG LQ Hg.
  unfold rconf_enc, fldz in *. cbn [rc_seg rc_refusal rc_refused rc_overflow rc_reading rc_gen]. b3f_rcn.
  rewrite !length_app in HL.
  split; [rewrite !length_app, length_le4; lia|].
  split; [exact HS|].
  split; [intros i Hi; rewrite (b3f_fld_lo P' _ (G ++ Q)) by lia; exact (HSeg i Hi)|].
  split; [rewrite (b3f_fld_lo P' _ (G ++ Q)) by lia; exact HN|].
  split; [exact HR|].
  split; [intros i Hi; rewrite (b3f_fld_lo P' _ (G ++ Q)) by lia; exact (HRef i Hi)|].
  split; [rewrite (b3f_fld_lo P' _ (G ++ Q)) by lia; exact HNR|].
  split; [rewrite (b3f_fld_lo P' _ (G ++ Q)) by lia; exact HRd|].
  split; [rewrite (b3f_fld_lo P' _ (G ++ Q)) by lia; exact HOv|].
  split; [rewrite (b3f_fld_lo P' _ (G ++ Q)) by lia; exact HRead|].
  rewrite (b3f_fld_at P' G Q LP LG) in HG. rewrite (b3f_fld_at P' _ Q LP (length_le4 _)).
  destruct HG as [HG0 _]. split; [lia | reflexivity].
Qed.

(* ============================== 1. the format and what snprintf stores ============================== *)
Lemma b3f_F_s : F_s = [37; 115].
Proof. vm_compute. reflexivity. Qed.

Lemma b3f_reading : forall L : list Z, ~ In 0 L -> snprintf_s 96 F_s [AS L] = firstn 95 L.
Proof.
  intros L HL. unfold snprintf_s. rewrite b3f_F_s.
  change (fmt [37; 115] [AS L]) with (cut_nul L ++ []).
  rewrite cut_nul_id by exact HL. rewrite app_nil_r. reflexivity.
Qed.

(* ======================= 2. a C string through a byte-valued reader: range, no NUL ======================= *)
Lemma b3f_str_range : forall (rd : reader) (p : Z) (s : list Z),
  (forall a v, rd a = Some v -> 0 <= v < 256) -> sa_str rd p s ->
  Forall (fun x => 0 <= x < 256) s.
Proof.
  intros rd p s Hrd [[Hzs _] _]. apply Forall_forall. intros x Hx.
  destruct (In_nth s x 0 Hx) as [i [Hi Hn]].
  assert (Hi' : (i < length (s ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
  pose proof (Hzs i Hi') as E. rewrite (b3f_app_nth1 s [0] 0 i Hi) in E. rewrite Hn in E.
  exact (Hrd _ _ E).
Qed.

Lemma b3f_str_pos : forall (rd : reader) (p : Z) (s : list Z),
  (forall a v, rd a = Some v -> 0 <= v < 256) -> sa_str rd p s ->
  Forall (fun x => 0 < x < 256) s.
Proof.
  intros rd p s Hrd Hs. pose proof (b3f_str_range rd p s Hrd Hs) as HR.
  destruct Hs as [[_ Hn0] _]. rewrite Forall_forall in HR |- *. intros x Hx.
  pose proof (HR x Hx) as Rx. assert (x <> 0) by (intros ->; exact (Hn0 Hx)). lia.
Qed.

(* ================================ 3. the gen field of the record ================================ *)
Lemma b3f_rconf_gen_val : forall (rd : reader) (c : Z) (rc : rconf),
  sa_rconf rd c rc ->
  0 <= rc_gen rc < 2 ^ 32 /\ sa_val rd (c + seg_spec.RC_GEN) 4 (rc_gen rc).
Proof.
  intros rd c rc (bs & Hb & Henc).
  destruct Henc as (HL & _ & _ & _ & _ & _ & _ & _ & _ & _ & HG).
  destruct HG as [Hg Hf].
  split; [exact Hg|].
  intros k Hk.
  assert (Hi : (Z.to_nat seg_spec.RC_GEN + k < length bs)%nat)
    by (unfold seg_spec.RC_GEN, seg_spec.SEG_C_SIZE in *; lia).
  pose proof (Hb _ Hi) as E.
  replace (c + Z.of_nat (Z.to_nat seg_spec.RC_GEN + k)) with (c + seg_spec.RC_GEN + Z.of_nat k) in E
    by (unfold seg_spec.RC_GEN; lia).
  rewrite E. f_equal.
  rewrite <- (b3f_fld_nth (Z.to_nat seg_spec.RC_GEN) (Z.to_nat 4) k bs ZB0) by lia.
  unfold fldz in Hf. rewrite Hf.
  apply b3f_le4_nth; [exact Hg | exact Hk].
Qed.

(* ================================ 4. the record after the reading snprintf ================================ *)
Lemma b3f_rconf_reading : forall (rd rd' : reader) (c : Z) (rc : rconf) (Tw : list Z),
  sa_rconf rd c rc ->
  (length Tw < 96)%nat -> ~ In 0 Tw -> Forall (fun x => 0 <= x < 256) Tw ->
  (forall i, 0 <= i < Z.of_nat (S (length Tw)) ->
     rd' (c + seg_spec.RC_READING + i) = Some (nth (Z.to_nat i) (Tw ++ [0]) 0)) ->
  (forall a, c <= a < c + seg_spec.SEG_C_SIZE ->
     ~ (c + seg_spec.RC_READING <= a < c + seg_spec.RC_READING + Z.of_nat (S (length Tw))) ->
     rd' a = rd a) ->
  sa_rconf rd' c (RConf (rc_seg rc) (rc_refusal rc) (rc_refused rc) (rc_overflow rc) Tw (rc_gen rc)).
Proof.
  intros rd rd' c rc Tw (bs & Hb & Henc) LT NT BT HW HF.
  pose proof Henc as HL. destruct HL as [HL _]. unfold seg_spec.SEG_C_SIZE in HL.
  destruct (b3f_app_split bs (Z.to_nat 16512) ltac:(lia)) as (P & T1 & -> & LP0).
  rewrite length_app in HL.
  destruct (b3f_app_split T1 96 ltac:(lia)) as (R & T2 & -> & LR).
  rewrite length_app in HL.
  destruct (b3f_app_split T2 4 ltac:(lia)) as (G & Q & -> & LG).
  rewrite length_app in HL.
  assert (LQ : length Q = 4%nat) by lia.
  assert (LP : Z.of_nat (length P) = 16512) by lia.
  clear LP0.
  set (W := zb (Tw ++ [0])).
  assert (LW : length W = S (length Tw)).
  { unfold W, zb. rewrite length_map, length_app. cbn [length]. lia. }
  exists (P ++ (W ++ skipn (S (length Tw)) R) ++ G ++ Q). split.
  - intros i Hi.
    assert (Hi' : (i < length (P ++ R ++ G ++ Q))%nat).
    { rewrite !length_app in Hi. rewrite !length_app. rewrite length_skipn, LW in Hi. lia. }
    assert (HiZ : Z.of_nat i < 16616) by (rewrite !length_app in Hi'; lia).
    rewrite (b3f_nth_splice P R W (G ++ Q) (S (length Tw)) i ZB0 LW) by lia.
    destruct (Nat.leb_spec (length P) i) as [H1|H1];
      destruct (Nat.ltb_spec i (length P + S (length Tw))) as [H2|H2]; cbn [andb].
    + unfold W, zb, ZB0. rewrite (map_nth (Z_to_bv 8) (Tw ++ [0]) 0 (i - length P)).
      pose proof (HW (Z.of_nat (i - length P)) ltac:(lia)) as E. rewrite Nat2Z.id in E.
      replace (c + seg_spec.RC_READING + Z.of_nat (i - length P)) with (c + Z.of_nat i) in E
        by (unfold seg_spec.RC_READING; lia).
      rewrite E. f_equal. symmetry. apply b3f_u8_small. apply b3f_nth_range.
      apply Forall_app. split; [exact BT | constructor; [lia | constructor]].
    + rewrite HF by (unfold seg_spec.SEG_C_SIZE, seg_spec.RC_READING; lia). exact (Hb i Hi').
    + rewrite HF by (unfold seg_spec.SEG_C_SIZE, seg_spec.RC_READING; lia). exact (Hb i Hi').
    + rewrite HF by (unfold seg_spec.SEG_C_SIZE, seg_spec.RC_READING; lia). exact (Hb i Hi').
  - exact (b3f_enc_reading rc P R G Q Tw Henc LP LR LG LQ LT NT BT).
Qed.

(* ================================ 5. the record after c->gen++ ================================ *)
Lemma b3f_rconf_gen : forall (rd rd' : reader) (c : Z) (rc : rconf),
  sa_rconf rd c rc -> rc_gen rc + 1 < 2 ^ 32 ->
  sa_val rd' (c + seg_spec.RC_GEN) 4 (rc_gen rc + 1) ->
  (forall a, c <= a < c + seg_spec.SEG_C_SIZE ->
     ~ (c + seg_spec.RC_GEN <= a < c + seg_spec.RC_GEN + 4) -> rd' a = rd a) ->
  sa_rconf rd' c (RConf (rc_seg rc) (rc_refusal rc) (rc_refused rc) (rc_overflow rc) (rc_reading rc) (rc_gen rc + 1)).
Proof.
  intros rd rd' c rc (bs & Hb & Henc) Hg1 HV HF.
  pose proof Henc as HL. destruct HL as [HL _]. unfold seg_spec.SEG_C_SIZE in HL.
  pose proof Henc as HG. destruct HG as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HG). destruct HG as [Hg0 _].
  destruct (b3f_app_split bs (Z.to_nat 16608) ltac:(lia)) as (P & T1 & -> & LP0).
  rewrite length_app in HL.
  destruct (b3f_app_split T1 4 ltac:(lia)) as (G & Q & -> & LG).
  rewrite length_app in HL.
  assert (LQ : length Q = 4%nat) by lia.
  assert (LP : Z.of_nat (length P) = 16608) by lia.
  clear LP0.
  set (V := le4 (Z_to_bv 64 (rc_gen rc + 1))).
  assert (LV : length V = length G) by (unfold V; rewrite length_le4; lia).
  exists (P ++ V ++ Q). split.
  - intros i Hi.
    assert (Hi' : (i < length (P ++ G ++ Q))%nat) by (rewrite !length_app in Hi; rewrite !length_app; lia).
    assert (HiZ : Z.of_nat i < 16616) by (rewrite !length_app in Hi'; lia).
    rewrite (b3f_nth_mid P G V Q i ZB0 LV).
    destruct (Nat.leb_spec (length P) i) as [H1|H1];
      destruct (Nat.ltb_spec i (length P + length G)) as [H2|H2]; cbn [andb].
    + pose proof (HV (i - length P)%nat ltac:(lia)) as E.
      replace (c + seg_spec.RC_GEN + Z.of_nat (i - length P)) with (c + Z.of_nat i) in E
        by (unfold seg_spec.RC_GEN; lia).
      rewrite E. f_equal. unfold V. symmetry. apply b3f_le4_nth; lia.
    + rewrite HF by (unfold seg_spec.SEG_C_SIZE, seg_spec.RC_GEN; lia). exact (Hb i Hi').
    + rewrite HF by (unfold seg_spec.SEG_C_SIZE, seg_spec.RC_GEN; lia). exact (Hb i Hi').
    + rewrite HF by (unfold seg_spec.SEG_C_SIZE, seg_spec.RC_GEN; lia). exact (Hb i Hi').
  - exact (b3f_enc_gen rc P G Q Henc LP LG LQ Hg1).
Qed.

(* ================================ 6. the two together are pf_start ================================ *)
Lemma b3f_pf_start_eq : forall (rc : rconf) (lab : option (list Z)) (L : list Z),
  L = match lab with Some l => l | None => S_base end -> ~ In 0 L ->
  pf_start rc lab =
  RConf (rc_seg rc) (rc_refusal rc) (rc_refused rc) (rc_overflow rc) (firstn 95 L) (rc_gen rc + 1).
Proof.
  intros rc lab L HLd NL. subst L. unfold pf_start.
  rewrite b3f_reading by exact NL. reflexivity.
Qed.

(* ========================================= 7. the empty text ========================================= *)
Lemma b3f_s_nil : forall s : list Z, ~ In 0 s -> hd0 s = 0 -> s = [].
Proof.
  intros [|b s] Hn H; [reflexivity|]. cbn [hd0] in H. subst b.
  exfalso. apply Hn. left. reflexivity.
Qed.

Lemma b3f_lines_nil : lines [] = [].
Proof. reflexivity. Qed.

(* ================================= 8. r_parse_file through pf_start ================================= *)
Lemma b3f_parse_fst : forall rc s lab,
  fst (r_parse_file rc s lab) = fst (fst (r_lines (pf_start rc lab, None, []) 0 (lines s))).
Proof. intros rc s lab. rewrite (L_parse_start_holds rc s lab). reflexivity. Qed.

Lemma b3f_parse_snd : forall rc s lab,
  snd (r_parse_file rc s lab) = Z.of_nat (length (rc_seg (fst (r_parse_file rc s lab)))).
Proof. intros rc s lab. rewrite (L_parse_start_holds rc s lab). reflexivity. Qed.

Lemma b3f_parse_done : forall rc s lab, s = [] -> fst (r_parse_file rc s lab) = pf_start rc lab.
Proof. intros rc s lab ->. rewrite b3f_parse_fst. reflexivity. Qed.

(* ================================== 9. the counters at the loop head ================================== *)
Lemma b3f_cnt_start : forall (rc : rconf) (lab : option (list Z)) (s : list Z),
  rc_refused rc + 2 ^ 17 < 2 ^ 32 -> rc_overflow rc + 2 ^ 17 < 2 ^ 32 ->
  (length s <= 65535)%nat -> pf_cnt (pf_start rc lab) (length s).
Proof. intros rc lab s H1 H2 H3. exact (pf_cnt_start rc lab (length s) H1 H2 H3). Qed.

(* ================================= 10. the empty cur_name buffer ================================= *)
Lemma b3f_nm_nil : forall (rd : reader) (a : Z),
  (forall i, 0 <= i < 16 -> rd (a + i) = Some 0) ->
  exists f : list byte, sa_bytes rd a f /\ seg_spec.cstr_enc 16 [] f.
Proof.
  intros rd a H. exists (repeat ZB0 16). split.
  - intros i Hi. rewrite repeat_length in Hi. rewrite (H (Z.of_nat i)) by lia. f_equal.
    rewrite b3f_nth_repeat. unfold ZB0. rewrite b3f_u8_small by lia. reflexivity.
  - unfold cstr_enc. split; [apply repeat_length|]. split; [cbn [length]; lia|]. split; [apply in_nil|].
    unfold zs, ZB0. cbn [length repeat map firstn app]. rewrite b3f_u8_small by lia. reflexivity.
Qed.
