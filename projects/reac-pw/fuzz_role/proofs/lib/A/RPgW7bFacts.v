(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb): the facts the assembly of the walk of
   LLVMFuzzerTestOneInput from G 0x80d14 to J 0x8165c uses besides its blocks: the model of case 0 (Model.ent_build
   on a case-0 turn is ent_headamp_key's key with its four parts joined uncut), the frame shadow patterns at G and
   J, the image ranges around the strings and the param table, the frame for locals' bounds, and the moves of a
   location list, a value and the read-only data across a memory step. Proves no function (kind: model lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgImgA RPgMem RPgSeg RPgW7bBase RPgW7bKit.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A.Rt Require Import WrapRo.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ====================== the model of a case-0 turn ====================== *)
Definition w7_sepb (p : Z) : list byte := if Z.testbit p 7 then [] else DOT.
Definition w7_pab (p : Z) : list byte := nth (Z.to_nat (p mod 8)) param [].
Definition w7_js (chs : list byte) (p : Z) : list byte := HPFX ++ chs ++ w7_sepb p ++ w7_pab p.

Lemma w7_param_len : forall p, (length (w7_pab p) <= 9)%nat.
Proof.
intros p. unfold w7_pab. pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as H.
assert (Hc : p mod 8 = 0 \/ p mod 8 = 1 \/ p mod 8 = 2 \/ p mod 8 = 3 \/ p mod 8 = 4 \/ p mod 8 = 5 \/ p mod 8 = 6 \/ p mod 8 = 7) by lia.
destruct Hc as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E; vm_compute; lia.
Qed.
Lemma w7_sep_len : forall p, (length (w7_sepb p) <= 1)%nat.
Proof. intros p. unfold w7_sepb. destruct (Z.testbit p 7); vm_compute; lia. Qed.
Lemma w7_hpfx_len : length HPFX = 13%nat.
Proof. reflexivity. Qed.

Lemma w7_join_part_small : forall t s, (length t + length s < 96)%nat -> join_part t s = t ++ s.
Proof.
intros t s H. unfold join_part.
destruct (Nat.leb_spec 96 (length t + length s)) as [H1|H1]; [lia|]. rewrite firstn_all. reflexivity.
Qed.
Lemma w7_join4 : forall a b c d, (length a + length b + length c + length d < 96)%nat ->
join_parts [a; b; c; d] = a ++ b ++ c ++ d.
Proof.
intros a b c d H. unfold join_parts. cbn [fold_left].
rewrite (w7_join_part_small [] a) by (cbn; lia). cbn [app].
rewrite (w7_join_part_small a b) by lia.
rewrite (w7_join_part_small (a ++ b) c) by (rewrite length_app; lia).
rewrite (w7_join_part_small ((a ++ b) ++ c) d) by (rewrite !length_app in *; lia).
rewrite <- !app_assoc. reflexivity.
Qed.

Lemma w7_len4 : forall a b c d : list byte, length a = 13%nat -> (length b <= 21)%nat -> (length c <= 1)%nat ->
(length d <= 9)%nat -> (length a + length b + length c + length d < 96)%nat.
Proof. intros a b c d Ha Hb Hc Hd. lia. Qed.

(* ent_build of a case-0 turn: the key ent_text makes of the four parts *)
Lemma w7_ent_build_0 : forall rr chs pb r, fst (fuzz_u8 rr) mod 10 = 0 -> (chs, pb, r) = rs_g_of rr ->
(length chs <= 21)%nat ->
ent_build rr = (ent_text (w7_js chs pb) true, r).
Proof.
intros rr chs pb r Hk Hg Hl. unfold ent_build. unfold rs_g_of in Hg.
destruct (fuzz_u8 rr) as [kd r1] eqn:E1. cbn [fst] in Hk. rewrite Hk. cbn [Z.to_nat].
unfold ent_headamp_key.
destruct (fuzz_u8 r1) as [c r2]. destruct (fuzz_u8 r2) as [p r3]. injection Hg as Hch Hpb Hr. subst.
unfold w7_js, w7_sepb, w7_pab. rewrite w7_join4; [reflexivity|].
apply w7_len4; [exact w7_hpfx_len | exact Hl | exact (w7_sep_len p) | exact (w7_param_len p)].
Qed.
Lemma w7_js_len : forall chs p, (length chs <= 21)%nat -> (length (w7_js chs p) <= 44)%nat.
Proof.
intros chs p H. unfold w7_js. rewrite !length_app, w7_hpfx_len.
pose proof (w7_param_len p). pose proof (w7_sep_len p). lia.
Qed.
Lemma w7_ent_text_js : forall chs p, (length chs <= 21)%nat ->
ent_text (w7_js chs p) true = Ent POD_STRING (Z.of_nat (length (w7_js chs p)) + 1) (w7_js chs p ++ [NUL]).
Proof.
intros chs p H. unfold ent_text. pose proof (w7_js_len chs p H).
rewrite firstn_all2 by lia. rewrite length_app. cbn [length]. f_equal. lia.
Qed.

(* ====================== the frame's shadow at G and at J ====================== *)
Lemma w7_PG : rs_PG = rm_sh true true false true false.
Proof. vm_compute. reflexivity. Qed.
(* the two patterns differ exactly where t and ch go out of scope (0x80e18 .. 0x80e50) *)
Lemma w7_PG_PJ : forall i, 0 <= i < 52 ->
(4 <= i < 16 \/ 20 <= i < 23 -> nth (Z.to_nat i) rs_PJ 0 = 0xf8) /\
(~ (4 <= i < 16 \/ 20 <= i < 23) -> nth (Z.to_nat i) rs_PJ 0 = nth (Z.to_nat i) rs_PG 0).
Proof.
intros i Hi.
assert (HB : forallb (fun j => let z := Z.of_nat j in
  (implb ((4 <=? z) && (z <? 16) || (20 <=? z) && (z <? 23)) (nth j rs_PJ 0 =? 0xf8)) &&
  (implb (negb ((4 <=? z) && (z <? 16) || (20 <=? z) && (z <? 23))) (nth j rs_PJ 0 =? nth j rs_PG 0))) (seq 0 52) = true)
by (vm_compute; reflexivity).
rewrite forallb_forall in HB. specialize (HB (Z.to_nat i) ltac:(apply in_seq; lia)). cbv beta zeta in HB.
rewrite Z2Nat.id in HB by lia. apply andb_prop in HB as [H1 H2].
split; intros Hc.
- apply Z.eqb_eq. destruct ((4 <=? i) && (i <? 16) || (20 <=? i) && (i <? 23)) eqn:E; [exact H1|].
  exfalso. apply Bool.orb_false_iff in E as [E1 E2].
  apply Bool.andb_false_iff in E1. apply Bool.andb_false_iff in E2.
  destruct E1 as [E1|E1]; [apply Z.leb_gt in E1 | apply Z.ltb_ge in E1];
  (destruct E2 as [E2|E2]; [apply Z.leb_gt in E2 | apply Z.ltb_ge in E2]); lia.
- apply Z.eqb_eq. destruct ((4 <=? i) && (i <? 16) || (20 <=? i) && (i <? 23)) eqn:E; [|exact H2].
  exfalso. apply Bool.orb_true_iff in E as [E|E]; apply andb_prop in E as [E1 E2];
  apply Z.leb_le in E1; apply Z.ltb_lt in E2; lia.
Qed.

(* ====================== image A's ranges ====================== *)
Definition w7_in_seg_b (lo hi : Z) : bool :=
existsb (fun sg => (Z.of_N (seg_base sg) <=? lo) && (hi <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) rsegs.
Lemma w7_in_seg : forall lo hi a, w7_in_seg_b lo hi = true -> lo <= a < hi -> in_img rsegs a.
Proof.
intros lo hi a Hb Ha. unfold w7_in_seg_b in Hb. apply existsb_exists in Hb as (sg & Hin & Hs).
apply andb_prop in Hs as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
exists sg. split; [exact Hin | lia].
Qed.
(* the read-only PT_LOAD holding the strings, and the .data.rel.ro part holding the param table *)
Lemma w7_img_ro : w7_in_seg_b 0x10000 0x2f634 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma w7_img_relro : w7_in_seg_b 0x9a0e8 0x9b000 = true.
Proof. vm_compute. reflexivity. Qed.

(* ====================== moves of facts across a memory step ====================== *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* e at J: e.type, e.size, the body's bytes, the NUL and the zeros after it *)
Lemma w7_e_bytes : forall (W : world rsegs) mJ F ntot (js : list byte),
ntot = Z.of_nat (length js) -> (length js <= 44)%nat ->
val_mem rsegs (mrestrict (w_H W) mJ) (F + 0xf0) 4 8 ->
val_mem rsegs (mrestrict (w_H W) mJ) (F + 0xf0 + 4) 4 (ntot + 1) ->
aview rsegs (w_H W) mJ (F + 0xf8 + ntot) = Some 0 ->
(forall j, (j < length js)%nat -> aview rsegs (w_H W) mJ (F + 0xf8 + Z.of_nat j) = Some (bv_unsigned (nth j js (Z_to_bv 8 0)))) ->
(forall j, (9 + length js <= j < 104)%nat -> aview rsegs (w_H W) mJ (F + 0xf0 + Z.of_nat j) = Some 0) ->
garr8 rsegs (mrestrict (w_H W) mJ) (F + 0xf0) (rs_u8s (ent_mem (Ent POD_STRING (ntot + 1) (js ++ [NUL])))).
Proof.
intros W mJ F ntot js Hn HL EA0 EA4 XB0 BJ ZJ.
apply (proj2 (rm_bytes_aview rsegs (w_H W) mJ (F + 0xf0) (ent_mem (Ent POD_STRING (ntot + 1) (js ++ [NUL]))))).
intros i Hi. unfold ent_mem in Hi |- *. cbn [e_type e_size e_body] in Hi |- *.
assert (E0 : length (le32 POD_STRING) = 4%nat) by (unfold le32; apply length_Z_to_le_bytes).
assert (E1 : length (le32 (ntot + 1)) = 4%nat) by (unfold le32; apply length_Z_to_le_bytes).
assert (Eb : length (js ++ [NUL]) = (length js + 1)%nat) by (rewrite length_app; reflexivity).
assert (HiL : (i < 104)%nat).
{ rewrite !length_app in Hi. unfold le32, zeros in Hi. rewrite !length_Z_to_le_bytes, repeat_length in Hi. cbn [length] in Hi. lia. }
clear Hi.
destruct (Nat.lt_ge_cases i 4) as [H1|H1].
{ rewrite app_nth1 by (rewrite E0; lia).
  exact (proj1 (rm_bytes_aview rsegs (w_H W) mJ (F + 0xf0) (Z_to_le_bytes 4 8)) (rm_bytes_of_val rsegs (w_H W) mJ (F + 0xf0) 4 8 EA0) i
    ltac:(rewrite length_Z_to_le_bytes; lia)). }
rewrite app_nth2 by (rewrite E0; lia). rewrite E0.
destruct (Nat.lt_ge_cases i 8) as [H2|H2].
{ rewrite app_nth1 by (rewrite E1; lia).
  pose proof (proj1 (rm_bytes_aview rsegs (w_H W) mJ (F + 0xf0 + 4) (Z_to_le_bytes 4 (ntot + 1))) (rm_bytes_of_val rsegs (w_H W) mJ (F + 0xf0 + 4) 4 (ntot + 1) EA4) (i - 4)%nat
    ltac:(rewrite length_Z_to_le_bytes; lia)) as X.
  replace (F + 0xf0 + 4 + Z.of_nat (i - 4)%nat) with (F + 0xf0 + Z.of_nat i) in X by lia. exact X. }
rewrite app_nth2 by (rewrite E1; lia). rewrite E1.
destruct (Nat.lt_ge_cases i (8 + length js)) as [H3|H3].
{ rewrite app_nth1 by (rewrite Eb; lia). rewrite app_nth1 by lia.
  replace (F + 0xf0 + Z.of_nat i) with (F + 0xf8 + Z.of_nat (i - 4 - 4)%nat) by lia. exact (BJ (i - 4 - 4)%nat ltac:(lia)). }
destruct (Nat.eq_dec i (8 + length js)) as [H4|H4].
{ rewrite app_nth1 by (rewrite Eb; lia). rewrite app_nth2 by lia.
  replace (i - 4 - 4 - length js)%nat with 0%nat by lia. cbn [nth].
  replace (F + 0xf0 + Z.of_nat i) with (F + 0xf8 + ntot) by lia. rewrite XB0. unfold NUL. rewrite rm_unsigned_byte. reflexivity. }
rewrite app_nth2 by (rewrite Eb; lia). unfold zeros, NUL. rewrite nth_repeat. rewrite rm_unsigned_byte.
exact (ZJ i ltac:(lia)).
Qed.

Lemma w7_vm_kept : forall (W : world rsegs) m m' a n v,
val_mem rsegs (mrestrict (w_H W) m) a n v ->
(forall i, 0 <= i < Z.of_nat n -> aview rsegs (w_H W) m' (a + i) = aview rsegs (w_H W) m (a + i)) ->
val_mem rsegs (mrestrict (w_H W) m') a n v.
Proof.
intros W m m' a n v V K k Hk. rewrite <- (V k Hk). apply (mbyte_of_aview rsegs). apply K. lia.
Qed.
Lemma w7_in_rom_low : forall a, in_rom rsegs a -> 0 <= a < kLowMemEnd.
Proof. intros a (sg & Hin & _ & Hb). exact (w7_segs_low a (ex_intro _ sg (conj Hin Hb))). Qed.

(* a location list of RPgSeg.rs_at: one register, one real-frame cell *)
Lemma w7_at_reg : forall H mem regs e L r v, rs_at rsegs H mem regs e L -> In (LReg r, v) L ->
getr regs (Z_to_bv 5 r) = w64 v.
Proof. intros H mem regs e L r v HA Hin. unfold rs_at in HA. rewrite Forall_forall in HA. exact (HA _ Hin). Qed.
Lemma w7_at_cell : forall H mem regs e L o v, rs_at rsegs H mem regs e L -> In (LCell XR o, v) L ->
val_mem rsegs (mrestrict H mem) (e_R e + o) 8 (v mod 2 ^ 64).
Proof. intros H mem regs e L o v HA Hin. unfold rs_at in HA. rewrite Forall_forall in HA. exact (HA _ Hin). Qed.
End b.
