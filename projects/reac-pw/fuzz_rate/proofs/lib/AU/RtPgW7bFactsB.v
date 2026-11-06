(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW7bFacts.v at 25d4b718638e for reac-pw/fuzz_rate's image A: module paths changed; the image is fuzz_rate.asan (images.Asan) in place of lib/A/Img0; the frame's shadow patterns are over lib/A/RtPgMem.v rtm_sh (56 granules) in place of RPgMem.rm_sh (52); the image ranges are rate's PT_LOADs; w7_at_cell reads the cell at q_R e + o (lib/A/RtPgBase.v rt_renv). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW7bFacts.v at 7ef0f92b27f1 for the same unit's image B (fuzz_rate.asan-ubsan): the image is images.AsanUbsan; the frame's shadow patterns are lib/AU/RtPgSegB.v rsb_PG / rsb_PJ over lib/AU/RtPgMemB.v rtmb_sh (88 granules); the image ranges are image B's PT_LOADs; rs_g_of / rs_at are lib/AU/RtPgSegB.v rsb_g_of / rsb_at; aro_unowned is lib/AU/RtPgW7bCallB.v w7b_aro_unowned; the prefix w7_ becomes w7b_. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; addresses measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1): the facts the assembly of the walk of
   LLVMFuzzerTestOneInput from G 0x8160c to J 0x820dc uses besides its blocks: the model of case 0 (Model.ent_build
   on a case-0 turn is ent_headamp_key's key with its four parts joined uncut), the frame shadow patterns at G and
   J, the image ranges around the strings and the param table, and the moves of a location list, a value and the
   read-only data across a memory step. Proves no function (kind: model lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgMemB RtPgSegB RtPgW7bBaseB RtPgW7bKitB RtPgW7bCallB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* image B's loaded segments; an abbreviation, so every statement names the image module's own term *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ====================== the model of a case-0 turn ====================== *)
Definition w7b_sepb (p : Z) : list byte := if Z.testbit p 7 then [] else DOT.
Definition w7b_pab (p : Z) : list byte := nth (Z.to_nat (p mod 8)) param [].
Definition w7b_js (chs : list byte) (p : Z) : list byte := HPFX ++ chs ++ w7b_sepb p ++ w7b_pab p.

Lemma w7b_param_len : forall p, (length (w7b_pab p) <= 9)%nat.
Proof.
intros p. unfold w7b_pab. pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as H.
assert (Hc : p mod 8 = 0 \/ p mod 8 = 1 \/ p mod 8 = 2 \/ p mod 8 = 3 \/ p mod 8 = 4 \/ p mod 8 = 5 \/ p mod 8 = 6 \/ p mod 8 = 7) by lia.
destruct Hc as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E; vm_compute; lia.
Qed.
Lemma w7b_sep_len : forall p, (length (w7b_sepb p) <= 1)%nat.
Proof. intros p. unfold w7b_sepb. destruct (Z.testbit p 7); vm_compute; lia. Qed.
Lemma w7b_hpfx_len : length HPFX = 13%nat.
Proof. reflexivity. Qed.

Lemma w7b_join_part_small : forall t s, (length t + length s < 96)%nat -> join_part t s = t ++ s.
Proof.
intros t s H. unfold join_part.
destruct (Nat.leb_spec 96 (length t + length s)) as [H1|H1]; [lia|]. rewrite firstn_all. reflexivity.
Qed.
Lemma w7b_join4 : forall a b c d, (length a + length b + length c + length d < 96)%nat ->
join_parts [a; b; c; d] = a ++ b ++ c ++ d.
Proof.
intros a b c d H. unfold join_parts. cbn [fold_left].
rewrite (w7b_join_part_small [] a) by (cbn; lia). cbn [app].
rewrite (w7b_join_part_small a b) by lia.
rewrite (w7b_join_part_small (a ++ b) c) by (rewrite length_app; lia).
rewrite (w7b_join_part_small ((a ++ b) ++ c) d) by (rewrite !length_app in *; lia).
rewrite <- !app_assoc. reflexivity.
Qed.

Lemma w7b_len4 : forall a b c d : list byte, length a = 13%nat -> (length b <= 21)%nat -> (length c <= 1)%nat ->
(length d <= 9)%nat -> (length a + length b + length c + length d < 96)%nat.
Proof. intros a b c d Ha Hb Hc Hd. lia. Qed.

(* ent_build of a case-0 turn: the key ent_text makes of the four parts *)
Lemma w7b_ent_build_0 : forall rr chs pb r, fst (fuzz_u8 rr) mod 10 = 0 -> (chs, pb, r) = rsb_g_of rr ->
(length chs <= 21)%nat ->
ent_build rr = (ent_text (w7b_js chs pb) true, r).
Proof.
intros rr chs pb r Hk Hg Hl. unfold ent_build. unfold rsb_g_of in Hg.
destruct (fuzz_u8 rr) as [kd r1] eqn:E1. cbn [fst] in Hk. rewrite Hk. cbn [Z.to_nat].
unfold ent_headamp_key.
destruct (fuzz_u8 r1) as [c r2]. destruct (fuzz_u8 r2) as [p r3]. injection Hg as Hch Hpb Hr. subst.
unfold w7b_js, w7b_sepb, w7b_pab. rewrite w7b_join4; [reflexivity|].
apply w7b_len4; [exact w7b_hpfx_len | exact Hl | exact (w7b_sep_len p) | exact (w7b_param_len p)].
Qed.
Lemma w7b_js_len : forall chs p, (length chs <= 21)%nat -> (length (w7b_js chs p) <= 44)%nat.
Proof.
intros chs p H. unfold w7b_js. rewrite !length_app, w7b_hpfx_len.
pose proof (w7b_param_len p). pose proof (w7b_sep_len p). lia.
Qed.
Lemma w7b_ent_text_js : forall chs p, (length chs <= 21)%nat ->
ent_text (w7b_js chs p) true = Ent POD_STRING (Z.of_nat (length (w7b_js chs p)) + 1) (w7b_js chs p ++ [NUL]).
Proof.
intros chs p H. unfold ent_text. pose proof (w7b_js_len chs p H).
rewrite firstn_all2 by lia. rewrite length_app. cbn [length]. f_equal. lia.
Qed.

(* ====================== the frame's shadow at G and at J ====================== *)
Lemma w7b_PG : rsb_PG = rtmb_sh true true false false false true false.
Proof. reflexivity. Qed.
Lemma w7b_PJ : rsb_PJ = rtmb_sh false false false false false true false.
Proof. reflexivity. Qed.
(* the two patterns differ exactly where t and ch go out of scope (0x8172c .. 0x81764) *)
Lemma w7b_PG_PJ : forall i, 0 <= i < 88 ->
(4 <= i < 16 \/ 20 <= i < 23 -> nth (Z.to_nat i) rsb_PJ 0 = 0xf8) /\
(~ (4 <= i < 16 \/ 20 <= i < 23) -> nth (Z.to_nat i) rsb_PJ 0 = nth (Z.to_nat i) rsb_PG 0).
Proof.
intros i Hi.
assert (HB : forallb (fun j => let z := Z.of_nat j in
  (implb ((4 <=? z) && (z <? 16) || (20 <=? z) && (z <? 23)) (nth j rsb_PJ 0 =? 0xf8)) &&
  (implb (negb ((4 <=? z) && (z <? 16) || (20 <=? z) && (z <? 23))) (nth j rsb_PJ 0 =? nth j rsb_PG 0))) (seq 0 88) = true)
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

(* ====================== image B's ranges ====================== *)
Definition w7b_in_seg_b (lo hi : Z) : bool :=
existsb (fun sg => (Z.of_N (seg_base sg) <=? lo) && (hi <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) rsegs.
Lemma w7b_in_seg : forall lo hi a, w7b_in_seg_b lo hi = true -> lo <= a < hi -> in_img rsegs a.
Proof.
intros lo hi a Hb Ha. unfold w7b_in_seg_b in Hb. apply existsb_exists in Hb as (sg & Hin & Hs).
apply andb_prop in Hs as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
exists sg. split; [exact Hin | lia].
Qed.
(* the read-only PT_LOAD holding the strings, and the RELRO PT_LOAD holding the param table (.data.rel.ro) *)
Lemma w7b_img_ro : w7b_in_seg_b 0x10000 0x2fa0c = true.
Proof. vm_compute. reflexivity. Qed.
Lemma w7b_img_relro : w7b_in_seg_b 0x9b998 0x9d000 = true.
Proof. vm_compute. reflexivity. Qed.

(* ====================== moves of facts across a memory step ====================== *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Lemma w7b_vm_kept : forall (W : world rsegs) m m' a n v,
val_mem rsegs (mrestrict (w_H W) m) a n v ->
(forall i, 0 <= i < Z.of_nat n -> aview rsegs (w_H W) m' (a + i) = aview rsegs (w_H W) m (a + i)) ->
val_mem rsegs (mrestrict (w_H W) m') a n v.
Proof.
intros W m m' a n v V K k Hk. rewrite <- (V k Hk). apply (mbyte_of_aview rsegs). apply K. lia.
Qed.
Lemma w7b_aro_kept : forall B (W : world rsegs) m m' (Zn : Z -> Prop),
w7b_aro_unowned rsegs B (aview rsegs (w_H W) m) -> w7b_kept W m m' Zn -> (forall a, in_rom rsegs a -> ~ Zn a) ->
w7b_aro_unowned rsegs B (aview rsegs (w_H W) m').
Proof.
intros B W m m' Zn HA HK HZ a Hr Ho He. rewrite (HK a); [exact (HA a Hr Ho He) | | exact (HZ a Hr)].
destruct Hr as (sg & Hin & _ & Hb). pose proof (w7b_segs_low a (ex_intro _ sg (conj Hin Hb))) as L.
unfold kLowMemEnd in L. lia.
Qed.
Lemma w7b_in_rom_low : forall a, in_rom rsegs a -> 0 <= a < kLowMemEnd.
Proof. intros a (sg & Hin & _ & Hb). exact (w7b_segs_low a (ex_intro _ sg (conj Hin Hb))). Qed.

(* a location list of RtPgSegB.rsb_at: one register, one real-frame cell *)
Lemma w7b_at_reg : forall H mem regs e L r v, rsb_at rsegs H mem regs e L -> In (LReg r, v) L ->
getr regs (Z_to_bv 5 r) = w64 v.
Proof. intros H mem regs e L r v HA Hin. unfold rsb_at in HA. rewrite Forall_forall in HA. exact (HA _ Hin). Qed.
Lemma w7b_at_cell : forall H mem regs e L o v, rsb_at rsegs H mem regs e L -> In (LCell XR o, v) L ->
val_mem rsegs (mrestrict H mem) (q_R e + o) 8 (v mod 2 ^ 64).
Proof. intros H mem regs e L o v HA Hin. unfold rsb_at in HA. rewrite Forall_forall in HA. exact (HA _ Hin). Qed.
End b.

Print Assumptions w7b_ent_build_0.
Print Assumptions w7b_ent_text_js.
Print Assumptions w7b_PG.
Print Assumptions w7b_PJ.
Print Assumptions w7b_PG_PJ.
Print Assumptions w7b_img_ro.
Print Assumptions w7b_img_relro.
Print Assumptions w7b_in_seg.
Print Assumptions w7b_vm_kept.
Print Assumptions w7b_aro_kept.
Print Assumptions w7b_at_reg.
Print Assumptions w7b_at_cell.
