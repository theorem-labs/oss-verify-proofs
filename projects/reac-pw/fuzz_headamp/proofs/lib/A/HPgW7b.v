(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; addresses measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a): the piece G 0x81a34 -> J 0x8237c of the walk of
   LLVMFuzzerTestOneInput, HPgSeg.hs_piece_W7b_stmt. Proves no function (kind: segment lemma).

   THE PIECE (pod.h:250-262, ent_headamp_key after its first part, then ent_text): param[p % 8] and sep, the four
   parts stored at R+0x140 .. R+0x158, four turns strlen(part) / memcpy(t + n, part, l) with n += l, the 95 clamp of
   ent_text (never cuts: n <= 44), memcpy(e.body, t, n), e.body[n] = 0, e.type = 8, e.size = n + 1, t and ch out of
   scope, the three reloads and `j 0x8237c`. The blocks are lib/A/HPgW7bBlkA.v (A1), HPgW7bBlkA2.v (A2),
   HPgW7bBlkB.v (B, C, D, E1), HPgW7bBlkE.v (E2); the turn is HPgW7bIter.v; the calls are the strlen wrapper
   (HPgW7bCall.w7_strlen_at) and __asan_memcpy (HPgW7bKit.w7_memcpy_at). J's pod is Model.ent_build of the turn's
   input (HPgW7bFacts.w7_ent_build_0).
   The two callees' laws are the Section's hypotheses ASTRLEN (astrlen_realizes at 0x41b98, lib/A/Rt/StrlenDef.v's
   STRLEN_ENTRY_A) and AMEMCPY (aintrin_realizes OCpy at 0x51d0c: the AsanAPI
   field aa_asan_memcpy, lib/Reusable/YG0d.v). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgMem HPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgW7bBase HPgW7bKit HPgW7bKitB HPgW7bFacts HPgW7bCall HPgW7bBlkA HPgW7bBlkA2 HPgW7bBlkB HPgW7bBlkE HPgW7bIter.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require Import StrlenDef WrapRo.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Lemma w7_pptr_range : forall j, 0 <= j < 8 -> 0x21200 <= w7_pptr j <= 0x21400.
Proof.
intros j Hj. assert (H : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7) by lia.
destruct H as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; split; discriminate.
Qed.
(* the RELRO PT_LOAD of image A from its start to the page after .data.rel.ro, holding ent_headamp_key.param *)
Lemma w7_img_rw : w7_in_seg_b 0x9bc48 0x9d000 = true.
Proof. vm_compute. reflexivity. Qed.
Ltac w7_keep H r := rewrite (H r ltac:(vm_compute; lia) ltac:(vm_compute; intuition discriminate)).

Lemma w7_lit : forall (regs : bvmap 5 word) (r : bv 5) v, getr regs (Z_to_bv 5 (bv_unsigned r)) = v -> getr regs r = v.
Proof. intros regs r v H. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma w7_w64_mod : forall v, w64 (v mod 2 ^ 64) = w64 v.
Proof. intros v. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia. Qed.
Lemma w7_mod_small : forall v, 0 <= v < 2 ^ 64 -> v mod 2 ^ 64 = v.
Proof. intros v Hv. apply Z.mod_small. exact Hv. Qed.

(* an address of the frame for locals' shadow is never in the shadow hull of an image byte range whose
   surroundings are image bytes: the frame's own bytes are not image bytes *)
Lemma w7_img_hull_apart : forall F x n a,
(forall b, F <= b < F + 1024 -> ~ in_img rsegs b) -> 4096 <= F ->
(forall y, x - 0x300 <= y < x + n + 0x300 -> in_img rsegs y) -> 0 <= x -> 0 < n <= 0x100 ->
w7_hull x n a -> ~ (shadow_addr F <= a < shadow_addr F + 80).
Proof.
intros F x n a HF HF0 HI Hx Hn Ha Hs. unfold w7_hull, shadow_addr, SHADOW_OFF in *.
pose proof (Z.div_mod (0x7fff8000 + x / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (0x7fff8000 + x / 8) 8 ltac:(lia)).
pose proof (Z.div_mod (0x7fff8000 + (x + n - 1) / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (0x7fff8000 + (x + n - 1) / 8) 8 ltac:(lia)).
pose proof (Z.div_mod F 8 ltac:(lia)). pose proof (Z.mod_pos_bound F 8 ltac:(lia)).
pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)).
apply (HF F ltac:(lia)). apply HI. lia.
Qed.

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
garr8 rsegs (mrestrict (w_H W) mJ) (F + 0xf0) (hd_zbytes (ent_mem (Ent POD_STRING (ntot + 1) (js ++ [NUL])))).
Proof.
intros W mJ F ntot js Hn HL EA0 EA4 XB0 BJ ZJ.
apply (proj2 (hm_bytes_aview rsegs (w_H W) mJ (F + 0xf0) (ent_mem (Ent POD_STRING (ntot + 1) (js ++ [NUL]))))).
intros i Hi. unfold ent_mem in Hi |- *. cbn [e_type e_size e_body] in Hi |- *.
assert (E0 : length (le32 POD_STRING) = 4%nat) by (unfold le32; apply length_Z_to_le_bytes).
assert (E1 : length (le32 (ntot + 1)) = 4%nat) by (unfold le32; apply length_Z_to_le_bytes).
assert (Eb : length (js ++ [NUL]) = (length js + 1)%nat) by (rewrite length_app; reflexivity).
assert (HiL : (i < 104)%nat).
{ rewrite !length_app in Hi. unfold le32, zeros in Hi. rewrite !length_Z_to_le_bytes, repeat_length in Hi. cbn [length] in Hi. lia. }
clear Hi.
destruct (Nat.lt_ge_cases i 4) as [H1|H1].
{ rewrite app_nth1 by (rewrite E0; lia).
  exact (proj1 (hm_bytes_aview rsegs (w_H W) mJ (F + 0xf0) (Z_to_le_bytes 4 8)) (hm_bytes_of_val rsegs (w_H W) mJ (F + 0xf0) 4 8 EA0) i
    ltac:(rewrite length_Z_to_le_bytes; lia)). }
rewrite app_nth2 by (rewrite E0; lia). rewrite E0.
destruct (Nat.lt_ge_cases i 8) as [H2|H2].
{ rewrite app_nth1 by (rewrite E1; lia).
  pose proof (proj1 (hm_bytes_aview rsegs (w_H W) mJ (F + 0xf0 + 4) (Z_to_le_bytes 4 (ntot + 1))) (hm_bytes_of_val rsegs (w_H W) mJ (F + 0xf0 + 4) 4 (ntot + 1) EA4) (i - 4)%nat
    ltac:(rewrite length_Z_to_le_bytes; lia)) as X.
  replace (F + 0xf0 + 4 + Z.of_nat (i - 4)%nat) with (F + 0xf0 + Z.of_nat i) in X by lia. exact X. }
rewrite app_nth2 by (rewrite E1; lia). rewrite E1.
destruct (Nat.lt_ge_cases i (8 + length js)) as [H3|H3].
{ rewrite app_nth1 by (rewrite Eb; lia). rewrite app_nth1 by lia.
  replace (F + 0xf0 + Z.of_nat i) with (F + 0xf8 + Z.of_nat (i - 4 - 4)%nat) by lia. exact (BJ (i - 4 - 4)%nat ltac:(lia)). }
destruct (Nat.eq_dec i (8 + length js)) as [H4|H4].
{ rewrite app_nth1 by (rewrite Eb; lia). rewrite app_nth2 by lia.
  replace (i - 4 - 4 - length js)%nat with 0%nat by lia. cbn [nth].
  replace (F + 0xf0 + Z.of_nat i) with (F + 0xf8 + ntot) by lia. rewrite XB0. unfold NUL. rewrite hm_unsigned_byte. reflexivity. }
rewrite app_nth2 by (rewrite Eb; lia). unfold zeros, NUL. rewrite nth_repeat. rewrite hm_unsigned_byte.
exact (ZJ i ltac:(lia)).
Qed.

Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws rsegs B := AR_laws_ok rsegs B.
Hypothesis ASTRLEN : astrlen_realizes rsegs B W7_STRLEN.
Hypothesis AMEMCPY : aintrin_realizes rsegs B OCpy W7_MEMCPY.



(* moves across a change of world as well as of memory: only the readers matter *)
Lemma w7_vm_kept2 : forall (W W' : world rsegs) m m' a n v,
val_mem rsegs (mrestrict (w_H W) m) a n v ->
(forall i, 0 <= i < Z.of_nat n -> aview rsegs (w_H W') m' (a + i) = aview rsegs (w_H W) m (a + i)) ->
val_mem rsegs (mrestrict (w_H W') m') a n v.
Proof.
intros W W' m m' a n v V K j Hj. rewrite <- (V j Hj). apply (mbyte_of_aview rsegs). apply K. lia.
Qed.

(* the frame for locals at a state of the walk's journal *)
Lemma w7_frame : forall STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem md k pos F,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem md k ->
In (4, pos) (frames S2) -> frame_addr ly2 4 pos = F ->
F mod 32 = 0 /\ 4096 <= F /\ F + 1024 <= alloc_ceiling /\ in_app F 1024 /\
(forall a, F <= a < F + 1024 -> apresent (w_H W2) mem a /\ ~ in_img rsegs a) /\
(forall i, 0 <= i < 128 -> apresent (w_H W2) mem (shadow_addr F + i)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem md k pos F HJ Hin HF.
pose proof HJ as (HAR & _).
destruct (al_frames _ _ LAWS ly2 S2 W2 mem md 4 pos HAR Hin) as (H32 & Happ & Hb & Hsh).
destruct (frames_bounds rsegs B LAWS ly2 S2 W2 mem md 4 pos HAR Hin) as (H0 & H1 & _).
replace (fs_frame_bytes 4) with 1024 in * by reflexivity. rewrite HF in *.
split; [exact H32|]. split; [exact H0|]. split; [exact H1|]. split; [exact Happ|]. split.
- intros a Ha. split; [exact (proj1 (Hb a Ha))|].
  refine (proj2 (al_client_img _ _ LAWS ly2 S2 W2 mem md a HAR _)).
  right. left. exists 4, pos. split; [exact Hin|]. replace (fs_frame_bytes 4) with 1024 by reflexivity. rewrite HF. lia.
- intros i Hi. exact (proj1 (Hsh i ltac:(change (1024 / 8) with 128; lia))).
Qed.
Lemma w7_awr_frame : forall STK sp0 FP bl0 blc lyc own pos F a, In (4, pos) own -> frame_addr lyc 4 pos = F ->
(F <= a < F + 1024 \/ shadow_addr F <= a < shadow_addr F + 128) -> awr_byte STK sp0 FP bl0 blc lyc own a.
Proof.
intros STK sp0 FP bl0 blc lyc own pos F a Hin HF Ha. right. right. right. exists 4, pos. split; [exact Hin|].
unfold in_zr. cbn [fst snd]. replace (fs_frame_bytes 4) with 1024 by reflexivity. change (1024 / 8) with 128. rewrite HF. lia.
Qed.
(* an image byte range [x, x + n), its NUL word's tail and its shadow hull lie off everything the piece and the
   segment before it write *)
Lemma w7_img_apart : forall F R pp ppn x n a,
(forall b, F <= b < F + 1024 -> ~ in_img rsegs b) -> 4096 <= F -> in_app F 1024 ->
(forall b, pp <= b < pp + ppn -> ~ in_img rsegs b) -> in_app pp ppn -> 0 <= ppn ->
0x7fff7f800000 <= R - 16384 ->
(forall y, x - 0x300 <= y < x + n + 0x300 -> in_img rsegs y) -> 0x10000 <= x -> 0 < n <= 0x100 -> x + n < 0x9d000 ->
(x <= a < x + n + 8 \/ w7_hull x n a) ->
0 <= a < 0x100000000 /\ ~ (R - 16384 <= a < R + 0x160) /\ ~ (F <= a < F + 1024) /\ ~ (shadow_addr F <= a < shadow_addr F + 80) /\ ~ (pp <= a < pp + ppn).
Proof.
intros F R pp ppn x n a HFi HF0 HFa Hpi Hpa Hpn HR HI Hx Hn Hxn Ha.
destruct Ha as [Ha|Ha].
- split; [lia|]. split; [lia|]. split; [intros Hb; exact (HFi a Hb (HI a ltac:(lia)))|].
  split; [unfold shadow_addr, SHADOW_OFF; pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)); lia|].
  intros Hb. exact (Hpi a Hb (HI a ltac:(lia))).
- pose proof Ha as Hh. unfold w7_hull, shadow_addr, SHADOW_OFF in Hh.
  pose proof (Z.div_le_mono 0x10000 x 8 ltac:(lia) Hx) as D1.
  pose proof (Z.div_le_mono (x + n - 1) 0x9d000 8 ltac:(lia) ltac:(lia)) as D2.
  pose proof (Z.mul_div_le (0x7fff8000 + x / 8) 8 ltac:(lia)) as D3.
  pose proof (Z.mul_div_le (0x7fff8000 + (x + n - 1) / 8) 8 ltac:(lia)) as D4.
  pose proof (Z.div_mod (0x7fff8000 + x / 8) 8 ltac:(lia)) as D5.
  pose proof (Z.mod_pos_bound (0x7fff8000 + x / 8) 8 ltac:(lia)) as D6.
  change (0x10000 / 8) with 0x2000 in D1. change (0x9d000 / 8) with 0x13a00 in D2.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFa, Hpa.
  split; [lia|]. split; [lia|]. split; [lia|]. split.
  + exact (w7_img_hull_apart F x n a HFi HF0 HI ltac:(lia) Hn Ha).
  + lia.
Qed.


Lemma w7_pres_step : forall (regs regs' regs0 : bvmap 5 word) (clob : list (bv 5)) (X : list Z),
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr regs' r = getr regs r) ->
(forall r, acallee_saved r -> ~ In r X -> getr regs (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r)) ->
(forall r, acallee_saved r -> In r (map (fun c => bv_unsigned c) clob) -> In r X) ->
forall r, acallee_saved r -> ~ In r X -> getr regs' (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r).
Proof.
intros regs regs' regs0 clob X H1 H2 H3 r Hr Hn.
rewrite H1; [exact (H2 r Hr Hn) | rewrite w7_cs_bv by exact Hr; unfold acallee_saved in Hr; lia |].
apply w7_cs_out; [exact Hr|]. intros Hin. exact (Hn (H3 r Hr Hin)).
Qed.
Ltac w7_clobX := let r := fresh "r" in let Hr := fresh "Hr" in let Hin := fresh "Hin" in
intros r Hr Hin; vm_compute in Hin; unfold acallee_saved in Hr; cbn [In]; lia.


Lemma w7_view_present : forall (H : word -> bool) m a, apresent H m a -> aview rsegs H m a <> None.
Proof.
intros H m a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate.
Qed.
(* the shadow hull of a range inside t, ch or e lies in the frame's own shadow bytes *)
Lemma w7_hull_in : forall F o n a, F mod 32 = 0 -> 0 <= F -> 0x20 <= o -> o + n <= 0x158 -> 0 <= n ->
w7_hull (F + o) n a -> shadow_addr F <= a < shadow_addr F + 80.
Proof.
intros F o n a H32 HF Ho Hon Hn Ha. unfold w7_hull, shadow_addr, SHADOW_OFF in *.
pose proof (Z.div_mod F 32 ltac:(lia)) as D0. rewrite H32, Z.add_0_r in D0.
set (q := F / 32) in *.
assert (E1 : (F + o) / 8 = 4 * q + o / 8) by (rewrite D0; replace (32 * q + o) with (o + (4 * q) * 8) by lia; rewrite Z.div_add by lia; lia).
assert (E2 : (F + o + n - 1) / 8 = 4 * q + (o + n - 1) / 8)
  by (rewrite D0; replace (32 * q + o + n - 1) with ((o + n - 1) + (4 * q) * 8) by lia; rewrite Z.div_add by lia; lia).
assert (E3 : F / 8 = 4 * q) by (rewrite D0; replace (32 * q) with ((4 * q) * 8) by lia; apply Z.div_mul; lia).
rewrite E1, E2 in Ha. rewrite E3.
pose proof (Z.div_le_mono 0x20 o 8 ltac:(lia) Ho) as M1. change (0x20 / 8) with 4 in M1.
pose proof (Z.div_le_mono (o + n - 1) 0x157 8 ltac:(lia) ltac:(lia)) as M2. change (0x157 / 8) with 42 in M2.
pose proof (Z.div_mod (0x7fff8000 + (4 * q + o / 8)) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (0x7fff8000 + (4 * q + o / 8)) 8 ltac:(lia)).
pose proof (Z.div_mod (0x7fff8000 + (4 * q + (o + n - 1) / 8)) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (0x7fff8000 + (4 * q + (o + n - 1) / 8)) 8 ltac:(lia)).
pose proof (Z.div_mod q 2 ltac:(lia)). pose proof (Z.mod_pos_bound q 2 ltac:(lia)).
pose proof (Z.div_mod (o / 8) 2 ltac:(lia)). pose proof (Z.mod_pos_bound (o / 8) 2 ltac:(lia)).
lia.
Qed.
Lemma w7_hull_frame : forall (W : world rsegs) m F o n, F mod 32 = 0 -> 0 <= F -> 0x20 <= o -> o + n <= 0x158 -> 0 < n ->
(forall i, 0 <= i < 128 -> apresent (w_H W) m (shadow_addr F + i)) ->
shadow_hull_vis (aview rsegs (w_H W) m) (F + o) n.
Proof.
intros W m F o n H32 HF Ho Hon Hn HP a Ha. pose proof (w7_hull_in F o n a H32 HF Ho Hon ltac:(lia) Ha) as Hin.
replace a with (shadow_addr F + (a - shadow_addr F)) by lia. apply w7_view_present. apply HP. lia.
Qed.
(* ch, the key's first part, as a string of the strlen / memcpy calls *)
Lemma w7_strok_ch : forall (W : world rsegs) m R F (chs : list byte),
garr8 rsegs (mrestrict (w_H W) m) (F + 0xa0) (map (fun b : byte => bv_unsigned b) (chs ++ [NUL])) ->
Forall (fun b : byte => bv_unsigned b <> 0) chs -> (length chs <= 21)%nat ->
hd_fsh rsegs (w_H W) m F (hm_sh true true false true false false) -> F mod 32 = 0 -> 4096 <= F -> in_app F 1024 ->
(forall a, F <= a < F + 1024 -> apresent (w_H W) m a) ->
(forall i, 0 <= i < 128 -> apresent (w_H W) m (shadow_addr F + i)) ->
F + 1024 <= R - 2 * ESTACK ->
w7_strok W m R (F + 0xa0) chs.
Proof.
intros W m R F chs HB HZ HL HS H32 HF0 HFa HP HSP HR.
assert (HB' := proj1 (hm_bytes_aview rsegs (w_H W) m (F + 0xa0) (chs ++ [NUL])) HB).
rewrite length_app in HB'. cbn [length] in HB'.
pose proof ASAN_CEIL_range as (AC & _). unfold in_app, kLowShadowBeg, kHighMemBeg in HFa. unfold ESTACK in HR.
split; [lia|]. split; [lia|]. split; [lia|].
split.
{ intros j Hj. rewrite (HB' j ltac:(lia)). rewrite app_nth1 by exact Hj. split; [reflexivity|].
  rewrite Forall_forall in HZ. apply HZ. apply nth_In. exact Hj. }
split.
{ pose proof (HB' (length chs) ltac:(lia)) as H. rewrite app_nth2, Nat.sub_diag in H by lia. cbn [nth] in H.
  rewrite H. reflexivity. }
split.
{ intros a Ha. apply w7_view_present. apply HP. pose proof (Z.mod_pos_bound (F + 0xa0 + Z.of_nat (length chs)) 8 ltac:(lia)). lia. }
split; [intros a Ha; unfold ESTACK; lia|].
split; [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd; lia|].
split.
{ apply (hm_A_ra_ch rsegs (w_H W) m F true false true false false 0 (Z.of_nat (length chs) + 1)) in HS;
  [rewrite Z.add_0_r in HS; exact HS | pose proof (Z.div_mod F 32 ltac:(lia)); lia | lia | lia]. }
apply (w7_hull_frame W m F 0xa0); [exact H32 | lia | lia | lia | lia | exact HSP].
Qed.

(* the bytes a state keeps from the segment's start: all but the callees' stack and the real frame, the frame for
   locals and its shadow, and the first block *)
Definition w7_KC (W2 : world rsegs) (m : word -> option byte) (R F pp ppn : Z) (W : world rsegs) (memc : word -> option byte) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ (R - 16384 <= a < R + 0x160) -> ~ (F <= a < F + 1024) ->
~ (shadow_addr F <= a < shadow_addr F + 80) -> ~ (pp <= a < pp + ppn) ->
aview rsegs (w_H W2) m a = aview rsegs (w_H W) memc a.
Lemma w7_KC_step : forall W2 m m' R F pp ppn W memc (Zn : Z -> Prop),
w7_KC W2 m R F pp ppn W memc -> w7_kept W2 m m' Zn ->
(forall a, Zn a -> R - 16384 <= a < R + 0x160 \/ F <= a < F + 1024 \/ shadow_addr F <= a < shadow_addr F + 80) ->
w7_KC W2 m' R F pp ppn W memc.
Proof.
intros W2 m m' R F pp ppn W memc Zn HK HS HZ a Ha H1 H2 H3 H4.
rewrite (HS a Ha). - exact (HK a Ha H1 H2 H3 H4). - intros Hz. destruct (HZ a Hz) as [X|[X|X]]; contradiction.
Qed.


(* t's bytes so far, extended by one turn's copy *)
Lemma w7_tt_step : forall (W : world rsegs) m m' t (p s : list byte),
(forall j, (j < length p)%nat -> aview rsegs (w_H W) m (t + Z.of_nat j) = Some (bv_unsigned (nth j p (Z_to_bv 8 0)))) ->
(forall j, (j < length p)%nat -> aview rsegs (w_H W) m' (t + Z.of_nat j) = aview rsegs (w_H W) m (t + Z.of_nat j)) ->
(forall j, (j < length s)%nat -> aview rsegs (w_H W) m' (t + Z.of_nat (length p) + Z.of_nat j) = Some (bv_unsigned (nth j s (Z_to_bv 8 0)))) ->
forall j, (j < length (p ++ s))%nat -> aview rsegs (w_H W) m' (t + Z.of_nat j) = Some (bv_unsigned (nth j (p ++ s) (Z_to_bv 8 0))).
Proof.
intros W m m' t p s Hp HK Hs j Hj. rewrite length_app in Hj.
destruct (Nat.lt_ge_cases j (length p)) as [Hl|Hl].
- rewrite app_nth1 by exact Hl. rewrite (HK j Hl). exact (Hp j Hl).
- rewrite app_nth2 by exact Hl. specialize (Hs (j - length p)%nat ltac:(lia)).
  replace (t + Z.of_nat (length p) + Z.of_nat (j - length p)) with (t + Z.of_nat j) in Hs by lia. exact Hs.
Qed.


(* two ranges of a pairwise disjoint list, one from each part *)
Lemma w7_pw_in : forall (l1 l2 : list (Z * Z)) x y, pairwise zdisjoint (l1 ++ l2) -> In x l1 -> In y l2 -> zdisjoint x y.
Proof.
induction l1 as [|z l1 IH]; intros l2 x y Hp Hx Hy; [destruct Hx|]. cbn [app pairwise] in Hp. destruct Hp as [Hf Hp].
destruct Hx as [<-|Hx].
- rewrite Forall_forall in Hf. apply Hf. apply in_or_app. right. exact Hy.
- exact (IH l2 x y Hp Hx Hy).
Qed.
(* the first block's image at a cut of the pod loop is PP_SIZE bytes long *)
Lemma w7_pc_ents_ok : forall sh ps es, hs_wf sh ps -> Forall ent_wf es -> (length es < 32)%nat ->
(length (pc_ents (PbCut sh ps (Some es))) <= 32)%nat /\ Forall (fun e => (length (e_body e) <= 96)%nat) (pc_ents (PbCut sh ps (Some es))).
Proof.
intros sh ps es (_ & Hps & Hall & _) Hes Hl. unfold pc_ents. cbn [pc_props pc_open]. unfold first_params.
destruct (find (fun kv => fst kv =? POD_PROP_PARAMS) ps) as [[k v]|] eqn:Ef; cbn [option_map snd].
- apply find_some in Ef as [Hin _]. destruct v as [z|es'].
  + split; [cbn; lia | constructor].
  + rewrite Forall_forall in Hps. pose proof (proj2 (Hps _ Hin)) as Hw. cbn [snd pval_wf] in Hw. split; [exact Hw|].
    rewrite Forall_forall in Hall |- *. intros e0 He0.
    assert (Hin' : In e0 (all_ents ps)) by (unfold all_ents; apply in_flat_map; exists (k, PStruct es'); split; [exact Hin | exact He0]).
    destruct (Hall e0 Hin') as (_ & Hb & Hs). lia.
- split; [lia|]. rewrite Forall_forall in Hes |- *. intros e0 He0. destruct (Hes e0 He0) as (_ & Hb & Hs). lia.
Qed.
Lemma w7_pp_len : forall sh ps es, hs_wf sh ps -> Forall ent_wf es -> (length es < 32)%nat -> (length ps <= 2)%nat ->
Z.of_nat (length (pc_image (PbCut sh ps (Some es)))) = Layout.PP_SIZE.
Proof.
intros sh ps es Hw Hes Hl Hp. pose proof Hw as (_ & Hps & Hall & _).
destruct (w7_pc_ents_ok sh ps es Hw Hes Hl) as [H1 H2].
unfold pc_image. apply length_pp_image; [| exact H1 | exact H2].
destruct (pc_buf_len_open sh ps es) as [H _].
- rewrite Forall_forall in Hps |- *. intros kv Hkv. exact (proj2 (Hps kv Hkv)).
- exact Hall.
- exact Hes.
- lia.
Qed.

Ltac w7_inL := unfold hs_L_Dc0, hs_Rc0, hs_Kc; cbv zeta; cbn [app]; repeat (first [left; reflexivity | right]).

Lemma w7_mod32_8 : forall F, F mod 32 = 0 -> F mod 8 = 0.
Proof. intros F H. lia. Qed.
Lemma w7_mod16_8 : forall x, x mod 16 = 0 -> x mod 8 = 0.
Proof. intros x H. lia. Qed.
(* the walk's arithmetic is linear: no division or remainder equations from here on *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Theorem w7b_piece_A : hs_piece_W7b_stmt rsegs B MT.
Proof.
unfold hs_piece_W7b_stmt. intros cx POST rest ip k Hst HJc.
unfold hs_from_G. intros ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r pb chs Hip Hk HG.
destruct Hst as (Hpre & _ & _ & _).
pose proof Hpre as (HJ0 & _ & Hsp0 & Hgp0 & Htp0 & HeS & HR32 & HRsz & HSTKR & Hown & HFe & _ & _ & _ & Haro0 & Hglobs & _ & Hstrs & Hcells & _ & _ & (_ & Hppin & _)).
assert (HR16 : e_R (x_e rsegs cx) mod 16 = 0).
{ pose proof (Z.div_mod (e_R (x_e rsegs cx)) 32 ltac:(lia)) as D. rewrite HR32, Z.add_0_r in D. rewrite D.
  replace (32 * (e_R (x_e rsegs cx) / 32)) with ((2 * (e_R (x_e rsegs cx) / 32)) * 16) by ring. apply Z_mod_mult. }
pose proof HG as (HPB & HAT & HFSH & HPP & HCH & HE0 & Hkind & Hg & Hchl & Hpb).
pose proof HPB as (Hcore & _).
pose proof Hcore as (HJG & Hr234 & Hfrs & Hperm & HioG & Hmo & HKG).
unfold hs_at_cx in HAT. unfold hs_fsh_at in HFSH.
set (e := x_e rsegs cx) in *.
set (STK := x_STK rsegs cx) in *. set (sp0 := x_sp0 rsegs cx) in *. set (FP := x_FP rsegs cx) in *. set (ly := x_ly rsegs cx) in *.
set (S := x_S rsegs cx) in *. set (W0 := x_W0 rsegs cx) in *. set (mem0 := x_mem0 rsegs cx) in *. set (md0 := x_md0 rsegs cx) in *.
set (own := x_own rsegs cx) in *. set (k0 := x_k rsegs cx) in *.
set (R := e_R e) in *. set (F := e_F e) in *. set (pp := e_pp e) in *.
set (cur := hs_cur rsegs cx rest r) in *.
(* ---- the registers at G ---- *)
pose proof (w7_at_reg _ _ _ _ _ 8 (e_S e) HAT ltac:(w7_inL)) as G8.
pose proof (w7_at_reg _ _ _ _ _ 9 R HAT ltac:(w7_inL)) as G9.
pose proof (w7_at_reg _ _ _ _ _ 19 (shadow_addr F) HAT ltac:(w7_inL)) as G19.
pose proof (w7_at_reg _ _ _ _ _ 23 SHADOW_OFF HAT ltac:(w7_inL)) as G23.
pose proof (w7_at_reg _ _ _ _ _ 26 (F + 0x20) HAT ltac:(w7_inL)) as G26.
pose proof (w7_at_reg _ _ _ _ _ 21 (pp + 0x4000) HAT ltac:(w7_inL)) as G21.
pose proof (w7_at_reg _ _ _ _ _ 20 (F + 0xa0) HAT ltac:(w7_inL)) as G20.
pose proof (w7_at_reg _ _ _ _ _ 27 pb HAT ltac:(w7_inL)) as G27.
pose proof (w7_at_reg _ _ _ _ _ 25 cur HAT ltac:(w7_inL)) as G25.
pose proof (w7_at_cell _ _ _ _ _ 0x98 (pp + 0x4000) HAT ltac:(w7_inL)) as C70.
pose proof (w7_at_cell _ _ _ _ _ 0xf0 pp HAT ltac:(w7_inL)) as C80.
pose proof (w7_at_cell _ _ _ _ _ 0xd0 (shadow_addr (pp + 0x4000)) HAT ltac:(w7_inL)) as Cb0.
pose proof (w7_at_cell _ _ _ _ _ 0xe0 (F + 0xf8) HAT ltac:(w7_inL)) as Cc0.
pose proof (w7_at_cell _ _ _ _ _ 0x110 (F + 0xf0) HAT ltac:(w7_inL)) as Cf0.
(* ---- the stack, R and the journal's layouts ---- *)
pose proof HJ0 as (HAR0 & HlyC & _ & _ & _ & HfrsC & _ & _ & _ & _ & _ & _ & _ & _ & Hastk & _).
pose proof HJG as (HARG & HlyG & _ & _ & _ & HfrsG & _).
pose proof Hastk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (AC & _).
unfold T_SEG_STK, ASTACK in HSTKR. cbn [hi_rsz headamp_himg_A] in HRsz.
assert (HR1 : 0x7fff7f800000 + 16384 <= R) by lia.
assert (HR2 : R + 0x1e0 <= 2 ^ 47) by lia.
assert (HRS : R + 0x1e0 <= sp0) by lia.
assert (G2 : getr regs2 2 = w64 R).
{ refine (eq_trans (Hr234 2 ltac:(lia)) _). exact Hsp0. }
(* ---- the frame for locals and the first block ---- *)
cbn [hi_cid headamp_himg_A] in Hown, HFe.
set (pos := x_pos rsegs cx) in *.
assert (HinS2 : In (4, pos) (frames S2)) by (rewrite HfrsG; apply in_or_app; left; exact Hown).
pose proof HlyC as (_ & _ & _ & _ & _ & HFlC & _). pose proof HlyG as (_ & _ & _ & _ & _ & HFlG & _).
assert (EF2 : frame_addr ly2 4 pos = F) by (rewrite HFe; unfold frame_addr; rewrite HFlG, HFlC; reflexivity).
destruct (w7_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJG HinS2 EF2) as (HF32 & HF0 & HF1 & HFapp & HFb & HFsh).
assert (HFd8 : 0 <= F / 8 <= 17592186044416).
{ split; [apply Z.div_pos; lia|].
  pose proof (Z.div_le_mono F (2 ^ 47) 8 ltac:(lia) ltac:(pose proof asan_consts; lia)) as X47.
  change (2 ^ 47 / 8) with 17592186044416 in X47. exact X47. }
assert (HF8d : 8 * (F / 8) <= F) by (apply Z.mul_div_le; lia).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hppin) as (Hpp16 & Hpp0 & Hpp1 & Hppapp & Hppb & _ & _).
assert (Hppi : forall b, pp <= b < pp + req_size Layout.PP_SIZE -> ~ in_img rsegs b).
{ intros b Hb. refine (proj2 (al_client_img _ _ LAWS _ _ _ _ _ b HAR0 _)). left. exists pp, Layout.PP_SIZE. split; [exact Hppin | exact Hb]. }
pose proof (req_size_pos Layout.PP_SIZE ltac:(unfold Layout.PP_SIZE; lia)) as Hreq.
assert (HspR : spZ (x_regs rsegs cx) = R) by (unfold spZ; rewrite Hsp0; unfold w64; apply unsigned_lit_small; lia).
assert (HFapp' : (F + 1024 <= kLowShadowBeg \/ kHighMemBeg <= F) /\ 4096 <= F) by (unfold in_app in HFapp; destruct HFapp as [_ [H|[H _]]]; split; lia || (left; lia) || (right; lia)).
(* the segment's start memory and G's agree off the callees' stack, the frame, its shadow, the real frame and pp *)
assert (KG : forall a, 0 <= a < 2 ^ 64 -> ~ (R - 16384 <= a < R + 0x160) -> ~ (F <= a < F + 1024) ->
  ~ (shadow_addr F <= a < shadow_addr F + 80) -> ~ (pp <= a < pp + req_size Layout.PP_SIZE) ->
  aview rsegs (w_H W2) mem2 a = aview rsegs (w_H (x_W rsegs cx)) (x_memc rsegs cx) a).
{ intros a Ha H1 H2 H3 H4. apply HKG; [exact Ha | rewrite HspR; unfold T_SEG_STK, ASTACK; lia |].
  unfold hs_E1, hd_inw. cbn [hi_w1 headamp_himg_A]. rewrite !Exists_cons, Exists_nil. cbn [hd_xv fst snd].
  fold e R F pp. intros [[Hx|[Hx|[Hx|[]]]]|Hx]; [lia | lia | lia | lia]. }
set (ppn := req_size Layout.PP_SIZE) in *.
assert (IMGA : forall x n a, (forall y, x - 0x300 <= y < x + n + 0x300 -> in_img rsegs y) -> 0x10000 <= x -> 0 < n <= 0x100 ->
  x + n < 0x9d000 -> (x <= a < x + n + 8 \/ w7_hull x n a) ->
  0 <= a < 0x100000000 /\ ~ (R - 16384 <= a < R + 0x160) /\ ~ (F <= a < F + 1024) /\ ~ (shadow_addr F <= a < shadow_addr F + 80) /\ ~ (pp <= a < pp + ppn)).
{ intros x n a HI Hx Hn Hxn Ha. apply (w7_img_apart F R pp ppn x n a); try assumption; try lia.
  intros b Hb. exact (proj2 (HFb b Hb)). }
assert (IMG_RO : forall x n, 0x10300 <= x -> x + n + 0x300 <= 0x2f6e4 -> forall y, x - 0x300 <= y < x + n + 0x300 -> in_img rsegs y)
by (intros x n H1 H2 y Hy; apply (w7_in_seg 0x10000 0x2f6e4); [exact w7_img_ro | lia]).
assert (IMG_RR : forall x n, 0x9bf48 <= x -> x + n + 0x300 <= 0x9d000 -> forall y, x - 0x300 <= y < x + n + 0x300 -> in_img rsegs y)
by (intros x n H1 H2 y Hy; apply (w7_in_seg 0x9bc48 0x9d000); [exact w7_img_rw | lia]).
(* ======================== A1: 0x81a34 -> 0x81a5c ======================== *)
pose proof (Z.mod_pos_bound pb 8 ltac:(lia)) as Hpb8.
unfold cfg_at.
eapply SRr_bind.
{ apply (w7_A1 B LAWS STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k0 regs2 pb HJG).
  - exact (w7_lit _ 23%bv _ G23).
  - exact (w7_lit _ 27%bv _ G27).
  - exact Hpb.
  - rewrite Forall_forall in Hglobs.
    pose proof (Hglobs (0x9c180, 64) ltac:(cbn [hi_globs headamp_himg_A headamp_A_globs]; repeat (first [left; reflexivity | right]))) as HG0.
    cbn [fst snd] in HG0.
    apply (range_addressable_sub _ _ 0x9c180 64); [| lia | lia].
    apply (w7_ra_rd (aview rsegs (w_H (x_W rsegs cx)) (x_memc rsegs cx))); [exact HG0 | lia |].
    intros a Ha. destruct (IMGA 0x9c180 64 a (IMG_RR 0x9c180 64 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia) ltac:(lia) (or_intror Ha))
      as (H0 & H1 & H2 & H3 & H4).
    exact (KG a ltac:(lia) H1 H2 H3 H4). }
cbv beta. intros W1 c1 _ (-> & rA1 & mA1 & dA1 & -> & HJA1 & HioA1 & HrA1 & HKA1 & HpA1 & RA1).
(* ======================== A2: 0x81a5c -> strlen(parts[0]) ======================== *)
set (j8 := pb mod 8) in *.
assert (HPA : val_mem rsegs (mrestrict (w_H W2) mA1) (W7_PTAB pb) 8 (w7_pptr j8)).
{ unfold hd_ro_cells in Hcells. cbn [hi_cells headamp_himg_A] in Hcells. rewrite Forall_forall in Hcells.
  pose proof (Hcells _ (w7_param_cell j8 Hpb8)) as HC0. cbn [fst snd] in HC0.
  unfold W7_PTAB. fold j8.
  apply (w7_vm_kept2 (x_W rsegs cx) W2 (x_memc rsegs cx) mA1 _ 8 _ HC0).
  intros q Hq. rewrite (HKA1 (0x9c180 + 8 * j8 + q) ltac:(lia) (fun f => f)).
  destruct (IMGA 0x9c180 64 (0x9c180 + 8 * j8 + q) (IMG_RR 0x9c180 64 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(left; lia)) as (H0 & H1 & H2 & H3 & H4).
  exact (KG (0x9c180 + 8 * j8 + q) ltac:(lia) H1 H2 H3 H4). }
pose proof HlyG as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HsloG & HshiG & _).
pose proof (w7_pptr_range j8 Hpb8) as Hpa.
eapply SRr_bind.
{ apply (w7_A2 B LAWS STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mA1 dA1 k0 rA1 pb R (F + 0xa0) cur (w7_pptr j8) HJA1).
  - exact RA1.
  - w7_keep HrA1 (23%bv : bv 5). exact (w7_lit _ 23%bv _ G23).
  - w7_keep HrA1 (27%bv : bv 5). exact (w7_lit _ 27%bv _ G27).
  - exact Hpb.
  - w7_keep HrA1 (9%bv : bv 5). exact (w7_lit _ 9%bv _ G9).
  - lia.
  - lia.
  - exact HR16.
  - w7_keep HrA1 (20%bv : bv 5). exact (w7_lit _ 20%bv _ G20).
  - unfold in_app, ASAN_CEIL in HFapp. lia.
  - w7_keep HrA1 (25%bv : bv 5). exact (w7_lit _ 25%bv _ G25).
  - exact HPA.
  - lia.
  - pose proof HJA1 as (HARa & _). apply (hm_stk_ra rsegs B ly2 S2 W2 mA1 dA1 (R + 0x148) 8 sp0 HARa); [lia | lia | lia | exact (w7_mod16_8 sp0 Hal16)].
  - intros a Ha. left. lia. }
cbv beta. intros W1 c1 _ (-> & rA2 & mA2 & dA2 & -> & HJA2 & HioA2 & HrA2 & HKA2 & HpA2 &
  (RA2ra & RA2a0 & RA2s9 & RA2s4 & RA2s5 & RA2s8 & SL118 & SL120 & SL128 & SL130)).
(* ---- what the rest of the piece carries ---- *)
assert (G3 : getr regs2 3 = w64 (as_gp B)) by (refine (eq_trans (Hr234 3 ltac:(lia)) _); exact Hgp0).
assert (G4 : getr regs2 4 = w64 (as_tp B)) by (refine (eq_trans (Hr234 4 ltac:(lia)) _); exact Htp0).
assert (PRA2 : forall r, acallee_saved r -> ~ In r [20; 21; 24; 25; 27] -> getr rA2 (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)).
{ apply (w7_pres_step rA1 rA2 regs2 [1; 10; 11; 12; 20; 21; 24; 25; 27]%bv); [exact HrA2 | | w7_clobX].
  apply (w7_pres_step regs2 rA1 regs2 [10; 11]%bv); [exact HrA1 | intros; reflexivity | w7_clobX]. }
assert (KC2 : w7_KC W2 mA2 R F pp ppn (x_W rsegs cx) (x_memc rsegs cx)).
{ intros a Ha H1 H2 H3 H4. rewrite (HKA2 a Ha ltac:(cbv beta; lia)), (HKA1 a Ha (fun f => f)). exact (KG a Ha H1 H2 H3 H4). }
set (Acc := fun a => R - 8192 <= a < R \/ R + 0x140 <= a < R + 0x160 \/ F + 0x20 <= a < F + 0x80).
assert (KF2 : w7_kept W2 mem2 mA2 Acc).
{ intros a Ha Hz. rewrite (HKA2 a Ha ltac:(cbv beta; unfold Acc in Hz; lia)). exact (HKA1 a Ha (fun f => f)). }
assert (HFlo : F + 1024 <= 0x10000 \/ 0x2f6e4 <= F).
{ destruct (Z_lt_le_dec F 0x10000) as [Hlt|Hge].
  - destruct (Z_le_gt_dec (F + 1024) 0x10000) as [Hle|Hgt]; [left; exact Hle|]. exfalso.
    apply (proj2 (HFb 0x10000 ltac:(lia))). apply (w7_in_seg 0x10000 0x2f6e4); [exact w7_img_ro | lia].
  - destruct (Z_le_gt_dec 0x2f6e4 F) as [Hle|Hgt]; [right; exact Hle|]. exfalso.
    apply (proj2 (HFb F ltac:(lia))). apply (w7_in_seg 0x10000 0x2f6e4); [exact w7_img_ro | lia]. }
assert (STRI : forall m x l, w7_KC W2 m R F pp ppn (x_W rsegs cx) (x_memc rsegs cx) ->
  hd_cstr rsegs (w_H (x_W rsegs cx)) (x_memc rsegs cx) x (map (fun b : byte => bv_unsigned b) l) ->
  In (x, Z.of_nat (length l)) w7_tail_strs -> 0x10300 <= x -> x + Z.of_nat (length l) + 1 + 0x300 <= 0x2f6e4 ->
  (length l <= 21)%nat -> w7_strok W2 m R x l).
{ intros m x l HK HC HT Hx1 Hx2 Hl.
  apply (w7_strok_kept2 (x_W rsegs cx) W2 (x_memc rsegs cx) m R x l).
  - apply (w7_strok_cstr _ _ R x l HC); [| unfold ESTACK; lia | lia].
    intros a Ha. exact (w7_tail_img x (Z.of_nat (length l)) HT a Ha _ _).
  - intros a Ha. destruct (IMGA x (Z.of_nat (length l) + 1) a (IMG_RO x (Z.of_nat (length l) + 1) Hx1 ltac:(lia)) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(unfold w7_strz in Ha; destruct Ha as [Ha|Ha]; [left; lia | right; exact Ha])) as (H0 & H1 & H2 & H3 & H4).
    exact (HK a ltac:(lia) H1 H2 H3 H4). }
assert (AROm : forall m, w7_KC W2 m R F pp ppn (x_W rsegs cx) (x_memc rsegs cx) -> aro_unowned rsegs B (aview rsegs (w_H W2) m)).
{ intros m HK. apply (aro_unowned_keep rsegs B (aview rsegs (w_H (x_W rsegs cx)) (x_memc rsegs cx))).
  - exact (aro_unowned_of_arodata _ _ _ _ _ Haro0).
  - intros a Hr Ho He. pose proof (w7_in_rom_low a Hr) as Hlow. unfold kLowMemEnd in Hlow.
    assert (Himg : in_img rsegs a) by (destruct Hr as (sg & Hin & _ & Hb); exists sg; split; [exact Hin | exact Hb]).
    apply HK; [lia | lia | intros Hb; exact (proj2 (HFb a Hb) Himg) | unfold shadow_addr, SHADOW_OFF; pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)); lia |
      intros Hb; exact (Hppi a Hb Himg)]. }
assert (FSHm : forall m, w7_kept W2 mem2 m Acc -> hd_fsh rsegs (w_H W2) m F (hm_sh true true false true false false)).
{ intros m HK. rewrite <- w7_PG. apply (hm_fsh_kept rsegs (w_H W2) mem2 (w_H W2) m F hs_PG HFSH).
  intros q Hq. replace (length hs_PG) with 80%nat in Hq by reflexivity.
  apply HK; [unfold shadow_addr, SHADOW_OFF; pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)); unfold in_app, ASAN_CEIL in HFapp; pose proof ASAN_CEIL_range; lia |].
  unfold Acc. unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)).
  pose proof ASAN_CEIL_range as (AC1 & _). unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp. unfold ASAN_CEIL in *.
  pose proof (Z.div_le_mono F (2 ^ 47) 8 ltac:(lia) ltac:(lia)) as X47. change (2 ^ 47 / 8) with 17592186044416 in X47. lia. }
assert (HRsp : R mod 16 = 0 /\ sp0 mod 16 = 0 /\ R <= sp0 /\ 2 * ESTACK - (R - sp0) <= STK /\ 2 * ESTACK <= R /\ R < 2 ^ 63)
by (unfold ESTACK; repeat split; lia).
destruct HRsp as (HRa & HRb & HRc & HRd & HRe & HRf).
assert (HtR : F + 0x20 + 0x80 <= R - 2 * ESTACK) by (unfold ESTACK; lia).
assert (HFR : F + 1024 <= R - 2 * ESTACK) by (unfold ESTACK; lia).
cbn [hi_strs headamp_himg_A] in Hstrs. rewrite Forall_forall in Hstrs.
assert (HFsb : shadow_addr F + 80 <= R - 2 * ESTACK).
{ unfold shadow_addr, SHADOW_OFF, ESTACK. pose proof ASAN_CEIL_range as (AC1 & _). unfold in_app, ASAN_CEIL in HFapp.
  pose proof (Z.div_le_mono F (2 ^ 47) 8 ltac:(lia) ltac:(lia)) as X47. change (2 ^ 47 / 8) with 17592186044416 in X47. lia. }
assert (HshF0 : 0 <= shadow_addr F) by (unfold shadow_addr, SHADOW_OFF; pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)); lia).
assert (Ham : forall o n, 0 <= o -> o + n <= 1024 -> 0 <= n -> amem_range (F + o) n).
{ intros o n H1 H2 H3. pose proof ASAN_CEIL_range as (AC1 & _). unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. unfold ASAN_CEIL in AC1. lia. }
assert (HLh : (length HPFX <= 21)%nat) by (rewrite w7_hpfx_len; lia).
(* ======================== turn 0: strlen("reac.headamp."), memcpy(t, ., 13) ======================== *)
destruct (w7_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJA2 HinS2 EF2) as (_ & _ & _ & _ & _ & HFsA2).
apply (w7_iter B LAWS ASTRLEN AMEMCPY STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mA2 dA2 k0 rA2 R (F + 0x20) 0 0x20f00 HPFX POST HJA2).
- exact RA2ra.
- exact RA2a0.
- exact RA2s9.
- exact RA2s8.
- refine (eq_trans (PRA2 26 ltac:(unfold acallee_saved; lia) ltac:(cbn; lia)) _). exact (w7_lit _ 26%bv _ G26).
- refine (eq_trans (PRA2 2 ltac:(unfold acallee_saved; lia) ltac:(cbn; lia)) _). exact G2.
- refine (eq_trans (PRA2 3 ltac:(unfold acallee_saved; lia) ltac:(cbn; lia)) _). exact G3.
- refine (eq_trans (PRA2 4 ltac:(unfold acallee_saved; lia) ltac:(cbn; lia)) _). exact G4.
- exact HRa. - exact HRb. - exact HRc. - exact HRd. - exact HRe. - exact HRf.
- apply (STRI mA2 0x20f00 HPFX KC2 (Hstrs _ w7_hpfx_str)); [vm_compute; left; reflexivity | lia | rewrite w7_hpfx_len; cbn; lia | exact HLh].
- exact (AROm mA2 KC2).
- exact HLh.
- lia.
- lia.
- exact HtR.
- intros a Ha. apply (w7_awr_frame _ _ _ _ _ _ _ pos F a Hown EF2). left. pose proof w7_hpfx_len. lia.
- replace (F + 0x20 + 0) with (F + 0x20) by lia. apply Ham; pose proof w7_hpfx_len; lia.
- pose proof (hm_A_ra_t rsegs (w_H W2) mA2 F true false true false false 0 (Z.of_nat (length HPFX)) (FSHm mA2 KF2)
    (w7_mod32_8 F HF32) ltac:(lia) ltac:(pose proof w7_hpfx_len; lia)) as X.
  unfold HM_T in X. exact X.
- intros Hl. replace (F + 0x20 + 0) with (F + 0x20) by lia.
  apply (w7_hull_frame W2 mA2 F 0x20); [exact HF32 | lia | lia | pose proof w7_hpfx_len; lia | lia | exact HFsA2].
- intros a Ha. replace (F + 0x20 + 0) with (F + 0x20) in Ha by lia.
  pose proof (w7_hull_in F 0x20 (Z.of_nat (length HPFX)) a HF32 ltac:(lia) ltac:(lia) ltac:(pose proof w7_hpfx_len; lia) ltac:(pose proof w7_hpfx_len; lia) Ha).
  unfold shadow_addr, SHADOW_OFF in *. pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)). lia.
- intros a Ha. destruct (IMGA 0x20f00 (Z.of_nat (length HPFX) + 1) a (IMG_RO 0x20f00 (Z.of_nat (length HPFX) + 1) ltac:(lia) ltac:(rewrite w7_hpfx_len; cbn; lia))
    ltac:(lia) ltac:(rewrite w7_hpfx_len; cbn; lia) ltac:(rewrite w7_hpfx_len; cbn; lia)
    ltac:(unfold w7_strz in Ha; destruct Ha as [Ha|Ha]; [left; lia | right; exact Ha])) as (H0 & H1 & H2 & H3 & H4).
  unfold ESTACK. lia.
- pose proof w7_hpfx_len. lia.
- intros rI0 mI0 dI0 HJI0 HioI0 PRI0 RI0s11 TI0 KI0 HpI0. {
assert (PRI0' : forall r, acallee_saved r -> ~ In r [20; 21; 24; 25; 27] -> getr rI0 (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)).
{ intros q Hq Hn. rewrite (PRI0 q Hq ltac:(cbn in Hn; lia)). exact (PRA2 q Hq Hn). }
assert (KCI0 : w7_KC W2 mI0 R F pp ppn (x_W rsegs cx) (x_memc rsegs cx)).
{ apply (w7_KC_step _ _ _ _ _ _ _ _ _ _ KC2 KI0). intros a Ha. cbv beta in Ha. unfold ESTACK in Ha. pose proof w7_hpfx_len. lia. }
assert (KFI0 : w7_kept W2 mem2 mI0 Acc).
{ apply (w7_kept_trans W2 mem2 mA2 mI0 Acc _ Acc KF2 KI0). intros a [Ha|Ha]; [exact Ha|]. unfold Acc. cbv beta in Ha. unfold ESTACK in Ha. pose proof w7_hpfx_len. lia. }
(* ======================== C0: n = 13, parts[1] = ch ======================== *)
eapply SRr_bind.
{ apply (w7_C B LAWS STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mI0 dI0 k0 rI0 0%nat R 0 (Z.of_nat (length HPFX)) (F + 0xa0) HJI0).
  - lia.
  - refine (eq_trans (PRI0' 9 ltac:(unfold acallee_saved; lia) ltac:(cbn; lia)) _). exact (w7_lit _ 9%bv _ G9).
  - lia.
  - lia.
  - exact HR16.
  - refine (eq_trans (PRI0 20 ltac:(unfold acallee_saved; lia) ltac:(lia)) _). transitivity (w64 (R + 0x140)); [exact RA2s4 | f_equal; lia].
  - refine (eq_trans (PRI0 24 ltac:(unfold acallee_saved; lia) ltac:(lia)) _). exact RA2s8.
  - exact RI0s11.
  - lia.
  - pose proof w7_hpfx_len. lia.
  - replace (R + 0x148 + 8 * Z.of_nat 0) with (R + 0x148) by lia. apply (w7_vm_kept W2 mA2 mI0 _ 8 _ SL120).
    intros q Hq. apply KI0; [lia | cbv beta; unfold ESTACK; pose proof w7_hpfx_len; lia].
  - unfold in_app, ASAN_CEIL in HFapp. pose proof ASAN_CEIL_range. lia. }
cbv beta. intros W1 c1 _ (-> & rC0 & mC0 & dC0 & -> & HJC0 & HioC0 & HrC0 & HKC0 & HpC0 & (RC0ra & RC0a0 & RC0s9 & RC0s4 & RC0s8)).
assert (PRC0 : forall r, acallee_saved r -> ~ In r [20; 21; 24; 25; 27] -> getr rC0 (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)).
{ apply (w7_pres_step rI0 rC0 regs2 [1; 10; 20; 24; 25]%bv); [exact HrC0 | exact PRI0' | w7_clobX]. }
assert (KCC0 : w7_KC W2 mC0 R F pp ppn (x_W rsegs cx) (x_memc rsegs cx)).
{ apply (w7_KC_step _ _ _ _ _ _ _ _ _ _ KCI0 HKC0). intros a []. }
assert (KFC0 : w7_kept W2 mem2 mC0 Acc).
{ apply (w7_kept_trans W2 mem2 mI0 mC0 Acc _ Acc KFI0 HKC0). intros a [Ha|[]]; exact Ha. }
(* ======================== turn 1: strlen(ch), memcpy(t + 13, ch, |ch|) ======================== *)
destruct (w7_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJC0 HinS2 EF2) as (_ & _ & _ & _ & HFbC0 & HFsC0).
assert (HCHC0 : garr8 rsegs (mrestrict (w_H W2) mC0) (F + 0xa0) (map (fun b : byte => bv_unsigned b) (chs ++ [NUL]))).
{ apply (hm_bytes_kept rsegs (w_H W2) mem2 (w_H W2) mC0 (F + 0xa0) (chs ++ [NUL]) HCH).
  intros x Hx. rewrite length_app in Hx. cbn [length] in Hx.
  apply KFC0; [unfold in_app, ASAN_CEIL in HFapp; pose proof ASAN_CEIL_range; lia | unfold Acc; lia]. }
assert (SOCH : w7_strok W2 mC0 R (F + 0xa0) chs).
{ apply (w7_strok_ch W2 mC0 R F chs HCHC0 (w7_chs_nonzero rr chs pb r Hg) Hchl (FSHm mC0 KFC0) HF32 HF0 HFapp
    (fun a Ha => proj1 (HFbC0 a Ha)) HFsC0). unfold ESTACK. lia. }
apply (w7_iter B LAWS ASTRLEN AMEMCPY STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mC0 dC0 k0 rC0 R (F + 0x20) (0 + Z.of_nat (length HPFX)) (F + 0xa0) chs POST HJC0).
- exact RC0ra.
- exact RC0a0.
- exact RC0s9.
- exact RC0s8.
- refine (eq_trans (PRC0 26 ltac:(unfold acallee_saved; lia) ltac:(cbn; lia)) _). exact (w7_lit _ 26%bv _ G26).
- refine (eq_trans (PRC0 2 ltac:(unfold acallee_saved; lia) ltac:(cbn; lia)) _). exact G2.
- refine (eq_trans (PRC0 3 ltac:(unfold acallee_saved; lia) ltac:(cbn; lia)) _). exact G3.
- refine (eq_trans (PRC0 4 ltac:(unfold acallee_saved; lia) ltac:(cbn; lia)) _). exact G4.
- exact HRa. - exact HRb. - exact HRc. - exact HRd. - exact HRe. - exact HRf.
- exact SOCH.
- exact (AROm mC0 KCC0).
- exact Hchl.
- pose proof w7_hpfx_len. lia.
- lia.
- exact HtR.
- intros a Ha. apply (w7_awr_frame _ _ _ _ _ _ _ pos F a Hown EF2). left. pose proof w7_hpfx_len. lia.
- replace (F + 0x20 + (0 + Z.of_nat (length HPFX))) with (F + (0x20 + Z.of_nat (length HPFX))) by lia.
  apply Ham; pose proof w7_hpfx_len; lia.
- pose proof (hm_A_ra_t rsegs (w_H W2) mC0 F true false true false false (0 + Z.of_nat (length HPFX)) (Z.of_nat (length chs)) (FSHm mC0 KFC0)
    (w7_mod32_8 F HF32) ltac:(lia) ltac:(pose proof w7_hpfx_len; lia)) as X.
  unfold HM_T in X. exact X.
- intros Hl. replace (F + 0x20 + (0 + Z.of_nat (length HPFX))) with (F + (0x20 + Z.of_nat (length HPFX))) by lia.
  apply (w7_hull_frame W2 mC0 F (0x20 + Z.of_nat (length HPFX))); [exact HF32 | lia | lia | pose proof w7_hpfx_len; lia | lia | exact HFsC0].
- intros a Ha. replace (F + 0x20 + (0 + Z.of_nat (length HPFX))) with (F + (0x20 + Z.of_nat (length HPFX))) in Ha by lia.
  pose proof (w7_hull_in F (0x20 + Z.of_nat (length HPFX)) (Z.of_nat (length chs)) a HF32 ltac:(lia) ltac:(lia) ltac:(pose proof w7_hpfx_len; lia) ltac:(lia) Ha).
  unfold ESTACK in *. lia.
- intros a Ha. unfold w7_strz in Ha. destruct Ha as [Ha|Ha].
  + unfold ESTACK in *. lia.
  + pose proof (w7_hull_in F 0xa0 (Z.of_nat (length chs) + 1) a HF32 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Ha).
    unfold ESTACK in *. lia.
- pose proof w7_hpfx_len. lia.
- intros rI1 mI1 dI1 HJI1 HioI1 PRI1 RI1s11 TI1 KI1 HpI1. {
(* ---- registers, relative to the state after A2 ---- *)
assert (B26 : getr rA2 26%bv = w64 (F + 0x20)).
{ refine (eq_trans (PRA2 26 ltac:(unfold acallee_saved; lia) ltac:(cbn; lia)) _). exact (w7_lit _ 26%bv _ G26). }
assert (B2 : getr rA2 2%bv = w64 R).
{ refine (eq_trans (PRA2 2 ltac:(unfold acallee_saved; lia) ltac:(cbn; lia)) _). exact G2. }
assert (B3 : getr rA2 3%bv = w64 (as_gp B)).
{ refine (eq_trans (PRA2 3 ltac:(unfold acallee_saved; lia) ltac:(cbn; lia)) _). exact G3. }
assert (B4 : getr rA2 4%bv = w64 (as_tp B)).
{ refine (eq_trans (PRA2 4 ltac:(unfold acallee_saved; lia) ltac:(cbn; lia)) _). exact G4. }
assert (B9 : getr rA2 9%bv = w64 R).
{ refine (eq_trans (PRA2 9 ltac:(unfold acallee_saved; lia) ltac:(cbn; lia)) _). exact (w7_lit _ 9%bv _ G9). }
assert (PRC0a : forall r, acallee_saved r -> ~ In r [20; 24; 25; 27] -> getr rC0 (Z_to_bv 5 r) = getr rA2 (Z_to_bv 5 r)).
{ apply (w7_pres_step rI0 rC0 rA2 [1; 10; 20; 24; 25]%bv); [exact HrC0 | | w7_clobX].
  intros q Hq Hn. apply PRI0; [exact Hq | cbn in Hn; lia]. }
assert (PRI1a : forall r, acallee_saved r -> ~ In r [20; 24; 25; 27] -> getr rI1 (Z_to_bv 5 r) = getr rA2 (Z_to_bv 5 r)).
{ intros q Hq Hn. rewrite (PRI1 q Hq ltac:(cbn in Hn; lia)). exact (PRC0a q Hq Hn). }
assert (KCI1 : w7_KC W2 mI1 R F pp ppn (x_W rsegs cx) (x_memc rsegs cx)).
{ apply (w7_KC_step _ _ _ _ _ _ _ _ _ _ KCC0 KI1). intros a Ha. cbv beta in Ha. unfold ESTACK in Ha. pose proof w7_hpfx_len. lia. }
assert (KFI1 : w7_kept W2 mem2 mI1 Acc).
{ apply (w7_kept_trans W2 mem2 mC0 mI1 Acc _ Acc KFC0 KI1). intros a [Ha|Ha]; [exact Ha|]. unfold Acc. cbv beta in Ha. unfold ESTACK in Ha. pose proof w7_hpfx_len. lia. }
set (AccS := fun a => R - 8192 <= a < R \/ F + 0x20 <= a < F + 0x80).
assert (KSI1 : w7_kept W2 mA2 mI1 AccS).
{ intros a Ha Hz. unfold AccS in Hz. pose proof w7_hpfx_len.
  rewrite (KI1 a Ha ltac:(cbv beta; unfold ESTACK; lia)), (HKC0 a Ha (fun f => f)).
  exact (KI0 a Ha ltac:(cbv beta; unfold ESTACK; lia)). }
assert (TT1 : forall j, (j < length (HPFX ++ chs))%nat ->
  aview rsegs (w_H W2) mI1 (F + 0x20 + Z.of_nat j) = Some (bv_unsigned (nth j (HPFX ++ chs) (Z_to_bv 8 0)))).
{ apply (w7_tt_step W2 mI0 mI1 (F + 0x20) HPFX chs).
  - intros j Hj. rewrite <- (TI0 j Hj). f_equal; lia.
  - intros j Hj. pose proof w7_hpfx_len. rewrite (KI1 (F + 0x20 + Z.of_nat j) ltac:(lia) ltac:(cbv beta; unfold ESTACK; lia)). apply HKC0; [lia | exact (fun f => f)].
  - intros j Hj. rewrite <- (TI1 j Hj). f_equal; lia. }
(* ======================== C1: n = 13 + |ch|, parts[2] = sep ======================== *)
eapply SRr_bind.
{ apply (w7_C B LAWS STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mI1 dI1 k0 rI1 1%nat R (0 + Z.of_nat (length HPFX)) (Z.of_nat (length chs)) (w7_sep pb) HJI1).
  - lia.
  - refine (eq_trans (PRI1a 9 ltac:(unfold acallee_saved; lia) ltac:(cbn; lia)) _). exact B9.
  - lia.
  - lia.
  - exact HR16.
  - refine (eq_trans (PRI1 20 ltac:(unfold acallee_saved; lia) ltac:(lia)) _). transitivity (w64 (R + 0x148 + 8 * Z.of_nat 0)); [exact RC0s4 | f_equal; lia].
  - refine (eq_trans (PRI1 24 ltac:(unfold acallee_saved; lia) ltac:(lia)) _). exact RC0s8.
  - exact RI1s11.
  - pose proof w7_hpfx_len. lia.
  - lia.
  - replace (R + 0x148 + 8 * Z.of_nat 1) with (R + 0x150) by lia. apply (w7_vm_kept W2 mA2 mI1 _ 8 _ SL128).
    intros q Hq. apply KSI1; [lia | unfold AccS; lia].
  - unfold w7_sep. destruct (Z.testbit pb 7); lia. }
cbv beta. intros W1 c1 _ (-> & rC1 & mC1 & dC1 & -> & HJC1 & HioC1 & HrC1 & HKC1 & HpC1 & (RC1ra & RC1a0 & RC1s9 & RC1s4 & RC1s8)).
assert (PRC1a : forall r, acallee_saved r -> ~ In r [20; 24; 25; 27] -> getr rC1 (Z_to_bv 5 r) = getr rA2 (Z_to_bv 5 r)).
{ apply (w7_pres_step rI1 rC1 rA2 [1; 10; 20; 24; 25]%bv); [exact HrC1 | exact PRI1a | w7_clobX]. }
assert (KCC1 : w7_KC W2 mC1 R F pp ppn (x_W rsegs cx) (x_memc rsegs cx)).
{ apply (w7_KC_step _ _ _ _ _ _ _ _ _ _ KCI1 HKC1). intros a []. }
assert (KFC1 : w7_kept W2 mem2 mC1 Acc).
{ apply (w7_kept_trans W2 mem2 mI1 mC1 Acc _ Acc KFI1 HKC1). intros a [Ha|[]]; exact Ha. }
assert (KSC1 : w7_kept W2 mA2 mC1 AccS).
{ apply (w7_kept_trans W2 mA2 mI1 mC1 AccS _ AccS KSI1 HKC1). intros a [Ha|[]]; exact Ha. }
(* ======================== turn 2: strlen(sep), memcpy(t + n, sep, |sep|) ======================== *)
destruct (w7_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJC1 HinS2 EF2) as (_ & _ & _ & _ & _ & HFsC1).
pose proof (w7_sep_len pb) as HLs.
assert (Hsep : 0x21200 <= w7_sep pb <= 0x21420) by (unfold w7_sep; destruct (Z.testbit pb 7); lia).
apply (w7_iter B LAWS ASTRLEN AMEMCPY STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mC1 dC1 k0 rC1 R (F + 0x20)
  (0 + Z.of_nat (length HPFX) + Z.of_nat (length chs)) (w7_sep pb) (w7_sepb pb) POST HJC1).
- exact RC1ra.
- exact RC1a0.
- exact RC1s9.
- exact RC1s8.
- refine (eq_trans (PRC1a 26 ltac:(unfold acallee_saved; lia) ltac:(cbn; lia)) _). exact B26.
- refine (eq_trans (PRC1a 2 ltac:(unfold acallee_saved; lia) ltac:(cbn; lia)) _). exact B2.
- refine (eq_trans (PRC1a 3 ltac:(unfold acallee_saved; lia) ltac:(cbn; lia)) _). exact B3.
- refine (eq_trans (PRC1a 4 ltac:(unfold acallee_saved; lia) ltac:(cbn; lia)) _). exact B4.
- exact HRa. - exact HRb. - exact HRc. - exact HRd. - exact HRe. - exact HRf.
- apply (STRI mC1 (w7_sep pb) (w7_sepb pb) KCC1 (Hstrs _ (w7_sep_str pb))); [exact (w7_sep_tail pb) | lia | lia | lia].
- exact (AROm mC1 KCC1).
- lia.
- pose proof w7_hpfx_len. lia.
- lia.
- exact HtR.
- intros a Ha. apply (w7_awr_frame _ _ _ _ _ _ _ pos F a Hown EF2). left. pose proof w7_hpfx_len. lia.
- replace (F + 0x20 + (0 + Z.of_nat (length HPFX) + Z.of_nat (length chs))) with (F + (0x20 + Z.of_nat (length HPFX) + Z.of_nat (length chs))) by lia.
  apply Ham; pose proof w7_hpfx_len; lia.
- pose proof (hm_A_ra_t rsegs (w_H W2) mC1 F true false true false false (0 + Z.of_nat (length HPFX) + Z.of_nat (length chs)) (Z.of_nat (length (w7_sepb pb))) (FSHm mC1 KFC1)
    (w7_mod32_8 F HF32) ltac:(lia) ltac:(pose proof w7_hpfx_len; lia)) as X.
  unfold HM_T in X. exact X.
- intros Hl. replace (F + 0x20 + (0 + Z.of_nat (length HPFX) + Z.of_nat (length chs))) with (F + (0x20 + Z.of_nat (length HPFX) + Z.of_nat (length chs))) by lia.
  apply (w7_hull_frame W2 mC1 F (0x20 + Z.of_nat (length HPFX) + Z.of_nat (length chs))); [exact HF32 | lia | lia | pose proof w7_hpfx_len; lia | lia | exact HFsC1].
- intros a Ha. replace (F + 0x20 + (0 + Z.of_nat (length HPFX) + Z.of_nat (length chs))) with (F + (0x20 + Z.of_nat (length HPFX) + Z.of_nat (length chs))) in Ha by lia.
  pose proof (w7_hull_in F (0x20 + Z.of_nat (length HPFX) + Z.of_nat (length chs)) (Z.of_nat (length (w7_sepb pb))) a HF32 ltac:(lia) ltac:(lia) ltac:(pose proof w7_hpfx_len; lia) ltac:(lia) Ha).
  unfold ESTACK in *. lia.
- intros a Ha. destruct (IMGA (w7_sep pb) (Z.of_nat (length (w7_sepb pb)) + 1) a (IMG_RO (w7_sep pb) (Z.of_nat (length (w7_sepb pb)) + 1) ltac:(lia) ltac:(lia))
    ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(unfold w7_strz in Ha; destruct Ha as [Ha|Ha]; [left; lia | right; exact Ha])) as (H0 & H1 & H2 & H3 & H4).
  unfold ESTACK. lia.
- pose proof w7_hpfx_len. lia.
- intros rI2 mI2 dI2 HJI2 HioI2 PRI2 RI2s11 TI2 KI2 HpI2. {
assert (PRI2a : forall r, acallee_saved r -> ~ In r [20; 24; 25; 27] -> getr rI2 (Z_to_bv 5 r) = getr rA2 (Z_to_bv 5 r)).
{ intros q Hq Hn. rewrite (PRI2 q Hq ltac:(cbn in Hn; lia)). exact (PRC1a q Hq Hn). }
assert (KCI2 : w7_KC W2 mI2 R F pp ppn (x_W rsegs cx) (x_memc rsegs cx)).
{ apply (w7_KC_step _ _ _ _ _ _ _ _ _ _ KCC1 KI2). intros a Ha. cbv beta in Ha. unfold ESTACK in Ha. pose proof w7_hpfx_len. lia. }
assert (KFI2 : w7_kept W2 mem2 mI2 Acc).
{ apply (w7_kept_trans W2 mem2 mC1 mI2 Acc _ Acc KFC1 KI2). intros a [Ha|Ha]; [exact Ha|]. unfold Acc. cbv beta in Ha. unfold ESTACK in Ha. pose proof w7_hpfx_len. lia. }
assert (KSI2 : w7_kept W2 mA2 mI2 AccS).
{ apply (w7_kept_trans W2 mA2 mC1 mI2 AccS _ AccS KSC1 KI2). intros a [Ha|Ha]; [exact Ha|]. unfold AccS. cbv beta in Ha. unfold ESTACK in Ha. pose proof w7_hpfx_len. lia. }
assert (TT2 : forall j, (j < length ((HPFX ++ chs) ++ w7_sepb pb))%nat ->
  aview rsegs (w_H W2) mI2 (F + 0x20 + Z.of_nat j) = Some (bv_unsigned (nth j ((HPFX ++ chs) ++ w7_sepb pb) (Z_to_bv 8 0)))).
{ apply (w7_tt_step W2 mI1 mI2 (F + 0x20) (HPFX ++ chs) (w7_sepb pb) TT1).
  - intros j Hj. rewrite length_app in Hj. pose proof w7_hpfx_len.
    rewrite (KI2 (F + 0x20 + Z.of_nat j) ltac:(lia) ltac:(cbv beta; unfold ESTACK; lia)). apply HKC1; [lia | exact (fun f => f)].
  - intros j Hj. rewrite <- (TI2 j Hj). f_equal; rewrite length_app; lia. }
(* ======================== C2: parts[3] = param[p % 8] ======================== *)
eapply SRr_bind.
{ apply (w7_C B LAWS STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mI2 dI2 k0 rI2 2%nat R (0 + Z.of_nat (length HPFX) + Z.of_nat (length chs)) (Z.of_nat (length (w7_sepb pb))) (w7_pptr j8) HJI2).
  - lia.
  - refine (eq_trans (PRI2a 9 ltac:(unfold acallee_saved; lia) ltac:(cbn; lia)) _). exact B9.
  - lia.
  - lia.
  - exact HR16.
  - refine (eq_trans (PRI2 20 ltac:(unfold acallee_saved; lia) ltac:(lia)) _). transitivity (w64 (R + 0x148 + 8 * Z.of_nat 1)); [exact RC1s4 | f_equal; lia].
  - refine (eq_trans (PRI2 24 ltac:(unfold acallee_saved; lia) ltac:(lia)) _). exact RC1s8.
  - exact RI2s11.
  - pose proof w7_hpfx_len. lia.
  - lia.
  - replace (R + 0x148 + 8 * Z.of_nat 2) with (R + 0x158) by lia. apply (w7_vm_kept W2 mA2 mI2 _ 8 _ SL130).
    intros q Hq. apply KSI2; [lia | unfold AccS; lia].
  - lia. }
cbv beta. intros W1 c1 _ (-> & rC2 & mC2 & dC2 & -> & HJC2 & HioC2 & HrC2 & HKC2 & HpC2 & (RC2ra & RC2a0 & RC2s9 & RC2s4 & RC2s8)).
assert (PRC2a : forall r, acallee_saved r -> ~ In r [20; 24; 25; 27] -> getr rC2 (Z_to_bv 5 r) = getr rA2 (Z_to_bv 5 r)).
{ apply (w7_pres_step rI2 rC2 rA2 [1; 10; 20; 24; 25]%bv); [exact HrC2 | exact PRI2a | w7_clobX]. }
assert (KCC2 : w7_KC W2 mC2 R F pp ppn (x_W rsegs cx) (x_memc rsegs cx)).
{ apply (w7_KC_step _ _ _ _ _ _ _ _ _ _ KCI2 HKC2). intros a []. }
assert (KFC2 : w7_kept W2 mem2 mC2 Acc).
{ apply (w7_kept_trans W2 mem2 mI2 mC2 Acc _ Acc KFI2 HKC2). intros a [Ha|[]]; exact Ha. }
assert (KSC2 : w7_kept W2 mA2 mC2 AccS).
{ apply (w7_kept_trans W2 mA2 mI2 mC2 AccS _ AccS KSI2 HKC2). intros a [Ha|[]]; exact Ha. }
(* ======================== turn 3: strlen(param), memcpy(t + n, param, |param|) ======================== *)
destruct (w7_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJC2 HinS2 EF2) as (_ & _ & _ & _ & _ & HFsC2).
pose proof (w7_param_len pb) as HLp.
apply (w7_iter B LAWS ASTRLEN AMEMCPY STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mC2 dC2 k0 rC2 R (F + 0x20)
  (0 + Z.of_nat (length HPFX) + Z.of_nat (length chs) + Z.of_nat (length (w7_sepb pb))) (w7_pptr j8) (w7_pab pb) POST HJC2).
- exact RC2ra.
- exact RC2a0.
- exact RC2s9.
- exact RC2s8.
- refine (eq_trans (PRC2a 26 ltac:(unfold acallee_saved; lia) ltac:(cbn; lia)) _). exact B26.
- refine (eq_trans (PRC2a 2 ltac:(unfold acallee_saved; lia) ltac:(cbn; lia)) _). exact B2.
- refine (eq_trans (PRC2a 3 ltac:(unfold acallee_saved; lia) ltac:(cbn; lia)) _). exact B3.
- refine (eq_trans (PRC2a 4 ltac:(unfold acallee_saved; lia) ltac:(cbn; lia)) _). exact B4.
- exact HRa. - exact HRb. - exact HRc. - exact HRd. - exact HRe. - exact HRf.
- apply (STRI mC2 (w7_pptr j8) (w7_pab pb) KCC2 (Hstrs _ (w7_param_str j8 Hpb8))); [exact (w7_param_tail j8 Hpb8) | lia | lia | lia].
- exact (AROm mC2 KCC2).
- lia.
- pose proof w7_hpfx_len. lia.
- lia.
- exact HtR.
- intros a Ha. apply (w7_awr_frame _ _ _ _ _ _ _ pos F a Hown EF2). left. pose proof w7_hpfx_len. lia.
- replace (F + 0x20 + (0 + Z.of_nat (length HPFX) + Z.of_nat (length chs) + Z.of_nat (length (w7_sepb pb))))
    with (F + (0x20 + Z.of_nat (length HPFX) + Z.of_nat (length chs) + Z.of_nat (length (w7_sepb pb)))) by lia.
  apply Ham; pose proof w7_hpfx_len; lia.
- pose proof (hm_A_ra_t rsegs (w_H W2) mC2 F true false true false false (0 + Z.of_nat (length HPFX) + Z.of_nat (length chs) + Z.of_nat (length (w7_sepb pb)))
    (Z.of_nat (length (w7_pab pb))) (FSHm mC2 KFC2)
    (w7_mod32_8 F HF32) ltac:(lia) ltac:(pose proof w7_hpfx_len; lia)) as X.
  unfold HM_T in X. exact X.
- intros Hl. replace (F + 0x20 + (0 + Z.of_nat (length HPFX) + Z.of_nat (length chs) + Z.of_nat (length (w7_sepb pb))))
    with (F + (0x20 + Z.of_nat (length HPFX) + Z.of_nat (length chs) + Z.of_nat (length (w7_sepb pb)))) by lia.
  apply (w7_hull_frame W2 mC2 F (0x20 + Z.of_nat (length HPFX) + Z.of_nat (length chs) + Z.of_nat (length (w7_sepb pb))));
    [exact HF32 | lia | lia | pose proof w7_hpfx_len; lia | lia | exact HFsC2].
- intros a Ha. replace (F + 0x20 + (0 + Z.of_nat (length HPFX) + Z.of_nat (length chs) + Z.of_nat (length (w7_sepb pb))))
    with (F + (0x20 + Z.of_nat (length HPFX) + Z.of_nat (length chs) + Z.of_nat (length (w7_sepb pb)))) in Ha by lia.
  pose proof (w7_hull_in F (0x20 + Z.of_nat (length HPFX) + Z.of_nat (length chs) + Z.of_nat (length (w7_sepb pb))) (Z.of_nat (length (w7_pab pb))) a HF32
    ltac:(lia) ltac:(lia) ltac:(pose proof w7_hpfx_len; lia) ltac:(lia) Ha).
  unfold ESTACK in *. lia.
- intros a Ha. destruct (IMGA (w7_pptr j8) (Z.of_nat (length (w7_pab pb)) + 1) a (IMG_RO (w7_pptr j8) (Z.of_nat (length (w7_pab pb)) + 1) ltac:(lia) ltac:(lia))
    ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(unfold w7_strz in Ha; destruct Ha as [Ha|Ha]; [left; lia | right; exact Ha])) as (H0 & H1 & H2 & H3 & H4).
  unfold ESTACK. lia.
- pose proof w7_hpfx_len. lia.
- intros rI3 mI3 dI3 HJI3 HioI3 PRI3 RI3s11 TI3 KI3 HpI3. {
assert (PRI3a : forall r, acallee_saved r -> ~ In r [20; 24; 25; 27] -> getr rI3 (Z_to_bv 5 r) = getr rA2 (Z_to_bv 5 r)).
{ intros q Hq Hn. rewrite (PRI3 q Hq ltac:(cbn in Hn; lia)). exact (PRC2a q Hq Hn). }
assert (KFI3 : w7_kept W2 mem2 mI3 Acc).
{ apply (w7_kept_trans W2 mem2 mC2 mI3 Acc _ Acc KFC2 KI3). intros a [Ha|Ha]; [exact Ha|]. unfold Acc. cbv beta in Ha. unfold ESTACK in Ha. pose proof w7_hpfx_len. lia. }
set (js3 := ((HPFX ++ chs) ++ w7_sepb pb) ++ w7_pab pb).
assert (Hjs3 : js3 = w7_js chs pb) by (unfold js3, w7_js; rewrite <- !app_assoc; reflexivity).
assert (HLj : length js3 = (length HPFX + length chs + length (w7_sepb pb) + length (w7_pab pb))%nat) by (unfold js3; rewrite !length_app; lia).
assert (TT3 : forall j, (j < length js3)%nat ->
  aview rsegs (w_H W2) mI3 (F + 0x20 + Z.of_nat j) = Some (bv_unsigned (nth j js3 (Z_to_bv 8 0)))).
{ apply (w7_tt_step W2 mI2 mI3 (F + 0x20) ((HPFX ++ chs) ++ w7_sepb pb) (w7_pab pb) TT2).
  - intros j Hj. rewrite !length_app in Hj. pose proof w7_hpfx_len.
    rewrite (KI3 (F + 0x20 + Z.of_nat j) ltac:(lia) ltac:(cbv beta; unfold ESTACK; lia)). apply HKC2; [lia | exact (fun f => f)].
  - intros j Hj. rewrite <- (TI3 j Hj). f_equal; rewrite !length_app; lia. }
set (ntot := Z.of_nat (length js3)).
assert (Hnt : ntot = 0 + Z.of_nat (length HPFX) + Z.of_nat (length chs) + Z.of_nat (length (w7_sepb pb)) + Z.of_nat (length (w7_pab pb))) by (unfold ntot; rewrite HLj; lia).
assert (Hnt44 : 13 <= ntot <= 44) by (pose proof w7_hpfx_len; lia).
(* ======================== D: the 95 clamp, memcpy(e.body, t, n) ======================== *)
assert (EB : val_mem rsegs (mrestrict (w_H W2) mI3) (R + 0xe0) 8 (F + 0xf8)).
{ rewrite <- (w7_mod_small (F + 0xf8)) by lia. apply (w7_vm_kept W2 mem2 mI3 _ 8 _ Cc0).
  intros q Hq. apply KFI3; [lia | unfold Acc; lia]. }
eapply SRr_bind.
{ apply (w7_D B LAWS STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mI3 dI3 k0 rI3 R
    (0 + Z.of_nat (length HPFX) + Z.of_nat (length chs) + Z.of_nat (length (w7_sepb pb))) (Z.of_nat (length (w7_pab pb))) (F + 0x20) (F + 0xf8) HJI3).
  - refine (eq_trans (PRI3a 9 ltac:(unfold acallee_saved; lia) ltac:(cbn; lia)) _). exact B9.
  - lia.
  - lia.
  - exact HR16.
  - refine (eq_trans (PRI3 20 ltac:(unfold acallee_saved; lia) ltac:(lia)) _). transitivity (w64 (R + 0x148 + 8 * Z.of_nat 2)); [exact RC2s4 | f_equal; lia].
  - refine (eq_trans (PRI3 24 ltac:(unfold acallee_saved; lia) ltac:(lia)) _). exact RC2s8.
  - exact RI3s11.
  - pose proof w7_hpfx_len. lia.
  - lia.
  - refine (eq_trans (PRI3a 26 ltac:(unfold acallee_saved; lia) ltac:(cbn; lia)) _). exact B26.
  - exact EB.
  - lia. }
cbv beta. intros W1 c1 _ (-> & rD & mD & dD & -> & HJD & HioD & HrD & HKD & HpD & (RDra & RDa0 & RDa1 & RDa2 & RDs4 & RDs8)).
assert (PRDa : forall r, acallee_saved r -> ~ In r [20; 24; 25; 27] -> getr rD (Z_to_bv 5 r) = getr rA2 (Z_to_bv 5 r)).
{ apply (w7_pres_step rI3 rD rA2 [1; 10; 11; 12; 20; 24]%bv); [exact HrD | exact PRI3a | w7_clobX]. }
assert (KFD : w7_kept W2 mem2 mD Acc).
{ apply (w7_kept_trans W2 mem2 mI3 mD Acc _ Acc KFI3 HKD). intros a [Ha|[]]; exact Ha. }
assert (TTD : forall j, (j < length js3)%nat ->
  aview rsegs (w_H W2) mD (F + 0x20 + Z.of_nat j) = Some (bv_unsigned (nth j js3 (Z_to_bv 8 0)))).
{ intros j Hj. rewrite (HKD (F + 0x20 + Z.of_nat j) ltac:(lia) (fun f => f)). exact (TT3 j Hj). }
destruct (w7_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJD HinS2 EF2) as (_ & _ & _ & _ & _ & HFsD).
assert (SPD : spZ rD = sp0 + (R - sp0)).
{ unfold spZ. rewrite (w7_reg_eq rA2 rD 2%bv (PRDa 2 ltac:(unfold acallee_saved; lia) ltac:(cbn; lia))), B2.
  unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (FSHD : hd_fsh rsegs (w_H W2) mD F (hm_sh true true false true false false)) by exact (FSHm mD KFD).
eapply SRr_bind.
{ apply (w7_memcpy_at B LAWS AMEMCPY W2 rD mD STK sp0 FP ly S W0 mem0 md0 own ly2 S2 dD k0 (F + 0xf8) (F + 0x20) ntot (R - sp0)
    (w64 W7_AFTER_TEXT) HJD RDa0 RDa1).
  - rewrite Hnt. exact RDa2.
  - lia.
  - lia.
  - lia.
  - exact SPD.
  - rewrite Zminus_mod, HR16, HRb. reflexivity.
  - lia.
  - unfold ESTACK in *. lia.
  - rewrite (w7_reg_eq rA2 rD 3%bv (PRDa 3 ltac:(unfold acallee_saved; lia) ltac:(cbn; lia))). exact B3.
  - rewrite (w7_reg_eq rA2 rD 4%bv (PRDa 4 ltac:(unfold acallee_saved; lia) ltac:(cbn; lia))). exact B4.
  - exact RDra.
  - apply ret_ok_even; vm_compute; reflexivity.
  - intros a Ha. split; [apply (w7_awr_frame _ _ _ _ _ _ _ pos F a Hown EF2); left; lia | unfold ESTACK in *; lia].
  - apply Ham; lia.
  - pose proof (hm_A_ra_e rsegs (w_H W2) mD F true true false false false 8 ntot FSHD
      (w7_mod32_8 F HF32) ltac:(lia) ltac:(lia)) as X.
    unfold HM_E in X. replace (F + 0xf0 + 8) with (F + 0xf8) in X by lia. exact X.
  - intros Hl.
    apply (w7_hull_frame W2 mD F 0xf8); [exact HF32 | lia | lia | lia | lia | exact HFsD].
  - lia.
  - lia.
  - intros a Ha. split.
    + replace a with (F + 0x20 + Z.of_nat (Z.to_nat (a - (F + 0x20)))) by lia.
      rewrite (TTD (Z.to_nat (a - (F + 0x20))) ltac:(unfold ntot in Ha; lia)). discriminate.
    + rewrite SPD. unfold ESTACK in *. lia.
  - lia.
  - apply Ham; lia.
  - pose proof (hm_A_ra_t rsegs (w_H W2) mD F true false true false false 0 ntot FSHD
      (w7_mod32_8 F HF32) ltac:(lia) ltac:(lia)) as X.
    unfold HM_T in X. replace (F + 0x20 + 0) with (F + 0x20) in X by lia. exact X.
  - intros Hl.
    apply (w7_hull_frame W2 mD F 0x20); [exact HF32 | lia | lia | lia | lia | exact HFsD]. }
cbv beta. intros W1 c1 _ (-> & rM & mM & dM & -> & HJM & HioM & HPM & RMa0 & HCM & HKM & HpM).
(* ======================== E1: the NUL's address ======================== *)
eapply SRr_bind.
{ apply (w7_E1 B LAWS STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mM dM k0 rM (F + 0xf8) ntot HJM).
  - rewrite (w7_reg_eq rD rM 20%bv (HPM 20 ltac:(unfold acallee_saved; lia))). exact RDs4.
  - rewrite (w7_reg_eq rD rM 24%bv (HPM 24 ltac:(unfold acallee_saved; lia))). rewrite Hnt. exact RDs8.
  - lia.
  - lia.
  - lia. }
cbv beta. intros W1 c1 _ (-> & rE & mE & dE & -> & HJE & HioE & HrE & HKE & HpE & (REa0 & REs8)).
assert (PREa : forall r, acallee_saved r -> ~ In r [20; 24; 25; 27] -> getr rE (Z_to_bv 5 r) = getr rA2 (Z_to_bv 5 r)).
{ apply (w7_pres_step rM rE rA2 [10; 24]%bv); [exact HrE | | w7_clobX].
  intros q Hq Hn. rewrite (HPM q Hq). exact (PRDa q Hq Hn). }
assert (HshFd : shadow_addr F + 80 <= F \/ F + 1024 <= shadow_addr F).
{ unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. unfold shadow_addr, SHADOW_OFF.
  pose proof (Z.div_mod F 8 ltac:(lia)). pose proof (Z.mod_pos_bound F 8 ltac:(lia)). lia. }
(* the bytes of [R, R + 0x120) and of e and the frame's shadow outside what E2 writes, from G to before E2 *)
assert (KGE : forall a, 0 <= a < 2 ^ 64 -> ~ Acc a -> ~ (F + 0xf8 <= a < F + 0xf8 + ntot) -> ~ (R - 4096 <= a < R) ->
  aview rsegs (w_H W2) mE a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha H1 H2 H3. rewrite (HKE a Ha (fun f => f)), (HKM a Ha H2 ltac:(unfold ESTACK; lia)). exact (KFD a Ha H1). }
assert (CellE : forall o v, val_mem rsegs (mrestrict (w_H W2) mem2) (R + o) 8 v -> 0 <= o -> o + 8 <= 0x140 ->
  val_mem rsegs (mrestrict (w_H W2) mE) (R + o) 8 v).
{ intros o v V H1 H2. apply (w7_vm_kept W2 mem2 mE _ 8 _ V). intros q Hq. apply KGE; [lia | unfold Acc; lia | lia | lia]. }
(* ======================== E2: NUL, e.type, e.size, t and ch out of scope, the reloads, j J ======================== *)
eapply SRr_bind.
{ apply (w7_E2 B LAWS STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mE dE k0 rE R (shadow_addr F) (F + 0xf8 + ntot) (F + 0xf0) (ntot + 1) cur
    ((pp + 0x4000) mod 2 ^ 64) (shadow_addr (pp + 0x4000) mod 2 ^ 64) (pp mod 2 ^ 64) HJE).
  - exact REa0.
  - refine (eq_trans (PREa 9 ltac:(unfold acallee_saved; lia) ltac:(cbn; lia)) _). exact B9.
  - lia.
  - lia.
  - exact HR16.
  - refine (eq_trans (PREa 19 ltac:(unfold acallee_saved; lia) ltac:(cbn; lia)) _).
    refine (eq_trans (PRA2 19 ltac:(unfold acallee_saved; lia) ltac:(cbn; lia)) _). exact (w7_lit _ 19%bv _ G19).
  - refine (eq_trans (PREa 21 ltac:(unfold acallee_saved; lia) ltac:(cbn; lia)) _). exact RA2s5.
  - exact REs8.
  - lia.
  - rewrite <- (w7_mod_small (F + 0xf0)) by lia. apply CellE; [exact Cf0 | lia | lia].
  - apply CellE; [exact C80 | lia | lia].
  - apply CellE; [exact Cb0 | lia | lia].
  - apply CellE; [exact C70 | lia | lia].
  - lia.
  - lia.
  - lia.
  - exact HshF0.
  - lia.
  - unfold ESTACK in HFsb. lia.
  - apply Z.mod_pos_bound. lia.
  - apply Z.mod_pos_bound. lia.
  - apply Z.mod_pos_bound. lia.
  - apply (w7_awr_frame _ _ _ _ _ _ _ pos F _ Hown EF2). left. lia.
  - intros a Ha. apply (w7_awr_frame _ _ _ _ _ _ _ pos F a Hown EF2). left. lia.
  - intros a Ha. apply (w7_awr_frame _ _ _ _ _ _ _ pos F a Hown EF2). right. lia. }
cbv beta. intros W1 c1 _ (-> & rJ & mJ & dJ & -> & HJJ & HioJ & HrJ & HKJ & HpJ & (RJ27 & RJ20 & RJ25 & RJ21 & XB0 & EA0 & EA4 & SHJ)).
assert (PRJa : forall r, acallee_saved r -> ~ In r [20; 21; 24; 25; 27] -> getr rJ (Z_to_bv 5 r) = getr rA2 (Z_to_bv 5 r)).
{ apply (w7_pres_step rE rJ rA2 [10; 11; 20; 21; 25; 27]%bv); [exact HrJ | | w7_clobX].
  intros q Hq Hn. apply PREa; [exact Hq | cbn in Hn |- *; lia]. }
(* from G to J, every byte the piece does not write *)
assert (KGJ : forall a, 0 <= a < 2 ^ 64 -> ~ Acc a -> ~ (F + 0xf0 <= a <= F + 0xf8 + ntot) -> ~ (R - 4096 <= a < R) ->
  ~ (shadow_addr F + 4 <= a < shadow_addr F + 0x10) -> ~ (shadow_addr F + 0x14 <= a < shadow_addr F + 0x17) ->
  aview rsegs (w_H W2) mJ a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha H1 H2 H3 H4 H5. rewrite (HKJ a Ha ltac:(cbv beta; lia)). apply KGE; [exact Ha | exact H1 | lia | exact H3]. }
assert (Hntd : ntot = Z.of_nat (length js3)) by reflexivity.
assert (Hppn : ppn = Layout.PP_SIZE) by (unfold ppn, req_size, Layout.PP_SIZE; reflexivity).
assert (HppR : pp + ppn <= R - 2 * ESTACK) by (unfold ESTACK; lia).
assert (HinSc : In (4, pos) (frames (x_Sc rsegs cx))) by (rewrite <- Hfrs; exact HinS2).
assert (HFpp : F + 1024 <= pp \/ pp + ppn <= F).
{ destruct (al_sep _ _ LAWS _ _ _ _ _ HAR0) as [Hpw _].
  pose proof (w7_pw_in _ _ _ _ Hpw (in_map (fun b => (fst b, req_size (snd b))) _ _ Hppin)
     (in_map (fun f => (frame_addr (x_lyc rsegs cx) (fst f) (snd f), fs_frame_bytes (fst f))) _ _ HinSc)) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. replace (fs_frame_bytes 4) with 1024 in Hd by reflexivity. fold ppn in Hd.
  pose proof HFe. lia. }
assert (Hppsh : pp + ppn <= shadow_addr F \/ shadow_addr F + 80 <= pp).
{ pose proof ASAN_CEIL_range. unfold in_app, kLowShadowBeg, kHighMemBeg in Hppapp, HFapp. unfold shadow_addr, SHADOW_OFF.
  pose proof (Z.div_mod F 8 ltac:(lia)). pose proof (Z.mod_pos_bound F 8 ltac:(lia)). lia. }
pose proof HPB as (_ & _ & _ & _ & HWF & _ & _ & _ & _ & _ & _ & _ & _ & HPSL & _ & HESW & HESL & _).
change (mkCfg (mkst rJ (Z_to_bv 64 W7_J) mJ (seg_rom rsegs)) dJ) with (cfg_at rsegs HS_J rJ mJ dJ).
apply (HJc ly2 S2 W2 rJ mJ dJ sh np ps cnt es rr r (ent_text (w7_js chs pb) true) Hip Hk).
unfold ESTACK in *.
unfold hs_cut_J.
split; [|split; [|split; [|split; [|split; [|split]]]]].
- (* the pod base: the journal-and-frame part moves, the rest is G's *)
  destruct HPB as (_ & HPBr). split; [|exact HPBr].
  unfold hs_core, hs_mid. split; [exact HJJ|]. split.
  { intros q Hq. assert (Hc : acallee_saved q) by (unfold acallee_saved; lia).
    rewrite (PRJa q Hc ltac:(cbn; lia)), (PRA2 q Hc ltac:(cbn; lia)). exact (Hr234 q Hq). }
  split; [exact Hfrs|]. split; [exact Hperm|]. split.
  { eapply same_io_trans; [exact HioG|]. eapply same_io_trans; [exact HioA1|]. eapply same_io_trans; [exact HioA2|].
    eapply same_io_trans; [exact HioI0|]. eapply same_io_trans; [exact HioC0|]. eapply same_io_trans; [exact HioI1|].
    eapply same_io_trans; [exact HioC1|]. eapply same_io_trans; [exact HioI2|]. eapply same_io_trans; [exact HioC2|].
    eapply same_io_trans; [exact HioI3|]. eapply same_io_trans; [exact HioD|]. eapply same_io_trans; [exact HioM|].
    eapply same_io_trans; [exact HioE|]. exact HioJ. }
  split; [exact Hmo|].
  intros a Ha Hs HE. rewrite <- (HKG a Ha Hs HE). rewrite HspR in Hs. unfold T_SEG_STK, ASTACK in Hs.
  unfold hs_E1, hd_inw in HE. cbn [hi_w1 headamp_himg_A] in HE. rewrite !Exists_cons, Exists_nil in HE. cbn [hd_xv fst snd] in HE.
  fold e R F pp in HE.
  apply KGJ; [exact Ha | unfold Acc | | | |]; lia.
- (* the locations *)
  assert (CellJ : forall o v, hd_at rsegs (w_H W2) mem2 regs2 e (LCell XR o) v -> 0 <= o -> o + 8 <= 0x120 ->
    hd_at rsegs (w_H W2) mJ rJ e (LCell XR o) v).
  { intros o v Af H1 H2. cbn [hd_at hd_xv] in Af |- *. fold R in Af |- *.
    apply (w7_vm_kept W2 mem2 mJ _ 8 _ Af). intros q Hq. unfold ESTACK in *.
    apply KGJ; [lia | unfold Acc; lia | lia | lia | lia | lia]. }
  unfold hs_at_cx, hs_at in HAT |- *. unfold hs_L_Dc0 in HAT. rewrite !Forall_app in HAT.
  destruct HAT as [[ARc [AKc A6]] Atl]. apply Forall_cons_iff in Atl as [A8 _].
  unfold hs_Rc, hs_L_Dc, hs_L_Dc0. rewrite !Forall_app.
  assert (JRc : Forall (fun f => hd_at rsegs (w_H W2) mJ rJ (x_e rsegs cx) (fst f) (snd f)) (hs_Rc0 rsegs cx)).
  { unfold hs_Rc0 in ARc |- *. cbv zeta in ARc |- *. rewrite Forall_forall in ARc |- *. intros f Hf. pose proof (ARc f Hf) as Af.
    cbn [In] in Hf. destruct Hf as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; cbn [fst snd hd_at] in Af |- *.
    all: first
      [ match goal with |- getr _ (Z_to_bv 5 ?q) = _ =>
          rewrite (PRJa q ltac:(unfold acallee_saved; lia) ltac:(cbn; lia)), (PRA2 q ltac:(unfold acallee_saved; lia) ltac:(cbn; lia)); exact Af end
      | etransitivity; [exact RJ21 | apply w7_w64_mod] ]. }
  assert (J27 : Forall (fun f => hd_at rsegs (w_H W2) mJ rJ (x_e rsegs cx) (fst f) (snd f)) [(LReg 27, e_pp (x_e rsegs cx))]).
  { apply Forall_cons; [cbn [fst snd hd_at]; etransitivity; [exact RJ27 | apply w7_w64_mod] | apply Forall_nil]. }
  assert (JKc : Forall (fun f => hd_at rsegs (w_H W2) mJ rJ (x_e rsegs cx) (fst f) (snd f)) (hs_Kc rsegs cx sh np)).
  { unfold hs_Kc in AKc |- *. cbv zeta in AKc |- *. rewrite Forall_forall in AKc |- *. intros f Hf. pose proof (AKc f Hf) as Af.
    cbn [In] in Hf. repeat (destruct Hf as [<-|Hf]; [cbn [fst snd] in Af |- *; apply CellJ; [exact Af | lia | lia] |]). destruct Hf. }
  assert (J6 : Forall (fun f => hd_at rsegs (w_H W2) mJ rJ (x_e rsegs cx) (fst f) (snd f))
    [(LCell XR 0xd8, Z.of_nat (length ps)); (LCell XR 0xc0, hs_at_of sh ps); (LCell XR 0xc8, cnt); (LCell XR 0xa8, 1);
     (LCell XR 0xe8, hs_first ps); (LCell XR 0xf8, Z.of_nat (length es))]).
  { rewrite Forall_forall in A6 |- *. intros f Hf. pose proof (A6 f Hf) as Af.
    cbn [In] in Hf. repeat (destruct Hf as [<-|Hf]; [cbn [fst snd] in Af |- *; apply CellJ; [exact Af | lia | lia] |]). destruct Hf. }
  repeat split; try assumption.
  apply Forall_cons; [cbn [fst snd hd_at]; etransitivity; [exact RJ20 | apply w7_w64_mod] |].
  apply Forall_cons; [cbn [fst snd hd_at]; exact RJ25 |].
  apply Forall_cons; [cbn [fst snd]; apply CellJ; [exact A8 | lia | lia] | apply Forall_nil].
- (* the frame's shadow: t and ch out of scope *)
  unfold hs_fsh_at. intros i Hi. fold e F. replace (length hs_PJ) with 80%nat in Hi by reflexivity.
  destruct (w7_PG_PJ i ltac:(lia)) as [P1 P2].
  assert (Hc : (4 <= i < 16 \/ 20 <= i < 23) \/ ~ (4 <= i < 16 \/ 20 <= i < 23)) by lia.
  destruct Hc as [Hc|Hc].
  + rewrite (P1 Hc). exact (SHJ i Hc).
  + rewrite (P2 Hc). unfold hs_fsh_at in HFSH. rewrite (KGJ (shadow_addr F + i) ltac:(lia) ltac:(unfold Acc; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    exact (HFSH i ltac:(replace (length hs_PG) with 80%nat by reflexivity; lia)).
- (* the first block *)
  unfold hs_pp_at in HPP |- *. apply (hm_bytes_kept rsegs (w_H W2) mem2 (w_H W2) mJ pp _ HPP).
  intros x Hx. rewrite (w7_pp_len sh ps es HWF HESW HESL HPSL) in Hx.
  apply KGJ; [lia | unfold Acc; lia | lia | lia | lia | lia].
- (* e *)
  rewrite (w7_ent_text_js chs pb Hchl). rewrite <- Hjs3. fold e F.
  apply (w7_e_bytes W2 mJ F ntot js3 Hntd ltac:(lia) EA0 EA4 XB0).
  + intros j Hj. rewrite (HKJ (F + 0xf8 + Z.of_nat j) ltac:(lia) ltac:(cbv beta; lia)), (HKE (F + 0xf8 + Z.of_nat j) ltac:(lia) (fun f => f)).
    rewrite (HCM (Z.of_nat j) ltac:(lia)). exact (TTD j Hj).
  + intros j Hj. rewrite (KGJ (F + 0xf0 + Z.of_nat j) ltac:(lia) ltac:(unfold Acc; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    rewrite (proj1 (hm_bytes_aview rsegs (w_H W2) mem2 (F + 0xf0) (zeros 104)) HE0 j ltac:(unfold zeros; rewrite repeat_length; lia)).
    unfold zeros, NUL. rewrite nth_repeat. rewrite hm_unsigned_byte. reflexivity.
- symmetry. exact (w7_ent_build_0 rr chs pb r Hkind Hg Hchl).
- rewrite (w7_ent_text_js chs pb Hchl). unfold ent_wf. cbn [e_type e_size e_body]. pose proof (w7_js_len chs pb Hchl).
  rewrite length_app. cbn [length]. unfold POD_STRING. lia. } } } }
Qed.
End d.
End b.
Check w7b_piece_A.
Print Assumptions w7b_piece_A.
Print Assumptions w7_e_bytes.
