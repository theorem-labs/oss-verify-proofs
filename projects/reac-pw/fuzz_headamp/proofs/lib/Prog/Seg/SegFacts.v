(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 456 of its 574 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/U/Prog/Seg/Tac_slot.v, with its module names changed; 277 of its 306 lines of code are new or changed and 545 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/U/Prog/Seg/M03.v, with its module paths and module names changed; 187 of its 226 lines of code are new or changed and 267 lines of the source are left out. *)
(* Facts the segment walks of reac-pw/fuzz_headamp LLVMFuzzerTestOneInput (plain) use, stated over plain inputs
   (registers, memory, byte lists, numbers), with no slot frame, cut or ghost in any statement, so that a cut-free
   copy of a walk can use them as they are. One copy each; the segment files Prog/Seg/M01.v .. M04.v and X01.v
   instantiate them at the ghost's input (g_in g) or its tail (g_rest g).
   - Bytes: the tail of a byte run, the run after the two harness bytes, the thirteen saved words at S - 104.
   - The input cursor (Pod/Cursor.v fuzz_u8 twice, fuzz.h:37-43): the tail is skipn 2, null = data[0] & 1 is 0 or
     1, cap = data[1] mod 10 is in [0, 9].
   - The model (Pod/Model.v pod_build_wf, Pod/Spa.v buf_header, Pod/Layout.v length_pp_bytes): the record of any
     input is well formed, its buffer has 8 .. 5440 bytes, its pp image 19744.
   - The answer (Pod/Headamp.v parse_props_total, Spec/HeadBytes.v answer_ok_parts): answer_ok, -1 <= rc <= cap,
     out_after is 3 (cap + 1) bytes, first_req's bounds, the cells by the sign of rc.
   - Memory: the CJ normalization keeps the bytes outside the image below TASK_SIZE and the stack region; errno
     (tp - 164 = 0x3017c) is a readable and writable 4-byte cell on every memory (each byte lies in a writable image
     segment that gives it an initial byte); errno, the SSP GOT slot 0x1eea8 and the guard 0x50490 are image bytes;
     a range of non-image bytes is apart from a range of image bytes; the SSP cells from an allocator relation's
     statics (YL01.ax_statics). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Contract Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require MemNorm KindBGlue.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Model Layout Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Spa Cursor.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import reac_headamp_prop_parse_result_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import SlotInv.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.Seg Require Import Tac_slot.
Import ListNotations.
Open Scope Z_scope.

(* ---- Bytes ---- *)

(* The bytes after the first one. *)
Lemma sf_ba_tl : forall m a b l, bytes_at rsegs m a (b :: l) -> bytes_at rsegs m (a + 1) l.
Proof.
  intros m a b l (H1 & H2 & H). cbn [length] in H2. split; [lia|]. split; [lia|].
  intros i Hi. replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (S i)) by lia. apply H. cbn [length]. lia.
Qed.

(* The bytes after the first min 2 (length l) of them. *)
Lemma sf_ba_skip2 : forall m a l, bytes_at rsegs m a l ->
  bytes_at rsegs m (a + Z.min 2 (Z.of_nat (length l))) (skipn 2 l).
Proof.
  intros m a [|b [|c l]] H; cbn [skipn length].
  - pose proof H as (H1 & H2 & _). cbn [length] in H2.
    replace (a + Z.min 2 (Z.of_nat 0)) with a by lia. apply sl_bytes_nil. lia.
  - pose proof H as (H1 & H2 & _). cbn [length] in H2.
    replace (a + Z.min 2 (Z.of_nat 1)) with (a + 1) by lia. apply sl_bytes_nil. lia.
  - apply sf_ba_tl in H. apply sf_ba_tl in H.
    replace (a + Z.min 2 (Z.of_nat (S (S (length l))))) with (a + 1 + 1) by lia. exact H.
Qed.

(* Thirteen words in a row at S - 104 (the harness's saved s11, s10, .., s2, s1, s0, ra), word by word. *)
Lemma sf_saved_split : forall mem S (r27 r26 r25 r24 r23 r22 r21 r20 r19 r18 r9 r8 r1 : word),
  bytes_at rsegs mem (S - 104)
    (le8 r27 ++ le8 r26 ++ le8 r25 ++ le8 r24 ++ le8 r23 ++ le8 r22 ++ le8 r21 ++ le8 r20 ++ le8 r19 ++
     le8 r18 ++ le8 r9 ++ le8 r8 ++ le8 r1) ->
  bytes_at rsegs mem (S - 104) (le8 r27) /\ bytes_at rsegs mem (S - 96) (le8 r26) /\
  bytes_at rsegs mem (S - 88) (le8 r25) /\ bytes_at rsegs mem (S - 80) (le8 r24) /\
  bytes_at rsegs mem (S - 72) (le8 r23) /\ bytes_at rsegs mem (S - 64) (le8 r22) /\
  bytes_at rsegs mem (S - 56) (le8 r21) /\ bytes_at rsegs mem (S - 48) (le8 r20) /\
  bytes_at rsegs mem (S - 40) (le8 r19) /\ bytes_at rsegs mem (S - 32) (le8 r18) /\
  bytes_at rsegs mem (S - 24) (le8 r9) /\ bytes_at rsegs mem (S - 16) (le8 r8) /\
  bytes_at rsegs mem (S - 8) (le8 r1).
Proof.
  intros mem S r27 r26 r25 r24 r23 r22 r21 r20 r19 r18 r9 r8 r1 H.
  repeat (apply bytes_at_app in H; destruct H as [?H H]; rewrite length_le8 in H).
  repeat match goal with |- _ /\ _ => split end;
    match goal with H : bytes_at _ _ ?a (le8 ?v) |- bytes_at _ _ ?b (le8 ?v) => replace b with a by lia; exact H end.
Qed.

(* ---- The input cursor: fuzz_u8 twice ---- *)

(* The input after the two harness bytes (no advance past the end). *)
Lemma sf_rest_eq : forall inp, snd (Cursor.fuzz_u8 (snd (Cursor.fuzz_u8 inp))) = skipn 2 inp.
Proof. intros inp. destruct inp as [|b [|c l]]; reflexivity. Qed.

Lemma sf_rest_len : forall inp,
  Z.of_nat (length (snd (Cursor.fuzz_u8 (snd (Cursor.fuzz_u8 inp))))) =
  Z.of_nat (length inp) - Z.min 2 (Z.of_nat (length inp)).
Proof. intros inp. rewrite sf_rest_eq, length_skipn. lia. Qed.

(* null = the first byte & 1. *)
Lemma sf_null_rng : forall inp, 0 <= Z.land (fst (Cursor.fuzz_u8 inp)) 1 <= 1.
Proof.
  intros inp.
  pose proof (Z.land_ones (fst (Cursor.fuzz_u8 inp)) 1 ltac:(lia)) as E. change (Z.ones 1) with 1 in E.
  change (2 ^ 1) with 2 in E. rewrite E. pose proof (Z.mod_pos_bound (fst (Cursor.fuzz_u8 inp)) 2 ltac:(lia)). lia.
Qed.

(* cap = the second byte mod 10. *)
Lemma sf_cap_rng : forall inp, 0 <= fst (Cursor.fuzz_u8 (snd (Cursor.fuzz_u8 inp))) mod 10 <= 9.
Proof.
  intros inp. pose proof (Z.mod_pos_bound (fst (Cursor.fuzz_u8 (snd (Cursor.fuzz_u8 inp)))) 10 ltac:(lia)). lia.
Qed.

(* ---- The record pod_build makes of any input ---- *)

Lemma sf_rec_wf : forall inp, pod_rec_wf (head_rec inp).
Proof.
  intros inp. unfold head_rec. apply (pod_build_wf inp _ (snd (pod_build inp))). apply surjective_pairing.
Qed.

Lemma sf_len_bound : forall inp, 8 <= head_len inp <= 5440.
Proof. intros inp. destruct (Spa.buf_header (head_rec inp) (sf_rec_wf inp)) as (_ & _ & _ & H). exact H. Qed.

Lemma sf_pp_len : forall inp, Z.of_nat (length (pp_bytes (head_rec inp))) = POD_PROPS.
Proof. intros inp. rewrite (length_pp_bytes (head_rec inp) (sf_rec_wf inp)). reflexivity. Qed.

(* ---- The parse's answer ---- *)

Lemma sf_ans_ok : forall nl cap inp, 0 <= cap -> answer_ok cap (head_ans nl cap inp).
Proof. intros nl cap inp Hc. unfold head_ans. exact (parse_props_total _ cap Hc). Qed.

Lemma sf_rc_bound : forall nl cap inp, 0 <= cap -> -1 <= ans_rc (head_ans nl cap inp) <= cap.
Proof.
  intros nl cap inp Hc.
  destruct (answer_ok_parts cap _ (sf_ans_ok nl cap inp Hc)) as [[(E & _) | (E1 & _)] _]; lia.
Qed.

Lemma sf_out_after_len : forall cap o, 0 <= cap -> answer_ok cap o ->
  Z.of_nat (length (out_after cap o)) = OUT_LEN cap.
Proof.
  intros cap o Hc HO. unfold out_after. rewrite length_app, repeat_length, length_ha_cells_bytes.
  destruct (answer_ok_parts cap o HO) as [[(E1 & E2 & _) | (E1 & E2 & _)] _].
  - rewrite E2. cbn [length]. unfold OUT_LEN. lia.
  - unfold OUT_LEN. lia.
Qed.

Lemma sf_first_req : forall rc, rc <= 9 -> 1 <= first_req rc <= 27.
Proof. intros rc H. unfold first_req. destruct (Z.ltb_spec 0 rc); lia. Qed.

Lemma sf_first_max : forall rc, 3 * Z.max rc 0 <= first_req rc.
Proof. intros rc. unfold first_req. destruct (Z.ltb_spec 0 rc); lia. Qed.

(* The cells of an answer, by the sign of rc. *)
Lemma sf_cells_pos : forall cap o, answer_ok cap o -> 0 < ans_rc o ->
  Z.of_nat (length (ha_cells_bytes (ans_cells o))) = 3 * ans_rc o.
Proof.
  intros cap o HO Hp. rewrite length_ha_cells_bytes.
  destruct (answer_ok_parts cap o HO) as [[(E1 & _) | (E1 & E2 & _)] _]; lia.
Qed.

Lemma sf_cells_nonpos : forall cap o, answer_ok cap o -> ans_rc o <= 0 -> ans_cells o = [].
Proof.
  intros cap o HO Hn.
  destruct (answer_ok_parts cap o HO) as [[(E1 & E2 & _) | (E1 & E2 & _)] _]; [exact E2|].
  apply length_zero_iff_nil. lia.
Qed.

(* ---- The CJ normalization keeps every byte the segments read ---- *)

(* A byte outside every image segment and below TASK_SIZE survives normalize_cj. *)
Lemma sf_cj_keep : forall (w : word), bv_unsigned w < TASK_SIZE ->
  find_segment rsegs (bv_unsigned w) 1 = None -> MemNorm.cj_drop rsegs w = false.
Proof.
  intros w Ht Hns. apply MemNorm.cj_drop_false_intro; [|right; exact Ht].
  unfold Mem.ro_addr. rewrite Hns. reflexivity.
Qed.

(* A byte above the image and below TASK_SIZE (the stack window) survives normalize_cj. *)
Lemma sf_cj_hi : forall (w : word), SL_TOP <= bv_unsigned w -> bv_unsigned w < TASK_SIZE ->
  MemNorm.cj_drop rsegs w = false.
Proof.
  intros w Hlo Ht. apply sf_cj_keep; [exact Ht|].
  destruct (find_segment rsegs (bv_unsigned w) 1) as [seg|] eqn:E; [|reflexivity].
  exfalso. pose proof (sl_find_top (bv_unsigned w) 1 seg E). unfold SL_TOP in *. lia.
Qed.

(* The stack region on the CJ-normalized memory (Tac_slot.sl_stk_norm with normalize_cj). *)
Lemma sf_stk_cj : forall m lo hi, ro_agree rsegs m -> SL_TOP <= lo -> hi <= TASK_SIZE ->
  (forall a, lo <= a < hi -> writable_at rsegs m a) ->
  stk rsegs (MemNorm.normalize_cj rsegs m) lo hi.
Proof.
  intros m lo hi Hro Hlo Hhi H.
  assert (Htask : TASK_SIZE < 2 ^ 64) by (unfold TASK_SIZE; lia).
  apply sl_stk_of_writable; [exact Hlo | lia|].
  intros a Ha. unfold writable_at.
  assert (Hu : bv_unsigned (Z_to_bv 64 a) = a) by (apply MState.unsigned_lit; unfold SL_TOP in *; lia).
  rewrite (MemNorm.wview_rel_cj rsegs m _ (Z_to_bv 64 a) (MemNorm.mem_rel_cj_normalize rsegs m Hro)
             (sf_cj_hi (Z_to_bv 64 a) ltac:(rewrite Hu; unfold SL_TOP in *; lia) ltac:(rewrite Hu; lia))).
  exact (H a Ha).
Qed.

(* ---- errno's cell on any memory ---- *)

(* Each byte of errno (tp - 164 = 0x3017c) lies in a writable image segment that gives it an initial byte. *)
Lemma sf_errno_seg : forall i, 0 <= i < 4 ->
  wview rsegs (fun _ => None) (wa (0x3017c + i)) <> None /\ seg_rom rsegs (wa (0x3017c + i)) <> None.
Proof.
  intros i Hi. assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
  destruct E as [-> | [-> | [-> | ->]]]; split; vm_compute; intros H; discriminate H.
Qed.

Lemma sf_errno_access : forall m a, 0x3017c <= a < 0x3017c + 4 ->
  writable_at rsegs m a /\ exists v, mbyte rsegs m a = Some v.
Proof.
  intros m a Ha. destruct (sf_errno_seg (a - 0x3017c) ltac:(lia)) as [W R].
  replace (0x3017c + (a - 0x3017c)) with a in W, R by lia.
  unfold writable_at, wview, mbyte, wa in *. destruct (m (Z_to_bv 64 a)) as [v|] eqn:M.
  - split; [discriminate | exists v; reflexivity].
  - split; [exact W|]. change (YK11.seg_rom rsegs (Z_to_bv 64 a)) with (seg_rom rsegs (Z_to_bv 64 a)).
    destruct (seg_rom rsegs (Z_to_bv 64 a)) as [v|]; [exists v; reflexivity | contradiction].
Qed.

(* errno is a readable and writable 4-byte cell on every memory. *)
Lemma sf_errno_cells : forall m, exists ev, rw_cells rsegs m 0x3017c [C4 ev].
Proof.
  intros m.
  destruct (sf_errno_access m 0x3017c ltac:(lia)) as (_ & b0 & B0).
  destruct (sf_errno_access m (0x3017c + 1) ltac:(lia)) as (_ & b1 & B1).
  destruct (sf_errno_access m (0x3017c + 2) ltac:(lia)) as (_ & b2 & B2).
  destruct (sf_errno_access m (0x3017c + 3) ltac:(lia)) as (_ & b3 & B3).
  pose proof (bytes_le_to_Z_bound [b0; b1; b2; b3]) as N1. pose proof (bytes_le_to_Z_nonneg [b0; b1; b2; b3]) as N0.
  cbn [length Z.of_nat] in N1.
  exists (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3])).
  split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. unfold le4. rewrite MState.unsigned_lit by lia.
    change 4%nat with (length [b0; b1; b2; b3]). rewrite StrFun.Z_to_le_bytes_to_Z.
    split; [lia|]. split; [cbn [length]; lia|].
    intros i Hi. cbn [length] in Hi.
    destruct i as [|[|[|[|i]]]]; cbn [nth_error]; [| | | | lia].
    + change (Z.of_nat 0) with 0. rewrite Z.add_0_r. exact B0.
    + change (Z.of_nat 1) with 1. exact B1.
    + change (Z.of_nat 2) with 2. exact B2.
    + change (Z.of_nat 3) with 3. exact B3.
  - cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros i Hi.
    exact (proj1 (sf_errno_access m (0x3017c + i) ltac:(lia))).
Qed.

(* ---- Image ranges and the regions apart from them ---- *)

(* errno [0x3017c, 0x30180), the SSP GOT slot [0x1eea8, 0x1eeb0) and the guard [0x50490, 0x50498) lie in reserved
   image segments. *)
Lemma sf_resv_errno : existsb (fun s : word * word => (bv_unsigned (fst s) <=? 0x3017c) &&
    (0x3017c + 4 <=? bv_unsigned (fst s) + bv_unsigned (snd s))) (segments_reserved rsegs) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sf_resv_got : existsb (fun s : word * word => (bv_unsigned (fst s) <=? 0x1eea8) &&
    (0x1eea8 + 8 <=? bv_unsigned (fst s) + bv_unsigned (snd s))) (segments_reserved rsegs) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sf_resv_guard : existsb (fun s : word * word => (bv_unsigned (fst s) <=? 0x50490) &&
    (0x50490 + 8 <=? bv_unsigned (fst s) + bv_unsigned (snd s))) (segments_reserved rsegs) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sf_img_range : forall B c n a, ms_segs B = rsegs ->
  existsb (fun s : word * word => (bv_unsigned (fst s) <=? c) && (c + n <=? bv_unsigned (fst s) + bv_unsigned (snd s)))
    (segments_reserved rsegs) = true -> c <= a < c + n -> in_img B a.
Proof.
  intros B c n a HS H Ha. apply existsb_exists in H as (s & Hs & Hc).
  apply andb_true_iff in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  split; [rewrite HS; intros Hn; rewrite Hn in Hs; cbn in Hs; destruct Hs|].
  exists s. rewrite HS. split; [exact Hs | lia].
Qed.

Lemma sf_errno_in : forall B, ms_segs B = rsegs -> forall a, 0x3017c <= a < 0x3017c + 4 -> in_img B a.
Proof. intros B HS a Ha. exact (sf_img_range B 0x3017c 4 a HS sf_resv_errno Ha). Qed.

Lemma sf_got_in : forall B, ms_segs B = rsegs -> forall a, 0x1eea8 <= a < 0x1eea8 + 8 -> in_img B a.
Proof. intros B HS a Ha. exact (sf_img_range B 0x1eea8 8 a HS sf_resv_got Ha). Qed.

Lemma sf_guard_in : forall B, ms_segs B = rsegs -> forall a, 0x50490 <= a < 0x50490 + 8 -> in_img B a.
Proof. intros B HS a Ha. exact (sf_img_range B 0x50490 8 a HS sf_resv_guard Ha). Qed.

(* A nonempty interval [lo, hi) none of whose points has P is apart from a nonempty interval [c, c + n) all of whose
   points have P. *)
Lemma sf_apart : forall (P : Z -> Prop) lo hi c n, lo < hi -> 0 < n ->
  (forall a, lo <= a < hi -> ~ P a) -> (forall a, c <= a < c + n -> P a) ->
  c + n <= lo \/ hi <= c.
Proof.
  intros P lo hi c n Hlh Hn HA HB.
  destruct (Z_le_dec (c + n) lo) as [H|H]; [left; exact H|].
  destruct (Z_le_dec hi c) as [H'|H']; [right; exact H'|]. exfalso.
  destruct (Z_le_dec lo c) as [H2|H2].
  - apply (HA c); [lia | apply HB; lia].
  - apply (HA lo); [lia | apply HB; lia].
Qed.

(* ---- The SSP cells from an allocator relation's statics ---- *)
Section SSP.
Context {fx : FPState} {rc : RunCeil}.

Lemma sf_ssp : forall B MR, AllocExtra B MR -> ms_segs B = rsegs -> ms_got_guard B = 0x1eea8 ->
  ms_guard B = 0x50490 -> forall L A mem md, MR L A mem md ->
  bytes_at rsegs mem PARSE_SSP_GOT (le8 (Z_to_bv 64 PARSE_SSP_GUARD)) /\
  exists gv, 0 <= gv < 2 ^ 64 /\ bytes_at rsegs mem PARSE_SSP_GUARD (le8 (Z_to_bv 64 gv)).
Proof.
  intros B MR AX HS Egot Eguard L A mem md HM.
  destruct (ax_statics AX L A mem md HM) as (HG1 & (gv & Hgv & HG2) & _).
  rewrite Egot, Eguard in HG1. rewrite Eguard in HG2. rewrite HS in HG1, HG2.
  unfold PARSE_SSP_GOT, PARSE_SSP_GUARD.
  split.
  - exact (KindBGlue.word_mem_le8 rsegs mem 0x1eea8 0x50490 HG1 ltac:(lia) ltac:(lia) ltac:(lia)).
  - exists gv. split; [exact Hgv|].
    exact (KindBGlue.word_mem_le8 rsegs mem 0x50490 gv HG2 Hgv ltac:(lia) ltac:(lia)).
Qed.

End SSP.
