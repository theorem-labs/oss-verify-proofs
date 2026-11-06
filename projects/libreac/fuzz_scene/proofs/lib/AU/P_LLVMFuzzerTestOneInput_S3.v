(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: SEGMENT S3 of the ASan+UBSan walk of libreac/fuzz_scene's
   LLVMFuzzerTestOneInput: ONE turn of the whole_transfer loop, 0x82eac .. 0x82f6c, on the image
   fuzz_scene.asan-ubsan (sha256 e98b1ed286c1aa5c3d558cb2069011d2413d58b2122f741531364382a528833f). *)

(*   The statement proved here is `seg_S3_turn_stmt` of lib/AU/P_LLVMFuzzerTestOneInput_seg.v, at the geometry table
   `scene_geom_asan_ubsan` of that same file, with scene's own sink head passed explicitly (gate 6h).  Nothing of the
   cut file is restated: the lane takes cut_T / cut_TX exactly as that file states them.

   The turn, as the listing has it (a Theorem Labs lane's dis-LLVMF.asan-ubsan.txt; offsets from LLVMFuzzerTestOneInput
   0x828a4):
     0x82eac-0x82ec0  blk.i unpoison: sb zero,4(s3) .. sb zero,7(s3), li a0,2, sb a0,8(s3)
     0x82ec4-0x82ed4  a0 = s9 (blk.i), a2 = s11 (8904), a3 = s7 (k), jal reac_ctrl_build_scene_step; bnez a0 -> abort
     0x82ed8-0x82f14  the n_k and declared reads, the k = 0 split, UBSan guard 0x82eec, the bound test
                      `bltu s11,s8` 0x82f14 -> abort
     0x82f18-0x82f20  a0 = s9, a2 = s7, jal check_step
     0x82f24-0x82f44  UBSan guard 0x82f28, the source select on k = 0, jal __asan_memcpy
     0x82f48-0x82f6c  blk.i re-poison, k := k + 1, got := got + n_k, back edge `bne s7,a0(343)` -> 0x82eac
   Both UBSan guards are refuted here, from the cut's own bounds: 0x82eec `bltu (-9), s9` from blk.i = F + 32 with
   F inside the application range, 0x82f28 `bltu ~again, got` from again + 8904 <= alloc_ceiling and got <= 8904
   (s3_guard_blki / s3_guard_again below). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
(* gate 6o: in lib/AU only the image-differing modules come from lib.AU -- here YCbq, YC5d, YE01, YCbp. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YO09 YE00.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YE01 YCbp.
(* YK06 is NOT imported: it carries a second `alloc_ceiling` (and a second `alloc_ceiling_val`), and importing it
   after YM05 would make the unqualified name in this file a different constant from the one the cut speaks
   about. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05 YG0s YG0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import SceneBlock SceneTM.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaTable PaSym PaRun PaShadow.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import SceneSyms SceneList SceneAddr ScenePa SceneImg.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaJournal ScenePaLib SceneBase SceneRo SceneFrame YC85.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_LLVMFuzzerTestOneInput_ctx P_LLVMFuzzerTestOneInput_seg.
(* the two program callees of the turn, by the names their owners gave them:
   reac_ctrl_build_scene_step (a Theorem Labs lane) and check_step (a Theorem Labs lane). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_reac_ctrl_build_scene_step P_check_step.
(* st_ok_pi_submem and frm_off_imgP, which the run of the turn's first part uses. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import YC1h.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* =================================================================================================================
   PURE FACTS OF THE TURN.  Each is used to decide one branch of the turn or to read one field of blk.i; none
   speaks about the machine.
   ================================================================================================================= *)
Lemma s3_u8 : forall v, 0 <= v < 256 -> bv_unsigned (Z_to_bv 8 v) = v.
Proof.
intros v Hv. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
replace (2 ^ Z.of_N 8) with 256 by reflexivity. apply Z.mod_small. exact Hv.
Qed.

Lemma s3_len_cases : forall k, scene_len k = 24 \/ scene_len k = 26 \/ scene_len k = 14.
Proof.
intros k. unfold scene_len. destruct (k =? 0); [left; reflexivity|].
destruct (k =? 342); [right; right; reflexivity | right; left; reflexivity].
Qed.

(* blk[4] << 8 | blk[5], the n_k the turn computes at 0x82edc-0x82f0c, is scene_len k. *)
Lemma s3_nk : forall (b : list byte) (k : Z),
256 * bv_unsigned (nth 4 (scene_block b k) (Z_to_bv 8 0))
+ bv_unsigned (nth 5 (scene_block b k) (Z_to_bv 8 0)) = scene_len k.
Proof.
intros b k. rewrite scT_nth4, scT_nth5, (s3_u8 0 ltac:(lia)).
rewrite s3_u8 by (destruct (s3_len_cases k) as [H | [H | H]]; rewrite H; lia). lia.
Qed.

(* blk[7] << 8 | blk[8] at k = 0, the `declared` the turn stores at 0x82f00, is 8904. *)
Lemma s3_declared : forall b : list byte,
256 * bv_unsigned (nth 7 (scene_block b 0) (Z_to_bv 8 0))
+ bv_unsigned (nth 8 (scene_block b 0) (Z_to_bv 8 0)) = 8904.
Proof. intros b. rewrite scT_nth7_0, scT_nth8_0, !s3_u8 by lia. lia. Qed.

(* The bound test 0x82f14 `bltu s11,s8` (8904 <u got + n_k) is not taken. *)
Lemma s3_bound : forall k, 0 <= k <= 342 -> scT_off k + scene_len k <= 8904.
Proof. intros k Hk. destruct (scT_bnd k Hk) as (_ & H & _). exact H. Qed.

(* UBSan guard 0x82eec, on the k = 0 arm: `bltu a1,s9` with a1 = 2^64 - 9 and s9 = blk.i = F + 32.  The frame
   lies in the application range (al_frames: F + fs_frame_bytes 8 <= 140737479966720 < 2 ^ 47), so blk.i is far
   below 2^64 - 9 and the trap edge is dead. *)
Lemma s3_guard_blki : forall blki : Z, 0 <= blki < 2 ^ 47 -> ~ (2 ^ 64 - 9 < blki).
Proof. intros blki Hb. lia. Qed.

(* req_size of every block of this walk is the block's own size. *)

Lemma s3_req_size_scene : req_size 8904 = 8904.
Proof. reflexivity. Qed.

(* ---- blk.i's shadow INSIDE the turn.  The five stores 0x82eac-0x82ec0 leave shadow(F)+4..+8 = 00 00 00 00 02,
   which is exactly `block_shadow` of a 34-byte object at F + 32: four full granules and a 2-byte tail
   (YG0v.v:37-40).  `block_shadow_range` (YG0v.v:62) then gives the `range_addressable blk.i 34` that
   reac_ctrl_build_scene_step and check_step both ask for. ---- *)
Lemma s3_shadow_blki : forall (rd : Z -> option Z) (F : Z),
F mod 8 = 0 ->
(forall o, 4 <= o < 8 -> rd (shadow_addr F + o) = Some 0) ->
rd (shadow_addr F + 8) = Some 2 ->
block_shadow rd SHADOW_OFF (F + 32) 34.
Proof.
intros rd F HF H0 H2.
assert (Hd : (F + 32) / 8 = F / 8 + 4) by (replace (F + 32) with (F + 4 * 8) by lia; rewrite Z.div_add by lia; reflexivity).
assert (HS : shadow_of_addr SHADOW_OFF (F + 32) = shadow_addr F + 4)
by (unfold shadow_of_addr, shadow_addr; rewrite Hd; lia).
unfold block_shadow. rewrite HS.
split; [rewrite Z.add_mod by lia; rewrite HF; reflexivity|].
split; [lia|].
intros i Hi. change ((34 + 7) / 8) with 5 in Hi. change (34 / 8) with 4. change (34 mod 8) with 2.
destruct (Z.ltb_spec i 4) as [Hlt|Hge].
- replace (shadow_addr F + 4 + i) with (shadow_addr F + (4 + i)) by lia. apply H0. lia.
- replace (shadow_addr F + 4 + i) with (shadow_addr F + 8) by lia. exact H2.
Qed.

Lemma s3_ra_blki : forall (rd : Z -> option Z) (F : Z),
F mod 8 = 0 ->
(forall o, 4 <= o < 8 -> rd (shadow_addr F + o) = Some 0) ->
rd (shadow_addr F + 8) = Some 2 ->
range_addressable rd SHADOW_OFF (F + 32) 34.
Proof.
intros rd F HF H0 H2.
exact (block_shadow_range rd SHADOW_OFF (F + 32) 34 (F + 32) 34
(s3_shadow_blki rd F HF H0 H2) ltac:(lia) ltac:(lia)).
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {LS : lib_shape}.
(* RC1 / gate 6h: scene's own sink head, musl's ofl_head of this image, as an instance of this file and passed by
   name at every constant that takes one.  Never left to instance search, so that no other sink_head instance
   (such as a src0_sink_head or tfib_sink_head in another tree) can be picked up; none is in scope here. *)
#[local] Instance scene_sink_head : YI16.sink_head := {| YI16.sk_ofl_head := 0x5f7190 |}.
#[local] Notation SEGS := (@pa_segs _ scene_listing PI_scene).
#[local] Notation VAL := (@pa_val _ scene_listing PI_scene).
#[local] Notation SIGMA := (@pa_sigma _ scene_listing PI_scene).
#[local] Notation BASE := (@pa_val _ scene_listing PI_scene A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ scene_listing PI_scene).
#[local] Notation RHI := (@pa_relro_hi _ scene_listing PI_scene).

(* UBSan guard 0x82f28: `bltu a0,s6` with a0 = 2^64 - 1 - again (the `not` hoisted to 0x82e90-0x82e98) and
   s6 = got.  again lies below alloc_ceiling and got <= 8904, so again + got never reaches 2^64.  It is in this
   Section because `alloc_ceiling` is the kernel's, under the RunCeil instance. *)
Lemma s3_guard_again : forall again got : Z,
0 <= again -> again + 8904 <= alloc_ceiling -> 0 <= got <= 8904 -> ~ (2 ^ 64 - 1 - again < got).
Proof. intros again got H0 Hhi Hg. pose proof YM05.alloc_ceiling_lt as Hlt. lia. Qed.

(* ---- Four bridges between the cut and YP09's region predicate, proved by this lane's helper
   and pasted verbatim from its scratch file
   S3Entry_scratch.v (sha256 a43dfb21185b; internal record) lines 44-86.
   NOTE: YG01 declares a SECOND chunk_ok, over an astate, so every YP09 name below
   stays qualified. ---- *)

(* ---- four one-line bridges between the cut's reader facts and YP09's region predicate ---- *)
Lemma s3e_unsigned64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof.
intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
replace (2 ^ Z.of_N 64) with (2 ^ 64) by reflexivity. apply Z.mod_small. exact Hz.
Qed.

Lemma s3e_mbyte : forall (H : word -> bool) (m : word -> option byte) a v,
aview SEGS H m a = Some v -> mbyte SEGS (mrestrict H m) a = Some (Z_to_bv 8 v).
Proof.
intros H m a v Ha. unfold aview in Ha.
destruct (mbyte SEGS (mrestrict H m) a) as [x|] eqn:Hm; cbn in Ha; [|discriminate Ha].
injection Ha as <-. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* register atom i is register x_i (sr_atoms), and Eimg's image part never touches an index below 32. *)
Lemma s3e_ew : forall (regs : bvmap 5 word) (r : bv 5) (n : nat),
(n < 32)%nat -> Z.to_nat (bv_unsigned r) = n -> ew (Eimg (Ereg regs [])) n = getr regs r.
Proof.
intros regs r n Hn Hr. unfold Eimg. cbn [ew].
replace ((A_TEXT <=? n) && (n <? A_LIM))%nat with false.
2:{ symmetry. apply andb_false_iff. left. apply Nat.leb_gt. unfold A_TEXT. lia. }
rewrite <- Hr. apply ew_Ereg_reg.
Qed.

(* `CVal 1 (SLit (2 ^ 64 - 8))` pins exactly the low byte of s5, which is the poison byte 0xf8. *)
Lemma s3e_chunk_f8 : forall E (m : word -> option byte) base off,
mbyte SEGS m (base + off) = Some (Z_to_bv 8 248) ->
YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal 1 (SLit (2 ^ 64 - 8)))).
Proof.
intros E m base off Hm. unfold YP09.chunk_ok. intros i Hi.
cbn [YP09.c_len YP09.cv_len YP09.c_val] in Hi. replace i with 0 by lia.
exists (Z_to_bv 8 248). split.
- cbn [YP09.cbyte YP09.c_off YP09.c_val]. f_equal.
  unfold YP09.byte_of_word. cbn [sv_denot].
  rewrite (s3e_unsigned64 (2 ^ 64 - 8) ltac:(lia)).
  replace (8 * 0) with 0 by lia. rewrite Z.shiftr_0_r.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  replace (2 ^ Z.of_N 8) with 256 by reflexivity. reflexivity.
- cbn [YP09.c_off]. rewrite Z.add_0_r. exact Hm.
Qed.

Section h.
Variable B : asyms.
(* The walk's constant record, as the cut file's statements take it.  S3 never reads a field of it apart from the
   stack budget: the sink cells, the entry pc, the return address, the event and live budgets and the read-only
   window are carried through the cut, not used, so this lane is proved for the record the composition supplies. *)
Variable WK : swalk.
(* A Theorem Labs lane's ruling 04:04Z: segment-Section binding, discharged by the composition *)
Hypothesis HWRLO : sw_rlo WK = pa_relro_lo.
(* A Theorem Labs lane's ruling 04:04Z: segment-Section binding, discharged by the composition *)
Hypothesis HWRHI : sw_rhi WK = pa_relro_hi.
(* The walk's event budget, in the text a Theorem Labs lane's segment files state it (at 5560cdc9ff68
   lib/A/P_LLVMFuzzerTestOneInput_S1.v:144, at 61818d377d80 S5_kit.v:187, at 916e1f35ef3f S6.v:108): the composition builds WK with
   sw_ev = LLVMF_EV = 6.  check_step's premise `st_nev S + EV_CHECK_STEP <= EV_MAX` needs it: the journal bounds
   st_nev at the call by the entry's st_nev plus the turn's event count, and sc_base bounds the entry's by
   EV_MAX - sw_ev WK. *)
Hypothesis HEV : 6 <= sw_ev WK.
(* The static shadow and image-byte facts of reac_ctrl_build_scene_step.TAIL_TRAILER (0x20e20, 12 bytes), which
   build_scene_step's accepting call asks for.  HB_Z_TT / HB_C_TT: = entry statement Section h,
   lib/AU/P_LLVMFuzzerTestOneInput.v at 327f73c7513 (announced 04:57Z), with that file's two literal Definitions
   A_TAIL_TRAILER = 0x20e20 and TAIL_TRAILER_N = 12 written in place and TT_SHCELLS unfolded -- the same rows up to
   delta, nothing evaluated or narrowed -- in a Theorem Labs lane's S2 text (at 729b9b9d254,
   lib/AU/P_LLVMFuzzerTestOneInput_S2.v:232-235).  The statement file is not Required here. *)
Hypothesis HB_Z_TT : in_zs B (0x20e20 - 0x20) (0x20 + (12 - 12 mod 8)).
Hypothesis HB_C_TT : forall ly, Forall (fun c => In c (as_const B ly))
  (z1 (ANum (shadow_addr (0x20e20 + 8))) (12 mod 8)
   :: map (fun k => z1 (ANum (shadow_addr (0x20e20 + 8) + 1 + Z.of_nat k)) 0xf9) (seq 0 2)).
(* = entry statement Section h, lib/AU/P_LLVMFuzzerTestOneInput.v:212-213 at 327f73c7513 (announced 04:57Z) *)
Hypothesis HRO_TT : forall i, 0 <= i < 12 ->
  ~ Exists (in_zr (0x20e20 + i)) (as_owned_static B) /\ ~ (as_errno B <= 0x20e20 + i < as_errno B + 4).
Context {RO : ro_below_ofl (SK := scene_sink_head) SEGS RLO RHI}.
(* The two budget hypotheses of the entry statement (lib/AU/P_LLVMFuzzerTestOneInput.v HSTK / HSTK_CS) at this
   record's window.  240 is that file's LLVMF_SPDROP: 224 of frame (`addi sp,sp,-0xe0` 0x828a8) and at most 16 of
   realignment (`andi sp,sp,-0x20` 0x828e4), the bound `sc_base`'s own c_sp1 equation gives back. *)
Hypothesis HSTK : 240 + ASTACK <= sw_stk WK.
Hypothesis HSTK_CS : 240 + TCHECK_STEP_STK <= sw_stk WK.

(* -- framework laws and the glue's instances, as the entry statement takes them.  AR_laws is not a hypothesis:
   it is AR_laws_ok (Reusable/YG0q.v:803). -- *)
Hypothesis TL : PALib (L := scene_listing) (PI := PI_scene) B.
Hypothesis TLF : PALibF (L := scene_listing) (PI := PI_scene) B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP SEGS B.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
(* -- the runtime intrinsic the turn calls (a Theorem Labs lane) -- *)
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA SS___asan_memcpy).
(* -- the two program callees of the turn.  Gate 6h: both take scene's own sink head by name; left implicit,
   build_scene_step's Section variable would be resolved by instance search.  No other sink_head instance is
   in scope in this tree (a re-check by a Theorem Labs lane, 2026-10-29), but passing it by name keeps that so. -- *)
Hypothesis BSS : treac_ctrl_build_scene_step_spec (SK := scene_sink_head) (PI := PI_scene) B.
Hypothesis TCHECKX : tcheck_step_specX scene_sink_head B.

(* The two heap blocks of the turn lie in the application range: every `sc_blk_ok` block does. *)
Lemma s3_blk_range : forall (cx : rtcx SEGS) (b n : Z),
sc_blk_ok SEGS B WK cx b n -> 0 < n -> 4096 <= b /\ b + n <= alloc_ceiling /\ 0 <= b < 2 ^ 47.
Proof.
intros cx b n H Hn. destruct H as (Hlo & _ & Hhi & _).
unfold req_size in Hhi. rewrite (proj2 (Z.eqb_neq n 0)) in Hhi by lia.
pose proof YM05.alloc_ceiling_lt as Hlt.
split; [exact Hlo|]. split; [exact Hhi | lia].
Qed.

(* got = scT_off k is in [0, 8904] at every turn index the loop head takes, 343 included. *)
Lemma s3_off_range : forall k, 0 <= k <= 343 -> 0 <= scT_off k <= 8904.
Proof.
intros k Hk. unfold scT_off, scene_off.
destruct (Z.eqb_spec k 343) as [->|H3]; [lia|].
destruct (Z.eqb_spec k 0) as [->|H0]; [lia|].
destruct (Z.eqb_spec k 342) as [->|H2]; lia.
Qed.

(* The entry's fake frame is 32-aligned and lies in the application range at every state the walk's journal
   reaches.  This is what refutes the UBSan pointer-overflow edge 0x82eec, through s3_guard_blki. *)
Lemma s3_frame_range : forall (cx : rtcx SEGS) ly3 S3 (W3 : world SEGS) mem3 md3 ev,
ajournal (SK := scene_sink_head) SEGS B (sw_stk WK) (spZ (c_regs cx)) []
(c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(8, c_fpos cx)] ly3 S3 W3 mem3 md3 ev ->
frames S3 = [(8, c_fpos cx)] ->
frame_addr ly3 8 (c_fpos cx) mod 32 = 0 /\
4096 <= frame_addr ly3 8 (c_fpos cx) /\
frame_addr ly3 8 (c_fpos cx) + fs_frame_bytes 8 < 2 ^ 47.
Proof.
intros cx ly3 S3 W3 mem3 md3 ev HJ Hfr.
pose proof (proj1 HJ) as HAR.
assert (Hin : In (8, c_fpos cx) (frames S3)) by (rewrite Hfr; left; reflexivity).
destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md3 8 (c_fpos cx) HAR Hin) as (Hal & Happ & _ & _).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
pose proof YM05.alloc_ceiling_lt as Hlt.
split; [exact Hal | lia].
Qed.

(* ---- The two UBSan trap edges of the turn, decided from the cut alone (a Theorem Labs lane's TWINMAP.md:152-153, rows 76-77
   of a Theorem Labs lane's SCENE-U.md).  Neither is reachable, so the turn never leaves through 0x83234. ---- *)

(* 0x82f28 `bltu a0,s6`, with a0 = [s1+0x50] = 2^64 - 1 - again (hoisted at 0x82e90-0x82e98) and s6 = got:
   the memcpy destination again + got would have to wrap. *)
Lemma s3_cut_guard_again : forall (cx : rtcx SEGS) ly3 S3 (W3 : world SEGS) regs3 mem3 md3 bs body again b k,
cut_T (SK := scene_sink_head) SEGS B ameter_triv WK scene_geom_asan_ubsan cx
ly3 S3 W3 regs3 mem3 md3 bs body again b k ->
~ (2 ^ 64 - 1 - again < scT_off k).
Proof.
intros cx ly3 S3 W3 regs3 mem3 md3 bs body again b k
(Hk & _ & _ & _ & _ & _ & Hoka & _).
cbn [sg_nturns sg_scene_n scene_geom_asan_ubsan] in Hk, Hoka.
destruct (s3_blk_range cx again 8904 Hoka ltac:(lia)) as (Hlo & Hhi & _).
exact (s3_guard_again again (scT_off k) ltac:(lia) Hhi (s3_off_range k ltac:(lia))).
Qed.

(* 0x82eec `bltu a1,s9`, on the k = 0 arm only, with a1 = 2^64 - 9 and s9 = blk.i = F + 32: the read of blk.i[8]
   would have to wrap.  F is the entry's fake frame, inside the application range. *)
Lemma s3_cut_guard_blki : forall (cx : rtcx SEGS) ly3 S3 (W3 : world SEGS) regs3 mem3 md3 bs body again b k,
cut_T (SK := scene_sink_head) SEGS B ameter_triv WK scene_geom_asan_ubsan cx
ly3 S3 W3 regs3 mem3 md3 bs body again b k ->
~ (2 ^ 64 - 9 < frame_addr ly3 8 (c_fpos cx) + 32).
Proof.
intros cx ly3 S3 W3 regs3 mem3 md3 bs body again b k (_ & _ & Hj & _).
destruct Hj as (HJ & Hfr & _).
cbn [sg_cid scene_geom_asan_ubsan] in HJ, Hfr.
destruct (s3_frame_range cx ly3 S3 W3 mem3 md3 2 HJ Hfr) as (_ & Hlo & Hhi).
assert (Hfb : fs_frame_bytes 8 = 16384) by (vm_compute; reflexivity).
apply s3_guard_blki. lia.
Qed.

(* The frame's address does not move along the walk: `al_layout` (YG0d.v:481) from the entry's AR and the
   journal's own layout_le.  The cut names the frame by the ENTRY layout (`sc_F` = rt_F 8 cx), the AR laws speak
   about the layout at the cut, and this is what identifies the two. *)
Lemma s3_layout_eq : forall (cx : rtcx SEGS) ly3 S3 (W3 : world SEGS) mem3 md3 ev,
(* sc_base takes no SK: it does not mention the sink head (gate 6h: checked on the term, not assumed). *)
sc_base SEGS B ameter_triv WK cx ->
ajournal (SK := scene_sink_head) SEGS B (sw_stk WK) (spZ (c_regs cx)) []
(c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(8, c_fpos cx)] ly3 S3 W3 mem3 md3 ev ->
forall cid pos, frame_addr ly3 cid pos = frame_addr (c_ly cx) cid pos.
Proof.
intros cx ly3 S3 W3 mem3 md3 ev HB HJ cid pos.
destruct HB as ((HPRE & _) & _). destruct HPRE as (HAR & _).
destruct HJ as (_ & HLE & _).
destruct (al_layout _ _ LAWS (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) ly3 HAR HLE) as (_ & HF & _).
apply HF.
Qed.

(* The cut's own frame address, the one the registers hold: 32-aligned, in the application range. *)
Lemma s3_cut_F : forall (cx : rtcx SEGS) ly3 S3 (W3 : world SEGS) regs3 mem3 md3 bs body again b k,
sc_base SEGS B ameter_triv WK cx ->
cut_T (SK := scene_sink_head) SEGS B ameter_triv WK scene_geom_asan_ubsan cx
ly3 S3 W3 regs3 mem3 md3 bs body again b k ->
sc_F SEGS scene_geom_asan_ubsan cx mod 32 = 0 /\
4096 <= sc_F SEGS scene_geom_asan_ubsan cx /\
sc_F SEGS scene_geom_asan_ubsan cx + fs_frame_bytes 8 < 2 ^ 47.
Proof.
intros cx ly3 S3 W3 regs3 mem3 md3 bs body again b k HB (_ & _ & Hj & _).
destruct Hj as (HJ & Hfr & _).
cbn [sg_cid scene_geom_asan_ubsan] in HJ, Hfr.
destruct (s3_frame_range cx ly3 S3 W3 mem3 md3 2 HJ Hfr) as (Hal & Hlo & Hhi).
rewrite (s3_layout_eq cx ly3 S3 W3 mem3 md3 2 HB HJ 8 (c_fpos cx)) in Hal, Hlo, Hhi.
unfold sc_F, rt_F. cbn [sg_cid scene_geom_asan_ubsan].
split; [exact Hal | split; [exact Hlo | exact Hhi]].
Qed.

(* 0x82eec `bltu a1,s9`, on the k = 0 arm only, with a1 = 2^64 - 9 and s9 = blk.i = F + 32, at the F the
   registers hold. *)
Lemma s3_cut_guard_blki_F : forall (cx : rtcx SEGS) ly3 S3 (W3 : world SEGS) regs3 mem3 md3 bs body again b k,
sc_base SEGS B ameter_triv WK cx ->
cut_T (SK := scene_sink_head) SEGS B ameter_triv WK scene_geom_asan_ubsan cx
ly3 S3 W3 regs3 mem3 md3 bs body again b k ->
~ (2 ^ 64 - 9 < sc_F SEGS scene_geom_asan_ubsan cx + 32).
Proof.
intros cx ly3 S3 W3 regs3 mem3 md3 bs body again b k HB HT.
destruct (s3_cut_F cx ly3 S3 W3 regs3 mem3 md3 bs body again b k HB HT) as (_ & Hlo & Hhi).
assert (Hfb : fs_frame_bytes 8 = 16384) by (vm_compute; reflexivity).
apply s3_guard_blki. lia.
Qed.

(* The cut states a block's contents as `garr8 ... (u8s l)`; reac_ctrl_build_scene_step and check_step both ask
   for them as `aview ... (a + i) = Some (bv_unsigned (nth i l 0))`.  One conversion, used for body at both call
   sites and for blk.i after the build. *)
Lemma s3_bytes_of_garr8 : forall (H : word -> bool) (m : word -> option byte) (a : Z) (l : list byte),
garr8 SEGS (mrestrict H m) a (u8s l) ->
forall i, 0 <= i < Z.of_nat (length l) ->
aview SEGS H m (a + i) = Some (bv_unsigned (nth (Z.to_nat i) l (Z_to_bv 8 0))).
Proof.
intros H m a l Hg i Hi.
assert (Hl : (Z.to_nat i < length (u8s l))%nat) by (unfold u8s; rewrite length_map; lia).
pose proof (garr8_mbyte SEGS (mrestrict H m) a (u8s l) (Z.to_nat i) Hg Hl) as Hm.
rewrite Z2Nat.id in Hm by lia.
assert (Hn : nth (Z.to_nat i) (u8s l) 0 = bv_unsigned (nth (Z.to_nat i) l (Z_to_bv 8 0)))
by (unfold u8s; exact (map_nth bv_unsigned l (Z_to_bv 8 0) (Z.to_nat i))).
unfold aview. rewrite Hm. cbn [option_map]. rewrite Hn.
pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) l (Z_to_bv 8 0))) as Hr.
change (bv_modulus 8) with 256 in Hr.
rewrite s3_u8 by lia. reflexivity.
Qed.

(* ---- The blk.i side of reac_ctrl_build_scene_step's precondition (lib/AU/P_reac_ctrl_build_scene_step.v:367-372),
   at the state the five unpoison stores leave: the frame object, the 34 bytes' presence, their
   range_addressable and their shadow hull.  check_step's `afobj` (lib/AU/Prog/SceneBase.v:52) is the same three
   facts. ---- *)
Lemma s3_bss_blki_pre : forall (cx : rtcx SEGS) ly3 S3 (W3 : world SEGS) regs3 mem3 md3 bs body again b k
(mem' : word -> option byte),
sc_base SEGS B ameter_triv WK cx ->
cut_T (SK := scene_sink_head) SEGS B ameter_triv WK scene_geom_asan_ubsan cx
ly3 S3 W3 regs3 mem3 md3 bs body again b k ->
AR SEGS B ly3 S3 W3 mem' md3 ->
(forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) mem' a) ->
(forall o, 4 <= o < 8 ->
aview SEGS (w_H W3) mem' (shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) + o) = Some 0) ->
aview SEGS (w_H W3) mem' (shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) + 8) = Some 2 ->
(exists cid pos, In (cid, pos) [(8, c_fpos cx)] /\ 0 <= cid /\
frame_addr ly3 cid pos <= sc_F SEGS scene_geom_asan_ubsan cx + 32 /\
sc_F SEGS scene_geom_asan_ubsan cx + 32 + 34 <= frame_addr ly3 cid pos + fs_frame_bytes cid) /\
(forall a, sc_F SEGS scene_geom_asan_ubsan cx + 32 <= a < sc_F SEGS scene_geom_asan_ubsan cx + 32 + 34 ->
apresent (w_H W3) mem' a) /\
range_addressable (aview SEGS (w_H W3) mem') SHADOW_OFF (sc_F SEGS scene_geom_asan_ubsan cx + 32) 34 /\
shadow_hull_vis (aview SEGS (w_H W3) mem') (sc_F SEGS scene_geom_asan_ubsan cx + 32) 34.
Proof.
intros cx ly3 S3 W3 regs3 mem3 md3 bs body again b k mem' HB HT HAR' Hgrow H0 H2.
pose proof HT as HT'.
destruct HT' as (_ & _ & Hj & _ & _ & _ & _ & _ & _ & _ & _ & Hfrm & _).
destruct Hj as (HJ & Hfrs & _).
cbn [sg_cid scene_geom_asan_ubsan] in HJ, Hfrs.
assert (HFE : frame_addr ly3 8 (c_fpos cx) = sc_F SEGS scene_geom_asan_ubsan cx).
{ unfold sc_F, rt_F. cbn [sg_cid scene_geom_asan_ubsan].
exact (s3_layout_eq cx ly3 S3 W3 mem3 md3 2 HB HJ 8 (c_fpos cx)). }
destruct (s3_cut_F cx ly3 S3 W3 regs3 mem3 md3 bs body again b k HB HT) as (Hal & Hlo & Hhi).
assert (Hfb : fs_frame_bytes 8 = 16384) by (vm_compute; reflexivity).
assert (H8 : sc_F SEGS scene_geom_asan_ubsan cx mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal; [|lia]. destruct Hal as [q Hq]. exists (4 * q). lia. }
assert (Hin : In (8, c_fpos cx) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct Hfrm as (_ & Hpres & _).
cbn [sg_cid scene_geom_asan_ubsan] in Hpres.
split; [exists 8, (c_fpos cx); split; [left; reflexivity|]; split; [lia|]; rewrite HFE; lia|].
split.
{ intros a Ha. apply Hgrow. apply Hpres. unfold sc_F, rt_F in Ha. cbn [sg_cid scene_geom_asan_ubsan] in Ha.
unfold sc_F, rt_F. cbn [sg_cid scene_geom_asan_ubsan]. lia. }
split.
{ exact (s3_ra_blki (aview SEGS (w_H W3) mem') (sc_F SEGS scene_geom_asan_ubsan cx) H8 H0 H2). }
rewrite <- HFE.
exact (shadow_hull_vis_of_frame _ _ LAWS ly3 S3 W3 mem' md3 8 (c_fpos cx)
(frame_addr ly3 8 (c_fpos cx) + 32) 34 HAR' Hin ltac:(lia) ltac:(rewrite Hfb; lia) ltac:(lia)).
Qed.

(* check_step's own frame-object premise (`afobj`, lib/AU/Prog/SceneBase.v:52) is the same three facts. *)
Lemma s3_afobj_blki : forall (cx : rtcx SEGS) ly3 S3 (W3 : world SEGS) regs3 mem3 md3 bs body again b k
(mem' : word -> option byte),
sc_base SEGS B ameter_triv WK cx ->
cut_T (SK := scene_sink_head) SEGS B ameter_triv WK scene_geom_asan_ubsan cx
ly3 S3 W3 regs3 mem3 md3 bs body again b k ->
AR SEGS B ly3 S3 W3 mem' md3 ->
(forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) mem' a) ->
(forall o, 4 <= o < 8 ->
aview SEGS (w_H W3) mem' (shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) + o) = Some 0) ->
aview SEGS (w_H W3) mem' (shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) + 8) = Some 2 ->
afobj SEGS B ly3 S3 W3 mem' (sc_F SEGS scene_geom_asan_ubsan cx + 32) 34.
Proof.
intros cx ly3 S3 W3 regs3 mem3 md3 bs body again b k mem' HB HT HAR' Hgrow H0 H2.
destruct (s3_bss_blki_pre cx ly3 S3 W3 regs3 mem3 md3 bs body again b k mem' HB HT HAR' Hgrow H0 H2)
as (Hobj & _ & Hra & _).
destruct (s3_cut_F cx ly3 S3 W3 regs3 mem3 md3 bs body again b k HB HT) as (Hal & _ & _).
pose proof HT as HT'.
destruct HT' as (_ & _ & Hj & _). destruct Hj as (HJ & Hfrs & _).
cbn [sg_cid scene_geom_asan_ubsan] in HJ, Hfrs.
assert (H8 : sc_F SEGS scene_geom_asan_ubsan cx mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal; [|lia]. destruct Hal as [q Hq]. exists (4 * q). lia. }
destruct Hobj as (cid & pos & Hinl & Hcid & Hlo & Hhi).
cbn [In] in Hinl. destruct Hinl as [Heq | []]. injection Heq as <- <-.
split; [|split].
- exists 8, (c_fpos cx). split; [rewrite Hfrs; left; reflexivity|]. split; [lia|].
  split; [|split; [exact Hlo | exact Hhi]].
  apply Z.mod_divide; [lia|]. apply Z.mod_divide in H8; [|lia].
  destruct H8 as (q & Hq).
  assert (HFE : frame_addr ly3 8 (c_fpos cx) = sc_F SEGS scene_geom_asan_ubsan cx).
  { unfold sc_F, rt_F. cbn [sg_cid scene_geom_asan_ubsan].
    exact (s3_layout_eq cx ly3 S3 W3 mem3 md3 2 HB HJ 8 (c_fpos cx)). }
  rewrite HFE. exists q. exact Hq.
- rewrite Z.add_mod by lia. rewrite H8. reflexivity.
- exact Hra.
Qed.


(* ================================================================================================================
   The memory-transport lemmas of the turn, proved by a Theorem Labs lane's helper and pasted here
   verbatim (its scratch file S3Keep_scratch.v (sha256 d4e067461992; internal record)
   lines 62-340).
   ================================================================================================================ *)
(* =================================================================================================================
   MEMORY TRANSPORT OF THE CUT'S MEMORY FACTS ACROSS THE TURN'S THREE CALLS.
   Each cut predicate reads memory only through `aview` (and, for sc_frame, `apresent`), so it moves from (W, mem) to
   (W', mem') as soon as aview agrees on the bytes it reads.  The `_pt` lemmas state exactly that, over the smallest
   address range each predicate reads; the others turn the callees' own write-set posts into it:
   - s3_keep_* : one excluded window [lo, hi), the world kept, presence grows (the shape of the lane's request);
   - s3_keep_*_w2 : the window [lo, hi) and one more condition Q a, the world kept, presence grows: both
     __asan_memcpy's post (aj_intrin_at / aj_intrin_atS: Q a := ~ (sp - ESTACK <= a < sp)) and
     build_scene_step's post (treac_ctrl_build_scene_step_post: [lo, hi) = its stack window, Q a := (ok = true ->
     ~ (blk <= a < blk + BLK_LEN))) are of this shape;
   - s3_keep_*_j : check_step's post, an ajournal with FP = [] from the call site (apost_base); the world may grow,
     and the frame's presence comes back from AR at the return state.
   sc_frame needs only its FLAG WORD [F + fs - 8, F + fs) outside the write set: its other two clauses are
   presence, which every post keeps.  This matters for build_scene_step, whose write set blk.i = F + 32 lies INSIDE
   the frame window.
   ================================================================================================================= *)

(* The frame of the cut, at the cut's own layout: the journal from the entry keeps ly_F (layout_le). *)
Lemma s3_keep_F : forall MT (cx : rtcx SEGS) ly3 S3 (W3 : world SEGS) regs3 mem3 md3 bs body again b k,
cut_T (SK := scene_sink_head) SEGS B MT WK scene_geom_asan_ubsan cx ly3 S3 W3 regs3 mem3 md3 bs body again b k ->
frame_addr ly3 (sg_cid scene_geom_asan_ubsan) (c_fpos cx) = sc_F SEGS scene_geom_asan_ubsan cx /\
In (sg_cid scene_geom_asan_ubsan, c_fpos cx) (frames S3).
Proof.
intros MT cx ly3 S3 W3 regs3 mem3 md3 bs body again b k (_ & _ & (HJ & Hfr & _) & _).
pose proof HJ as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & HF & _).
split.
- unfold sc_F, rt_F, frame_addr. rewrite HF. reflexivity.
- rewrite Hfr. left. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   1. sc_frame
   --------------------------------------------------------------------------------------------------------------- *)
Lemma s3_keep_frame_pt : forall (cx : rtcx SEGS) (W W' : world SEGS) (mem mem' : word -> option byte),
sc_frame SEGS scene_geom_asan_ubsan cx W mem ->
(forall a, sc_F SEGS scene_geom_asan_ubsan cx + fs_frame_bytes (sg_cid scene_geom_asan_ubsan) - 8 <= a <
sc_F SEGS scene_geom_asan_ubsan cx + fs_frame_bytes (sg_cid scene_geom_asan_ubsan) ->
aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
(forall a,
(sc_F SEGS scene_geom_asan_ubsan cx <= a <
sc_F SEGS scene_geom_asan_ubsan cx + fs_frame_bytes (sg_cid scene_geom_asan_ubsan) \/
shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) <= a <
shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) + fs_frame_bytes (sg_cid scene_geom_asan_ubsan) / 8) ->
apresent (w_H W) mem a -> apresent (w_H W') mem' a) ->
sc_frame SEGS scene_geom_asan_ubsan cx W' mem'.
Proof.
intros cx W W' mem mem' HF HK HP. unfold sc_frame in *. destruct HF as (HR & HP1 & HP2).
split; [|split].
- rewrite (rdword_ext (aview SEGS (w_H W) mem)); [exact HR|]. intros i Hi. apply HK. lia.
- intros a Ha. apply HP; [left; exact Ha | exact (HP1 a Ha)].
- intros a Ha. apply HP; [right; exact Ha | exact (HP2 a Ha)].
Qed.

Lemma s3_keep_frame : forall (cx : rtcx SEGS) (W3 : world SEGS) (mem3 mem' : word -> option byte) (lo hi : Z),
sc_frame SEGS scene_geom_asan_ubsan cx W3 mem3 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W3) mem' a = aview SEGS (w_H W3) mem3 a) ->
(forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) mem' a) ->
(forall a, sc_F SEGS scene_geom_asan_ubsan cx + fs_frame_bytes (sg_cid scene_geom_asan_ubsan) - 8 <= a <
sc_F SEGS scene_geom_asan_ubsan cx + fs_frame_bytes (sg_cid scene_geom_asan_ubsan) ->
0 <= a < 2 ^ 64 /\ ~ (lo <= a < hi)) ->
sc_frame SEGS scene_geom_asan_ubsan cx W3 mem'.
Proof.
intros cx W3 mem3 mem' lo hi HF HK HP HD.
apply (s3_keep_frame_pt cx W3 W3 mem3 mem' HF).
- intros a Ha. destruct (HD a Ha) as [H0 H1]. exact (HK a H0 H1).
- intros a _ Hp. exact (HP a Hp).
Qed.

Lemma s3_keep_frame_w2 : forall (cx : rtcx SEGS) (W3 : world SEGS) (mem3 mem' : word -> option byte) (lo hi : Z)
(Q : Z -> Prop),
sc_frame SEGS scene_geom_asan_ubsan cx W3 mem3 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> Q a -> aview SEGS (w_H W3) mem' a = aview SEGS (w_H W3) mem3 a) ->
(forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) mem' a) ->
(forall a, sc_F SEGS scene_geom_asan_ubsan cx + fs_frame_bytes (sg_cid scene_geom_asan_ubsan) - 8 <= a <
sc_F SEGS scene_geom_asan_ubsan cx + fs_frame_bytes (sg_cid scene_geom_asan_ubsan) ->
0 <= a < 2 ^ 64 /\ ~ (lo <= a < hi) /\ Q a) ->
sc_frame SEGS scene_geom_asan_ubsan cx W3 mem'.
Proof.
intros cx W3 mem3 mem' lo hi Q HF HK HP HD.
apply (s3_keep_frame_pt cx W3 W3 mem3 mem' HF).
- intros a Ha. destruct (HD a Ha) as (H0 & H1 & H2). exact (HK a H0 H1 H2).
- intros a _ Hp. exact (HP a Hp).
Qed.

Lemma s3_keep_frame_j : forall (cx : rtcx SEGS) STK sp0 ly S (W : world SEGS) mem md own ly' S' (W' : world SEGS)
mem' md' k,
ajournal (SK := scene_sink_head) SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
In (sg_cid scene_geom_asan_ubsan, c_fpos cx) (frames S) ->
frame_addr ly (sg_cid scene_geom_asan_ubsan) (c_fpos cx) = sc_F SEGS scene_geom_asan_ubsan cx ->
sc_frame SEGS scene_geom_asan_ubsan cx W mem -> sc_frame SEGS scene_geom_asan_ubsan cx W' mem'.
Proof.
intros cx STK sp0 ly S W mem md own ly' S' W' mem' md' k HJ Hin HFa HF.
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & Hfr & _).
assert (Hfs : fs_frame_bytes (sg_cid scene_geom_asan_ubsan) = 16384) by reflexivity.
assert (HFa' : frame_addr ly' (sg_cid scene_geom_asan_ubsan) (c_fpos cx) = sc_F SEGS scene_geom_asan_ubsan cx).
{ rewrite <- HFa. destruct Hly as (_ & _ & _ & _ & _ & E & _). unfold frame_addr. rewrite E. reflexivity. }
assert (Hin' : In (sg_cid scene_geom_asan_ubsan, c_fpos cx) (frames S')).
{ rewrite Hfrs. apply in_or_app. right. exact Hin. }
destruct (al_frames _ _ LAWS ly' S' W' mem' md' _ _ HAR Hin') as (_ & _ & Hb & Hsh).
rewrite HFa' in Hb, Hsh.
apply (s3_keep_frame_pt cx W W' mem mem' HF).
- intros a Ha. apply (Hfr _ _ a Hin); [|apply inFP_nil].
left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite HFa. lia.
- intros a [Ha | Ha] _; [exact (proj1 (Hb a Ha))|].
revert Hsh Ha. generalize (fs_frame_bytes (sg_cid scene_geom_asan_ubsan) / 8) as q.
generalize (shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx)) as s. intros s q Hsh Ha.
specialize (Hsh (a - s) ltac:(lia)). replace (s + (a - s)) with a in Hsh by lia. exact (proj1 Hsh).
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   2. sc_shr
   --------------------------------------------------------------------------------------------------------------- *)
Lemma s3_keep_shr_pt : forall (cx : rtcx SEGS) (W W' : world SEGS) (mem mem' : word -> option byte) (l h v : Z),
sc_shr SEGS scene_geom_asan_ubsan cx W mem l h v ->
(forall a, shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) + l <= a <
shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) + h ->
aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
sc_shr SEGS scene_geom_asan_ubsan cx W' mem' l h v.
Proof.
intros cx W W' mem mem' l h v HS HK o Ho. rewrite HK by lia. exact (HS o Ho).
Qed.

Lemma s3_keep_shr : forall (cx : rtcx SEGS) (W3 : world SEGS) (mem3 mem' : word -> option byte) (lo hi l h v : Z),
sc_shr SEGS scene_geom_asan_ubsan cx W3 mem3 l h v ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W3) mem' a = aview SEGS (w_H W3) mem3 a) ->
(forall a, shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) + l <= a <
shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) + h ->
0 <= a < 2 ^ 64 /\ ~ (lo <= a < hi)) ->
sc_shr SEGS scene_geom_asan_ubsan cx W3 mem' l h v.
Proof.
intros cx W3 mem3 mem' lo hi l h v HS HK HD.
apply (s3_keep_shr_pt cx W3 W3 mem3 mem' l h v HS).
intros a Ha. destruct (HD a Ha) as [H0 H1]. exact (HK a H0 H1).
Qed.

Lemma s3_keep_shr_w2 : forall (cx : rtcx SEGS) (W3 : world SEGS) (mem3 mem' : word -> option byte) (lo hi : Z)
(Q : Z -> Prop) (l h v : Z),
sc_shr SEGS scene_geom_asan_ubsan cx W3 mem3 l h v ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> Q a -> aview SEGS (w_H W3) mem' a = aview SEGS (w_H W3) mem3 a) ->
(forall a, shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) + l <= a <
shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) + h ->
0 <= a < 2 ^ 64 /\ ~ (lo <= a < hi) /\ Q a) ->
sc_shr SEGS scene_geom_asan_ubsan cx W3 mem' l h v.
Proof.
intros cx W3 mem3 mem' lo hi Q l h v HS HK HD.
apply (s3_keep_shr_pt cx W3 W3 mem3 mem' l h v HS).
intros a Ha. destruct (HD a Ha) as (H0 & H1 & H2). exact (HK a H0 H1 H2).
Qed.

Lemma s3_keep_shr_j : forall (cx : rtcx SEGS) STK sp0 ly S (W : world SEGS) mem md own ly' S' (W' : world SEGS)
mem' md' k (l h v : Z),
ajournal (SK := scene_sink_head) SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
In (sg_cid scene_geom_asan_ubsan, c_fpos cx) (frames S) ->
frame_addr ly (sg_cid scene_geom_asan_ubsan) (c_fpos cx) = sc_F SEGS scene_geom_asan_ubsan cx ->
0 <= l -> h <= fs_frame_bytes (sg_cid scene_geom_asan_ubsan) / 8 ->
sc_shr SEGS scene_geom_asan_ubsan cx W mem l h v -> sc_shr SEGS scene_geom_asan_ubsan cx W' mem' l h v.
Proof.
intros cx STK sp0 ly S W mem md own ly' S' W' mem' md' k l h v HJ Hin HFa Hl Hh HS.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfr & _).
apply (s3_keep_shr_pt cx W W' mem mem' l h v HS).
intros a Ha. apply (Hfr _ _ a Hin); [|apply inFP_nil].
right. unfold in_zr. cbn [fst snd]. rewrite HFa.
revert Hh. generalize (fs_frame_bytes (sg_cid scene_geom_asan_ubsan) / 8) as q. intros q Hh. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   3. garr8
   --------------------------------------------------------------------------------------------------------------- *)
Lemma s3_keep_garr8_pt : forall (W W' : world SEGS) (mem mem' : word -> option byte) (a0 : Z) (l : list Z),
garr8 SEGS (mrestrict (w_H W) mem) a0 l ->
(forall a, a0 <= a < a0 + Z.of_nat (length l) -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
garr8 SEGS (mrestrict (w_H W') mem') a0 l.
Proof.
intros W W' mem mem' a0 l HG HK. apply (garr8_frame SEGS _ _ a0 l HG).
intros a Ha. apply (mbyte_of_aview SEGS). exact (HK a Ha).
Qed.

Lemma s3_keep_garr8 : forall (W3 : world SEGS) (mem3 mem' : word -> option byte) (lo hi a0 : Z) (l : list Z),
garr8 SEGS (mrestrict (w_H W3) mem3) a0 l ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W3) mem' a = aview SEGS (w_H W3) mem3 a) ->
(forall a, a0 <= a < a0 + Z.of_nat (length l) -> 0 <= a < 2 ^ 64 /\ ~ (lo <= a < hi)) ->
garr8 SEGS (mrestrict (w_H W3) mem') a0 l.
Proof.
intros W3 mem3 mem' lo hi a0 l HG HK HD.
apply (s3_keep_garr8_pt W3 W3 mem3 mem' a0 l HG).
intros a Ha. destruct (HD a Ha) as [H0 H1]. exact (HK a H0 H1).
Qed.

Lemma s3_keep_garr8_w2 : forall (W3 : world SEGS) (mem3 mem' : word -> option byte) (lo hi : Z) (Q : Z -> Prop)
(a0 : Z) (l : list Z),
garr8 SEGS (mrestrict (w_H W3) mem3) a0 l ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> Q a -> aview SEGS (w_H W3) mem' a = aview SEGS (w_H W3) mem3 a) ->
(forall a, a0 <= a < a0 + Z.of_nat (length l) -> 0 <= a < 2 ^ 64 /\ ~ (lo <= a < hi) /\ Q a) ->
garr8 SEGS (mrestrict (w_H W3) mem') a0 l.
Proof.
intros W3 mem3 mem' lo hi Q a0 l HG HK HD.
apply (s3_keep_garr8_pt W3 W3 mem3 mem' a0 l HG).
intros a Ha. destruct (HD a Ha) as (H0 & H1 & H2). exact (HK a H0 H1 H2).
Qed.

(* check_step, a heap block of the call site that the return state still holds (body, again). *)
Lemma s3_keep_garr8_jb : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' (W' : world SEGS) mem' md' k
(p n a0 : Z) (l : list Z),
ajournal (SK := scene_sink_head) SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') ->
p <= a0 -> a0 + Z.of_nat (length l) <= p + req_size n ->
garr8 SEGS (mrestrict (w_H W) mem) a0 l -> garr8 SEGS (mrestrict (w_H W') mem') a0 l.
Proof.
intros STK sp0 ly S W mem md own ly' S' W' mem' md' k p n a0 l HJ Hin Hin' Hlo Hhi HG.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk & _).
apply (s3_keep_garr8_pt W W' mem mem' a0 l HG).
intros a Ha. replace a with (p + (a - p)) by lia.
apply (Hblk p n (a - p) Hin Hin'); [lia | apply inFP_nil].
Qed.

(* check_step, an object of the cut's frame (mac). *)
Lemma s3_keep_garr8_jf : forall (cx : rtcx SEGS) STK sp0 ly S (W : world SEGS) mem md own ly' S' (W' : world SEGS)
mem' md' k (a0 : Z) (l : list Z),
ajournal (SK := scene_sink_head) SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
In (sg_cid scene_geom_asan_ubsan, c_fpos cx) (frames S) ->
frame_addr ly (sg_cid scene_geom_asan_ubsan) (c_fpos cx) = sc_F SEGS scene_geom_asan_ubsan cx ->
sc_F SEGS scene_geom_asan_ubsan cx <= a0 ->
a0 + Z.of_nat (length l) <= sc_F SEGS scene_geom_asan_ubsan cx + fs_frame_bytes (sg_cid scene_geom_asan_ubsan) ->
garr8 SEGS (mrestrict (w_H W) mem) a0 l -> garr8 SEGS (mrestrict (w_H W') mem') a0 l.
Proof.
intros cx STK sp0 ly S W mem md own ly' S' W' mem' md' k a0 l HJ Hin HFa Hlo Hhi HG.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfr & _).
apply (s3_keep_garr8_pt W W' mem mem' a0 l HG).
intros a Ha. apply (Hfr _ _ a Hin); [|apply inFP_nil].
left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite HFa. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   4. sc_saves
   --------------------------------------------------------------------------------------------------------------- *)
Lemma s3_keep_saves_pt : forall (cx : rtcx SEGS) (W W' : world SEGS) (mem mem' : word -> option byte),
sc_saves SEGS cx W mem ->
(forall a, spZ (c_regs cx) - 104 <= a < spZ (c_regs cx) -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
sc_saves SEGS cx W' mem'.
Proof.
intros cx W W' mem mem' HS HK j Hj.
rewrite (rdword_ext (aview SEGS (w_H W) mem)); [exact (HS j Hj)|]. intros i Hi. apply HK. lia.
Qed.

Lemma s3_keep_saves : forall (cx : rtcx SEGS) (W3 : world SEGS) (mem3 mem' : word -> option byte) (lo hi : Z),
sc_saves SEGS cx W3 mem3 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W3) mem' a = aview SEGS (w_H W3) mem3 a) ->
(forall a, spZ (c_regs cx) - 104 <= a < spZ (c_regs cx) -> 0 <= a < 2 ^ 64 /\ ~ (lo <= a < hi)) ->
sc_saves SEGS cx W3 mem'.
Proof.
intros cx W3 mem3 mem' lo hi HS HK HD.
apply (s3_keep_saves_pt cx W3 W3 mem3 mem' HS).
intros a Ha. destruct (HD a Ha) as [H0 H1]. exact (HK a H0 H1).
Qed.

Lemma s3_keep_saves_w2 : forall (cx : rtcx SEGS) (W3 : world SEGS) (mem3 mem' : word -> option byte) (lo hi : Z)
(Q : Z -> Prop),
sc_saves SEGS cx W3 mem3 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> Q a -> aview SEGS (w_H W3) mem' a = aview SEGS (w_H W3) mem3 a) ->
(forall a, spZ (c_regs cx) - 104 <= a < spZ (c_regs cx) -> 0 <= a < 2 ^ 64 /\ ~ (lo <= a < hi) /\ Q a) ->
sc_saves SEGS cx W3 mem'.
Proof.
intros cx W3 mem3 mem' lo hi Q HS HK HD.
apply (s3_keep_saves_pt cx W3 W3 mem3 mem' HS).
intros a Ha. destruct (HD a Ha) as (H0 & H1 & H2). exact (HK a H0 H1 H2).
Qed.

(* check_step: the saves lie above the call's sp0 and at or above alloc_ceiling (the stack is above it, astk_ok). *)
Lemma s3_keep_saves_j : forall (cx : rtcx SEGS) STK sp0 ly S (W : world SEGS) mem md own ly' S' (W' : world SEGS)
mem' md' k,
ajournal (SK := scene_sink_head) SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
(forall a, spZ (c_regs cx) - 104 <= a < spZ (c_regs cx) -> alloc_ceiling <= a < 2 ^ 64 /\ ~ (sp0 - STK <= a < sp0)) ->
sc_saves SEGS cx W mem -> sc_saves SEGS cx W' mem'.
Proof.
intros cx STK sp0 ly S W mem md own ly' S' W' mem' md' k HJ HD HS.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & Hhigh & _).
apply (s3_keep_saves_pt cx W W' mem mem' HS).
intros a Ha. destruct (HD a Ha) as [H0 H1]. exact (Hhigh a H0 H1).
Qed.

(* ---- The lane's ENTRY BLOCK: the symbolic state the run engine starts the turn from, built from the semantic cut.
   Proved by a helper, pasted verbatim from S3Entry_scratch.v (sha256 a43dfb21185b; internal record) lines 104-225. ---- *)
Definition S3_PC : Z := AF_LLVMFuzzerTestOneInput + SEG_T_off.
Definition s3_spill_region (declared srcA nagain again : Z) : YP09.region :=
YP09.mkRegion (Some 9%nat) 0x40 0x60 0x40 0x48
[YP09.mkChunk 0x40 (CVal 8 (SLit declared)); YP09.mkChunk 0x48 (CVal 8 (SLit srcA));
YP09.mkChunk 0x50 (CVal 8 (SLit nagain)); YP09.mkChunk 0x58 (CVal 8 (SLit again))].
Definition s3_shadow_region : YP09.region :=
YP09.mkRegion (Some 19%nat) 4 9 4 9
(map (fun j => YP09.mkChunk (4 + Z.of_nat j) (CVal 1 (SLit (2 ^ 64 - 8)))) (seq 0 5)).
Definition s3_ss (declared srcA nagain again : Z) : sstate :=
mkSS S3_PC sr_atoms [s3_spill_region declared srcA nagain again; s3_shadow_region] None (mkFacts [] [] []).

Lemma s3_entry_state : forall (cx : rtcx SEGS) ly3 S3 (W3 : world SEGS) regs3 mem3 md3 bs body again b k,
sc_base SEGS B ameter_triv WK cx ->
cut_T (SK := scene_sink_head) SEGS B ameter_triv WK scene_geom_asan_ubsan cx
ly3 S3 W3 regs3 mem3 md3 bs body again b k ->
st_ok_pi SEGS VAL (Eimg (Ereg regs3 []))
(s3_ss (if k =? 0 then 0 else 8904)
(frame_addr (c_ly cx) 8 (c_fpos cx) + 39)
(2 ^ 64 - 1 - again) again)
(restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (sg_pc_t scene_geom_asan_ubsan)) mem3 (seg_rom SEGS))).
Proof.
intros cx ly3 S3 W3 regs3 mem3 md3 bs body again b k HB HT.
destruct HT as (Hk & _ & Hj & _ & _ & _ & Hoka & _ & _ & _ & _ & Hfr & _ & _ & Hshr & _ & _ & _ & _ & _ &
_ & Hsp1 & _ & HshF & _ & HsrcA & _ & _ & _ & _ & Hagain & _ & _ & _ & Hdecl & _ & _ & Hnag & _).
destruct Hj as (HJ & Hfrs & _).
destruct HB as (_ & Hsp1eq).
pose proof (@YM05.alloc_ceiling_value rc) as Hacv.
(* the entry's fake frame, by the name the cut's own clauses use *)
assert (HF : sc_F SEGS scene_geom_asan_ubsan cx = frame_addr (c_ly cx) 8 (c_fpos cx))
by (unfold sc_F, rt_F; cbn [sg_cid scene_geom_asan_ubsan]; reflexivity).
unfold sc_frame in Hfr. unfold sc_shr in Hshr.
rewrite HF in Hfr, Hshr, HshF, HsrcA.
destruct Hfr as (_ & _ & Hshpres).
cbn [sg_cid sg_scene_n sg_off_blki sg_sh_blki_lo sg_sh_blki_hi sgT_sp1 sgT_shF sgT_srcA sgT_again sgT_decl
sgT_nagain scene_geom_asan_ubsan] in HJ, Hfrs, Hoka, Hshpres, Hshr, Hsp1, HshF, HsrcA, Hagain, Hdecl, Hnag.
cbn [vat] in Hsp1, HshF, HsrcA, Hagain, Hdecl, Hnag.
destruct HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstkp & Hstk & _).
(* the layout keeps ly_F, so the journal's frame is the entry's *)
assert (HlyF : frame_addr ly3 8 (c_fpos cx) = frame_addr (c_ly cx) 8 (c_fpos cx)).
{ unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & HFF & _). rewrite HFF. reflexivity. }
assert (Hin : In (8, c_fpos cx) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md3 8 (c_fpos cx) HAR Hin) as (_ & Happ & _ & _).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. rewrite HlyF in Happ.
assert (Hfb : fs_frame_bytes 8 = 16384) by reflexivity.
rewrite Hfb in Happ, Hshpres. change (16384 / 8) with 2048 in Hshpres.
set (F := frame_addr (c_ly cx) 8 (c_fpos cx)) in *.
assert (HFr : 4096 <= F /\ F + 16384 <= 140737479966720) by lia.
assert (HFd : F / 8 <= 17592184993792) by (apply Z.div_le_upper_bound; lia).
assert (HFd0 : 0 <= F / 8) by (apply Z.div_pos; lia).
unfold shadow_addr in Hshpres, Hshr.
(* the stack: sp1 sits 224..255 below sp0 and the whole budget is present *)
destruct Hstk as (_ & HSTKnn & Hceil & Hstklo & Hsphi & Hstkhi & _).
assert (Hsp1b : spZ (c_regs cx) - 255 <= c_sp1 cx <= spZ (c_regs cx) - 224).
{ rewrite Hsp1eq. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 224) 32 ltac:(lia)) as Hm.
  pose proof (Z_div_mod_eq_full (spZ (c_regs cx) - 224) 32) as He. lia. }
unfold ASTACK in HSTK.
(* `again` is one of the walk's heap blocks *)
assert (Hagr : 4096 <= again /\ again + 8904 <= alloc_ceiling).
{ destruct Hoka as (Hlo & _ & Hhi & _). change (req_size 8904) with 8904 in Hhi.
  split; [exact Hlo | exact Hhi]. }
(* the two region bases *)
assert (Hb1 : bv_unsigned (ew (Eimg (Ereg regs3 [])) 9%nat) = c_sp1 cx).
{ rewrite (s3e_ew regs3 RV_s1 9%nat ltac:(lia) ltac:(vm_compute; reflexivity)).
  unfold RV_s1 in *. rewrite Hsp1. apply s3e_unsigned64. lia. }
assert (Hb2 : bv_unsigned (ew (Eimg (Ereg regs3 [])) 19%nat) = SHADOW_OFF + F / 8).
{ rewrite (s3e_ew regs3 RV_s3 19%nat ltac:(lia) ltac:(vm_compute; reflexivity)).
  unfold RV_s3 in *. rewrite HshF. apply s3e_unsigned64. unfold SHADOW_OFF. lia. }
(* the goal's pc is BASE + S3_PC *)
assert (Hpc : sg_pc_t scene_geom_asan_ubsan = BASE + S3_PC)
by (cbn [sg_pc_t scene_geom_asan_ubsan]; unfold S3_PC; lia).
rewrite Hpc, restrict_mkst_fx. unfold s3_ss.
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons.
  { (* the four live spill words *)
    unfold s3_spill_region, YP09.region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
    rewrite Hb1. split; [lia|]. split; [lia|]. split.
    - intros o Ho. apply (apresent_writable SEGS). apply Hstkp. lia.
    - apply Forall_cons.
      { apply (chunk_ok_val SEGS _ _ (c_sp1 cx) 0x40 8 (SLit (if k =? 0 then 0 else 8904))
                 (if k =? 0 then 0 else 8904)).
        - reflexivity.
        - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). destruct (k =? 0); lia.
        - cbn [Z.of_N]. lia.
        - exact (val_mem_of_rdword SEGS (w_H W3) mem3 _ _ Hdecl). }
      apply Forall_cons.
      { apply (chunk_ok_val SEGS _ _ (c_sp1 cx) 0x48 8 (SLit (F + 39)) (F + 39)).
        - reflexivity.
        - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
        - cbn [Z.of_N]. lia.
        - replace (F + 39) with (F + 32 + 7) by lia.
          exact (val_mem_of_rdword SEGS (w_H W3) mem3 _ _ HsrcA). }
      apply Forall_cons.
      { apply (chunk_ok_val SEGS _ _ (c_sp1 cx) 0x50 8 (SLit (2 ^ 64 - 1 - again)) (2 ^ 64 - 1 - again)).
        - reflexivity.
        - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
        - cbn [Z.of_N]. lia.
        - exact (val_mem_of_rdword SEGS (w_H W3) mem3 _ _ Hnag). }
      apply Forall_cons; [| apply Forall_nil].
      { apply (chunk_ok_val SEGS _ _ (c_sp1 cx) 0x58 8 (SLit again) again).
        - reflexivity.
        - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
        - cbn [Z.of_N]. lia.
        - exact (val_mem_of_rdword SEGS (w_H W3) mem3 _ _ Hagain). } }
  apply Forall_cons; [| apply Forall_nil].
  { (* the five poisoned shadow cells of blk.i *)
    unfold s3_shadow_region, YP09.region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
    rewrite Hb2. split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split.
    - intros o Ho. apply (apresent_writable SEGS). apply Hshpres. lia.
    - apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
      apply s3e_chunk_f8. apply s3e_mbyte. apply Hshr. lia. }
- unfold s3_spill_region, s3_shadow_region.
  cbn [YP09.pairwise_disjoint YP09.all_disjoint].
  split; [split; [| exact I] | split; [exact I | exact I]].
  unfold YP09.extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val].
  rewrite Hb1, Hb2. right. unfold SHADOW_OFF. lia.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. tauto.
Qed.

(* ---- The again buffer at the latch.  `cut_T` says again holds `firstn (scT_off k) b ++ ja` for some tail ja of
   the right length; the memcpy at 0x82f44 overwrites the first scene_len k bytes of that tail with
   `firstn (scene_len k) (skipn (scT_src k) (scene_block b k))`, and SceneTM's scT_again_step says that is
   exactly what extends the prefix to scT_off (k + 1).  The tail that is left is `skipn (scene_len k) ja`. ---- *)
Lemma s3_again_step_list : forall (b ja : list byte) (k : Z),
length b = 8904%nat -> 0 <= k <= 342 -> Z.of_nat (length ja) = 8904 - scT_off k ->
firstn (Z.to_nat (scT_off k)) b
++ (firstn (Z.to_nat (scene_len k)) (skipn (Z.to_nat (scT_src k)) (scene_block b k))
++ skipn (Z.to_nat (scene_len k)) ja)
= firstn (Z.to_nat (scT_off (k + 1))) b ++ skipn (Z.to_nat (scene_len k)) ja
/\ Z.of_nat (length (skipn (Z.to_nat (scene_len k)) ja)) = 8904 - scT_off (k + 1).
Proof.
intros b ja k Hb Hk Hja.
pose proof (scT_bnd k Hk) as (Hlo & Hhi & Hlen).
pose proof (scT_off_step k Hk) as Hstep.
split.
- rewrite app_assoc. rewrite (scT_again_step b k Hb Hk). reflexivity.
- rewrite length_skipn. lia.
Qed.

(* At the loop exit (k = 343) the tail is empty and `again` holds b in full: this is the `exists ja` clause of
   cut_T at NTURNS, which cut_TX inherits. *)
Lemma s3_again_all_list : forall (b ja : list byte),
length b = 8904%nat -> Z.of_nat (length ja) = 8904 - scT_off 343 ->
firstn (Z.to_nat (scT_off 343)) b ++ ja = b.
Proof.
intros b ja Hb Hja. rewrite scT_off_343 in Hja |- *.
assert (Hnil : ja = []) by (destruct ja as [|x ja']; [reflexivity|]; cbn [length] in Hja; lia).
rewrite Hnil, app_nil_r. apply firstn_all2. rewrite Hb. change (Z.to_nat 8904) with 8904%nat. lia.
Qed.

(* `declared` is 8904 at every head after the first: the k = 0 store 0x82f00 writes 0x22c8 and the loop never
   writes that slot again. *)
Lemma s3_decl_next : forall k, 0 <= k -> (if k + 1 =? 0 then 0 else 8904) = 8904.
Proof. intros k Hk. destruct (Z.eqb_spec (k + 1) 0) as [He|_]; [lia | reflexivity]. Qed.

(* ---- What the memcpy at 0x82f44 does to `again`'s contents, as a list.  The cut holds `again` as
   `u8s (pre ++ ja)`; the call overwrites the first `length src` bytes of the tail and leaves the rest; the
   result is `u8s (pre ++ src ++ skipn (length src) ja)`.  Decomposed with garr8_app (YI00.v:55), so there is no
   index arithmetic over nth. ---- *)
Lemma s3_garr8_splice : forall (H : word -> bool) (m m' : word -> option byte) (a : Z) (pre src ja : list byte),
garr8 SEGS (mrestrict H m) a (u8s (pre ++ ja)) ->
(length src <= length ja)%nat ->
garr8 SEGS (mrestrict H m') (a + Z.of_nat (length pre)) (u8s src) ->
(forall x, a <= x < a + Z.of_nat (length pre) -> aview SEGS H m' x = aview SEGS H m x) ->
(forall x, a + Z.of_nat (length pre) + Z.of_nat (length src) <=
x < a + Z.of_nat (length pre) + Z.of_nat (length ja) -> aview SEGS H m' x = aview SEGS H m x) ->
garr8 SEGS (mrestrict H m') a (u8s (pre ++ src ++ skipn (length src) ja)).
Proof.
intros H m m' a pre src ja HG Hle HS Hkpre Hktail.
unfold u8s in HG, HS |- *. rewrite map_app in HG.
destruct (proj1 (garr8_app SEGS (mrestrict H m) a _ _) HG) as (HGp & HGj).
rewrite length_map in HGj.
assert (HJsplit : map (fun x : byte => bv_unsigned x) ja
= map (fun x : byte => bv_unsigned x) (firstn (length src) ja)
++ map (fun x : byte => bv_unsigned x) (skipn (length src) ja)).
{ rewrite <- map_app, firstn_skipn. reflexivity. }
rewrite HJsplit in HGj.
destruct (proj1 (garr8_app SEGS (mrestrict H m) (a + Z.of_nat (length pre)) _ _) HGj) as (_ & HGt).
rewrite length_map, length_firstn, (Nat.min_l _ _ Hle) in HGt.
rewrite !map_app.
apply (proj2 (garr8_app SEGS (mrestrict H m') a _ _)). split.
- apply (garr8_frame SEGS (mrestrict H m) _ a _ HGp).
  intros x Hx. apply (mbyte_of_aview SEGS). apply Hkpre. rewrite length_map in Hx. exact Hx.
- rewrite length_map.
  apply (proj2 (garr8_app SEGS (mrestrict H m') (a + Z.of_nat (length pre)) _ _)). split; [exact HS|].
  rewrite length_map.
  apply (garr8_frame SEGS (mrestrict H m) _ _ _ HGt).
  intros x Hx. apply (mbyte_of_aview SEGS). apply Hktail.
  rewrite length_map, length_skipn in Hx. lia.
Qed.


(* ---- The premise bundle of __asan_memcpy at 0x82f44,
   proved by this lane's helper and pasted
   verbatim from its scratch file S3Cpy_scratch.v
   (sha256 63d50626ac54; internal record) lines 92-189. ---- *)
(* ---- THE PREMISE BUNDLE OF __asan_memcpy AT 0x82f44.  The call copies n = scene_len k bytes from
   x = blk.i + scT_src k (blk.i = F + 32; scT_src k = 9 at k = 0, else 7) to d = again + scT_off k.
   The conclusion is, in aj_intrin_atS's order (lib/AU/Prog/YC85.v:243-253, = aj_intrin_at lib/AU/YCbq.v:1954-1964
   = aintrin_realizes lib/Reusable/YG0d.v:321-326 at op = OCpy), every premise about the addresses and the memory:
   the size and destination range, the destination's per-byte write permission and its stack exclusion, its
   amem_range / range_addressable / shadow hull, and the whole OCpy source clause.
   Hypotheses beyond the cut, all facts the lane holds INSIDE the turn at the call:
   - HJ : the journal from the entry to the call state (lyc, Sc, W, memT, mdc), the one aj_intrin_atS consumes;
   - Hin : `again` is still a live block at the call state;
   - H0 / H2 : blk.i's shadow after the unpoison stores 0x82eac-0x82ec0 (00 00 00 00 02), at memT;
   - Hsp / Ho : the call's stack offset, the same two facts aj_intrin_atS asks for.
   d, x, n are quantified with their defining equations, so a caller instantiates them with its register values. ---- *)
Lemma s3_cpy_pre : forall (cx : rtcx SEGS) ly3 S3 (W3 : world SEGS) regs3 mem3 md3 bs body again b k
(lyc : alayout) (Sc : astate) (W : world SEGS) (memT : word -> option byte) (mdc : Model) (ev : Z)
(regsT : bvmap 5 word) (o d x n : Z),
cut_T (SK := scene_sink_head) SEGS B ameter_triv WK scene_geom_asan_ubsan cx
ly3 S3 W3 regs3 mem3 md3 bs body again b k ->
k < sg_nturns scene_geom_asan_ubsan ->
ajournal (SK := scene_sink_head) SEGS B (sw_stk WK) (spZ (c_regs cx)) []
(c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(8, c_fpos cx)] lyc Sc W memT mdc ev ->
In (again, sg_scene_n scene_geom_asan_ubsan) (ablocks B lyc Sc) ->
(forall j, 4 <= j < 8 ->
aview SEGS (w_H W) memT (shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) + j) = Some 0) ->
aview SEGS (w_H W) memT (shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) + 8) = Some 2 ->
spZ regsT = spZ (c_regs cx) + o -> ESTACK - o <= sw_stk WK ->
d = again + scT_off k ->
x = sc_F SEGS scene_geom_asan_ubsan cx + 32 + scT_src k ->
n = scene_len k ->
(0 <= n < 2 ^ 32 /\ 0 <= d /\ d + n <= 2 ^ 63) /\
(forall a, d <= a < d + n ->
awr_byte (sw_stk WK) (spZ (c_regs cx)) [] (ablocks B (c_ly cx) (c_S cx)) (ablocks B lyc Sc) lyc
[(8, c_fpos cx)] a /\
~ (spZ (c_regs cx) + o - ESTACK <= a < spZ (c_regs cx) + o)) /\
amem_range d n /\
range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF d n /\
(0 < n -> shadow_hull_vis (aview SEGS (w_H W) memT) d n) /\
(0 <= x /\ x + n <= 2 ^ 63 /\ src_ok SEGS W regsT memT x n /\ (d + n <= x \/ x + n <= d) /\
amem_range x n /\ range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF x n /\
(0 < n -> shadow_hull_vis (aview SEGS (w_H W) memT) x n)).
Proof.
intros cx ly3 S3 W3 regs3 mem3 md3 bs body again b k lyc Sc W memT mdc ev regsT o d x n
HT Hkn HJ Hin H0 H2 Hsp Ho Hd Hx Hn.
destruct HT as (Hk & _ & _ & _ & _ & _ & Hoka & _).
cbn [sg_nturns sg_scene_n scene_geom_asan_ubsan] in Hk, Hkn, Hoka, Hin.
destruct Hoka as (Halo & _ & Hahi & _ & Hawr & _).
change (req_size 8904) with 8904 in Hahi, Hawr.
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (_ & _ & Hceil & Hslo & _).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hfb : fs_frame_bytes 8 = 16384) by reflexivity.
pose proof YM05.alloc_ceiling_lt as Hlt.
(* the fake frame at the call state's layout is the cut's F *)
assert (HFE : frame_addr lyc 8 (c_fpos cx) = sc_F SEGS scene_geom_asan_ubsan cx).
{ destruct Hly as (_ & _ & _ & _ & _ & HF & _). unfold sc_F, rt_F, frame_addr. rewrite HF. reflexivity. }
assert (Hinf : In (8, c_fpos cx) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS lyc Sc W memT mdc 8 (c_fpos cx) HAR Hinf) as (Hal & _ & Hpres & _).
destruct (frames_bounds SEGS B LAWS lyc Sc W memT mdc 8 (c_fpos cx) HAR Hinf) as (HFlo & HFhi & Happ).
pose proof (sep_block_frame SEGS B LAWS lyc Sc W memT mdc again 8904 8 (c_fpos cx) HAR Hin Hinf) as Hsep.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. change (req_size 8904) with 8904 in Hsep.
rewrite HFE in Hal, Hpres, HFlo, HFhi, Happ, Hsep. rewrite Hfb in Hpres, HFhi, Happ, Hsep.
set (F := sc_F SEGS scene_geom_asan_ubsan cx) in *.
assert (H8 : F mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal; [|lia]. destruct Hal as [q Hq]. exists (4 * q). lia. }
(* the three numbers of the call *)
pose proof (s3_off_range k ltac:(lia)) as Hoff.
pose proof (s3_bound k ltac:(lia)) as Hbnd.
assert (Hsrc : 7 <= scT_src k /\ scT_src k + scene_len k <= 33 /\ 14 <= scene_len k)
by (unfold scT_src, scene_len; destruct (k =? 0); [lia | destruct (k =? 342); lia]).
split; [split; [lia | split; lia]|].
(* the destination: write permission (sc_blk_ok's in_tmp_block clause) and the stack window above alloc_ceiling *)
split.
{ intros a Ha. split.
  - replace a with (again + (a - again)) by lia.
    apply (Hawr (ablocks B lyc Sc) lyc [(8, c_fpos cx)] (a - again) Hin). lia.
  - lia. }
split; [exact (amem_range_of_block SEGS B LAWS lyc Sc W memT mdc again 8904 d n HAR Hin
  ltac:(lia) ltac:(change (req_size 8904) with 8904; lia))|].
split; [exact (range_addressable_of_block SEGS B LAWS lyc Sc W memT mdc again 8904 d n HAR Hin
  ltac:(lia) ltac:(change (req_size 8904) with 8904; lia))|].
split; [intros Hn0; exact (shadow_hull_vis_of_block SEGS B LAWS lyc Sc W memT mdc again 8904 d n HAR Hin
  ltac:(lia) ltac:(change (req_size 8904) with 8904; lia) Hn0)|].
(* the source: inside blk.i's 34 bytes, inside the fake frame *)
split; [lia|]. split; [lia|].
split.
{ intros a Ha. split.
  - apply aview_some_of_apresent. exact (proj1 (Hpres a ltac:(lia))).
  - rewrite Hsp. lia. }
split; [lia|].
split.
{ unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. lia. }
split.
{ exact (block_shadow_range (aview SEGS (w_H W) memT) SHADOW_OFF (F + 32) 34 x n
  (s3_shadow_blki (aview SEGS (w_H W) memT) F H8 H0 H2) ltac:(lia) ltac:(lia)). }
intros Hn0.
exact (shadow_hull_vis_of_frame _ _ LAWS lyc Sc W memT mdc 8 (c_fpos cx) x n HAR Hinf
  ltac:(rewrite HFE; lia) ltac:(rewrite HFE, Hfb; lia) Hn0).
Qed.

(* ---- The run infrastructure of the turn's first part (0x82eac .. the build_scene_step call), proved by
   this lane's helper and pasted verbatim, on its hand-over at 04:24Z, from its scratch file
   S3Run_scratch.v (sha256 75d1723198de; internal record) lines 857-1084 (the lemmas it reports Qed; the
   walk lemma s3_run_build itself was still in progress then). ---- *)
Let RUN := paj_run (SK := scene_sink_head) B LAWS.
(* No shadow check runs in 0x82eac .. 0x82ed0, so the run carries no shadow entry and an empty span. *)
Definition S3_BSPAN : Z * Z := (0, 0).
(* The entry block without the spill region (the stores and moves of 0x82eac .. 0x82ed0 never touch it), with the
   unsigned range of s3's atom 19 = shadow_addr F, so the run's window check sees the shadow region's window. *)
Definition S3_F19 : afact := mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0.
Definition s3_ss_sh : sstate := mkSS S3_PC sr_atoms [s3_shadow_region] None (mkFacts [(19%nat, S3_F19)] [] []).

(* shadow_addr F is s3, atom 19 of the entry environment. *)
Lemma s3r_E19 : forall (cx : rtcx SEGS) ly3 S3 (W3 : world SEGS) regs3 mem3 md3 bs body again b k,
sc_base SEGS B ameter_triv WK cx ->
cut_T (SK := scene_sink_head) SEGS B ameter_triv WK scene_geom_asan_ubsan cx
ly3 S3 W3 regs3 mem3 md3 bs body again b k ->
bv_unsigned (ew (Eimg (Ereg regs3 [])) 19%nat) = shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) /\
0 <= sc_F SEGS scene_geom_asan_ubsan cx / 8 <= 2 ^ 44.
Proof.
intros cx ly3 S3 W3 regs3 mem3 md3 bs body again b k HB HT.
destruct (s3_cut_F cx ly3 S3 W3 regs3 mem3 md3 bs body again b k HB HT) as (_ & Hlo & Hhi).
assert (Hfb : fs_frame_bytes 8 = 16384) by reflexivity.
destruct HT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HshF & _).
cbn [sgT_shF scene_geom_asan_ubsan vat] in HshF.
revert Hlo Hhi HshF. generalize (sc_F SEGS scene_geom_asan_ubsan cx) as F. intros F Hlo Hhi HshF.
assert (HFd : F / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
assert (HFd0 : 0 <= F / 8) by (apply Z.div_pos; lia).
split; [|lia].
rewrite (s3e_ew regs3 RV_s3 19%nat ltac:(lia) ltac:(vm_compute; reflexivity)).
unfold RV_s3 in *. rewrite HshF. unfold shadow_addr. apply s3e_unsigned64. unfold SHADOW_OFF. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   Small helpers of the piece.
   --------------------------------------------------------------------------------------------------------------- *)
#[local] Notation TPI := (@pl_tpi scene_listing PL_scene).
#[local] Notation ATT := (A_TT (PI := PI_scene)).

(* A register the symbolic state names as an entry atom holds that atom's value. *)
Lemma s3r_reg_off : forall (H : word -> bool) E ss ms (r : bv 5) n,
st_ok SEGS E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 -> getr (ms_regs ms) r = ew E n.
Proof.
intros H E ss ms r n HS Hr. rewrite (st_ok_restrict_reg SEGS H E ss ms r HS), Hr.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* A one-byte literal chunk of a region pins that byte. *)
Lemma s3r_chunk_byte : forall E (m : word -> option byte) base off v,
YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal 1 (SLit v))) -> 0 <= v < 256 ->
mbyte SEGS m (base + off) = Some (Z_to_bv 8 v).
Proof.
intros E m base off v Hc Hv. unfold YP09.chunk_ok in Hc.
destruct (Hc 0 ltac:(cbn [YP09.c_len YP09.cv_len YP09.c_val]; lia)) as (x & Hx & Hm).
cbn [YP09.cbyte YP09.c_off YP09.c_val] in Hx, Hm. injection Hx as <-.
rewrite Z.add_0_r in Hm. rewrite Hm. f_equal.
unfold YP09.byte_of_word. cbn [sv_denot]. rewrite s3e_unsigned64 by lia.
replace (8 * 0) with 0 by lia. rewrite Z.shiftr_0_r. reflexivity.
Qed.

(* range_addressable reads only the shadow cells of its range. *)
Lemma s3r_ra_keep : forall (rd rd' : Z -> option Z) a n,
(forall x, a <= x < a + n -> rd' (shadow_of_addr SHADOW_OFF x) = rd (shadow_of_addr SHADOW_OFF x)) ->
range_addressable rd SHADOW_OFF a n -> range_addressable rd' SHADOW_OFF a n.
Proof. intros rd rd' a n HK HR x Hx. rewrite HK by exact Hx. exact (HR x Hx). Qed.

(* block_shadow (sc_open) reads only the shadow cells of its object. *)
Lemma s3r_open_keep : forall (rd rd' : Z -> option Z) p n,
(forall i, 0 <= i < (n + 7) / 8 -> rd' (shadow_of_addr SHADOW_OFF p + i) = rd (shadow_of_addr SHADOW_OFF p + i)) ->
block_shadow rd SHADOW_OFF p n -> block_shadow rd' SHADOW_OFF p n.
Proof.
intros rd rd' p n HK (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
intros i Hi. rewrite HK by exact Hi. exact (H3 i Hi).
Qed.

(* s3_bss_blki_pre with the model left free: the run materialises the model, the call needs the four facts at it. *)
Lemma s3r_blki_pre : forall (cx : rtcx SEGS) ly3 S3 (W3 : world SEGS) regs3 mem3 md3 bs body again b k
(mem' : word -> option byte) md',
sc_base SEGS B ameter_triv WK cx ->
cut_T (SK := scene_sink_head) SEGS B ameter_triv WK scene_geom_asan_ubsan cx
ly3 S3 W3 regs3 mem3 md3 bs body again b k ->
AR SEGS B ly3 S3 W3 mem' md' ->
(forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) mem' a) ->
(forall o, 4 <= o < 8 ->
aview SEGS (w_H W3) mem' (shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) + o) = Some 0) ->
aview SEGS (w_H W3) mem' (shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) + 8) = Some 2 ->
(exists cid pos, In (cid, pos) [(8, c_fpos cx)] /\ 0 <= cid /\
frame_addr ly3 cid pos <= sc_F SEGS scene_geom_asan_ubsan cx + 32 /\
sc_F SEGS scene_geom_asan_ubsan cx + 32 + 34 <= frame_addr ly3 cid pos + fs_frame_bytes cid) /\
(forall a, sc_F SEGS scene_geom_asan_ubsan cx + 32 <= a < sc_F SEGS scene_geom_asan_ubsan cx + 32 + 34 ->
apresent (w_H W3) mem' a) /\
range_addressable (aview SEGS (w_H W3) mem') SHADOW_OFF (sc_F SEGS scene_geom_asan_ubsan cx + 32) 34 /\
shadow_hull_vis (aview SEGS (w_H W3) mem') (sc_F SEGS scene_geom_asan_ubsan cx + 32) 34.
Proof.
intros cx ly3 S3 W3 regs3 mem3 md3 bs body again b k mem' md' HB HT HAR' Hgrow H0 H2.
pose proof HT as HT'.
destruct HT' as (_ & _ & Hj & _ & _ & _ & _ & _ & _ & _ & _ & Hfrm & _).
destruct Hj as (HJ & Hfrs & _).
cbn [sg_cid scene_geom_asan_ubsan] in HJ, Hfrs.
assert (HFE : frame_addr ly3 8 (c_fpos cx) = sc_F SEGS scene_geom_asan_ubsan cx).
{ unfold sc_F, rt_F. cbn [sg_cid scene_geom_asan_ubsan].
exact (s3_layout_eq cx ly3 S3 W3 mem3 md3 2 HB HJ 8 (c_fpos cx)). }
destruct (s3_cut_F cx ly3 S3 W3 regs3 mem3 md3 bs body again b k HB HT) as (Hal & Hlo & Hhi).
assert (Hfb : fs_frame_bytes 8 = 16384) by (vm_compute; reflexivity).
assert (H8 : sc_F SEGS scene_geom_asan_ubsan cx mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal; [|lia]. destruct Hal as [q Hq]. exists (4 * q). lia. }
assert (Hin : In (8, c_fpos cx) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct Hfrm as (_ & Hpres & _).
cbn [sg_cid scene_geom_asan_ubsan] in Hpres.
split; [exists 8, (c_fpos cx); split; [left; reflexivity|]; split; [lia|]; rewrite HFE; lia|].
split.
{ intros a Ha. apply Hgrow. apply Hpres. unfold sc_F, rt_F in Ha. cbn [sg_cid scene_geom_asan_ubsan] in Ha.
unfold sc_F, rt_F. cbn [sg_cid scene_geom_asan_ubsan]. lia. }
split.
{ exact (s3_ra_blki (aview SEGS (w_H W3) mem') (sc_F SEGS scene_geom_asan_ubsan cx) H8 H0 H2). }
rewrite <- HFE.
exact (shadow_hull_vis_of_frame _ _ LAWS ly3 S3 W3 mem' md' 8 (c_fpos cx)
(frame_addr ly3 8 (c_fpos cx) + 32) 34 HAR' Hin ltac:(lia) ltac:(rewrite Hfb; lia) ltac:(lia)).
Qed.

(* ---- One concrete step: the branch at 0x82ed4.  These five lemmas are copied from a Theorem Labs lane's
   lib/A/P_LLVMFuzzerTestOneInput_S4.v at 1e7a7d0d863 (s4_fetch, s4_reg, s4_pc4,
   s4_branch, s4_branch_off), with the prefix changed; they hold no image fact. ---- *)
Lemma s3r_fetch : forall k w, plookup TPI k = Some (PW w) ->
fetch_word SEGS (Z_to_bv 64 (BASE + k)) = Some (Z_to_bv 32 w).
Proof. intros k w H. exact (pa_fetch_pw k w H). Qed.

Lemma s3r_reg : forall (W : world SEGS) regs k mem md regs' k' Q,
RiscvSemantics.step SEGS (mkst regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (seg_rom SEGS))
= MachineOk (mkst regs' (Z_to_bv 64 (BASE + k')) (mrestrict (w_H W) mem) (seg_rom SEGS)) ->
(forall md', same_but_materialized md md' ->
SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + k')) mem (seg_rom SEGS)) md') Q) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + k)) mem (seg_rom SEGS)) md) Q.
Proof.
intros W regs k mem md regs' k' Q Hs HK.
eapply (SRr_step SEGS pa_wx W (mkst regs (Z_to_bv 64 (BASE + k)) mem (seg_rom SEGS))
(mkst regs' (Z_to_bv 64 (BASE + k')) (mrestrict (w_H W) mem) (seg_rom SEGS)) md Q).
- reflexivity.
- rewrite restrict_mkst_fx. exact Hs.
- intros md' Hm. cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict. exact (HK md' Hm).
Qed.

Lemma s3r_pc4 : forall k, v_addi (Z_to_bv 64 (BASE + k)) 4 = Z_to_bv 64 (BASE + (k + 4)).
Proof. intros k. rewrite YCbn.v_addi_lit. f_equal. lia. Qed.

Lemma s3r_branch : forall (W : world SEGS) regs k mem md Q w c rs1 rs2 (imm : bv 13),
plookup TPI k = Some (PW w) -> is_ecall (Z_to_bv 32 w) = false ->
decode_any (Z_to_bv 32 w) = Some (Branch c rs1 rs2 imm, 4%Z) ->
(branch_taken c (getr regs rs1) (getr regs rs2) = true -> forall md', same_but_materialized md md' ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + (k + bv_signed imm))) mem (seg_rom SEGS)) md') Q) ->
(branch_taken c (getr regs rs1) (getr regs rs2) = false -> forall md', same_but_materialized md md' ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + (k + 4))) mem (seg_rom SEGS)) md') Q) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + k)) mem (seg_rom SEGS)) md) Q.
Proof.
intros W regs k mem md Q w c rs1 rs2 imm Hpl He Hd HT HF.
destruct (branch_taken c (getr regs rs1) (getr regs rs2)) eqn:Hb.
- eapply s3r_reg; [|exact (HT eq_refl)].
rewrite (step_branch_tk_gen SEGS regs _ _ _ (Z_to_bv 32 w) c rs1 rs2 imm (s3r_fetch k w Hpl) He Hd Hb).
unfold btgt. rewrite YCbn.v_addi_lit.
replace (BASE + k + bv_signed imm) with (BASE + (k + bv_signed imm)) by lia. reflexivity.
- eapply s3r_reg; [|exact (HF eq_refl)].
rewrite (step_branch_ft_gen SEGS regs _ _ _ (Z_to_bv 32 w) c rs1 rs2 imm (s3r_fetch k w Hpl) He Hd Hb).
rewrite s3r_pc4. reflexivity.
Qed.

Lemma s3r_branch_off : forall (W : world SEGS) regs k mem md Q w c r1 r2 (imm : bv 13) rs1 rs2 off,
plookup TPI k = Some (PW w) -> is_ecall (Z_to_bv 32 w) = false ->
decode_any (Z_to_bv 32 w) = Some (Branch c r1 r2 imm, 4%Z) ->
r1 = rs1 -> r2 = rs2 -> bv_signed imm = off ->
(branch_taken c (getr regs rs1) (getr regs rs2) = true -> forall md', same_but_materialized md md' ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + (k + off))) mem (seg_rom SEGS)) md') Q) ->
(branch_taken c (getr regs rs1) (getr regs rs2) = false -> forall md', same_but_materialized md md' ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + (k + 4))) mem (seg_rom SEGS)) md') Q) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + k)) mem (seg_rom SEGS)) md) Q.
Proof.
intros W regs k mem md Q w c r1 r2 imm rs1 rs2 off Hpl He Hd E1 E2 Hoff HT HF.
subst r1 r2.
apply (s3r_branch W regs k mem md Q w c rs1 rs2 imm Hpl He Hd); rewrite ?Hoff; assumption.
Qed.

(* ---- The cut's located values, all but `a1 = body` (a1 is the callee's to clobber): the twenty-one `vat`s of
   cut_T in its own order, each at the expression cut_T states it with. ---- *)
Definition s3_vats (cx : rtcx SEGS) (bs : Z -> Z) (body again k : Z) : list (vloc * Z) :=
let IM := scene_geom_asan_ubsan in
[(sgT_sp0 IM, spZ (c_regs cx)); (sgT_sp1 IM, c_sp1 cx); (sgT_Fsp IM, sc_F SEGS IM cx);
(sgT_shF IM, shadow_addr (sc_F SEGS IM cx)); (sgT_blki IM, sc_F SEGS IM cx + sg_off_blki IM);
(sgT_srcA IM, sc_F SEGS IM cx + sg_off_blki IM + 7); (sgT_srcB IM, sc_F SEGS IM cx + sg_off_blki IM + 9);
(sgT_mac IM, sc_F SEGS IM cx + sg_off_mac IM);
(sgT_shexp IM, shadow_addr (sc_F SEGS IM cx) + sg_off_expect IM / 8);
(sgT_body IM, body); (sgT_again IM, again); (sgT_nprime IM, sg_scene_n IM); (sgT_got IM, scT_off k);
(sgT_k IM, k); (sgT_decl IM, if k =? 0 then 0 else sg_scene_n IM); (sgT_n1 IM, sg_scene_n IM);
(VSpill 0x50, 2 ^ 64 - 1 - again);
(sgT_expect IM, sc_F SEGS IM cx + sg_off_expect IM); (sgT_Fb IM, sc_F SEGS IM cx); (sgT_nn IM, sc_nn IM bs);
(sgT_f8 IM, 2 ^ 64 - 8)].

Lemma s3r_vats_cut : forall (cx : rtcx SEGS) ly3 S3 (W3 : world SEGS) regs3 mem3 md3 bs body again b k,
cut_T (SK := scene_sink_head) SEGS B ameter_triv WK scene_geom_asan_ubsan cx
ly3 S3 W3 regs3 mem3 md3 bs body again b k ->
Forall (fun lv => vat SEGS (c_sp1 cx) W3 mem3 regs3 (fst lv) (snd lv)) (s3_vats cx bs body again k).
Proof.
intros cx ly3 S3 W3 regs3 mem3 md3 bs body again b k HT.
destruct HT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13 & V14 & V15 & V16 & _ & V17 &
V18 & V19 & V20 & _ & V21).
unfold s3_vats. cbv zeta.
repeat (apply Forall_cons; [cbn [fst snd]; assumption|]). apply Forall_nil.
Qed.

(* where each of those values lives: a callee-saved register, or a spill word inside [sp1 + 8, sp1 + 0x60) *)
Definition s3_vloc_okb (l : vloc) : bool :=
match l with
| VReg r => let z := bv_unsigned r in
(z =? 2) || (z =? 3) || (z =? 4) || (z =? 8) || (z =? 9) || ((18 <=? z) && (z <=? 27))
| VSpill off => (8 <=? off) && (off + 8 <=? 0x60)
end.

Lemma s3r_vat_keep : forall (sp1 : Z) (W : world SEGS) mem mem' regs regs' l v,
vat SEGS sp1 W mem regs l v -> s3_vloc_okb l = true -> aregs_preserved regs regs' ->
(forall i, 8 <= i < 0x60 -> aview SEGS (w_H W) mem' (sp1 + i) = aview SEGS (w_H W) mem (sp1 + i)) ->
vat SEGS sp1 W mem' regs' l v.
Proof.
intros sp1 W mem mem' regs regs' l v Hv Hok HP HK.
destruct l as [r | off]; cbn [vat s3_vloc_okb] in *.
- assert (Hr : acallee_saved (bv_unsigned r)).
  { rewrite !Bool.orb_true_iff, !Bool.andb_true_iff, !Z.eqb_eq, !Z.leb_le in Hok.
    unfold acallee_saved. lia. }
  pose proof (HP _ Hr) as E. rewrite !Z_to_bv_bv_unsigned in E. rewrite E. exact Hv.
- apply andb_prop in Hok as [H1 H2]. apply Z.leb_le in H1, H2.
  rewrite (rdword_ext (aview SEGS (w_H W) mem)); [exact Hv|].
  intros i Hi. replace (sp1 + off + i) with (sp1 + (off + i)) by lia. apply HK. lia.
Qed.


(* ---- The turn's first part as one lemma: from the cut, the five unpoison stores, the argument moves,
   reac_ctrl_build_scene_step at 0x82ed0 and the refuted abort edge `bnez a0` 0x82ed4, landing at 0x82ed8 in the
   state s3_build_post names.  Proved by a helper, pasted verbatim from S3Run_scratch.v
   (sha256 75d1723198de; internal record) lines 1085-1453 (its 04:50Z hand-over, after
   trimming). ---- *)
(* ================================================================================================================
   THE POST the first part of the turn hands on: the machine is at 0x82ed8 (BASE + AF_LLVMFuzzerTestOneInput + 0x634),
   the fall-through of `bnez a0` 0x82ed4, after reac_ctrl_build_scene_step returned 0.
   F = sc_F, blk.i = F + 32, sp1 = c_sp1 (the sp of the call), the callee's window [sp1 - SCENE_STEP_WIN, sp1).
   ================================================================================================================ *)
Definition s3_build_post (cx : rtcx SEGS) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (regs3 : bvmap 5 word)
(mem3 : word -> option byte) (bs : Z -> Z) (body again : Z) (b : list byte) (k : Z)
(W4 : world SEGS) (regs4 : bvmap 5 word) (mem4 : word -> option byte) (md4 : Model) : Prop :=
let IM := scene_geom_asan_ubsan in
let F := sc_F SEGS IM cx in
W4 = W3 /\
(* the journal from the entry, at the cut's own event count *)
ajournal (SK := scene_sink_head) SEGS B (sw_stk WK) (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
(c_md cx) [(sg_cid IM, c_fpos cx)] ly3 S3 W3 mem4 md4 2 /\
aregs_preserved regs3 regs4 /\ getr regs4 10 = w64 0 /\
(* blk.i is the turn's block, and its shadow is open (four 00 and one 02, s3_shadow_blki) *)
(forall i, 0 <= i < 34 ->
aview SEGS (w_H W3) mem4 (F + sg_off_blki IM + i) = Some (bv_unsigned (nth (Z.to_nat i) (scene_block b k) (Z_to_bv 8 0)))) /\
sc_shr SEGS IM cx W3 mem4 4 8 0 /\ sc_shr SEGS IM cx W3 mem4 8 9 2 /\
(* everything else is the cut's: outside the callee's window, blk.i and blk.i's shadow, memory is unchanged, and
   nothing present went away *)
(forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx - SCENE_STEP_WIN <= a < c_sp1 cx) ->
(~ (F + sg_off_blki IM <= a < F + sg_off_blki IM + sg_blk_n IM) /\
~ (shadow_addr F + sg_sh_blki_lo IM <= a < shadow_addr F + sg_sh_blki_hi IM)) ->
aview SEGS (w_H W3) mem4 a = aview SEGS (w_H W3) mem3 a) /\
(forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) mem4 a) /\
(* the cut's memory facts, carried *)
sc_frame SEGS IM cx W3 mem4 /\ sc_saves SEGS cx W3 mem4 /\ sc_shbg SEGS IM cx W3 mem4 /\
sc_open SEGS IM cx W3 mem4 (sg_off_blk IM) (sg_blk_n IM) /\ sc_open SEGS IM cx W3 mem4 (sg_off_mac IM) (sg_mac_n IM) /\
garr8 SEGS (mrestrict (w_H W3) mem4) body (u8s b) /\
(exists ja : list byte, Z.of_nat (length ja) = sg_scene_n IM - scT_off k /\
garr8 SEGS (mrestrict (w_H W3) mem4) again (u8s (firstn (Z.to_nat (scT_off k)) b ++ ja))) /\
garr8 SEGS (mrestrict (w_H W3) mem4) (F + sg_off_mac IM) (sc_macb bs) /\
(* the cut's located values, at the new registers and memory *)
Forall (fun lv => vat SEGS (c_sp1 cx) W3 mem4 regs4 (fst lv) (snd lv)) (s3_vats cx bs body again k).

Local Ltac s3r_rd HS r n H :=
lazymatch type of HS with st_ok _ ?E ?ss (restrict ?Hh ?ms) =>
pose proof (s3r_reg_off Hh E ss ms r n HS ltac:(vm_compute; reflexivity)) as H end.

Lemma s3_run_build : forall (cx : rtcx SEGS) ly3 S3 (W3 : world SEGS) regs3 mem3 md3 bs body again b k POST,
sc_base SEGS B ameter_triv WK cx ->
cut_T (SK := scene_sink_head) SEGS B ameter_triv WK scene_geom_asan_ubsan cx
ly3 S3 W3 regs3 mem3 md3 bs body again b k ->
k < sg_nturns scene_geom_asan_ubsan ->
(* reac_ctrl_build_scene_step's four TAIL_TRAILER conjuncts, as its spec states them, at the cut's state *)
(forall i, 0 <= i < TT_LEN ->
aview SEGS (w_H W3) mem3 (ATT + i) = Some (bv_unsigned (nth (Z.to_nat i) scene_trailer (Z_to_bv 8 0)))) ->
range_addressable (aview SEGS (w_H W3) mem3) SHADOW_OFF ATT TT_LEN ->
shadow_hull_vis (aview SEGS (w_H W3) mem3) ATT TT_LEN ->
(ATT + TT_LEN <= sc_F SEGS scene_geom_asan_ubsan cx + sg_off_blki scene_geom_asan_ubsan \/
sc_F SEGS scene_geom_asan_ubsan cx + sg_off_blki scene_geom_asan_ubsan + BLK_LEN <= ATT) ->
(forall (W4 : world SEGS) regs4 mem4 md4,
s3_build_post cx ly3 S3 W3 regs3 mem3 bs body again b k W4 regs4 mem4 md4 ->
SRr SEGS W4 (cfg_at SEGS (BASE + AF_LLVMFuzzerTestOneInput + 0x634) regs4 mem4 md4) POST) ->
SRr SEGS W3 (cfg_at SEGS (sg_pc_t scene_geom_asan_ubsan) regs3 mem3 md3) POST.
Proof.
intros cx ly3 S3 W3 regs3 mem3 md3 bs body again b k POST HB HT Hk343 HTT HRAtt HHVtt HTTd HK.
(* ---------------- the cut, taken apart ---------------- *)
pose proof (s3r_vats_cut cx ly3 S3 W3 regs3 mem3 md3 bs body again b k HT) as HV3.
destruct (s3r_E19 cx ly3 S3 W3 regs3 mem3 md3 bs body again b k HB HT) as (U19 & _).
destruct (s3_keep_F ameter_triv cx ly3 S3 W3 regs3 mem3 md3 bs body again b k HT) as (HFly & HFin).
destruct (s3_cut_F cx ly3 S3 W3 regs3 mem3 md3 bs body again b k HB HT) as (HF32 & HF4096 & HF47).
pose proof HT as (Hk & _ & (HJ & Hfrs & _) & Hab & _ & Hokb & Hoka & _ & Hlenb & Hgb & Hga & Hfrm & Hsav & Hbg &
_ & Hopb & Hopm & (Hsp & Hgp & Htp & _) & _ & Hgm & _ & _ & _ & HshF & Hblki & _ & _ & _ & _ & _ & _ & _ & _ &
Hkv & _ & Hn1 & _ & _ & _ & _ & _ & Ha1 & _).
cbn [sg_cid sg_scene_n sg_nturns sg_off_blki sgT_shF sgT_blki sgT_k sgT_n1 sgT_body2 scene_geom_asan_ubsan vat]
in Hk343, HTTd, HFly, HFin, HJ, Hfrs, Hab, Hokb, Hoka, Hlenb, HshF, Hblki, Hkv, Hn1, Ha1.
pose proof (proj1 HJ) as HAR.
pose proof HB as (_ & Hsp1eq).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hsp16 & _ & Hceil & Hstklo & Hsphi & Hstkhi & _).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 8 (c_fpos cx) HAR HFin) as (_ & HFceil & HFapp).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR HFin) as HFimg.
assert (Hfb : fs_frame_bytes 8 = 16384) by reflexivity.
rewrite HFly in HFceil, HFapp, HFimg. rewrite Hfb in HF47, HFceil, HFapp, HFimg.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, off_img in HFapp, HFimg.
pose proof asan_consts as (HAC & _ & _ & _ & _).
pose proof (@pa_obj_img _ scene_listing PI_scene 12%nat ltac:(lia)) as HTTimg.
change (VAL (A_OBJ 12)) with ATT in HTTimg.
unfold ASTACK in HSTK.
destruct Hokb as (Hb4096 & Hbz & Hbceil & _).
destruct Hoka as (Ha4096 & Haz & Haceil & _).
change (req_size 8904) with 8904 in Hbz, Hbceil, Haz, Haceil.
unfold zone2, off_img in Hbz, Haz.
assert (Hbin : In (body, 8904) (ablocks B ly3 S3))
by (rewrite Hab; apply in_or_app; left; apply in_or_app; right; left; reflexivity).
assert (Hain : In (again, 8904) (ablocks B ly3 S3))
by (rewrite Hab; apply in_or_app; right; left; reflexivity).
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 mem3 md3 body 8904 8 (c_fpos cx) HAR Hbin HFin) as Hbsep.
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 mem3 md3 again 8904 8 (c_fpos cx) HAR Hain HFin) as Hasep.
unfold zdisjoint in Hbsep, Hasep. cbn [fst snd] in Hbsep, Hasep.
rewrite HFly, Hfb in Hbsep, Hasep. change (req_size 8904) with 8904 in Hbsep, Hasep.
set (F := sc_F SEGS scene_geom_asan_ubsan cx) in *.
assert (HF8 : F mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply Z.mod_divide in HF32; [|lia]. destruct HF32 as [t Ht]. exists (4 * t). lia. }
pose proof (Z.div_mod F 8 ltac:(lia)) as HFq. rewrite HF8, Z.add_0_r in HFq.
assert (HshA : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity.
set (q := F / 8) in *.
assert (Hsp1b : spZ (c_regs cx) - 255 <= c_sp1 cx <= spZ (c_regs cx) - 224).
{ rewrite Hsp1eq. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 224) 32 ltac:(lia)) as Hm.
  pose proof (Z_div_mod_eq_full (spZ (c_regs cx) - 224) 32) as He. lia. }
assert (Ho16 : (c_sp1 cx - spZ (c_regs cx)) mod 16 = 0).
{ rewrite Hsp1eq. generalize ((spZ (c_regs cx) - 224) / 32) as t. intros t.
  apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hsp16; [|lia]. destruct Hsp16 as [u Hu]. exists (2 * t - u). lia. }
pose proof YM05.alloc_ceiling_lt as Hacl.
assert (HOK : scene_step_okZ (F + 32) body 8904 k = true).
{ unfold scene_step_okZ, SCENE_BYTES, SCENE_LAST.
  destruct (Z.eqb_spec (F + 32) 0), (Z.eqb_spec body 0), (Z.eqb_spec 8904 8904), (Z.leb_spec k 342);
  cbn; first [reflexivity | lia]. }
(* ---------------- the entry block: the frame-shadow region only, with atom 19's range ---------------- *)
pose proof (s3_entry_state cx ly3 S3 W3 regs3 mem3 md3 bs body again b k HB HT) as HS0.
pose proof (st_ok_pi_submem _ _ _ [s3_shadow_region] HS0 ltac:(unfold s3_ss; cbn [ss_mem]; submem_tac)
  ltac:(vm_compute; reflexivity)) as HS1.
clear HS0.
pose proof (st_ok_pi_add_fact _ _ _ 19%nat S3_F19 HS1) as HS2.
clear HS1.
specialize (HS2 ltac:(unfold afact_ok, S3_F19; cbn [af_lo af_hi af_al2]; rewrite U19, HshA;
  rewrite Z.pow_0_r, Z.mod_1_r; unfold SHADOW_OFF in *; lia)).
change (st_ok_pi SEGS VAL (Eimg (Ereg regs3 [])) s3_ss_sh
  (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (sg_pc_t scene_geom_asan_ubsan)) mem3 (seg_rom SEGS)))) in HS2.
rename HS2 into HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs3 []))) by apply Eimg_env.
assert (SHOK : sh_ok SEGS (SOff 0 0) [] (Eimg (Ereg regs3 [])) (mrestrict (w_H W3) mem3)) by constructor.
unfold cfg_at. change (w64 (sg_pc_t scene_geom_asan_ubsan)) with (Z_to_bv 64 (sg_pc_t scene_geom_asan_ubsan)).
unfold s3_ss_sh in HS.
(* ---------------- 0x82eac .. 0x82ed0: the five shadow stores, li, the three moves, jal ---------------- *)
paj_run_tok RUN HS HJ SHOK S3_BSPAN.
{ (* the run writes only blk.i's five shadow cells, which are the own frame's shadow *)
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?ownx =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx ownx) end.
  eapply awr_ok_cons_gen; [reflexivity | exact U19 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
  right; right; right. exists 8, (c_fpos cx). split; [left; reflexivity|]. right.
  unfold in_zr. cbn [fst snd]. rewrite HFly, Hfb. change (16384 / 8) with 2048. lia. }
(* ---------------- at the entry of reac_ctrl_build_scene_step ---------------- *)
cbn [ms_mem mkst] in HF, HFr, HG.
(* what the run did to memory: only the five shadow cells of blk.i changed *)
assert (Rrun : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr F + 4 <= a < shadow_addr F + 9) ->
  aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hn. apply (aview_eq_of SEGS). apply HFr. rewrite s3e_unsigned64 by exact Ha.
  intros (r & Hin & Hr). cbn [ss_mem In] in Hin. destruct Hin as [<- | []].
  cbn [s3_shadow_region YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hr. rewrite U19 in Hr. lia. }
assert (Prun : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem ms) a)
by (intros a Ha; exact (apresent_grows (w_H W3) mem3 (ms_mem ms) a HG Ha)).
(* the five cells the run wrote: 00 00 00 00 02 *)
pose proof (st_ok_mem_ok SEGS _ _ _ HS) as HM.
lazymatch type of HM with context [ss_mem ?x] =>
  let y := eval vm_compute in (ss_mem x) in change (ss_mem x) with y in HM end.
destruct HM as (_ & HMr & _).
apply Forall_inv in HMr. unfold YP09.region_ok in HMr.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val] in HMr.
rewrite U19 in HMr. destruct HMr as (_ & _ & _ & HMc). cbn [ms_mem restrict] in HMc.
assert (Sh : forall o v, 4 <= o < 9 -> v = (if o =? 8 then 2 else 0) ->
  aview SEGS (w_H W3) (ms_mem ms) (shadow_addr F + o) = Some v).
{ intros o v Ho ->. unfold aview.
  assert (Hc : YP09.chunk_ok SEGS (Eimg (Ereg regs3 [])) (mrestrict (w_H W3) (ms_mem ms)) (shadow_addr F)
    (YP09.mkChunk o (CVal 1 (SLit (if o =? 8 then 2 else 0))))).
  { apply (proj1 (Forall_forall _ _) HMc).
    assert (Hcase : o = 4 \/ o = 5 \/ o = 6 \/ o = 7 \/ o = 8) by lia.
    destruct Hcase as [-> | [-> | [-> | [-> | ->]]]]; cbn; tauto. }
  rewrite (s3r_chunk_byte _ _ _ _ _ Hc ltac:(destruct (o =? 8); lia)). cbn [option_map].
  rewrite s3_u8 by (destruct (o =? 8); lia). reflexivity. }
(* ---------------- the call: the registers at the jal ---------------- *)
pmkst HS.
rewrite pa_sigma_reac_ctrl_build_scene_step.
s3r_rd HS (2%bv : bv 5) 2%nat Rg2. s3r_rd HS (3%bv : bv 5) 3%nat Rg3. s3r_rd HS (4%bv : bv 5) 4%nat Rg4.
s3r_rd HS (10%bv : bv 5) 25%nat Rg10. s3r_rd HS (11%bv : bv 5) 11%nat Rg11. s3r_rd HS (12%bv : bv 5) 27%nat Rg12.
s3r_rd HS (13%bv : bv 5) 23%nat Rg13.
rewrite (s3e_ew regs3 (2%bv : bv 5) 2%nat ltac:(lia) ltac:(vm_compute; reflexivity)) in Rg2.
rewrite (s3e_ew regs3 (3%bv : bv 5) 3%nat ltac:(lia) ltac:(vm_compute; reflexivity)) in Rg3.
rewrite (s3e_ew regs3 (4%bv : bv 5) 4%nat ltac:(lia) ltac:(vm_compute; reflexivity)) in Rg4.
rewrite (s3e_ew regs3 RV_s9 25%nat ltac:(lia) ltac:(vm_compute; reflexivity)) in Rg10.
rewrite (s3e_ew regs3 RV_a1 11%nat ltac:(lia) ltac:(vm_compute; reflexivity)) in Rg11.
rewrite (s3e_ew regs3 RV_s11 27%nat ltac:(lia) ltac:(vm_compute; reflexivity)) in Rg12.
rewrite (s3e_ew regs3 RV_s7 23%nat ltac:(lia) ltac:(vm_compute; reflexivity)) in Rg13.
rewrite Hblki in Rg10. rewrite Ha1 in Rg11. rewrite Hn1 in Rg12. rewrite Hkv in Rg13.
pose proof (st_ok_restrict_reg SEGS (w_H W3) _ _ ms (1%bv : bv 5) HS) as Rra0.
assert (Rra : getr (ms_regs ms) (1%bv : bv 5) = Z_to_bv 64 (BASE + 1584))
by (rewrite Rra0; exact (codeptr_val _ 1584 HEI)).
clear Rra0.
assert (Rsp : spZ (ms_regs ms) = c_sp1 cx) by (unfold spZ; rewrite Rg2; exact Hsp).
(* the callee-saved registers are the cut's *)
assert (RK : forall r, acallee_saved r -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs3 (Z_to_bv 5 r)).
{ intros r Hr.
  assert (Hin : In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]) by (unfold acallee_saved in Hr; cbn [In]; lia).
  exact (regs_kept_of_st_ok SEGS _ _ _ regs3 [] (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27])
    HS ltac:(split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]) ltac:(vm_compute; reflexivity)
    (Z_to_bv 5 r) (in_map (Z_to_bv 5) _ r Hin)). }
set (rgS := ms_regs ms) in *. set (mmS := ms_mem ms) in *.
(* ---------------- reac_ctrl_build_scene_step (blk.i, body, 8904, k) ---------------- *)
eapply SRr_bind.
{ eapply (BSS W3 rgS mmS _ (sw_stk WK) (spZ (c_regs cx)) (c_sp1 cx - spZ (c_regs cx)) []
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(8, c_fpos cx)] ly3 S3 2 (F + 32) body 8904 k b HJ).
  - rewrite Rsp. lia.
  - exact Ho16.
  - lia.
  - unfold SCENE_STEP_WIN, SCENE_STEP_FRAME, ESTACK. lia.
  - rewrite Rg3. exact Hgp.
  - rewrite Rg4. exact Htp.
  - rewrite Rra. apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact Rg10.
  - exact Rg11.
  - exact Rg12.
  - exact Rg13.
  - lia.
  - lia.
  - lia.
  - lia.
  - intros _.
    destruct (s3r_blki_pre cx ly3 S3 W3 regs3 mem3 md3 bs body again b k mmS _ HB HT (proj1 HJ) Prun
      (fun o Ho => Sh o 0 ltac:(lia) ltac:(destruct (Z.eqb_spec o 8); [lia | reflexivity])) (Sh 8 2 ltac:(lia) eq_refl))
      as (P1 & P2 & P3 & P4).
    split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|].
    split; [exists body, 8904; split; [exact Hbin|]; change (req_size 8904) with 8904; unfold SCENE_BYTES; lia|].
    split; [unfold SCENE_BYTES; lia|].
    split.
    { intros i Hi. unfold SCENE_BYTES in Hi. rewrite Rrun by (unfold SHADOW_OFF in *; lia).
      apply (s3_bytes_of_garr8 (w_H W3) mem3 body b Hgb). lia. }
    split.
    { intros i Hi. unfold TT_LEN in Hi. rewrite Rrun by (unfold SHADOW_OFF in *; lia). exact (HTT i Hi). }
    split.
    { apply (s3r_ra_keep (aview SEGS (w_H W3) mem3)); [|exact HRAtt].
      intros x Hx. unfold TT_LEN in Hx. apply Rrun.
      - unfold shadow_of_addr. assert (0 <= x / 8 <= x) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
        unfold SHADOW_OFF in *. lia.
      - unfold shadow_of_addr. rewrite HshA. fold q.
        assert (Hx8 : x / 8 <= 0x5f9003 / 8) by (apply Z.div_le_mono; lia).
        assert (Hx8' : 0x10000 / 8 <= x / 8) by (apply Z.div_le_mono; lia).
        change (0x5f9003 / 8) with 782848 in Hx8. change (0x10000 / 8) with 8192 in Hx8'.
        revert Hx8 Hx8'. generalize (x / 8) as y. intros y Hx8 Hx8'. lia. }
    split.
    { intros s Hs. apply (aview_keeps_vis SEGS (w_H W3) mem3 mmS s HG). exact (HHVtt s Hs). }
    exact HTTd. }
(* ---------------- the callee's post ---------------- *)
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Hfr4 & Hpres4 & Hif).
rewrite HOK in Hif. destruct Hif as (Ha04 & Hblk4).
rewrite Rra.
(* ---------------- 0x82ed4 `bnez a0`: a0 = 0, the abort edge is dead ---------------- *)
let d := eval vm_compute in (decode_any (Z_to_bv 32 0x36051263)) in
assert (Hdec : decode_any (Z_to_bv 32 0x36051263) = d) by (vm_compute; reflexivity);
lazymatch d with Some (Branch ?c ?r1 ?r2 ?imm, _) =>
  eapply (s3r_branch_off W3 regs4 1584 mem4 md4 POST 0x36051263 c r1 r2 imm (10%bv : bv 5) (0%bv : bv 5) 0x364) end.
- vm_compute; reflexivity.
- vm_compute; reflexivity.
- exact Hdec.
- apply bv_eq. vm_compute; reflexivity.
- apply bv_eq. vm_compute; reflexivity.
- vm_compute; reflexivity.
- intros Hc. exfalso. rewrite Ha04 in Hc. vm_compute in Hc. discriminate Hc.
- intros _ md5 Hsm.
  replace (BASE + (1584 + 4)) with (BASE + AF_LLVMFuzzerTestOneInput + 0x634) by (unfold AF_LLVMFuzzerTestOneInput; lia).
  apply (HK W3 regs4 mem4 md5).
  (* ---------------- the post ---------------- *)
  assert (Rel : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx - SCENE_STEP_WIN <= a < c_sp1 cx) ->
    (~ (F + 32 <= a < F + 32 + 34) /\ ~ (shadow_addr F + 4 <= a < shadow_addr F + 9)) ->
    aview SEGS (w_H W3) mem4 a = aview SEGS (w_H W3) mem3 a).
  { intros a Ha Hs (Hb & Hw).
    rewrite (Hfr4 a Ha ltac:(rewrite Rsp; exact Hs) ltac:(intros _; unfold BLK_LEN; exact Hb)).
    exact (Rrun a Ha Hw). }
  assert (Pres : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) mem4 a)
  by (intros a Ha; apply Hpres4, Prun, Ha).
  assert (HPR : aregs_preserved regs3 regs4) by (intros r Hr; rewrite (HP4 r Hr); exact (RK r Hr)).
  assert (HOKB : Forall (fun lv => s3_vloc_okb (fst lv) = true) (s3_vats cx bs body again k))
  by (unfold s3_vats; cbv zeta; repeat (apply Forall_cons; [reflexivity|]); apply Forall_nil).
  (* the geometry, as linear facts: lia is given only these (the disjunctive facts are resolved once, below) *)
  assert (BND : 4096 <= F /\ F = 8 * q /\ 512 <= q /\ q + 2048 < 2 ^ 44 /\ shadow_addr F = SHADOW_OFF + q /\
    F + 16384 <= alloc_ceiling /\ 0x7fff7f800000 <= alloc_ceiling /\
    alloc_ceiling + 16624 <= spZ (c_regs cx) /\ spZ (c_regs cx) <= 2 ^ 47 /\
    spZ (c_regs cx) - 255 <= c_sp1 cx <= spZ (c_regs cx) - 224)
  by (clear - HF4096 HF47 HFq HshA HFceil HAC Hceil Hstklo HSTK Hsphi Hstkhi Hsp1b; repeat split; lia).
  (* the frame's bytes are not blk.i's shadow cells, and the frame's shadow is not blk.i *)
  assert (E1 : forall a, F <= a < F + 16384 -> a < shadow_addr F + 4 \/ shadow_addr F + 9 <= a).
  { intros a Ha. clear - BND HFapp Ha. destruct HFapp as (_ & HFapp). unfold SHADOW_OFF in *. lia. }
  assert (E2 : forall a, shadow_addr F <= a < shadow_addr F + 2048 -> a < F + 32 \/ F + 66 <= a).
  { intros a Ha. clear - BND HFapp Ha. destruct HFapp as (_ & HFapp). unfold SHADOW_OFF in *. lia. }
  (* body and again: heap blocks, off the frame and off the shadow band *)
  assert (Eb : forall a, body <= a < body + 8904 ->
    (a < F + 32 \/ F + 66 <= a) /\ (a < shadow_addr F + 4 \/ shadow_addr F + 9 <= a)).
  { intros a Ha. clear - BND Hbsep Hbz Ha. destruct Hbz as (_ & Hbz). unfold SHADOW_OFF in *. lia. }
  assert (Ea : forall a, again <= a < again + 8904 ->
    (a < F + 32 \/ F + 66 <= a) /\ (a < shadow_addr F + 4 \/ shadow_addr F + 9 <= a)).
  { intros a Ha. clear - BND Hasep Haz Ha. destruct Haz as (_ & Haz). unfold SHADOW_OFF in *. lia. }
  pose proof (s3_off_range k ltac:(clear - Hk Hk343; cbn [sg_nturns scene_geom_asan_ubsan] in Hk; lia)) as Hoff.
  set (Q := fun a => ~ (F + 32 <= a < F + 32 + 34) /\ ~ (shadow_addr F + 4 <= a < shadow_addr F + 9)).
  unfold s3_build_post. cbv zeta. fold F.
  split; [reflexivity|].
  split; [rewrite (same_but_materialized_wvb md4 md5 Hsm);
    apply (ajournal_materialize (SK := scene_sink_head) SEGS B LAWS pa_segs_low); exact HJ4|].
  split; [exact HPR|].
  split; [exact Ha04|].
  split; [intros i Hi; exact (Hblk4 i Hi)|].
  split.
  { intros o Ho. fold F. transitivity (aview SEGS (w_H W3) mmS (shadow_addr F + o)).
    - pose proof (E2 (shadow_addr F + o) ltac:(clear - Ho; lia)) as Hx.
      apply Hfr4; [| rewrite Rsp | intros _; unfold BLK_LEN];
      clear - BND Ho Hx; unfold SCENE_STEP_WIN, SCENE_STEP_FRAME, ESTACK, SHADOW_OFF in *; lia.
    - apply Sh; [clear - Ho; lia|]. destruct (Z.eqb_spec o 8) as [He | He]; [clear - Ho He; lia | reflexivity]. }
  split.
  { intros o Ho. fold F. transitivity (aview SEGS (w_H W3) mmS (shadow_addr F + o)).
    - pose proof (E2 (shadow_addr F + o) ltac:(clear - Ho; lia)) as Hx.
      apply Hfr4; [| rewrite Rsp | intros _; unfold BLK_LEN];
      clear - BND Ho Hx; unfold SCENE_STEP_WIN, SCENE_STEP_FRAME, ESTACK, SHADOW_OFF in *; lia.
    - apply Sh; [clear - Ho; lia|]. replace o with 8 by (clear - Ho; lia). reflexivity. }
  split; [exact Rel|].
  split; [exact Pres|].
  split.
  { apply (s3_keep_frame_w2 cx W3 mem3 mem4 (c_sp1 cx - SCENE_STEP_WIN) (c_sp1 cx) Q Hfrm Rel Pres).
    intros a Ha. change (fs_frame_bytes (sg_cid scene_geom_asan_ubsan)) with 16384 in Ha. fold F in Ha.
    pose proof (E1 a ltac:(clear - Ha; lia)) as Hx.
    subst Q. cbv beta. clear - BND Ha Hx. unfold SCENE_STEP_WIN, SCENE_STEP_FRAME, ESTACK, SHADOW_OFF in *. lia. }
  split.
  { apply (s3_keep_saves_w2 cx W3 mem3 mem4 (c_sp1 cx - SCENE_STEP_WIN) (c_sp1 cx) Q Hsav Rel).
    intros a Ha. subst Q. cbv beta. clear - BND Ha.
    unfold SCENE_STEP_WIN, SCENE_STEP_FRAME, ESTACK, SHADOW_OFF in *. lia. }
  split.
  { assert (HBR : Forall (fun t => 0 <= fst (fst t) /\ snd (fst t) <= 0x498 /\ (snd (fst t) <= 4 \/ 9 <= fst (fst t)))
      (sg_sh_bg scene_geom_asan_ubsan))
    by (cbn [sg_sh_bg scene_geom_asan_ubsan]; repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil).
    unfold sc_shbg in Hbg |- *. rewrite Forall_forall in Hbg, HBR |- *. intros t Ht.
    destruct (HBR t Ht) as (Hl & Hh & Hlh).
    apply (s3_keep_shr_w2 cx W3 mem3 mem4 (c_sp1 cx - SCENE_STEP_WIN) (c_sp1 cx) Q _ _ _ (Hbg t Ht) Rel).
    intros a Ha. fold F in Ha. subst Q. cbv beta.
    revert Ha Hl Hh Hlh. generalize (fst (fst t)) as l. generalize (snd (fst t)) as h. intros h l Ha Hl Hh Hlh.
    pose proof (E2 a ltac:(clear - Ha Hl Hh; lia)) as Hx.
    clear - BND Ha Hl Hh Hlh Hx. unfold SCENE_STEP_WIN, SCENE_STEP_FRAME, ESTACK, SHADOW_OFF in *. lia. }
  split.
  { unfold sc_open in Hopb |- *. fold F in Hopb |- *.
    apply (s3r_open_keep (aview SEGS (w_H W3) mem3)); [|exact Hopb].
    intros i Hi. change (sg_blk_n scene_geom_asan_ubsan) with 34 in Hi. change ((34 + 7) / 8) with 5 in Hi.
    change (sg_off_blk scene_geom_asan_ubsan) with 144.
    assert (Hsb : shadow_of_addr SHADOW_OFF (F + 144) = shadow_addr F + 18).
    { unfold shadow_of_addr. destruct BND as (_ & HFq' & _ & _ & HshA' & _). rewrite HshA', HFq'.
      replace (8 * q + 144) with ((q + 18) * 8) by lia. rewrite Z.div_mul by lia. lia. }
    rewrite Hsb. pose proof (E2 (shadow_addr F + 18 + i) ltac:(clear - Hi; lia)) as Hx.
    apply Rel; clear - BND Hi Hx; unfold SCENE_STEP_WIN, SCENE_STEP_FRAME, ESTACK, SHADOW_OFF in *; lia. }
  split.
  { unfold sc_open in Hopm |- *. fold F in Hopm |- *.
    apply (s3r_open_keep (aview SEGS (w_H W3) mem3)); [|exact Hopm].
    intros i Hi. change (sg_mac_n scene_geom_asan_ubsan) with 6 in Hi. change ((6 + 7) / 8) with 1 in Hi.
    change (sg_off_mac scene_geom_asan_ubsan) with 112.
    assert (Hsb : shadow_of_addr SHADOW_OFF (F + 112) = shadow_addr F + 14).
    { unfold shadow_of_addr. destruct BND as (_ & HFq' & _ & _ & HshA' & _). rewrite HshA', HFq'.
      replace (8 * q + 112) with ((q + 14) * 8) by lia. rewrite Z.div_mul by lia. lia. }
    rewrite Hsb. pose proof (E2 (shadow_addr F + 14 + i) ltac:(clear - Hi; lia)) as Hx.
    apply Rel; clear - BND Hi Hx; unfold SCENE_STEP_WIN, SCENE_STEP_FRAME, ESTACK, SHADOW_OFF in *; lia. }
  split.
  { apply (s3_keep_garr8_w2 W3 mem3 mem4 (c_sp1 cx - SCENE_STEP_WIN) (c_sp1 cx) Q body (u8s b) Hgb Rel).
    intros a Ha. unfold u8s in Ha. rewrite length_map, Hlenb in Ha.
    pose proof (Eb a Ha) as Hx. subst Q. cbv beta. clear - BND Ha Hx Hbceil Hb4096.
    unfold SCENE_STEP_WIN, SCENE_STEP_FRAME, ESTACK, SHADOW_OFF in *. lia. }
  split.
  { destruct Hga as (ja & Hjl & Hjg). exists ja. split; [exact Hjl|].
    apply (s3_keep_garr8_w2 W3 mem3 mem4 (c_sp1 cx - SCENE_STEP_WIN) (c_sp1 cx) Q again _ Hjg Rel).
    intros a Ha.
    assert (Hlen : Z.of_nat (length (u8s (firstn (Z.to_nat (scT_off k)) b ++ ja))) = 8904).
    { unfold u8s. rewrite length_map, length_app, length_firstn. cbn [sg_scene_n scene_geom_asan_ubsan] in Hjl.
      clear - Hjl Hlenb Hoff. lia. }
    rewrite Hlen in Ha. pose proof (Ea a Ha) as Hx. subst Q. cbv beta. clear - BND Ha Hx Haceil Ha4096.
    unfold SCENE_STEP_WIN, SCENE_STEP_FRAME, ESTACK, SHADOW_OFF in *. lia. }
  split.
  { apply (s3_keep_garr8_w2 W3 mem3 mem4 (c_sp1 cx - SCENE_STEP_WIN) (c_sp1 cx) Q _ (sc_macb bs) Hgm Rel).
    intros a Ha. change (length (sc_macb bs)) with 6%nat in Ha. change (sg_off_mac scene_geom_asan_ubsan) with 112 in Ha.
    fold F in Ha. pose proof (E1 a ltac:(clear - Ha; lia)) as Hx.
    subst Q. cbv beta. clear - BND Ha Hx. unfold SCENE_STEP_WIN, SCENE_STEP_FRAME, ESTACK, SHADOW_OFF in *. lia. }
  { rewrite Forall_forall in HV3, HOKB |- *. intros lv Hlv.
    apply (s3r_vat_keep (c_sp1 cx) W3 mem3 mem4 regs3 regs4 (fst lv) (snd lv) (HV3 lv Hlv) (HOKB lv Hlv) HPR).
    intros i Hi. apply Rel; clear - BND Hi; unfold SCENE_STEP_WIN, SCENE_STEP_FRAME, ESTACK, SHADOW_OFF in *; lia. }
Qed.

(* ---- The premise bundle of check_step at 0x82f20, proved by this lane's helper and pasted
   verbatim from its scratch file S3Chk_scratch.v (sha256 6abd3aa05c34; internal record)
   lines 157-321 (its 04:29Z hand-over). ---- *)
(* ---- THE PREMISE BUNDLE OF check_step AT 0x82f20.  The call passes a0 = s9 = blk.i = F + 32, a1 = s4 = body,
   a2 = s7 = k (`mv a0,s9` / `mv a2,s7` 0x82f18-0x82f1c; a1 = body from `mv a1,s4` 0x82f04) with sp = sp1 and
   s0 = sp0.  The conclusion is tcheck_step_specX's premise list (lib/AU/P_check_step.v:74-87) at the call state,
   in its order, without the three argument registers: afn_pre (through afn_pre_at, lib/AU/YCbq.v:1806, from the
   journal of the entry; its chain is the entry's chain pushed with LLVMFuzzerTestOneInput's own record
   (sp0, ra0, s0_0) read from the saved slots, or the empty chain when sp0 lies within 16 of the stack top), the
   two stack facts, the frame count, arodata_okP (arodata_ok_journalP, lib/AU/Prog/SceneBase.v:36, from the
   entry's arodata_okS through HWRLO / HWRHI), k's range, blk.i's afobj, body's block, b's length, body's and
   blk.i's bytes, and the two budgets.
   Hypotheses beyond sc_base and the cut, all facts the lane holds INSIDE the turn at the call:
   - Hkn : this is a turn (k < NTURNS);
   - HJ / Hev : the journal from the entry to the call state (lyc, Sc, W, memT, mdc), with at most 6 events;
   - Hin : body is still a live block at the call state;
   - H0 / H2 : blk.i's shadow after the unpoison stores 0x82eac-0x82ec0 (00 00 00 00 02), at memT;
   - HBLK : blk.i's 34 bytes are scene_block b k at memT (reac_ctrl_build_scene_step's post, carried);
   - HKB : memT agrees with the cut's memory over body's 8904 bytes;
   - HSV : the 13 callee-saved words of the entry's caller are still in place at memT (the chain reads two);
   - HR2 / HR3 / HR4 / HR8 : sp, gp, tp and s0 at the call are the cut's;
   - Hret / Hra4 : the return address the jal 0x82f20 writes. ---- *)
Lemma s3_chk_pre : forall (cx : rtcx SEGS) ly3 S3 (W3 : world SEGS) regs3 mem3 md3 bs body again b k
(lyc : alayout) (Sc : astate) (W : world SEGS) (memT : word -> option byte) (mdc : Model) (ev : Z)
(regsT : bvmap 5 word),
sc_base SEGS B ameter_triv WK cx ->
cut_T (SK := scene_sink_head) SEGS B ameter_triv WK scene_geom_asan_ubsan cx
ly3 S3 W3 regs3 mem3 md3 bs body again b k ->
k < sg_nturns scene_geom_asan_ubsan ->
ajournal (SK := scene_sink_head) SEGS B (sw_stk WK) (spZ (c_regs cx)) []
(c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(8, c_fpos cx)] lyc Sc W memT mdc ev ->
ev <= 6 ->
In (body, sg_scene_n scene_geom_asan_ubsan) (ablocks B lyc Sc) ->
(forall j, 4 <= j < 8 ->
aview SEGS (w_H W) memT (shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) + j) = Some 0) ->
aview SEGS (w_H W) memT (shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) + 8) = Some 2 ->
(forall i, 0 <= i < 34 ->
aview SEGS (w_H W) memT (sc_F SEGS scene_geom_asan_ubsan cx + 32 + i)
= Some (bv_unsigned (nth (Z.to_nat i) (scene_block b k) (Z_to_bv 8 0)))) ->
(forall a, body <= a < body + sg_scene_n scene_geom_asan_ubsan ->
aview SEGS (w_H W) memT a = aview SEGS (w_H W3) mem3 a) ->
sc_saves SEGS cx W memT ->
getr regsT 2 = getr regs3 2 -> getr regsT 3 = getr regs3 3 -> getr regsT 4 = getr regs3 4 ->
getr regsT 8 = getr regs3 8 ->
YK0s.ret_ok (getr regsT 1) -> 4096 <= raZ regsT ->
(exists ch, afn_pre SEGS B TCHECK_STEP_STK lyc Sc W regsT memT mdc ch) /\
spZ regsT mod 32 = 0 /\ spZ regsT + 32 <= ly_top lyc /\
Z.of_nat (length (frames Sc)) <= 7 /\
arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) memT) /\
0 <= k <= CS_LAST /\
afobj SEGS B lyc Sc W memT (sc_F SEGS scene_geom_asan_ubsan cx + 32) CS_BLK_LEN /\
In (body, CS_BODY_LEN) (ablocks B lyc Sc) /\
length b = Z.to_nat CS_BODY_LEN /\
(forall i, 0 <= i < CS_BODY_LEN ->
aview SEGS (w_H W) memT (body + i) = Some (bv_unsigned (nth (Z.to_nat i) b (Z_to_bv 8 0)))) /\
(forall i, 0 <= i < CS_BLK_LEN ->
aview SEGS (w_H W) memT (sc_F SEGS scene_geom_asan_ubsan cx + 32 + i)
= Some (bv_unsigned (nth (Z.to_nat i) (scene_block b k) (Z_to_bv 8 0)))) /\
st_nev Sc + EV_CHECK_STEP <= EV_MAX /\ blocks_bytes Sc + LIVE_CHECK_STEP <= LIVE_MAX.
Proof.
intros cx ly3 S3 W3 regs3 mem3 md3 bs body again b k lyc Sc W memT mdc ev regsT
HB HT Hkn HJ Hev Hin H0 H2 HBLK HKB HSV HR2 HR3 HR4 HR8 Hret Hra4.
(* ---------------- the cut ---------------- *)
destruct HT as (Hk & _ & _ & _ & _ & _ & _ & _ & Hlenb & Hgb & _ & _ & _ & _ & _ & _ & _ & (Hsp3 & Hgp & Htp & _) &
_ & _ & Hs0 & _).
cbn [sg_nturns sg_scene_n sgT_sp0 scene_geom_asan_ubsan vat] in Hk, Hkn, Hlenb, Hs0, Hin, HKB.
unfold RV_s0 in Hs0.
(* ---------------- the entry ---------------- *)
destruct HB as ((HPRE & _ & _ & _ & _ & Hfr0 & Hev0 & _ & Hrod0 & _) & Hsp1eq).
destruct HPRE as (_ & _ & Hra40 & _ & _ & _ & _ & Hch0 & _).
(* ---------------- the journal ---------------- *)
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & Hnev & _ & F1 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal16 & Hstkn & Hceil & Hslo & Hshi & H47 & _ & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & HF & _ & _ & Etop & _).
rewrite Hfr0, app_nil_r in Hfrs.
pose proof YM05.alloc_ceiling_lt as Hlt.
pose proof (@YM05.alloc_ceiling_value rc) as Hacv.
assert (Hfb : fs_frame_bytes 8 = 16384) by reflexivity.
assert (FFS : TCHECK_STEP_STK = 8496) by reflexivity.
(* the frame at the call state's layout is the cut's F *)
assert (HFE : frame_addr lyc 8 (c_fpos cx) = sc_F SEGS scene_geom_asan_ubsan cx).
{ unfold sc_F, rt_F, frame_addr. rewrite HF. reflexivity. }
assert (Hinf : In (8, c_fpos cx) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS lyc Sc W memT mdc 8 (c_fpos cx) HAR Hinf) as (Hal & _ & _ & _).
destruct (frames_bounds SEGS B LAWS lyc Sc W memT mdc 8 (c_fpos cx) HAR Hinf) as (HFlo & HFhi & _).
rewrite HFE in Hal, HFlo, HFhi. rewrite Hfb in HFhi.
set (F := sc_F SEGS scene_geom_asan_ubsan cx) in *.
assert (H8 : F mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal; [|lia]. destruct Hal as [q Hq]. exists (4 * q). lia. }
(* ---------------- the registers at the call ---------------- *)
set (sp0 := spZ (c_regs cx)) in *.
assert (HspT : spZ regsT = c_sp1 cx) by (unfold spZ; rewrite HR2; exact Hsp3).
assert (Hsp0r : 0 <= sp0 < 2 ^ 64) by lia.
assert (Hs0T : s0Z regsT = sp0).
{ unfold s0Z. rewrite HR8, Hs0. unfold w64. apply s3e_unsigned64. exact Hsp0r. }
assert (Hsp1b : sp0 - 240 <= c_sp1 cx <= sp0 - 224 /\ c_sp1 cx mod 32 = 0).
{ rewrite Hsp1eq. pose proof (Z.mod_pos_bound (sp0 - 224) 32 ltac:(lia)) as Hm.
  pose proof (Z_div_mod_eq_full (sp0 - 224) 32) as He.
  apply Z.mod_divide in Hal16; [|lia]. destruct Hal16 as [u Hu].
  split; [|rewrite Z.mul_comm, Z_mod_mult; reflexivity].
  assert (Hr : exists m, (sp0 - 224) mod 32 = 16 * m) by (exists (u - 14 - 2 * ((sp0 - 224) / 32)); lia).
  destruct Hr as [m Hmq]. lia. }
assert (Ho16 : (c_sp1 cx - sp0) mod 16 = 0).
{ destruct Hsp1b as (_ & H32). apply Z.mod_divide in H32; [|lia]. apply Z.mod_divide in Hal16; [|lia].
  destruct H32 as [t Ht]. destruct Hal16 as [u Hu]. apply Z.mod_divide; [lia|]. exists (2 * t - u). lia. }
(* ---------------- the conclusion, in tcheck_step_specX's order ---------------- *)
split.
{ (* afn_pre, from the journal *)
  assert (Hch : exists ch, achain lyc (aview SEGS (w_H W) memT) (spZ regsT) (s0Z regsT) ch).
  { rewrite HspT, Hs0T.
    destruct (Z.ltb_spec sp0 (ly_top (c_ly cx) - 16)) as [Hlo16 | Hhi16].
    - exists [(sp0, raZ (c_regs cx), s0Z (c_regs cx))].
      apply (achain_ly_top (c_ly cx) lyc); [exact Etop|].
      apply (achain_push (c_ly cx) (aview SEGS (w_H (c_W cx)) (c_mem cx)) (aview SEGS (w_H W) memT)
        sp0 (s0Z (c_regs cx)) (raZ (c_regs cx)) [] (c_sp1 cx) Hch0).
      + lia.
      + intros a Ha. apply F1; lia.
      + replace (sp0 - 8) with (sp0 - 8 - 8 * 0) by lia. exact (HSV 0 ltac:(lia)).
      + replace (sp0 - 16) with (sp0 - 8 - 8 * 1) by lia. exact (HSV 1 ltac:(lia)).
      + exact Hra40.
      + lia.
      + apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal16; [|lia]. destruct Hal16 as [u Hu].
        exists (2 * u). lia.
      + exact Hlo16.
      + lia.
    - exists []. left. split; [right; left; rewrite Etop; lia | reflexivity]. }
  destruct Hch as (ch & Hch).
  exists ch.
  eapply (afn_pre_at (SK := scene_sink_head) SEGS B (sw_stk WK) sp0 [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
    (c_md cx) [(8, c_fpos cx)] lyc Sc W memT mdc ev regsT TCHECK_STEP_STK (c_sp1 cx - sp0) ch HJ).
  - rewrite HspT. lia.
  - exact Ho16.
  - lia.
  - lia.
  - lia.
  - exact Hret.
  - exact Hra4.
  - rewrite HR3. exact Hgp.
  - rewrite HR4. exact Htp.
  - exact Hch. }
split; [rewrite HspT; exact (proj2 Hsp1b)|].
split; [rewrite HspT, Etop; lia|].
split; [rewrite Hfrs; cbn [length]; lia|].
split.
{ (* arodata_okP, from the entry's arodata_okS *)
  assert (HROD0 : arodata_okP SEGS RLO RHI B (aview SEGS (w_H (c_W cx)) (c_mem cx))).
  { rewrite HWRLO, HWRHI in Hrod0. exact Hrod0. }
  exact (arodata_ok_journalP (SK := scene_sink_head) SEGS RLO RHI pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    HJ HROD0). }
split; [unfold CS_LAST; lia|].
split.
{ (* afobj of blk.i = F + 32 *)
  unfold afobj, CS_BLK_LEN. split; [|split].
  - exists 8, (c_fpos cx). split; [exact Hinf|]. split; [lia|]. rewrite HFE.
    split; [exact H8|]. split; [lia|]. rewrite Hfb. lia.
  - rewrite Z.add_mod by lia. rewrite H8. reflexivity.
  - exact (s3_ra_blki (aview SEGS (w_H W) memT) F H8 H0 H2). }
split; [exact Hin|].
split; [rewrite <- (Nat2Z.id (length b)), Hlenb; reflexivity|].
split.
{ intros i Hi. unfold CS_BODY_LEN in Hi. rewrite HKB by lia.
  apply (s3_bytes_of_garr8 (w_H W3) mem3 body b Hgb). lia. }
split; [unfold CS_BLK_LEN; exact HBLK|].
split.
- unfold EV_CHECK_STEP. lia.
- pose proof (wf_live _ _ _ _ _ (am_wf _ _ _ _ (proj1 HAR))) as Hlive. unfold LIVE_CHECK_STEP. lia.
Qed.

(* ---- The re-assembly of the loop cut after one turn: cut_T at k + 1 (s3_next_T) and cut_TX at the exit
   (s3_next_TX) from what one turn changes.  Proved by this lane's helper
   and pasted
   verbatim. ---- *)

(* =================================================================================================================
   RE-ASSEMBLY OF THE LOOP CUT AFTER ONE TURN (by a Theorem Labs lane with a helper).
   ================================================================================================================= *)

(* one byte read through aview is a one-byte val_mem: copied from lib/AU/Prog/YC88.v:71-84 (le_byte_1_0,
   val_mem1_of_aview), at SEGS. *)
Lemma s3n_le_byte_1_0 : forall v, 0 <= v < 256 -> YO0f.le_byte v 1 0 = v.
Proof.
intros v Hv. unfold YO0f.le_byte. rewrite Z.shiftr_0_r.
change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite (Z.mod_small v 256) by lia. apply Z.mod_small. lia.
Qed.

Lemma s3n_val_mem1_of_aview : forall H m a v,
aview SEGS H m a = Some v -> val_mem SEGS (mrestrict H m) a 1 v /\ 0 <= v < 256.
Proof.
intros H m a v Hv. unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H m) a) as [b|] eqn:Eb; cbn in Hv; [|discriminate]. injection Hv as <-.
pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
split; [|exact Hr]. intros k Hk. destruct k; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r, Eb. f_equal.
rewrite (s3n_le_byte_1_0 _ Hr). symmetry. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* a spilled doubleword moves with the eight bytes it reads *)
Lemma s3n_spill : forall (W W' : world SEGS) (mem mem' : word -> option byte) (a v : Z),
rdword (aview SEGS (w_H W) mem) a = Some v ->
(forall i, 0 <= i < 8 -> aview SEGS (w_H W') mem' (a + i) = aview SEGS (w_H W) mem (a + i)) ->
rdword (aview SEGS (w_H W') mem') a = Some v.
Proof.
intros W W' mem mem' a v Hv HK.
rewrite (rdword_ext (aview SEGS (w_H W) mem)); [exact Hv|]. exact HK.
Qed.

(* a register the turn leaves alone: every callee-saved one except s6, s7, s8, s10 *)
Lemma s3n_keep_reg : forall (regs regs' : bvmap 5 word) (r : bv 5) (z v : Z),
(forall r0, acallee_saved r0 -> r0 <> 22 -> r0 <> 23 -> r0 <> 24 -> r0 <> 26 ->
getr regs' (Z_to_bv 5 r0) = getr regs (Z_to_bv 5 r0)) ->
Z_to_bv 5 z = r -> acallee_saved z -> z <> 22 -> z <> 23 -> z <> 24 -> z <> 26 ->
getr regs r = w64 v -> getr regs' r = w64 v.
Proof.
intros regs regs' r z v HR <- Hz H22 H23 H24 H26 Hv. rewrite (HR z Hz H22 H23 H24 H26). exact Hv.
Qed.

(* block_shadow (sc_open) reads only the shadow cells of its object *)
Lemma s3n_open_keep : forall (rd rd' : Z -> option Z) p n,
(forall i, 0 <= i < (n + 7) / 8 -> rd' (shadow_of_addr SHADOW_OFF p + i) = rd (shadow_of_addr SHADOW_OFF p + i)) ->
block_shadow rd SHADOW_OFF p n -> block_shadow rd' SHADOW_OFF p n.
Proof.
intros rd rd' p n HK (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
intros i Hi. rewrite HK by exact Hi. exact (H3 i Hi).
Qed.

(* s3_garr8_splice with the world of the new state free (check_step may grow it): the memcpy's destination bytes
   at the new (H', m'), the untouched prefix and tail carried from the old (H, m) by aview agreement. *)
Lemma s3n_garr8_splice : forall (H H' : word -> bool) (m m' : word -> option byte) (a : Z) (pre src ja : list byte),
garr8 SEGS (mrestrict H m) a (u8s (pre ++ ja)) ->
(length src <= length ja)%nat ->
garr8 SEGS (mrestrict H' m') (a + Z.of_nat (length pre)) (u8s src) ->
(forall x, a <= x < a + Z.of_nat (length pre) -> aview SEGS H' m' x = aview SEGS H m x) ->
(forall x, a + Z.of_nat (length pre) + Z.of_nat (length src) <=
x < a + Z.of_nat (length pre) + Z.of_nat (length ja) -> aview SEGS H' m' x = aview SEGS H m x) ->
garr8 SEGS (mrestrict H' m') a (u8s (pre ++ src ++ skipn (length src) ja)).
Proof.
intros H H' m m' a pre src ja HG Hle HS Hkpre Hktail.
unfold u8s in HG, HS |- *. rewrite map_app in HG.
destruct (proj1 (garr8_app SEGS (mrestrict H m) a _ _) HG) as (HGp & HGj).
rewrite length_map in HGj.
assert (HJsplit : map (fun x : byte => bv_unsigned x) ja
= map (fun x : byte => bv_unsigned x) (firstn (length src) ja)
++ map (fun x : byte => bv_unsigned x) (skipn (length src) ja)).
{ rewrite <- map_app, firstn_skipn. reflexivity. }
rewrite HJsplit in HGj.
destruct (proj1 (garr8_app SEGS (mrestrict H m) (a + Z.of_nat (length pre)) _ _) HGj) as (_ & HGt).
rewrite length_map, length_firstn, (Nat.min_l _ _ Hle) in HGt.
rewrite !map_app.
apply (proj2 (garr8_app SEGS (mrestrict H' m') a _ _)). split.
- apply (garr8_frame SEGS (mrestrict H m) _ a _ HGp).
  intros x Hx. apply (mbyte_of_aview SEGS). apply Hkpre. rewrite length_map in Hx. exact Hx.
- rewrite length_map.
  apply (proj2 (garr8_app SEGS (mrestrict H' m') (a + Z.of_nat (length pre)) _ _)). split; [exact HS|].
  rewrite length_map.
  apply (garr8_frame SEGS (mrestrict H m) _ _ _ HGt).
  intros x Hx. apply (mbyte_of_aview SEGS). apply Hktail.
  rewrite length_map, length_skipn in Hx. lia.
Qed.

(* The `exists ja` clause of cut_T at k + 1, from the clause at k, the memcpy's bytes (as its post and blk.i's
   contents give them, byte by byte) and aview agreement on the rest of `again`. *)
Lemma s3n_again_next : forall (W3 W' : world SEGS) (mem3 mem' : word -> option byte) (again : Z)
(b ja : list byte) (k : Z),
length b = 8904%nat -> 0 <= k <= 342 -> Z.of_nat (length ja) = 8904 - scT_off k ->
garr8 SEGS (mrestrict (w_H W3) mem3) again (u8s (firstn (Z.to_nat (scT_off k)) b ++ ja)) ->
(forall a, again <= a < again + 8904 -> ~ (again + scT_off k <= a < again + scT_off k + scene_len k) ->
aview SEGS (w_H W') mem' a = aview SEGS (w_H W3) mem3 a) ->
(forall i, 0 <= i < scene_len k ->
aview SEGS (w_H W') mem' (again + scT_off k + i)
= Some (bv_unsigned (nth (Z.to_nat (scT_src k + i)) (scene_block b k) (Z_to_bv 8 0)))) ->
exists ja' : list byte, Z.of_nat (length ja') = 8904 - scT_off (k + 1) /\
garr8 SEGS (mrestrict (w_H W') mem') again (u8s (firstn (Z.to_nat (scT_off (k + 1))) b ++ ja')).
Proof.
intros W3 W' mem3 mem' again b ja k Hb Hk Hja HG HK HC.
pose proof (scT_bnd k Hk) as (Hlo & Hhi & Hlen).
assert (Hsrc : 7 <= scT_src k /\ scT_src k + scene_len k <= 33)
by (unfold scT_src, scene_len; destruct (k =? 0); [lia | destruct (k =? 342); lia]).
pose proof (scT_block_len b k Hb Hk) as Hbl.
destruct (s3_again_step_list b ja k Hb Hk Hja) as (Heq & Hlen').
exists (skipn (Z.to_nat (scene_len k)) ja). split; [exact Hlen'|].
rewrite <- Heq.
set (src := firstn (Z.to_nat (scene_len k)) (skipn (Z.to_nat (scT_src k)) (scene_block b k))).
set (pre := firstn (Z.to_nat (scT_off k)) b).
assert (Hsl : length src = Z.to_nat (scene_len k)).
{ unfold src. rewrite length_firstn, length_skipn, Hbl. lia. }
assert (Hpl : length pre = Z.to_nat (scT_off k)).
{ unfold pre. rewrite length_firstn, Hb. apply Nat.min_l.
  (* 8904%nat is `Nat.of_num_uint 8904` (abstract-large-number), an atom for lia: say it as Z.to_nat *)
  change 8904%nat with (Z.to_nat 8904). lia. }
rewrite <- Hsl.
apply (s3n_garr8_splice (w_H W3) (w_H W') mem3 mem' again pre src ja HG).
- rewrite Hsl. lia.
- rewrite Hpl, Z2Nat.id by lia.
  intros j Hj. unfold u8s in Hj. rewrite length_map, Hsl in Hj.
  assert (Hn : nth j (u8s src) 0 = bv_unsigned (nth j src (Z_to_bv 8 0)))
  by (unfold u8s; exact (map_nth bv_unsigned src (Z_to_bv 8 0) j)).
  assert (Hs : nth j src (Z_to_bv 8 0) = nth (Z.to_nat (scT_src k + Z.of_nat j)) (scene_block b k) (Z_to_bv 8 0)).
  { unfold src. rewrite nth_firstn.
    replace (j <? Z.to_nat (scene_len k))%nat with true by (symmetry; apply Nat.ltb_lt; lia).
    rewrite nth_skipn. f_equal. lia. }
  rewrite Hn, Hs.
  exact (s3n_val_mem1_of_aview (w_H W') mem' (again + scT_off k + Z.of_nat j) _ (HC (Z.of_nat j) ltac:(lia))).
- intros x Hx. rewrite Hpl, Z2Nat.id in Hx by lia. apply HK; lia.
- intros x Hx. rewrite Hpl, Hsl, !Z2Nat.id in Hx by lia. apply HK; lia.
Qed.

Local Ltac s3n_rg HRk z V :=
  apply (s3n_keep_reg _ _ _ z _ HRk);
  [first [reflexivity | apply bv_eq; vm_compute; reflexivity] | unfold acallee_saved; lia | lia | lia | lia | lia | exact V].
Local Ltac s3n_sp KK V := apply (s3n_spill _ _ _ _ _ _ V); intros ? ?; apply KK; lia.

(* ---- THE RE-ASSEMBLY.  The turn's effect, in the forms the turn's run hands over (F = sc_F, sp1 = c_sp1 cx,
   sp0 = spZ (c_regs cx)):
   - the journal from the entry at the new state, ev = 2, and the block list unchanged;
   - registers: every callee-saved register but s6, s7, s8, s10 unchanged (the calls' aregs_preserved and the
     run's own moves); s8 = got + n_k (0x82f0c / 0x82f10), s6 = s8 (`mv s6,s8` 0x82f60), s7 = k + 1 (`addiw`
     0x82f58), a1 = s4 (`mv a1,s4` 0x82f64);
   - the spill [sp1 + 0x40] holds 8904 (0x82f00 on k = 0, the cut's own value after);
   - aview agreement, on each range the cut reads, outside what the turn wrote: the cut's stack frame
     [sp1 + 8, sp0) outside [sp1 + 0x40, +8); the fake frame outside blk.i [F + 32, +34); the frame's shadow
     outside blk.i's five cells [sh F + 4, sh F + 9); all of body; again outside the memcpy destination
     [again + got, +n_k); the read-only bytes arodata_okS reads;
   - what the turn wrote: blk.i's five shadow cells are 0xf8 again (0x82f48-0x82f5c), and the memcpy destination
     holds blk.i[scT_src k ..], byte by byte. ---- *)
Lemma s3_next_T : forall MT (cx : rtcx SEGS) ly3 S3 (W3 : world SEGS) regs3 mem3 md3 bs body again b k
(ly' : alayout) (S' : astate) (W' : world SEGS) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
sc_base SEGS B MT WK cx ->
cut_T (SK := scene_sink_head) SEGS B MT WK scene_geom_asan_ubsan cx ly3 S3 W3 regs3 mem3 md3 bs body again b k ->
k < sg_nturns scene_geom_asan_ubsan ->
(* the journal and the heap *)
sc_j (SK := scene_sink_head) SEGS B MT WK scene_geom_asan_ubsan cx ly' S' W' mem' md' 2 ->
ablocks B ly' S' = ablocks B ly3 S3 ->
(* registers *)
(forall r, acallee_saved r -> r <> 22 -> r <> 23 -> r <> 24 -> r <> 26 ->
getr regs' (Z_to_bv 5 r) = getr regs3 (Z_to_bv 5 r)) ->
getr regs' RV_s8 = w64 (scT_off k + scene_len k) ->
getr regs' RV_s6 = getr regs' RV_s8 ->
getr regs' RV_s7 = w64 (k + 1) ->
getr regs' RV_a1 = getr regs' RV_s4 ->
(* the one spill the turn writes *)
rdword (aview SEGS (w_H W') mem') (c_sp1 cx + 0x40) = Some 8904 ->
(* memory the cut reads, outside what the turn wrote *)
(forall a, c_sp1 cx + 8 <= a < spZ (c_regs cx) -> ~ (c_sp1 cx + 0x40 <= a < c_sp1 cx + 0x48) ->
aview SEGS (w_H W') mem' a = aview SEGS (w_H W3) mem3 a) ->
(forall a, sc_F SEGS scene_geom_asan_ubsan cx <= a < sc_F SEGS scene_geom_asan_ubsan cx + 16384 ->
~ (sc_F SEGS scene_geom_asan_ubsan cx + 32 <= a < sc_F SEGS scene_geom_asan_ubsan cx + 32 + 34) ->
aview SEGS (w_H W') mem' a = aview SEGS (w_H W3) mem3 a) ->
(forall a, shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) <= a <
shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) + 2048 ->
~ (shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) + 4 <= a < shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) + 9) ->
aview SEGS (w_H W') mem' a = aview SEGS (w_H W3) mem3 a) ->
(forall a, body <= a < body + 8904 -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W3) mem3 a) ->
(forall a, again <= a < again + 8904 -> ~ (again + scT_off k <= a < again + scT_off k + scene_len k) ->
aview SEGS (w_H W') mem' a = aview SEGS (w_H W3) mem3 a) ->
(forall a, in_roP SEGS (sw_rlo WK) (sw_rhi WK) a ->
~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
aview SEGS (w_H W') mem' a = aview SEGS (w_H W3) mem3 a) ->
(* what the turn wrote *)
sc_shr SEGS scene_geom_asan_ubsan cx W' mem' 4 9 0xf8 ->
(forall i, 0 <= i < scene_len k ->
aview SEGS (w_H W') mem' (again + scT_off k + i)
= Some (bv_unsigned (nth (Z.to_nat (scT_src k + i)) (scene_block b k) (Z_to_bv 8 0)))) ->
cut_T (SK := scene_sink_head) SEGS B MT WK scene_geom_asan_ubsan cx ly' S' W' regs' mem' md' bs body again b (k + 1).
Proof.
intros MT cx ly3 S3 W3 regs3 mem3 md3 bs body again b k ly' S' W' regs' mem' md'
HB HT Hk343 HJ' Hab' HRk Hs8 Hs6 Hs7 Ha1 Hdecl KK KF KS KB KA KR Hsh' Hcpy.
pose proof HT as (Hk & Hwh & _ & Hab & Hbb & Hokb & Hoka & Hdis & Hlenb & Hgb & Hga & Hfrm & Hsav & Hbg &
_ & Hopb & Hopm & Himg & Hin & Hgm & V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & _ &
_ & _ & V16 & _ & Vna & V17 & V18 & V19 & _ & V20).
cbn [sg_nturns sg_scene_n scene_geom_asan_ubsan] in Hk, Hk343, Hab, Hbb, Hokb, Hoka, Hdis, Hlenb, Hga.
cbn [sgT_sp0 sgT_sp1 sgT_Fsp sgT_shF sgT_blki sgT_srcA sgT_srcB sgT_mac sgT_shexp sgT_body sgT_again sgT_nprime
sgT_n1 sgT_nagain sgT_expect sgT_Fb sgT_nn sgT_f8 sg_off_blki sg_off_mac sg_off_expect sg_scene_n
scene_geom_asan_ubsan vat] in V1, V2, V3, V4, V5, V6, V7, V8, V9, V10, V11, V12, V16, Vna, V17, V18, V19, V20.
destruct HB as (_ & Hsp1eq).
assert (Hsp1b : c_sp1 cx <= spZ (c_regs cx) - 224).
{ rewrite Hsp1eq. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 224) 32 ltac:(lia)) as Hm.
  pose proof (Z_div_mod_eq_full (spZ (c_regs cx) - 224) 32) as He. lia. }
clear Hsp1eq.
assert (Hb : length b = 8904%nat) by (change 8904%nat with (Z.to_nat 8904); lia).
(* the new journal's frame: the entry's, at the new layout *)
pose proof HJ' as (HJj & Hfr' & _).
pose proof HJj as (HAR' & Hly' & _).
assert (HFa' : frame_addr ly' (sg_cid scene_geom_asan_ubsan) (c_fpos cx) = sc_F SEGS scene_geom_asan_ubsan cx).
{ destruct Hly' as (_ & _ & _ & _ & _ & E & _). unfold sc_F, rt_F, frame_addr. rewrite E. reflexivity. }
assert (Hin' : In (sg_cid scene_geom_asan_ubsan, c_fpos cx) (frames S')) by (rewrite Hfr'; left; reflexivity).
assert (Hfs : fs_frame_bytes (sg_cid scene_geom_asan_ubsan) = 16384) by reflexivity.
unfold cut_T.
cbn [sg_nturns sg_scene_n sg_sh_blki_lo sg_sh_blki_hi sg_off_blk sg_blk_n sg_off_mac sg_mac_n sg_off_blki
sg_off_expect sgT_sp0 sgT_sp1 sgT_Fsp sgT_shF sgT_blki sgT_srcA sgT_srcB sgT_mac sgT_shexp sgT_body sgT_again
sgT_nprime sgT_got sgT_k sgT_decl sgT_n1 sgT_extra sgT_nagain sgT_expect sgT_Fb sgT_nn sgT_body2 sgT_f8
scene_geom_asan_ubsan vat].
split; [lia|].
split; [exact Hwh|].
split; [exact HJ'|].
split; [rewrite Hab'; exact Hab|].
split.
{ rewrite (blocks_bytes_bsum B ly' S'), Hab', <- (blocks_bytes_bsum B ly3 S3). exact Hbb. }
split; [exact Hokb|].
split; [exact Hoka|].
split; [exact Hdis|].
split; [exact Hlenb|].
split.
{ apply (s3_keep_garr8_pt W3 W' mem3 mem' body (u8s b) Hgb).
  intros a Ha. unfold u8s in Ha. rewrite length_map in Ha. apply KB. lia. }
split.
{ destruct Hga as (ja & Hja & Hgja).
  exact (s3n_again_next W3 W' mem3 mem' again b ja k Hb ltac:(lia) Hja Hgja KA Hcpy). }
split.
{ (* sc_frame: the flag word by agreement, the presence from AR at the new state *)
  destruct (al_frames _ _ LAWS ly' S' W' mem' md' _ _ HAR' Hin') as (_ & _ & Hpb & Hpsh).
  rewrite HFa' in Hpb, Hpsh.
  apply (s3_keep_frame_pt cx W3 W' mem3 mem' Hfrm).
  - intros a Ha. rewrite Hfs in Ha. apply KF; lia.
  - intros a [Ha | Ha] _; [exact (proj1 (Hpb a Ha))|].
    revert Hpsh Ha. generalize (fs_frame_bytes (sg_cid scene_geom_asan_ubsan) / 8) as q.
    generalize (shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx)) as s. intros s q Hpsh Ha.
    specialize (Hpsh (a - s) ltac:(lia)). replace (s + (a - s)) with a in Hpsh by lia. exact (proj1 Hpsh). }
split.
{ apply (s3_keep_saves_pt cx W3 W' mem3 mem' Hsav). intros a Ha. apply KK; lia. }
split.
{ (* sc_shbg: every background cell lies in the frame's shadow, outside blk.i's five cells *)
  unfold sc_shbg in Hbg |- *.
  assert (Hbnd : Forall (fun t : Z * Z * Z => 0 <= fst (fst t) /\ snd (fst t) <= 2048 /\
    (snd (fst t) <= 4 \/ 9 <= fst (fst t))) (sg_sh_bg scene_geom_asan_ubsan)).
  { cbn [sg_sh_bg scene_geom_asan_ubsan]. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
  apply Forall_forall. intros t Ht.
  pose proof (proj1 (Forall_forall _ _) Hbg t Ht) as Ht1.
  destruct (proj1 (Forall_forall _ _) Hbnd t Ht) as (Hl & Hh & Hout).
  apply (s3_keep_shr_pt cx W3 W' mem3 mem' _ _ _ Ht1).
  intros a Ha. apply KS; lia. }
split; [exact Hsh'|].
split.
{ unfold sc_open in Hopb |- *. cbn [sg_off_blk sg_blk_n scene_geom_asan_ubsan] in Hopb.
  apply (s3n_open_keep (aview SEGS (w_H W3) mem3)); [|exact Hopb].
  intros i Hi. change ((34 + 7) / 8) with 5 in Hi.
  assert (E : shadow_of_addr SHADOW_OFF (sc_F SEGS scene_geom_asan_ubsan cx + 144)
    = shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) + 18).
  { unfold shadow_of_addr, shadow_addr.
    replace (sc_F SEGS scene_geom_asan_ubsan cx + 144) with (sc_F SEGS scene_geom_asan_ubsan cx + 18 * 8) by ring.
    rewrite Z.div_add by lia. ring. }
  rewrite E. apply KS; lia. }
split.
{ unfold sc_open in Hopm |- *. cbn [sg_off_mac sg_mac_n scene_geom_asan_ubsan] in Hopm.
  apply (s3n_open_keep (aview SEGS (w_H W3) mem3)); [|exact Hopm].
  intros i Hi. change ((6 + 7) / 8) with 1 in Hi.
  assert (E : shadow_of_addr SHADOW_OFF (sc_F SEGS scene_geom_asan_ubsan cx + 112)
    = shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) + 14).
  { unfold shadow_of_addr, shadow_addr.
    replace (sc_F SEGS scene_geom_asan_ubsan cx + 112) with (sc_F SEGS scene_geom_asan_ubsan cx + 14 * 8) by ring.
    rewrite Z.div_add by lia. ring. }
  rewrite E. apply KS; lia. }
split.
{ destruct Himg as (Hsp & Hgp & Htp & Hro).
  assert (R2 : getr regs' 2%bv = getr regs3 2%bv).
  { replace (2%bv : bv 5) with (Z_to_bv 5 2) by (apply bv_eq; reflexivity).
    exact (HRk 2 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
  split; [unfold spZ in Hsp |- *; rewrite R2; exact Hsp|].
  split; [apply (s3n_keep_reg _ _ _ 3 _ HRk);
    [first [reflexivity | apply bv_eq; vm_compute; reflexivity] | unfold acallee_saved; lia | lia | lia | lia | lia | exact Hgp]|].
  split; [apply (s3n_keep_reg _ _ _ 4 _ HRk);
    [first [reflexivity | apply bv_eq; vm_compute; reflexivity] | unfold acallee_saved; lia | lia | lia | lia | lia | exact Htp]|].
  intros a Hra Ho He. rewrite (KR a Hra Ho He). exact (Hro a Hra Ho He). }
split; [exact Hin|].
split.
{ apply (s3_keep_garr8_pt W3 W' mem3 mem' _ (sc_macb bs) Hgm).
  intros a Ha. assert (Hl6 : Z.of_nat (length (sc_macb bs)) = 6) by reflexivity.
  rewrite Hl6 in Ha. cbn [sg_off_mac scene_geom_asan_ubsan] in Ha. apply KF; lia. }
(* the located values *)
split; [s3n_rg HRk 8 V1|].
split; [s3n_rg HRk 9 V2|].
split; [s3n_sp KK V3|].
split; [s3n_rg HRk 19 V4|].
split; [s3n_rg HRk 25 V5|].
split; [s3n_sp KK V6|].
split; [s3n_rg HRk 18 V7|].
split; [s3n_sp KK V8|].
split; [s3n_sp KK V9|].
split; [s3n_rg HRk 20 V10|].
split; [s3n_sp KK V11|].
split; [s3n_sp KK V12|].
split; [rewrite Hs6, Hs8, (scT_off_step k ltac:(lia)); reflexivity|].
split; [exact Hs7|].
split; [rewrite (s3_decl_next k ltac:(lia)); exact Hdecl|].
split; [s3n_rg HRk 27 V16|].
split; [apply Forall_nil|].
split; [s3n_sp KK Vna|].
split; [s3n_sp KK V17|].
split; [s3n_sp KK V18|].
split; [s3n_sp KK V19|].
split; [rewrite Ha1; s3n_rg HRk 20 V10|].
s3n_rg HRk 21 V20.
Qed.

(* At the last turn (k + 1 = NTURNS) the head cut is the exit cut: got = scT_off 343 = 8904 in s6 and in s8. *)
Lemma s3_next_TX : forall MT (cx : rtcx SEGS) bs body again b k
(ly' : alayout) (S' : astate) (W' : world SEGS) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
cut_T (SK := scene_sink_head) SEGS B MT WK scene_geom_asan_ubsan cx ly' S' W' regs' mem' md' bs body again b (k + 1) ->
k + 1 = sg_nturns scene_geom_asan_ubsan ->
getr regs' RV_s8 = w64 (scT_off k + scene_len k) ->
getr regs' RV_s6 = getr regs' RV_s8 ->
cut_TX (SK := scene_sink_head) SEGS B MT WK scene_geom_asan_ubsan cx ly' S' W' regs' mem' md' bs body again b.
Proof.
intros MT cx bs body again b k ly' S' W' regs' mem' md' HT HX Hs8 Hs6.
cbn [sg_nturns scene_geom_asan_ubsan] in HX.
assert (Hgot : scT_off k + scene_len k = 8904).
{ rewrite <- (scT_off_step k ltac:(lia)), HX. exact scT_off_343. }
unfold cut_TX. cbn [sg_nturns sg_scene_n sgT_got sgTX_got2 scene_geom_asan_ubsan vat].
rewrite <- HX. split; [exact HT|].
split; [rewrite Hs6, Hs8, Hgot; reflexivity | rewrite Hs8, Hgot; reflexivity].
Qed.

(* ---- The trailer facts at the cut, for s3_run_build's four TAIL_TRAILER premises.  s2u_div8_add, s2u_ra_part,
   s2u_const1, s2u_zs_byte, s2u_in_ro and s2u_tt are a Theorem Labs lane's text for the S2 lane, copied verbatim from
   729b9b9d254, lib/AU/P_LLVMFuzzerTestOneInput_S2.v:65-87 and :239-307 (that lane is
   proved: seg_S2_stmt).  s3_tt_at_cut, below them, is this lane's: it takes the AR and arodata_okP of the cut's
   state from the journal and adds the trailer / blk.i disjointness from frm_off_imgP. ---- *)
Lemma s2u_div8_add : forall x c, x mod 8 = 0 -> (x + 8 * c) / 8 = x / 8 + c.
Proof.
intros x c Hx. rewrite (Z.div_mod x 8) at 1 by lia. rewrite Hx, Z.add_0_r.
replace (8 * (x / 8) + 8 * c) with ((x / 8 + c) * 8) by lia. apply Z.div_mul. lia.
Qed.
Lemma s2u_ra_part : forall (rd : reader) a q r, a mod 8 = 0 -> 0 <= q -> 0 < r < 8 ->
(forall i, 0 <= i < q -> rd (SHADOW_OFF + a / 8 + i) = Some 0) -> rd (SHADOW_OFF + a / 8 + q) = Some r ->
range_addressable rd SHADOW_OFF a (8 * q + r).
Proof.
intros rd a q r Ha Hq Hr H0 Hl x Hx. unfold shadow_of_addr.
assert (Ex : x / 8 = a / 8 + (x - a) / 8).
{ replace x with (a + (x - a)) at 1 by lia. rewrite (Z.div_mod a 8) at 1 by lia. rewrite Ha, Z.add_0_r.
  replace (8 * (a / 8) + (x - a)) with ((x - a) + (a / 8) * 8) by lia. rewrite Z.div_add by lia. lia. }
assert (Hd : 0 <= (x - a) / 8 < q + 1) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite Ex, Z.add_assoc.
destruct (Z.eq_dec ((x - a) / 8) q) as [Eq|Nq].
- rewrite Eq. exists r. split; [exact Hl|]. right.
  assert (Hm : x mod 8 = (x - a) mod 8).
  { rewrite (Z.div_mod a 8) at 1 by lia. rewrite Ha, Z.add_0_r.
    replace (x - 8 * (a / 8)) with (x + (- (a / 8)) * 8) by lia. rewrite Z.mod_add by lia. reflexivity. }
  pose proof (Z.div_mod (x - a) 8 ltac:(lia)) as Hdm. rewrite Eq in Hdm. lia.
- exists 0. split; [apply H0; lia | left; reflexivity].
Qed.
Lemma s2u_const1 : forall ly S (W : world SEGS) mem md a v, AR SEGS B ly S W mem md ->
In (z1 (ANum a) v) (as_const B ly) -> aview SEGS (w_H W) mem a = Some (le_byte v 1 0).
Proof.
intros ly S W mem md a v HAR Hin.
pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ (proj1 HAR)) _ Hin) as X.
unfold cell_holds in X. cbn [c_at YG0f.c_val c_w aeval z1 c1] in X. specialize (X 0%nat ltac:(lia)). rewrite Z.add_0_r in X. exact X.
Qed.
Lemma s2u_zs_byte : forall ly S (W : world SEGS) mem md a n x, AR SEGS B ly S W mem md ->
in_zs B a n -> a <= x < a + n -> aview SEGS (w_H W) mem (SHADOW_OFF + x / 8) = Some 0.
Proof.
intros ly S W mem md a n x HAR (q & m & Hin & H1 & H2) Hx.
destruct (zs_range SEGS B q m Hin ly S W mem md HAR) as (Hq0 & Hm0 & Hq8 & Hm8 & Hhi).
pose proof (zs_zero SEGS B LAWS q m Hin ly S W mem md HAR) as Hz.
assert (Ex : x / 8 = q / 8 + (x - q) / 8).
{ replace x with ((x - q) + (q / 8) * 8) at 1 by (pose proof (Z.div_mod q 8 ltac:(lia)); lia). rewrite Z.div_add by lia. lia. }
unfold zero_shadow, shadow_of_addr in Hz.
rewrite Ex, Z.add_assoc. apply Hz. split; [apply Z.div_pos; lia|].
apply Z.div_lt_upper_bound; [lia|]. pose proof (Z.div_mod m 8 ltac:(lia)). lia.
Qed.
Lemma s2u_in_ro : forall a, existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? a)
  && (a <? Z.of_N (seg_base s) + Z.of_N (seg_size s))) SEGS = true -> in_roP SEGS pa_relro_lo pa_relro_hi a.
Proof.
intros a H. apply existsb_exists in H as (s & Hs & Hb). left. exists s. split; [exact Hs|].
apply andb_prop in Hb as (Hb & H3). apply andb_prop in Hb as (H1 & H2).
apply Bool.negb_true_iff in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3. auto.
Qed.
Lemma s2u_tt : forall ly S (W' : world SEGS) (m : word -> option byte) md, AR SEGS B ly S W' m md ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W') m) ->
  (forall i, 0 <= i < 12 ->
     aview SEGS (w_H W') m (A_TT + i) = Some (bv_unsigned (nth (Z.to_nat i) scene_trailer (Z_to_bv 8 0)))) /\
  range_addressable (aview SEGS (w_H W') m) SHADOW_OFF A_TT 12 /\
  shadow_hull_vis (aview SEGS (w_H W') m) A_TT 12.
Proof.
intros ly S W' m md HAR HRD.
assert (EA : A_TT = 0x20e20) by (vm_compute; reflexivity). rewrite EA.
pose proof (HB_C_TT ly) as HC. cbn [map seq] in HC.
pose proof (Forall_inv HC) as C0. pose proof (Forall_inv (Forall_inv_tail HC)) as C1.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HC))) as C2. cbv beta in C0, C1, C2.
change (shadow_addr (0x20e20 + 8)) with 2147467717 in C0, C1, C2.
change (12 mod 8) with 4 in C0. change (2147467717 + 1 + Z.of_nat 0) with 2147467718 in C1.
change (2147467717 + 1 + Z.of_nat 1) with 2147467719 in C2.
pose proof HB_Z_TT as HZ. change (0x20e20 - 0x20) with 0x20e00 in HZ.
change (0x20 + (12 - 12 mod 8)) with 40 in HZ.
split; [|split].
- intros i Hi. destruct (HRO_TT i Hi) as (Ho & He).
  assert (Hro : in_roP SEGS pa_relro_lo pa_relro_hi (0x20e20 + i)).
  { apply s2u_in_ro.
    assert (Hi' : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11) by lia.
    destruct Hi' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]];
    vm_compute; reflexivity. }
  rewrite (HRD _ Hro Ho He).
  assert (Hi' : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11) by lia.
  destruct Hi' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]];
  vm_compute; reflexivity.
- change 12 with (8 * 1 + 4). apply s2u_ra_part; [reflexivity | lia | lia | |].
  + intros i Hi. replace i with 0 by lia. rewrite Z.add_0_r.
    exact (s2u_zs_byte ly S W' m md 0x20e00 40 0x20e20 HAR HZ ltac:(lia)).
  + change (SHADOW_OFF + 0x20e20 / 8 + 1) with 2147467717. rewrite (s2u_const1 ly S W' m md _ _ HAR C0). reflexivity.
- intros s Hs. change (shadow_addr 0x20e20 / 8 * 8) with 2147467712 in Hs.
  change (shadow_addr (0x20e20 + 12 - 1) / 8 * 8 + 8) with 2147467720 in Hs.
  assert (Hc : 2147467712 <= s < 2147467717 \/ s = 2147467717 \/ s = 2147467718 \/ s = 2147467719) by lia.
  destruct Hc as [Hc | [-> | [-> | ->]]].
  + replace s with (SHADOW_OFF + (0x20e00 + 8 * (s - 2147467712)) / 8).
    * rewrite (s2u_zs_byte ly S W' m md 0x20e00 40 _ HAR HZ); [discriminate | lia].
    * rewrite s2u_div8_add by reflexivity. unfold SHADOW_OFF. change (0x20e00 / 8) with 16832. lia.
  + rewrite (s2u_const1 ly S W' m md _ _ HAR C0). discriminate.
  + rewrite (s2u_const1 ly S W' m md _ _ HAR C1). discriminate.
  + rewrite (s2u_const1 ly S W' m md _ _ HAR C2). discriminate.
Qed.

Lemma s3_tt_at_cut : forall (cx : rtcx SEGS) ly3 S3 (W3 : world SEGS) regs3 mem3 md3 bs body again b k,
sc_base SEGS B ameter_triv WK cx ->
cut_T (SK := scene_sink_head) SEGS B ameter_triv WK scene_geom_asan_ubsan cx
ly3 S3 W3 regs3 mem3 md3 bs body again b k ->
(forall i, 0 <= i < TT_LEN ->
aview SEGS (w_H W3) mem3 (ATT + i) = Some (bv_unsigned (nth (Z.to_nat i) scene_trailer (Z_to_bv 8 0)))) /\
range_addressable (aview SEGS (w_H W3) mem3) SHADOW_OFF ATT TT_LEN /\
shadow_hull_vis (aview SEGS (w_H W3) mem3) ATT TT_LEN /\
(ATT + TT_LEN <= sc_F SEGS scene_geom_asan_ubsan cx + sg_off_blki scene_geom_asan_ubsan \/
sc_F SEGS scene_geom_asan_ubsan cx + sg_off_blki scene_geom_asan_ubsan + BLK_LEN <= ATT).
Proof.
intros cx ly3 S3 W3 regs3 mem3 md3 bs body again b k HB HT.
pose proof HT as (_ & _ & Hj & _). destruct Hj as (HJ & Hfrs & _).
cbn [sg_cid scene_geom_asan_ubsan] in HJ, Hfrs.
pose proof (proj1 HJ) as HAR.
pose proof HB as ((_ & _ & _ & _ & _ & _ & _ & _ & Hrod0 & _) & _).
assert (HROD0 : arodata_okP SEGS RLO RHI B (aview SEGS (w_H (c_W cx)) (c_mem cx))).
{ rewrite HWRLO, HWRHI in Hrod0. exact Hrod0. }
pose proof (arodata_ok_journalP (SK := scene_sink_head) SEGS RLO RHI pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  HJ HROD0) as HROD.
destruct (s2u_tt ly3 S3 W3 mem3 md3 HAR HROD) as (H1 & H2 & H3).
unfold TT_LEN. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
assert (Hin : In (8, c_fpos cx) (frames S3)) by (rewrite Hfrs; left; reflexivity).
pose proof (frm_off_imgP B ly3 S3 W3 mem3 md3 8 (c_fpos cx) HAR Hin) as Hoff.
rewrite (s3_layout_eq cx ly3 S3 W3 mem3 md3 2 HB HJ 8 (c_fpos cx)) in Hoff.
assert (EA : ATT = 0x20e20) by (vm_compute; reflexivity). rewrite EA.
assert (Hfb : fs_frame_bytes 8 = 16384) by (vm_compute; reflexivity). rewrite Hfb in Hoff.
unfold off_img in Hoff. unfold sc_F, rt_F. cbn [sg_cid sg_off_blki scene_geom_asan_ubsan]. unfold BLK_LEN.
lia.
Qed.

(* ---- The middle of the turn, first half: s3_mem_mid / s3_check_post (the state at check_step's return
   0x82f24) and the check_step call step s3m_call through TCHECKX with s3_chk_pre.  By a helper,
   pasted verbatim on its 05:04Z hand-over from S3Mid_scratch.v (sha256 6c11e22949d3; internal record)
   lines 2157-2335. ---- *)
(* ================================================================================================================
   S3MID -- the middle of the turn, 0x82ed8 .. 0x82f24.
   ================================================================================================================ *)
#[local] Notation ACS := (A_check_step (PI := PI_scene)).

(* ---- What the middle of the turn hands on, about memory: blk.i holds the turn's block with its shadow open, the
   spill [sp1 + 0x40] holds 8904, and every range the loop cut reads agrees with the cut's state outside what the
   turn wrote (the forms of s3_next_T's premises KK KF KS KB KA KR; `again` is not yet written). ---- *)
Definition s3_mem_mid (cx : rtcx SEGS) (W3 : world SEGS) (mem3 : word -> option byte) (body again : Z)
(b : list byte) (k : Z) (W : world SEGS) (mem : word -> option byte) : Prop :=
let F := sc_F SEGS scene_geom_asan_ubsan cx in
(forall i, 0 <= i < 34 ->
aview SEGS (w_H W) mem (F + 32 + i) = Some (bv_unsigned (nth (Z.to_nat i) (scene_block b k) (Z_to_bv 8 0)))) /\
(forall o, 4 <= o < 8 -> aview SEGS (w_H W) mem (shadow_addr F + o) = Some 0) /\
aview SEGS (w_H W) mem (shadow_addr F + 8) = Some 2 /\
rdword (aview SEGS (w_H W) mem) (c_sp1 cx + 0x40) = Some 8904 /\
(forall a, c_sp1 cx + 8 <= a < spZ (c_regs cx) -> ~ (c_sp1 cx + 0x40 <= a < c_sp1 cx + 0x48) ->
aview SEGS (w_H W) mem a = aview SEGS (w_H W3) mem3 a) /\
(forall a, F <= a < F + 16384 -> ~ (F + 32 <= a < F + 32 + 34) ->
aview SEGS (w_H W) mem a = aview SEGS (w_H W3) mem3 a) /\
(forall a, shadow_addr F <= a < shadow_addr F + 2048 -> ~ (shadow_addr F + 4 <= a < shadow_addr F + 9) ->
aview SEGS (w_H W) mem a = aview SEGS (w_H W3) mem3 a) /\
(forall a, body <= a < body + 8904 -> aview SEGS (w_H W) mem a = aview SEGS (w_H W3) mem3 a) /\
(forall a, again <= a < again + 8904 -> aview SEGS (w_H W) mem a = aview SEGS (w_H W3) mem3 a) /\
(forall a, in_roP SEGS (sw_rlo WK) (sw_rhi WK) a ->
~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
aview SEGS (w_H W) mem a = aview SEGS (w_H W3) mem3 a).

(* ---- THE POST of the middle of the turn, at check_step's return 0x82f24 (BASE + AF_LLVMFuzzerTestOneInput +
   0x680): the journal of the cut at the new state (check_step emits no event, EV_CHECK_STEP = 0), the heap blocks
   unchanged, every callee-saved register but s8 and s10 the cut's, s8 = got + n_k and s10 = n_k, and the memory
   facts above.  a1 = body does NOT survive the call (a1 is caller-saved); s4 = body does. ---- *)
Definition s3_check_post (cx : rtcx SEGS) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (regs3 : bvmap 5 word)
(mem3 : word -> option byte) (bs : Z -> Z) (body again : Z) (b : list byte) (k : Z)
(W5 : world SEGS) (regs5 : bvmap 5 word) (mem5 : word -> option byte) (md5 : Model) : Prop :=
exists ly5 S5,
sc_j (SK := scene_sink_head) SEGS B ameter_triv WK scene_geom_asan_ubsan cx ly5 S5 W5 mem5 md5 2 /\
ablocks B ly5 S5 = ablocks B ly3 S3 /\
(forall r, acallee_saved r -> r <> 24 -> r <> 26 -> getr regs5 (Z_to_bv 5 r) = getr regs3 (Z_to_bv 5 r)) /\
getr regs5 RV_s8 = w64 (scT_off k + scene_len k) /\ getr regs5 RV_s10 = w64 (scene_len k) /\
s3_mem_mid cx W3 mem3 body again b k W5 mem5.

(* ---- s3_mem_mid across a callee's journal (FP = [], own = [], called with sp = sp1): the callee keeps the
   caller's frame and its shadow, the two heap blocks, everything at or above its sp, and the read-only bytes. ---- *)
Lemma s3m_mid_j : forall (cx : rtcx SEGS) (W3 : world SEGS) mem3 body again b k
STK1 ly S (W : world SEGS) mem md ly' S' (W' : world SEGS) mem' md' k1,
ajournal (SK := scene_sink_head) SEGS B STK1 (c_sp1 cx) [] ly S W mem md [] ly' S' W' mem' md' k1 ->
In (8, c_fpos cx) (frames S) -> frame_addr ly 8 (c_fpos cx) = sc_F SEGS scene_geom_asan_ubsan cx ->
In (body, 8904) (ablocks B ly S) -> In (body, 8904) (ablocks B ly' S') ->
In (again, 8904) (ablocks B ly S) -> In (again, 8904) (ablocks B ly' S') ->
alloc_ceiling <= c_sp1 cx -> c_sp1 cx + 0x60 <= spZ (c_regs cx) <= 2 ^ 47 ->
s3_mem_mid cx W3 mem3 body again b k W mem -> s3_mem_mid cx W3 mem3 body again b k W' mem'.
Proof.
intros cx W3 mem3 body again b k STK1 ly S W mem md ly' S' W' mem' md' k1 HJ Hin HFa Hb Hb' Ha Ha' Hce Hsp
(M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & Hhigh & Hblk & Hro & Hfr & _).
assert (Hfb : fs_frame_bytes 8 = 16384) by reflexivity.
set (F := sc_F SEGS scene_geom_asan_ubsan cx) in *.
assert (KH : forall a, c_sp1 cx <= a < 2 ^ 64 -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a)
by (intros a Ha0; apply Hhigh; lia).
assert (KF : forall a, F <= a < F + 16384 -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a).
{ intros a Ha0. apply (Hfr _ _ a Hin); [|apply inFP_nil]. left. unfold in_zr, frame_rng. cbn [fst snd].
  rewrite HFa, Hfb. lia. }
assert (KS : forall a, shadow_addr F <= a < shadow_addr F + 2048 -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a).
{ intros a Ha0. apply (Hfr _ _ a Hin); [|apply inFP_nil]. right. unfold in_zr. cbn [fst snd].
  rewrite HFa, Hfb. change (16384 / 8) with 2048. lia. }
assert (KB : forall p, In (p, 8904) (ablocks B ly S) -> In (p, 8904) (ablocks B ly' S') ->
  forall a, p <= a < p + 8904 -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a).
{ intros p Hp Hp' a Ha0. replace a with (p + (a - p)) by lia.
  apply (Hblk p 8904 (a - p) Hp Hp'); [change (req_size 8904) with 8904; lia | apply inFP_nil]. }
assert (KR : forall a, in_roP SEGS (sw_rlo WK) (sw_rhi WK) a ->
  ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a).
{ intros a Hro0 Ho He. rewrite HWRLO, HWRHI in Hro0.
  rewrite (Hro a); [reflexivity | | exact Ho | exact He |
    exact (ro_spares (SK := scene_sink_head) SEGS RLO RHI [] a Hro0)].
  destruct Hro0 as [(s & Hs & _ & Hr) | Hgot]; [exists s; split; [exact Hs | exact Hr]|].
  exact (pa_relro_img a Hgot). }
unfold s3_mem_mid. cbv zeta. fold F.
split; [intros i Hi; rewrite KF by (clear - Hi; lia); exact (M1 i Hi)|].
set (sF := shadow_addr F) in *. clearbody sF.
split; [intros o Ho; rewrite KS by (clear - Ho; lia); exact (M2 o Ho)|].
split; [rewrite KS by (clear; lia); exact M3|].
split; [apply (s3n_spill W W' mem mem' _ _ M4); intros i Hi; apply KH; clear - Hi Hsp; lia|].
split; [intros a Ha0 Hn; rewrite KH by (clear - Ha0 Hsp Hce; lia); exact (M5 a Ha0 Hn)|].
split; [intros a Ha0 Hn; rewrite KF by (clear - Ha0; lia); exact (M6 a Ha0 Hn)|].
split; [intros a Ha0 Hn; rewrite KS by (clear - Ha0; lia); exact (M7 a Ha0 Hn)|].
split; [intros a Ha0; rewrite (KB body Hb Hb') by (clear - Ha0; lia); exact (M8 a Ha0)|].
split; [intros a Ha0; rewrite (KB again Ha Ha') by (clear - Ha0; lia); exact (M9 a Ha0)|].
intros a Hro0 Ho He. rewrite (KR a Hro0 Ho He). exact (M10 a Hro0 Ho He).
Qed.

(* ---- check_step at 0x82f20 (a0 = blk.i, a1 = body, a2 = k), through its contract TCHECKX with the premise bundle
   s3_chk_pre, and its post carried back to the cut: the journal composed with the callee's (ajournal_sub),
   s3_mem_mid across the callee's journal (s3m_mid_j). ---- *)
Lemma s3m_call : forall (cx : rtcx SEGS) ly3 S3 (W3 : world SEGS) regs3 mem3 md3 bs body again b k
(regsT : bvmap 5 word) (memT : word -> option byte) (mdT : Model) POST,
sc_base SEGS B ameter_triv WK cx ->
cut_T (SK := scene_sink_head) SEGS B ameter_triv WK scene_geom_asan_ubsan cx
ly3 S3 W3 regs3 mem3 md3 bs body again b k ->
k < sg_nturns scene_geom_asan_ubsan ->
ajournal (SK := scene_sink_head) SEGS B (sw_stk WK) (spZ (c_regs cx)) []
(c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(8, c_fpos cx)] ly3 S3 W3 memT mdT 2 ->
s3_mem_mid cx W3 mem3 body again b k W3 memT ->
(forall r, acallee_saved r -> r <> 24 -> r <> 26 -> getr regsT (Z_to_bv 5 r) = getr regs3 (Z_to_bv 5 r)) ->
getr regsT RV_s8 = w64 (scT_off k + scene_len k) -> getr regsT RV_s10 = w64 (scene_len k) ->
getr regsT 10 = w64 (sc_F SEGS scene_geom_asan_ubsan cx + 32) -> getr regsT 11 = w64 body -> getr regsT 12 = w64 k ->
getr regsT 1 = Z_to_bv 64 (BASE + AF_LLVMFuzzerTestOneInput + 0x680) ->
(forall (W5 : world SEGS) regs5 mem5 md5,
s3_check_post cx ly3 S3 W3 regs3 mem3 bs body again b k W5 regs5 mem5 md5 ->
SRr SEGS W5 (cfg_at SEGS (BASE + AF_LLVMFuzzerTestOneInput + 0x680) regs5 mem5 md5) POST) ->
SRr SEGS W3 (cfg_at SEGS ACS regsT memT mdT) POST.
Proof.
intros cx ly3 S3 W3 regs3 mem3 md3 bs body again b k regsT memT mdT POST HB HT Hkn HJ HM HRk Hs8 Hs10 Ha0 Ha1 Ha2
Hra HK.
pose proof HM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10).
destruct (s3_keep_F ameter_triv cx ly3 S3 W3 regs3 mem3 md3 bs body again b k HT) as (HFly & HFin).
cbn [sg_cid scene_geom_asan_ubsan] in HFly, HFin.
pose proof HT as (Hk & _ & (_ & Hfrs & _) & Hab & _ & _ & _ & _ & _ & _ & _ & _ & Hsav & _ & _ & _ & _ &
(Hsp & _ & _ & _) & _).
cbn [sg_cid sg_scene_n sg_nturns scene_geom_asan_ubsan] in Hk, Hkn, Hfrs, Hab.
pose proof HB as (_ & Hsp1eq).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hsp16 & _ & Hceil & Hstklo & Hsphi & Hstkhi & _).
unfold ASTACK in HSTK.
assert (Hsp1b : spZ (c_regs cx) - 255 <= c_sp1 cx <= spZ (c_regs cx) - 224).
{ rewrite Hsp1eq. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 224) 32 ltac:(lia)) as Hm.
  pose proof (Z_div_mod_eq_full (spZ (c_regs cx) - 224) 32) as He. lia. }
assert (Hbin : In (body, 8904) (ablocks B ly3 S3))
by (rewrite Hab; apply in_or_app; left; apply in_or_app; right; left; reflexivity).
assert (Hain : In (again, 8904) (ablocks B ly3 S3))
by (rewrite Hab; apply in_or_app; right; left; reflexivity).
(* the callee-saved registers, by bv name *)
assert (HR : forall (r : bv 5) z, bv_unsigned r = z -> acallee_saved z -> z <> 24 -> z <> 26 ->
  getr regsT r = getr regs3 r).
{ intros r z Ez Hr H24 H26. subst z. pose proof (HRk (bv_unsigned r) Hr H24 H26) as E.
  rewrite !Z_to_bv_bv_unsigned in E. exact E. }
assert (HR2 : getr regsT 2 = getr regs3 2) by (apply (HR _ 2); [reflexivity | unfold acallee_saved; lia | lia | lia]).
assert (HR3 : getr regsT 3 = getr regs3 3) by (apply (HR _ 3); [reflexivity | unfold acallee_saved; lia | lia | lia]).
assert (HR4 : getr regsT 4 = getr regs3 4) by (apply (HR _ 4); [reflexivity | unfold acallee_saved; lia | lia | lia]).
assert (HR8 : getr regsT 8 = getr regs3 8) by (apply (HR _ 8); [reflexivity | unfold acallee_saved; lia | lia | lia]).
assert (HspT : spZ regsT = c_sp1 cx) by (unfold spZ; rewrite HR2; exact Hsp).
pose proof (@pa_base_lo _ scene_listing PL_scene PI_scene) as HBlo.
pose proof (@pa_B_ok _ scene_listing PI_scene) as (HB0 & HB1 & _).
assert (Hret : YK0s.ret_ok (getr regsT 1)).
{ rewrite Hra. replace (BASE + AF_LLVMFuzzerTestOneInput + 0x680) with (BASE + 0x680)
    by (unfold AF_LLVMFuzzerTestOneInput; lia).
  apply ret_ok_codeptr_v; [lia | reflexivity]. }
assert (Hra4 : 4096 <= raZ regsT).
{ unfold raZ. rewrite Hra. rewrite s3e_unsigned64; unfold AF_LLVMFuzzerTestOneInput; lia. }
assert (HSV : sc_saves SEGS cx W3 memT).
{ apply (s3_keep_saves_pt cx W3 W3 mem3 memT Hsav). intros a Ha. apply M5; lia. }
destruct (s3_chk_pre cx ly3 S3 W3 regs3 mem3 md3 bs body again b k ly3 S3 W3 memT mdT 2 regsT HB HT Hkn HJ
  ltac:(lia) Hbin M2 M3 M1 M8 HSV HR2 HR3 HR4 HR8 Hret Hra4)
  as ((ch & HPRE) & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13).
eapply SRr_bind.
{ exact (TCHECKX ly3 S3 W3 regsT memT mdT ch (sc_F SEGS scene_geom_asan_ubsan cx + 32) body k b HPRE P2 P3 P4 P5
    Ha0 Ha1 Ha2 P6 P7 P8 P9 P10 P11 P12 P13). }
cbv beta. intros W5 c5 _ (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HP5 & HQ5).
cbv beta in HQ5.
rewrite Hra. apply (HK W5 regs5 mem5 md5).
assert (HP5' : forall (r : bv 5) z, bv_unsigned r = z -> acallee_saved z -> getr regs5 r = getr regsT r).
{ intros r z Ez Hr. subst z. pose proof (HP5 (bv_unsigned r) Hr) as E. rewrite !Z_to_bv_bv_unsigned in E. exact E. }
assert (FFS : TCHECK_STEP_STK = 8496) by reflexivity.
pose proof (ajournal_sub (SK := scene_sink_head) SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  _ _ _ _ _ _ _ _ _ _ HJ HJ5 ltac:(rewrite HspT, FFS; clear - Hsp1b HSTK; lia) ltac:(rewrite HspT; clear - Hsp1b; lia)
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJc.
pose proof HJ5 as (_ & _ & _ & _ & _ & Hfrs5 & _).
rewrite HspT in HJ5.
exists ly5, S5.
split.
{ split; [exact HJc|]. split; [rewrite Hfrs5, Hfrs; reflexivity | exact I]. }
split; [exact HQ5|].
split; [intros r Hr H24 H26; rewrite (HP5 r Hr); exact (HRk r Hr H24 H26)|].
split; [rewrite (HP5' RV_s8 24 eq_refl ltac:(unfold acallee_saved; lia)); exact Hs8|].
split; [rewrite (HP5' RV_s10 26 eq_refl ltac:(unfold acallee_saved; lia)); exact Hs10|].
apply (s3m_mid_j cx W3 mem3 body again b k _ ly3 S3 W3 memT mdT ly5 S5 W5 mem5 md5 _ HJ5 HFin HFly Hbin
  ltac:(rewrite HQ5; exact Hbin) Hain ltac:(rewrite HQ5; exact Hain) ltac:(lia) ltac:(lia) HM).
Qed.

(* ---- The middle of the turn, second half: the run 0x82ed8 .. 0x82f20 (the n_k / declared reads, the k = 0
   split, UBSan guard 0x82eec and the bound test 0x82f14 decided by atom facts) into s3m_call, as s3_run_mid.  By
   a helper, pasted verbatim on its 05:18Z hand-over from S3Mid_scratch.v
   (sha256 6c11e22949d3; internal record) lines 2337-2786. ---- *)
(* ================================================================================================================
   The run 0x82ed8 .. 0x82f20 (S3MID, part 2).
   ================================================================================================================ *)
Definition S3M_PC : Z := AF_LLVMFuzzerTestOneInput + 0x634.
(* blk.i, read-only, holding the bytes the run reads (offset, value) *)
Definition s3m_blk_region (ovs : list (Z * Z)) : YP09.region :=
YP09.mkRegion (Some 25%nat) 0 34 0 0 (map (fun ov => YP09.mkChunk (fst ov) (CVal 1 (SLit (snd ov)))) ovs).
(* [sp1 + 0x40, + 8), the `declared` spill the k = 0 arm writes *)
Definition s3m_spill_region : YP09.region := YP09.mkRegion (Some 9%nat) 0x40 0x48 0x40 0x48 [].
Definition s3m_regions (ovs : list (Z * Z)) (sp : bool) : list YP09.region :=
s3m_blk_region ovs :: (if sp then [s3m_spill_region] else []).

Lemma s3m_off_cases : forall k,
(k = 0 -> scT_off k = 0 /\ scene_len k = 24) /\ (k = 342 -> scT_off k = 8890 /\ scene_len k = 14) /\
(1 <= k <= 341 -> 24 <= scT_off k <= 8864 /\ scene_len k = 26).
Proof.
intros k. unfold scT_off, scene_off, scene_len.
split; [intros ->; split; reflexivity|]. split; [intros ->; split; reflexivity|].
intros Hk. destruct (Z.eqb_spec k 343) as [E|_]; [lia|]. destruct (Z.eqb_spec k 0) as [E|_]; [lia|].
destruct (Z.eqb_spec k 342) as [E|_]; [lia|]. split; [lia | reflexivity].
Qed.

Lemma s3m_afact : forall E n v lo hi,
ew E n = w64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi -> afact_ok E n (mkAF lo hi 0).
Proof.
intros E n v lo hi H1 Hv Hlh. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite H1. unfold w64. rewrite s3e_unsigned64 by exact Hv. rewrite Z.pow_0_r, Z.mod_1_r. lia.
Qed.

Lemma s3m_reg_lit : forall (H : word -> bool) E ss ms (r : bv 5) z,
st_ok SEGS E ss (restrict H ms) -> sr_get (ss_regs ss) r = SLit z -> getr (ms_regs ms) r = Z_to_bv 64 z.
Proof. intros H E ss ms r z HS Hr. rewrite (st_ok_restrict_reg SEGS H E ss ms r HS), Hr. reflexivity. Qed.

Lemma s3m_reg_offc : forall (H : word -> bool) E ss ms (r : bv 5) n c,
st_ok SEGS E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n c ->
getr (ms_regs ms) r = Z_to_bv 64 (bv_unsigned (ew E n) + c).
Proof. intros H E ss ms r n c HS Hr. rewrite (st_ok_restrict_reg SEGS H E ss ms r HS), Hr. reflexivity. Qed.

(* the blk.i region is ok at a memory that holds the listed bytes *)
Lemma s3m_blk_ok : forall E (H : word -> bool) (m : word -> option byte) F (ovs : list (Z * Z)),
bv_unsigned (ew E 25%nat) = F + 32 -> 0 <= F -> F + 66 <= 2 ^ 64 ->
Forall (fun ov => aview SEGS H m (F + 32 + fst ov) = Some (snd ov)) ovs ->
YP09.region_ok SEGS E (mrestrict H m) (s3m_blk_region ovs).
Proof.
intros E H m F ovs H25 HF0 HF1 Hovs. unfold s3m_blk_region, YP09.region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val]. rewrite H25.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_map. eapply Forall_impl; [|exact Hovs]. intros ov Hov. cbv beta in Hov |- *.
destruct (s3n_val_mem1_of_aview H m _ _ Hov) as (Hvm & Hv).
apply (chunk_ok_val SEGS E (mrestrict H m) (F + 32) (fst ov) 1 (SLit (snd ov)) (snd ov)); [reflexivity | cbn; lia | cbn; lia |].
exact Hvm.
Qed.

(* The geometry of the turn, as linear facts (F = sc_F, the fake frame; sp0 = the entry sp; sp1 = c_sp1). *)
Lemma s3m_geo : forall (cx : rtcx SEGS) ly3 S3 (W3 : world SEGS) regs3 mem3 md3 bs body again b k,
sc_base SEGS B ameter_triv WK cx ->
cut_T (SK := scene_sink_head) SEGS B ameter_triv WK scene_geom_asan_ubsan cx
ly3 S3 W3 regs3 mem3 md3 bs body again b k ->
4096 <= sc_F SEGS scene_geom_asan_ubsan cx /\
sc_F SEGS scene_geom_asan_ubsan cx + 16384 <= alloc_ceiling /\
0x7fff7f800000 <= alloc_ceiling /\ alloc_ceiling < 2 ^ 47 /\
alloc_ceiling + 16624 <= spZ (c_regs cx) /\ spZ (c_regs cx) <= 2 ^ 47 /\
spZ (c_regs cx) - 255 <= c_sp1 cx <= spZ (c_regs cx) - 224 /\
SHADOW_OFF + 512 <= shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) /\
shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) + 2048 <= SHADOW_OFF + 2 ^ 44 /\
(forall a, sc_F SEGS scene_geom_asan_ubsan cx <= a < sc_F SEGS scene_geom_asan_ubsan cx + 16384 ->
 a < shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) \/ shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) + 2048 <= a) /\
(sc_F SEGS scene_geom_asan_ubsan cx + 16384 <= 0x10000 \/ 0x5f9000 <= sc_F SEGS scene_geom_asan_ubsan cx) /\
4096 <= body /\ body + 8904 <= alloc_ceiling /\ 4096 <= again /\ again + 8904 <= alloc_ceiling /\
(body + 8904 <= sc_F SEGS scene_geom_asan_ubsan cx \/ sc_F SEGS scene_geom_asan_ubsan cx + 16384 <= body) /\
(again + 8904 <= sc_F SEGS scene_geom_asan_ubsan cx \/ sc_F SEGS scene_geom_asan_ubsan cx + 16384 <= again) /\
(body + 8904 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= body) /\
(again + 8904 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= again).
Proof.
intros cx ly3 S3 W3 regs3 mem3 md3 bs body again b k HB HT.
destruct (s3_keep_F ameter_triv cx ly3 S3 W3 regs3 mem3 md3 bs body again b k HT) as (HFly & HFin).
destruct (s3_cut_F cx ly3 S3 W3 regs3 mem3 md3 bs body again b k HB HT) as (HF32 & HF4096 & HF47).
pose proof HT as (_ & _ & (HJ & _ & _) & Hab & _ & Hokb & Hoka & _).
cbn [sg_cid sg_scene_n scene_geom_asan_ubsan] in HFly, HFin, HJ, Hab, Hokb, Hoka.
pose proof (proj1 HJ) as HAR.
pose proof HB as (_ & Hsp1eq).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hsp16 & _ & Hceil & Hstklo & Hsphi & Hstkhi & _).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 8 (c_fpos cx) HAR HFin) as (_ & HFceil & HFapp).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR HFin) as HFimg.
assert (Hfb : fs_frame_bytes 8 = 16384) by reflexivity.
rewrite HFly in HFceil, HFapp, HFimg. rewrite Hfb in HF47, HFceil, HFapp, HFimg.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, off_img in HFapp, HFimg.
pose proof asan_consts as (HAC & _ & _ & _ & _).
pose proof YM05.alloc_ceiling_lt as Hacl.
unfold ASTACK in HSTK.
destruct Hokb as (Hb4096 & Hbz & Hbceil & _).
destruct Hoka as (Ha4096 & Haz & Haceil & _).
change (req_size 8904) with 8904 in Hbz, Hbceil, Haz, Haceil.
unfold zone2, off_img in Hbz, Haz.
assert (Hbin : In (body, 8904) (ablocks B ly3 S3))
by (rewrite Hab; apply in_or_app; left; apply in_or_app; right; left; reflexivity).
assert (Hain : In (again, 8904) (ablocks B ly3 S3))
by (rewrite Hab; apply in_or_app; right; left; reflexivity).
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 mem3 md3 body 8904 8 (c_fpos cx) HAR Hbin HFin) as Hbsep.
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 mem3 md3 again 8904 8 (c_fpos cx) HAR Hain HFin) as Hasep.
unfold zdisjoint in Hbsep, Hasep. cbn [fst snd] in Hbsep, Hasep.
rewrite HFly, Hfb in Hbsep, Hasep. change (req_size 8904) with 8904 in Hbsep, Hasep.
set (F := sc_F SEGS scene_geom_asan_ubsan cx) in *.
assert (HF8 : F mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply Z.mod_divide in HF32; [|lia]. destruct HF32 as [t Ht]. exists (4 * t). lia. }
pose proof (Z.div_mod F 8 ltac:(lia)) as HFq. rewrite HF8, Z.add_0_r in HFq.
assert (HshA : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity.
set (q := F / 8) in *. clearbody q.
assert (Hsp1b : spZ (c_regs cx) - 255 <= c_sp1 cx <= spZ (c_regs cx) - 224).
{ rewrite Hsp1eq. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 224) 32 ltac:(lia)) as Hm.
  pose proof (Z_div_mod_eq_full (spZ (c_regs cx) - 224) 32) as He. lia. }
clear Hsp1eq.
destruct Hbz as (_ & Hbz). destruct Haz as (_ & Haz).
rewrite HshA. unfold SHADOW_OFF in *.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [lia|]. split; [lia|].
split; [intros a Ha; destruct HFapp as (_ & HFapp); lia|].
split; [exact HFimg|].
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [exact Hbsep|]. split; [exact Hasep|].
split; lia.
Qed.

(* s3_mem_mid at the call state, from the build's post and a run that wrote only [sp1 + 0x40, + 8) to 8904. *)
Lemma s3m_mid_of_build : forall (cx : rtcx SEGS) ly3 S3 (W3 : world SEGS) regs3 mem3 md3 bs body again b k
regs4 mem4 md4 (memT : word -> option byte),
sc_base SEGS B ameter_triv WK cx ->
cut_T (SK := scene_sink_head) SEGS B ameter_triv WK scene_geom_asan_ubsan cx
ly3 S3 W3 regs3 mem3 md3 bs body again b k ->
s3_build_post cx ly3 S3 W3 regs3 mem3 bs body again b k W3 regs4 mem4 md4 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 0x40 <= a < c_sp1 cx + 0x48) ->
 aview SEGS (w_H W3) memT a = aview SEGS (w_H W3) mem4 a) ->
rdword (aview SEGS (w_H W3) memT) (c_sp1 cx + 0x40) = Some 8904 ->
s3_mem_mid cx W3 mem3 body again b k W3 memT.
Proof.
intros cx ly3 S3 W3 regs3 mem3 md3 bs body again b k regs4 mem4 md4 memT HB HT HP RT HM4.
destruct (s3m_geo cx ly3 S3 W3 regs3 mem3 md3 bs body again b k HB HT) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 &
G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19).
destruct HP as (_ & _ & _ & _ & HBLK4 & HSH0 & HSH2 & HREL4 & _).
cbn [sg_off_blki sg_blk_n sg_sh_blki_lo sg_sh_blki_hi scene_geom_asan_ubsan] in HBLK4, HREL4.
unfold sc_shr in HSH0, HSH2.
unfold s3_mem_mid. cbv zeta.
set (F := sc_F SEGS scene_geom_asan_ubsan cx) in *.
set (sF := shadow_addr F) in *. clearbody sF.
unfold SCENE_STEP_WIN, SCENE_STEP_FRAME, ESTACK, SHADOW_OFF in *.
(* one fact: aview at the call state agrees with the cut wherever the build and the run both left memory alone *)
assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 0x40 <= a < c_sp1 cx + 0x48) ->
  ~ (c_sp1 cx - 4144 <= a < c_sp1 cx) -> ~ (F + 32 <= a < F + 32 + 34) -> ~ (sF + 4 <= a < sF + 9) ->
  aview SEGS (w_H W3) memT a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hs Hw Hb Hh. rewrite (RT a Ha Hs). exact (HREL4 a Ha Hw (conj Hb Hh)). }
split; [intros i Hi; rewrite RT by (clear - Hi G1 G2 G3 G4 G5 G6 G7 G8 G9; lia); exact (HBLK4 i Hi)|].
split; [intros o Ho; rewrite RT by (clear - Ho G1 G2 G3 G4 G5 G6 G7 G8 G9; lia); exact (HSH0 o Ho)|].
split; [rewrite RT by (clear - G1 G2 G3 G4 G5 G6 G7 G8 G9; lia); exact (HSH2 8 ltac:(lia))|].
split; [exact HM4|].
split; [intros a Ha Hn; apply K; clear - Ha Hn G1 G2 G3 G4 G5 G6 G7 G8 G9; lia|].
split.
{ intros a Ha Hn. pose proof (G10 a Ha) as Hx. apply K; clear - Ha Hn Hx G1 G2 G3 G4 G5 G6 G7 G8 G9; lia. }
split.
{ intros a Ha Hn. pose proof (G10 (F + 32) ltac:(clear - G1; lia)) as Hx1. pose proof (G10 (F + 65) ltac:(clear - G1; lia)) as Hx2.
  apply K; clear - Ha Hn Hx1 Hx2 G1 G2 G3 G4 G5 G6 G7 G8 G9; lia. }
split; [intros a Ha; apply K; clear - Ha G1 G2 G3 G4 G5 G6 G7 G8 G9 G12 G13 G16 G18; lia|].
split; [intros a Ha; apply K; clear - Ha G1 G2 G3 G4 G5 G6 G7 G8 G9 G14 G15 G17 G19; lia|].
intros a Hro Ho He.
assert (Himg : 0x10000 <= a < 0x5f9000).
{ rewrite HWRLO, HWRHI in Hro. apply (pa_img_range (PAImg := PI_scene)).
  destruct Hro as [(s0 & Hs & _ & Hr) | Hgot]; [exists s0; split; [exact Hs | exact Hr]|].
  exact (pa_relro_img a Hgot). }
apply K; clear - Himg G1 G2 G3 G4 G5 G6 G7 G8 G9 G11; lia.
Qed.

Lemma s3_run_mid : forall (cx : rtcx SEGS) ly3 S3 (W3 : world SEGS) regs3 mem3 md3 bs body again b k
(W4 : world SEGS) regs4 mem4 md4 POST,
sc_base SEGS B ameter_triv WK cx ->
cut_T (SK := scene_sink_head) SEGS B ameter_triv WK scene_geom_asan_ubsan cx
ly3 S3 W3 regs3 mem3 md3 bs body again b k ->
k < sg_nturns scene_geom_asan_ubsan ->
s3_build_post cx ly3 S3 W3 regs3 mem3 bs body again b k W4 regs4 mem4 md4 ->
(forall (W5 : world SEGS) regs5 mem5 md5,
s3_check_post cx ly3 S3 W3 regs3 mem3 bs body again b k W5 regs5 mem5 md5 ->
SRr SEGS W5 (cfg_at SEGS (BASE + AF_LLVMFuzzerTestOneInput + 0x680) regs5 mem5 md5) POST) ->
SRr SEGS W4 (cfg_at SEGS (BASE + AF_LLVMFuzzerTestOneInput + 0x634) regs4 mem4 md4) POST.
Proof.
intros cx ly3 S3 W3 regs3 mem3 md3 bs body again b k W4 regs4 mem4 md4 POST HB HT Hkn HP HK.
pose proof HP as (-> & HJ4 & HPR4 & _ & HBLK4 & _ & _ & HREL4 & _).
cbn [sg_off_blki sg_blk_n sg_sh_blki_lo sg_sh_blki_hi sg_cid scene_geom_asan_ubsan] in HBLK4, HREL4, HJ4.
destruct (s3m_geo cx ly3 S3 W3 regs3 mem3 md3 bs body again b k HB HT) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 &
G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19).
pose proof HT as (Hk & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hsp & Hgp & Htp & _) &
_ & _ & _ & HVsp1 & _ & _ & HVblki & _ & _ & _ & _ & HVbody & _ & _ & HVgot & HVk & HVdecl & HVn1 & _).
cbn [sg_nturns sg_scene_n sgT_sp1 sgT_blki sgT_body sgT_got sgT_k sgT_decl sgT_n1 sg_off_blki scene_geom_asan_ubsan vat]
in Hk, Hkn, HVsp1, HVblki, HVbody, HVgot, HVk, HVdecl, HVn1.
assert (HR4 : forall (r : bv 5) z, bv_unsigned r = z -> acallee_saved z -> getr regs4 r = getr regs3 r).
{ intros r z Ez Hr. subst z. pose proof (HPR4 (bv_unsigned r) Hr) as E. rewrite !Z_to_bv_bv_unsigned in E. exact E. }
set (E := Eimg (Ereg regs4 [])).
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (EW : forall (r : bv 5) n z, (n < 32)%nat -> Z.to_nat (bv_unsigned r) = n -> bv_unsigned r = z -> acallee_saved z ->
  ew E n = getr regs3 r).
{ intros r n z Hn Hr Ez Hz. unfold E. rewrite (s3e_ew regs4 r n Hn Hr). exact (HR4 r z Ez Hz). }
pose proof (EW RV_s9 25%nat 25 ltac:(lia) eq_refl eq_refl ltac:(unfold acallee_saved; lia)) as E25.
pose proof (EW RV_s6 22%nat 22 ltac:(lia) eq_refl eq_refl ltac:(unfold acallee_saved; lia)) as E22.
pose proof (EW RV_s7 23%nat 23 ltac:(lia) eq_refl eq_refl ltac:(unfold acallee_saved; lia)) as E23.
pose proof (EW RV_s11 27%nat 27 ltac:(lia) eq_refl eq_refl ltac:(unfold acallee_saved; lia)) as E27.
pose proof (EW RV_s1 9%nat 9 ltac:(lia) eq_refl eq_refl ltac:(unfold acallee_saved; lia)) as E9.
pose proof (EW RV_s4 20%nat 20 ltac:(lia) eq_refl eq_refl ltac:(unfold acallee_saved; lia)) as E20.
rewrite HVblki in E25. rewrite HVgot in E22. rewrite HVk in E23. rewrite HVn1 in E27. rewrite HVsp1 in E9.
rewrite HVbody in E20.
pose proof (s3_off_range k ltac:(lia)) as Hoff.
assert (U25 : bv_unsigned (ew E 25%nat) = sc_F SEGS scene_geom_asan_ubsan cx + 32)
by (rewrite E25; unfold w64; apply s3e_unsigned64; lia).
assert (U9 : bv_unsigned (ew E 9%nat) = c_sp1 cx) by (rewrite E9; unfold w64; apply s3e_unsigned64; lia).
assert (SHOK : sh_ok SEGS (SOff 0 0) [] E (mrestrict (w_H W3) mem4)) by constructor.
unfold cfg_at. change (w64 (BASE + AF_LLVMFuzzerTestOneInput + 0x634)) with (Z_to_bv 64 (BASE + S3M_PC)).
destruct (s3m_off_cases k) as (OC0 & OC342 & OCm).
assert (Hcase : k = 0 \/ k = 342 \/ 1 <= k <= 341) by lia.
destruct Hcase as [Hk0 | [Hk342 | Hkm]].
{ (* ---------------- k = 0: n_k = 24, declared := blk[7] << 8 | blk[8] = 8904 ---------------- *)
destruct (OC0 Hk0) as (Hoff0 & Hlen).
pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstkp & _).
assert (HS0 : st_ok_pi SEGS VAL E
  (mkSS S3M_PC sr_atoms (s3m_regions [(4, 0); (5, 24); (7, 0x22); (8, 0xc8)] true) None (mkFacts [] [] []))
  (restrict (w_H W3) (mkst regs4 (Z_to_bv 64 (BASE + S3M_PC)) mem4 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (s3m_blk_ok E (w_H W3) mem4 (sc_F SEGS scene_geom_asan_ubsan cx)); [exact U25 | lia | lia |].
      rewrite Hk0 in HBLK4.
      repeat (apply Forall_cons; [cbn [fst snd]|]); [ | | | | apply Forall_nil].
      * rewrite (HBLK4 4 ltac:(lia)). reflexivity.
      * rewrite (HBLK4 5 ltac:(lia)). change (Z.to_nat 5) with 5%nat. rewrite scT_nth5. reflexivity.
      * rewrite (HBLK4 7 ltac:(lia)). change (Z.to_nat 7) with 7%nat. rewrite scT_nth7_0. reflexivity.
      * rewrite (HBLK4 8 ltac:(lia)). change (Z.to_nat 8) with 8%nat. rewrite scT_nth8_0. reflexivity.
    + unfold s3m_spill_region, YP09.region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). apply Hstkp. unfold ASTACK in HSTK. lia.
  - cbn [s3m_regions YP09.pairwise_disjoint YP09.all_disjoint].
    split; [split; [| exact I] | split; [exact I | exact I]].
    unfold YP09.extent_disjoint, s3m_blk_region, s3m_spill_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val]. rewrite U25, U9. left. lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. tauto. }
pose proof (st_ok_pi_add_fact _ _ _ 22%nat (mkAF 0 0 0) HS0
  (s3m_afact E 22 _ 0 0 E22 ltac:(lia) ltac:(lia))) as HS1.
pose proof (st_ok_pi_add_fact _ _ _ 25%nat (mkAF 4128 (2 ^ 47) 0) HS1
  (s3m_afact E 25 _ 4128 (2 ^ 47) E25 ltac:(lia) ltac:(lia))) as HS2.
pose proof (st_ok_pi_add_fact _ _ _ 27%nat (mkAF 8904 8904 0) HS2
  (s3m_afact E 27 _ 8904 8904 E27 ltac:(lia) ltac:(lia))) as HS3.
pose proof (st_ok_pi_add_fact _ _ _ 9%nat (mkAF 4096 (2 ^ 47) 0) HS3
  (s3m_afact E 9 _ 4096 (2 ^ 47) E9 ltac:(lia) ltac:(lia))) as HS4.
(* s7 = k = 0 as a literal, so `bnez s7` 0x82ee4 is decided *)
pose proof (st_ok_pi_pin_reg' _ _ _ RV_s7 0 HS4
  ltac:(cbn [ms_regs restrict mkst]; rewrite (HR4 RV_s7 23 eq_refl ltac:(unfold acallee_saved; lia)), HVk, Hk0; reflexivity)
  ltac:(vm_compute; reflexivity)) as HS.
clear HS0 HS1 HS2 HS3 HS4.
paj_run_tok RUN HS HJ4 SHOK S3_BSPAN.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?ownx =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx ownx) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen; [reflexivity | exact U9 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. left. unfold ASTACK in HSTK. lia. }
cbn [ms_mem mkst] in HF, HFr, HG.
set (mdv := with_vm_backing (m_vm_lazy md4) mat md4) in *. clearbody mdv.
lazymatch type of HFr with frame_of _ ?rs _ _ => let rs' := eval vm_compute in rs in change rs with rs' in HFr end.
(* the run wrote only the spill [sp1 + 0x40, + 8) *)
assert (RT : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 0x40 <= a < c_sp1 cx + 0x48) ->
  aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) mem4 a).
{ intros a Ha Hn. apply (aview_eq_of SEGS). apply HFr. rewrite s3e_unsigned64 by exact Ha.
  intros (r & Hin & Hr). destruct Hin as [<- | [<- | []]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hr; [lia|]. rewrite U9 in Hr. lia. }
(* ... and wrote 8904 there *)
assert (HM4 : rdword (aview SEGS (w_H W3) (ms_mem ms)) (c_sp1 cx + 0x40) = Some 8904).
{ pose proof (st_ok_mem_ok SEGS _ _ _ HS) as HM.
  lazymatch type of HM with context [ss_mem ?x] =>
    let y := eval vm_compute in (ss_mem x) in change (ss_mem x) with y in HM end.
  destruct HM as (_ & HMr & _). apply Forall_inv_tail, Forall_inv in HMr. unfold YP09.region_ok in HMr.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val] in HMr.
  rewrite U9 in HMr. destruct HMr as (_ & _ & _ & HMc). apply Forall_inv in HMc. cbn [ms_mem restrict] in HMc.
  pose proof (val_of_chunk_ok SEGS E _ (c_sp1 cx) 64 8 (SLit 8904) 8904 HMc eq_refl ltac:(cbn; lia) ltac:(cbn; lia))
    as Hvm.
  exact (rdword_of_val_mem SEGS (w_H W3) (ms_mem ms) (c_sp1 cx + 64) 8904 Hvm ltac:(lia)). }
pose proof (s3m_mid_of_build cx ly3 S3 W3 regs3 mem3 md3 bs body again b k regs4 mem4 md4 (ms_mem ms) HB HT HP
  RT HM4) as HMID.
(* the registers at the jal *)
assert (HRk : forall r, acallee_saved r -> r <> 24 -> r <> 26 -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs3 (Z_to_bv 5 r)).
{ intros r Hr H24 H26.
  destruct (Z.eq_dec r 23) as [-> | H23].
  - rewrite (s3m_reg_lit (w_H W3) E _ ms (Z_to_bv 5 23) 0 HS ltac:(vm_compute; reflexivity)).
    assert (E7 : Z_to_bv 5 23 = RV_s7) by (apply bv_eq; reflexivity).
    rewrite E7, HVk, Hk0. reflexivity.
  - assert (Hin : In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 25; 27]) by (unfold acallee_saved in Hr; cbn [In]; lia).
    pose proof (regs_kept_of_st_ok SEGS _ _ _ regs4 []
      (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 25; 27]) HS
      ltac:(unfold E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity])
      ltac:(vm_compute; reflexivity) (Z_to_bv 5 r) (in_map (Z_to_bv 5) _ r Hin)) as Ekeep.
    cbn [ms_regs restrict] in Ekeep. rewrite Ekeep. exact (HPR4 r Hr). }
pose proof (s3m_reg_offc (w_H W3) E _ ms RV_s8 22%nat 24 HS ltac:(vm_compute; reflexivity)) as Hs8.
rewrite E22 in Hs8. unfold w64 in Hs8. rewrite s3e_unsigned64 in Hs8 by lia. rewrite <- Hlen in Hs8.
pose proof (s3m_reg_lit (w_H W3) E _ ms RV_s10 24 HS ltac:(vm_compute; reflexivity)) as Hs10.
rewrite <- Hlen in Hs10.
pose proof (s3r_reg_off (w_H W3) E _ ms (10%bv : bv 5) 25%nat HS ltac:(vm_compute; reflexivity)) as Ha0.
pose proof (s3r_reg_off (w_H W3) E _ ms (11%bv : bv 5) 20%nat HS ltac:(vm_compute; reflexivity)) as Ha1.
pose proof (s3m_reg_lit (w_H W3) E _ ms (12%bv : bv 5) 0 HS ltac:(vm_compute; reflexivity)) as Ha2.
rewrite E25 in Ha0. rewrite E20 in Ha1. rewrite <- Hk0 in Ha2.
pose proof (st_ok_restrict_reg SEGS (w_H W3) _ _ ms (1%bv : bv 5) HS) as Rra0.
assert (Hra : getr (ms_regs ms) (1%bv : bv 5) = Z_to_bv 64 (BASE + AF_LLVMFuzzerTestOneInput + 0x680)).
{ rewrite Rra0. replace (BASE + AF_LLVMFuzzerTestOneInput + 0x680) with (BASE + 1664)
    by (unfold AF_LLVMFuzzerTestOneInput; lia). exact (codeptr_val _ 1664 HEI). }
clear Rra0.
pmkst HS.
rewrite pa_sigma_check_step.
exact (s3m_call cx ly3 S3 W3 regs3 mem3 md3 bs body again b k (ms_regs ms) (ms_mem ms) mdv POST HB HT Hkn HJ4 HMID
  HRk Hs8 Hs10 Ha0 Ha1 Ha2 Hra HK). }
{ (* ---------------- k = 342: n_k = 14 ---------------- *)
destruct (OC342 Hk342) as (Hoffm & Hlen).
assert (HS0 : st_ok_pi SEGS VAL E (mkSS S3M_PC sr_atoms (s3m_regions [(4, 0); (5, 14)] false) None (mkFacts [] [] []))
  (restrict (w_H W3) (mkst regs4 (Z_to_bv 64 (BASE + S3M_PC)) mem4 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    apply (s3m_blk_ok E (w_H W3) mem4 (sc_F SEGS scene_geom_asan_ubsan cx)); [exact U25 | lia | lia |].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd].
    + rewrite (HBLK4 4 ltac:(lia)). reflexivity.
    + rewrite (HBLK4 5 ltac:(lia)). change (Z.to_nat 5) with 5%nat. rewrite scT_nth5, Hlen. reflexivity.
  - cbn. tauto.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. tauto. }
pose proof (st_ok_pi_add_fact _ _ _ 22%nat (mkAF 8890 8890 0) HS0
  (s3m_afact E 22 _ 8890 8890 E22 ltac:(lia) ltac:(lia))) as HS1.
pose proof (st_ok_pi_add_fact _ _ _ 23%nat (mkAF 342 342 0) HS1
  (s3m_afact E 23 _ 342 342 E23 ltac:(lia) ltac:(lia))) as HS2.
pose proof (st_ok_pi_add_fact _ _ _ 27%nat (mkAF 8904 8904 0) HS2
  (s3m_afact E 27 _ 8904 8904 E27 ltac:(lia) ltac:(lia))) as HS.
clear HS0 HS1 HS2.
paj_run_tok RUN HS HJ4 SHOK S3_BSPAN.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?ownx =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx ownx) end.
  apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
cbn [ms_mem mkst] in HF, HFr, HG.
set (mdv := with_vm_backing (m_vm_lazy md4) mat md4) in *. clearbody mdv.
lazymatch type of HFr with frame_of _ ?rs _ _ => let rs' := eval vm_compute in rs in change rs with rs' in HFr end.
(* the run wrote nothing: blk.i is read-only *)
assert (RT : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) mem4 a).
{ intros a Ha. apply (aview_eq_of SEGS). apply HFr. rewrite s3e_unsigned64 by exact Ha.
  intros (r & Hin & Hr). destruct Hin as [<- | []]. cbn [YP09.r_wlo YP09.r_whi] in Hr. lia. }
assert (HM4 : rdword (aview SEGS (w_H W3) (ms_mem ms)) (c_sp1 cx + 0x40) = Some 8904).
{ destruct (Z.eqb_spec k 0) as [E0 | _]; [lia|].
  apply (s3n_spill W3 W3 mem4 (ms_mem ms) _ _); [|intros i Hi; apply RT; clear - Hi G3 G4 G5 G6 G7; lia].
  apply (s3n_spill W3 W3 mem3 mem4 _ _ HVdecl). intros i Hi. apply HREL4.
  - clear - Hi G3 G4 G5 G6 G7; lia.
  - unfold SCENE_STEP_WIN, SCENE_STEP_FRAME, ESTACK. clear - Hi G7; lia.
  - clear - Hi G1 G2 G3 G4 G5 G6 G7 G8 G9. unfold SHADOW_OFF in *. split; lia. }
pose proof (s3m_mid_of_build cx ly3 S3 W3 regs3 mem3 md3 bs body again b k regs4 mem4 md4 (ms_mem ms) HB HT HP
  (fun a Ha _ => RT a Ha) HM4) as HMID.
(* the registers at the jal *)
assert (HRk : forall r, acallee_saved r -> r <> 24 -> r <> 26 -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs3 (Z_to_bv 5 r)).
{ intros r Hr H24 H26.
  assert (Hin : In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 27]) by (unfold acallee_saved in Hr; cbn [In]; lia).
  pose proof (regs_kept_of_st_ok SEGS _ _ _ regs4 []
    (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 27]) HS
    ltac:(unfold E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity])
    ltac:(vm_compute; reflexivity) (Z_to_bv 5 r) (in_map (Z_to_bv 5) _ r Hin)) as Ekeep.
  cbn [ms_regs restrict] in Ekeep. rewrite Ekeep. exact (HPR4 r Hr). }
pose proof (s3m_reg_offc (w_H W3) E _ ms RV_s8 22%nat 14 HS ltac:(vm_compute; reflexivity)) as Hs8.
rewrite E22 in Hs8. unfold w64 in Hs8. rewrite s3e_unsigned64 in Hs8 by lia. rewrite <- Hlen in Hs8.
pose proof (s3m_reg_lit (w_H W3) E _ ms RV_s10 14 HS ltac:(vm_compute; reflexivity)) as Hs10.
rewrite <- Hlen in Hs10.
pose proof (s3r_reg_off (w_H W3) E _ ms (10%bv : bv 5) 25%nat HS ltac:(vm_compute; reflexivity)) as Ha0.
pose proof (s3r_reg_off (w_H W3) E _ ms (11%bv : bv 5) 20%nat HS ltac:(vm_compute; reflexivity)) as Ha1.
pose proof (s3r_reg_off (w_H W3) E _ ms (12%bv : bv 5) 23%nat HS ltac:(vm_compute; reflexivity)) as Ha2.
rewrite E25 in Ha0. rewrite E20 in Ha1. rewrite E23 in Ha2.
pose proof (st_ok_restrict_reg SEGS (w_H W3) _ _ ms (1%bv : bv 5) HS) as Rra0.
assert (Hra : getr (ms_regs ms) (1%bv : bv 5) = Z_to_bv 64 (BASE + AF_LLVMFuzzerTestOneInput + 0x680)).
{ rewrite Rra0. replace (BASE + AF_LLVMFuzzerTestOneInput + 0x680) with (BASE + 1664)
    by (unfold AF_LLVMFuzzerTestOneInput; lia). exact (codeptr_val _ 1664 HEI). }
clear Rra0.
pmkst HS.
rewrite pa_sigma_check_step.
exact (s3m_call cx ly3 S3 W3 regs3 mem3 md3 bs body again b k (ms_regs ms) (ms_mem ms) mdv POST HB HT Hkn HJ4 HMID
  HRk Hs8 Hs10 Ha0 Ha1 Ha2 Hra HK).
}
{ (* ---------------- 1 <= k <= 341: n_k = 26 ---------------- *)
destruct (OCm Hkm) as (Hoffm & Hlen).
assert (HS0 : st_ok_pi SEGS VAL E (mkSS S3M_PC sr_atoms (s3m_regions [(4, 0); (5, 26)] false) None (mkFacts [] [] []))
  (restrict (w_H W3) (mkst regs4 (Z_to_bv 64 (BASE + S3M_PC)) mem4 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    apply (s3m_blk_ok E (w_H W3) mem4 (sc_F SEGS scene_geom_asan_ubsan cx)); [exact U25 | lia | lia |].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd].
    + rewrite (HBLK4 4 ltac:(lia)). reflexivity.
    + rewrite (HBLK4 5 ltac:(lia)). change (Z.to_nat 5) with 5%nat. rewrite scT_nth5, Hlen. reflexivity.
  - cbn. tauto.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. tauto. }
pose proof (st_ok_pi_add_fact _ _ _ 22%nat (mkAF 24 8864 0) HS0
  (s3m_afact E 22 _ 24 8864 E22 ltac:(lia) ltac:(lia))) as HS1.
pose proof (st_ok_pi_add_fact _ _ _ 23%nat (mkAF 1 341 0) HS1
  (s3m_afact E 23 _ 1 341 E23 ltac:(lia) ltac:(lia))) as HS2.
pose proof (st_ok_pi_add_fact _ _ _ 27%nat (mkAF 8904 8904 0) HS2
  (s3m_afact E 27 _ 8904 8904 E27 ltac:(lia) ltac:(lia))) as HS.
clear HS0 HS1 HS2.
paj_run_tok RUN HS HJ4 SHOK S3_BSPAN.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?ownx =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx ownx) end.
  apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
cbn [ms_mem mkst] in HF, HFr, HG.
set (mdv := with_vm_backing (m_vm_lazy md4) mat md4) in *. clearbody mdv.
lazymatch type of HFr with frame_of _ ?rs _ _ => let rs' := eval vm_compute in rs in change rs with rs' in HFr end.
(* the run wrote nothing: blk.i is read-only *)
assert (RT : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) mem4 a).
{ intros a Ha. apply (aview_eq_of SEGS). apply HFr. rewrite s3e_unsigned64 by exact Ha.
  intros (r & Hin & Hr). destruct Hin as [<- | []]. cbn [YP09.r_wlo YP09.r_whi] in Hr. lia. }
assert (HM4 : rdword (aview SEGS (w_H W3) (ms_mem ms)) (c_sp1 cx + 0x40) = Some 8904).
{ destruct (Z.eqb_spec k 0) as [E0 | _]; [lia|].
  apply (s3n_spill W3 W3 mem4 (ms_mem ms) _ _); [|intros i Hi; apply RT; clear - Hi G3 G4 G5 G6 G7; lia].
  apply (s3n_spill W3 W3 mem3 mem4 _ _ HVdecl). intros i Hi. apply HREL4.
  - clear - Hi G3 G4 G5 G6 G7; lia.
  - unfold SCENE_STEP_WIN, SCENE_STEP_FRAME, ESTACK. clear - Hi G7; lia.
  - clear - Hi G1 G2 G3 G4 G5 G6 G7 G8 G9. unfold SHADOW_OFF in *. split; lia. }
pose proof (s3m_mid_of_build cx ly3 S3 W3 regs3 mem3 md3 bs body again b k regs4 mem4 md4 (ms_mem ms) HB HT HP
  (fun a Ha _ => RT a Ha) HM4) as HMID.
(* the registers at the jal *)
assert (HRk : forall r, acallee_saved r -> r <> 24 -> r <> 26 -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs3 (Z_to_bv 5 r)).
{ intros r Hr H24 H26.
  assert (Hin : In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 27]) by (unfold acallee_saved in Hr; cbn [In]; lia).
  pose proof (regs_kept_of_st_ok SEGS _ _ _ regs4 []
    (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 27]) HS
    ltac:(unfold E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity])
    ltac:(vm_compute; reflexivity) (Z_to_bv 5 r) (in_map (Z_to_bv 5) _ r Hin)) as Ekeep.
  cbn [ms_regs restrict] in Ekeep. rewrite Ekeep. exact (HPR4 r Hr). }
pose proof (s3m_reg_offc (w_H W3) E _ ms RV_s8 22%nat 26 HS ltac:(vm_compute; reflexivity)) as Hs8.
rewrite E22 in Hs8. unfold w64 in Hs8. rewrite s3e_unsigned64 in Hs8 by lia. rewrite <- Hlen in Hs8.
pose proof (s3m_reg_lit (w_H W3) E _ ms RV_s10 26 HS ltac:(vm_compute; reflexivity)) as Hs10.
rewrite <- Hlen in Hs10.
pose proof (s3r_reg_off (w_H W3) E _ ms (10%bv : bv 5) 25%nat HS ltac:(vm_compute; reflexivity)) as Ha0.
pose proof (s3r_reg_off (w_H W3) E _ ms (11%bv : bv 5) 20%nat HS ltac:(vm_compute; reflexivity)) as Ha1.
pose proof (s3r_reg_off (w_H W3) E _ ms (12%bv : bv 5) 23%nat HS ltac:(vm_compute; reflexivity)) as Ha2.
rewrite E25 in Ha0. rewrite E20 in Ha1. rewrite E23 in Ha2.
pose proof (st_ok_restrict_reg SEGS (w_H W3) _ _ ms (1%bv : bv 5) HS) as Rra0.
assert (Hra : getr (ms_regs ms) (1%bv : bv 5) = Z_to_bv 64 (BASE + AF_LLVMFuzzerTestOneInput + 0x680)).
{ rewrite Rra0. replace (BASE + AF_LLVMFuzzerTestOneInput + 0x680) with (BASE + 1664)
    by (unfold AF_LLVMFuzzerTestOneInput; lia). exact (codeptr_val _ 1664 HEI). }
clear Rra0.
pmkst HS.
rewrite pa_sigma_check_step.
exact (s3m_call cx ly3 S3 W3 regs3 mem3 md3 bs body again b k (ms_regs ms) (ms_mem ms) mdv POST HB HT Hkn HJ4 HMID
  HRk Hs8 Hs10 Ha0 Ha1 Ha2 Hra HK).
}
Qed.

(* ---- The tail of the turn, second half: from the jal __asan_memcpy at 0x82f44, the copy through AMEMCPY
   (aj_intrin_atS, premises from s3_cpy_pre), the re-poison 0x82f48-0x82f5c,
   the latch, and the back edge / exit closed by s3_next_T / s3_next_TX
   into the segment's two continuations, as s3t_cpy.
   By a helper, pasted verbatim
   on its 05:46Z hand-over (its first part repeats
   s3_mem_mid / s3_check_post, which are above). ---- *)
Let BRt := paj_branch (PI := PI_scene).

(* ---- Run A, 0x82f24 .. the jal __asan_memcpy 0x82f44: the three loads read the spill words [sp1 + 0x48],
   [sp1 + 0x50] and [sp1 + 0x58].  The region holds them as the extra atoms 32, 33, 34 of the entry environment
   (never as literals of the cut's names, so the engine runs on a closed state). ---- *)
Definition s3t_spillA : YP09.region := YP09.mkRegion (Some 9%nat) 0x48 0x60 0x48 0x48
[YP09.mkChunk 0x48 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x50 (CVal 8 (SOff 33 0));
 YP09.mkChunk 0x58 (CVal 8 (SOff 34 0))].
Definition s3t_ssA : sstate := mkSS 0x680 sr_atoms [s3t_spillA] None (mkFacts [] [] []).



(* ---- small helpers of the tail ---- *)
Lemma s3t_pres : forall (regs regs' : bvmap 5 word) (r : bv 5) z,
aregs_preserved regs regs' -> bv_unsigned r = z -> acallee_saved z -> getr regs' r = getr regs r.
Proof.
intros regs regs' r z HP Ez Hz. subst z. pose proof (HP _ Hz) as E. rewrite !Z_to_bv_bv_unsigned in E. exact E.
Qed.

(* a one-byte chunk of a run's region pins that byte, whatever symbolic value it holds *)
Lemma s3t_chunk_byte : forall E (m : word -> option byte) base off e v,
YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal 1 e)) -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
mbyte SEGS m (base + off) = Some (Z_to_bv 8 v).
Proof.
intros E m base off e v Hc He Hv. unfold YP09.chunk_ok in Hc.
destruct (Hc 0 ltac:(cbn [YP09.c_len YP09.cv_len YP09.c_val]; lia)) as (x & Hx & Hm).
cbn [YP09.cbyte YP09.c_off YP09.c_val] in Hx, Hm. injection Hx as <-.
rewrite Z.add_0_r in Hm. rewrite Hm. f_equal.
unfold YP09.byte_of_word. rewrite He, s3e_unsigned64 by lia.
replace (8 * 0) with 0 by lia. rewrite Z.shiftr_0_r. reflexivity.
Qed.

(* `addiw s7,s7,1` 0x82f58 on k < 2^31 - 1 *)
Lemma s3t_addiw1 : forall k, 0 <= k < 2 ^ 31 - 1 ->
sext 64 (alu32 ALU_ADD (low32 (w64 k)) (low32 (Z_to_bv 64 1))) = w64 (k + 1).
Proof.
intros k Hk.
replace (low32 (Z_to_bv 64 1)) with (sext 32 (Z_to_bv 12 1)) by (apply bv_eq; vm_compute; reflexivity).
rewrite w_addiw. replace (bv_signed (Z_to_bv 12 1)) with 1 by (vm_compute; reflexivity).
apply bv_eq. unfold w64. rewrite v_addiw_small; rewrite ?s3e_unsigned64; lia.
Qed.

Local Ltac s3t_inr z := lazymatch goal with |- In ?r (map (Z_to_bv 5) ?l) =>
  replace r with (Z_to_bv 5 z) by (apply bv_eq; reflexivity); apply in_map; cbn [In]; tauto end.

Local Ltac s3t_rd HS r H :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    pose proof (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) as H;
    let e := eval vm_compute in (sr_get (ss_regs ssx) r) in change (sr_get (ss_regs ssx) r) with e in H
  end.

(* ---- Run B, 0x82f48 .. the back edge 0x82f6c: the five re-poison stores into blk.i's shadow cells, seated with
   the frame-shadow window [sh F + 4, sh F + 9) and NO chunks (a Theorem Labs lane's SHADOW-SPEEDUP.md, fast form), with
   atom 19's range as s3_run_build seats it. ---- *)
Definition s3t_ssB : sstate :=
mkSS 0x6a4 sr_atoms [YP09.mkRegion (Some 19%nat) 4 9 4 9 []] None (mkFacts [(19%nat, S3_F19)] [] []).

Lemma s3t_cpy : forall (cx : rtcx SEGS) ly3 S3 (W3 : world SEGS) regs3 mem3 md3 bs body again b k POST
ly4 S4 (W4 : world SEGS) (regsT : bvmap 5 word) (memT : word -> option byte) (mdT : Model),
sc_base SEGS B ameter_triv WK cx ->
cut_T (SK := scene_sink_head) SEGS B ameter_triv WK scene_geom_asan_ubsan cx ly3 S3 W3 regs3 mem3 md3 bs body again b k ->
0 <= k < sg_nturns scene_geom_asan_ubsan ->
(k + 1 < sg_nturns scene_geom_asan_ubsan ->
 sc_from_T (SK := scene_sink_head) SEGS B ameter_triv WK scene_geom_asan_ubsan cx POST (k + 1)) ->
sc_from_TX (SK := scene_sink_head) SEGS B ameter_triv WK scene_geom_asan_ubsan cx POST ->
sc_j (SK := scene_sink_head) SEGS B ameter_triv WK scene_geom_asan_ubsan cx ly4 S4 W4 memT mdT 2 ->
ablocks B ly4 S4 = ablocks B ly3 S3 ->
(forall r, acallee_saved r -> r <> 24 -> r <> 26 -> getr regsT (Z_to_bv 5 r) = getr regs3 (Z_to_bv 5 r)) ->
getr regsT RV_s8 = w64 (scT_off k + scene_len k) ->
s3_mem_mid cx W3 mem3 body again b k W4 memT ->
getr regsT 10 = w64 (again + scT_off k) ->
getr regsT 11 = w64 (sc_F SEGS scene_geom_asan_ubsan cx + 32 + scT_src k) ->
getr regsT 12 = w64 (scene_len k) ->
getr regsT 1 = Z_to_bv 64 (BASE + 0x6a4) ->
SRr SEGS W4 (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA SS___asan_memcpy)) memT (seg_rom SEGS)) mdT) POST.
Proof.
intros cx ly3 S3 W3 regs3 mem3 md3 bs body again b k POST ly4 S4 W4 regsT memT mdT
HB HT Hkk HnT HnX (HJ & Hfr4 & Hmo4) Hab4 HRk Hs8 HM Ha0 Ha1 Ha2 Hra.
pose proof HM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10).
pose proof HT as (Hk & _ & (HJ3 & Hfrs3 & _) & Hab & _ & Hokb & Hoka & Hdis & Hlenb & _ & _ & _ & _ & _ & _ & _ &
  _ & (Hsp & Hgp & Htp & _) & _ & _ & V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & Vgot & Vk & _ &
  V16 & _ & Vna & _ & _ & _ & _ & V20).
cbn [sg_cid sg_nturns sg_scene_n sg_off_blki sg_off_mac sg_off_expect sgT_sp0 sgT_sp1 sgT_Fsp sgT_shF sgT_blki
  sgT_srcA sgT_srcB sgT_mac sgT_shexp sgT_body sgT_again sgT_nprime sgT_got sgT_k sgT_n1 sgT_nagain sgT_f8
  scene_geom_asan_ubsan vat] in Hkk, HJ, Hfr4, Hk, HJ3, Hfrs3, Hab, Hokb, Hoka, Hdis, Hlenb, V1, V2, V3, V4, V5,
  V6, V7, V8, V9, V10, V11, V12, Vgot, Vk, V16, Vna, V20.
change (224 / 8) with 28 in V9.
pose proof HB as (_ & Hsp1eq).
assert (Hsp1b : spZ (c_regs cx) - 255 <= c_sp1 cx <= spZ (c_regs cx) - 224).
{ rewrite Hsp1eq. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 224) 32 ltac:(lia)) as Hm.
  pose proof (Z_div_mod_eq_full (spZ (c_regs cx) - 224) 32) as He. lia. }
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hsp16 & _ & Hceil & Hstklo & Hsphi & Hstkhi & _).
unfold ASTACK in HSTK.
assert (Ho16 : (c_sp1 cx - spZ (c_regs cx)) mod 16 = 0).
{ rewrite Hsp1eq. generalize ((spZ (c_regs cx) - 224) / 32) as t. intros t.
  apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hsp16; [|lia]. destruct Hsp16 as [u Hu]. exists (2 * t - u). lia. }
clear Hsp1eq.
(* ---------------- the geometry, as linear facts ---------------- *)
destruct (s3_keep_F ameter_triv cx ly3 S3 W3 regs3 mem3 md3 bs body again b k HT) as (HFly3 & HFin3).
cbn [sg_cid scene_geom_asan_ubsan] in HFly3, HFin3.
assert (HFa4 : frame_addr ly4 8 (c_fpos cx) = sc_F SEGS scene_geom_asan_ubsan cx).
{ pose proof HJ as (_ & Hly4 & _). destruct Hly4 as (_ & _ & _ & _ & _ & EF & _).
  unfold sc_F, rt_F, frame_addr. rewrite EF. reflexivity. }
pose proof (proj1 HJ3) as HAR3.
destruct (s3_cut_F cx ly3 S3 W3 regs3 mem3 md3 bs body again b k HB HT) as (HF32 & HF4096 & HF47).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 8 (c_fpos cx) HAR3 HFin3) as (_ & HFceil & HFapp).
assert (Hfb : fs_frame_bytes 8 = 16384) by reflexivity.
rewrite HFly3 in HFceil, HFapp. rewrite Hfb in HF47, HFceil, HFapp.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
pose proof asan_consts as (HAC & _ & _ & _ & _).
pose proof YM05.alloc_ceiling_lt as Hacl.
assert (Hbin : In (body, 8904) (ablocks B ly3 S3))
  by (rewrite Hab; apply in_or_app; left; apply in_or_app; right; left; reflexivity).
assert (Hain : In (again, 8904) (ablocks B ly3 S3)) by (rewrite Hab; apply in_or_app; right; left; reflexivity).
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 mem3 md3 body 8904 8 (c_fpos cx) HAR3 Hbin HFin3) as Hbsep.
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 mem3 md3 again 8904 8 (c_fpos cx) HAR3 Hain HFin3) as Hasep.
unfold zdisjoint in Hbsep, Hasep. cbn [fst snd] in Hbsep, Hasep.
rewrite HFly3, Hfb in Hbsep, Hasep. change (req_size 8904) with 8904 in Hbsep, Hasep.
destruct Hokb as (Hb4096 & Hbz & Hbceil & _).
destruct Hoka as (Ha4096 & Haz & Haceil & _).
change (req_size 8904) with 8904 in Hbz, Hbceil, Haz, Haceil.
unfold zone2, off_img in Hbz, Haz.
set (F := sc_F SEGS scene_geom_asan_ubsan cx) in *.
assert (HF8 : F mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply Z.mod_divide in HF32; [|lia]. destruct HF32 as [t Ht]. exists (4 * t). lia. }
pose proof (Z.div_mod F 8 ltac:(lia)) as HFq. rewrite HF8, Z.add_0_r in HFq.
assert (HshA : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity.
set (q := F / 8) in *. clearbody q.
assert (BND : 4096 <= F /\ F = 8 * q /\ 512 <= q /\ q + 2048 < 2 ^ 44 /\ shadow_addr F = SHADOW_OFF + q /\
  F + 16384 <= alloc_ceiling /\ 0x7fff7f800000 <= alloc_ceiling /\
  alloc_ceiling + 16624 <= spZ (c_regs cx) /\ spZ (c_regs cx) <= 2 ^ 47 /\
  spZ (c_regs cx) - 255 <= c_sp1 cx <= spZ (c_regs cx) - 224)
by (clear - HF4096 HF47 HFq HshA HFceil HAC Hceil Hstklo HSTK Hsphi Hstkhi Hsp1b; repeat split; lia).
assert (Hof : 0 <= scT_off k /\ scT_off k + scene_len k <= 8904 /\ 14 <= scene_len k <= 26 /\
  7 <= scT_src k /\ scT_src k + scene_len k <= 33).
{ pose proof (s3_off_range k ltac:(lia)). pose proof (s3_bound k ltac:(lia)).
  assert (Hc : (scene_len k = 24 /\ scT_src k = 9) \/ ((scene_len k = 26 \/ scene_len k = 14) /\ scT_src k = 7)).
  { unfold scT_src, scene_len. destruct (k =? 0); [lia | destruct (k =? 342); lia]. }
  lia. }
(* the registers, by bv name *)
assert (RK : forall (r : bv 5) z, bv_unsigned r = z -> acallee_saved z -> z <> 24 -> z <> 26 ->
  getr regsT r = getr regs3 r).
{ intros r z Ez Hr H24 H26. subst z. pose proof (HRk (bv_unsigned r) Hr H24 H26) as E.
  rewrite !Z_to_bv_bv_unsigned in E. exact E. }
assert (HspT : spZ regsT = spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))).
{ unfold spZ. rewrite (RK 2%bv 2 eq_refl ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)).
  unfold spZ in Hsp. rewrite Hsp. lia. }
assert (HgpT : getr regsT 3 = w64 (as_gp B))
  by (rewrite (RK 3%bv 3 eq_refl ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)); exact Hgp).
assert (HtpT : getr regsT 4 = w64 (as_tp B))
  by (rewrite (RK 4%bv 4 eq_refl ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)); exact Htp).
assert (Hin4 : In (again, sg_scene_n scene_geom_asan_ubsan) (ablocks B ly4 S4)) by (rewrite Hab4; exact Hain).
(* ---------------- __asan_memcpy (again + got <- blk.i + scT_src k, n_k bytes) at 0x82f44 ---------------- *)
destruct (s3_cpy_pre cx ly3 S3 W3 regs3 mem3 md3 bs body again b k ly4 S4 W4 memT mdT 2 regsT
  (c_sp1 cx - spZ (c_regs cx)) (again + scT_off k) (F + 32 + scT_src k) (scene_len k) HT
  ltac:(cbn [sg_nturns scene_geom_asan_ubsan]; lia) HJ Hin4 M2 M3 HspT ltac:(unfold ESTACK; lia) eq_refl eq_refl eq_refl)
  as ((Hn & Hd0 & Hdn) & Hdest & Hamr & Hrad & Hhull & Hsrc).
eapply SRr_bind.
{ exact (aj_intrin_atS (SK := scene_sink_head) SEGS B LAWS pa_segs_low OCpy (SIGMA SS___asan_memcpy) AMEMCPY
    W4 regsT memT (sw_stk WK) (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(8, c_fpos cx)]
    ly4 S4 mdT 2 (again + scT_off k) (F + 32 + scT_src k) (scene_len k) (c_sp1 cx - spZ (c_regs cx))
    (Z_to_bv 64 (BASE + 0x6a4)) HJ Ha0 Ha1 Ha2 Hn Hd0 Hdn HspT Ho16 ltac:(lia) ltac:(unfold ESTACK; lia)
    HgpT HtpT Hra (ret_ok_codeptr_v 0x6a4 ltac:(lia) eq_refl) Hdest Hamr Hrad Hhull Hsrc). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & Heff & Hkeep & Hpres2 & _).
assert (RK2 : forall (r : bv 5) z, bv_unsigned r = z -> acallee_saved z -> z <> 24 -> z <> 26 ->
  getr regs2 r = getr regs3 r).
{ intros r z Ez Hr H24 H26. rewrite <- (RK r z Ez Hr H24 H26). subst z.
  pose proof (HP2 (bv_unsigned r) Hr) as E. rewrite !Z_to_bv_bv_unsigned in E. exact E. }
(* ---------------- run B: the re-poison 0x82f48 .. 0x82f6c ---------------- *)
set (E2 := Eimg (Ereg regs2 [])).
assert (HEI : img_env VAL A_LIM E2) by apply Eimg_env.
assert (U19 : bv_unsigned (ew E2 19%nat) = shadow_addr F).
{ unfold E2. rewrite (s3e_ew regs2 RV_s3 19%nat ltac:(lia) ltac:(vm_compute; reflexivity)).
  rewrite (RK2 RV_s3 19 eq_refl ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)), V4.
  unfold w64. apply s3e_unsigned64. rewrite HshA. unfold SHADOW_OFF. lia. }
pose proof (proj1 HJ2) as HAR2.
assert (HFin4 : In (8, c_fpos cx) (frames S4)) by (rewrite Hfr4; left; reflexivity).
destruct (al_frames _ _ LAWS ly4 S4 W4 mem2 md2 _ _ HAR2 HFin4) as (_ & _ & _ & Hpsh2).
rewrite HFa4, Hfb in Hpsh2. change (16384 / 8) with 2048 in Hpsh2.
assert (HS : st_ok_pi SEGS VAL E2 s3t_ssB
  (restrict (w_H W4) (mkst regs2 (Z_to_bv 64 (BASE + 0x6a4)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold YP09.region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
    rewrite U19, HshA. split; [unfold SHADOW_OFF in *; lia|]. split; [unfold SHADOW_OFF in *; lia|].
    split; [|constructor]. intros o Ho. apply (apresent_writable SEGS).
    rewrite <- HshA. exact (proj1 (Hpsh2 o ltac:(lia))).
  - cbn. tauto.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I].
    unfold afact_ok, S3_F19. cbn [af_lo af_hi af_al2]. rewrite U19, HshA, Z.pow_0_r, Z.mod_1_r.
    unfold SHADOW_OFF in *. lia. }
assert (SHOK : sh_ok SEGS (SOff 0 0) [] E2 (mrestrict (w_H W4) mem2)) by constructor.
unfold s3t_ssB in HS.
paj_run_tok RUN HS HJ2 SHOK S3_BSPAN.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?ownx =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx ownx) end.
  eapply awr_ok_cons_gen; [reflexivity | exact U19 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
  right; right; right. exists 8, (c_fpos cx). split; [left; reflexivity|]. right.
  unfold in_zr. cbn [fst snd]. rewrite HFa4, Hfb. change (16384 / 8) with 2048. lia. }
set (mdv := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody mdv.
s3t_rd HS RV_s6 R6. s3t_rd HS RV_s7 R7. s3t_rd HS RV_a1 R11. s3t_rd HS (10%bv : bv 5) R10.
set (memF := ms_mem ms) in *. set (regsF := ms_regs ms) in *.
(* ---------------- what run B did to memory: blk.i's five shadow cells, nothing else ---------------- *)
assert (Rrun : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr F + 4 <= a < shadow_addr F + 9) ->
  aview SEGS (w_H W4) memF a = aview SEGS (w_H W4) mem2 a).
{ intros a Ha Hna. apply (aview_eq_of SEGS). apply HFr. rewrite s3e_unsigned64 by exact Ha.
  intros (r & Hin & Hr). cbn [ss_mem In] in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hr. rewrite U19 in Hr. lia. }
assert (R21 : sv_denot E2 (SOff 21 0) = Z_to_bv 64 (2 ^ 64 - 8)).
{ cbn [sv_denot]. rewrite Z.add_0_r. unfold E2.
  rewrite (s3e_ew regs2 RV_s5 21%nat ltac:(lia) ltac:(vm_compute; reflexivity)).
  rewrite (RK2 RV_s5 21 eq_refl ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)), V20.
  unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
pose proof (st_ok_mem_ok SEGS _ _ _ HS) as HMB.
lazymatch type of HMB with context [ss_mem ?x] =>
  let y := eval vm_compute in (ss_mem x) in change (ss_mem x) with y in HMB end.
destruct HMB as (_ & HMr & _).
apply Forall_inv in HMr. unfold YP09.region_ok in HMr.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val] in HMr.
rewrite U19 in HMr. destruct HMr as (_ & _ & _ & HMc). cbn [ms_mem restrict] in HMc.
assert (ShB : forall o, 4 <= o < 9 -> aview SEGS (w_H W4) memF (shadow_addr F + o) = Some 248).
{ intros o Ho. unfold aview.
  assert (Hc : YP09.chunk_ok SEGS E2 (mrestrict (w_H W4) memF) (shadow_addr F)
    (YP09.mkChunk o (CVal 1 (SOff 21 0)))).
  { apply (proj1 (Forall_forall _ _) HMc).
    assert (Hcase : o = 4 \/ o = 5 \/ o = 6 \/ o = 7 \/ o = 8) by lia.
    destruct Hcase as [-> | [-> | [-> | [-> | ->]]]]; cbn; tauto. }
  rewrite (s3t_chunk_byte _ _ _ _ _ _ Hc R21 ltac:(lia)). reflexivity. }
(* ---------------- the registers at the back edge ---------------- *)
assert (HAG2 : env_agree 32 (Ereg regs2 []) E2) by (split; [intros n0 Hn0; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (KB2 : forall r, In r (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26; 27]) -> getr regsF r = getr regs2 r)
  by exact (regs_kept_of_st_ok_pi E2 _ _ regs2 [] (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26; 27])
    HS HAG2 ltac:(vm_compute; reflexivity)).
assert (HRkF : forall r, acallee_saved r -> r <> 22 -> r <> 23 -> r <> 24 -> r <> 26 ->
  getr regsF (Z_to_bv 5 r) = getr regs3 (Z_to_bv 5 r)).
{ intros r Hr H22 H23 H24 H26.
  assert (Hin : In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26; 27]) by (unfold acallee_saved in Hr; cbn [In]; lia).
  rewrite (KB2 _ (in_map (Z_to_bv 5) _ r Hin)), (HP2 r Hr). exact (HRk r Hr H24 H26). }
assert (S8F : getr regsF RV_s8 = w64 (scT_off k + scene_len k)).
{ rewrite (KB2 RV_s8 ltac:(s3t_inr 24)).
  rewrite (s3t_pres regsT regs2 RV_s8 24 HP2 eq_refl ltac:(unfold acallee_saved; lia)). exact Hs8. }
assert (S6F : getr regsF RV_s6 = getr regsF RV_s8).
{ rewrite R6, (KB2 RV_s8 ltac:(s3t_inr 24)). cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
  unfold E2. exact (s3e_ew regs2 RV_s8 24%nat ltac:(lia) ltac:(vm_compute; reflexivity)). }
assert (S7F : getr regsF RV_s7 = w64 (k + 1)).
{ rewrite R7. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. unfold E2.
  rewrite (s3e_ew regs2 RV_s7 23%nat ltac:(lia) ltac:(vm_compute; reflexivity)).
  rewrite (RK2 RV_s7 23 eq_refl ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)), Vk.
  apply s3t_addiw1. lia. }
assert (S11F : getr regsF RV_a1 = getr regsF RV_s4).
{ rewrite R11, (KB2 RV_s4 ltac:(s3t_inr 20)). cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
  unfold E2. exact (s3e_ew regs2 RV_s4 20%nat ltac:(lia) ltac:(vm_compute; reflexivity)). }
assert (S10F : getr regsF (10%bv : bv 5) = w64 343) by (rewrite R10; reflexivity).
(* ---------------- memory at the back edge, against the call's memory ---------------- *)
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr F + 4 <= a < shadow_addr F + 9) ->
  ~ (again + scT_off k <= a < again + scT_off k + scene_len k) -> ~ (c_sp1 cx - 4096 <= a < c_sp1 cx) ->
  aview SEGS (w_H W4) memF a = aview SEGS (w_H W4) memT a).
{ intros a Ha H1 H2 H3. rewrite (Rrun a Ha H1). apply Hkeep; [exact Ha | exact H2 | unfold ESTACK; lia]. }
assert (HCUT : forall md5, same_but_materialized mdv md5 ->
  cut_T (SK := scene_sink_head) SEGS B ameter_triv WK scene_geom_asan_ubsan cx ly4 S4 W4 regsF memF md5
    bs body again b (k + 1)).
{ intros md5 Hsm.
  apply (s3_next_T ameter_triv cx ly3 S3 W3 regs3 mem3 md3 bs body again b k ly4 S4 W4 regsF memF md5 HB HT
    ltac:(cbn [sg_nturns scene_geom_asan_ubsan]; lia)); fold F.
  - split; [|split; [exact Hfr4 | exact Hmo4]].
    rewrite (same_but_materialized_wvb mdv md5 Hsm).
    apply (ajournal_materialize (SK := scene_sink_head) SEGS B LAWS pa_segs_low). exact HJ2.
  - exact Hab4.
  - exact HRkF.
  - exact S8F.
  - exact S6F.
  - exact S7F.
  - exact S11F.
  - apply (s3n_spill W4 W4 memT memF _ _ M4). intros i Hi. apply KEEP; unfold SHADOW_OFF in *; lia.
  - intros a Ha Hna. rewrite KEEP by (unfold SHADOW_OFF in *; lia). exact (M5 a Ha Hna).
  - intros a Ha Hna. rewrite KEEP by (unfold SHADOW_OFF in *; lia). exact (M6 a Ha Hna).
  - intros a Ha Hna. rewrite KEEP by (unfold SHADOW_OFF in *; lia). exact (M7 a Ha Hna).
  - intros a Ha. rewrite KEEP by (unfold SHADOW_OFF in *; lia). exact (M8 a Ha).
  - intros a Ha Hna. rewrite KEEP by (unfold SHADOW_OFF in *; lia). exact (M9 a Ha).
  - intros a Hro Ho He.
    assert (Himg : 0x10000 <= a < 0x5f9000).
    { apply (@pa_img_range _ scene_listing PI_scene). pose proof Hro as Hro'. rewrite HWRLO, HWRHI in Hro'.
      destruct Hro' as [(s & Hs & _ & Hr) | Hgot]; [exists s; split; [exact Hs | exact Hr]|].
      exact (pa_relro_img a Hgot). }
    rewrite KEEP by (unfold SHADOW_OFF in *; lia). exact (M10 a Hro Ho He).
  - intros o Ho. exact (ShB o Ho).
  - intros i Hi. rewrite Rrun by (unfold SHADOW_OFF in *; lia).
    rewrite (Heff i Hi). replace (F + 32 + scT_src k + i) with (F + 32 + (scT_src k + i)) by lia.
    rewrite (M1 (scT_src k + i) ltac:(lia)). reflexivity. }
(* ---------------- 0x82f6c `bne s7,a0`: the back edge or the loop exit ---------------- *)
pmkst HS.
let d := eval vm_compute in (decode_any (Z_to_bv 32 0xf4ab90e3)) in
assert (Hdec : decode_any (Z_to_bv 32 0xf4ab90e3) = d) by (vm_compute; reflexivity);
lazymatch d with Some (Branch ?c ?r1 ?r2 ?imm, _) =>
  eapply (s3r_branch_off W4 regsF 1736 memF mdv POST 0xf4ab90e3 c r1 r2 imm RV_s7 (10%bv : bv 5) (-192)) end.
- vm_compute; reflexivity.
- vm_compute; reflexivity.
- exact Hdec.
- apply bv_eq. vm_compute; reflexivity.
- apply bv_eq. vm_compute; reflexivity.
- vm_compute; reflexivity.
- intros Hc md5 Hsm. cbn [branch_taken] in Hc. rewrite S7F, S10F, bv_eqb_unsigned in Hc. unfold w64 in Hc.
  rewrite !s3e_unsigned64 in Hc by lia.
  assert (Hk1 : k + 1 < 343) by (destruct (Z.eqb_spec (k + 1) 343); cbn in Hc; [discriminate Hc | lia]).
  replace (BASE + (1736 + -192)) with (sg_pc_t scene_geom_asan_ubsan)
    by (cbn [sg_pc_t scene_geom_asan_ubsan]; unfold AF_LLVMFuzzerTestOneInput, SEG_T_off; lia).
  change (SRr SEGS W4 (cfg_at SEGS (sg_pc_t scene_geom_asan_ubsan) regsF memF md5) POST).
  exact (HnT ltac:(cbn [sg_nturns scene_geom_asan_ubsan]; lia) ly4 S4 W4 regsF memF md5 bs body again b
    (HCUT md5 Hsm)).
- intros Hc md5 Hsm. cbn [branch_taken] in Hc. rewrite S7F, S10F, bv_eqb_unsigned in Hc. unfold w64 in Hc.
  rewrite !s3e_unsigned64 in Hc by lia.
  assert (Hk1 : k + 1 = 343) by (destruct (Z.eqb_spec (k + 1) 343); cbn in Hc; [lia | discriminate Hc]).
  replace (BASE + (1736 + 4)) with (sg_pc_tx scene_geom_asan_ubsan)
    by (cbn [sg_pc_tx scene_geom_asan_ubsan]; unfold AF_LLVMFuzzerTestOneInput, SEG_TX_off; lia).
  change (SRr SEGS W4 (cfg_at SEGS (sg_pc_tx scene_geom_asan_ubsan) regsF memF md5) POST).
  exact (HnX ly4 S4 W4 regsF memF md5 bs body again b
    (s3_next_TX ameter_triv cx bs body again b k ly4 S4 W4 regsF memF md5 (HCUT md5 Hsm)
      ltac:(cbn [sg_nturns scene_geom_asan_ubsan]; lia) S8F S6F)).
Qed.

(* ---- The tail of the turn, first half: 0x82f24 .. 0x82f40 (UBSan guard 0x82f28 and the source select) into
   s3t_cpy, as s3_run_tail over s3_check_post.  By a helper,
   pasted verbatim on its 05:50Z
   hand-over. ---- *)
(* a run over read-only regions changes no byte *)
Lemma s3t_frame_ro : forall E (rs : smem) (m m' : word -> option byte),
frame_of E rs m m' -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> forall x, m' x = m x.
Proof.
intros E rs m m' HF Hro x. apply HF. intros (r & Hin & Hr).
pose proof (proj1 (forallb_forall _ rs) Hro r Hin) as Hw. apply Z.leb_le in Hw. lia.
Qed.

Lemma s3t_mid_ext : forall (cx : rtcx SEGS) (W3 : world SEGS) mem3 body again b k (W : world SEGS) m m',
(forall a, aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
s3_mem_mid cx W3 mem3 body again b k W m -> s3_mem_mid cx W3 mem3 body again b k W m'.
Proof.
intros cx W3 mem3 body again b k W m m' HE (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10).
unfold s3_mem_mid. cbv zeta.
split; [intros i Hi; rewrite HE; exact (M1 i Hi)|].
split; [intros o Ho; rewrite HE; exact (M2 o Ho)|].
split; [rewrite HE; exact M3|].
split; [rewrite (rdword_ext (aview SEGS (w_H W) m) (aview SEGS (w_H W) m')); [exact M4 | intros i Hi; apply HE]|].
split; [intros a Ha Hn; rewrite HE; exact (M5 a Ha Hn)|].
split; [intros a Ha Hn; rewrite HE; exact (M6 a Ha Hn)|].
split; [intros a Ha Hn; rewrite HE; exact (M7 a Ha Hn)|].
split; [intros a Ha; rewrite HE; exact (M8 a Ha)|].
split; [intros a Ha; rewrite HE; exact (M9 a Ha)|].
intros a Hro Ho He. rewrite HE. exact (M10 a Hro Ho He).
Qed.

(* ================================================================================================================
   THE TAIL OF THE TURN as one lemma: from check_step's return at 0x82f24 (BASE + AF_LLVMFuzzerTestOneInput + 0x680),
   in the state the middle lane hands on (s3_check_post), to the head of turn k + 1 (sc_from_T (k + 1)) or the
   loop exit (sc_from_TX).  Run A 0x82f24 .. 0x82f44: `ld a0,0x50(s1)` (~again), the UBSan edge `bltu a0,s6`
   0x82f28 (refuted: s3_cut_guard_again), `mv a1,s2`, `beqz s7` 0x82f30 (both arms), `ld a1,0x48(s1)` on k <> 0,
   `ld a0,0x58(s1)`, `add a0,a0,s6`, `mv a2,s10`, `jal __asan_memcpy` 0x82f44; then s3t_cpy.
   ================================================================================================================ *)
Lemma s3_run_tail : forall (cx : rtcx SEGS) ly3 S3 (W3 : world SEGS) regs3 mem3 md3 bs body again b k
(W4 : world SEGS) regs4 mem4 md4 POST,
sc_base SEGS B ameter_triv WK cx ->
cut_T (SK := scene_sink_head) SEGS B ameter_triv WK scene_geom_asan_ubsan cx ly3 S3 W3 regs3 mem3 md3 bs body again b k ->
0 <= k < sg_nturns scene_geom_asan_ubsan ->
(k + 1 < sg_nturns scene_geom_asan_ubsan ->
 sc_from_T (SK := scene_sink_head) SEGS B ameter_triv WK scene_geom_asan_ubsan cx POST (k + 1)) ->
sc_from_TX (SK := scene_sink_head) SEGS B ameter_triv WK scene_geom_asan_ubsan cx POST ->
s3_check_post cx ly3 S3 W3 regs3 mem3 bs body again b k W4 regs4 mem4 md4 ->
SRr SEGS W4 (cfg_at SEGS (BASE + AF_LLVMFuzzerTestOneInput + 0x680) regs4 mem4 md4) POST.
Proof.
intros cx ly3 S3 W3 regs3 mem3 md3 bs body again b k W4 regs4 mem4 md4 POST HB HT Hkk HnT HnX HP.
destruct HP as (ly4 & S4 & (HJ & Hfr4 & Hmo4) & Hab4 & HRk & Hs8 & Hs10 & HM).
pose proof HM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10).
pose proof (s3_cut_guard_again cx ly3 S3 W3 regs3 mem3 md3 bs body again b k HT) as Hguard.
pose proof HT as (Hk & _ & _ & Hab & _ & Hokb & Hoka & Hdis & Hlenb & _ & _ & _ & _ & _ & _ & _ & _ &
  (Hsp & Hgp & Htp & _) & _ & _ & V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & Vgot & Vk & _ &
  V16 & _ & Vna & _ & _ & _ & _ & V20).
cbn [sg_nturns sg_scene_n sg_off_blki sg_off_mac sg_off_expect sgT_sp0 sgT_sp1 sgT_Fsp sgT_shF sgT_blki sgT_srcA
  sgT_srcB sgT_mac sgT_shexp sgT_body sgT_again sgT_nprime sgT_got sgT_k sgT_n1 sgT_nagain sgT_f8
  scene_geom_asan_ubsan vat] in Hkk, Hk, Hab, Hokb, Hoka, Hdis, Hlenb, V1, V2, V3, V4, V5, V6, V7, V8, V9, V10, V11,
  V12, Vgot, Vk, V16, Vna, V20.
change (224 / 8) with 28 in V9.
pose proof HB as (_ & Hsp1eq).
assert (Hsp1b : spZ (c_regs cx) - 255 <= c_sp1 cx <= spZ (c_regs cx) - 224).
{ rewrite Hsp1eq. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 224) 32 ltac:(lia)) as Hm.
  pose proof (Z_div_mod_eq_full (spZ (c_regs cx) - 224) 32) as He. lia. }
clear Hsp1eq.
pose proof HJ as (HAR4 & Hly4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstkp & Hstk & _).
destruct Hstk as (Hsp16 & _ & Hceil & Hstklo & Hsphi & Hstkhi & _).
unfold ASTACK in HSTK.
destruct (s3_cut_F cx ly3 S3 W3 regs3 mem3 md3 bs body again b k HB HT) as (HF32 & HF4096 & HF47).
assert (Hfb : fs_frame_bytes 8 = 16384) by reflexivity. rewrite Hfb in HF47.
set (F := sc_F SEGS scene_geom_asan_ubsan cx) in *.
(* the registers the run reads, as the cut has them *)
assert (HR : forall (r : bv 5) z, bv_unsigned r = z -> acallee_saved z -> z <> 24 -> z <> 26 ->
  getr regs4 r = getr regs3 r).
{ intros r z Ez Hr H24 H26. subst z. pose proof (HRk (bv_unsigned r) Hr H24 H26) as E.
  rewrite !Z_to_bv_bv_unsigned in E. exact E. }
assert (R9 : getr regs4 RV_s1 = w64 (c_sp1 cx))
  by (rewrite (HR RV_s1 9 eq_refl ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)); exact V2).
(* the three spill words at the run's memory *)
assert (S48 : rdword (aview SEGS (w_H W4) mem4) (c_sp1 cx + 0x48) = Some (F + 32 + 7))
  by (apply (s3n_spill W3 W4 mem3 mem4 _ _ V6); intros i Hi; apply M5; lia).
assert (S50 : rdword (aview SEGS (w_H W4) mem4) (c_sp1 cx + 0x50) = Some (2 ^ 64 - 1 - again))
  by (apply (s3n_spill W3 W4 mem3 mem4 _ _ Vna); intros i Hi; apply M5; lia).
assert (S58 : rdword (aview SEGS (w_H W4) mem4) (c_sp1 cx + 0x58) = Some again)
  by (apply (s3n_spill W3 W4 mem3 mem4 _ _ V11); intros i Hi; apply M5; lia).
destruct (s3_blk_range cx again 8904 Hoka ltac:(lia)) as (Ha4096 & Haceil & _).
pose proof YM05.alloc_ceiling_lt as Hacl.
(* ---------------- the entry block of run A ---------------- *)
set (E := Eimg (Ereg regs4 [w64 (F + 39); w64 (2 ^ 64 - 1 - again); w64 again])).
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs4 r)
  by (intros n r Hn; pose proof (bv_unsigned_in_range 5 r) as Hr; change (bv_modulus 5) with 32 in Hr;
      unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); replace n with (Z.to_nat (bv_unsigned r)) by lia;
      apply ew_Ereg_reg).
assert (Ex : forall (n : nat) (v : Z),
  n = 32%nat /\ v = F + 39 \/ n = 33%nat /\ v = 2 ^ 64 - 1 - again \/ n = 34%nat /\ v = again ->
  ew E n = w64 v).
{ intros n v Hn. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia).
  destruct Hn as [(-> & ->) | [(-> & ->) | (-> & ->)]]; reflexivity. }
assert (Dn : forall n (r : bv 5) v, Z.of_nat n = bv_unsigned r -> getr regs4 r = w64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff n 0) = w64 v).
{ intros n r v Hn Hr Hv. cbn [sv_denot]. rewrite (EE n r Hn), Hr, Z.add_0_r. unfold w64.
  rewrite s3e_unsigned64 by lia. reflexivity. }
assert (Dx : forall (n : nat) v, n = 32%nat /\ v = F + 39 \/ n = 33%nat /\ v = 2 ^ 64 - 1 - again \/
  n = 34%nat /\ v = again -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = w64 v).
{ intros n v Hn Hv. cbn [sv_denot]. rewrite (Ex n v Hn), Z.add_0_r. unfold w64.
  rewrite s3e_unsigned64 by lia. reflexivity. }
assert (Hb9 : bv_unsigned (ew E 9%nat) = c_sp1 cx).
{ rewrite (EE 9%nat RV_s1 eq_refl), R9. unfold w64. apply s3e_unsigned64. lia. }
assert (HS : st_ok_pi SEGS VAL E s3t_ssA
  (restrict (w_H W4) (mkst regs4 (Z_to_bv 64 (BASE + 0x680)) mem4 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold s3t_spillA, YP09.region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
    rewrite Hb9. split; [lia|]. split; [lia|]. split.
    + intros o Ho. apply (apresent_writable SEGS). apply Hstkp. lia.
    + apply Forall_cons.
      { apply (chunk_ok_val SEGS _ _ (c_sp1 cx) 0x48 8 (SOff 32 0) (F + 39)).
        - exact (Dx 32%nat (F + 39) ltac:(tauto) ltac:(lia)).
        - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
        - cbn [Z.of_N]. lia.
        - replace (F + 39) with (F + 32 + 7) by lia. exact (val_mem_of_rdword SEGS (w_H W4) mem4 _ _ S48). }
      apply Forall_cons.
      { apply (chunk_ok_val SEGS _ _ (c_sp1 cx) 0x50 8 (SOff 33 0) (2 ^ 64 - 1 - again)).
        - exact (Dx 33%nat (2 ^ 64 - 1 - again) ltac:(tauto) ltac:(lia)).
        - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
        - cbn [Z.of_N]. lia.
        - exact (val_mem_of_rdword SEGS (w_H W4) mem4 _ _ S50). }
      apply Forall_cons; [|apply Forall_nil].
      { apply (chunk_ok_val SEGS _ _ (c_sp1 cx) 0x58 8 (SOff 34 0) again).
        - exact (Dx 34%nat again ltac:(tauto) ltac:(lia)).
        - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
        - cbn [Z.of_N]. lia.
        - exact (val_mem_of_rdword SEGS (w_H W4) mem4 _ _ S58). }
  - cbn. tauto.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. tauto. }
assert (SHOK : sh_ok SEGS (SOff 0 0) [] E (mrestrict (w_H W4) mem4)) by constructor.
unfold cfg_at.
replace (w64 (BASE + AF_LLVMFuzzerTestOneInput + 0x680)) with (Z_to_bv 64 (BASE + 0x680))
  by (unfold w64, AF_LLVMFuzzerTestOneInput; f_equal; lia).
unfold s3t_ssA in HS.
(* the value facts the branches and the call read *)
assert (D22 : sv_denot E (SOff 22 0) = w64 (scT_off k)).
{ pose proof (s3_off_range k ltac:(lia)).
  apply (Dn 22%nat RV_s6); [reflexivity | | lia].
  rewrite (HR RV_s6 22 eq_refl ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)). exact Vgot. }
assert (D23 : sv_denot E (SOff 23 0) = w64 k).
{ apply (Dn 23%nat RV_s7); [reflexivity | | lia].
  rewrite (HR RV_s7 23 eq_refl ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)). exact Vk. }
(* ---------------- 0x82f24 `ld a0,0x50(s1)` and the UBSan edge 0x82f28 ---------------- *)
paj_run_tok RUN HS HJ SHOK S3_BSPAN.
{ apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
set (mdv1 := with_vm_backing (m_vm_lazy md4) mat md4) in *. clearbody mdv1.
psrr_branch_tok RUN BRt HS SHOK S3_BSPAN.
{ exfalso. cbn [branch_taken] in Hc. rewrite (Dx 33%nat (2 ^ 64 - 1 - again) ltac:(tauto) ltac:(lia)), D22 in Hc.
  rewrite bv_ltu_unsigned in Hc. unfold w64 in Hc. rewrite !s3e_unsigned64 in Hc by (pose proof (s3_off_range k ltac:(lia)); lia).
  apply Z.ltb_lt in Hc. exact (Hguard Hc). }
(* ---------------- 0x82f2c `mv a1,s2` and `beqz s7` 0x82f30 ---------------- *)
paj_run_tok RUN HS HJ SHOK S3_BSPAN.
{ apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
set (mdv2 := with_vm_backing (m_vm_lazy mdv1) mat0 mdv1) in *. clearbody mdv2.
assert (MEQ2 : forall x, mrestrict (w_H W4) (ms_mem ms0) x = mrestrict (w_H W4) mem4 x).
{ intros x. rewrite (s3t_frame_ro _ _ _ _ HFr0 ltac:(vm_compute; reflexivity) x).
  exact (s3t_frame_ro _ _ _ _ HFr ltac:(vm_compute; reflexivity) x). }
psrr_branch_tok RUN BRt HS SHOK S3_BSPAN.
- (* k = 0: a1 = s2 = blk.i + 9 *)
  cbn [branch_taken] in Hc0. rewrite D23 in Hc0. cbn [sv_denot] in Hc0. rewrite bv_eqb_unsigned in Hc0. unfold w64 in Hc0.
  rewrite !s3e_unsigned64 in Hc0 by lia. apply Z.eqb_eq in Hc0. subst k.
  paj_run_tok RUN HS HJ SHOK S3_BSPAN.
  { apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  set (mdv3 := with_vm_backing (m_vm_lazy mdv2) _ mdv2) in *. clearbody mdv3.
  lazymatch goal with HSx : st_ok _ _ _ (restrict (w_H W4) ?msx) |- _ => rename msx into ms3 end.
  lazymatch goal with Hx : frame_of _ _ (mrestrict (w_H W4) (ms_mem ms0)) (mrestrict (w_H W4) (ms_mem ms3)) |- _ =>
    rename Hx into HFr3 end.
  assert (MEQ3 : forall x, mrestrict (w_H W4) (ms_mem ms3) x = mrestrict (w_H W4) mem4 x).
  { intros x. rewrite (s3t_frame_ro _ _ _ _ HFr3 ltac:(vm_compute; reflexivity) x). exact (MEQ2 x). }
  assert (HAG : env_agree 32 (Ereg regs4 [w64 (F + 39); w64 (2 ^ 64 - 1 - again); w64 again]) E)
    by (split; [intros n0 Hn0; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (KA : forall r, In r (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]) ->
    getr (ms_regs ms3) r = getr regs4 r)
    by exact (regs_kept_of_st_ok SEGS E _ _ regs4 [w64 (F + 39); w64 (2 ^ 64 - 1 - again); w64 again]
      (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]) HS HAG ltac:(vm_compute; reflexivity)).
  pose proof (st_ok_restrict_reg SEGS (w_H W4) _ _ ms3 (10%bv : bv 5) HS) as Ra0.
  pose proof (st_ok_restrict_reg SEGS (w_H W4) _ _ ms3 (11%bv : bv 5) HS) as Ra1.
  pose proof (st_ok_restrict_reg SEGS (w_H W4) _ _ ms3 (12%bv : bv 5) HS) as Ra2.
  pose proof (st_ok_restrict_reg SEGS (w_H W4) _ _ ms3 (1%bv : bv 5) HS) as Rra.
  lazymatch type of HS with st_ok _ _ ?ssx _ =>
    let e0 := eval vm_compute in (sr_get (ss_regs ssx) (10%bv : bv 5)) in
    let e1 := eval vm_compute in (sr_get (ss_regs ssx) (11%bv : bv 5)) in
    let e2 := eval vm_compute in (sr_get (ss_regs ssx) (12%bv : bv 5)) in
    let er := eval vm_compute in (sr_get (ss_regs ssx) (1%bv : bv 5)) in
    change (sr_get (ss_regs ssx) (10%bv : bv 5)) with e0 in Ra0;
    change (sr_get (ss_regs ssx) (11%bv : bv 5)) with e1 in Ra1;
    change (sr_get (ss_regs ssx) (12%bv : bv 5)) with e2 in Ra2;
    change (sr_get (ss_regs ssx) (1%bv : bv 5)) with er in Rra end.
  cbn [ms_regs restrict] in Ra0, Ra1, Ra2, Rra.
  pmkst HS.
  apply (s3t_cpy cx ly3 S3 W3 regs3 mem3 md3 bs body again b 0 POST ly4 S4 W4 (ms_regs ms3) (ms_mem ms3) mdv3
    HB HT Hkk HnT HnX).
  + split; [exact HJ | split; [exact Hfr4 | exact Hmo4]].
  + exact Hab4.
  + intros r Hr H24 H26.
    assert (Hin : In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]) by (unfold acallee_saved in Hr; cbn [In]; lia).
    rewrite (KA _ (in_map (Z_to_bv 5) _ r Hin)). exact (HRk r Hr H24 H26).
  + rewrite (KA RV_s8 ltac:(s3t_inr 24)). exact Hs8.
  + apply (s3t_mid_ext cx W3 mem3 body again b 0 W4 mem4 (ms_mem ms3)); [|exact HM].
    intros a. apply (aview_eq_of SEGS). apply MEQ3.
  + rewrite Ra0.
    change (sv_denot E (SAlu ALU_ADD (SOff 22 0) (SOff 34 0)))
      with (alu64 ALU_ADD (sv_denot E (SOff 22 0)) (sv_denot E (SOff 34 0))).
    rewrite D22, (Dx 34%nat again ltac:(tauto) ltac:(lia)). unfold w64. rewrite alu64_add_lit. f_equal. lia.
  + rewrite Ra1, (Dn 18%nat RV_s2 (F + 32 + 9) eq_refl
      ltac:(rewrite (HR RV_s2 18 eq_refl ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)); exact V7) ltac:(lia)).
    reflexivity.
  + rewrite Ra2. apply (Dn 26%nat RV_s10 (scene_len 0) eq_refl Hs10). unfold scene_len. cbn. lia.
  + rewrite Rra. exact (codeptr_val E 1700 HEI).
- (* k <> 0: a1 = [s1+0x48] = blk.i + 7 *)
  cbn [branch_taken] in Hc0. rewrite D23 in Hc0. cbn [sv_denot] in Hc0. rewrite bv_eqb_unsigned in Hc0. unfold w64 in Hc0.
  rewrite !s3e_unsigned64 in Hc0 by lia. apply Z.eqb_neq in Hc0.
  paj_run_tok RUN HS HJ SHOK S3_BSPAN.
  { apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  set (mdv3 := with_vm_backing (m_vm_lazy mdv2) _ mdv2) in *. clearbody mdv3.
  lazymatch goal with HSx : st_ok _ _ _ (restrict (w_H W4) ?msx) |- _ => rename msx into ms3 end.
  lazymatch goal with Hx : frame_of _ _ (mrestrict (w_H W4) (ms_mem ms0)) (mrestrict (w_H W4) (ms_mem ms3)) |- _ =>
    rename Hx into HFr3 end.
  assert (MEQ3 : forall x, mrestrict (w_H W4) (ms_mem ms3) x = mrestrict (w_H W4) mem4 x).
  { intros x. rewrite (s3t_frame_ro _ _ _ _ HFr3 ltac:(vm_compute; reflexivity) x). exact (MEQ2 x). }
  assert (HAG : env_agree 32 (Ereg regs4 [w64 (F + 39); w64 (2 ^ 64 - 1 - again); w64 again]) E)
    by (split; [intros n0 Hn0; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (KA : forall r, In r (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]) ->
    getr (ms_regs ms3) r = getr regs4 r)
    by exact (regs_kept_of_st_ok SEGS E _ _ regs4 [w64 (F + 39); w64 (2 ^ 64 - 1 - again); w64 again]
      (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]) HS HAG ltac:(vm_compute; reflexivity)).
  pose proof (st_ok_restrict_reg SEGS (w_H W4) _ _ ms3 (10%bv : bv 5) HS) as Ra0.
  pose proof (st_ok_restrict_reg SEGS (w_H W4) _ _ ms3 (11%bv : bv 5) HS) as Ra1.
  pose proof (st_ok_restrict_reg SEGS (w_H W4) _ _ ms3 (12%bv : bv 5) HS) as Ra2.
  pose proof (st_ok_restrict_reg SEGS (w_H W4) _ _ ms3 (1%bv : bv 5) HS) as Rra.
  lazymatch type of HS with st_ok _ _ ?ssx _ =>
    let e0 := eval vm_compute in (sr_get (ss_regs ssx) (10%bv : bv 5)) in
    let e1 := eval vm_compute in (sr_get (ss_regs ssx) (11%bv : bv 5)) in
    let e2 := eval vm_compute in (sr_get (ss_regs ssx) (12%bv : bv 5)) in
    let er := eval vm_compute in (sr_get (ss_regs ssx) (1%bv : bv 5)) in
    change (sr_get (ss_regs ssx) (10%bv : bv 5)) with e0 in Ra0;
    change (sr_get (ss_regs ssx) (11%bv : bv 5)) with e1 in Ra1;
    change (sr_get (ss_regs ssx) (12%bv : bv 5)) with e2 in Ra2;
    change (sr_get (ss_regs ssx) (1%bv : bv 5)) with er in Rra end.
  cbn [ms_regs restrict] in Ra0, Ra1, Ra2, Rra.
  pmkst HS.
  apply (s3t_cpy cx ly3 S3 W3 regs3 mem3 md3 bs body again b k POST ly4 S4 W4 (ms_regs ms3) (ms_mem ms3) mdv3
    HB HT Hkk HnT HnX).
  + split; [exact HJ | split; [exact Hfr4 | exact Hmo4]].
  + exact Hab4.
  + intros r Hr H24 H26.
    assert (Hin : In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]) by (unfold acallee_saved in Hr; cbn [In]; lia).
    rewrite (KA _ (in_map (Z_to_bv 5) _ r Hin)). exact (HRk r Hr H24 H26).
  + rewrite (KA RV_s8 ltac:(s3t_inr 24)). exact Hs8.
  + apply (s3t_mid_ext cx W3 mem3 body again b k W4 mem4 (ms_mem ms3)); [|exact HM].
    intros a. apply (aview_eq_of SEGS). apply MEQ3.
  + rewrite Ra0.
    change (sv_denot E (SAlu ALU_ADD (SOff 22 0) (SOff 34 0)))
      with (alu64 ALU_ADD (sv_denot E (SOff 22 0)) (sv_denot E (SOff 34 0))).
    rewrite D22, (Dx 34%nat again ltac:(tauto) ltac:(lia)). unfold w64. rewrite alu64_add_lit. f_equal. lia.
  + rewrite Ra1, (Dx 32%nat (F + 39) ltac:(tauto) ltac:(lia)).
    unfold scT_src. rewrite (proj2 (Z.eqb_neq k 0) Hc0). f_equal. lia.
  + rewrite Ra2. apply (Dn 26%nat RV_s10 (scene_len k) eq_refl Hs10).
    unfold scene_len. destruct (k =? 0); [lia | destruct (k =? 342); lia].
  + rewrite Rra. exact (codeptr_val E 1700 HEI).
Qed.


(* =================================================================================================================
   THE SEGMENT.  One whole_transfer turn, 0x82eac .. 0x82f6c, of the asan-ubsan LLVMFuzzerTestOneInput, as the cut
   file states it: from cut_T at k, the turn reaches cut_T at k + 1 (the back edge) or cut_TX (the exit).  The four
   pieces, in the order the code runs them:
     s3_tt_at_cut   build_scene_step's trailer premises at the cut (HRO_TT, HB_Z_TT, HB_C_TT);
     s3_run_build   0x82eac .. 0x82ed4: the unpoison, reac_ctrl_build_scene_step, the refuted abort edge;
     s3_run_mid     0x82ed8 .. 0x82f20: the n_k / declared reads, UBSan 0x82eec, the bound test, check_step;
     s3_run_tail    0x82f24 .. 0x82f6c: UBSan 0x82f28, __asan_memcpy, the re-poison, the latch, closed by
                    s3_next_T / s3_next_TX into the two continuations.
   ================================================================================================================= *)
Theorem scene_seg_S3_turn_au :
seg_S3_turn_stmt (SK := scene_sink_head) SEGS B ameter_triv WK scene_geom_asan_ubsan.
Proof.
intros cx POST k HB Hk Hnext HX.
intros ly3 S3 W3 regs3 mem3 md3 bs body again b HT.
destruct (s3_tt_at_cut cx ly3 S3 W3 regs3 mem3 md3 bs body again b k HB HT) as (T1 & T2 & T3 & T4).
apply (s3_run_build cx ly3 S3 W3 regs3 mem3 md3 bs body again b k POST HB HT (proj2 Hk) T1 T2 T3 T4).
intros W4 regs4 mem4 md4 Hpost.
apply (s3_run_mid cx ly3 S3 W3 regs3 mem3 md3 bs body again b k W4 regs4 mem4 md4 POST HB HT (proj2 Hk) Hpost).
intros W5 regs5 mem5 md5 Hchk.
exact (s3_run_tail cx ly3 S3 W3 regs3 mem3 md3 bs body again b k W5 regs5 mem5 md5 POST HB HT Hk Hnext HX Hchk).
Qed.
End h.
End d.
