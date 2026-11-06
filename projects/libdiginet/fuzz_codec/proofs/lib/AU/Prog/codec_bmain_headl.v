(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the run / keep / branch / leaf tactics, kept_run and same_io_wvb are the text of
   projects/reac-pw/fuzz_qdisc/proofs/lib/A/QPgSlots.v:123-188 (made there from proofs/libreac/fuzz_knock/lib/A/APgStep.v,
   origin/ossv/recipes 6ebe35ba632), the stack-slot write tactics that of QPgCheck.v:52-69, the entry regions those of
   QPgRt.v:61-65 / 193-243, the shadow entry that of proofs/libreac/fuzz_identity/lib/A/Prog/sb_dec.v:354-370
   (origin/ossv/recipes 4b6f0df50aa7), cw_U_sx32_eqb that of proofs/libreac/fuzz_knock/lib/A/APgStep.v:54-68
   (U_sx32_eqb, origin/ossv/recipes 4b6f0df50aa7), cw_join_win that of proofs/reac-pw/fuzz_qdisc/lib/A/QPgLoop0.v:169-196
   (ra_join_win, a working branch b0f706c04a19), cw_bcmp_at that of lib/Reusable/YCbq.v:2262-2310 (aj_bcmp_at) with
   the wrapper's same_but_materialized kept in its post, cw_st_ok_at that of lib/Reusable/YI04.v:342-356 (entry_st_ok_full)
   with the env apart from the registers, renamed with the prefix cw_ and moved to libdiginet/fuzz_codec's ASan
   build (image A); the leaf ends in lib/A/Prog/CPgBase.v's cdc_post, whose memory clause is CodecCJ's tcj_kept. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/CPgWalk.v, with its module names changed; 414 of its 469 lines of code are new or changed and 578 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_owel.v, with its module names and numbers changed; 557 of its 629 lines of code are new or changed and 397 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_oweh_lib.v, with its module paths and module names changed; 355 of its 438 lines of code are new or changed and 546 lines of the source are left out. *)
(* The calls inside the HEAD segment of the image-B walk of LLVMFuzzerTestOneInput (0x80c30-0x80dc8,
   lib/AU/Prog/codec_bmain_inv.v seg_head): the two calls of the runtime's checked memset (0x80cd8 and
   0x80da0) and the call of diginet_personality_of (0x80d50) as steps from one cut to the next, and the small
   memory facts the record needs. It is the image-A layer (lib/A/Prog/codec_amain_headl.v) at image B: the
   record at F + 192, the 60 shadow bytes of image B's frame, image B's entries and contracts.
   bm_call_kept_x is the image-A walk's am_call_kept (lib/A/Prog/codec_amain_encl.v) at image B: from the cut
   facts at a callee's entry and the pieces of the callee's post (tcj_kept with sp = sp1 and a write set inside
   the call record), the same facts at the return state, and every byte of the frame off the write set kept. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08 YI16.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YC85.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09 YE00 YE01 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgEncU CodecRo CodecGlobs.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkU CPgWalkImgU CPgWalkKeptU CPgWalkCallU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_inv codec_bmain_st codec_bmain_head_cut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ================================ bytes that are zero ================================ *)
Lemma hd_le_byte_0 : forall w k, YO0f.le_byte 0 w k = 0.
Proof.
intros w k. unfold YO0f.le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia).
rewrite Z.shiftr_0_l. reflexivity.
Qed.
Lemma hd_nth_repeat : forall (v : Z) (n j : nat), (j < n)%nat -> nth j (repeat v n) 0 = v.
Proof.
intros v n. induction n as [|n IH]; intros j Hj; [lia|].
cbn [repeat]. destruct j as [|j]; [reflexivity|]. cbn [nth]. apply IH. lia.
Qed.
Section z. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma hd_val_zero : forall (W : world tfibsegs) mem q (n : nat),
(forall i, 0 <= i < Z.of_nat n -> aview tfibsegs (w_H W) mem (q + i) = Some 0) ->
val_mem tfibsegs (mrestrict (w_H W) mem) q n 0.
Proof.
intros W mem q n H j Hj.
destruct (bm_mb W mem (q + Z.of_nat j) 0 (H (Z.of_nat j) ltac:(lia))) as (Hm & _).
rewrite Hm, hd_le_byte_0. reflexivity.
Qed.
Lemma hd_garr8_val : forall (W : world tfibsegs) mem q (n : nat) v,
(forall i, 0 <= i < Z.of_nat n -> aview tfibsegs (w_H W) mem (q + i) = Some v) -> 0 <= v < 256 ->
garr8 tfibsegs (mrestrict (w_H W) mem) q (repeat v n).
Proof.
intros W mem q n v H Hv j Hj. rewrite repeat_length in Hj.
rewrite (hd_nth_repeat v n j Hj). split; [|exact Hv].
destruct (bm_mb W mem (q + Z.of_nat j) v (H (Z.of_nat j) ltac:(lia))) as (Hm & _).
apply cpg_val_mem1; [exact Hv | exact Hm].
Qed.
Lemma hd_garr8_zero : forall (W : world tfibsegs) mem q (n : nat),
(forall i, 0 <= i < Z.of_nat n -> aview tfibsegs (w_H W) mem (q + i) = Some 0) ->
garr8 tfibsegs (mrestrict (w_H W) mem) q (repeat 0 n).
Proof. intros W mem q n H. apply (hd_garr8_val W mem q n 0 H ltac:(lia)). Qed.
(* bytes whose view is kept keep their values (the image-A walk's am_garr8_kept) *)
Lemma bm_garr8_kept_x : forall H H' (m m' : word -> option byte) a l,
(forall x, a <= x < a + Z.of_nat (length l) -> aview tfibsegs H' m' x = aview tfibsegs H m x) ->
garr8 tfibsegs (mrestrict H m) a l -> garr8 tfibsegs (mrestrict H' m') a l.
Proof.
intros H H' m m' a l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (cw_val_mem_kept H H' m m'); [|exact Hv]. intros x Hx. apply Hk. cbn in Hx. lia.
Qed.
(* a call record whose 184 bytes are kept is the same record *)
Lemma hd_kcall_kept : forall (W W' : world tfibsegs) mem mem' q k,
kcall_atA tfibsegs W mem q k -> kcall_wfZ k ->
(forall x, q <= x < q + 184 -> aview tfibsegs (w_H W') mem' x = aview tfibsegs (w_H W) mem x) ->
kcall_atA tfibsegs W' mem' q k.
Proof.
intros W W' mem mem' q k
  (V0 & V8 & V16 & V24 & V28 & V32 & V36 & G40 & V64 & V72 & G76 & G108 & V140 & G144 & V168 & V176 & V180)
  (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Lb & Lbe & Lo & Lw) Hk.
unfold kcall_atA.
assert (KV : forall o' n v, 0 <= o' -> o' + Z.of_nat n <= 184 ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (q + o') n v -> val_mem tfibsegs (mrestrict (w_H W') mem') (q + o') n v).
{ intros o' n v H1 H2 Hv. apply (cw_val_mem_kept (w_H W) (w_H W') mem mem'); [|exact Hv].
  intros x Hx. apply Hk; lia. }
assert (KG : forall o' l, 0 <= o' -> o' + Z.of_nat (length l) <= 184 ->
  garr8 tfibsegs (mrestrict (w_H W) mem) (q + o') l -> garr8 tfibsegs (mrestrict (w_H W') mem') (q + o') l).
{ intros o' l H1 H2 Hg. apply (bm_garr8_kept_x (w_H W) (w_H W') mem mem'); [|exact Hg].
  intros x Hx. apply Hk; lia. }
split; [rewrite <- (Z.add_0_r q); apply KV; [lia | cbn; lia | rewrite Z.add_0_r; exact V0]|].
split; [apply KV; [lia | cbn; lia | exact V8]|].
split; [apply KV; [lia | cbn; lia | exact V16]|].
split; [apply KV; [lia | cbn; lia | exact V24]|].
split; [apply KV; [lia | cbn; lia | exact V28]|].
split; [apply KV; [lia | cbn; lia | exact V32]|].
split; [apply KV; [lia | cbn; lia | exact V36]|].
split; [apply KG; [lia | rewrite Lb; cbn; lia | exact G40]|].
split; [apply KV; [lia | cbn; lia | exact V64]|].
split; [apply KV; [lia | cbn; lia | exact V72]|].
split; [apply KG; [lia | rewrite Lbe; cbn; lia | exact G76]|].
split; [apply KG; [lia | rewrite Lo; cbn; lia | exact G108]|].
split; [apply KV; [lia | cbn; lia | exact V140]|].
split; [apply KG; [lia | rewrite Lw; cbn; lia | exact G144]|].
split; [apply KV; [lia | cbn; lia | exact V168]|].
split; [apply KV; [lia | cbn; lia | exact V176]|].
apply KV; [lia | cbn; lia | exact V180].
Qed.
End z.

(* ================================ the two calls inside HEAD ================================ *)
Section m. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section n.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws tfibsegs B.

(* a byte of the entry's own frame is none of the image's *)
Lemma hd_frame_not_img : forall pos F ly2 S2 (W2 : world tfibsegs) mem2 md2 a,
AR tfibsegs B ly2 S2 W2 mem2 md2 -> In (3, pos) (frames S2) -> frame_addr ly2 3 pos = F ->
F <= a < F + 512 -> in_img tfibsegs a -> False.
Proof using LAWS.
intros pos F ly2 S2 W2 mem2 md2 a HAR Hin EFA Ha Him.
pose proof (al_client_img _ _ LAWS ly2 S2 W2 mem2 md2 a HAR) as Hc.
apply Hc; [|exact Him]. right. left. exists 3, pos. split; [exact Hin|].
unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 3) with 512. lia.
Qed.

Lemma hd_hull_arith : forall F off n s,
F mod 64 = 0 -> 0 <= off -> 0 < n -> off + n <= 448 ->
(SHADOW_OFF + (F + off) / 8) / 8 * 8 <= s < (SHADOW_OFF + (F + off + n - 1) / 8) / 8 * 8 + 8 ->
0 <= s - (SHADOW_OFF + F / 8) < 56.
Proof.
intros F off n s H64 Hoff Hn Hon Hs.
assert (D64 : F = 64 * (F / 64)) by (pose proof (Z.div_mod F 64 ltac:(lia)) as D; lia).
assert (E8 : F / 8 = 8 * (F / 64)).
{ rewrite D64 at 1. replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by lia. apply Z.div_mul. lia. }
assert (DF : forall m, (F + m) / 8 = F / 8 + m / 8).
{ intros m. replace (F + m) with ((F / 8) * 8 + m) by lia. apply Z.div_add_l. lia. }
set (q := 268431360 + F / 64).
assert (EA : SHADOW_OFF + F / 8 = 8 * q) by (unfold q, SHADOW_OFF; lia).
rewrite (DF off) in Hs.
replace (F + off + n - 1) with (F + (off + n - 1)) in Hs by lia.
rewrite (DF (off + n - 1)) in Hs.
replace (SHADOW_OFF + (F / 8 + off / 8)) with (8 * q + off / 8) in Hs by lia.
replace (SHADOW_OFF + (F / 8 + (off + n - 1) / 8)) with (8 * q + (off + n - 1) / 8) in Hs by lia.
assert (R1 : (8 * q + off / 8) / 8 = q + off / 8 / 8)
  by (rewrite (Z.mul_comm 8 q); apply Z.div_add_l; lia).
assert (R2 : (8 * q + (off + n - 1) / 8) / 8 = q + (off + n - 1) / 8 / 8)
  by (rewrite (Z.mul_comm 8 q); apply Z.div_add_l; lia).
rewrite R1, R2 in Hs.
assert (P1 : 0 <= off / 8) by (apply Z.div_pos; lia).
assert (P2 : 0 <= off / 8 / 8) by (apply Z.div_pos; lia).
assert (P3 : 0 <= (off + n - 1) / 8) by (apply Z.div_pos; lia).
pose proof (Z.div_le_mono (off + n - 1) 447 8 ltac:(lia) ltac:(lia)) as A2.
change (447 / 8) with 55 in A2.
pose proof (Z.div_le_mono ((off + n - 1) / 8) 55 8 ltac:(lia) ltac:(lia)) as A3.
change (55 / 8) with 6 in A3.
lia.
Qed.

(* the shadow bytes of a range of the frame are readable (the cut's 60 shadow bytes cover their 8-byte hull) *)
Lemma hd_hull : forall B0 MT0 K0 XM0 g pos sp1 kv ly2 S2 (W2 : world tfibsegs) regs2 mem2 md2 off n,
mcommon B0 MT0 K0 XM0 g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 ->
0 <= off -> 0 < n -> off + n <= 448 ->
shadow_hull_vis (aview tfibsegs (w_H W2) mem2) (FA g pos + off) n.
Proof using.
intros B0 MT0 K0 XM0 g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 off n HC Hoff Hn Hon.
pose proof HC as HF64. do 14 (destruct HF64 as (_ & HF64)). destruct HF64 as (HF64 & _).
pose proof HC as HSH. do 47 (destruct HSH as (_ & HSH)). destruct HSH as (HSH' & _).
intros s Hs. unfold shadow_addr in Hs.
pose proof (hd_hull_arith (FA g pos) off n s HF64 Hoff Hn Hon Hs) as Hi.
replace s with (shadow_addr (FA g pos) + (s - (SHADOW_OFF + FA g pos / 8))) by (unfold shadow_addr; lia).
rewrite (HSH' (s - (SHADOW_OFF + FA g pos / 8)) ltac:(lia)).
discriminate.
Qed.

(* ---- a cut across a call (the image-A walk's am_call_kept) ---- *)
Lemma bm_call_kept_x : forall g pos sp1 kv ly2 S2 W2 regsc mem2 md2 kev c T (Ef : Z -> Prop)
ly3 S3 W3 regs3 mem3 md3 k3,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 kev ->
frames S2 = [(3, pos)] ->
mcommon B MT K XM_LIB g pos sp1 kv ly2 S2 W2 regsc mem2 md2 ->
cur_at g sp1 c W2 mem2 ->
(forall a, Ef a -> FA g pos + 192 <= a < FA g pos + 376) ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly3 S3 W3 mem3 md3 k3 ->
aregs_preserved regsc regs3 ->
Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) ->
tcj_kept tfibsegs B T ly2 S2 W2 mem2 W3 mem3 (spZ regsc) Ef ->
mcommon B MT K XM_LIB g pos sp1 kv ly3 S3 W3 regs3 mem3 md3 /\ cur_at g sp1 c W3 mem3 /\
(forall a, FA g pos <= a < FA g pos + 512 -> ~ Ef a ->
 aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W2) mem2 a).
Proof using LAWS.
intros g pos sp1 kv ly2 S2 W2 regsc mem2 md2 kev c T Ef ly3 S3 W3 regs3 mem3 md3 k3 HJ Hfr HC Hcur HEf HJ3 HPR HPerm HK.
destruct (bm_facts B MT K XM_LIB LAWS g pos sp1 kv ly2 S2 W2 regsc mem2 md2 kev HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hn & Hp & Hpn & Hblk).
pose proof HJ as (HAR & _).
assert (Hin : In (3, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
destruct (frames_bounds tfibsegs B LAWS ly2 S2 W2 mem2 md2 3 pos HAR Hin) as (_ & _ & Happ).
assert (E512 : fs_frame_bytes 3 = 512) by reflexivity.
rewrite EFA, E512 in Happ.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
destruct HC as (Hpre & Hsp1 & R2 & R9 & R8 & R3 & R4 & R21 & R18 & R27 & R23 & R25 & R19 & R26 & H64 &
  V16 & V24 & V32 & V40 & V48 & V56 & V64 & V72 & V80 & V88 & V96 & V104 & V112 & V120 & V128 & V136 & V144 & V152 &
  S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S96 & S104 & VFL & SHM & GIN & PERM).
assert (Usp : spZ regsc = sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; unfold BM_HI in *; lia).
rewrite Usp in HK. destruct HK as (K1 & _ & _ & K4 & _ & _).
set (F := FA g pos) in *.
(* the machine stack at or above sp1: kept by clause 1 *)
assert (KS : forall a, sp1 <= a < e_sp0 g -> aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W2) mem2 a).
{ intros a Ha. apply K1; [lia | lia | intros He; pose proof (HEf a He); unfold BM_HI in *; lia]. }
(* the frame and its shadow: kept by clause 4 off E *)
assert (KF : forall a, F <= a < F + 512 -> ~ Ef a -> aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W2) mem2 a).
{ intros a Ha He. apply (K4 3 pos a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFA, E512; lia | exact He]. }
assert (KSH : forall i, 0 <= i < 60 ->
  aview tfibsegs (w_H W3) mem3 (shadow_addr F + i) = aview tfibsegs (w_H W2) mem2 (shadow_addr F + i)).
{ intros i Hi. apply (K4 3 pos _ Hin).
  - right. unfold in_zr. cbn [fst snd]. rewrite EFA, E512. change (512 / 8) with 64. lia.
  - intros He. pose proof (HEf _ He) as Hr. unfold shadow_addr, SHADOW_OFF in Hr.
    pose proof (Z.div_mod F 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as M8.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. lia. }
assert (VK : forall a n v, sp1 <= a -> a + Z.of_nat n <= e_sp0 g ->
  val_mem tfibsegs (mrestrict (w_H W2) mem2) a n v -> val_mem tfibsegs (mrestrict (w_H W3) mem3) a n v).
{ intros a n v H1 H2 Hv. apply (cw_val_mem_kept (w_H W2) (w_H W3) mem2 mem3); [|exact Hv].
  intros x Hx. apply KS. lia. }
assert (P2 : getr regs3 2 = getr regsc 2) by exact (HPR 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : getr regs3 3 = getr regsc 3) by exact (HPR 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : getr regs3 4 = getr regsc 4) by exact (HPR 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs3 8 = getr regsc 8) by exact (HPR 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : getr regs3 9 = getr regsc 9) by exact (HPR 9 ltac:(unfold acallee_saved; lia)).
assert (P18 : getr regs3 18 = getr regsc 18) by exact (HPR 18 ltac:(unfold acallee_saved; lia)).
assert (P19 : getr regs3 19 = getr regsc 19) by exact (HPR 19 ltac:(unfold acallee_saved; lia)).
assert (P21 : getr regs3 21 = getr regsc 21) by exact (HPR 21 ltac:(unfold acallee_saved; lia)).
assert (P23 : getr regs3 23 = getr regsc 23) by exact (HPR 23 ltac:(unfold acallee_saved; lia)).
assert (P25 : getr regs3 25 = getr regsc 25) by exact (HPR 25 ltac:(unfold acallee_saved; lia)).
assert (P26 : getr regs3 26 = getr regsc 26) by exact (HPR 26 ltac:(unfold acallee_saved; lia)).
assert (P27 : getr regs3 27 = getr regsc 27) by exact (HPR 27 ltac:(unfold acallee_saved; lia)).
pose proof Hcur as (Hc & C184 & C192).
split; [|split].
- refine (conj Hpre (conj Hsp1 _)).
  rewrite P2, P9, P8, P3, P4, P21, P18, P27, P23, P25, P19, P26.
  refine (conj R2 (conj R9 (conj R8 (conj R3 (conj R4 (conj R21 (conj R18 (conj R27 (conj R23 (conj R25
    (conj R19 (conj R26 (conj H64 _))))))))))))).
  split; [apply VK; [lia | cbn; lia | exact V16]|].
  split; [apply VK; [lia | cbn; lia | exact V24]|].
  split; [apply VK; [lia | cbn; lia | exact V32]|].
  split; [apply VK; [lia | cbn; lia | exact V40]|].
  split; [apply VK; [lia | cbn; lia | exact V48]|].
  split; [apply VK; [lia | cbn; lia | exact V56]|].
  split; [apply VK; [lia | cbn; lia | exact V64]|].
  split; [apply VK; [lia | cbn; lia | exact V72]|].
  split; [apply VK; [lia | cbn; lia | exact V80]|].
  split; [apply VK; [lia | cbn; lia | exact V88]|].
  split; [apply VK; [lia | cbn; lia | exact V96]|].
  split; [apply VK; [lia | cbn; lia | exact V104]|].
  split; [apply VK; [lia | cbn; lia | exact V112]|].
  split; [apply VK; [lia | cbn; lia | exact V120]|].
  split; [apply VK; [lia | cbn; lia | exact V128]|].
  split; [apply VK; [lia | cbn; lia | exact V136]|].
  split; [apply VK; [lia | cbn; lia | exact V144]|].
  split; [apply VK; [lia | cbn; lia | exact V152]|].
  split; [apply VK; [lia | cbn; lia | exact S8]|].
  split; [apply VK; [lia | cbn; lia | exact S16]|].
  split; [apply VK; [lia | cbn; lia | exact S24]|].
  split; [apply VK; [lia | cbn; lia | exact S32]|].
  split; [apply VK; [lia | cbn; lia | exact S40]|].
  split; [apply VK; [lia | cbn; lia | exact S48]|].
  split; [apply VK; [lia | cbn; lia | exact S56]|].
  split; [apply VK; [lia | cbn; lia | exact S64]|].
  split; [apply VK; [lia | cbn; lia | exact S72]|].
  split; [apply VK; [lia | cbn; lia | exact S80]|].
  split; [apply VK; [lia | cbn; lia | exact S88]|].
  split; [apply VK; [lia | cbn; lia | exact S96]|].
  split; [apply VK; [lia | cbn; lia | exact S104]|].
  split.
  { apply (cw_val_mem_kept (w_H W2) (w_H W3) mem2 mem3); [|exact VFL].
    intros x Hx. cbn in Hx. apply KF; [lia|]. intros He. pose proof (HEf x He). lia. }
  pose proof Hpre as Hpre'. unfold e_pre, codec_lib_pre_x in Hpre'.
  destruct Hpre' as (_ & _ & _ & _ & _ & Hnpl & _).
  split; [intros i Hi; etransitivity; [exact (KSH i Hi) | exact (SHM i Hi)]|].
  split; [|exact (Permutation_trans HPerm PERM)].
  destruct (Z.eq_dec (e_n g) 0) as [Hn0 | Hn0].
  + intros j Hj. exfalso. rewrite length_map in Hj. lia.
  + destruct (Hblk ltac:(lia)) as (Hb2 & Hb0).
    assert (Hb3 : In (e_p g, e_n g) (ablocks B ly3 S3))
      by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | exact Hb2]).
    pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & J2 & _).
    pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & J3 & _).
    pose proof (req_size_pos (e_n g) ltac:(lia)) as (_ & Hrq).
    apply (bm_garr8_kept_x (w_H W2) (w_H W3) mem2 mem3); [|exact GIN].
    intros x Hx. rewrite length_map in Hx.
    replace x with (e_p g + (x - e_p g)) by lia.
    rewrite (J3 (e_p g) (e_n g) (x - e_p g) Hb0 Hb3 ltac:(lia) (inFP_nil _)).
    rewrite (J2 (e_p g) (e_n g) (x - e_p g) Hb0 Hb2 ltac:(lia) (inFP_nil _)). reflexivity.
- split; [exact Hc|]. split; [apply VK; [lia | cbn; lia | exact C184] | apply VK; [lia | cbn; lia | exact C192]].
- exact KF.
Qed.

(* ---- the checked memset of a range of the frame (0x80cd8 and 0x80da0) ---- *)
Hypothesis AMEMSET : aintrin_realizes tfibsegs B OSet BM_asan_memset.
Lemma hd_memset_at : forall (Q : world tfibsegs -> config -> Prop) g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 c off n x retpc,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 0 ->
frames S2 = [(3, pos)] ->
mcommon B MT K XM_LIB g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 ->
cur_at g sp1 c W2 mem2 ->
getr regs2 10 = w64 (FA g pos + off) -> getr regs2 11 = w64 x -> getr regs2 12 = w64 n ->
0 <= x < 2 ^ 64 -> 0 < n < 2 ^ 32 -> 192 <= off -> off + n <= 376 ->
getr regs2 1 = w64 retpc -> YK0s.ret_ok (w64 retpc) -> 0 <= retpc < 2 ^ 64 ->
range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (FA g pos + off) n ->
(forall regs3 mem3 md3,
 ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem3 md3 0 ->
 mcommon B MT K XM_LIB g pos sp1 kv ly2 S2 W2 regs3 mem3 md3 ->
 cur_at g sp1 c W2 mem3 ->
 aregs_preserved regs2 regs3 ->
 (forall i, 0 <= i < n -> aview tfibsegs (w_H W2) mem3 (FA g pos + off + i) = Some (x mod 256)) ->
 (forall a, FA g pos <= a < FA g pos + 512 -> ~ (FA g pos + off <= a < FA g pos + off + n) ->
    aview tfibsegs (w_H W2) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
 SRr tfibsegs W2 (cfg_at tfibsegs retpc regs3 mem3 md3) Q) ->
SRr tfibsegs W2 (cfg_at tfibsegs BM_asan_memset regs2 mem2 md2) Q.
Proof using LAWS AMEMSET.
intros Q g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 c off n x retpc
  HJ Hfr HC Hcur H10 H11 H12 Hx Hn Hoff Hon H1 Hret Hretr HBS CONT.
destruct (bm_facts B MT K XM_LIB LAWS g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 0 HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hng & Hpg & Hpng & Hblk).
unfold BM_HI in Hchi.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & _).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
assert (Hin : In (3, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
destruct (frames_bounds tfibsegs B LAWS ly2 S2 W2 mem2 md2 3 pos HAR Hin) as (_ & _ & Happ).
rewrite EFA in Happ. change (fs_frame_bytes 3) with 512 in Happ.
pose proof HC as (_ & _ & R2 & _ & _ & R3 & R4 & _).
assert (Usp : spZ regs2 = sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (Hamr : amem_range (FA g pos + off) n).
{ unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
  unfold kLowMemEnd, kHighMemBeg, kHighMemEnd. destruct Happ as (_ & [Hlo | (Hh1 & Hh2)]); [left; lia | right; lia]. }
unfold cfg_at. change (w64 BM_asan_memset) with (Z_to_bv 64 BM_asan_memset).
eapply SRr_bind.
{ eapply (aj_intrin_atS tfibsegs B LAWS tfib_segs_low OSet BM_asan_memset AMEMSET W2 regs2 mem2 LLVMF_STK (e_sp0 g) []
    (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 md2 0 (FA g pos + off) x n (sp1 - e_sp0 g) (w64 retpc)).
  - exact HJ.
  - exact H10.
  - exact H11.
  - exact H12.
  - lia.
  - lia.
  - lia.
  - rewrite Usp. lia.
  - assert (H16 : sp1 mod 16 = 0).
    { pose proof (Z.div_mod sp1 32 ltac:(lia)) as D. rewrite Hsp32, Z.add_0_r in D.
      replace sp1 with ((2 * (sp1 / 32)) * 16) by lia. apply Z_mod_mult. }
    rewrite Zminus_mod, Hsp016, H16. reflexivity.
  - lia.
  - unfold ESTACK. lia.
  - exact R3.
  - exact R4.
  - exact H1.
  - exact Hret.
  - intros a Ha. split.
    + right. right. right. exists 3, pos. split; [left; reflexivity|]. left.
      unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 3) with 512. lia.
    + replace (e_sp0 g + (sp1 - e_sp0 g)) with sp1 by lia. unfold ESTACK. lia.
  - exact Hamr.
  - exact HBS.
  - intros _. exact (hd_hull B MT K XM_LIB g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 off n HC ltac:(lia) ltac:(lia) ltac:(lia)).
  - exact I. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HPR & Ha0 & Hset & Hkeep & Hpres2 & Hsame).
replace (e_sp0 g + (sp1 - e_sp0 g)) with sp1 in Hkeep by lia.
(* what the call kept, in the walk's form *)
assert (KT0 : tcj_kept tfibsegs B 4096 ly2 S2 W2 mem2 W2 mem2 sp1 (fun a => FA g pos + off <= a < FA g pos + off + n))
  by exact (cw_kept0 B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)]
              ly2 S2 W2 mem2 md2 0 sp1 4096 _ HJ ltac:(lia) ltac:(lia)).
assert (KT : tcj_kept tfibsegs B 4096 ly2 S2 W2 mem2 W2 mem3 sp1 (fun a => FA g pos + off <= a < FA g pos + off + n)).
{ apply (cw_kept_step B LAWS 4096 ly2 S2 W2 mem2 md2 W2 mem2 mem3 sp1 _
    (fun a => (FA g pos + off <= a < FA g pos + off + n) \/ (sp1 - ESTACK <= a < sp1))
    ltac:(unfold ESTACK; lia) HAR KT0).
  - intros a Ha Hz. apply Hkeep; [exact Ha | intros X; apply Hz; left; exact X | intros X; apply Hz; right; exact X].
  - intros a [Ha | Ha]; [right; left; split; [exact Ha|] | left; unfold ESTACK in Ha; lia].
    intros Him. exact (hd_frame_not_img pos (FA g pos) ly2 S2 W2 mem2 md2 a HAR Hin EFA ltac:(lia) Him).
  - exact Hpres2. }
rewrite <- Usp in KT.
destruct (bm_call_kept_x g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 0 c 4096
  (fun a => FA g pos + off <= a < FA g pos + off + n) ly2 S2 W2 regs3 mem3 md3 0
  HJ Hfr HC Hcur ltac:(intros a Ha; cbv beta in Ha; lia) HJ3 HPR (Permutation_refl _) KT) as (HC3 & Hcur3 & KF).
apply (CONT regs3 mem3 md3 HJ3 HC3 Hcur3 HPR).
- intros i Hi. exact (Hset i Hi).
- intros a Ha Hna. exact (KF a Ha Hna).
Qed.

(* ---- the call of diginet_personality_of (0x80d50) ---- *)
Hypothesis POF : cdcU_pers_of_specX tfibsegs B MT BM_pers_of CB_PERS.
Lemma hd_pof_at : forall (Q : world tfibsegs -> config -> Prop) g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 c d retpc,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 0 ->
frames S2 = [(3, pos)] -> mo_le MT (e_S g) S2 0 ->
mcommon B MT K XM_LIB g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 ->
cur_at g sp1 c W2 mem2 ->
getr regs2 10 = w64 d -> 0 <= d < 2 ^ 64 ->
getr regs2 1 = w64 retpc -> YK0s.ret_ok (w64 retpc) -> 4096 <= retpc < 2 ^ 64 ->
(forall (W3 : world tfibsegs) ly3 S3 regs3 mem3 md3,
 ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly3 S3 W3 mem3 md3 0 ->
 frames S3 = [(3, pos)] -> mo_le MT (e_S g) S3 0 ->
 mcommon B MT K XM_LIB g pos sp1 kv ly3 S3 W3 regs3 mem3 md3 ->
 cur_at g sp1 c W3 mem3 ->
 aregs_preserved regs2 regs3 ->
 getr regs3 10 = w64 (pers_ofA CB_PERS d) ->
 (forall a, FA g pos <= a < FA g pos + 512 -> aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
 SRr tfibsegs W3 (cfg_at tfibsegs retpc regs3 mem3 md3) Q) ->
SRr tfibsegs W2 (cfg_at tfibsegs BM_pers_of regs2 mem2 md2) Q.
Proof using MTL LAWS POF.
intros Q g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 c d retpc HJ Hfr Hmo HC Hcur H10 Hd H1 Hret Hretr CONT.
destruct (bm_facts B MT K XM_LIB LAWS g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 0 HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hng & Hpg & Hpng & Hblk).
unfold BM_HI in Hchi.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & _).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
pose proof HC as (Hpre & _ & R2 & _ & _ & R3 & R4 & _).
pose proof HC as HPerm0. do 49 (destruct HPerm0 as (_ & HPerm0)).
assert (Usp : spZ regs2 = sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (Hal16 : spZ regs2 mod 16 = 0).
{ rewrite Usp. pose proof (Z.div_mod sp1 32 ltac:(lia)) as D. rewrite Hsp32, Z.add_0_r in D.
  replace sp1 with ((2 * (sp1 / 32)) * 16) by lia. apply Z_mod_mult. }
pose proof Hpre as HPRE. unfold e_pre, codec_lib_pre_x in HPRE.
destruct HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & Hev & Hlive & _).
assert (HENT : cdc_entry tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
  [(3, pos)] ly2 S2 W2 mem2 md2 0 regs2 TB_pers_of).
{ eapply (cpw_entry B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)]
    (e_ly g) (e_S g) ly2 S2 W2 mem2 md2 0 regs2 TB_pers_of HJ).
  - rewrite H1. exact Hret.
  - unfold raZ. rewrite H1. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - exact R3.
  - exact R4.
  - exact Hal16.
  - rewrite Usp. unfold TB_pers_of. lia.
  - rewrite Usp. lia.
  - unfold EV_CDC. unfold EV_LIB in Hev. lia.
  - exact HPerm0.
  - unfold LIVE_CDC. unfold LIVE_LIB in Hlive. lia. }
unfold cfg_at. change (w64 BM_pers_of) with (Z_to_bv 64 BM_pers_of).
eapply SRr_bind.
{ change (Z_to_bv 64 BM_pers_of) with (w64 BM_pers_of).
  exact (POF LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 0
           regs2 d HENT H10 Hd). }
cbv beta. intros W3 c3 Hwle (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HPR & Hfrs3 & HPerm3 & Hio3 & Hmo3 & KTc & HRc).
unfold EV_CDC in HJ3. rewrite Z.add_0_r in HJ3.
rewrite H1 in *.
assert (Hfr3 : frames S3 = [(3, pos)]) by (rewrite Hfrs3; exact Hfr).
destruct (bm_call_kept_x g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 0 c TB_pers_of
  cno_wr ly3 S3 W3 regs3 mem3 md3 0 HJ Hfr HC Hcur ltac:(intros a []) HJ3 HPR HPerm3 KTc) as (HC3 & Hcur3 & KF).
assert (Hmo3' : mo_le MT (e_S g) S3 0)
  by (pose proof (mle_station _ _ _ _ 0 0 MTL Hmo Hmo3) as X; rewrite Z.add_0_r in X; exact X).
change (mkCfg (mkst regs3 (w64 retpc) mem3 (seg_rom tfibsegs)) md3)
  with (cfg_at tfibsegs retpc regs3 mem3 md3).
apply (CONT W3 ly3 S3 regs3 mem3 md3 HJ3 Hfr3 Hmo3' HC3 Hcur3 HPR HRc).
intros a Ha. exact (KF a Ha ltac:(intros [])).
Qed.
End n.
End m.
