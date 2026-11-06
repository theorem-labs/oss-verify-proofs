(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of proofs/reac-pw/fuzz_role/lib/A/RPgX01.v at 9bffaa83ff88
   [Apache-2.0] (rx_reg_atom / rx_reg_ext / rx_ew_reg / rx_st_region / rx_chunk_zero / rx_flag0_of, the saved-slot
   chunk list rx_sv_chunks, the numeral tactics z5 / z5g and the flag-store tactic rx_run_flag, which passes
   aj_flag_store its sixteen journal arguments) and of proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018
   [Apache-2.0] (the shape of a `ret` leaf into a callee post), for reac-pw/fuzz_rate's image A: the walk is
   check_csv's release and epilogue, the side-stack class is 2 instead of 3, and the post is RtPgCSpec.rt_cpost_o,
   whose owned-set conjunct is discharged from the cut's layout, chunk and frame equalities. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCcsvS3.v, with its module names changed; 710 of its 748 lines of code are new or changed and 288 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW7bWalk.v at 7ef0f92b27f1 for the same unit's image B (fuzz_rate.asan-ubsan): the image is images.AsanUbsan; the pcs, the registers of G and J, the real-frame cells (parts at R+0x198 .., e62.body at R+0x130, &e62 at R+0x150, &pp->len at R+0x158, ~(F + 0x218) at R+0x100, the cursor at R+0x128) and the class-4 frame for locals (1024 bytes, 88 pattern granules, e62 at F+0x210) are image B's; the blocks are lib/AU/RtPgW7b{BlkAB,BlkA2B,BlkBB,E2B,IterB}.v; E1 also reloads the two J registers and steps over image B's UBSan test; the memory, step and cut names are lib/AU/RtPgMemB.v, RtPgStepsB.v and RtPgSegB.v's; the prefix w7_ becomes w7b_. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; addresses measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1): the walk of LLVMFuzzerTestOneInput from G
   0x8160c (ent_build case 0 after the digits, the reverse and the odd_ch part, pod.h:250) to J 0x820dc (the pod is
   built), composed from its blocks (lib/AU/RtPgW7bBaseB.v: A1, A2, the four parts, D, the memcpy into e62.body, E1,
   E2). Proves no function (kind: segment lemma).

   THE STATE AT G is given as explicit facts (the Section's hypotheses): the registers the code reads, the real-frame
   cells it reads, the bytes of ch (the key's first part with its NUL), the 104 zero bytes of e62, the frame's shadow
   rsb_PG, the param table cell and its shadow, the three read-only strings (HPFX, the separator, param[p % 8]) and
   the read-only bytes as the image's. THE FOUR PARTS (pod.h:254-259): part i is the string at w7b_xs[i] with the
   bytes w7b_ss[i]; a turn (w7b_part, then w7b_next for i < 3) runs strlen, the clamp that never cuts
   (n + l <= 44 < 95) and memcpy(t + n, part, l); w7b_inv i is the state at the strlen entry of part i, w7b_mid i the
   state after its memcpy. The bytes written before J: the parts cells [R+0x198, R+0x1b8), t's first n bytes, the
   callees' stack below R; then e62.body, its NUL, e62.type and e62.size, and the 15 shadow bytes of t and ch. The
   post at J: the registers J reads, e62 holding Layout.ent_mem of the key's pod (ent_text of HPFX ++ chs ++ sep ++
   param[p % 8] with its NUL) and the frame's shadow rsb_PJ. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgMemB RtPgSegB RtPgStepsB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgW7bBaseB RtPgW7bBlkAB RtPgW7bBlkA2B RtPgW7bBlkBB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgW7bKitB RtPgW7bCallB RtPgW7bFactsB RtPgW7bIterB RtPgW7bE2B.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ======================================== small helpers ======================================== *)
Ltac w7b_bvu := repeat lazymatch goal with |- context [bv_unsigned ?x] =>
  let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end.
Ltac w7b_nz := w7b_bvu; discriminate.
Ltac w7b_notin := let H := fresh "H" in intros H; cbv [rtsb_caller_saved app In] in H;
  repeat (destruct H as [H|H]; [apply (f_equal (@bv_unsigned 5)) in H; vm_compute in H; discriminate H|]); exact H.
Ltac w7b_incl := let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; cbv [rtsb_caller_saved app In] in Hx |- *;
  repeat (destruct Hx as [<-|Hx]; [repeat (first [left; reflexivity | right]) |]); destruct Hx.
Ltac w7b_cs := unfold acallee_saved; w7b_bvu; lia.

Lemma w7b_notin_incl : forall (l1 l2 : list (bv 5)) r, incl l1 l2 -> ~ In r l2 -> ~ In r l1.
Proof. intros l1 l2 r Hi Hn X. exact (Hn (Hi r X)). Qed.
Lemma w7b_cs22 : forall (regs regs' : bvmap 5 word) (r : bv 5),
(forall z, acallee_saved z -> z <> 22 -> getr regs' (Z_to_bv 5 z) = getr regs (Z_to_bv 5 z)) ->
acallee_saved (bv_unsigned r) -> bv_unsigned r <> 22 -> getr regs' r = getr regs r.
Proof. intros regs regs' r H H1 H2. rewrite <- (Z_to_bv_bv_unsigned 5 r). apply H; assumption. Qed.
Lemma w7b_csp : forall (regs regs' : bvmap 5 word) (r : bv 5),
aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) -> getr regs' r = getr regs r.
Proof. intros regs regs' r H H1. rewrite <- (Z_to_bv_bv_unsigned 5 r). apply H; assumption. Qed.
(* a register outside a list containing 22 is not 22 *)
Lemma w7b_cs_not22 : forall (r : bv 5) (l : list (bv 5)), In 22%bv l -> ~ In r l -> bv_unsigned r <> 22.
Proof.
intros r l H22 Hn E. assert (Er : r = 22%bv) by (apply bv_eq; rewrite E; reflexivity). subst r. exact (Hn H22).
Qed.

(* a present byte reads as something *)
Lemma w7b_ap_av : forall {fx : YK11.FPState} (H : word -> bool) mem a, apresent H mem a -> aview rsegs H mem a <> None.
Proof.
intros fx H mem a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate.
Qed.

(* a slice of zero bytes is zero bytes *)
Lemma w7b_slice_zeros : forall m o n, (o + n <= m)%nat -> rtmb_slice (zeros m) o n = zeros n.
Proof.
unfold rtmb_slice, zeros. intros m o. revert m. induction o as [|o IH]; intros m n H.
- change (skipn 0 (repeat NUL m)) with (repeat NUL m). revert m H. induction n as [|n IHn]; intros m H; [reflexivity|].
  destruct m as [|m]; [lia|]. cbn [repeat firstn]. f_equal. apply IHn. lia.
- destruct m as [|m]; [lia|]. cbn [repeat skipn]. apply IH. lia.
Qed.

(* the shadow hull of an address range below kHighMemEnd lies in the shadow band [kLowMemEnd, kHighMemBeg) *)
Lemma w7b_hull_band : forall x n a, 0 <= x -> 0 <= x + n - 1 -> x + n - 1 < kHighMemEnd -> w7b_hull x n a ->
kLowMemEnd <= a < kHighMemBeg.
Proof.
intros x n a Hx Hn Hh [H1 H2]. unfold shadow_addr, SHADOW_OFF in H1, H2. unfold kLowMemEnd, kHighMemBeg.
unfold kHighMemEnd in Hh.
assert (D1 : 0 <= x / 8) by (apply Z.div_pos; lia).
assert (D2 : (x + n - 1) / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
assert (D3 : 0 <= (x + n - 1) / 8) by (apply Z.div_pos; lia).
pose proof (Z.div_mod (2147450880 + x / 8) 8 ltac:(lia)) as E1.
pose proof (Z.mod_pos_bound (2147450880 + x / 8) 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (2147450880 + (x + n - 1) / 8) 8 ltac:(lia)) as E2.
pose proof (Z.mod_pos_bound (2147450880 + (x + n - 1) / 8) 8 ltac:(lia)) as M2.
lia.
Qed.

(* the shadow hull of an object at F + o (32 <= o, o + n <= 648) of the frame for locals lies inside its 88 pattern
   shadow bytes, so a frame shadow pattern makes it visible *)
Lemma w7b_hull_fsh : forall {fx : YK11.FPState} H mem F pat o n,
rt_fsh rsegs H mem F pat -> (88 <= length pat)%nat -> F mod 32 = 0 -> 0 <= F -> 32 <= o -> 0 < n -> o + n <= 648 ->
shadow_hull_vis (aview rsegs H mem) (F + o) n.
Proof.
intros fx H mem F pat o n P Hl HF HF0 Ho Hn Hon s Hs.
rewrite (rtsb_fsh_addr F o HF ltac:(lia)) in Hs. replace (F + o + n - 1) with (F + (o + n - 1)) in Hs by lia.
rewrite (rtsb_fsh_addr F (o + n - 1) HF ltac:(lia)) in Hs.
destruct (rtsb_fdiv F HF) as [_ E]. rewrite E in Hs. unfold SHADOW_OFF in Hs.
set (q := F / 32) in *.
assert (Ho8 : 4 <= o / 8) by (apply Z.div_le_lower_bound; lia).
assert (Hn8 : (o + n - 1) / 8 < 81) by (apply Z.div_lt_upper_bound; lia).
assert (Hoo : o / 8 <= (o + n - 1) / 8) by (apply Z.div_le_mono; lia).
pose proof (Z.div_mod (2147450880 + 4 * q + o / 8) 8 ltac:(lia)) as E1.
pose proof (Z.mod_pos_bound (2147450880 + 4 * q + o / 8) 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (2147450880 + 4 * q + (o + n - 1) / 8) 8 ltac:(lia)) as E2.
pose proof (Z.mod_pos_bound (2147450880 + 4 * q + (o + n - 1) / 8) 8 ltac:(lia)) as M2.
assert (Hi : 0 <= s - shadow_addr F < 88).
{ rewrite E. unfold SHADOW_OFF. lia. }
pose proof (P (s - shadow_addr F) ltac:(lia)) as V. replace (shadow_addr F + (s - shadow_addr F)) with s in V by lia.
rewrite V. discriminate.
Qed.

Lemma w7b_pptr_rng : forall j, 0 <= j < 8 -> 0x212e0 <= w7b_pptr j <= 0x214e0.
Proof.
intros j Hj. assert (E : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7) by lia.
destruct E as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; split; discriminate.
Qed.
Lemma w7b_sep_rng : forall p, w7b_sep p = 0x212e0 \/ w7b_sep p = 0x21500.
Proof. intros p. unfold w7b_sep. destruct (Z.testbit p 7); auto. Qed.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section w.
Variable B : asyms.
Hypothesis LAWS : AR_laws rsegs B.
Hypothesis ASTRLEN : w7b_astrlen_realizes rsegs B W7B_STRLEN.
Hypothesis AMEMCPY : aintrin_realizes rsegs B OCpy W7B_MEMCPY.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (Sa : astate) (W0 : world rsegs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world rsegs)
  (k : Z) (regsG : bvmap 5 word) (memG : word -> option byte) (mdG : Model)
  (R F pos cur left pb v158 v100 : Z) (chs : list byte).
(* the journal at G *)
Hypothesis HJ : ajournal rsegs B STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W memG mdG k.
(* the registers G's walk reads: sp, gp, tp, s1 = R, s2 = &ch, s3 = shF, s4 = K, s9 = p, s11 = &t, t1 = what is
   left *)
Hypothesis G2 : getr regsG 2 = w64 R.
Hypothesis G3 : getr regsG 3 = w64 (as_gp B).
Hypothesis G4 : getr regsG 4 = w64 (as_tp B).
Hypothesis G9 : getr regsG 9 = w64 R.
Hypothesis G18 : getr regsG 18 = w64 (F + 0xa0).
Hypothesis G19 : getr regsG 19 = w64 (shadow_addr F).
Hypothesis G20 : getr regsG 20 = w64 SHADOW_OFF.
Hypothesis G25 : getr regsG 25 = w64 pb.
Hypothesis G27 : getr regsG 27 = w64 (F + 0x20).
Hypothesis G6 : getr regsG 6 = w64 left.
(* the real frame, the caller's stack window and the frame for locals (a class-4 side-stack frame the harness holds) *)
Hypothesis HR0 : 0x7fff7f800000 <= R.
Hypothesis HRs : R + 0x220 <= sp0.
Hypothesis Hsp47 : sp0 <= 2 ^ 47.
Hypothesis HR16 : R mod 16 = 0.
Hypothesis Hs16 : sp0 mod 16 = 0.
Hypothesis HSTK : sp0 - STK <= R - 16384.
Hypothesis HFR : F + 1024 <= R - 16384.
Hypothesis Hown : In (4, pos) own.
Hypothesis HFa : frame_addr lyc 4 pos = F.
(* p and the key's first part *)
Hypothesis Hpb : 0 <= pb < 256.
Hypothesis Hchs : (length chs <= 21)%nat.
Hypothesis Hchz : Forall (fun b : byte => bv_unsigned b <> 0) chs.
(* the bytes and cells at G *)
Hypothesis Hch : rtmb_bytes rsegs (w_H W) memG (F + 0xa0) (chs ++ [NUL]).
Hypothesis He0 : rtmb_bytes rsegs (w_H W) memG (F + 0x210) (zeros 104).
Hypothesis Hsh : rt_fsh rsegs (w_H W) memG F rsb_PG.
Hypothesis Hc130 : val_mem rsegs (mrestrict (w_H W) memG) (R + 0x130) 8 (F + 0x218).
Hypothesis Hc150 : val_mem rsegs (mrestrict (w_H W) memG) (R + 0x150) 8 (F + 0x210).
Hypothesis Hc158 : val_mem rsegs (mrestrict (w_H W) memG) (R + 0x158) 8 v158.
Hypothesis Hc100 : val_mem rsegs (mrestrict (w_H W) memG) (R + 0x100) 8 v100.
Hypothesis Hc128 : val_mem rsegs (mrestrict (w_H W) memG) (R + 0x128) 8 cur.
Hypothesis Hv158 : 0 <= v158 < 2 ^ 64.
Hypothesis Hv100 : 2 ^ 63 <= v100 < 2 ^ 64.
Hypothesis Hcur : 0 <= cur < 2 ^ 64.
Hypothesis Hpcell : val_mem rsegs (mrestrict (w_H W) memG) (W7B_PTAB pb) 8 (w7b_pptr (pb mod 8)).
Hypothesis Hpra : range_addressable (aview rsegs (w_H W) memG) SHADOW_OFF (W7B_PTAB pb) 8.
Hypothesis Hra1a0 : range_addressable (aview rsegs (w_H W) memG) SHADOW_OFF (R + 0x1a0) 8.
Hypothesis Hcs0 : rt_cstr rsegs (w_H W) memG 0x20fe0 (map (fun b : byte => bv_unsigned b) HPFX).
Hypothesis Hcs2 : rt_cstr rsegs (w_H W) memG (w7b_sep pb) (map (fun b : byte => bv_unsigned b) (w7b_sepb pb)).
Hypothesis Hcs3 : rt_cstr rsegs (w_H W) memG (w7b_pptr (pb mod 8)) (map (fun b : byte => bv_unsigned b) (w7b_pab pb)).
Hypothesis Hro : w7b_aro_unowned rsegs B (aview rsegs (w_H W) memG).

(* ---------------- the four parts ---------------- *)
Definition w7b_xs : list Z := [0x20fe0; F + 0xa0; w7b_sep pb; w7b_pptr (pb mod 8)].
Definition w7b_ss : list (list byte) := [HPFX; chs; w7b_sepb pb; w7b_pab pb].
Definition w7b_pre (i : nat) : list byte := concat (firstn i w7b_ss).
(* the bytes the parts' turns may write: the callees' stack below R, the parts cells, t *)
Definition w7b_Zm (a : Z) : Prop := R - 2 * ESTACK <= a < R \/ R + 0x198 <= a < R + 0x1b8 \/ F + 0x20 <= a < F + 0x80.
(* the registers the walk may change: the caller-saved ones and s2, s6, s8, s9, s10 *)
Definition w7b_clob : list (bv 5) := rtsb_caller_saved ++ [18; 22; 24; 25; 26]%bv.
Definition w7b_WrW (a : Z) : Prop :=
R - 2 * ESTACK <= a < R \/ R + 0x198 <= a < R + 0x1b8 \/ F + 0x20 <= a < F + 0x80 \/ F + 0x210 <= a < F + 0x278 \/
shadow_addr F + 4 <= a < shadow_addr F + 23.
Definition w7b_RJ (regs3 : bvmap 5 word) (mem3 : word -> option byte) : Prop :=
getr regs3 18 = w64 v158 /\ getr regs3 22 = w64 (F + 0x210) /\ getr regs3 26 = w64 cur /\ getr regs3 6 = w64 left /\
rtmb_bytes rsegs (w_H W) mem3 (F + 0x210) (ent_mem (ent_text (w7b_js chs pb) true)) /\
rt_fsh rsegs (w_H W) mem3 F rsb_PJ.

(* ---------------- facts of the frame and of the image ---------------- *)
Lemma w7b_fr : F mod 32 = 0 /\ in_app F 1024 /\ (forall a, F <= a < F + 1024 -> apresent (w_H W) memG a) /\
(forall a, F <= a < F + 1024 -> ~ in_img rsegs a).
Proof.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (M & A & P & _).
rewrite HFa in M, A, P. change (fs_frame_bytes 4) with 1024 in A, P.
split; [exact M|]. split; [exact A|]. split; [intros a Ha; exact (proj1 (P a Ha))|].
intros a Ha.
assert (Hc : exists cid pos', In (cid, pos') (frames Sc) /\
  frame_addr lyc cid pos' <= a < frame_addr lyc cid pos' + fs_frame_bytes cid).
{ exists 4, pos. split; [exact Hin|]. rewrite HFa. change (fs_frame_bytes 4) with 1024. lia. }
destruct (al_client_img _ _ LAWS _ _ _ _ _ a HAR (or_intror (or_introl Hc))) as [_ Hni]. exact Hni.
Qed.

Lemma w7b_fb : 4096 <= F /\ F + 1024 <= alloc_ceiling /\ 0 <= shadow_addr F /\
(F + 1024 <= shadow_addr F \/ shadow_addr F + 128 <= F) /\
(forall o n, 0 <= o -> 0 <= n -> o + n < 1024 -> amem_range (F + o) n).
Proof.
destruct w7b_fr as (M & A & _). destruct (rtsb_fbounds F M A) as (B1 & B2 & B3 & _ & B5 & B6). tauto.
Qed.

(* a shadow byte of an address of the image or of the frame lies in the shadow band, so it is no byte of the
   frame, of the stack window or of the real frame *)
Lemma w7b_band_out : forall a, kLowMemEnd <= a < kHighMemBeg ->
~ (F <= a < F + 1024) /\ a < R - 2 * ESTACK.
Proof.
intros a Ha. destruct w7b_fr as (_ & A & _). unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
unfold kLowMemEnd, kHighMemBeg in Ha. unfold ESTACK. split; lia.
Qed.

Lemma w7b_shF_band : forall i, 0 <= i < 128 -> kLowMemEnd <= shadow_addr F + i < kHighMemBeg.
Proof.
intros i Hi. destruct w7b_fb as (B1 & _).
unfold shadow_addr, SHADOW_OFF, kLowMemEnd, kHighMemBeg.
assert (0 <= F / 8) by (apply Z.div_pos; lia).
assert (F / 8 <= 2 ^ 44 - 128) by (apply Z.div_le_upper_bound; lia). lia.
Qed.

Lemma w7b_rom_out : forall a, in_rom rsegs a -> ~ w7b_Zm a.
Proof.
intros a Ha. pose proof (w7b_in_rom_low a Ha) as L. destruct w7b_fr as (_ & _ & _ & Ni).
assert (Hi : in_img rsegs a) by (destruct Ha as (sg & Hs & _ & Hb); exists sg; split; [exact Hs | exact Hb]).
unfold w7b_Zm, kLowMemEnd, ESTACK in *. intros [X|[X|X]]; [lia | lia | exact (Ni a ltac:(lia) Hi)].
Qed.

(* a read-only string of the image lies on one side of t: the frame holds no image byte *)
Lemma w7b_ro_side : forall x l, 0x10000 <= x -> x + l < 0x2fa0c -> 0 <= l ->
(F + 0x80 <= x) \/ (x + l <= F).
Proof.
intros x l H1 H2 H3. destruct w7b_fr as (_ & _ & _ & Ni).
assert (Img : forall a, 0x10000 <= a < 0x2fa0c -> in_img rsegs a) by (intros a Ha; exact (w7b_in_seg _ _ a w7b_img_ro Ha)).
destruct (Z.lt_ge_cases F 0x10000) as [HF|HF].
- left. destruct (Z.le_gt_cases (F + 1024) 0x10000) as [HF2|HF2]; [lia|].
  exfalso. apply (Ni 0x10000); [lia | apply Img; lia].
- right. destruct (Z.le_gt_cases 0x2fa0c F) as [HF2|HF2]; [lia|].
  exfalso. apply (Ni F); [lia | apply Img; lia].
Qed.

Lemma w7b_pb8 : 0 <= pb mod 8 < 8.
Proof. apply Z.mod_pos_bound. lia. Qed.

(* ---------------- the parts: lengths, the prefix, where each lies ---------------- *)
Lemma w7b_len : forall i, (i < 4)%nat -> (length (nth i w7b_ss []) <= 21)%nat.
Proof.
intros i Hi. destruct i as [|[|[|[|i]]]]; try lia; cbn [nth w7b_ss].
- rewrite w7b_hpfx_len. lia.
- exact Hchs.
- pose proof (w7b_sep_len pb). lia.
- pose proof (w7b_param_len pb). lia.
Qed.
Lemma w7b_pre_S : forall i, (i < 4)%nat -> w7b_pre (S i) = w7b_pre i ++ nth i w7b_ss [].
Proof.
intros i Hi. unfold w7b_pre. destruct i as [|[|[|[|i]]]]; try lia; cbn [firstn concat w7b_ss nth];
rewrite ?app_nil_r, <- ?app_assoc; reflexivity.
Qed.
Lemma w7b_pre_4 : w7b_pre 4 = w7b_js chs pb.
Proof. unfold w7b_pre, w7b_js. cbn [firstn concat w7b_ss]. rewrite app_nil_r. reflexivity. Qed.
Lemma w7b_pre_len : forall i, (i < 4)%nat ->
(length (w7b_pre i) <= 35)%nat /\ (length (w7b_pre i) + length (nth i w7b_ss []) <= 44)%nat.
Proof.
intros i Hi. pose proof (w7b_sep_len pb) as L2. pose proof (w7b_param_len pb) as L3. pose proof w7b_hpfx_len as L0.
unfold w7b_pre. destruct i as [|[|[|[|i]]]]; try lia; cbn [firstn concat w7b_ss nth]; rewrite ?app_nil_r, ?length_app;
cbn [length]; lia.
Qed.
Lemma w7b_xs_rng : forall i, (i < 4)%nat -> 0 < nth i w7b_xs 0 < 2 ^ 63.
Proof.
intros i Hi. destruct w7b_fb as (B1 & _). pose proof (w7b_sep_rng pb). pose proof (w7b_pptr_rng (pb mod 8) w7b_pb8).
destruct i as [|[|[|[|i]]]]; try lia; cbn [nth w7b_xs]; lia.
Qed.

(* the four strings as the strlen / memcpy calls ask them, at G *)
Lemma w7b_ch_strok : w7b_strok W memG R (F + 0xa0) chs.
Proof.
destruct w7b_fr as (HF32 & HFapp & HFp & _). destruct w7b_fb as (B1 & _ & _ & _ & Ham).
pose proof (proj1 (rtmb_bytes_aview rsegs (w_H W) memG (F + 0xa0) (chs ++ [NUL])) Hch) as Hb.
rewrite length_app in Hb. cbn [length] in Hb.
assert (HF8 : F mod 8 = 0) by (pose proof (rtsb_fmod8 F 0 HF32) as X; rewrite Z.mul_0_r, Z.add_0_r in X; exact X).
pose proof Hsh as Hsh'. rewrite w7b_PG in Hsh'.
unfold w7b_strok. split; [lia|]. split; [lia|]. split; [unfold ESTACK in *; lia|].
split.
{ intros j Hj. specialize (Hb j ltac:(lia)). rewrite app_nth1 in Hb by lia. split; [exact Hb|].
  rewrite Forall_forall in Hchz. apply Hchz, nth_In. exact Hj. }
split.
{ specialize (Hb (length chs) ltac:(lia)). rewrite nth_middle in Hb. rewrite Hb. reflexivity. }
split.
{ intros a Ha. apply w7b_ap_av. apply HFp.
  pose proof (Z.mod_pos_bound (F + 0xa0 + Z.of_nat (length chs)) 8 ltac:(lia)). lia. }
split; [intros a Ha; unfold ESTACK; lia|].
split; [apply Ham; lia|].
split.
{ replace (F + 0xa0) with (F + RTMB_CH + 0) by (unfold RTMB_CH; lia).
  apply (rtmb_B_ra_ch rsegs (w_H W) memG F true false false false true false 0 (Z.of_nat (length chs) + 1) Hsh' HF8); lia. }
apply (w7b_hull_fsh (w_H W) memG F rsb_PG); [exact Hsh | rewrite w7b_PG, rtmb_sh_len; lia | exact HF32 | lia | lia | lia | lia].
Qed.

Lemma w7b_strok_G : forall i, (i < 4)%nat -> w7b_strok W memG R (nth i w7b_xs 0) (nth i w7b_ss []).
Proof.
intros i Hi. destruct i as [|[|[|[|i]]]]; try lia; cbn [nth w7b_xs w7b_ss].
- apply (w7b_strok_cstr W memG R 0x20fe0 HPFX Hcs0);
    [| rewrite w7b_hpfx_len; simpl Z.of_nat; unfold ESTACK; lia | rewrite w7b_hpfx_len; lia].
  intros a Ha. rewrite w7b_hpfx_len in Ha. simpl Z.of_nat in Ha.
  apply (w7b_tail_img 0x20fe0 13); [cbv [w7b_tail_strs In]; left; reflexivity | exact Ha].
- exact w7b_ch_strok.
- pose proof (w7b_sep_rng pb) as Hs. pose proof (w7b_sep_len pb) as Hl.
  apply (w7b_strok_cstr W memG R (w7b_sep pb) (w7b_sepb pb) Hcs2); [| unfold ESTACK; lia | lia].
  intros a Ha. apply (w7b_tail_img (w7b_sep pb) (Z.of_nat (length (w7b_sepb pb)))); [exact (w7b_sep_tail pb) | exact Ha].
- pose proof (w7b_pptr_rng (pb mod 8) w7b_pb8) as Hs. pose proof (w7b_param_len pb) as Hl.
  apply (w7b_strok_cstr W memG R (w7b_pptr (pb mod 8)) (w7b_pab pb) Hcs3); [| unfold ESTACK; lia | lia].
  intros a Ha. apply (w7b_tail_img (w7b_pptr (pb mod 8)) (Z.of_nat (length (w7b_pab pb)))); [| exact Ha].
  unfold w7b_pab. exact (w7b_param_tail (pb mod 8) w7b_pb8).
Qed.

(* the bytes a string fact reads lie below the callees' stack and outside what the turns write *)
Lemma w7b_strz_out : forall i a, (i < 4)%nat -> w7b_strz (nth i w7b_xs 0) (nth i w7b_ss []) a ->
0 <= a < R - 2 * ESTACK /\ ~ w7b_Zm a.
Proof.
intros i a Hi Hz. pose proof (w7b_len i Hi) as Hl. pose proof (w7b_xs_rng i Hi) as Hx.
destruct w7b_fb as (B1 & _). pose proof (w7b_sep_rng pb) as Hs2. pose proof (w7b_pptr_rng (pb mod 8) w7b_pb8) as Hs3.
destruct Hz as [Hz | Hz].
2:{ assert (Hb : kLowMemEnd <= a < kHighMemBeg).
    { apply (w7b_hull_band (nth i w7b_xs 0) (Z.of_nat (length (nth i w7b_ss [])) + 1)); [lia | lia | | exact Hz].
      unfold kHighMemEnd. destruct i as [|[|[|[|i]]]]; try lia; cbn [nth w7b_xs] in *; lia. }
    destruct (w7b_band_out a Hb) as [N1 N2]. unfold w7b_Zm. unfold kLowMemEnd, kHighMemBeg, ESTACK in *.
    split; [lia|]. intros [X|[X|X]]; lia. }
destruct i as [|[|[|[|i]]]]; try lia; cbn [nth w7b_xs w7b_ss] in Hz, Hl |- *; unfold w7b_Zm, ESTACK.
- rewrite w7b_hpfx_len in Hz. destruct (w7b_ro_side 0x20fe0 21 ltac:(lia) ltac:(lia) ltac:(lia)); split; lia.
- split; lia.
- pose proof (w7b_sep_rng pb) as Hs. pose proof (w7b_sep_len pb).
  destruct (w7b_ro_side (w7b_sep pb) 10 ltac:(lia) ltac:(lia) ltac:(lia)); split; lia.
- pose proof (w7b_pptr_rng (pb mod 8) w7b_pb8) as Hs. pose proof (w7b_param_len pb).
  destruct (w7b_ro_side (w7b_pptr (pb mod 8)) 18 ltac:(lia) ltac:(lia) ltac:(lia)); split; lia.
Qed.

(* t and the part do not overlap *)
Lemma w7b_dis : forall i, (i < 4)%nat ->
F + 0x20 + Z.of_nat (length (w7b_pre i)) + Z.of_nat (length (nth i w7b_ss [])) <= nth i w7b_xs 0 \/
nth i w7b_xs 0 + Z.of_nat (length (nth i w7b_ss [])) <= F + 0x20 + Z.of_nat (length (w7b_pre i)).
Proof.
intros i Hi. pose proof (w7b_pre_len i Hi) as [L1 L2]. pose proof (w7b_len i Hi) as Hl.
destruct i as [|[|[|[|i]]]]; try lia; cbn [nth w7b_xs w7b_ss] in *.
- destruct (w7b_ro_side 0x20fe0 21 ltac:(lia) ltac:(lia) ltac:(lia)); [left | right]; lia.
- left. lia.
- pose proof (w7b_sep_rng pb). destruct (w7b_ro_side (w7b_sep pb) 21 ltac:(lia) ltac:(lia) ltac:(lia)); [left | right]; lia.
- pose proof (w7b_pptr_rng (pb mod 8) w7b_pb8).
  destruct (w7b_ro_side (w7b_pptr (pb mod 8)) 21 ltac:(lia) ltac:(lia) ltac:(lia)); [left | right]; lia.
Qed.

(* the frame's shadow at any memory that kept the frame's shadow bytes *)
Lemma w7b_fsh_kept : forall m (Zn : Z -> Prop), w7b_kept W memG m Zn ->
(forall i, 0 <= i < 88 -> ~ Zn (shadow_addr F + i)) -> rt_fsh rsegs (w_H W) m F rsb_PG.
Proof.
intros m Zn K Hz i Hi. rewrite w7b_PG, rtmb_sh_len in Hi.
pose proof (w7b_shF_band i ltac:(lia)) as Hb. unfold kLowMemEnd, kHighMemBeg in Hb.
rewrite K; [exact (Hsh i ltac:(rewrite w7b_PG, rtmb_sh_len; lia)) | lia | apply Hz; lia].
Qed.
Lemma w7b_shF_Zm : forall i, 0 <= i < 128 -> ~ w7b_Zm (shadow_addr F + i).
Proof.
intros i Hi. pose proof (w7b_shF_band i ltac:(lia)) as Hb. destruct (w7b_band_out _ Hb) as [N1 N2].
unfold w7b_Zm, ESTACK in *. intros [X|[X|X]]; lia.
Qed.

(* ---------------- the states between the blocks ---------------- *)
Definition w7b_inv (i : nat) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
ajournal rsegs B STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W mem1 md1 k /\ same_io mdG md1 /\
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r w7b_clob -> getr regs1 r = getr regsG r) /\
w7b_kept W memG mem1 w7b_Zm /\ (forall a, apresent (w_H W) memG a -> apresent (w_H W) mem1 a) /\
getr regs1 1 = w64 W7B_AFTER_STRLEN /\ getr regs1 10 = w64 (nth i w7b_xs 0) /\ getr regs1 26 = w64 (nth i w7b_xs 0) /\
getr regs1 25 = w64 (Z.of_nat (length (w7b_pre i))) /\ getr regs1 18 = w64 (R + 0x198 + 8 * Z.of_nat i) /\
getr regs1 24 = w64 left /\
(forall j, (j < 4)%nat -> val_mem rsegs (mrestrict (w_H W) mem1) (R + 0x198 + 8 * Z.of_nat j) 8 (nth j w7b_xs 0)) /\
(forall j, (j < length (w7b_pre i))%nat ->
 aview rsegs (w_H W) mem1 (F + 0x20 + Z.of_nat j) = Some (bv_unsigned (nth j (w7b_pre i) (Z_to_bv 8 0)))).
Definition w7b_mid (i : nat) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop :=
ajournal rsegs B STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W mem2 md2 k /\ same_io mdG md2 /\
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r w7b_clob -> getr regs2 r = getr regsG r) /\
w7b_kept W memG mem2 w7b_Zm /\ (forall a, apresent (w_H W) memG a -> apresent (w_H W) mem2 a) /\
getr regs2 25 = w64 (Z.of_nat (length (w7b_pre i))) /\ getr regs2 22 = w64 (Z.of_nat (length (nth i w7b_ss []))) /\
getr regs2 18 = w64 (R + 0x198 + 8 * Z.of_nat i) /\ getr regs2 24 = w64 left /\
(forall j, (j < 4)%nat -> val_mem rsegs (mrestrict (w_H W) mem2) (R + 0x198 + 8 * Z.of_nat j) 8 (nth j w7b_xs 0)) /\
(forall j, (j < length (w7b_pre (S i)))%nat ->
 aview rsegs (w_H W) mem2 (F + 0x20 + Z.of_nat j) = Some (bv_unsigned (nth j (w7b_pre (S i)) (Z_to_bv 8 0)))).

Lemma w7b_incl_A1 : incl [10; 11; 12]%bv w7b_clob.
Proof. unfold w7b_clob. w7b_incl. Qed.
Lemma w7b_incl_A2 : incl [1; 10; 11; 12; 18; 24; 25; 26]%bv w7b_clob.
Proof. unfold w7b_clob. w7b_incl. Qed.
Lemma w7b_incl_C : incl [1; 10; 18; 25; 26]%bv w7b_clob.
Proof. unfold w7b_clob. w7b_incl. Qed.
Lemma w7b_incl_D : incl [1; 10; 11; 12; 18; 25; 26]%bv w7b_clob.
Proof. unfold w7b_clob. w7b_incl. Qed.
Lemma w7b_incl_E1 : incl [10; 18; 22; 25]%bv w7b_clob.
Proof. unfold w7b_clob. w7b_incl. Qed.
Lemma w7b_incl_E2 : incl [6; 10; 26]%bv w7b_clob.
Proof. unfold w7b_clob. w7b_incl. Qed.
Lemma w7b_cs_of : forall (r : bv 5) (l : list (bv 5)), bv_unsigned r <> 0 -> ~ In r (rtsb_caller_saved ++ l) ->
acallee_saved (bv_unsigned r).
Proof. intros r l H0 Hn. apply rtsb_callee; [exact H0|]. intros X. apply Hn. apply in_or_app. left. exact X. Qed.

(* ---------------- one part: strlen, the clamp, memcpy(t + n, part, l) ---------------- *)
Lemma w7b_part : forall (i : nat) regs1 mem1 md1 (Q : world rsegs -> config -> Prop), (i < 4)%nat ->
w7b_inv i regs1 mem1 md1 ->
(forall regs2 mem2 md2, w7b_mid i regs2 mem2 md2 ->
 SRr rsegs W (mkCfg (mkst regs2 (Z_to_bv 64 W7B_AFTER_MEMCPY) mem2 (seg_rom rsegs)) md2) Q) ->
SRr rsegs W (mkCfg (mkst regs1 (Z_to_bv 64 W7B_STRLEN) mem1 (seg_rom rsegs)) md1) Q.
Proof.
intros i regs1 mem1 md1 Q Hi HI K.
destruct HI as (J1 & Io1 & Kr1 & Km1 & Pr1 & R1 & R10 & R26 & R25 & R18 & R24 & Cl1 & T1).
pose proof (w7b_len i Hi) as Hl. pose proof (w7b_pre_len i Hi) as [Hn1 Hn2].
destruct w7b_fr as (HF32 & HFapp & _). destruct w7b_fb as (B1 & _ & B3 & B4 & Ham).
assert (HF8 : F mod 8 = 0) by (pose proof (rtsb_fmod8 F 0 HF32) as X; rewrite Z.mul_0_r, Z.add_0_r in X; exact X).
assert (Fsh : rt_fsh rsegs (w_H W) mem1 F (rtmb_sh true true false false false true false)).
{ rewrite <- w7b_PG. apply (w7b_fsh_kept mem1 w7b_Zm Km1). intros i0 Hi0. apply w7b_shF_Zm. lia. }
set (n := Z.of_nat (length (w7b_pre i))) in *. set (l := Z.of_nat (length (nth i w7b_ss []))) in *.
set (x := nth i w7b_xs 0) in *. set (s := nth i w7b_ss []) in *.
assert (Hl' : l <= 21) by (unfold l; lia). assert (Hn' : n <= 35) by (unfold n; lia).
assert (Hnl : n + l <= 44) by (unfold n, l; lia).
eapply (w7b_iter B LAWS ASTRLEN AMEMCPY STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W mem1 md1 k regs1 R (F + 0x20) n x s Q
  J1 R1 R10 R26 R25).
- rewrite (Kr1 27%bv) by (first [w7b_nz | unfold w7b_clob; w7b_notin]). exact G27.
- rewrite (Kr1 2%bv) by (first [w7b_nz | unfold w7b_clob; w7b_notin]). exact G2.
- rewrite (Kr1 3%bv) by (first [w7b_nz | unfold w7b_clob; w7b_notin]). exact G3.
- rewrite (Kr1 4%bv) by (first [w7b_nz | unfold w7b_clob; w7b_notin]). exact G4.
- exact HR16.
- exact Hs16.
- lia.
- unfold ESTACK. lia.
- unfold ESTACK. lia.
- lia.
- apply (w7b_strok_kept W memG mem1); [exact (w7b_strok_G i Hi)|].
  intros a Ha. destruct (w7b_strz_out i a Hi Ha) as [Ha1 Ha2]. apply Km1; [unfold ESTACK in Ha1; lia | exact Ha2].
- exact (w7b_aro_kept B W memG mem1 w7b_Zm Hro Km1 w7b_rom_out).
- exact Hl.
- unfold n. lia.
- lia.
- unfold ESTACK. lia.
- intros a Ha. apply (rtsb_awr_fobj STK sp0 FP _ _ lyc own pos a Hown). rewrite HFa. unfold n, l in *. lia.
- replace (F + 0x20 + n) with (F + (0x20 + n)) by lia. apply Ham; unfold n, l in *; lia.
- replace (F + 0x20 + n) with (F + RTMB_T + n) by (unfold RTMB_T; lia).
  apply (rtmb_B_ra_t rsegs (w_H W) mem1 F true false false false true false n l Fsh HF8); unfold n, l in *; lia.
- intros Hl0. replace (F + 0x20 + n) with (F + (0x20 + n)) by lia.
  apply (w7b_hull_fsh (w_H W) mem1 F _ (0x20 + n) l Fsh); [rewrite rtmb_sh_len; lia | exact HF32 | lia | unfold n; lia | exact Hl0 | lia].
- intros a Ha. assert (Hb : kLowMemEnd <= a < kHighMemBeg).
  { apply (w7b_hull_band (F + 0x20 + n) l); [lia | unfold l, n in *; lia | unfold kHighMemEnd; lia | exact Ha]. }
  destruct (w7b_band_out a Hb) as [_ N2]. unfold kLowMemEnd in Hb. unfold ESTACK in *. lia.
- intros a Ha. exact (proj1 (w7b_strz_out i a Hi Ha)).
- exact (w7b_dis i Hi).
- intros regs2 mem2 md2 J2 Io2 Kc2 R22 Copy Km2 Pr2. apply K.
  assert (Kr2 : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r w7b_clob -> getr regs2 r = getr regsG r).
  { intros r Hr0 Hn. rewrite (w7b_cs22 regs1 regs2 r Kc2).
    - exact (Kr1 r Hr0 Hn).
    - exact (w7b_cs_of r _ Hr0 Hn).
    - apply (w7b_cs_not22 r w7b_clob); [unfold w7b_clob; cbv [rtsb_caller_saved app In]; repeat (first [left; reflexivity | right]) | exact Hn]. }
  assert (Kz : forall a, 0 <= a < 2 ^ 64 -> ~ (R - 2 * ESTACK <= a < R \/ F + 0x20 + n <= a < F + 0x20 + n + l) ->
    aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) mem1 a) by exact Km2.
  unfold w7b_mid. split; [exact J2|]. split; [exact (same_io_trans _ _ _ Io1 Io2)|]. split; [exact Kr2|].
  split.
  { apply (w7b_kept_trans W memG mem1 mem2 w7b_Zm _ w7b_Zm Km1 Km2). intros a [X|[X|X]]; [exact X | left; exact X |].
    unfold w7b_Zm. right; right. unfold n, l in *. lia. }
  split; [intros a Ha; exact (Pr2 a (Pr1 a Ha))|].
  split; [rewrite (w7b_cs22 regs1 regs2 25%bv Kc2) by first [w7b_cs | w7b_nz | w7b_bvu; lia]; exact R25|].
  split; [exact R22|].
  split; [rewrite (w7b_cs22 regs1 regs2 18%bv Kc2) by first [w7b_cs | w7b_bvu; lia]; exact R18|].
  split; [rewrite (w7b_cs22 regs1 regs2 24%bv Kc2) by first [w7b_cs | w7b_bvu; lia]; exact R24|].
  split.
  { intros j Hj. apply (w7b_vm_kept W mem1 mem2); [exact (Cl1 j Hj)|]. intros i0 Hi0. apply Kz; [lia|].
    unfold ESTACK. intros [X|X]; [lia|]. unfold n, l in *. lia. }
  rewrite (w7b_pre_S i Hi). intros j Hj. rewrite length_app in Hj.
  destruct (Nat.lt_ge_cases j (length (w7b_pre i))) as [Hj1|Hj1].
  + rewrite app_nth1 by exact Hj1. rewrite Kz; [exact (T1 j Hj1) | lia |].
    unfold ESTACK. intros [X|X]; [lia|]. unfold n in *. lia.
  + rewrite app_nth2 by exact Hj1. fold s in Hj. pose proof (Copy (j - length (w7b_pre i))%nat ltac:(lia)) as C.
    replace (F + 0x20 + n + Z.of_nat (j - length (w7b_pre i))) with (F + 0x20 + Z.of_nat j) in C by (unfold n; lia).
    exact C.
Qed.

(* ---------------- C: the next part's pointer and strlen entry (i < 3) ---------------- *)
Lemma w7b_next : forall (i : nat) regs2 mem2 md2 (Q : world rsegs -> config -> Prop), (i < 3)%nat ->
w7b_mid i regs2 mem2 md2 ->
(forall regs3 mem3 md3, w7b_inv (S i) regs3 mem3 md3 ->
 SRr rsegs W (mkCfg (mkst regs3 (Z_to_bv 64 W7B_STRLEN) mem3 (seg_rom rsegs)) md3) Q) ->
SRr rsegs W (mkCfg (mkst regs2 (Z_to_bv 64 W7B_AFTER_MEMCPY) mem2 (seg_rom rsegs)) md2) Q.
Proof.
intros i regs2 mem2 md2 Q Hi HM K.
destruct HM as (J2 & Io2 & Kr2 & Km2 & Pr2 & M25 & M22 & M18 & M24 & Cl2 & T2).
pose proof (w7b_len i ltac:(lia)) as Hl. pose proof (w7b_pre_len i ltac:(lia)) as [Hn1 Hn2].
pose proof (w7b_xs_rng (S i) ltac:(lia)) as Hx.
eapply SRr_bind.
{ apply (w7b_C B LAWS STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W mem2 md2 k regs2 i R (Z.of_nat (length (w7b_pre i)))
    (Z.of_nat (length (nth i w7b_ss []))) (nth (S i) w7b_xs 0) J2 Hi).
  - rewrite (Kr2 9%bv) by (first [w7b_nz | unfold w7b_clob; w7b_notin]). exact G9.
  - exact HR0.
  - lia.
  - exact HR16.
  - exact M18.
  - exact M25.
  - exact M22.
  - lia.
  - lia.
  - replace (R + 0x1a0 + 8 * Z.of_nat i) with (R + 0x198 + 8 * Z.of_nat (S i)) by lia. exact (Cl2 (S i) ltac:(lia)).
  - lia. }
intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & J3 & Io3 & Kr3 & Km3 & Pr3 & (C1 & C10 & C26 & C18 & C25)).
apply K. unfold w7b_inv.
split; [exact J3|]. split; [exact (same_io_trans _ _ _ Io2 Io3)|].
split.
{ intros r Hr0 Hn. rewrite (Kr3 r Hr0 (w7b_notin_incl _ _ r w7b_incl_C Hn)). exact (Kr2 r Hr0 Hn). }
split.
{ apply (w7b_kept_trans W memG mem2 mem3 w7b_Zm (fun _ => False) w7b_Zm Km2); [|intros a [X|X]; [exact X | destruct X]].
  intros a Ha Hz. exact (Km3 a Ha Hz). }
split; [intros a Ha; exact (Pr3 a (Pr2 a Ha))|].
split; [exact C1|]. split; [exact C10|]. split; [exact C26|].
split; [rewrite (w7b_pre_S i ltac:(lia)), length_app, Nat2Z.inj_add; exact C25|].
split; [rewrite C18; f_equal; lia|].
split; [rewrite (Kr3 24%bv) by (first [w7b_nz | w7b_notin]); exact M24|].
split.
{ intros j Hj. apply (w7b_vm_kept W mem2 mem3); [exact (Cl2 j Hj)|]. intros i0 Hi0. apply Km3; [lia | intros []]. }
intros j Hj. rewrite (Km3 (F + 0x20 + Z.of_nat j)); [exact (T2 j Hj) | | intros []].
pose proof (w7b_pre_len (S i) ltac:(lia)) as [L _]. destruct w7b_fb as (B1 & _). lia.
Qed.

(* ---------------- the start: A1, A2 ---------------- *)
Lemma w7b_start : forall (Q : world rsegs -> config -> Prop),
(forall regs2 mem2 md2, w7b_inv 0 regs2 mem2 md2 ->
 SRr rsegs W (mkCfg (mkst regs2 (Z_to_bv 64 W7B_STRLEN) mem2 (seg_rom rsegs)) md2) Q) ->
SRr rsegs W (mkCfg (mkst regsG (Z_to_bv 64 0x8160c) memG (seg_rom rsegs)) mdG) Q.
Proof.
intros Q K.
destruct w7b_fb as (B1 & _).
pose proof (w7b_pptr_rng (pb mod 8) w7b_pb8) as Hpa.
eapply SRr_bind; [exact (w7b_A1 B LAWS STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W memG mdG k regsG pb HJ G20 G25 Hpb Hpra)|].
intros W1 c1 _ (-> & regs1 & mem1 & md1 & -> & J1 & Io1 & Kr1 & Km1 & Pr1 & A10).
assert (Km1' : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W) mem1 a = aview rsegs (w_H W) memG a)
  by (intros a Ha; exact (Km1 a Ha (fun X => X))).
eapply SRr_bind.
{ apply (w7b_A2 B LAWS STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W mem1 md1 k regs1 pb R (F + 0xa0) left
    (w7b_pptr (pb mod 8)) J1).
  - exact A10.
  - rewrite (Kr1 20%bv) by (first [w7b_nz | w7b_notin]). exact G20.
  - rewrite (Kr1 25%bv) by (first [w7b_nz | w7b_notin]). exact G25.
  - exact Hpb.
  - rewrite (Kr1 9%bv) by (first [w7b_nz | w7b_notin]). exact G9.
  - exact HR0.
  - lia.
  - exact HR16.
  - rewrite (Kr1 18%bv) by (first [w7b_nz | w7b_notin]). exact G18.
  - lia.
  - rewrite (Kr1 6%bv) by (first [w7b_nz | w7b_notin]). exact G6.
  - apply (w7b_vm_kept W memG mem1); [exact Hpcell|]. intros i0 Hi0. apply Km1'. unfold W7B_PTAB.
    pose proof w7b_pb8. lia.
  - lia.
  - apply (rtmb_ra_kept rsegs (w_H W) memG (w_H W) mem1); [exact Hra1a0|]. intros x Hx. apply Km1'.
    unfold shadow_of_addr, SHADOW_OFF. assert (0 <= x / 8 <= 2 ^ 47) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
    lia.
  - intros a Ha. apply rtsb_awr_stk. lia. }
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & J2 & Io2 & Kr2 & Km2 & Pr2 &
  (A21 & A210 & A226 & A218 & A224 & A225 & P0 & P1 & P2 & P3)).
apply K. unfold w7b_inv.
split; [exact J2|]. split; [exact (same_io_trans _ _ _ Io1 Io2)|].
split.
{ intros r Hr0 Hn. rewrite (Kr2 r Hr0 (w7b_notin_incl _ _ r w7b_incl_A2 Hn)).
  apply Kr1; [exact Hr0|]. apply (w7b_notin_incl [10; 11; 12]%bv w7b_clob r); [exact w7b_incl_A1 | exact Hn]. }
split.
{ intros a Ha Hz. rewrite (Km2 a Ha); [exact (Km1' a Ha)|]. intros X. apply Hz. right; left; exact X. }
split; [intros a Ha; exact (Pr2 a (Pr1 a Ha))|].
split; [exact A21|]. split; [exact A210|]. split; [exact A226|].
split; [exact A225|]. split; [rewrite A218; f_equal; lia|]. split; [exact A224|].
split.
{ intros j Hj. destruct j as [|[|[|[|j]]]]; try lia; cbn [nth w7b_xs]; rewrite ?Z.add_0_r.
  - exact P0.
  - replace (R + 0x198 + 8 * Z.of_nat 1) with (R + 0x1a0) by lia. exact P1.
  - replace (R + 0x198 + 8 * Z.of_nat 2) with (R + 0x1a8) by lia. exact P2.
  - replace (R + 0x198 + 8 * Z.of_nat 3) with (R + 0x1b0) by lia. exact P3. }
intros j Hj. cbn in Hj. lia.
Qed.

(* ---------------- the end: D, memcpy(e62.body, t, n), E1, E2 ---------------- *)
Lemma w7b_tail : forall regs2 mem2 md2, w7b_mid 3 regs2 mem2 md2 ->
SRr rsegs W (mkCfg (mkst regs2 (Z_to_bv 64 W7B_AFTER_MEMCPY) mem2 (seg_rom rsegs)) md2)
(w7b_post B STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W k W7B_J regsG memG mdG w7b_clob w7b_WrW w7b_RJ).
Proof.
intros regs2 mem2 md2 HM.
destruct HM as (J2 & Io2 & Kr2 & Km2 & Pr2 & M25 & M22 & M18 & M24 & Cl2 & T2).
destruct w7b_fr as (HF32 & HFapp & _). destruct w7b_fb as (B1 & _ & B3 & B4 & Ham).
assert (HF8 : F mod 8 = 0) by (pose proof (rtsb_fmod8 F 0 HF32) as X; rewrite Z.mul_0_r, Z.add_0_r in X; exact X).
pose proof (w7b_len 3 ltac:(lia)) as Hl. pose proof (w7b_pre_len 3 ltac:(lia)) as [Hn1 Hn2].
rewrite w7b_pre_4 in T2.
pose proof (w7b_js_len chs pb Hchs) as Hjs.
assert (Hlen : (length (w7b_pre 3) + length (nth 3 w7b_ss []) = length (w7b_js chs pb))%nat).
{ rewrite <- w7b_pre_4, (w7b_pre_S 3 ltac:(lia)), length_app. reflexivity. }
set (len := Z.of_nat (length (w7b_js chs pb))) in *.
assert (Hlen' : Z.of_nat (length (w7b_pre 3)) + Z.of_nat (length (nth 3 w7b_ss [])) = len) by (unfold len; lia).
assert (Hlen44 : len <= 44) by (unfold len; lia).
assert (Fsh2 : rt_fsh rsegs (w_H W) mem2 F rsb_PG).
{ apply (w7b_fsh_kept mem2 w7b_Zm Km2). intros i0 Hi0. apply w7b_shF_Zm. lia. }
assert (KG2 : forall a, 0 <= a < 2 ^ 64 -> ~ w7b_Zm a -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memG a)
  by exact Km2.
assert (HshL : length rsb_PG = 88%nat) by (rewrite w7b_PG; apply rtmb_sh_len).
(* ---- D ---- *)
eapply SRr_bind.
{ apply (w7b_D B LAWS STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W mem2 md2 k regs2 R (Z.of_nat (length (w7b_pre 3)))
    (Z.of_nat (length (nth 3 w7b_ss []))) (F + 0x20) (F + 0x218) J2).
  - rewrite (Kr2 9%bv) by (first [w7b_nz | unfold w7b_clob; w7b_notin]). exact G9.
  - exact HR0.
  - lia.
  - exact HR16.
  - rewrite M18. f_equal. lia.
  - exact M25.
  - exact M22.
  - lia.
  - lia.
  - rewrite (Kr2 27%bv) by (first [w7b_nz | unfold w7b_clob; w7b_notin]). exact G27.
  - apply (w7b_vm_kept W memG mem2); [exact Hc130|]. intros i0 Hi0. apply KG2; [lia|].
    unfold w7b_Zm, ESTACK. lia.
  - lia. }
intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & J3 & Io3 & Kr3 & Km3 & Pr3 & (D1 & D10 & D11 & D12 & D26 & D25)).
rewrite Hlen' in D12, D25.
assert (Km3' : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W) mem3 a = aview rsegs (w_H W) mem2 a)
  by (intros a Ha; exact (Km3 a Ha (fun X => X))).
assert (R3_2 : getr regs3 2 = w64 R).
{ rewrite (Kr3 2%bv) by (first [w7b_nz | w7b_notin]).
  rewrite (Kr2 2%bv) by (first [w7b_nz | unfold w7b_clob; w7b_notin]). exact G2. }
assert (Hsp3 : spZ regs3 = sp0 + (R - sp0)) by (unfold spZ; rewrite R3_2; unfold w64; rewrite unsigned_lit_small; lia).
assert (Fsh3 : forall i0, (0 <= i0 < Z.of_nat (length rsb_PG)) ->
  aview rsegs (w_H W) mem3 (shadow_addr F + i0) = Some (nth (Z.to_nat i0) rsb_PG 0)).
{ intros i0 Hi0. rewrite HshL in Hi0.
  rewrite Km3' by (pose proof (w7b_shF_band i0 ltac:(lia)); unfold kLowMemEnd, kHighMemBeg in *; lia).
  exact (Fsh2 i0 ltac:(rewrite HshL; lia)). }
(* ---- memcpy(e62.body, t, len) ---- *)
eapply SRr_bind.
{ apply (w7b_memcpy_at B LAWS AMEMCPY W regs3 mem3 STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc md3 k (F + 0x218) (F + 0x20)
    len (R - sp0) (w64 W7B_AFTER_TEXT) J3 D10 D11 D12).
  - lia.
  - lia.
  - lia.
  - exact Hsp3.
  - rewrite Zminus_mod, HR16, Hs16. reflexivity.
  - lia.
  - unfold ESTACK. lia.
  - rewrite (Kr3 3%bv) by (first [w7b_nz | w7b_notin]).
    rewrite (Kr2 3%bv) by (first [w7b_nz | unfold w7b_clob; w7b_notin]). exact G3.
  - rewrite (Kr3 4%bv) by (first [w7b_nz | w7b_notin]).
    rewrite (Kr2 4%bv) by (first [w7b_nz | unfold w7b_clob; w7b_notin]). exact G4.
  - exact D1.
  - apply ret_ok_even; vm_compute; reflexivity.
  - intros a Ha. split; [apply (rtsb_awr_fobj STK sp0 FP _ _ lyc own pos a Hown); rewrite HFa; lia | unfold ESTACK; lia].
  - apply Ham; lia.
  - replace (F + 0x218) with (F + RTMB_E62 + 8) by (unfold RTMB_E62; lia).
    apply (rtmb_B_ra_e62 rsegs (w_H W) mem3 F true true false false false false 8 len); [| exact HF8 | lia | lia].
    rewrite <- w7b_PG. exact Fsh3.
  - intros Hl0.
    apply (w7b_hull_fsh (w_H W) mem3 F rsb_PG 0x218 len); [exact Fsh3 | rewrite HshL; lia | exact HF32 | lia | lia | exact Hl0 | lia].
  - lia.
  - lia.
  - intros a Ha. split; [|rewrite Hsp3; unfold ESTACK; lia].
    rewrite Km3' by lia. replace a with (F + 0x20 + Z.of_nat (Z.to_nat (a - (F + 0x20)))) by lia.
    rewrite T2; [discriminate | unfold len in Ha; lia].
  - right. lia.
  - apply Ham; lia.
  - replace (F + 0x20) with (F + RTMB_T + 0) by (unfold RTMB_T; lia).
    apply (rtmb_B_ra_t rsegs (w_H W) mem3 F true false false false true false 0 len); [| exact HF8 | lia | lia].
    rewrite <- w7b_PG. exact Fsh3.
  - intros Hl0. apply (w7b_hull_fsh (w_H W) mem3 F rsb_PG 0x20 len); [exact Fsh3 | rewrite HshL; lia | exact HF32 | lia | lia | exact Hl0 | lia]. }
intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & J4 & Io4 & Pv4 & R410 & Copy4 & Km4 & Pr4).
replace (sp0 + (R - sp0)) with R in Km4 by lia.
(* the bytes from G to just before E1: kept outside the turns' bytes, e62.body [F+0x218, F+0x218+len) and the
   stack *)
assert (K4G : forall a, 0 <= a < 2 ^ 64 -> ~ w7b_Zm a -> ~ (F + 0x218 <= a < F + 0x218 + len) ->
  aview rsegs (w_H W) mem4 a = aview rsegs (w_H W) memG a).
{ intros a Ha Hz He. rewrite Km4; [| exact Ha | exact He | intros X; apply Hz; left; unfold ESTACK in *; lia].
  rewrite Km3' by exact Ha. exact (KG2 a Ha Hz). }
(* ---- E1 ---- *)
eapply SRr_bind.
{ apply (w7b_E1 B LAWS STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W mem4 md4 k regs4 R (F + 0x218) len v158 (F + 0x210) v100 J4).
  - rewrite (w7b_csp regs3 regs4 9%bv Pv4) by w7b_cs.
    rewrite (Kr3 9%bv) by (first [w7b_nz | w7b_notin]).
    rewrite (Kr2 9%bv) by (first [w7b_nz | unfold w7b_clob; w7b_notin]). exact G9.
  - exact HR0.
  - lia.
  - exact HR16.
  - rewrite (w7b_csp regs3 regs4 26%bv Pv4) by w7b_cs. exact D26.
  - rewrite (w7b_csp regs3 regs4 25%bv Pv4) by w7b_cs. exact D25.
  - lia. - lia. - lia.
  - apply (w7b_vm_kept W memG mem4); [exact Hc158|]. intros i0 Hi0. apply K4G; [lia | unfold w7b_Zm, ESTACK; lia | lia].
  - exact Hv158.
  - apply (w7b_vm_kept W memG mem4); [exact Hc150|]. intros i0 Hi0. apply K4G; [lia | unfold w7b_Zm, ESTACK; lia | lia].
  - lia.
  - apply (w7b_vm_kept W memG mem4); [exact Hc100|]. intros i0 Hi0. apply K4G; [lia | unfold w7b_Zm, ESTACK; lia | lia].
  - exact Hv100. }
intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & J5 & Io5 & Kr5 & Km5 & Pr5 & (E10 & E25 & E18 & E22)).
assert (Km5' : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W) mem5 a = aview rsegs (w_H W) mem4 a)
  by (intros a Ha; exact (Km5 a Ha (fun X => X))).
assert (K5G : forall a, 0 <= a < 2 ^ 64 -> ~ w7b_Zm a -> ~ (F + 0x218 <= a < F + 0x218 + len) ->
  aview rsegs (w_H W) mem5 a = aview rsegs (w_H W) memG a).
{ intros a Ha Hz He. rewrite Km5' by exact Ha. exact (K4G a Ha Hz He). }
assert (Rg : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r w7b_clob -> getr regs5 r = getr regsG r).
{ intros r Hr0 Hn.
  rewrite (Kr5 r Hr0 (w7b_notin_incl _ _ r w7b_incl_E1 Hn)).
  rewrite (w7b_csp regs3 regs4 r Pv4 (w7b_cs_of r _ Hr0 Hn)).
  rewrite (Kr3 r Hr0 (w7b_notin_incl _ _ r w7b_incl_D Hn)).
  exact (Kr2 r Hr0 Hn). }
(* ---- E2 ---- *)
eapply SRr_bind.
{ apply (w7b_E2 B LAWS STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W mem5 md5 k regs5 R (F + 0x210) len (shadow_addr F)
    cur left J5).
  - rewrite (Rg 9%bv) by (first [w7b_nz | unfold w7b_clob; w7b_notin]). exact G9.
  - exact HR0.
  - lia.
  - exact HR16.
  - rewrite E10. f_equal. lia.
  - exact E25.
  - lia.
  - exact E22.
  - rewrite (Rg 19%bv) by (first [w7b_nz | unfold w7b_clob; w7b_notin]). exact G19.
  - rewrite (Kr5 24%bv) by (first [w7b_nz | w7b_notin]). rewrite (w7b_csp regs3 regs4 24%bv Pv4) by w7b_cs.
    rewrite (Kr3 24%bv) by (first [w7b_nz | w7b_notin]). exact M24.
  - lia.
  - pose proof (rtsb_fmod8 F 66 HF32) as X. replace (F + 0x210) with (F + 8 * 66) by lia. exact X.
  - lia.
  - exact B3.
  - destruct B4; [right | left]; lia.
  - pose proof (w7b_shF_band 0 ltac:(lia)) as Hb. unfold kLowMemEnd, kHighMemBeg in Hb. lia.
  - apply (w7b_vm_kept W memG mem5); [exact Hc128|]. intros i0 Hi0. apply K5G; [lia | unfold w7b_Zm, ESTACK; lia | lia].
  - exact Hcur.
  - intros a [Ha|Ha].
    + apply (rtsb_awr_fobj STK sp0 FP _ _ lyc own pos a Hown). rewrite HFa. lia.
    + apply (rtsb_awr_fsh STK sp0 FP _ _ lyc own pos a Hown). rewrite HFa. lia. }
intros W6 c6 _ (-> & regs6 & mem6 & md6 & -> & J6 & Io6 & Kr6 & Km6 & Pr6 &
  (F26 & F6 & Fnul & Fh0 & Fh4 & Fsh6)).
(* ---- the post ---- *)
apply SRr_ret. split; [reflexivity|]. exists regs6, mem6, md6.
split; [reflexivity|]. split; [exact J6|].
split; [exact (same_io_trans _ _ _ (same_io_trans _ _ _ (same_io_trans _ _ _ (same_io_trans _ _ _ Io2 Io3) Io4) Io5) Io6)|].
split.
{ intros r Hr0 Hn. rewrite (Kr6 r Hr0 (w7b_notin_incl _ _ r w7b_incl_E2 Hn)). exact (Rg r Hr0 Hn). }
assert (Z6 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (a = F + 0x210 + 8 + len \/ F + 0x210 <= a < F + 0x210 + 8 \/ shadow_addr F + 4 <= a < shadow_addr F + 16 \/
     shadow_addr F + 20 <= a < shadow_addr F + 23) ->
  aview rsegs (w_H W) mem6 a = aview rsegs (w_H W) mem5 a) by exact Km6.
split.
{ intros a Ha Hw. unfold w7b_WrW in Hw. rewrite Z6; [| exact Ha | lia]. apply K5G; [exact Ha | unfold w7b_Zm; lia | lia]. }
split; [intros a Ha; exact (Pr6 a (Pr5 a (Pr4 a (Pr3 a (Pr2 a Ha)))))|].
unfold w7b_RJ.
split; [rewrite (Kr6 18%bv) by (first [w7b_nz | w7b_notin]); exact E18|].
split; [rewrite (Kr6 22%bv) by (first [w7b_nz | w7b_notin]); exact E22|].
split; [exact F26|]. split; [exact F6|].
split.
- (* e62: type, size, the key's text, its NUL, zeros *)
  rewrite (w7b_ent_text_js chs pb Hchs). unfold ent_mem. cbn [e_type e_size e_body]. fold len.
  apply rtmb_bytes_app. split; [apply rtmb_bytes_of_val; exact Fh0|].
  unfold le32 at 1. rewrite length_Z_to_le_bytes.
  apply rtmb_bytes_app. split.
  { unfold le32. replace (F + 0x210 + Z.of_nat 4) with (F + 0x210 + 4) by lia. apply rtmb_bytes_of_val. exact Fh4. }
  unfold le32 at 1. rewrite length_Z_to_le_bytes.
  apply rtmb_bytes_app. split.
  { apply rtmb_bytes_app. split.
    - apply rtmb_bytes_aview. intros j Hj.
      replace (F + 0x210 + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat j) with (F + 0x218 + Z.of_nat j) by lia.
      rewrite Z6; [| lia | lia]. rewrite Km5' by lia. rewrite (Copy4 (Z.of_nat j)) by (unfold len; lia).
      rewrite Km3' by lia. exact (T2 j Hj).
    - apply rtmb_bytes_aview. intros j Hj. cbn [length] in Hj. assert (j = 0%nat) by lia. subst j.
      replace (F + 0x210 + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat (length (w7b_js chs pb)) + Z.of_nat 0)
        with (F + 0x210 + 8 + len) by (unfold len; lia).
      rewrite Fnul. reflexivity. }
  rewrite length_app. cbn [length].
  pose proof (rtmb_bytes_slice rsegs (w_H W) memG (F + 0x210) (zeros 104) (9 + length (w7b_js chs pb))
    (96 - length (w7b_js chs pb ++ [NUL])) He0) as Hz.
  rewrite length_app in Hz. cbn [length] in Hz. rewrite length_zeros in Hz.
  specialize (Hz ltac:(lia)).
  assert (Ez : rtmb_slice (zeros 104) (9 + length (w7b_js chs pb)) (96 - (length (w7b_js chs pb) + 1))
    = zeros (96 - (length (w7b_js chs pb) + 1))).
  { apply w7b_slice_zeros. lia. }
  rewrite Ez in Hz.
  apply (rtmb_bytes_kept rsegs (w_H W) memG); [replace (F + 0x210 + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat (length (w7b_js chs pb) + 1))
    with (F + 0x210 + Z.of_nat (9 + length (w7b_js chs pb))) by lia; exact Hz|].
  intros y Hy. rewrite length_zeros in Hy. rewrite Z6; [| lia | unfold len in *; lia].
  apply K5G; [lia | unfold w7b_Zm, ESTACK; lia | unfold len in *; lia].
- (* the frame's shadow: t and ch out of scope *)
  intros i0 Hi0. rewrite w7b_PJ, rtmb_sh_len in Hi0.
  destruct (w7b_PG_PJ i0 Hi0) as [P1 P2].
  pose proof (w7b_shF_band i0 ltac:(lia)) as Hb. unfold kLowMemEnd, kHighMemBeg in Hb.
  assert (Hdec : (4 <= i0 < 16 \/ 20 <= i0 < 23) \/ ~ (4 <= i0 < 16 \/ 20 <= i0 < 23)) by lia.
  destruct Hdec as [Hin|Hout].
  + rewrite (P1 Hin). exact (Fsh6 i0 Hin).
  + rewrite (P2 Hout). rewrite Z6; [| lia | lia]. rewrite K5G; [| lia | apply w7b_shF_Zm; lia | lia].
    exact (Hsh i0 ltac:(rewrite HshL; lia)).
Qed.

(* ======================================== the walk G -> J ======================================== *)
Lemma w7b_walk :
SRr rsegs W (mkCfg (mkst regsG (Z_to_bv 64 0x8160c) memG (seg_rom rsegs)) mdG)
(w7b_post B STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W k W7B_J regsG memG mdG w7b_clob w7b_WrW w7b_RJ).
Proof using All.
apply w7b_start. intros r0 m0 d0 I0.
apply (w7b_part 0 r0 m0 d0 _ ltac:(lia) I0). intros r1 m1 d1 M0.
apply (w7b_next 0 r1 m1 d1 _ ltac:(lia) M0). intros r2 m2 d2 I1.
apply (w7b_part 1 r2 m2 d2 _ ltac:(lia) I1). intros r3 m3 d3 M1.
apply (w7b_next 1 r3 m3 d3 _ ltac:(lia) M1). intros r4 m4 d4 I2.
apply (w7b_part 2 r4 m4 d4 _ ltac:(lia) I2). intros r5 m5 d5 M2.
apply (w7b_next 2 r5 m5 d5 _ ltac:(lia) M2). intros r6 m6 d6 I3.
apply (w7b_part 3 r6 m6 d6 _ ltac:(lia) I3). intros r7 m7 d7 M3.
exact (w7b_tail r7 m7 d7 M3).
Qed.
End w.
End b.

Print Assumptions w7b_walk.
