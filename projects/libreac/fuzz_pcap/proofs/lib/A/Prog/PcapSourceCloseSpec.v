(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the tail of pcap_source_open (fuzz_pcap.asan-ubsan 0x811e0, listing offset
   AF_pcap_source_open = 0xa58, 246 instructions) on libreac v1.9.0's ASan+UBSan build: lib/A's PcapSourceOpenB.v, the
   walk from the two semantic cuts of lib/B/Prog/PcapSourceOpenPh.v to the return. op_from_null and op_from_read prove
   `op_from op_gi_null` and `op_from op_gi_read`, i.e. lib/A's image-generic post tpcap_source_open_post (with
   topen_kept, lib/A/Prog/PcapSourceOpenDefs.v) at this image (SEGS = pa_segs, the relro window pa_relro_lo /
   pa_relro_hi of the lib/B PAImg instance PI); PcapSourceOpen.v (the head) composes them. At ossv/recipes 25e3d17bdb50 (2026-10-29), this image had no released
   proof (rule 24, a Theorem Labs lane, 22:35Z); the released v1.8 UBSan proof lib/U/Prog/pcap_source_open.v is the guard
   template only.

   The paths, at this image's pcs:
   - the empty input (cut 0x813f8, f = NULL): a0 := -1, `j 0x81474`, the epilogue without the buffer re-poison;
   - the short read (cut 0x8138c, kr <> 24): `bne a0,s9` to 0x81400, the shadow test of ps (0x81400 `lbu`, 0x81404
     `bnez`), f = ps->f (0x81408), the fclose wrapper's call (0x8140c), the second shadow test (0x81410, 0x81414
     `beqz` to 0x8145c), ps->f := NULL (0x8145c), a0 := -1, the epilogue from 0x81464 (op_fclose);
   - kr = 24: the UBSan guard G6 (below), the magic of the four header bytes F + 32 .. F + 35 (0x81398..0x813c4, the
     top byte through `slliw`, magic_U), then 0xd4c3b2a1 (0x813c8 `beq` to 0x81420: ps->swapped := 1, a0 := 0,
     `j 0x81464`), 0xa1b2c3d4 (0x813d4 `bne` falls to 0x813d8: ps->swapped := 0, a0 := 0, `j 0x81464`), or the bad
     magic (0x81444: as the short read, fclose at 0x81450);
   - the epilogue (op_epi): the buffer out of scope (0x81464..0x81470, 3 shadow bytes 0xf8), the retired magic
     0x45e0360e at F (0x8147c); 0x81480 `beqz s2` NOT taken (s2 = F >= 4096, atom 18's fact), so the machine-frame
     arm 0x814d4..0x81500 is dead; F's 16 shadow bytes 0xf5 (0x81484..0x814c4); the flag through `ld a1,0x78(s2)` and
     `sb zero,0(a1)` (0x814c8, 0x814cc), which gives the frame back (lib/B/Prog/PcapFrame.v aj_flag_store_pi:
     astack_free_law, frame_flag_lawP); the restores and `ret` (0x81504..0x81538).
   The two guards on ps (G5, 0x812f8 and 0x81300 / 0x81304) are before the cuts, in the head.

   THE GUARD G6. 0x81390 `addi a0,zero,-3`, 0x81394 `bgeu s4,a0` branches to the `unimp` at 0x8153c when the header
   buffer s4 = F + 32 lies within 3 bytes of 2^64. The symbolic run decides it, NOT taken: decide_cond2
   (Reusable/YP0e.v:932) maps BC_GEU to the negation of decide_ltu2 (:922), and decide_ltu (Reusable/YP0m.v:673) finds
   atom 20 (s4) below the literal 2^64 - 3 from its range fact [4128, 0x7fffff800020] (rd_facts), which rd_entry
   proves from frames_bounds on the class-1 frame (F + 128 <= alloc_ceiling <= 0x7fffff800000). Templates: the released
   UBSan proof of the v1.8 image, proofs/libreac/fuzz_pcap/lib/U/Prog/pcap_source_open.v on origin/ossv/recipes
   c8557374ad2e, open_mid :286 (premise bv_unsigned sp0 < 2 ^ 63 at :291, frame bounds :295-299), which decides the
   guard at :410-412; and the earlier walk of this image, on a working branch
   (a8ccd33b1a7) pcap_source_open_tl.v (sha256 4aaa5af08467; internal record) pso_rdchk :36-67 (premise bv_unsigned s4 < 2 ^ 64 - 3 at :44,
   `step; step; if_false` at :65).

   THE REPORT PATHS are proved unreachable; no run steps into one. Every shadow test of ps in this stretch
   (0x81400 / 0x81404 and 0x81410 / 0x81414 on the short read, 0x81444 / 0x81448 and 0x81454 / 0x81458 on the bad
   magic, 0x813e4 / 0x813e8 and 0x8142c / 0x81430 on ps + 8 before the slow checks 0x81570 / 0x81584) is decided by
   the shadow entry of ps (rd_SH: ps's 24 bytes addressable; shent_rd_ok from op_pre's range_addressable, kept to the
   cut by op_mid's topen_kept and across fclose by its journal, shok_transfer), so the token run reads a 0 shadow byte
   and takes the non-report successor: the report calls 0x8141c, 0x81580, 0x81594 and 0x815a0..0x815b4 are never
   reached.

   The callees are Section hypotheses of their exact statement types: the fclose wrapper AFCLOSE, of
   lib/A/Stdio/PFclose.v's image-generic afclose_source_spec (= afclose_source_spec_stk PFCLOSE_STK) at this image,
   bound as lib/B/Prog/PcapSourceClose.v binds it (its data-buffer premise from op_pre's input block); the file meter
   FM (lib/A/Stdio/PSourceMeter.v asrc_file_meter); the frame give-back laws astack_free_law (Reusable/YG0d.v:301) and
   frame_flag_lawP (Reusable/YCbq.v:797) with model_laws; the meter laws (Reusable/YC5d.v ameter_laws,
   ameter_fs_laws); ASIL (lib/A/Stdio/PSourceMeta.v asource_img_laws). The stream predicates' frame lemmas are copied
   from lib/B/Prog/PcapSourceClose.v (not required). getr / mkst / seg_rom come from YK11; nothing from lib/Lib is
   imported. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/PcapSourceOpenB.v, with its module paths and module names changed; 96 of its 202 lines of code are new or changed and 1640 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: split out of lib/A/Prog/PcapSourceClose.v under a Theorem Labs lane's standing statement/walk rule (a lib/A file that a lib/B file Requires holds only statements, segs-generic lemmas and image-free definitions; its walk lies in a separate lib/A file that lib/B never Requires), after a Theorem Labs lane's measurement (lib/B/Prog/PcapSourceClose.v, PcapEntryEnd, PcapEntryRec and PcapEntryTail carried lib/A/Prog/PcapList.v through the walk imports of PcapSourceClose.v). MOVED here unchanged: CLOSE_FRAME, TPCAP_SOURCE_CLOSE_STK, EV_CLOSE, tclose_fblk, wvb_fds_fs, div8_in, div8_of_mul64, in_asource_fp, Section fr (vm_frame_segs, asource_none_frame_segs, asource_at_frame_segs), tclose_kept, tpcap_source_close_post, tpcap_source_close_specX, their Arguments lines and SK guards. The imports are PcapSourceClose.v's without PaTable, PaSym, PaShadow, PaStep, PaRun, PaJournal, PcapSyms, PcapList, PcapPa, PcapPaLib, YC4b, YC81, YC1g, YC1h, YC85, PcapFrame and PSourceMeter. The walk (CL_RET_FCLOSE, cl_entry, pb_pcap_source_closeX) stays in PcapSourceClose.v, which Require Exports this file. *)
(* pcap_source_close (fuzz_pcap.asan 0x81e90, listing offset AF_pcap_source_close = 0x1758, 27 instructions) on
   libreac v1.9.0's ASan build: the contract of the code and its walk.

   The code takes a 32-byte frame on the machine stack, saves ra, s0 and s1 there, loads the shadow base through the
   GOT word 0x99830 (object 1) from the cell 0xa18b8 (object 15), checks the shadow byte of the source struct's first
   8 bytes (0x81eb8 `lbu`, 0x81ebc `bnez` to the error path at 0x81eec), loads the FILE pointer f = ps->f
   (0x81ec0) and, when f is not null (0x81ec4 `beqz` to 0x81ed8), calls the fclose wrapper's 4-byte jump
   (0x81ec8 `jal __interceptor_trampoline_fclose`), checks the same shadow byte again (0x81ecc, 0x81ed0 `bnez` to the
   error path at 0x81ef4) and stores ps->f = NULL (0x81ed4 `sd zero,0(s0)`); it then restores the three registers,
   releases the frame and returns. The two error paths (calls of __asan_report_load8 / __asan_report_store8) are not
   reached: the walk discharges both checks from the shadow premise.

   The store writes 8 bytes of the caller's source struct, which lies in a side-stack frame the caller took (the
   harness's `struct pcap_source ps` in LLVMFuzzerTestOneInput's class-1 frame), so the contract is in cgif's
   caller-journal form (proofs/cgif/cgif_file_fuzzer/lib/YC20.v:311-365): the premise is the caller's journal, the
   caller's frame holding the field is one of the frames its journal took (`own`), and the post extends the same
   journal. tclose_kept is cgif's tlzw_kept / the kit's acall_kept with the image clause leaving out the open-file
   list head, which fclose sets to null.

   The fclose wrapper's contract is a Section hypothesis of the exact type a Theorem Labs lane's lib/A/Stdio/PFclose.v
   afclose_source_spec states; the stream predicates are a Theorem Labs lane's lib/A/Stdio/PSource.v and PSourceMeta.v, whose
   image laws asource_img_laws are a Section hypothesis discharged once at instantiation. getr / mkst / seg_rom come
   from YK11 (imported after LinuxProcessSem); nothing from lib/Lib is imported.

   The statement (tclose_kept, tpcap_source_close_post, tpcap_source_close_specX) is shared with the asan-ubsan build:
   it lies outside the Section with `Context {PI : PAImg pcap_listing}` and takes every image datum as a parameter,
   the segments `segs` and the relro bounds `rlo rhi` (with B, K, MT as before). Its only literal constants are the
   ones the two images share: CLOSE_FRAME = 32 (so TPCAP_SOURCE_CLOSE_STK = 32 + PFCLOSE_STK), PFCLOSE_STK, EV_CLOSE = 2,
   SRC_FILE_BLOCK = 1304, SHADOW_OFF and alloc_ceiling; the open-file list head AOFL_HEAD is the explicit sink head
   SK's. The theorem stays in the PI Section and states the contract at segs := SEGS, rlo := pa_relro_lo,
   rhi := pa_relro_hi. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0s YI16 YG0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 PcapImgEnd YE00 YG0p YC5d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapBase.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PFclose.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* The stack the call needs: its own 32-byte frame (0x81e90 `addi sp,sp,-32`) and the fclose wrapper's. *)
Definition CLOSE_FRAME : Z := 32.
Definition TPCAP_SOURCE_CLOSE_STK : Z := CLOSE_FRAME + PFCLOSE_STK.
(* The allocator events of the call: fclose's two (a free of the FILE block and a free of null). *)
Definition EV_CLOSE : Z := 2.

(* The FILE block the call frees: none when the struct holds a null FILE pointer. *)
Definition tclose_fblk (f : Z) : list (Z * Z) := if f =? 0 then [] else [(f, SRC_FILE_BLOCK)].

(* Materialising the lazy vm backing keeps the descriptor table and the file system. *)
Lemma wvb_fds_fs : forall l X m, m_fds (with_vm_backing l X m) = m_fds m /\ m_fs (with_vm_backing l X m) = m_fs m.
Proof. intros l X [fd [maps lazy mat] io fs proc lim tm]. split; reflexivity. Qed.

Lemma div8_in : forall p x, p mod 8 = 0 -> p <= x < p + 8 -> x / 8 = p / 8.
Proof.
intros p x H Hx. pose proof (Z_div_mod_eq_full p 8) as E. rewrite H, Z.add_0_r in E.
symmetry. apply (Z.div_unique x 8 (p / 8) (x - p)); [left; lia | lia].
Qed.

Lemma div8_of_mul64 : forall a, a mod 64 = 0 -> a / 8 = 8 * (a / 64) /\ a = 64 * (a / 64).
Proof.
intros a H. pose proof (Z_div_mod_eq_full a 64) as E. rewrite H, Z.add_0_r in E. split; [|exact E].
symmetry. apply (Z.div_unique a 8 (8 * (a / 64)) 0); [left; lia | lia].
Qed.

Lemma in_asource_fp : forall f a, inFP (asource_fp f) a -> (f <= a < f + SRC_FILE_BLOCK) \/ (0 <= a < 1).
Proof.
intros f a (r & Hr & Ha). unfold asource_fp, YI16.sink_token in Hr.
destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Ha; [left | right]; lia.
Qed.

(* ---- the stream predicates read only their footprint, over any segment list -------------------------------- *)
(* Image-generic (no PAImg, no sink head): a consumer that walks another segment list (a Theorem Labs lane's fread
   interceptor over tfibsegs) uses these directly; Section d below instantiates them at SEGS. *)
Section fr.
Variable segs : list Segment.

Lemma vm_frame_segs : forall (m m' : word -> option byte) a n v,
  (forall x, a <= x < a + Z.of_nat n -> mbyte segs m' x = mbyte segs m x) ->
  val_mem segs m a n v -> val_mem segs m' a n v.
Proof. intros m m' a n v Hfr Hv k Hk. rewrite Hfr by lia. exact (Hv k Hk). Qed.

Ltac vmf Hfr H := eapply vm_frame_segs; [| exact H]; intros ?x ?Hx; apply Hfr.

Lemma asource_none_frame_segs : forall K (m m' : word -> option byte),
  (forall a, asrc_env_addr K a -> mbyte segs m' a = mbyte segs m a) ->
  asource_none segs K m -> asource_none segs K m'.
Proof.
intros K m m' Hfr ((Hth & Hnl & Hlk & Hmode & Hms & (cv & Hcv & Hc)) & Hhead).
unfold asource_none, asrc_stdio_env, as_ofl_head in *.
split; [split; [|split; [|split; [|split; [|split]]]]|].
- vmf Hfr Hth. unfold asrc_env_addr. cbn in Hx. lia.
- vmf Hfr Hnl. unfold asrc_env_addr. cbn in Hx. lia.
- vmf Hfr Hlk. unfold asrc_env_addr. cbn in Hx. lia.
- apply (garr8_frame segs m m' _ _ Hmode). intros x Hx. apply Hfr. unfold asrc_env_addr.
  cbn [length src_mode_Z app] in Hx. cbn in Hx. lia.
- apply (garr8_frame segs m m' _ _ Hms). intros x Hx. apply Hfr. unfold asrc_env_addr.
  cbn [length src_modeset_Z app] in Hx. cbn in Hx. lia.
- exists cv. split; [exact Hcv|]. vmf Hfr Hc. unfold asrc_env_addr. cbn in Hx. lia.
- vmf Hfr Hhead. unfold asrc_env_addr. cbn in Hx. lia.
Qed.

Lemma asource_at_frame_segs : forall K (m m' : word -> option byte) f b C p,
  (forall a, (f <= a < f + SRC_FILE_BLOCK) \/ (b <= a < b + Z.of_nat (length C)) \/ asrc_env_addr K a ->
     mbyte segs m' a = mbyte segs m a) ->
  asource_at segs K m f b C p -> asource_at segs K m' f b C p.
Proof.
intros K m m' f b C p Hfr (Wn & cpos & fl & md & H). cbv zeta in H.
destruct H as (Hp0 & Hp1 & Hp2 & Hn63 & Hwrap & Hcp & HW & Hbok & Hgb & Hst & Hwin & Hfl & Hfl24 & Hmd & Hcpos & Henv & Hhead & Hf0).
assert (HF : forall x, f <= x < f + SRC_FILE_BLOCK -> mbyte segs m' x = mbyte segs m x) by (intros x Hx; apply Hfr; left; exact Hx).
assert (HE : forall x, asrc_env_addr K x -> mbyte segs m' x = mbyte segs m x) by (intros x Hx; apply Hfr; right; right; exact Hx).
destruct Hst as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17 & S168 &
  S18 & S19 & S20 & Sf & Sal & Sb & Sdisj).
exists Wn, cpos, fl, md. cbv zeta.
split; [exact Hp0|]. split; [exact Hp1|]. split; [exact Hp2|]. split; [exact Hn63|]. split; [exact Hwrap|].
split; [exact Hcp|]. split; [exact HW|].
split; [exact Hbok|].
split; [apply (garr8_frame segs m m' _ _ Hgb); intros x Hx; apply Hfr; right; left; exact Hx|].
split.
{ unfold source_static, SRC_COOKIE_OFF, SRC_BUF_OFF, SRC_BUFSIZ, SRC_MODE_R, U32M1 in *.
  split; [vmf HF S1; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [vmf HF S2; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [vmf HF S3; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [vmf HF S4; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [vmf HF S5; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [vmf HF S6; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [vmf HF S7; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [vmf HF S8; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [vmf HF S9; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [vmf HF S10; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [vmf HF S11; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [vmf HF S12; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [vmf HF S13; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [vmf HF S14; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [vmf HF S15; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [vmf HF S16; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [vmf HF S17; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [vmf HF S168; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [vmf HF S18; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [vmf HF S19; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [vmf HF S20; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
  split; [exact Sf|]. split; [exact Sal|]. split; [exact Sb | exact Sdisj]. }
split.
{ unfold source_window, SRC_BUF_OFF, SRC_BUFSIZ in *. destruct Hwin as [(-> & W1 & W2) | (i & Hi0 & Hi1 & W1 & W2 & W3)].
  - left. split; [reflexivity|]. split; [vmf HF W1 | vmf HF W2]; unfold SRC_FILE_BLOCK; cbn in Hx; lia.
  - right. exists i. split; [exact Hi0|]. split; [exact Hi1|].
    split; [vmf HF W1; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
    split; [vmf HF W2; unfold SRC_FILE_BLOCK; cbn in Hx; lia|].
    apply (garr8_frame segs m m' _ _ W3). intros x Hx. apply HF. unfold SRC_FILE_BLOCK. lia. }
split.
{ unfold source_flags in *. destruct Hfl as [Hfl1 Hfl2]. split; [|exact Hfl2]. vmf HF Hfl1. unfold SRC_FILE_BLOCK. cbn in Hx. lia. }
split; [exact Hfl24|].
split.
{ unfold source_mode in *. destruct Hmd as [Hmd1 Hmd2]. split; [|exact Hmd2]. vmf HF Hmd1. unfold SRC_FILE_BLOCK. cbn in Hx. lia. }
split; [vmf HF Hcpos; unfold SRC_COOKIE_OFF, SRC_FILE_BLOCK in *; cbn in Hx; lia|].
split.
{ unfold asrc_stdio_env in *. destruct Henv as (Hth & Hnl & Hlk & Hmode & Hms & (cv & Hcv & Hc)).
  split; [vmf HE Hth; unfold asrc_env_addr; cbn in Hx; lia|].
  split; [vmf HE Hnl; unfold asrc_env_addr; cbn in Hx; lia|].
  split; [vmf HE Hlk; unfold asrc_env_addr; cbn in Hx; lia|].
  split; [apply (garr8_frame segs m m' _ _ Hmode); intros x Hx; apply HE; unfold asrc_env_addr; cbn in Hx; lia|].
  split; [apply (garr8_frame segs m m' _ _ Hms); intros x Hx; apply HE; unfold asrc_env_addr; cbn in Hx; lia|].
  exists cv. split; [exact Hcv|]. vmf HE Hc. unfold asrc_env_addr. cbn in Hx. lia. }
split; [vmf HE Hhead; unfold asrc_env_addr, as_ofl_head in *; cbn in Hx; lia | exact Hf0].
Qed.

End fr.

(* MOVED here unchanged from PcapSourceClose.v (image-free: no segment list, only the shadow map), so callee walks
   that need it Require this file instead of keeping copies (a Theorem Labs lane, 2026-10-29 09:09Z). *)
Lemma ra_frame : forall (rd rd' : Z -> option Z) a n,
  range_addressable rd SHADOW_OFF a n ->
  (forall x, a <= x < a + n -> rd' (shadow_of_addr SHADOW_OFF x) = rd (shadow_of_addr SHADOW_OFF x)) ->
  range_addressable rd' SHADOW_OFF a n.
Proof. intros rd rd' a n HR Hk x Hx. destruct (HR x Hx) as (s & Hs & Ho). exists s. rewrite Hk by exact Hx. split; [exact Hs | exact Ho]. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ---- the contract, over the image data as parameters (shared with the asan-ubsan build) ---------------------- *)
Section s.
Variable segs : list Segment.
Variables rlo rhi : Z.
Variable B : asyms.
Variable K : asource_syms.
Variable MT : ameter_ops.

(* What a call keeps (the kit's acall_kept, YCbq.v:823-834), but for the open-file list head, which fclose sets to
   null: every byte above the allocator's ceiling outside the call's stack window, every byte of a heap block and of a
   frame that is not in E, every image byte but the runtime's own statics, errno and the list head, and the presence
   of the window. *)
Definition tclose_kept (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte)
  (W2 : world segs) (mem2 : word -> option byte) (slo shi : Z) (E : Z -> Prop) : Prop :=
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (slo <= a < shi) ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
  (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ E (b + i) ->
     aview segs (w_H W2) mem2 (b + i) = aview segs (w_H W) memc (b + i)) /\
  (forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     ~ (AOFL_HEAD <= a < AOFL_HEAD + 8) -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
  (forall cid pos a, In (cid, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
     ~ E a -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (slo <= a < shi) -> apresent (w_H W) memc a -> apresent (w_H W2) mem2 a) /\
  (forall a, slo <= a < shi -> apresent (w_H W2) mem2 a).

Definition tpcap_source_close_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z)
  (regs : bvmap 5 word) (ps f b : Z) (C : list Z) : world segs -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
  c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom segs)) md2 /\
  ajournal segs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_CLOSE) /\
  aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
  (* the allocator meter: the two frees of fclose, nothing when f = 0 *)
  mo_le MT Sc S2 (if f =? 0 then 0 else mo_free MT + mo_free MT) /\
  (* no descriptor and no file-system change *)
  m_fds md2 = m_fds mdc /\ m_fs md2 = m_fs mdc /\
  Permutation (ablocks B lyc Sc) (tclose_fblk f ++ ablocks B ly2 S2) /\
  (* ps->f reads NULL *)
  val_mem segs (rdW W2 mem2) ps 8 0 /\
  tclose_kept lyc Sc W memc W2 mem2 (spZ regs - TPCAP_SOURCE_CLOSE_STK) (spZ regs)
    (fun a => (ps <= a < ps + 8) \/ (f <> 0 /\ f <= a < f + req_size SRC_FILE_BLOCK)) /\
  (* the stream is closed and its data is untouched *)
  (f <> 0 -> asource_none segs K (rdW W2 mem2) /\ garr8 segs (rdW W2 mem2) b C).

Definition tpcap_source_close_specX (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (ps f b M p : Z) (C : list Z)
    (cid pos : Z),
  ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okP segs rlo rhi B (aview segs (w_H W) memc) ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 ps ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TPCAP_SOURCE_CLOSE_STK -> spZ regs <= sp0 ->
  (* the struct's FILE-pointer field, in a side-stack frame the caller took, its shadow marked usable *)
  In (cid, pos) own -> frame_addr lyc cid pos <= ps -> ps + 8 <= frame_addr lyc cid pos + fs_frame_bytes cid ->
  ps <> 0 /\ ps mod 8 = 0 ->
  val_mem segs (rdW W memc) ps 8 f -> 0 <= f < 2 ^ 64 ->
  range_addressable (aview segs (w_H W) memc) SHADOW_OFF ps 8 ->
  (* an open stream: its FILE block, its data buffer, the meta region, and the caller's right to let fclose change
     them *)
  (f <> 0 ->
     In (f, SRC_FILE_BLOCK) (ablocks B lyc Sc) /\ In (b, Z.of_nat (length C)) (ablocks B lyc Sc) /\
     asource_at segs K (rdW W memc) f b C p /\ asrc_meta_inv segs K lyc (rdW W memc) M /\
     (forall x, inFP (asource_fp f) x -> inFP FP x \/ in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) x)) ->
  st_nev Sc + EV_CLOSE <= EV_MAX ->
  SRr segs W (cfg_at segs a regs memc mdc)
    (tpcap_source_close_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ps f b C).

End s.
End b.

(* The sink-head instance is explicit on every exported statement and theorem (a Theorem Labs lane, 21:57Z): the only global
   sink_head instance in this closure is the plain build's (lib/Reusable/YI5b.v src0_sink_head), so a caller must name
   the ASan head (0x5f4f88 on the pin) instead of obtaining an instance by inference. *)
Arguments tclose_kept {rc} SK.
Arguments tpcap_source_close_post {fx rc} SK.
Arguments tpcap_source_close_specX {fx rc} SK.

(* GUARD: SK must stay explicit. SK is passed by position; were it implicit again, the positional SK
   would land on the next argument and this file would stop compiling. *)
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) (segs : list Segment) (rlo rhi : Z)
  (B : asyms) (K : asource_syms) (MT : ameter_ops) (a : Z) =>
  tpcap_source_close_specX (fx:=fx) (rc:=rc) SK segs rlo rhi B K MT a : Prop).
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) =>
  tpcap_source_close_post (fx:=fx) (rc:=rc) SK).
