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
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/PcapSourceOpenB.v, with its module paths, module names and numbers changed; 660 of its 725 lines of code are new or changed and 1681 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/fuzz_recv_entry.v, with its module paths and module names changed; 2301 of its 2378 lines of code are new or changed and 648 lines of the source are left out. *)
(* nl_talk on image A (fuzz_link.asan 0x88974; listing (internal path)
   (internal record, sha256 628c2741aace)): the RECEIVE phase of the walk (lib/A/Prog/nl_talk_defs.v fixes its boundaries):

     nt_recv : nt_from POST nt_attr_inv -> nt_from POST nt_exit_inv -> nt_from POST nt_recv_inv.

   The code, offsets from 0x88974 (a0 = the bytes left in the chunk, a1 = the message):
     +0x1ec..+0x200  a2 := 16384; `sd s6, 0x28(s1)` (the socket); a0 := s6; a1 := s10 (the buffer F + 32);
                     a3 := 0; `jal fuzz_recv` (fuzz_recv_acontract under SRr_bind)
     +0x204          `bltz a0` -> the failure arm +0x2ac
     +0x208..+0x210  s4 := 16, s3 := 2, s6 := 15
     +0x214          `bltu a0, s4` -> +0x294 (the chunk is done); +0x218 a1 := s10
     +0x21c..+0x270  the message loop: the instrumented check of the 4-byte load at a1, `lwu a3, 0(a1)` (the
                     message length ml), `bltu a3, s4` and `bltu a0, a3` -> +0x294; the check and `lhu a2, 4(a1)`
                     (the type); `beq a2, s4` -> +0x314 (RTM_NEWLINK: nt_attr_inv); `beq a2, s3` -> +0x4ac
                     (NLMSG_ERROR); else a3 += 3, `srliw` 2, `slli` 2 (NLMSG_ALIGN), a0 -= it, a1 += it,
                     `blt s6, a0` -> +0x21c, else `j +0x294`
     +0x294..+0x2a4  a2 := 16384; a0 := the socket from 0x28(s1); a1 := s10; a3 := 0; `jal fuzz_recv`
     +0x2a8          `bgez a0` -> +0x214, else into the failure arm
     +0x2ac..+0x2c8  `jal ___errno_location` (LinkWalkErrno.v aj_gx_errno_at), the instrumented check of the
                     4-byte load, `lw a0, 0(a0)`, `negw s11, a0`, `j +0x4dc` (nt_exit_inv)
     +0x4ac..+0x4d8  an NLMSG_ERROR: a0 := 0x24, `bgeu a3, a0` -> +0x4c4; else s11 := -5 (-EIO), `j +0x4dc`;
                     +0x4c4 a0 := a1 + 16, the instrumented check, `lw s11, 0(a0)` (the code), +0x4dc
   The partial-granule paths of the four instrumented checks (+0x274, +0x284 and the errpath_load4 calls at
   +0x5b0, +0x5b8, +0x590, +0x5a0) are never reached: each seat hands the engine a shadow entry for the checked
   range (the message's 20 bytes: mkSHE 11 0 20; errno's 4: mkSHE 10 0 4), proved addressable from
   nt_frame_shadow cx fp 0 (nr_ra_buf) and LinkWalkZsh.v zsh_errno_ard, and the engine decides each `bnez` on
   the shadow byte as not taken, so no run stops there.

   The model: link_spec's chunk_loop over the queue from k_next, and msg_scan inside one chunk. Both loops are
   proved by induction, as the plain walk (lib/Prog/nt_scan.v msg_loop) does: the
   receive loop on the chunk loop's fuel (nr_chunks over nr_next_inv, at +0x294), the message loop on msg_scan's
   fuel (nr_msg_loop over nr_loop_inv, at +0x21c).

   Section hypotheses: LAWS, LV, TB (the image instance: AR_laws, LinkVals, AF0m.PcapSyms B, as in the other
   phases), HSEGS (pa_segs = tfibsegs: g_nl's and errno's writability and the relro window, RELRO_IMG below),
   RECV (fuzz_recv_acontract, lib/A/Prog/fuzz_recv.v fuzz_recv_aproof) and ERRNO
   (RtErrnoLoc.aerrno_location_realizes, lib/A/Rt/RtErrnoLocClosed.v link_errno_location_closed).

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality Classical_Prop.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK1d YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YN0h.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import RtErrnoLoc.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC81 YC4b PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkSide LinkWalkPi LinkWalkZsh LinkWalkErrno.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
fuzz_recv_c copy_attr_c nl_talk_c nl_talk_defs nl_talk_kit LinkWalkWseg LinkWalkShadow LinkWalkNlk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
(* ==========================================================================
   1. Helpers over the memory views (the same facts nl_talk_exit.v uses at its cut, stated here for this file)
   ========================================================================== *)

(* A run whose regions have no write window leaves the memory as it was. *)
Lemma nr_frame_nowrite : forall E (rs : smem) (m m' : word -> option byte),
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true ->
  frame_of E rs m m' -> m' = m.
Proof.
  intros E rs m m' Hw HF. apply functional_extensionality. intros x. apply HF.
  intros (r & Hin & Ha). pose proof (proj1 (forallb_forall _ rs) Hw r Hin) as Hr.
  apply Z.leb_le in Hr. lia.
Qed.

(* A byte the step left as it was (aview, across two worlds), as mbyte. *)
Lemma nr_mbyte_of_aview : forall segs (H H' : word -> bool) (m m' : word -> option byte) a,
  aview segs H' m' a = aview segs H m a -> mbyte segs (mrestrict H' m') a = mbyte segs (mrestrict H m) a.
Proof.
  intros segs H H' m m' a E. unfold aview in E.
  destruct (mbyte segs (mrestrict H' m') a) as [b'|], (mbyte segs (mrestrict H m) a) as [b|];
    cbn in E; try discriminate; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* A machine word kept across a step whose eight bytes did not change. *)
Lemma nr_rdword_kept : forall (rd rd' : Z -> option Z) a v,
  (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) ->
  rdword rd a = Some v -> rdword rd' a = Some v.
Proof.
  intros rd rd' a v Hk Hr. unfold rdword in *.
  replace a with (a + 0) at 1 by lia.
  rewrite (Hk 0 ltac:(lia)), (Hk 1 ltac:(lia)), (Hk 2 ltac:(lia)), (Hk 3 ltac:(lia)),
    (Hk 4 ltac:(lia)), (Hk 5 ltac:(lia)), (Hk 6 ltac:(lia)), (Hk 7 ltac:(lia)).
  rewrite Z.add_0_r. exact Hr.
Qed.

(* g_nl lies in one loaded segment, in no read-only segment, and in no runtime-owned static (computations over the
   image's segments and over the instance's owned-static table). *)
Lemma nr_gnl_img_b : existsb (fun s => (Z.of_N (seg_base s) <=? LA_G_NL) &&
    (LA_G_NL + NK_SIZE <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma nr_gnl_rw_b : forallb (fun s => seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? LA_G_NL) ||
    (LA_G_NL + NK_SIZE <=? Z.of_N (seg_base s))) tfibsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma nr_gnl_own_b : forallb (fun r : Z * Z => (fst r + snd r <=? LA_G_NL) || (LA_G_NL + NK_SIZE <=? fst r))
    Tfib_owned_static = true.
Proof. vm_compute. reflexivity. Qed.

Lemma nr_gnl_img : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> in_img tfibsegs a.
Proof.
  intros a Ha. destruct (proj1 (existsb_exists _ _) nr_gnl_img_b) as (s & Hin & Hs).
  apply andb_prop in Hs as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists s. split; [exact Hin | lia].
Qed.

(* the relro window lies in one loaded segment: a computation *)
Lemma nr_relro_b : existsb (fun s => (Z.of_N (seg_base s) <=? PCAP_RLO) &&
    (PCAP_RHI <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma nr_relro_img : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img tfibsegs a.
Proof.
  intros a Ha. destruct (proj1 (existsb_exists _ _) nr_relro_b) as (s & Hin & Hs).
  apply andb_prop in Hs as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists s. split; [exact Hin | lia].
Qed.

Lemma nr_gnl_not_ro_seg : forall s a, In s tfibsegs -> seg_writable s = false ->
  Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s) -> LA_G_NL <= a < LA_G_NL + NK_SIZE -> False.
Proof.
  intros s a Hin Hw Hs Ha. pose proof (proj1 (forallb_forall _ _) nr_gnl_rw_b s Hin) as H.
  cbv beta in H. rewrite Hw in H. cbn [orb] in H. apply orb_prop in H as [H|H]; apply Z.leb_le in H; lia.
Qed.

Lemma nr_gnl_not_owned : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> ~ Exists (in_zr a) Tfib_owned_static.
Proof.
  intros a Ha Hx. apply Exists_exists in Hx as (r & Hin & Hr). unfold in_zr in Hr.
  pose proof (proj1 (forallb_forall _ _) nr_gnl_own_b r Hin) as H.
  apply orb_prop in H as [H|H]; apply Z.leb_le in H; lia.
Qed.

Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.

(* The journal's window lies above the allocator's ceiling and below 2 ^ 47. *)
Lemma nr_aj_bounds : forall segs B G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k,
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
  alloc_ceiling <= sp0 - STK /\ sp0 + XO <= 2 ^ 47 /\ 0 <= STK /\ 0 <= XO.
Proof.
  intros segs B G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k (H0 & H1 & (memS & HJ & _) & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _). lia.
Qed.

(* The frames the journal's owner took are frames of the current state. *)
Lemma nr_aj_own : forall segs B G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k,
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
  forall c q, In (c, q) own -> In (c, q) (frames Sc).
Proof.
  intros segs B G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k (_ & _ & (memS & HJ & _) & _) c q Hin.
  pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. apply in_or_app. left. exact Hin.
Qed.

Lemma nr_aj_AR : forall segs B G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k,
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k -> AR segs B lyc Sc Wc memc mdc.
Proof. intros segs B G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k (_ & _ & (memS & HJ & _) & _). exact (proj1 HJ). Qed.

(* ajw at a later state of the same journal whose blocks and owned frames include the call's. *)
Lemma nr_ajw_mono : forall B G XO OUT STK sp0 FP ly S lyc Sc own lyc' Sc' own' a,
  ajw B G XO OUT STK sp0 FP ly S lyc Sc own a ->
  (forall b m, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B lyc' Sc')) ->
  (forall x, In x own -> In x own') ->
  (forall c q, frame_addr lyc' c q = frame_addr lyc c q) ->
  ajw B G XO OUT STK sp0 FP ly S lyc' Sc' own' a.
Proof.
  intros B G XO OUT STK sp0 FP ly S lyc Sc own lyc' Sc' own' a Hw Hbl Hown Hfa.
  destruct Hw as [(Haw & Hno) | [HGa | Hout]]; [left | right; left; exact HGa | right; right; exact Hout].
  split; [|exact Hno].
  destruct Haw as [Hs | [(Hf & b & n & Hin & Hr) | [(b & n & Hin & Hn0 & Hr) | (c & q & Hin & Hr)]]].
  - left. exact Hs.
  - right; left. split; [exact Hf|]. exists b, n. split; [exact (Hbl b n Hin) | exact Hr].
  - right; right; left. exists b, n. split; [exact (Hbl b n Hin)|]. split; [exact Hn0 | exact Hr].
  - right; right; right. exists c, q. split; [exact (Hown _ Hin)|]. rewrite !Hfa. exact Hr.
Qed.
End h.
(* ==========================================================================
   2. The facts every piece of the phase uses
   ========================================================================== *)

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ link_listing PI).
#[local] Abbreviation VAL := (@pa_val _ link_listing PI).
#[local] Abbreviation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis LV : LinkVals.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : SEGS = tfibsegs.
Hypothesis RECV : fuzz_recv_acontract SK SEGS PCAP_RLO PCAP_RHI B.
Hypothesis ERRNO : RtErrnoLoc.aerrno_location_realizes SEGS B (pa_sigma LS____errno_location).

(* the relro window is image bytes (a computation over the image's segments) *)
Lemma RELRO_IMG : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img SEGS a.
Proof. intros a Ha. rewrite HSEGS. exact (nr_relro_img a Ha). Qed.

Lemma nr_vals : BASE = 0x821cc /\ pa_sigma LS_fuzz_recv = 0x823cc /\ pa_sigma LS____errno_location = 0x90a7c.
Proof.
  split; [exact (lv_text LV)|].
  split; rewrite (lv_sigma LV); reflexivity.
Qed.

(* a machine state at a cut is the `mkst` of its registers, its pc and its memory *)
Lemma nr_ms_mkst : forall pc ms3, nt_shape pc ms3 ->
  ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + pc)) (ms_mem ms3) (seg_rom SEGS).
Proof.
  intros pc ms3 (Hpc & Hresv & Hsvc & Hrom & Hfregs & Hfcsr).
  destruct ms3 as [rg fr pcv svp rv fc mm rm];
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *.
  subst. reflexivity.
Qed.

(* the numbers of the call, from its premises *)
Lemma nr_base_facts : forall cx, nt_base SK B cx ->
  alloc_ceiling + NL_TALK_AK <= spZ (n_regs cx) /\ spZ (n_regs cx) <= n_sp0 cx /\
  n_sp0 cx + n_XO cx <= 2 ^ 47 /\ n_sp0 cx - n_STK cx <= spZ (n_regs cx) - NL_TALK_AK /\
  alloc_ceiling <= n_sp0 cx - n_STK cx /\ 0 <= n_XO cx /\
  spZ (n_regs cx) - 208 <= n_sp1 cx <= spZ (n_regs cx) - 192 /\ n_sp1 cx mod 32 = 0.
Proof.
  intros cx HB. destruct HB as (HA & _).
  destruct HA as (HJc & _ & _ & _ & _ & _ & _ & H16 & Hwlo & Hwhi & _).
  destruct (nr_aj_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as (Hceil & H47 & HSTK & HXO).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof NL_TALK_AK_val as EK. rewrite EK in *.
  set (sp := spZ (n_regs cx)) in *.
  assert (Hsp0 : 0 <= sp - NL_TALK_AFRAME) by (unfold NL_TALK_AFRAME; lia).
  destruct (nt_sp1_range sp Hsp0 H16) as (R1 & R2 & R3).
  unfold NL_TALK_AFRAME in R1. unfold n_sp1. fold sp.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [lia | exact R2].
Qed.

(* the numbers of the class-9 frame, from the journal at a cut *)
Lemma nr_frame_nums : forall cx fp ly3 S3 (W3 : world SEGS) mem3 md3,
  AR SEGS B ly3 S3 W3 mem3 md3 -> In (NT_CID, fp) (frames S3) ->
  (forall c p, frame_addr ly3 c p = frame_addr (n_lyc cx) c p) ->
  4096 <= nF cx fp /\ nF cx fp + 32768 <= alloc_ceiling /\ nF cx fp mod 64 = 0 /\
  nSH cx fp = SHADOW_OFF + nF cx fp / 8 /\
  (nF cx fp + 32768 <= kLowShadowBeg \/ kHighMemBeg <= nF cx fp) /\
  (forall a, nF cx fp <= a < nF cx fp + 32768 -> ~ in_img SEGS a).
Proof.
  intros cx fp ly3 S3 W3 mem3 md3 HAR Hin Hfa.
  destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 NT_CID fp HAR Hin) as (Hf4096 & Hfceil & Happ).
  destruct (frame_al64 SEGS B ly3 S3 W3 mem3 md3 NT_CID fp HAR Hin) as (Hal & _ & _).
  assert (EF : frame_addr ly3 NT_CID fp = nF cx fp) by (rewrite Hfa; reflexivity).
  rewrite EF in Hf4096, Hfceil, Happ, Hal. change (fs_frame_bytes NT_CID) with 32768 in *.
  split; [lia|]. split; [lia|]. split; [exact Hal|]. split; [reflexivity|].
  split.
  - unfold in_app in Happ. destruct Happ as (_ & [Hlow | [Hhi1 _]]); [left; lia | right; lia].
  - intros a Ha Hi. rewrite <- EF in Ha.
    exact (frm_img SEGS B LAWS ly3 S3 W3 mem3 md3 NT_CID fp a HAR Hin
             ltac:(change (fs_frame_bytes NT_CID) with 32768; exact Ha) Hi).
Qed.

(* the receive buffer's shadow, from the frame's (nt_frame_shadow with the buffer usable) *)
Lemma nr_buf_shadow : forall cx fp (W3 : world SEGS) ms3, nF cx fp mod 64 = 0 -> 0 <= nF cx fp ->
  nt_frame_shadow cx fp 0 W3 ms3 ->
  range_addressable (ard SEGS (rdW W3 (ms_mem ms3))) SHADOW_OFF (nBUF cx fp) NT_BUFLEN /\
  shadow_hull_vis (ard SEGS (rdW W3 (ms_mem ms3))) (nBUF cx fp) NT_BUFLEN.
Proof.
  intros cx fp W3 ms3 Hal H0 (F1 & F2 & F3). rewrite ard_aview.
  assert (ESH : nSH cx fp = SHADOW_OFF + nF cx fp / 8) by reflexivity.
  unfold nBUF, NT_BUFOFF, NT_BUFLEN. split.
  - intros x Hx. exists 0. split; [|left; reflexivity].
    unfold shadow_of_addr. replace (SHADOW_OFF + x / 8) with (nSH cx fp + 4 + (x / 8 - nF cx fp / 8 - 4)) by lia.
    apply F2. lia.
  - intros s Hs. unfold shadow_addr in Hs. unfold SHADOW_OFF in *.
    destruct (Z_lt_le_dec s (nSH cx fp + 4)) as [L1|L1].
    + replace s with (nSH cx fp + (s - nSH cx fp)) by lia. rewrite F1 by lia. discriminate.
    + destruct (Z_lt_le_dec s (nSH cx fp + 2052)) as [L2|L2].
      * replace s with (nSH cx fp + 4 + (s - nSH cx fp - 4)) by lia. rewrite F2 by lia. discriminate.
      * replace s with (nSH cx fp + 2052 + (s - nSH cx fp - 2052)) by lia. rewrite F3 by lia. discriminate.
Qed.

(* g_nl's bytes, in the forms akept's image clause and the read-only set need *)
Lemma nr_gnl_facts : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ in_roP SEGS PCAP_RLO PCAP_RHI a /\ a < kLowMemEnd.
Proof.
  intros a Ha. rewrite (ts_owned B TB). split; [rewrite HSEGS; exact (nr_gnl_img a Ha)|].
  split; [exact (nr_gnl_not_owned a Ha)|].
  split.
  - intros [(s & Hin & Hw & Hs) | Hr].
    + rewrite HSEGS in Hin. exact (nr_gnl_not_ro_seg s a Hin Hw Hs Ha).
    + unfold PCAP_RLO, PCAP_RHI, LA_G_NL, NK_SIZE in *. lia.
  - unfold LA_G_NL, NK_SIZE, kLowMemEnd in *. lia.
Qed.

(* errno is writable at any memory: it lies in the image's writable range (LinkWalkWseg.v) *)
Lemma nr_errno_wr : forall m, awrange SEGS m (as_errno B) 4.
Proof.
  intros m i Hi. rewrite (ts_errno B TB), HSEGS.
  apply wseg_writable_tfib_rng. unfold TFIB_ERRNO. lia.
Qed.

(* A read-only byte is an image byte. *)
Lemma nr_ro_img : forall a, in_roP SEGS PCAP_RLO PCAP_RHI a -> in_img SEGS a.
Proof.
  intros a [(s & Hin & _ & Hs) | Hr]; [exists s; split; [exact Hin | exact Hs] | exact (RELRO_IMG a Hr)].
Qed.

(* arodata_okP moves across a step that keeps every read-only byte outside the runtime's statics and errno. *)
Lemma nr_ro_kept : forall (rd rd' : Z -> option Z),
  arodata_okP SEGS PCAP_RLO PCAP_RHI B rd ->
  (forall a, in_roP SEGS PCAP_RLO PCAP_RHI a -> ~ Exists (in_zr a) (as_owned_static B) ->
     ~ (as_errno B <= a < as_errno B + 4) -> rd' a = rd a) ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B rd'.
Proof. intros rd rd' HR HK a Hro Hno Her. rewrite (HK a Hro Hno Her). exact (HR a Hro Hno Her). Qed.

(* two intervals, one of P-bytes and one of non-P bytes, are apart *)
Lemma nr_apart_of : forall (P : Z -> Prop) a n b k, 0 < n -> 0 < k ->
  (forall x, a <= x < a + n -> P x) -> (forall x, b <= x < b + k -> ~ P x) -> apart a n b k.
Proof.
  intros P a n b k Hn Hk HA HB. unfold apart.
  destruct (Z_le_gt_dec (a + n) b) as [L|L]; [left; exact L|].
  destruct (Z_le_gt_dec (b + k) a) as [L'|L']; [right; exact L'|].
  exfalso. apply (HB (Z.max a b)); [lia|]. apply HA. lia.
Qed.
(* ==========================================================================
   3. The model: the exchange's chunk loop and the message walk of one chunk
   ========================================================================== *)

(* the chunk queue of the exchange, and the answer its chunk loop gives *)
Definition nr_cs (cx : ntcx) : list (list byte) := k_chunks (n_K0 cx).
Definition nr_CL (cx : ntcx) : nlv * nat :=
  chunk_loop (S (length (nr_cs cx))) (nr_cs cx) (k_next (n_K0 cx)).

Lemma nr_owes : forall K, talk_owes K = true -> k_sock K = 0 /\ k_send K = 0.
Proof.
  intros K H. unfold talk_owes in H. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1, H2. split; assumption.
Qed.

(* the exchange's answer, once the chunk loop is known *)
Lemma nr_answer : forall cx v j, talk_owes (n_K0 cx) = true -> nr_CL cx = (v, j) ->
  talk_rc_lib (n_K0 cx) = nt_nlv_rc v (k_end (n_K0 cx)) /\ talk_attrs (n_K0 cx) = nt_nlv_attrs v /\
  k_next (talk_after (n_K0 cx)) = j.
Proof.
  intros cx v j Ho HL. destruct (nr_owes _ Ho) as [H1 H2].
  destruct (nt_talk_loop (n_K0 cx) H1 H2) as (R1 & R2 & R3 & _).
  unfold nr_CL, nr_cs in HL. rewrite HL in R1, R2, R3. cbn [fst snd] in R1, R2, R3.
  split; [exact R1|]. split; [exact R2|]. rewrite R3. reflexivity.
Qed.

(* the fuel of the chunk loop: enough for every chunk left *)
Definition nr_fuel (cs : list (list byte)) (j f : nat) : Prop := (length cs <= j \/ length cs < j + f)%nat.

Lemma nr_fuel_start : forall cs j, nr_fuel cs j (S (length cs)).
Proof. intros cs j. unfold nr_fuel. lia. Qed.

(* the chunk loop at a cursor past the queue *)
Lemma nr_cl_end : forall cs f j, (length cs <= j)%nat -> chunk_loop f cs j = (NlNone, j).
Proof. intros cs f j H. apply nt_chunk_loop_end. apply nth_error_None. exact H. Qed.

(* the chunk loop at a cursor inside the queue: one more chunk *)
Lemma nr_cl_some : forall cs f j, (j < length cs)%nat -> nr_fuel cs j f ->
  exists f' c, f = S f' /\ nth_error cs j = Some c /\ (length cs < S (j + f'))%nat.
Proof.
  intros cs f j Hj Hf. unfold nr_fuel in Hf. destruct f as [|f']; [lia|].
  destruct (nth_error cs j) as [c|] eqn:E; [|apply nth_error_None in E; lia].
  exists f', c. split; [reflexivity|]. split; [reflexivity|]. lia.
Qed.

Lemma nr_fuel_next : forall cs j f', (length cs < S (j + f'))%nat -> nr_fuel cs (S j) f'.
Proof. intros cs j f' H. unfold nr_fuel. lia. Qed.

(* a message walk that ends without an answer: the chunk loop takes the next chunk *)
Lemma nr_cl_none : forall cs f j c, nth_error cs j = Some c -> chunk_walk c = NlNone ->
  chunk_loop (S f) cs j = chunk_loop f cs (S j).
Proof. intros cs f j c E W. exact (nt_chunk_loop_step f cs j c E W). Qed.

Lemma nr_cl_hit : forall cs f j c v, nth_error cs j = Some c -> chunk_walk c = v -> v <> NlNone ->
  chunk_loop (S f) cs j = (v, S j).
Proof.
  intros cs f j c v E W N. rewrite <- W. apply nt_chunk_loop_hit; [exact E|]. rewrite W. exact N.
Qed.

(* the message walk at its first test, `bltu a0, s4` at +0x214: a chunk shorter than a header ends at once *)
Lemma nr_walk_short : forall c, Z.of_nat (length c) < 16 -> chunk_walk c = NlNone.
Proof.
  intros c H. unfold chunk_walk. cbn [msg_scan]. unfold NL_HDR.
  replace (Z.of_nat (length c) <? 16) with true by (symmetry; apply Z.ltb_lt; exact H). reflexivity.
Qed.

(* the walk's position after a step: what is left is below 16, so the walk ends *)
Lemma nr_msg_small : forall c g off left, left < 16 -> msg_scan g c off left = NlNone.
Proof.
  intros c [|g] off left H; [reflexivity|]. cbn [msg_scan]. unfold NL_HDR.
  replace (left <? 16) with true by (symmetry; apply Z.ltb_lt; exact H). reflexivity.
Qed.
(* ==========================================================================
   4. The state at the cuts of the receive phase, and the two loops' invariants
   ========================================================================== *)

(* What every cut of the phase keeps: the fixed fields of the machine state but its pc, the registers every phase
   keeps, s7 = alias_n, s9 = alias, s10 = the receive buffer, the saved registers, the frame's header, the five
   spill slots the body wrote before the first fuzz_recv, the frame's shadow with the buffer usable, the
   journal's bookkeeping, the kept clause, the owed request, the caller's buffers and the receive buffer. *)
Definition nr_com (cx : ntcx) (fp k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (md3 : Model) : Prop :=
  ms_resv ms3 = None /\ ms_svc_pending ms3 = None /\ ms_rom ms3 = seg_rom SEGS /\
  ms_fregs ms3 = fp_regs /\ ms_fcsr ms3 = fp_csr /\
  nt_regs cx fp ms3 /\ nt_saved cx W3 ms3 /\ nt_header cx fp W3 ms3 /\ nt_slots0 cx fp W3 ms3 /\
  nt_at W3 ms3 (n_sp1 cx + NS_SH4) (nSH cx fp + 4) /\
  nt_at W3 ms3 (n_sp1 cx + NS_FK) (nF cx fp) /\
  getr (ms_regs ms3) 23 = w64 (n_aliasn cx) /\
  getr (ms_regs ms3) 25 = w64 (n_alias cx) /\
  getr (ms_regs ms3) 26 = w64 (nBUF cx fp) /\
  nt_frame_shadow cx fp 0 W3 ms3 /\
  nt_jbk B cx fp k2 ly3 S3 md3 /\ nt_kept B cx (n_E cx) fp W3 (ms_mem ms3) /\
  talk_owes (n_K0 cx) = true /\
  nt_bufs_same cx (rdW W3 (ms_mem ms3)) /\
  abuf SEGS (rdW W3 (ms_mem ms3)) (nBUF cx fp) NT_BUFLEN.

(* g_nl with the receive cursor at j *)
Definition nr_gnl (cx : ntcx) (W3 : world SEGS) (ms3 : machine_state) (j : nat) : Prop :=
  exists bs, anlk_at SEGS (rdW W3 (ms_mem ms3)) LA_G_NL bs /\ nt_gnl_open cx bs true (Z.of_nat j).

(* the three constants of the message walk (+0x208..+0x210) *)
Definition nr_k3 (ms3 : machine_state) : Prop :=
  getr (ms_regs ms3) 19 = w64 2 /\ getr (ms_regs ms3) 20 = w64 16 /\ getr (ms_regs ms3) 22 = w64 15.

(* THE RECEIVE LOOP'S INVARIANT, at its head NT_next (+0x294): the next receive is about to be made with the
   cursor at j, and the exchange's chunk loop is the chunk loop from j with fuel f, enough for every chunk left. *)
Definition nr_next_inv (j f : nat) (cx : ntcx) (fp k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (md3 : Model) : Prop :=
  nt_shape NT_next ms3 /\ nr_com cx fp k2 ly3 S3 W3 ms3 md3 /\
  nt_at W3 ms3 (n_sp1 cx + NS_FD) NL_FD /\ nr_k3 ms3 /\
  nr_gnl cx W3 ms3 j /\
  nr_CL cx = chunk_loop f (nr_cs cx) j /\ nr_fuel (nr_cs cx) j f.

(* The chunk the receive at cursor j answered: it is the queue's chunk j, it lies at the front of the buffer,
   and the cursor has moved past it. *)
Definition nr_chunk (j f : nat) (c rest : list byte) (cx : ntcx) (fp : Z) (W3 : world SEGS)
    (ms3 : machine_state) : Prop :=
  nr_gnl cx W3 ms3 (S j) /\
  nth_error (nr_cs cx) j = Some c /\
  nr_CL cx = chunk_loop (S f) (nr_cs cx) j /\ (length (nr_cs cx) < S (j + f))%nat /\
  abytes SEGS (rdW W3 (ms_mem ms3)) (nBUF cx fp) (c ++ rest) /\
  Z.of_nat (length (c ++ rest)) = NT_BUFLEN /\ (length c <= Z.to_nat NL_CHUNK_MAX)%nat.

(* THE MESSAGE LOOP'S INVARIANT, at its head NT_loop (+0x21c): a1 = the message at off in the chunk, a0 = the
   bytes left, and the chunk's walk is msg_scan from there with fuel g. *)
Definition nr_loop_inv (j f : nat) (c rest : list byte) (off left : Z) (g : nat) (cx : ntcx) (fp k2 : Z)
    (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  nt_shape NT_loop ms3 /\ nr_com cx fp k2 ly3 S3 W3 ms3 md3 /\
  nt_at W3 ms3 (n_sp1 cx + NS_FD) NL_FD /\ nr_k3 ms3 /\
  getr (ms_regs ms3) 10 = w64 left /\
  getr (ms_regs ms3) 11 = w64 (nBUF cx fp + off) /\
  nr_chunk j f c rest cx fp W3 ms3 /\
  chunk_walk c = msg_scan g c off left /\
  0 <= off /\ off + left = Z.of_nat (length c) /\ 16 <= left /\ (Z.to_nat left < g)%nat.

(* The chunk walk's entry NT_walk (+0x214): a0 = the chunk's length. *)
Definition nr_walk_inv (j f : nat) (c rest : list byte) (cx : ntcx) (fp k2 : Z)
    (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  nt_shape NT_walk ms3 /\ nr_com cx fp k2 ly3 S3 W3 ms3 md3 /\
  nt_at W3 ms3 (n_sp1 cx + NS_FD) NL_FD /\ nr_k3 ms3 /\
  getr (ms_regs ms3) 10 = w64 (Z.of_nat (length c)) /\
  nr_chunk j f c rest cx fp W3 ms3.

(* The failure arm NT_fail_rv (+0x2ac): the receive at cursor j found the queue empty and set errno. *)
Definition nr_fail_inv (j : nat) (cx : ntcx) (fp k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (md3 : Model) : Prop :=
  nt_shape NT_fail_rv ms3 /\ nr_com cx fp k2 ly3 S3 W3 ms3 md3 /\
  nt_at W3 ms3 (n_sp1 cx + NS_FD) NL_FD /\
  nr_gnl cx W3 ms3 j /\ nr_CL cx = (NlNone, j) /\
  au32_at SEGS (rdW W3 (ms_mem ms3)) (as_errno B) (k_end (n_K0 cx)).
(* ==========================================================================
   5. The call of fuzz_recv (+0x200 and +0x2a4), under SRr_bind on the journal
   ========================================================================== *)

(* the state at fuzz_recv's first slot: a0 = the socket, a1 = the buffer, a2 = its length, ra = the return *)
Definition nr_pre (retk : Z) (j : nat) (cx : ntcx) (fp k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (md3 : Model) : Prop :=
  ms_pc_val ms3 = Z_to_bv 64 FUZZ_RECV_A /\
  nr_com cx fp k2 ly3 S3 W3 ms3 md3 /\ nt_at W3 ms3 (n_sp1 cx + NS_FD) NL_FD /\ nr_gnl cx W3 ms3 j /\
  getr (ms_regs ms3) 1 = w64 (BASE + retk) /\ getr (ms_regs ms3) 10 = w64 NL_FD /\
  getr (ms_regs ms3) 11 = w64 (nBUF cx fp) /\ getr (ms_regs ms3) 12 = w64 NT_BUFLEN.

(* the state fuzz_recv returns: everything of the cut kept, the callee-saved registers of the call, and either the
   queue was empty (a0 = -1, errno = end_errno) or the cursor's chunk is at the front of the buffer *)
Definition nr_rcvd (retk : Z) (j : nat) (regs0 : bvmap 5 word) (cx : ntcx) (fp k2 : Z) (ly3 : alayout)
    (S3 : astate) (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  nt_shape retk ms3 /\ nr_com cx fp k2 ly3 S3 W3 ms3 md3 /\ nt_at W3 ms3 (n_sp1 cx + NS_FD) NL_FD /\
  (forall r, acallee_saved r -> getr (ms_regs ms3) (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r)) /\
  (((length (nr_cs cx) <= j)%nat /\ getr (ms_regs ms3) 10 = w64 (-1) /\ nr_gnl cx W3 ms3 j /\
      au32_at SEGS (rdW W3 (ms_mem ms3)) (as_errno B) (k_end (n_K0 cx))) \/
   ((j < length (nr_cs cx))%nat /\ exists c rest, nth_error (nr_cs cx) j = Some c /\
      getr (ms_regs ms3) 10 = w64 (Z.of_nat (length c)) /\ nr_gnl cx W3 ms3 (S j) /\
      abytes SEGS (rdW W3 (ms_mem ms3)) (nBUF cx fp) (c ++ rest) /\
      Z.of_nat (length (c ++ rest)) = NT_BUFLEN /\ (length c <= Z.to_nat NL_CHUNK_MAX)%nat)).

Lemma nr_aarg1 : forall regs, aarg regs 1 = bv_unsigned (getr regs 11).
Proof. intros regs. reflexivity. Qed.
Lemma nr_aarg2 : forall regs, aarg regs 2 = bv_unsigned (getr regs 12).
Proof. intros regs. reflexivity. Qed.
Lemma nr_aarg0 : forall regs, aarg regs 0 = bv_unsigned (getr regs 10).
Proof. intros regs. reflexivity. Qed.

(* the numbers of a cut, in one place *)
Lemma nr_cut_nums : forall cx fp k2 ly3 S3 W3 ms3 md3,
  nt_base SK B cx ->
  ajournal_gx SEGS B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NT_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  frames S3 = (NT_CID, fp) :: frames (n_Sc cx) ->
  nr_com cx fp k2 ly3 S3 W3 ms3 md3 ->
  alloc_ceiling + NL_TALK_AK <= spZ (n_regs cx) /\ spZ (n_regs cx) <= n_sp0 cx /\
  n_sp0 cx + n_XO cx <= 2 ^ 47 /\ n_sp0 cx - n_STK cx <= spZ (n_regs cx) - NL_TALK_AK /\
  alloc_ceiling <= n_sp0 cx - n_STK cx /\ 0 <= n_XO cx /\
  spZ (n_regs cx) - 208 <= n_sp1 cx <= spZ (n_regs cx) - 192 /\ n_sp1 cx mod 32 = 0 /\
  4096 <= nF cx fp /\ nF cx fp + 32768 <= alloc_ceiling /\ nF cx fp mod 64 = 0 /\
  nSH cx fp = SHADOW_OFF + nF cx fp / 8 /\
  (nF cx fp + 32768 <= kLowShadowBeg \/ kHighMemBeg <= nF cx fp) /\
  (forall a, nF cx fp <= a < nF cx fp + 32768 -> ~ in_img SEGS a) /\
  AR SEGS B ly3 S3 W3 (ms_mem ms3) md3 /\ In (NT_CID, fp) (frames S3) /\
  (forall c p, frame_addr ly3 c p = frame_addr (n_lyc cx) c p).
Proof.
  intros cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR HC.
  pose proof (nr_base_facts cx HB) as BF.
  pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJB & _).
  pose proof HJB as (_ & _ & _ & _ & _ & Hfa & _).
  pose proof (nr_aj_AR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  assert (Hin : In (NT_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
  pose proof (nr_frame_nums cx fp ly3 S3 W3 (ms_mem ms3) md3 HAR Hin Hfa) as FN.
  destruct BF as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
  destruct FN as (F1 & F2 & F3 & F4 & F5 & F6).
  exact (conj B1 (conj B2 (conj B3 (conj B4 (conj B5 (conj B6 (conj B7 (conj B8 (conj F1 (conj F2 (conj F3
    (conj F4 (conj F5 (conj F6 (conj HAR (conj Hin Hfa)))))))))))))))).
Qed.

(* the receive buffer lies in our frame, below the ceiling, off the image, apart from g_nl and errno *)
Lemma nr_buf_where : forall cx fp,
  4096 <= nF cx fp -> nF cx fp + 32768 <= alloc_ceiling ->
  (forall a, nF cx fp <= a < nF cx fp + 32768 -> ~ in_img SEGS a) ->
  apart_gnl LA_G_NL (nBUF cx fp) NT_BUFLEN /\
  (forall a, nBUF cx fp <= a < nBUF cx fp + NT_BUFLEN -> ~ in_img SEGS a /\ a < alloc_ceiling /\
     nF cx fp <= a < nF cx fp + fs_frame_bytes NT_CID).
Proof.
  intros cx fp H4 Hc Hni. unfold nBUF, NT_BUFOFF, NT_BUFLEN. change (fs_frame_bytes NT_CID) with 32768.
  split.
  - unfold apart_gnl. pose proof (nr_apart_of (in_img SEGS) LA_G_NL NK_SIZE (nF cx fp + 32) 16384) as HA.
    unfold apart in HA. destruct HA as [HA|HA]; [unfold NK_SIZE; lia | lia | | | right; exact HA | left; exact HA].
    + intros x Hx. exact (proj1 (nr_gnl_facts x Hx)).
    + intros x Hx. apply Hni. lia.
  - intros a Ha. split; [apply Hni; lia|]. lia.
Qed.

(* the callee's premises at a call of fuzz_recv *)
Lemma nr_call_pre : forall retk j cx fp k2 ly3 S3 W3 ms3 md3,
  nt_base SK B cx ->
  ajournal_gx SEGS B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NT_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  frames S3 = (NT_CID, fp) :: frames (n_Sc cx) ->
  nr_pre retk j cx fp k2 ly3 S3 W3 ms3 md3 -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  apre SK SEGS PCAP_RLO PCAP_RHI B FUZZ_RECV_AK 0 [] (fuzz_recv_awr (ms_regs ms3) (rdW W3 (ms_mem ms3)))
    (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx)
    (n_md0 cx) ((NT_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 (ms_regs ms3) /\
  fuzz_recv_apre SEGS B (ms_regs ms3) (rdW W3 (ms_mem ms3)).
Proof.
  intros retk j cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR HPRE Hrk Hrk2.
  pose proof HPRE as (Hpc & HC & HFD & (bs & HNK & HGO) & R1 & R10 & R11 & R12).
  pose proof (nr_cut_nums cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR HC) as
    (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & F1 & F2 & F3 & F4 & F5 & F6 & HAR & Hin & Hfa).
  pose proof HC as (_ & _ & _ & _ & _ & HRG & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJB & HKP & _ & _ & HAB).
  pose proof HRG as (Rsp & Rs0 & Rs1 & Rs2 & Rs5 & Rs8 & Rgp & Rtp).
  pose proof HJB as (Hk2 & Hperm & HSfs & _ & _ & _ & _ & _ & _).
  pose proof HKP as (_ & HRO & _).
  pose proof HB as (HA & _ & HNP & _).
  pose proof HA as (_ & HGX & _ & _ & _ & Hgpc & Htpc & _ & _ & _ & Hev & _ & Hajw & _).
  pose proof HNP as (kbs & req & _ & _ & _ & _ & _ & _ & _ & (Herr & _ & _ & _ & Hegn) & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof NL_TALK_AK_val as EK. rewrite EK in *.
  destruct nr_vals as (VB & VR & VE).
  destruct (nr_buf_where cx fp F1 F2 F6) as (HBG & HBW).
  assert (USP : spZ (ms_regs ms3) = n_sp1 cx) by (unfold spZ; rewrite Rsp; unfold w64; apply unsigned_lit_small; lia).
  assert (A1 : aarg (ms_regs ms3) 1 = nBUF cx fp)
    by (rewrite nr_aarg1, R11; unfold w64, nBUF, NT_BUFOFF; apply unsigned_lit_small; lia).
  assert (A2 : aarg (ms_regs ms3) 2 = NT_BUFLEN)
    by (rewrite nr_aarg2, R12; unfold w64, NT_BUFLEN; apply unsigned_lit_small; lia).
  unfold FUZZ_RECV_AK, FUZZ_RECV_AFRAME, ESTACK.
  split.
  - unfold apre.
    split; [exact HJ|]. split; [exact HGX|]. split; [exact HRO|].
    split; [rewrite R1; unfold w64; apply ret_ok_codeptr_v; lia|].
    split; [unfold raZ; rewrite R1, VB; unfold w64; rewrite unsigned_lit_small by lia; lia|].
    split; [rewrite Rgp; exact Hgpc|]. split; [rewrite Rtp; exact Htpc|].
    rewrite USP. split; [apply Z.mod_divide; [lia|]; apply Z.mod_divide in B8; [|lia]; destruct B8 as [q Hq]; exists (2 * q); lia|].
    split; [lia|]. split; [lia|].
    split; [rewrite Hk2; exact Hev|].
    split; [apply Forall_nil|].
    split.
    + intros a Ha. unfold fuzz_recv_awr in Ha. rewrite A1, A2 in Ha.
      apply inFP_cons in Ha as [Ha | Ha].
      * apply (nr_ajw_mono B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
          (n_lyc cx) (n_Sc cx) (n_own cx) ly3 S3 ((NT_CID, fp) :: n_own cx) a).
        -- apply Hajw. exists (LA_G_NL, LA_G_NL + NK_N_SENT + 4). split; [left; reflexivity|].
           cbn [fst snd]. unfold NK_NEXT, NK_MISUSE, NK_N_SENT in *. lia.
        -- intros b m Hbm. apply (Permutation_in _ (Permutation_sym Hperm)). exact Hbm.
        -- intros x Hx. right. exact Hx.
        -- exact Hfa.
      * apply inFP_cons in Ha as [Ha | Ha]; [|destruct Ha as (r & Hr & _); destruct Hr].
        destruct (HBW a Ha) as (_ & Hac & Haf).
        left. split; [|lia].
        right; right; right. exists NT_CID, fp. split; [left; reflexivity|].
        left. unfold in_zr. cbn [fst snd]. rewrite Hfa. exact Haf.
    + intros a Ha. unfold fuzz_recv_awr in Ha. rewrite A1, A2 in Ha.
      apply inFP_cons in Ha as [Ha | Ha].
      * exact (proj1 (proj2 (proj2 (nr_gnl_facts a ltac:(unfold NK_NEXT, NK_MISUSE, NK_SIZE in *; lia))))).
      * apply inFP_cons in Ha as [Ha | Ha]; [|destruct Ha as (r & Hr & _); destruct Hr].
        intros Hro. exact (proj1 (HBW a Ha) (nr_ro_img a Hro)).
  - unfold fuzz_recv_apre. exists bs.
    pose proof HGO as (WF & _).
    destruct (zsh_gnl_ard B TB SEGS ly3 S3 W3 (ms_mem ms3) md3 HAR) as (Gra & Ghv).
    destruct (zsh_errno_ard B TB SEGS ly3 S3 W3 (ms_mem ms3) md3 HAR) as (Era & _).
    destruct (nr_buf_shadow cx fp W3 ms3 F3 ltac:(lia) (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2
      (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HC)))))))))))))))) as (Bra & Bhv).
    rewrite A1, A2.
    split; [exact HNK|]. split; [exact WF|]. split; [exact Gra|]. split; [exact Ghv|].
    split; [exact Herr|]. split; [apply nr_errno_wr|]. split; [exact Era|].
    split; [unfold apart_frame; rewrite USP, FUZZ_RECV_AK_val; left; rewrite (ts_errno B TB); unfold TFIB_ERRNO;
            lia|].
    split; [exact Hegn|].
    split; [unfold NL_CHUNK_MAX, NT_BUFLEN; lia|].
    split; [unfold nBUF, NT_BUFOFF; lia|].
    split; [exact HAB|].
    split; [unfold amem_range, nBUF, NT_BUFOFF, NT_BUFLEN; rewrite C3, C4, C5;
            destruct F5 as [F5|F5]; [left; unfold kLowShadowBeg in F5; lia | right; rewrite C3 in F5; lia]|].
    split; [exact Bra|]. split; [exact Bhv|]. split; [exact HBG|].
    unfold apart_frame. rewrite USP, FUZZ_RECV_AK_val. left. unfold nBUF, NT_BUFOFF, NT_BUFLEN. lia.
Qed.

(* the position of our frame, from the AR of a state where it is live *)
Lemma nr_fp_range : forall ly3 S3 (W3 : world SEGS) mem3 md3 fp,
  AR SEGS B ly3 S3 W3 mem3 md3 -> In (NT_CID, fp) (frames S3) -> 0 <= fp < fs_frames NT_CID.
Proof.
  intros ly3 S3 W3 mem3 md3 fp HAR Hin. destruct HAR as [M _].
  destruct (frame_facts B ly3 S3 _ _ _ M Hin) as (_ & H6 & _). exact H6.
Qed.

(* a byte the step left as it was, at an address the cut reads a word from *)
Lemma nr_at_kept : forall (W3 W2 : world SEGS) ms3 ms2 a v,
  (forall i, 0 <= i < 8 -> aview SEGS (w_H W2) (ms_mem ms2) (a + i) = aview SEGS (w_H W3) (ms_mem ms3) (a + i)) ->
  nt_at W3 ms3 a v -> nt_at W2 ms2 a v.
Proof. intros W3 W2 ms3 ms2 a v Hk H. exact (nr_rdword_kept _ _ a v Hk H). Qed.

(* a non-image byte that is writable is present *)
Lemma nr_present_of_writable : forall (H : word -> bool) (m : word -> option byte) a,
  0 <= a < 2 ^ 64 -> ~ in_img SEGS a -> writable_at SEGS (mrestrict H m) a -> apresent H m a.
Proof.
  intros H m a Ha Hn Hw. unfold apresent. unfold writable_at, wview, mrestrict in Hw.
  rewrite unsigned_lit_small in Hw by lia.
  match type of Hw with context [find_segment ?s ?x ?n] =>
    destruct (find_segment s x n) as [sg|] eqn:Ef end.
  { exfalso. apply Hn. destruct (find_segment_hit _ _ _ _ Ef) as (Hin & H1 & H2). exists sg. split; [exact Hin | lia]. }
  destruct (H (Z_to_bv 64 a)) eqn:E; try rewrite E in Hw; [exfalso; apply Hw; reflexivity|].
  split; [reflexivity|]. destruct (m (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity|].
  try rewrite Eb in Hw. exfalso. apply Hw. reflexivity.
Qed.

(* the caller's two buffers, when every byte of each is the same byte and stays writable *)
Lemma nr_bufs_frame : forall cx (m m' : word -> option byte),
  (n_kind cx <> 0 -> 1 <= n_kindn cx -> forall a, n_kind cx <= a < n_kind cx + n_kindn cx ->
     mbyte SEGS m' a = mbyte SEGS m a /\ (writable_at SEGS m a -> writable_at SEGS m' a)) ->
  (n_alias cx <> 0 -> 1 <= n_aliasn cx -> forall a, n_alias cx <= a < n_alias cx + n_aliasn cx ->
     mbyte SEGS m' a = mbyte SEGS m a /\ (writable_at SEGS m a -> writable_at SEGS m' a)) ->
  nt_bufs_same cx m -> nt_bufs_same cx m'.
Proof.
  intros cx m m' HK HA (F1 & F2 & F3 & F4).
  assert (Hstr : forall p n, (p <> 0 -> 1 <= n -> forall a, p <= a < p + n ->
            mbyte SEGS m' a = mbyte SEGS m a /\ (writable_at SEGS m a -> writable_at SEGS m' a)) ->
          p <> 0 -> forall s, Z.of_nat (length s) < n -> acstr_at SEGS m p s -> acstr_at SEGS m' p s).
  { intros p n Hk Hp s Hs (Hb & Hnz). split; [|exact Hnz].
    destruct Hb as (Hb0 & Hb1 & Hb2). split; [exact Hb0|]. split; [exact Hb1|].
    intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    rewrite (proj1 (Hk Hp ltac:(lia) (p + Z.of_nat i) ltac:(lia))). exact (Hb2 i ltac:(rewrite length_app; cbn [length]; lia)). }
  assert (Hbuf : forall p n, (p <> 0 -> 1 <= n -> forall a, p <= a < p + n ->
            mbyte SEGS m' a = mbyte SEGS m a /\ (writable_at SEGS m a -> writable_at SEGS m' a)) ->
          p <> 0 -> 1 <= n -> abuf SEGS m p n -> abuf SEGS m' p n).
  { intros p n Hk Hp Hn (junk & Hl & (Hb0 & Hb1 & Hb2) & Hw). exists junk. split; [exact Hl|].
    split; [split; [exact Hb0|]; split; [exact Hb1|]|].
    - intros i Hi. rewrite (proj1 (Hk Hp Hn (p + Z.of_nat i) ltac:(lia))). exact (Hb2 i Hi).
    - intros i Hi. apply (proj2 (Hk Hp Hn (p + i) ltac:(lia))). exact (Hw i Hi). }
  split; [intros Hk s Hs Hc; exact (Hstr (n_kind cx) (n_kindn cx) HK Hk s Hs (F1 Hk s Hs Hc))|].
  split; [intros Hk s Hs Hc; exact (Hstr (n_alias cx) (n_aliasn cx) HA Hk s Hs (F2 Hk s Hs Hc))|].
  split; [intros Hk Hn; exact (Hbuf (n_kind cx) (n_kindn cx) HK Hk Hn (F3 Hk Hn))|].
  intros Hk Hn. exact (Hbuf (n_alias cx) (n_aliasn cx) HA Hk Hn (F4 Hk Hn)).
Qed.

(* an ajw byte of the call is kept by a later callee's akept, stated at the callee's call state, outside the
   callee's window, its exception set and errno *)
Lemma nr_ajw_kept : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
    ly1 S1 (W1 : world SEGS) m1 (W2 : world SEGS) m2 slo shi (Ec : Z -> Prop) a,
  gx_ok SEGS B G ->
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  ajw B G XO OUT STK sp0 FP ly S lyc Sc own a ->
  akept SEGS B ly1 S1 W1 m1 W2 m2 slo shi Ec ->
  (forall b m, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly1 S1)) ->
  (forall c q, In (c, q) (frames Sc) -> In (c, q) (frames S1)) ->
  (forall c q, frame_addr ly1 c q = frame_addr lyc c q) ->
  ~ (slo <= a < shi) -> ~ Ec a -> ~ (as_errno B <= a < as_errno B + 4) ->
  aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a.
Proof.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ly1 S1 W1 m1 W2 m2 slo shi Ec a
    HG HJ Hw (K1 & K2 & K3 & K4 & _) Hbl Hfr Hfa Hwin HnE Herr.
  destruct (nr_aj_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (Hceil & H47 & HSTK & HXO).
  destruct Hw as [(Haw & Hno) | [HGa | (_ & Hout)]].
  - destruct Haw as [Hs | [(_ & b & n & Hin & Hr) | [(b & n & Hin & _ & Hr) | (c & q & Hin & Hr)]]].
    + apply K1; [lia | exact Hwin | exact HnE].
    + replace a with (b + (a - b)) by lia. apply (K2 b n (a - b) (Hbl b n Hin)); [lia|].
      replace (b + (a - b)) with a by lia. exact HnE.
    + replace a with (b + (a - b)) by lia. apply (K2 b n (a - b) (Hbl b n Hin)); [lia|].
      replace (b + (a - b)) with a by lia. exact HnE.
    + apply (K4 c q a (Hfr c q (nr_aj_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ c q Hin))); [|exact HnE].
      unfold frame_rng, in_zr. cbn [fst snd]. rewrite !Hfa. exact Hr.
  - destruct (HG a HGa) as (Hi & Hno). exact (K3 a Hi Hno Herr HnE).
  - apply K1; [lia | exact Hwin | exact HnE].
Qed.

Lemma nr_preserved : forall regs regs2, aregs_preserved regs regs2 ->
  forall (r : bv 5), acallee_saved (bv_unsigned r) -> getr regs2 r = getr regs r.
Proof. intros regs regs2 HP r Hr. rewrite <- (Z_to_bv_bv_unsigned 5 r). apply HP. exact Hr. Qed.

Ltac nr_cs :=
  match goal with |- acallee_saved (bv_unsigned ?r) =>
    let z := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with z end;
  unfold acallee_saved; lia.

(* the registers a cut keeps, across a step that keeps the callee-saved registers *)
Lemma nr_regs_keep : forall cx fp (ms ms' : machine_state),
  (forall (r : bv 5), acallee_saved (bv_unsigned r) -> getr (ms_regs ms') r = getr (ms_regs ms) r) ->
  nt_regs cx fp ms -> nt_regs cx fp ms'.
Proof.
  intros cx fp ms ms' HP (R2 & R8 & R9 & R18 & R21 & R24 & R3 & R4). unfold nt_regs.
  split; [rewrite HP by nr_cs; exact R2|]. split; [rewrite HP by nr_cs; exact R8|].
  split; [rewrite HP by nr_cs; exact R9|]. split; [rewrite HP by nr_cs; exact R18|].
  split; [rewrite HP by nr_cs; exact R21|]. split; [rewrite HP by nr_cs; exact R24|].
  split; [rewrite HP by nr_cs; exact R3|]. rewrite HP by nr_cs; exact R4.
Qed.

(* two byte lists agreeing at every index of [o, o + n) have the same slice there *)
Lemma nr_slice_eq : forall (bs bs' : list byte) o n, 0 <= o -> 0 <= n ->
  o + n <= Z.of_nat (length bs) -> o + n <= Z.of_nat (length bs') ->
  (forall i, o <= i < o + n -> nth_error bs' (Z.to_nat i) = nth_error bs (Z.to_nat i)) ->
  slice bs' o n = slice bs o n.
Proof.
  intros bs bs' o n Ho Hn H1 H2 Hk.
  apply lw_list_ext.
  - rewrite !lw_slice_length by lia. reflexivity.
  - intros k Hkl. rewrite lw_slice_length in Hkl by lia.
    rewrite !lw_slice_nth by lia.
    replace (Z.to_nat o + k)%nat with (Z.to_nat (o + Z.of_nat k)) by lia. apply Hk. lia.
Qed.

(* g_nl after fuzz_recv: the fields outside its written window are the call's *)
Lemma nr_gnl_after : forall cx (m m' : word -> option byte) bs bs' nextv,
  anlk_at SEGS m LA_G_NL bs -> anlk_at SEGS m' LA_G_NL bs' ->
  (forall i, 0 <= i < NK_SIZE -> ~ (NK_NEXT <= i < NK_MISUSE + 4) ->
     mbyte SEGS m' (LA_G_NL + i) = mbyte SEGS m (LA_G_NL + i)) ->
  nt_gnl_open cx bs true nextv ->
  nlk_wf bs' -> nk_n_chunks bs' = nk_n_chunks bs -> nk_end_errno bs' = nk_end_errno bs ->
  nk_socket_errno bs' = nk_socket_errno bs -> nk_send_errno bs' = nk_send_errno bs ->
  nk_chunks bs' = nk_chunks bs -> nk_open bs' = nk_open bs -> nk_opened bs' = nk_opened bs ->
  nk_closed bs' = nk_closed bs -> nk_n_sent bs' = nk_n_sent bs -> nk_misuse bs' = nk_misuse bs ->
  forall nextv', nk_next bs' = nextv' -> nt_gnl_open cx bs' true nextv'.
Proof.
  intros cx m m' bs bs' nextv (((_ & _ & Hb) & _) & Hl) (((_ & _ & Hb') & _) & Hl') Hk
    (WF & Ech & Enc & Eee & Eif & Eso & Ese & Eop & Emi & Eon & Ecl & Enx & Esn & Ens)
    WF' F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 nextv' Hnx'.
  assert (Hagree : forall i, 0 <= i < NK_SIZE -> ~ (NK_NEXT <= i < NK_MISUSE + 4) ->
            nth_error bs' (Z.to_nat i) = nth_error bs (Z.to_nat i)).
  { intros i Hi Hn. rewrite <- (Hb' (Z.to_nat i) ltac:(lia)), <- (Hb (Z.to_nat i) ltac:(lia)).
    rewrite Z2Nat.id by lia. exact (Hk i Hi Hn). }
  assert (Eif' : nk_n_if bs' = nk_n_if bs).
  { unfold nk_n_if, fld_u32, NK_N_IF. apply rdn_agree; [lia | lia | rewrite Hl; unfold NK_SIZE; lia | rewrite Hl'; unfold NK_SIZE; lia|].
    intros k Hk'. replace (Z.to_nat 271984 + k)%nat with (Z.to_nat (271984 + Z.of_nat k)) by lia.
    apply Hagree; unfold NK_SIZE, NK_NEXT, NK_MISUSE; lia. }
  assert (Esent : nk_sent bs' = nk_sent bs).
  { apply (nt_nk_sent_keep bs bs' WF). apply nr_slice_eq;
      [unfold NK_SENT; lia | unfold NK_SENT, NK_N_SENT; lia | rewrite Hl; unfold NK_SENT, NK_N_SENT, NK_SIZE; lia
      | rewrite Hl'; unfold NK_SENT, NK_N_SENT, NK_SIZE; lia |].
    intros i Hi. apply Hagree; unfold NK_SENT, NK_N_SENT, NK_SIZE, NK_NEXT, NK_MISUSE in *; lia. }
  unfold nt_gnl_open.
  split; [exact WF'|]. split; [rewrite F5; exact Ech|]. split; [rewrite F1; exact Enc|].
  split; [rewrite F2; exact Eee|]. split; [rewrite Eif'; exact Eif|].
  split; [rewrite F3; exact Eso|]. split; [rewrite F4; exact Ese|]. split; [rewrite F6; exact Eop|].
  split; [rewrite F10; exact Emi|]. split; [rewrite F7; exact Eon|]. split; [rewrite F8; exact Ecl|].
  split; [exact Hnx'|]. split; [rewrite Esent; exact Esn|].
  rewrite F9, Esent. exact Ens.
Qed.

(* a byte of a caller buffer (kind or alias, pointer not NULL) survives the call of fuzz_recv: its value and its
   writability *)
Lemma nr_buf_byte_call : forall cx fp k2 ly3 S3 (W3 : world SEGS) mem3 md3 (W2 : world SEGS) mem2 slo shi
    (Ec : Z -> Prop) p n a,
  nt_base SK B cx ->
  ajournal_gx SEGS B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NT_CID, fp) :: n_own cx) ly3 S3 W3 mem3 md3 k2 ->
  frames S3 = (NT_CID, fp) :: frames (n_Sc cx) ->
  nt_jbk B cx fp k2 ly3 S3 md3 ->
  akept SEGS B ly3 S3 W3 mem3 W2 mem2 slo shi Ec ->
  spZ (n_regs cx) - NL_TALK_AK <= slo -> shi <= spZ (n_regs cx) ->
  (forall x, Ec x -> LA_G_NL <= x < LA_G_NL + NK_SIZE \/ aside_rng (n_lyc cx) NT_CID fp x) ->
  (p, p + n) = aivl p n -> In (p, p + n) (n_Wr cx) -> p <> 0 -> 1 <= n ->
  apart_frame (n_regs cx) NL_TALK_AK p n -> apart_gnl LA_G_NL p n -> apart (as_errno B) 4 p n ->
  amem_range p n -> 0 <= p ->
  p <= a < p + n ->
  mbyte SEGS (rdW W2 mem2) a = mbyte SEGS (rdW W3 mem3) a /\
  (writable_at SEGS (rdW W3 mem3) a -> writable_at SEGS (rdW W2 mem2) a).
Proof.
  intros cx fp k2 ly3 S3 W3 mem3 md3 W2 mem2 slo shi Ec p n a HB HJ HFR HJB HK Hslo Hshi HEc Haivl HinW Hp Hn
    Hapf Hapg Hape Hamr Hp0 Ha.
  pose proof HB as (HA & _).
  pose proof HA as (HJc & HGX & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hajw & Hnro).
  pose proof HJB as (_ & Hperm & _ & _ & HnIn & Hfa & _).
  pose proof (nr_aj_AR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  assert (Hin9 : In (NT_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
  pose proof (nr_fp_range ly3 S3 W3 mem3 md3 fp HAR Hin9) as Hfp.
  pose proof NL_TALK_AK_val as EK.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct (nr_aj_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as (Hceil & _ & _ & _).
  assert (HW : inFP (n_Wr cx) a) by (exists (p, p + n); split; [exact HinW | cbn [fst snd]; lia]).
  pose proof (Hajw a HW) as Hw0.
  assert (Hw3 : ajw B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
                  ly3 S3 ((NT_CID, fp) :: n_own cx) a).
  { apply (nr_ajw_mono B _ _ _ _ _ _ _ _ (n_lyc cx) (n_Sc cx) (n_own cx) ly3 S3 _ a Hw0);
      [intros b m Hbm; apply (Permutation_in _ (Permutation_sym Hperm)); exact Hbm
      | intros x Hx; right; exact Hx | exact Hfa]. }
  assert (Happ : a < kLowMemEnd \/ kHighMemBeg <= a).
  { unfold amem_range in Hamr. rewrite C5, C3. rewrite C5, C3 in Hamr. lia. }
  assert (Hns : ~ aside_rng (n_lyc cx) NT_CID fp a).
  { exact (ajw_not_side SK SEGS B LAWS pa_img_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ NT_CID fp a
             HGX HJc ltac:(unfold NT_CID; lia) Hfp HnIn Hw0 Happ). }
  assert (HnE : ~ Ec a).
  { intros HE. destruct (HEc a HE) as [Hg | Hs]; [unfold apart_gnl in Hapg; lia | exact (Hns Hs)]. }
  assert (Hav : aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) mem3 a).
  { apply (nr_ajw_kept _ _ _ _ _ _ _ _ _ _ _ _ ly3 S3 W3 mem3 md3 k2 ly3 S3 W3 mem3 W2 mem2 slo shi Ec a
             HGX HJ Hw3 HK); [tauto | tauto | intros; reflexivity | | exact HnE |].
    - unfold apart_frame in Hapf. rewrite EK in Hapf. lia.
    - unfold apart in Hape. lia. }
  split; [exact (nr_mbyte_of_aview SEGS _ _ _ _ a Hav)|].
  intros Hwr.
  assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold amem_range in Hamr; rewrite C5, C4, C3 in Hamr; lia).
  destruct (classic (in_img SEGS a)) as [Himg | Hnimg].
  - destruct Himg as (s & Hs & Hsr).
    destruct (seg_writable s) eqn:Ews.
    + rewrite HSEGS in Hs. pose proof (wseg_writable_tfib (rdW W2 mem2) a
        (ex_intro _ s (conj Hs (conj Ews Hsr)))) as HW'. rewrite <- HSEGS in HW'. exact HW'.
    + exfalso. apply (Hnro a HW). left. exists s. split; [exact Hs|]. split; [exact Ews | exact Hsr].
  - apply apresent_writable.
    apply (apresent_transfer SEGS (w_H W3) (w_H W2) mem3 mem2 a Ha64 Hnimg Hav).
    exact (nr_present_of_writable (w_H W3) mem3 a Ha64 Hnimg Hwr).
Qed.

(* THE CALL OF fuzz_recv: fuzz_recv_acontract under SRr_bind, and the state it returns *)
Lemma nr_call : forall (POST : ntcx -> world SEGS -> config -> Prop) retk j cx fp k2 ly3 S3 W3 ms3 md3,
  nt_base SK B cx ->
  ajournal_gx SEGS B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NT_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  frames S3 = (NT_CID, fp) :: frames (n_Sc cx) ->
  nr_pre retk j cx fp k2 ly3 S3 W3 ms3 md3 -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  (forall ly2 S2 W2 ms2 md2,
     ajournal_gx SEGS B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
       (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NT_CID, fp) :: n_own cx) ly2 S2 W2 (ms_mem ms2) md2 k2 ->
     frames S2 = (NT_CID, fp) :: frames (n_Sc cx) ->
     nr_rcvd retk j (ms_regs ms3) cx fp k2 ly2 S2 W2 ms2 md2 ->
     SRr SEGS W2 (mkCfg ms2 md2) (POST cx)) ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros POST retk j cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR HPRE Hrk Hrk2 KONT.
  destruct (nr_call_pre retk j cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR HPRE Hrk Hrk2) as (HAP & HPR).
  pose proof HPRE as (Hpc & HC & HFD & (bs & HNK & HGO) & R1 & R10 & R11 & R12).
  pose proof (nr_cut_nums cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR HC) as
    (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & F1 & F2 & F3 & F4 & F5 & F6 & HAR & Hin & Hfa).
  pose proof HC as (Hresv & Hsvc & Hrom & Hfreg & Hfcsr & HRG & HSV & HHD & HSL & HSH4 & HFK & R23 & R25 & R26
    & HFS & HJB & HKP & HOW & HBS & HAB).
  assert (Ems : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 FUZZ_RECV_A) (ms_mem ms3) (seg_rom SEGS)).
  { clear - Hpc Hresv Hsvc Hrom Hfreg Hfcsr.
    destruct ms3 as [rg fr pcv svp rv fc mm rm];
      cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *.
    subst. reflexivity. }
  pose proof RECV as HR. unfold fuzz_recv_acontract, aleaf in HR.
  pose proof NL_TALK_AK_val as EK.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct nr_vals as (VB & VR & VE).
  pose proof HRG as (Rsp & Rs0 & Rs1 & Rs2 & Rs5 & Rs8 & Rgp & Rtp).
  assert (USP : spZ (ms_regs ms3) = n_sp1 cx) by (unfold spZ; rewrite Rsp; unfold w64; apply unsigned_lit_small; lia).
  assert (A0 : aarg (ms_regs ms3) 0 = NL_FD) by (rewrite nr_aarg0, R10; unfold w64, NL_FD; apply unsigned_lit_small; lia).
  assert (A1 : aarg (ms_regs ms3) 1 = nBUF cx fp)
    by (rewrite nr_aarg1, R11; unfold w64, nBUF, NT_BUFOFF; apply unsigned_lit_small; lia).
  assert (A2 : aarg (ms_regs ms3) 2 = NT_BUFLEN)
    by (rewrite nr_aarg2, R12; unfold w64, NT_BUFLEN; apply unsigned_lit_small; lia).
  rewrite Ems at 1.
  eapply SRr_bind; [exact (HR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAP HPR)|].
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Ec2 & HJ2 & HP & HFR2 & Hfds2 & Hfs2 & HK2 & _ & HES2
    & Hperm2 & HPost).
  subst c2. rewrite Z.add_0_r in HJ2.
  apply (KONT ly2 S2 W2 (mkst regs2 (getr (ms_regs ms3) 1) mem2 (seg_rom SEGS)) md2 HJ2); [rewrite HFR2; exact HFR|].
  (* what the callee's akept keeps *)
  rewrite USP, FUZZ_RECV_AK_val in HK2. unfold fuzz_recv_awr in HK2. rewrite A1, A2 in HK2.
  set (Erv := fun a => inFP [(LA_G_NL + NK_NEXT, LA_G_NL + NK_MISUSE + 4); (nBUF cx fp, nBUF cx fp + NT_BUFLEN)] a) in HK2.
  assert (NEr : forall a, Erv a -> (LA_G_NL + NK_NEXT <= a < LA_G_NL + NK_MISUSE + 4) \/
                                   (nBUF cx fp <= a < nBUF cx fp + NT_BUFLEN)).
  { intros a Ha. unfold Erv in Ha. apply inFP_cons in Ha as [Ha|Ha]; [left; exact Ha|].
    apply inFP_cons in Ha as [Ha|Ha]; [right; exact Ha|]. destruct Ha as (r & Hr & _). destruct Hr. }
  pose proof HK2 as (K1 & K2 & K3 & K4 & K5 & K6).
  unfold nBUF, NT_BUFOFF, NT_BUFLEN in NEr.
  assert (KST : forall a, alloc_ceiling <= a < 2 ^ 64 -> n_sp1 cx <= a ->
            aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha Hs. apply K1; [lia | lia|]. intros HE. destruct (NEr a HE) as [HE'|HE'];
      [unfold LA_G_NL, NK_NEXT, NK_MISUSE in HE'; lia | lia]. }
  assert (KFRM : forall a, (nF cx fp <= a < nF cx fp + 32 \/ nF cx fp + 16416 <= a < nF cx fp + 32768) ->
            aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha. apply (K4 NT_CID fp a Hin).
    - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Hfa. change (fs_frame_bytes NT_CID) with 32768.
      unfold nF in Ha. lia.
    - intros HE. destruct (NEr a HE) as [HE'|HE']; [|lia].
      apply (F6 a ltac:(lia)). exact (proj1 (nr_gnl_facts a ltac:(unfold NK_NEXT, NK_MISUSE, NK_SIZE in *; lia))). }
  assert (KSHD : forall i, 0 <= i < 2084 ->
            aview SEGS (w_H W2) mem2 (nSH cx fp + i) = aview SEGS (w_H W3) (ms_mem ms3) (nSH cx fp + i)).
  { intros i Hi. apply (K4 NT_CID fp (nSH cx fp + i) Hin).
    - right. unfold in_zr. cbn [fst snd]. rewrite Hfa. change (fs_frame_bytes NT_CID / 8) with 4096.
      unfold shadow_addr. fold (nF cx fp). rewrite F4. lia.
    - intros HE. rewrite F4 in HE. destruct (NEr _ HE) as [HE'|HE'].
      + unfold LA_G_NL, NK_NEXT, NK_MISUSE, SHADOW_OFF in HE'. lia.
      + unfold SHADOW_OFF, kLowShadowBeg in *. rewrite C3 in F5. destruct F5 as [F5|F5]; lia. }
  assert (KIMG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
            ~ (as_errno B <= a < as_errno B + 4) -> ~ (LA_G_NL + NK_NEXT <= a < LA_G_NL + NK_MISUSE + 4) ->
            aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Hi Hns Her Hng. apply K3; [exact Hi | exact Hns | exact Her|].
    intros HE. destruct (NEr a HE) as [HE'|HE']; [exact (Hng HE')|]. exact (F6 a ltac:(lia) Hi). }
  assert (PRS : forall (r : bv 5), acallee_saved (bv_unsigned r) ->
            getr (ms_regs (mkst regs2 (getr (ms_regs ms3) 1) mem2 (seg_rom SEGS))) r = getr (ms_regs ms3) r)
    by exact (nr_preserved _ _ HP).
  (* g_nl's bytes outside fuzz_recv's window are the call's *)
  pose proof HB as (_ & _ & HNP & _).
  pose proof HNP as (kbs & req & _ & _ & _ & _ & _ & _ & _ & (Herr & _ & _ & _ & Hegn) & _).
  assert (KG : forall i, 0 <= i < NK_SIZE -> ~ (NK_NEXT <= i < NK_MISUSE + 4) ->
            mbyte SEGS (rdW W2 mem2) (LA_G_NL + i) = mbyte SEGS (rdW W3 (ms_mem ms3)) (LA_G_NL + i)).
  { intros i Hi Hn. apply nr_mbyte_of_aview.
    destruct (nr_gnl_facts (LA_G_NL + i) ltac:(lia)) as (Gi & Gs & _ & _).
    apply KIMG; [exact Gi | exact Gs | unfold apart_gnl in Hegn; lia | lia]. }
  (* the Post's g_nl *)
  destruct HPost as (HPost1 & HPabuf).
  destruct (HPost1 bs HNK) as (bs' & HNK' & WF' & En & Ee & Eso & Ese & Ech & Eop & Eon & Ecl & Ens & Emi
    & Hempty & Hchunk).
  pose proof HGO as (WF & Echk & Enck & Eeek & _ & _ & _ & Eopk & _ & _ & _ & Enxk & _ & _).
  assert (Emi' : nk_misuse bs' = nk_misuse bs).
  { rewrite Emi, A0, Eopk. unfold NL_FD. reflexivity. }
  assert (Ecs : nr_cs cx = nk_chunks bs) by (unfold nr_cs, n_K0, nk_kstate; cbn [k_chunks]; rewrite Echk; reflexivity).
  assert (Elen : Z.of_nat (length (nr_cs cx)) = nk_n_chunks bs) by (rewrite Ecs; exact (nt_nk_chunks_length bs WF)).
  unfold nr_rcvd.
  split.
  { unfold nt_shape. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
    repeat split; try reflexivity. rewrite R1. reflexivity. }
  split.
  { unfold nr_com. cbn [ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact (nr_regs_keep cx fp ms3 _ PRS HRG)|].
    split.
    { destruct HSV as (S1 & S2v). split.
      - eapply nr_at_kept; [intros ?i ?Hi; apply KST; lia | exact S1].
      - intros jj Hjj. eapply nr_at_kept; [intros ?i ?Hi; apply KST; lia | exact (S2v jj Hjj)]. }
    split.
    { destruct HHD as (H1 & H2 & H3 & H4). unfold nt_header. change (fs_frame_bytes NT_CID) with 32768 in *.
      split; [eapply nr_at_kept; [intros ?i ?Hi; apply KFRM; left; lia | exact H1]|].
      split; [eapply nr_at_kept; [intros ?i ?Hi; apply KFRM; left; lia | exact H2]|].
      split; [eapply nr_at_kept; [intros ?i ?Hi; apply KFRM; left; lia | exact H3]|].
      eapply nr_at_kept; [intros ?i ?Hi; apply KFRM; right; lia | exact H4]. }
    split.
    { destruct HSL as (H1 & H2 & H3). unfold nt_slots0. unfold NS_KIND, NS_KINDN, NS_F in *.
      split; [eapply nr_at_kept; [intros ?i ?Hi; apply KST; lia | exact H1]|].
      split; [eapply nr_at_kept; [intros ?i ?Hi; apply KST; lia | exact H2]|].
      eapply nr_at_kept; [intros ?i ?Hi; apply KST; lia | exact H3]. }
    split; [unfold NS_SH4 in *; eapply nr_at_kept; [intros ?i ?Hi; apply KST; lia | exact HSH4]|].
    split; [unfold NS_FK in *; eapply nr_at_kept; [intros ?i ?Hi; apply KST; lia | exact HFK]|].
    split; [rewrite PRS by nr_cs; exact R23|].
    split; [rewrite PRS by nr_cs; exact R25|].
    split; [rewrite PRS by nr_cs; exact R26|].
    split.
    { destruct HFS as (H1 & H2 & H3). unfold nt_frame_shadow. cbn [ms_mem mkst].
      split; [intros i Hi; rewrite (KSHD i ltac:(lia)); exact (H1 i Hi)|].
      split; [intros i Hi; replace (nSH cx fp + 4 + i) with (nSH cx fp + (4 + i)) by lia;
              rewrite (KSHD (4 + i) ltac:(lia)); replace (nSH cx fp + (4 + i)) with (nSH cx fp + 4 + i) by lia;
              exact (H2 i Hi)|].
      intros i Hi; replace (nSH cx fp + 2052 + i) with (nSH cx fp + (2052 + i)) by lia;
        rewrite (KSHD (2052 + i) ltac:(lia)); replace (nSH cx fp + (2052 + i)) with (nSH cx fp + 2052 + i) by lia;
        exact (H3 i Hi). }
    split.
    { destruct HJB as (Hk2 & Hperm & HSfs & HFR' & HnIn & _ & Hwit & Hfds & Hfs).
      split; [exact Hk2|].
      split; [exact (Permutation_trans Hperm2 Hperm)|].
      split; [exact (set_fs_trans S3 S2 (n_Sc cx) HSfs HES2)|].
      split; [rewrite HFR2; exact HFR|].
      split; [exact HnIn|].
      split.
      { intros c p. destruct (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c p HJ2) as (E2 & _).
        destruct (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c p HJ) as (E3 & _).
        rewrite E2, <- E3. exact (Hfa c p). }
      split; [exact Hwit|].
      split; [rewrite Hfds2; exact Hfds | rewrite Hfs2; exact Hfs]. }
    split.
    { destruct HKP as (HKk & HRO & HEsub). split; [|split; [|exact HEsub]].
      - apply (akept_trans_ly SK SEGS B LAWS pa_segs_low (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) ly3 S3 W3
          (ms_mem ms3) W2 mem2 (spZ (n_regs cx) - NL_TALK_AK) (spZ (n_regs cx)) (n_sp1 cx - 4192) (n_sp1 cx)
          _ Erv _ ltac:(rewrite EK; lia) ltac:(lia) HKk HK2 ltac:(rewrite EK; lia) ltac:(lia)).
        + intros b m Hbm. apply (Permutation_in _ (Permutation_sym (proj1 (proj2 HJB)))). exact Hbm.
        + intros f Hf. rewrite HFR. right. exact Hf.
        + exact Hfa.
        + tauto.
        + intros a Ha. destruct (NEr a Ha) as [Hg|Hb].
          * left. exists (LA_G_NL, LA_G_NL + NK_N_SENT + 4). split; [left; reflexivity|].
            cbn [fst snd]. unfold NK_NEXT, NK_MISUSE, NK_N_SENT in *. lia.
          * right. left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes NT_CID) with 32768.
            fold (nF cx fp). lia.
      - apply (nr_ro_kept _ _ HRO). intros a Hro Hns Her. apply KIMG; [exact (nr_ro_img a Hro) | exact Hns | exact Her|].
        intros Hg. apply (proj1 (proj2 (proj2 (nr_gnl_facts a ltac:(unfold NK_NEXT, NK_MISUSE, NK_SIZE in *; lia))))).
        exact Hro. }
    split; [exact HOW|].
    split.
    { pose proof HB as (HA & _ & HNP2 & _).
      pose proof HNP2 as (kbs2 & req2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
        & Hek & Hea & _ & Hka & Haa & Hck & Hca).
      apply (nr_bufs_frame cx (rdW W3 (ms_mem ms3)) (rdW W2 mem2)); [| | exact HBS].
      - intros Hk Hn a Ha. destruct (Hka Hk) as (Hkf & Hkg). destruct (Hck Hk Hn) as (Hkr & _ & _).
        apply (nr_buf_byte_call cx fp k2 ly3 S3 W3 (ms_mem ms3) md3 W2 mem2 (n_sp1 cx - 4192) (n_sp1 cx) Erv
          (n_kind cx) (n_kindn cx) a HB HJ HFR HJB HK2 ltac:(rewrite EK; lia) ltac:(lia));
          [| unfold aivl; replace (n_kind cx =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hk); reflexivity
           | unfold n_Wr, nl_talk_awr; right; left; unfold aivl;
             replace (aarg (n_regs cx) 2 =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hk); reflexivity
           | exact Hk | exact Hn | exact Hkf | exact Hkg | exact (Hek Hk) | exact Hkr
           | exact (proj1 (bv_unsigned_in_range _ _)) | exact Ha].
        intros x Hx. destruct (NEr x Hx) as [Hg|Hb]; [left; unfold NK_NEXT, NK_MISUSE, NK_SIZE in *; lia|].
        right. left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes NT_CID) with 32768.
        fold (nF cx fp). lia.
      - intros Hk Hn a Ha. destruct (Haa Hk) as (Hkf & Hkg). destruct (Hca Hk Hn) as (Hkr & _ & _).
        apply (nr_buf_byte_call cx fp k2 ly3 S3 W3 (ms_mem ms3) md3 W2 mem2 (n_sp1 cx - 4192) (n_sp1 cx) Erv
          (n_alias cx) (n_aliasn cx) a HB HJ HFR HJB HK2 ltac:(rewrite EK; lia) ltac:(lia));
          [| unfold aivl; replace (n_alias cx =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hk); reflexivity
           | unfold n_Wr, nl_talk_awr; right; right; left; unfold aivl;
             replace (aarg (n_regs cx) 4 =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hk); reflexivity
           | exact Hk | exact Hn | exact Hkf | exact Hkg | exact (Hea Hk) | exact Hkr
           | exact (proj1 (bv_unsigned_in_range _ _)) | exact Ha].
        intros x Hx. destruct (NEr x Hx) as [Hg|Hb]; [left; unfold NK_NEXT, NK_MISUSE, NK_SIZE in *; lia|].
        right. left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes NT_CID) with 32768.
        fold (nF cx fp). lia. }
    rewrite A1, A2 in HPabuf. exact HPabuf. }
  split; [unfold NS_FD in *; eapply nr_at_kept; [intros ?i ?Hi; apply KST; lia | exact HFD]|].
  split; [exact HP|].
  destruct (Z_lt_le_dec (nk_next bs) (nk_n_chunks bs)) as [Hlt|Hge].
  - right. pose proof (Hchunk Hlt) as HCk. cbv zeta in HCk. destruct HCk as (R10' & Enx' & rest & Hab & Hrl).
    split; [lia|].
    exists (nk_chunk bs (nk_next bs)), rest.
    split; [rewrite Ecs; replace j with (Z.to_nat (nk_next bs)) by lia; apply nt_nk_chunks_nth; pose proof WF as (_ & HW2 & _); lia|].
    split; [exact R10'|].
    split; [exists bs'; split; [exact HNK'|];
            apply (nr_gnl_after cx (rdW W3 (ms_mem ms3)) (rdW W2 mem2) bs bs' (Z.of_nat j) HNK HNK' KG HGO WF'
              En Ee Eso Ese Ech Eop Eon Ecl Ens Emi'); rewrite Enx', Enxk; lia|].
    rewrite A1 in Hab. split; [exact Hab|].
    split; [rewrite length_app, Nat2Z.inj_add, Hrl, A2; lia|].
    change (Z.to_nat NL_CHUNK_MAX) with 4096%nat. apply (nt_nk_chunk_len bs (nk_next bs) WF). pose proof WF as (_ & HW2 & _). lia.
  - left. destruct (Hempty Hge) as (R10' & Enx' & Herrno).
    split; [lia|].
    split; [exact R10'|].
    split; [exists bs'; split; [exact HNK'|];
            apply (nr_gnl_after cx (rdW W3 (ms_mem ms3)) (rdW W2 mem2) bs bs' (Z.of_nat j) HNK HNK' KG HGO WF'
              En Ee Eso Ese Ech Eop Eon Ecl Ens Emi'); rewrite Enx', Enxk; lia|].
    unfold n_K0, nk_kstate. cbn [k_end]. rewrite <- Eeek. exact Herrno.
Qed.

(* ==========================================================================
   6. The engine's terms
   ========================================================================== *)

(* a read inside the chunk is the same read of the chunk and of the whole buffer *)
Lemma nr_rdn_app : forall (c rest : list byte) o n, 0 <= o -> 0 <= n -> o + n <= Z.of_nat (length c) ->
  rdn (c ++ rest) o n = rdn c o n.
Proof.
  intros c rest o n Ho Hn Hl. apply rdn_agree; [lia | lia | lia | rewrite length_app; lia |].
  intros k Hk. rewrite nth_error_app1 by lia. reflexivity.
Qed.

(* NLMSG_ALIGN as the engine leaves it (+0x258..+0x260): a3 + 3, `srliw` 2, `slli` 2 *)
Definition nr_alignX : sv := SAlu ALU_SLL (SAluw ALU_SRL (SOff 32 3) (SLit 2)) (SLit 2).

Lemma nr_U_align : forall E ml, ew E 32 = Z_to_bv 64 ml -> 0 <= ml <= 4096 -> U E nr_alignX = nl_align ml.
Proof.
  intros E ml H32 Hml. unfold nr_alignX.
  rewrite U_SAlu, U_SLit. change (zcanon 2) with 2.
  rewrite (U_of_S E (SAluw _ _ _)), S_SAluw, U_SOff, U_SLit. change (zcanon 2) with 2.
  rewrite H32, unsigned_lit_small by lia.
  rewrite (zcanon_id (ml + 3)) by (unfold M64; lia).
  cbn [zalu_raw]. change (Z.land (2 mod 2 ^ 32) 31) with 2. change (Z.land 2 63) with 2.
  rewrite (Z.mod_small (ml + 3) (2 ^ 32)) by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4.
  assert (D : 0 <= (ml + 3) / 4 <= 1025) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  rewrite nt_swrap32_lo by lia. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small ((ml + 3) / 4)) by lia.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
  rewrite zcanon_id by (unfold M64; lia). unfold nl_align. ring.
Qed.

Lemma nr_denot_zc : forall E v z, U E v = zcanon z -> sv_denot E v = Z_to_bv 64 z.
Proof.
  intros E v z H. rewrite denot_lit_U, H. unfold zcanon, M64. apply bv_eq. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.

(* the two registers the message loop steps, as the engine leaves them *)
Lemma nr_U_step : forall E left base ml,
  ew E 10 = Z_to_bv 64 left -> ew E 11 = Z_to_bv 64 base -> ew E 32 = Z_to_bv 64 ml ->
  0 <= left < 2 ^ 63 -> 0 <= base -> base + 4096 < 2 ^ 64 -> 0 <= ml <= 4096 ->
  sv_denot E (SAlu ALU_SUB (SOff 10 0) nr_alignX) = Z_to_bv 64 (left - nl_align ml) /\
  sv_denot E (SAlu ALU_ADD (SOff 11 0) nr_alignX) = Z_to_bv 64 (base + nl_align ml).
Proof.
  intros E left base ml H10 H11 H32 Hl Hb Hb2 Hml.
  pose proof (nr_U_align E ml H32 Hml) as HA.
  split; apply nr_denot_zc; rewrite U_SAlu, HA, U_SOff; cbn [zalu_raw].
  - rewrite H10, unsigned_lit_small by lia. rewrite Z.add_0_r, (zcanon_id left) by (unfold M64; lia). reflexivity.
  - rewrite H11, unsigned_lit_small by lia. rewrite Z.add_0_r, (zcanon_id base) by (unfold M64; lia). reflexivity.
Qed.

(* ==========================================================================
   7. Seats: the symbolic state the engine starts from at a cut
   ========================================================================== *)

Definition nr_Bx : sv := SOff 21 0.
Definition nr_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition nr_spf : afact := mkAF (2 ^ 46 - 512) (2 ^ 47) 5.
Definition nr_shf : afact := mkAF SHADOW_OFF SHADOW_OFF 0.
(* sp = s1 = the realigned stack pointer, s5 = the shadow base *)
Definition nr_cf : list (nat * afact) := [(2%nat, nr_spf); (9%nat, nr_spf); (21%nat, nr_shf)].

(* the registers every cut of the phase keeps *)
Definition nr_keep : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%bv.
(* ... and the ones nr_com reads (the walk's three constants s3, s4, s6 are not among them) *)
Definition nr_keepc : list (bv 5) := [2; 3; 4; 8; 9; 18; 21; 23; 24; 25; 26]%bv.

Lemma nr_seat : forall pc (ms : machine_state) (W : world SEGS) ext rs G,
  nt_shape pc ms -> regions_wf rs = true ->
  Forall (region_ok SEGS (Eimg (Ereg (ms_regs ms) ext)) (rdW W (ms_mem ms))) rs ->
  pairwise_disjoint (Eimg (Ereg (ms_regs ms) ext)) rs ->
  facts_ok (Eimg (Ereg (ms_regs ms) ext)) G ->
  st_ok_pi SEGS VAL (Eimg (Ereg (ms_regs ms) ext)) (mkSS pc sr_atoms rs None G) (restrict (w_H W) ms).
Proof.
  intros pc ms W ext rs G Hsh Hwf Hrs Hd Hf.
  assert (Hms' : restrict (w_H W) ms =
    mkst (ms_regs ms) (Z_to_bv 64 (BASE + pc)) (rdW W (ms_mem ms)) (seg_rom SEGS)).
  { rewrite (nr_ms_mkst pc ms Hsh) at 1. reflexivity. }
  rewrite Hms'. apply pa_entry_st_ok_full; [apply regs_ok_Eimg_Ereg | exact Hwf | exact Hrs | exact Hd | exact Hf].
Qed.

Lemma nr_atoms_app : forall E l1 l2, atoms_ok E l1 -> atoms_ok E l2 -> atoms_ok E (l1 ++ l2).
Proof.
  intros E l1 l2 H1 H2. induction l1 as [|[n f] l1 IH]; [exact H2|].
  destruct H1 as [Hf H1]. split; [exact Hf | apply IH; exact H1].
Qed.

Lemma nr_af0 : forall E n v lo hi, bv_unsigned (ew E n) = v -> lo <= v <= hi -> afact_ok E n (mkAF lo hi 0).
Proof.
  intros E n v lo hi Hv Hr. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Hv.
  split; [exact Hr|]. split; [apply Z.mod_1_r | lia].
Qed.

Lemma nr_ew_reg : forall regs ext n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (Eimg (Ereg regs ext)) n = getr regs r.
Proof. intros regs ext n r Hn. exact (ew_Eimg_Ereg_nat regs ext n r Hn). Qed.

Lemma nr_ew_ext : forall regs ext j, (32 + j < A_TEXT)%nat ->
  ew (Eimg (Ereg regs ext)) (32 + j) = nth j ext (Z_to_bv 64 0).
Proof. intros regs ext j Hj. rewrite Eimg_low by exact Hj. apply ew_Ereg_extra. Qed.

Lemma nr_uw : forall v, 0 <= v < 2 ^ 64 -> bv_unsigned (w64 v) = v.
Proof. intros v Hv. unfold w64. apply unsigned_lit_small. exact Hv. Qed.

(* the three facts every seat carries *)
Lemma nr_cf_ok : forall cx E, nt_base SK B cx ->
  ew E 2 = w64 (n_sp1 cx) -> ew E 9 = w64 (n_sp1 cx) -> ew E 21 = w64 SHADOW_OFF -> atoms_ok E nr_cf.
Proof.
  intros cx E HB E2 E9 E21.
  destruct (nr_base_facts cx HB) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
  pose proof asan_consts as ((C1a & C1b) & _).
  pose proof NL_TALK_AK_val as EK. rewrite EK in *.
  cbn [atoms_ok nr_cf]. unfold afact_ok, nr_spf, nr_shf. cbn [af_lo af_hi af_al2].
  rewrite E2, E9, E21, !nr_uw by (unfold SHADOW_OFF; lia).
  change (2 ^ 5) with 32. change (2 ^ 0) with 1.
  split; [split; [lia | split; [exact B8 | lia]]|].
  split; [split; [lia | split; [exact B8 | lia]]|].
  split; [split; [lia | split; [apply Z.mod_1_r | lia]] | exact I].
Qed.

(* the shadow entry of a range the code checks *)
Lemma nr_shent_ok : forall E (W : world SEGS) m (n : nat) p len,
  ew E 21 = w64 SHADOW_OFF -> ew E n = w64 p -> 0 <= p -> 0 <= len ->
  p + len < kLowMemEnd \/ kHighMemBeg <= p -> p + len < 2 ^ 47 ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF p len ->
  shent_ok SEGS nr_Bx E (rdW W m) (mkSHE n 0 len).
Proof.
  intros E W m n p len E21 En H0 Hl Happ H47 HRA. unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  assert (UB : U E nr_Bx = SHADOW_OFF) by (unfold nr_Bx; apply U_atom; [exact E21 | unfold SHADOW_OFF; lia]).
  assert (UA : U E (SOff n 0) = p) by (apply U_atom; [exact En | lia]).
  rewrite UB, UA. split.
  - rewrite Z.add_0_r, Z.sub_0_r. rewrite <- (aview_rd_of SEGS). exact HRA.
  - intros x Hx. pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
    rewrite Z.min_l, Z.max_r in Hx by lia.
    unfold kLowMemEnd, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.

(* the shadow of the receive buffer is zero: every range of it is addressable *)
Lemma nr_ra_buf : forall cx fp (W3 : world SEGS) ms3 q k,
  nt_frame_shadow cx fp 0 W3 ms3 -> nF cx fp mod 64 = 0 ->
  nBUF cx fp <= q -> q + k <= nBUF cx fp + NT_BUFLEN ->
  range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF q k.
Proof.
  intros cx fp W3 ms3 q k (_ & HZ & _) H64 Hq Hk x Hx. exists 0. split; [|left; reflexivity].
  unfold nBUF, NT_BUFOFF, NT_BUFLEN, nSH, shadow_of_addr in *.
  set (F := nF cx fp) in *.
  assert (E : SHADOW_OFF + x / 8 = SHADOW_OFF + F / 8 + 4 + (x / 8 - F / 8 - 4)) by lia.
  rewrite E. apply HZ. pose proof (Z.div_mod F 64 ltac:(lia)). split.
  - assert (F / 8 + 4 <= x / 8) by (apply Z.div_le_lower_bound; lia). lia.
  - assert (x / 8 < F / 8 + 4 + 2048) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

(* ---- the message loop's seat (NT_loop): the message's length, type and code as atoms 32, 33, 34 ---- *)
Definition nr_msg : YP09.region := YP09.mkRegion (Some 11%nat) 0 20 0 0
  [YP09.mkChunk 0 (CVal 4 (SOff 32 0)); YP09.mkChunk 4 (CVal 2 (SOff 33 0)); YP09.mkChunk 16 (CVal 4 (SOff 34 0))].
Definition nr_lfacts : facts :=
  mkFacts (nr_cf ++ [(10%nat, mkAF 16 4096 0); (11%nat, mkAF 4096 (2 ^ 47 - 64) 0);
           (32%nat, mkAF 0 (2 ^ 32 - 1) 0); (33%nat, mkAF 0 65535 0); (34%nat, mkAF 0 (2 ^ 32 - 1) 0)]) [] [].
Definition nr_lss0 : sstate := mkSS NT_loop sr_atoms [nr_msg] None nr_lfacts.
Definition nr_lSH : list shent := [mkSHE 11 0 20].

Lemma nr_loop_seat : forall cx fp (W3 : world SEGS) ms3 base left ml ty code,
  nt_base SK B cx -> nt_shape NT_loop ms3 -> nt_regs cx fp ms3 ->
  getr (ms_regs ms3) 10 = w64 left -> 16 <= left <= 4096 ->
  getr (ms_regs ms3) 11 = w64 base -> 4096 <= base <= 2 ^ 47 - 64 ->
  val_mem SEGS (rdW W3 (ms_mem ms3)) base 4 ml -> 0 <= ml < 2 ^ 32 ->
  val_mem SEGS (rdW W3 (ms_mem ms3)) (base + 4) 2 ty -> 0 <= ty < 2 ^ 16 ->
  val_mem SEGS (rdW W3 (ms_mem ms3)) (base + 16) 4 code -> 0 <= code < 2 ^ 32 ->
  st_ok_pi SEGS VAL (Eimg (Ereg (ms_regs ms3) [w64 ml; w64 ty; w64 code])) nr_lss0 (restrict (w_H W3) ms3).
Proof.
  intros cx fp W3 ms3 base left ml ty code HB Hshp Hrg R10 Hl R11 Hb Vml Hml Vty Hty Vcd Hcd.
  pose proof Hrg as (Rsp & Rs0 & Rs1 & Rs2 & Rs5 & Rs8 & Rgp & Rtp).
  set (E := Eimg (Ereg (ms_regs ms3) [w64 ml; w64 ty; w64 code])).
  assert (E2 : ew E 2 = w64 (n_sp1 cx)) by (unfold E; rewrite (nr_ew_reg _ _ 2 (2%bv : bv 5) eq_refl); exact Rsp).
  assert (E9 : ew E 9 = w64 (n_sp1 cx)) by (unfold E; rewrite (nr_ew_reg _ _ 9 (9%bv : bv 5) eq_refl); exact Rs1).
  assert (E10 : ew E 10 = w64 left) by (unfold E; rewrite (nr_ew_reg _ _ 10 (10%bv : bv 5) eq_refl); exact R10).
  assert (E11 : ew E 11 = w64 base) by (unfold E; rewrite (nr_ew_reg _ _ 11 (11%bv : bv 5) eq_refl); exact R11).
  assert (E21 : ew E 21 = w64 SHADOW_OFF) by (unfold E; rewrite (nr_ew_reg _ _ 21 (21%bv : bv 5) eq_refl); exact Rs5).
  assert (E32 : ew E 32 = w64 ml) by (unfold E; exact (nr_ew_ext _ _ 0 ltac:(unfold A_TEXT; lia))).
  assert (E33 : ew E 33 = w64 ty) by (unfold E; exact (nr_ew_ext _ _ 1 ltac:(unfold A_TEXT; lia))).
  assert (E34 : ew E 34 = w64 code) by (unfold E; exact (nr_ew_ext _ _ 2 ltac:(unfold A_TEXT; lia))).
  assert (U11 : bv_unsigned (ew E 11) = base) by (rewrite E11; apply nr_uw; lia).
  unfold nr_lss0. apply nr_seat; [exact Hshp | vm_compute; reflexivity | | unfold pairwise_disjoint; cbn; tauto |].
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, nr_msg.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. fold E. rewrite U11.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + apply (chunk_ok_val SEGS E _ base 0 4 (SOff 32 0) ml);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | change (Z.of_N 4) with 4; lia
        | rewrite Z.add_0_r; exact Vml].
    + apply (chunk_ok_val SEGS E _ base 4 2 (SOff 33 0) ty);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 2)) with (2 ^ 16); lia | change (Z.of_N 2) with 2; lia | exact Vty].
    + apply (chunk_ok_val SEGS E _ base 16 4 (SOff 34 0) code);
        [cbn [sv_denot]; rewrite E34, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | change (Z.of_N 4) with 4; lia | exact Vcd].
  - unfold facts_ok, nr_lfacts. cbn [f_atoms f_conds f_alias]. split; [|split; exact I].
    apply nr_atoms_app; [exact (nr_cf_ok cx E HB E2 E9 E21)|].
    cbn [atoms_ok]. fold E.
    split; [apply (nr_af0 E 10 left); [rewrite E10; apply nr_uw; lia | lia]|].
    split; [apply (nr_af0 E 11 base); [exact U11 | lia]|].
    split; [apply (nr_af0 E 32 ml); [rewrite E32; apply nr_uw; lia | lia]|].
    split; [apply (nr_af0 E 33 ty); [rewrite E33; apply nr_uw; lia | lia]|].
    split; [apply (nr_af0 E 34 code); [rewrite E34; apply nr_uw; lia | lia]|].
    exact I.
Qed.

(* ==========================================================================
   8. The cut predicates across a run that writes nothing
   ========================================================================== *)

Lemma nr_com_samec : forall cx fp k2 ly3 S3 W3 ms md ms' md',
  nr_com cx fp k2 ly3 S3 W3 ms md ->
  ms_mem ms' = ms_mem ms -> ms_resv ms' = None -> ms_svc_pending ms' = None -> ms_rom ms' = seg_rom SEGS ->
  ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr ->
  (forall r : bv 5, In r nr_keepc -> getr (ms_regs ms') r = getr (ms_regs ms) r) ->
  m_fds md' = m_fds md -> m_fs md' = m_fs md ->
  nr_com cx fp k2 ly3 S3 W3 ms' md'.
Proof.
  intros cx fp k2 ly3 S3 W3 ms md ms' md' HC Hm H1 H2 H3 H4 H5 HR F1 F2.
  destruct HC as (_ & _ & _ & _ & _ & HRG & HSV & HHD & HSL & HSH4 & HFK & R23 & R25 & R26 & HFS & HJB & HKP
    & HOW & HBS & HAB).
  pose proof HJB as (J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9).
  unfold nr_com, nt_saved, nt_header, nt_slots0, nt_frame_shadow, nt_at in *. rewrite Hm.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split.
  { unfold nt_regs in *. rewrite !HR by (unfold nr_keepc; cbn; tauto). exact HRG. }
  split; [exact HSV|]. split; [exact HHD|]. split; [exact HSL|]. split; [exact HSH4|]. split; [exact HFK|].
  split; [rewrite HR by (unfold nr_keepc; cbn; tauto); exact R23|].
  split; [rewrite HR by (unfold nr_keepc; cbn; tauto); exact R25|].
  split; [rewrite HR by (unfold nr_keepc; cbn; tauto); exact R26|].
  split; [exact HFS|].
  split.
  { unfold nt_jbk. split; [exact J1|]. split; [exact J2|]. split; [exact J3|]. split; [exact J4|].
    split; [exact J5|]. split; [exact J6|]. split; [exact J7|]. split; [rewrite F1; exact J8 | rewrite F2; exact J9]. }
  split; [exact HKP|]. split; [exact HOW|]. split; [exact HBS | exact HAB].
Qed.

Lemma nr_keep_c : forall r : bv 5, In r nr_keepc -> In r nr_keep.
Proof. intros r Hr. unfold nr_keepc in Hr. unfold nr_keep. cbn in Hr |- *. tauto. Qed.

Lemma nr_com_same : forall cx fp k2 ly3 S3 W3 ms md ms' md',
  nr_com cx fp k2 ly3 S3 W3 ms md ->
  ms_mem ms' = ms_mem ms -> ms_resv ms' = None -> ms_svc_pending ms' = None -> ms_rom ms' = seg_rom SEGS ->
  ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr ->
  (forall r : bv 5, In r nr_keep -> getr (ms_regs ms') r = getr (ms_regs ms) r) ->
  m_fds md' = m_fds md -> m_fs md' = m_fs md ->
  nr_com cx fp k2 ly3 S3 W3 ms' md'.
Proof.
  intros cx fp k2 ly3 S3 W3 ms md ms' md' HC Hm H1 H2 H3 H4 H5 HR F1 F2.
  exact (nr_com_samec cx fp k2 ly3 S3 W3 ms md ms' md' HC Hm H1 H2 H3 H4 H5 (fun r Hr => HR r (nr_keep_c r Hr)) F1 F2).
Qed.

Lemma nr_at_same : forall (W3 : world SEGS) ms ms' a v, nt_at W3 ms a v -> ms_mem ms' = ms_mem ms -> nt_at W3 ms' a v.
Proof. intros W3 ms ms' a v H Hm. unfold nt_at in *. rewrite Hm. exact H. Qed.

Lemma nr_gnl_same : forall cx (W3 : world SEGS) ms ms' j, nr_gnl cx W3 ms j -> ms_mem ms' = ms_mem ms -> nr_gnl cx W3 ms' j.
Proof. intros cx W3 ms ms' j H Hm. unfold nr_gnl in *. rewrite Hm. exact H. Qed.

Lemma nr_chunk_same : forall j f c rest cx fp (W3 : world SEGS) ms ms',
  nr_chunk j f c rest cx fp W3 ms -> ms_mem ms' = ms_mem ms -> nr_chunk j f c rest cx fp W3 ms'.
Proof. intros j f c rest cx fp W3 ms ms' H Hm. unfold nr_chunk, nr_gnl in *. rewrite Hm. exact H. Qed.

Lemma nr_k3_same : forall ms ms', nr_k3 ms ->
  (forall r : bv 5, In r nr_keep -> getr (ms_regs ms') r = getr (ms_regs ms) r) -> nr_k3 ms'.
Proof.
  intros ms ms' (K1 & K2 & K3) HR. unfold nr_k3.
  rewrite !HR by (unfold nr_keep; cbn; tauto). split; [exact K1 | split; [exact K2 | exact K3]].
Qed.

Lemma nr_shape_mkst : forall pc regs mem, nt_shape pc (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS)).
Proof. intros pc regs mem. unfold nt_shape. cbn. repeat split; reflexivity. Qed.

Lemma nr_wvb : forall md mat, m_fds (with_vm_backing (m_vm_lazy md) mat md) = m_fds md /\
  m_fs (with_vm_backing (m_vm_lazy md) mat md) = m_fs md.
Proof. intros [fd [maps lazy mt] io fs proc lim tm] mat. split; reflexivity. Qed.

(* ==========================================================================
   9. The exits of the message loop
   ========================================================================== *)

(* the chunk's walk ended without an answer: the receive loop goes on at the next cursor *)
Lemma nr_next_of : forall j f c rest cx fp k2 ly3 S3 W3 ms3 md3 ms' md',
  nr_com cx fp k2 ly3 S3 W3 ms3 md3 -> nt_at W3 ms3 (n_sp1 cx + NS_FD) NL_FD -> nr_k3 ms3 ->
  nr_chunk j f c rest cx fp W3 ms3 ->
  chunk_walk c = NlNone ->
  nt_shape NT_next ms' -> ms_mem ms' = ms_mem ms3 ->
  (forall r : bv 5, In r nr_keep -> getr (ms_regs ms') r = getr (ms_regs ms3) r) ->
  m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  nr_next_inv (S j) f cx fp k2 ly3 S3 W3 ms' md'.
Proof.
  intros j f c rest cx fp k2 ly3 S3 W3 ms3 md3 ms' md' HC HFD HK3 HCH HW Hsh Hm HR F1 F2.
  pose proof HCH as (HGN & Hnth & HCL & Hfu & _).
  pose proof Hsh as (_ & H1 & H2 & H3 & H4 & H5).
  unfold nr_next_inv.
  split; [exact Hsh|].
  split; [exact (nr_com_same cx fp k2 ly3 S3 W3 ms3 md3 ms' md' HC Hm H1 H2 H3 H4 H5 HR F1 F2)|].
  split; [exact (nr_at_same W3 ms3 ms' _ _ HFD Hm)|].
  split; [exact (nr_k3_same ms3 ms' HK3 HR)|].
  split; [exact (nr_gnl_same cx W3 ms3 ms' (S j) HGN Hm)|].
  split; [rewrite HCL; exact (nr_cl_none (nr_cs cx) f j c Hnth HW)|].
  exact (nr_fuel_next (nr_cs cx) j f Hfu).
Qed.

Lemma nr_to_next : forall j f c rest off left g cx fp k2 ly3 S3 W3 ms3 md3 ms' md',
  nr_loop_inv j f c rest off left g cx fp k2 ly3 S3 W3 ms3 md3 ->
  chunk_walk c = NlNone ->
  nt_shape NT_next ms' -> ms_mem ms' = ms_mem ms3 ->
  (forall r : bv 5, In r nr_keep -> getr (ms_regs ms') r = getr (ms_regs ms3) r) ->
  m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  nr_next_inv (S j) f cx fp k2 ly3 S3 W3 ms' md'.
Proof.
  intros j f c rest off left g cx fp k2 ly3 S3 W3 ms3 md3 ms' md' HI HW Hsh Hm HR F1 F2.
  pose proof HI as (_ & HC & HFD & HK3 & _ & _ & HCH & _).
  exact (nr_next_of j f c rest cx fp k2 ly3 S3 W3 ms3 md3 ms' md' HC HFD HK3 HCH HW Hsh Hm HR F1 F2).
Qed.

(* the chunk's walk answered v: the chunk loop's answer is v and the cursor is past the chunk *)
Lemma nr_hit : forall j f c rest cx fp (W3 : world SEGS) ms3 v,
  nr_chunk j f c rest cx fp W3 ms3 -> talk_owes (n_K0 cx) = true ->
  chunk_walk c = v -> v <> NlNone ->
  talk_rc_lib (n_K0 cx) = nt_nlv_rc v (k_end (n_K0 cx)) /\ talk_attrs (n_K0 cx) = nt_nlv_attrs v /\
  k_next (talk_after (n_K0 cx)) = S j.
Proof.
  intros j f c rest cx fp W3 ms3 v HCH HOW HW Hv.
  pose proof HCH as (_ & Hnth & HCL & _).
  apply (nr_answer cx v (S j) HOW). rewrite HCL. exact (nr_cl_hit (nr_cs cx) f j c v Hnth HW Hv).
Qed.

(* the attribute phase's cut, at an RTM_NEWLINK: the model's answer is that message's attribute walk *)
Lemma nr_mk_attr : forall j f c rest off left g cx fp k2 ly3 S3 W3 ms3 md3 ms' md',
  nr_loop_inv j f c rest off left (S g) cx fp k2 ly3 S3 W3 ms3 md3 ->
  16 <= rd32 c off <= left -> rd16 c (off + 4) = 16 ->
  nt_shape NT_attr ms' -> ms_mem ms' = ms_mem ms3 ->
  (forall r : bv 5, In r nr_keep -> getr (ms_regs ms') r = getr (ms_regs ms3) r) ->
  getr (ms_regs ms') 11 = w64 (nBUF cx fp + off) -> getr (ms_regs ms') 13 = w64 (rd32 c off) ->
  m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  nt_attr_inv B cx fp k2 ly3 S3 W3 ms' md'.
Proof.
  intros j f c rest off left g cx fp k2 ly3 S3 W3 ms3 md3 ms' md' HI Hml Hty Hsh Hm HR R11 R13 F1 F2.
  pose proof HI as (_ & HC & HFD & _ & _ & _ & HCH & HCW & Hoff & Hol & Hl16 & Hg).
  pose proof Hsh as (_ & H1 & H2 & H3 & H4 & H5).
  pose proof (nr_com_same cx fp k2 ly3 S3 W3 ms3 md3 ms' md' HC Hm H1 H2 H3 H4 H5 HR F1 F2) as HC'.
  destruct HC' as (_ & _ & _ & _ & _ & HRG & HSV & HHD & HSL & HSH4 & HFK & R23 & R25 & R26 & HFS & HJB & HKP
    & HOW & HBS & HAB).
  pose proof (nr_chunk_same j f c rest cx fp W3 ms3 ms' HCH Hm) as HCH'.
  pose proof HCH' as ((bs & HNK & HGO) & Hnth & HCL & Hfu & Hab & Hlen & Hcl).
  assert (HW : chunk_walk c = NlLink (attr_scan g c (off + 32) (rd32 c off - 32) no_attrs)).
  { rewrite HCW. apply nt_msg_link; [lia | lia | exact Hty]. }
  destruct (nr_hit j f c rest cx fp W3 ms' _ HCH' HOW HW ltac:(discriminate)) as (Trc & Tat & Tnx).
  exists c, rest, off, (rd32 c off), g, bs.
  split; [exact Hsh|]. split; [exact HRG|]. split; [exact HSV|]. split; [exact HHD|]. split; [exact HSL|].
  split; [exact HSH4|]. split; [exact HFK|].
  split; [exact (nr_at_same W3 ms3 ms' _ _ HFD Hm)|].
  split; [exact R11|]. split; [exact R13|]. split; [exact R25|]. split; [exact R23|].
  split; [exact HFS|]. split; [exact HJB|]. split; [exact HKP|].
  split; [exact HNK|]. split; [rewrite Tnx; exact HGO|].
  split; [exact HOW|]. split; [exact HBS|].
  split; [exact Hab|]. split; [exact Hlen|]. split; [exact Hcl|]. split; [exact HAB|].
  split; [exact Hoff|]. split; [unfold NL_HDR; lia|]. split; [lia|].
  split; [unfold NL_HDR, IFI_LEN; lia|].
  split; [rewrite Trc; reflexivity|].
  rewrite Tat. cbn [nt_nlv_attrs]. unfold NL_HDR, IFI_LEN. f_equal; lia.
Qed.

(* the exit phase's cut, when the chunk's walk answered v with no attributes *)
Lemma nr_mk_exit : forall j f c rest cx fp k2 ly3 S3 W3 ms3 md3 ms' md' v,
  nr_com cx fp k2 ly3 S3 W3 ms3 md3 -> nt_at W3 ms3 (n_sp1 cx + NS_FD) NL_FD ->
  nr_chunk j f c rest cx fp W3 ms3 ->
  chunk_walk c = v -> v <> NlNone -> nt_nlv_attrs v = no_attrs ->
  nt_shape NT_exit ms' -> ms_mem ms' = ms_mem ms3 ->
  (forall r : bv 5, In r nr_keep -> getr (ms_regs ms') r = getr (ms_regs ms3) r) ->
  getr (ms_regs ms') 27 = w64 (nt_nlv_rc v (k_end (n_K0 cx))) ->
  m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  nt_exit_inv B cx fp k2 ly3 S3 W3 ms' md'.
Proof.
  intros j f c rest cx fp k2 ly3 S3 W3 ms3 md3 ms' md' v HC HFD HCH HW Hv Ha Hsh Hm HR R27 F1 F2.
  pose proof Hsh as (_ & H1 & H2 & H3 & H4 & H5).
  pose proof (nr_com_same cx fp k2 ly3 S3 W3 ms3 md3 ms' md' HC Hm H1 H2 H3 H4 H5 HR F1 F2) as HC'.
  destruct HC' as (_ & _ & _ & _ & _ & HRG & HSV & HHD & HSL & HSH4 & HFK & R23 & R25 & R26 & HFS & HJB & HKP
    & HOW & HBS & HAB).
  pose proof (nr_chunk_same j f c rest cx fp W3 ms3 ms' HCH Hm) as HCH'.
  pose proof HCH' as ((bs & HNK & HGO) & _).
  destruct (nr_hit j f c rest cx fp W3 ms' v HCH' HOW HW Hv) as (Trc & Tat & Tnx).
  split; [exact Hsh|]. split; [exact HRG|]. split; [exact HSV|]. split; [exact HHD|].
  split; [exact HSH4|]. split; [exact HFK|].
  split; [exact (nr_at_same W3 ms3 ms' _ _ HFD Hm)|].
  split; [rewrite Trc; exact R27|].
  split; [exact HFS|]. split; [exact HJB|]. split; [exact HKP|].
  split; [exists bs; split; [exact HNK | rewrite HOW, Tnx; exact HGO]|].
  split; [exact HOW|].
  apply nt_bufs_same_fin; [rewrite Tat; exact Ha | exact HBS].
Qed.

(* the message loop's next turn: the message is skipped, the walk moves NLMSG_ALIGN of its length on *)
Lemma nr_mk_loop : forall j f c rest off left g cx fp k2 ly3 S3 W3 ms3 md3 ms' md',
  nr_loop_inv j f c rest off left (S g) cx fp k2 ly3 S3 W3 ms3 md3 ->
  16 <= rd32 c off <= left -> rd16 c (off + 4) <> 2 -> rd16 c (off + 4) <> 16 ->
  15 < left - nl_align (rd32 c off) ->
  nt_shape NT_loop ms' -> ms_mem ms' = ms_mem ms3 ->
  (forall r : bv 5, In r nr_keep -> getr (ms_regs ms') r = getr (ms_regs ms3) r) ->
  getr (ms_regs ms') 10 = w64 (left - nl_align (rd32 c off)) ->
  getr (ms_regs ms') 11 = w64 (nBUF cx fp + (off + nl_align (rd32 c off))) ->
  m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  nr_loop_inv j f c rest (off + nl_align (rd32 c off)) (left - nl_align (rd32 c off)) g
    cx fp k2 ly3 S3 W3 ms' md'.
Proof.
  intros j f c rest off left g cx fp k2 ly3 S3 W3 ms3 md3 ms' md' HI Hml Hty2 Hty16 Hl' Hsh Hm HR R10 R11 F1 F2.
  pose proof HI as (_ & HC & HFD & HK3 & _ & _ & HCH & HCW & Hoff & Hol & Hl16 & Hg).
  pose proof Hsh as (_ & H1 & H2 & H3 & H4 & H5).
  pose proof (nt_nl_align_ge (rd32 c off) ltac:(lia)) as HA.
  split; [exact Hsh|].
  split; [exact (nr_com_same cx fp k2 ly3 S3 W3 ms3 md3 ms' md' HC Hm H1 H2 H3 H4 H5 HR F1 F2)|].
  split; [exact (nr_at_same W3 ms3 ms' _ _ HFD Hm)|].
  split; [exact (nr_k3_same ms3 ms' HK3 HR)|].
  split; [exact R10|]. split; [exact R11|].
  split; [exact (nr_chunk_same j f c rest cx fp W3 ms3 ms' HCH Hm)|].
  split; [rewrite HCW; apply nt_msg_skip; [lia | lia | exact Hty2 | exact Hty16]|].
  split; [lia|]. split; [lia|]. split; [lia|]. lia.
Qed.

(* ==========================================================================
   10. The engine's values at a branch
   ========================================================================== *)

Lemma nr_den_atom : forall E n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.

Lemma nr_den_lit : forall E z, sv_denot E (SLit z) = Z_to_bv 64 z.
Proof. reflexivity. Qed.

Lemma nr_bt_ltu : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken BC_LTU (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof.
  intros x y Hx Hy.
  change (branch_taken BC_LTU (Z_to_bv 64 x) (Z_to_bv 64 y)) with (bv_unsigned (Z_to_bv 64 x) <? bv_unsigned (Z_to_bv 64 y)).
  rewrite !unsigned_lit_small by lia. reflexivity.
Qed.

Lemma nr_bt_geu : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken BC_GEU (Z_to_bv 64 x) (Z_to_bv 64 y) = negb (x <? y).
Proof.
  intros x y Hx Hy.
  change (branch_taken BC_GEU (Z_to_bv 64 x) (Z_to_bv 64 y)) with (negb (bv_unsigned (Z_to_bv 64 x) <? bv_unsigned (Z_to_bv 64 y))).
  rewrite !unsigned_lit_small by lia. reflexivity.
Qed.

Lemma nr_bt_eq : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken BC_EQ (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof.
  intros x y Hx Hy.
  change (branch_taken BC_EQ (Z_to_bv 64 x) (Z_to_bv 64 y)) with (bv_unsigned (Z_to_bv 64 x) =? bv_unsigned (Z_to_bv 64 y)).
  rewrite !unsigned_lit_small by lia. reflexivity.
Qed.

Lemma nr_bt_lt : forall x y, - 2 ^ 63 <= x < 2 ^ 63 -> - 2 ^ 63 <= y < 2 ^ 63 ->
  branch_taken BC_LT (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. cbn [branch_taken]. unfold bv_lts. rewrite !nt_signed64 by lia. reflexivity. Qed.

Lemma nr_bt_ge : forall x y, - 2 ^ 63 <= x < 2 ^ 63 -> - 2 ^ 63 <= y < 2 ^ 63 ->
  branch_taken BC_GE (Z_to_bv 64 x) (Z_to_bv 64 y) = negb (x <? y).
Proof. intros x y Hx Hy. cbn [branch_taken]. unfold bv_lts. rewrite !nt_signed64 by lia. reflexivity. Qed.

(* an atom of the seat (its index n given as a Z literal), in the condition of a branch the run stopped at *)
Ltac nr_den Hc n v Hn :=
  let k := eval vm_compute in (Z.to_nat n) in
  lazymatch type of Hc with context [sv_denot ?EF (SOff k 0)] =>
    rewrite (nr_den_atom EF k v ltac:(cbn [ew ewset Nat.eqb]; exact Hn)) in Hc end.

(* the run wrote nothing: the memory is the one it started from *)
Ltac nr_nowrite HF Em :=
  lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
    assert (Em : m' = m) by (apply (nr_frame_nowrite E rs m m'); [vm_compute; reflexivity | exact HF]) end.

Ltac nr_awr_ro :=
  lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ =>
    let rs' := eval vm_compute in rs in change rs with rs' end;
  repeat (apply awr_ok_x_cons; [intros ?a ?Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_nil.

(* a register of nr_keep the run left alone, at the end of a run from a seat over Eimg (Ereg regs ext) *)
Ltac nr_kreg HS HEdef :=
  let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; unfold nr_keep in Hr; cbn [In] in Hr;
  repeat (destruct Hr as [<- | Hr];
    [ lazymatch goal with |- getr (ms_regs _) ?rr = _ =>
        let Q := fresh "Q" in prreg HS rr Q; rewrite Q, HEdef; apply nr_ew_reg; reflexivity end |]);
  try destruct Hr.

Ltac nr_kregc HS HEdef :=
  let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; unfold nr_keepc in Hr; cbn [In] in Hr;
  repeat (destruct Hr as [<- | Hr];
    [ lazymatch goal with |- getr (ms_regs _) ?rr = _ =>
        let Q := fresh "Q" in prreg HS rr Q; rewrite Q, HEdef; apply nr_ew_reg; reflexivity end |]);
  try destruct Hr.

Ltac nr_md := first [ repeat rewrite (proj1 (nr_wvb _ _)); reflexivity | repeat rewrite (proj2 (nr_wvb _ _)); reflexivity ].

Ltac nr_rn HS m := lazymatch type of HS with
  | st_ok_pi _ _ _ _ (restrict _ ?x) => rename x into m
  | st_ok _ _ _ (restrict _ ?x) => rename x into m end.

(* a register the run computed: its symbolic value, evaluated *)
Ltac nr_creg HS r Q :=
  pose proof (st_ok_pi_restrict_reg _ _ _ _ r HS) as Q;
  lazymatch type of Q with _ = sv_denot _ ?ev => let ev' := eval vm_compute in ev in change ev with ev' in Q end.

(* ==========================================================================
   11. The message loop: one turn from NT_loop
   ========================================================================== *)

#[local] Abbreviation NRJ cx fp k2 ly3 S3 W3 mem3 md3 :=
  (ajournal_gx SEGS B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NT_CID, fp) :: n_own cx) ly3 S3 W3 mem3 md3 k2).

Section w.
Variable POST : ntcx -> world SEGS -> config -> Prop.
Hypothesis NATTR : nt_from SK B POST (nt_attr_inv B).
Hypothesis NEXIT : nt_from SK B POST (nt_exit_inv B).

Lemma nr_loop_step : forall j f c rest off left g cx fp k2 ly3 S3 W3 ms3 md3,
  nt_base SK B cx -> NRJ cx fp k2 ly3 S3 W3 (ms_mem ms3) md3 -> frames S3 = (NT_CID, fp) :: frames (n_Sc cx) ->
  nr_loop_inv j f c rest off left (S g) cx fp k2 ly3 S3 W3 ms3 md3 ->
  (forall off' left' ms' md', NRJ cx fp k2 ly3 S3 W3 (ms_mem ms') md' ->
     nr_loop_inv j f c rest off' left' g cx fp k2 ly3 S3 W3 ms' md' -> SRr SEGS W3 (mkCfg ms' md') (POST cx)) ->
  (forall ms' md', NRJ cx fp k2 ly3 S3 W3 (ms_mem ms') md' ->
     nr_next_inv (S j) f cx fp k2 ly3 S3 W3 ms' md' -> SRr SEGS W3 (mkCfg ms' md') (POST cx)) ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros j f c rest off left g cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR HI IH KN.
  pose proof HI as (Hshp & HC & HFD & HK3 & R10 & R11 & HCH & HCW & Hoff & Hol & Hl16 & Hg).
  pose proof HCH as (HGN & Hnth & HCL & Hfu & Hab & Hlen & Hcl).
  pose proof (nr_cut_nums cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR HC) as
    (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & F1 & F2 & F3 & F4 & F5 & F6 & HAR & Hin & Hfa).
  pose proof HC as (_ & _ & _ & _ & _ & HRG & _ & _ & _ & _ & _ & _ & _ & R26 & HFS & _).
  pose proof HRG as (Rsp & Rs0 & Rs1 & Rs2 & Rs5 & Rs8 & Rgp & Rtp).
  pose proof HK3 as (R19 & R20 & R22).
  pose proof HB as (HA & _). pose proof HA as (_ & HGX & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (Hcl' : Z.of_nat (length c) <= 4096) by (change (Z.to_nat NL_CHUNK_MAX) with 4096%nat in Hcl; lia).
  rewrite length_app in Hlen. unfold NT_BUFLEN in Hlen.
  (* the message's three fields *)
  set (ml := rd32 c off) in *. set (ty := rd16 c (off + 4)) in *. set (code := rd32 (c ++ rest) (off + 16)).
  assert (Vml : val_mem SEGS (rdW W3 (ms_mem ms3)) (nBUF cx fp + off) 4 ml)
    by exact (nt_read4 SEGS _ _ c rest off Hab Hoff ltac:(lia)).
  assert (Vty : val_mem SEGS (rdW W3 (ms_mem ms3)) (nBUF cx fp + off + 4) 2 ty).
  { replace (nBUF cx fp + off + 4) with (nBUF cx fp + (off + 4)) by lia.
    exact (nt_read2 SEGS _ _ c rest (off + 4) Hab ltac:(lia) ltac:(lia)). }
  assert (Vcd : val_mem SEGS (rdW W3 (ms_mem ms3)) (nBUF cx fp + off + 16) 4 code).
  { replace (nBUF cx fp + off + 16) with (nBUF cx fp + (off + 16)) by lia.
    apply (nt_read4 SEGS _ _ (c ++ rest) [] (off + 16)); [rewrite app_nil_r; exact Hab | lia | rewrite length_app; lia]. }
  assert (Rml : 0 <= ml < 2 ^ 32) by (apply nt_rd32_range; lia).
  assert (Rty : 0 <= ty < 2 ^ 16) by (apply nt_rd16_range; lia).
  assert (Rcd : 0 <= code < 2 ^ 32) by (apply nt_rd32_range; [lia | rewrite length_app; lia]).
  pose proof (nr_loop_seat cx fp W3 ms3 (nBUF cx fp + off) left ml ty code HB Hshp HRG R10 ltac:(lia) R11
    ltac:(unfold nBUF, NT_BUFOFF; lia) Vml Rml Vty Rty Vcd Rcd) as HS.
  remember (Eimg (Ereg (ms_regs ms3) [w64 ml; w64 ty; w64 code])) as E eqn:HEdef.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (E10 : ew E 10 = w64 left) by (subst E; rewrite (nr_ew_reg _ _ 10 (10%bv : bv 5) eq_refl); exact R10).
  assert (E11 : ew E 11 = w64 (nBUF cx fp + off))
    by (subst E; rewrite (nr_ew_reg _ _ 11 (11%bv : bv 5) eq_refl); exact R11).
  assert (E19 : ew E 19 = w64 2) by (subst E; rewrite (nr_ew_reg _ _ 19 (19%bv : bv 5) eq_refl); exact R19).
  assert (E20 : ew E 20 = w64 16) by (subst E; rewrite (nr_ew_reg _ _ 20 (20%bv : bv 5) eq_refl); exact R20).
  assert (E21 : ew E 21 = w64 SHADOW_OFF) by (subst E; rewrite (nr_ew_reg _ _ 21 (21%bv : bv 5) eq_refl); exact Rs5).
  assert (E22 : ew E 22 = w64 15) by (subst E; rewrite (nr_ew_reg _ _ 22 (22%bv : bv 5) eq_refl); exact R22).
  assert (E32 : ew E 32 = w64 ml) by (subst E; exact (nr_ew_ext _ _ 0 ltac:(unfold A_TEXT; lia))).
  assert (E33 : ew E 33 = w64 ty) by (subst E; exact (nr_ew_ext _ _ 1 ltac:(unfold A_TEXT; lia))).
  assert (E34 : ew E 34 = w64 code) by (subst E; exact (nr_ew_ext _ _ 2 ltac:(unfold A_TEXT; lia))).
  assert (SHOK : sh_ok SEGS nr_Bx nr_lSH E (rdW W3 (ms_mem ms3))).
  { apply Forall_cons; [|apply Forall_nil].
    apply (nr_shent_ok E W3 (ms_mem ms3) 11 (nBUF cx fp + off) 20 E21 E11);
      [unfold nBUF, NT_BUFOFF; lia | lia | | |].
    - unfold nBUF, NT_BUFOFF. rewrite C3, C5.
      destruct F5 as [F5|F5]; [left; unfold kLowShadowBeg in F5; lia | right; rewrite C3 in F5; lia].
    - unfold nBUF, NT_BUFOFF. lia.
    - apply (nr_ra_buf cx fp W3 ms3); [exact HFS | exact F3 | lia | unfold NT_BUFLEN; lia]. }
  clear Vml Vty Vcd.
  pose proof (paj_run_x SK B LAWS (n_G cx) HGX (n_XO cx) (n_OUT cx)) as RUN.
  pose proof (paj_run_to_x SK B LAWS (n_G cx) HGX (n_XO cx) (n_OUT cx)) as RUNTO.
  pose proof (paj_branch (PI := PI)) as BR.
  (* ---- +0x21c .. +0x228: the check of a1, `lwu a3`; the run stops at `bltu a3, s4` ---- *)
  paj_run_tok RUN HS HJ SHOK nr_span.
  1: nr_awr_ro.
  nr_rn HS ms1. nr_nowrite HF Em1. clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK nr_span.
  { (* +0x228 `bltu a3, s4` taken: ml < 16, the chunk is done (+0x294) *)
    nr_den Hc 32 ml E32. nr_den Hc 20 16 E20. rewrite nr_bt_ltu in Hc by lia. apply Z.ltb_lt in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK nr_span NT_next.
    1: nr_awr_ro.
    nr_rn HS ms2. nr_nowrite HF Em2. clear HF HFr HG.
    pmkst HS.
    assert (Hregs : forall r : bv 5, In r nr_keep -> getr (ms_regs ms2) r = getr (ms_regs ms3) r)
      by nr_kreg HS HEdef.
    apply KN; [exact HJ|].
    apply (nr_to_next j f c rest off left (S g) cx fp k2 ly3 S3 W3 ms3 md3 _ _ HI).
    - rewrite HCW. apply nt_msg_none; [lia|]. apply orb_true_intro. left. apply Z.ltb_lt. exact Hc.
    - exact (nr_shape_mkst NT_next _ _).
    - cbn [ms_mem mkst]. rewrite Em2, Em1. reflexivity.
    - exact Hregs.
    - nr_md.
    - nr_md. }
  nr_den Hc 32 ml E32. nr_den Hc 20 16 E20. rewrite nr_bt_ltu in Hc by lia. apply Z.ltb_ge in Hc.
  rename Hc into Hml16.
  (* ---- +0x22c: `bltu a0, a3` ---- *)
  paj_run_tok RUN HS HJ SHOK nr_span.
  1: nr_awr_ro.
  nr_rn HS ms2. nr_nowrite HF Em2. clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK nr_span.
  { (* taken: left < ml, the chunk is done (+0x294) *)
    nr_den Hc 10 left E10. nr_den Hc 32 ml E32. rewrite nr_bt_ltu in Hc by lia. apply Z.ltb_lt in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK nr_span NT_next.
    1: nr_awr_ro.
    nr_rn HS ms4. nr_nowrite HF Em4. clear HF HFr HG.
    pmkst HS.
    assert (Hregs : forall r : bv 5, In r nr_keep -> getr (ms_regs ms4) r = getr (ms_regs ms3) r)
      by nr_kreg HS HEdef.
    apply KN; [exact HJ|].
    apply (nr_to_next j f c rest off left (S g) cx fp k2 ly3 S3 W3 ms3 md3 _ _ HI).
    - rewrite HCW. apply nt_msg_none; [lia|]. apply orb_true_intro. right. apply Z.ltb_lt. exact Hc.
    - exact (nr_shape_mkst NT_next _ _).
    - cbn [ms_mem mkst]. rewrite Em4, Em2, Em1. reflexivity.
    - exact Hregs.
    - nr_md.
    - nr_md. }
  nr_den Hc 10 left E10. nr_den Hc 32 ml E32. rewrite nr_bt_ltu in Hc by lia. apply Z.ltb_ge in Hc.
  rename Hc into Hmll.
  (* ---- +0x230 .. +0x244: the check of a1 + 4, `lhu a2`; `beq a2, s4` ---- *)
  paj_run_tok RUN HS HJ SHOK nr_span.
  1: nr_awr_ro.
  nr_rn HS ms4. nr_nowrite HF Em4. clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK nr_span.
  { (* taken: an RTM_NEWLINK, the attribute walk (+0x314) *)
    nr_den Hc 33 ty E33. nr_den Hc 20 16 E20. rewrite nr_bt_eq in Hc by lia. apply Z.eqb_eq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK nr_span NT_attr.
    1: nr_awr_ro.
    nr_rn HS ms5. nr_nowrite HF Em5. clear HF HFr HG.
    pmkst HS.
    assert (Hregs : forall r : bv 5, In r nr_keep -> getr (ms_regs ms5) r = getr (ms_regs ms3) r)
      by nr_kreg HS HEdef.
    prreg HS (11%bv : bv 5) Q11. prreg HS (13%bv : bv 5) Q13.
    lazymatch goal with |- SRr _ _ {| cfg_ms := ?MS; cfg_model := ?MD |} _ =>
      apply (NATTR cx fp k2 ly3 S3 W3 MS MD HB HJ HFR) end.
    apply (nr_mk_attr j f c rest off left g cx fp k2 ly3 S3 W3 ms3 md3 _ _ HI); [lia | exact Hc | | | | | | |].
    - exact (nr_shape_mkst NT_attr _ _).
    - cbn [ms_mem mkst]. rewrite Em5, Em4, Em2, Em1. reflexivity.
    - exact Hregs.
    - cbn [ms_regs mkst]. rewrite Q11. exact E11.
    - cbn [ms_regs mkst]. rewrite Q13. exact E32.
    - nr_md.
    - nr_md. }
  nr_den Hc 33 ty E33. nr_den Hc 20 16 E20. rewrite nr_bt_eq in Hc by lia. apply Z.eqb_neq in Hc.
  rename Hc into Hty16.
  (* ---- +0x248: `beq a2, s3` ---- *)
  paj_run_tok RUN HS HJ SHOK nr_span.
  1: nr_awr_ro.
  nr_rn HS ms5. nr_nowrite HF Em5. clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK nr_span.
  { (* taken: an NLMSG_ERROR (+0x4ac): a0 := 36, `bgeu a3, a0` *)
    nr_den Hc 33 ty E33. nr_den Hc 19 2 E19. rewrite nr_bt_eq in Hc by lia. apply Z.eqb_eq in Hc.
    rename Hc into Hty2e.
    assert (HWe : chunk_walk c = if ml <? 36 then NlShort else NlErr (rd32s c (off + 16)))
      by (rewrite HCW; apply nt_msg_err; [lia | lia | exact Hty2e]).
    paj_run_tok RUN HS HJ SHOK nr_span.
    1: nr_awr_ro.
    nr_rn HS ms6. nr_nowrite HF Em6. clear HF HFr HG.
    psrr_branch_tok RUN BR HS SHOK nr_span.
    - (* +0x4b0 taken: ml >= 36, s11 := the message's code, `lw s11, 16(a1)` (+0x4c4 .. +0x4d8) *)
      idtac.
      nr_den Hc 32 ml E32. rewrite nr_den_lit, nr_bt_geu in Hc by lia. apply negb_true_iff, Z.ltb_ge in Hc.
      rewrite (proj2 (Z.ltb_ge ml 36) Hc) in HWe.
      paj_run_to_tok RUNTO HS HJ SHOK nr_span NT_exit.
      1: nr_awr_ro.
      nr_rn HS ms7. nr_nowrite HF Em7. clear HF HFr HG.
      pmkst HS.
      assert (Hregs : forall r : bv 5, In r nr_keep -> getr (ms_regs ms7) r = getr (ms_regs ms3) r)
        by nr_kreg HS HEdef.
      nr_creg HS (27%bv : bv 5) Q27.
      lazymatch type of Q27 with _ = sv_denot ?EF (SExt true 32 (SOff 34 0)) =>
        change (sv_denot EF (SExt true 32 (SOff 34 0))) with (sext 64 (bv_extract 0 32 (sv_denot EF (SOff 34 0)))) in Q27 end.
      nr_den Q27 34 code E34.
      assert (Ecode : code = rd32 c (off + 16)) by (unfold code, rd32; apply nr_rdn_app; lia).
      assert (Hsx : sext 64 (bv_extract 0 32 (Z_to_bv 64 code)) = w64 (rd32s c (off + 16))).
      { apply nt_rd32s_of_rd32''; [lia | lia |]. rewrite unsigned_lit_small by lia. rewrite Z.mod_small by lia.
        exact Ecode. }
      rewrite Hsx in Q27.
      lazymatch goal with |- SRr _ _ {| cfg_ms := ?MS; cfg_model := ?MD |} _ =>
        apply (NEXIT cx fp k2 ly3 S3 W3 MS MD HB HJ HFR) end.
      apply (nr_mk_exit j f c rest cx fp k2 ly3 S3 W3 ms3 md3 _ _ (NlErr (rd32s c (off + 16))) HC HFD HCH HWe
        ltac:(discriminate) eq_refl).
      * exact (nr_shape_mkst NT_exit _ _).
      * cbn [ms_mem mkst]. rewrite Em7, Em6, Em5, Em4, Em2, Em1. reflexivity.
      * exact Hregs.
      * cbn [ms_regs mkst nt_nlv_rc]. exact Q27.
      * nr_md.
      * nr_md.
    - (* +0x4b0 not taken: ml < 36, s11 := -EIO (+0x4b4 .. +0x4c0) *)
      idtac.
      nr_den Hc 32 ml E32. rewrite nr_den_lit, nr_bt_geu in Hc by lia. apply negb_false_iff, Z.ltb_lt in Hc.
      rewrite (proj2 (Z.ltb_lt ml 36) Hc) in HWe.
      paj_run_to_tok RUNTO HS HJ SHOK nr_span NT_exit.
      1: nr_awr_ro.
      nr_rn HS ms7. nr_nowrite HF Em7. clear HF HFr HG.
      pmkst HS.
      assert (Hregs : forall r : bv 5, In r nr_keep -> getr (ms_regs ms7) r = getr (ms_regs ms3) r)
        by nr_kreg HS HEdef.
      nr_creg HS (27%bv : bv 5) Q27.
      lazymatch goal with |- SRr _ _ {| cfg_ms := ?MS; cfg_model := ?MD |} _ =>
        apply (NEXIT cx fp k2 ly3 S3 W3 MS MD HB HJ HFR) end.
      apply (nr_mk_exit j f c rest cx fp k2 ly3 S3 W3 ms3 md3 _ _ NlShort HC HFD HCH HWe
        ltac:(discriminate) eq_refl).
      * exact (nr_shape_mkst NT_exit _ _).
      * cbn [ms_mem mkst]. rewrite Em7, Em6, Em5, Em4, Em2, Em1. reflexivity.
      * exact Hregs.
      * cbn [ms_regs mkst nt_nlv_rc]. rewrite Q27, nr_den_lit. unfold E_IO, w64. apply bv_eq. vm_compute. reflexivity.
      * nr_md.
      * nr_md. }
  nr_den Hc 33 ty E33. nr_den Hc 19 2 E19. rewrite nr_bt_eq in Hc by lia. apply Z.eqb_neq in Hc.
  rename Hc into Hty2.
  (* ---- +0x250 .. +0x268: NLMSG_ALIGN, a0 -= it, a1 += it; `blt s6, a0` ---- *)
  paj_run_tok RUN HS HJ SHOK nr_span.
  1: nr_awr_ro.
  nr_rn HS ms6. nr_nowrite HF Em6. clear HF HFr HG.
  pose proof (nt_nl_align_ge ml ltac:(lia)) as HAl.
  lazymatch type of HS with st_ok_pi _ _ ?EF _ _ =>
    destruct (nr_U_step EF left (nBUF cx fp + off) ml ltac:(cbn [ew ewset Nat.eqb]; exact E10)
      ltac:(cbn [ew ewset Nat.eqb]; exact E11) ltac:(cbn [ew ewset Nat.eqb]; exact E32)
      ltac:(lia) ltac:(unfold nBUF, NT_BUFOFF; lia) ltac:(unfold nBUF, NT_BUFOFF; lia) ltac:(lia)) as (D10 & D11) end.
  unfold nr_alignX in D10, D11.
  psrr_branch_tok RUN BR HS SHOK nr_span.
  { (* taken: 15 < left', round the loop again (+0x21c) *)
    nr_den Hc 22 15 E22. rewrite D10 in Hc. rewrite nr_bt_lt in Hc by lia. apply Z.ltb_lt in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK nr_span NT_loop.
    1: nr_awr_ro.
    nr_rn HS ms7. nr_nowrite HF Em7. clear HF HFr HG.
    pmkst HS.
    assert (Hregs : forall r : bv 5, In r nr_keep -> getr (ms_regs ms7) r = getr (ms_regs ms3) r)
      by nr_kreg HS HEdef.
    nr_creg HS (10%bv : bv 5) Q10. nr_creg HS (11%bv : bv 5) Q11.
    apply (IH (off + nl_align ml) (left - nl_align ml)); [exact HJ|].
    apply (nr_mk_loop j f c rest off left g cx fp k2 ly3 S3 W3 ms3 md3 _ _ HI); [lia | exact Hty2 | exact Hty16 | exact Hc | | | | | | | ].
    - exact (nr_shape_mkst NT_loop _ _).
    - cbn [ms_mem mkst]. rewrite Em7, Em6, Em5, Em4, Em2, Em1. reflexivity.
    - exact Hregs.
    - cbn [ms_regs mkst]. rewrite Q10, D10. reflexivity.
    - cbn [ms_regs mkst]. rewrite Q11, D11. unfold w64. rewrite Z.add_assoc. reflexivity.
    - nr_md.
    - nr_md. }
  (* not taken: left' <= 15, the chunk is done (+0x270 `j` +0x294) *)
  nr_den Hc 22 15 E22. rewrite D10 in Hc. rewrite nr_bt_lt in Hc by lia. apply Z.ltb_ge in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK nr_span NT_next.
  1: nr_awr_ro.
  nr_rn HS ms7. nr_nowrite HF Em7. clear HF HFr HG.
  pmkst HS.
  assert (Hregs : forall r : bv 5, In r nr_keep -> getr (ms_regs ms7) r = getr (ms_regs ms3) r)
    by nr_kreg HS HEdef.
  apply KN; [exact HJ|].
  apply (nr_to_next j f c rest off left (S g) cx fp k2 ly3 S3 W3 ms3 md3 _ _ HI).
  - rewrite HCW, nt_msg_skip by (first [lia | exact Hty2 | exact Hty16]). apply nr_msg_small.
    change (rd32 c off) with ml. lia.
  - exact (nr_shape_mkst NT_next _ _).
  - cbn [ms_mem mkst]. rewrite Em7, Em6, Em5, Em4, Em2, Em1. reflexivity.
  - exact Hregs.
  - nr_md.
  - nr_md.
Qed.

(* ==========================================================================
   12. The message loop, by induction on msg_scan's fuel; the chunk walk's entry
   ========================================================================== *)

Lemma nr_msg_loop : forall g j f c rest off left cx fp k2 ly3 S3 W3 ms3 md3,
  nt_base SK B cx -> NRJ cx fp k2 ly3 S3 W3 (ms_mem ms3) md3 -> frames S3 = (NT_CID, fp) :: frames (n_Sc cx) ->
  nr_loop_inv j f c rest off left g cx fp k2 ly3 S3 W3 ms3 md3 ->
  (forall ms' md', NRJ cx fp k2 ly3 S3 W3 (ms_mem ms') md' ->
     nr_next_inv (S j) f cx fp k2 ly3 S3 W3 ms' md' -> SRr SEGS W3 (mkCfg ms' md') (POST cx)) ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  induction g as [|g IHg]; intros j f c rest off left cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR HI KN.
  - exfalso. pose proof HI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hg). lia.
  - apply (nr_loop_step j f c rest off left g cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR HI); [|exact KN].
    intros off' left' ms' md' HJ' HI'. exact (IHg j f c rest off' left' cx fp k2 ly3 S3 W3 ms' md' HB HJ' HFR HI' KN).
Qed.

(* the message loop's entry: the walk at offset 0 with the whole chunk left *)
Lemma nr_mk_loop0 : forall j f c rest cx fp k2 ly3 S3 W3 ms3 md3 ms' md',
  nr_walk_inv j f c rest cx fp k2 ly3 S3 W3 ms3 md3 -> 16 <= Z.of_nat (length c) ->
  nt_shape NT_loop ms' -> ms_mem ms' = ms_mem ms3 ->
  (forall r : bv 5, In r nr_keep -> getr (ms_regs ms') r = getr (ms_regs ms3) r) ->
  getr (ms_regs ms') 10 = w64 (Z.of_nat (length c)) -> getr (ms_regs ms') 11 = w64 (nBUF cx fp + 0) ->
  m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  nr_loop_inv j f c rest 0 (Z.of_nat (length c)) (S (length c)) cx fp k2 ly3 S3 W3 ms' md'.
Proof.
  intros j f c rest cx fp k2 ly3 S3 W3 ms3 md3 ms' md' HI H16 Hsh Hm HR R10 R11 F1 F2.
  pose proof HI as (_ & HC & HFD & HK3 & _ & HCH).
  pose proof Hsh as (_ & H1 & H2 & H3 & H4 & H5).
  split; [exact Hsh|].
  split; [exact (nr_com_same cx fp k2 ly3 S3 W3 ms3 md3 ms' md' HC Hm H1 H2 H3 H4 H5 HR F1 F2)|].
  split; [exact (nr_at_same W3 ms3 ms' _ _ HFD Hm)|].
  split; [exact (nr_k3_same ms3 ms' HK3 HR)|].
  split; [exact R10|]. split; [exact R11|].
  split; [exact (nr_chunk_same j f c rest cx fp W3 ms3 ms' HCH Hm)|].
  split; [reflexivity|].
  split; [lia|]. split; [lia|]. split; [lia|]. lia.
Qed.

(* NT_walk (+0x214): `bltu a0, s4` on the chunk's length; a1 := s10 *)
Lemma nr_walk_step : forall j f c rest cx fp k2 ly3 S3 W3 ms3 md3,
  nt_base SK B cx -> NRJ cx fp k2 ly3 S3 W3 (ms_mem ms3) md3 -> frames S3 = (NT_CID, fp) :: frames (n_Sc cx) ->
  nr_walk_inv j f c rest cx fp k2 ly3 S3 W3 ms3 md3 ->
  (forall ms' md', NRJ cx fp k2 ly3 S3 W3 (ms_mem ms') md' ->
     nr_next_inv (S j) f cx fp k2 ly3 S3 W3 ms' md' -> SRr SEGS W3 (mkCfg ms' md') (POST cx)) ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros j f c rest cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR HI KN.
  pose proof HI as (Hshp & HC & HFD & HK3 & R10 & HCH).
  pose proof HCH as (HGN & Hnth & HCL & Hfu & Hab & Hlen & Hcl).
  pose proof HC as (_ & _ & _ & _ & _ & HRG & _ & _ & _ & _ & _ & _ & _ & R26 & _).
  pose proof HK3 as (R19 & R20 & R22).
  pose proof HB as (HA & _). pose proof HA as (_ & HGX & _).
  assert (Hcl' : Z.of_nat (length c) <= 4096) by (change (Z.to_nat NL_CHUNK_MAX) with 4096%nat in Hcl; lia).
  assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg (ms_regs ms3) [])) (mkSS NT_walk sr_atoms [] None (mkFacts [] [] []))
                 (restrict (w_H W3) ms3)).
  { apply nr_seat; [exact Hshp | reflexivity | apply Forall_nil | exact I | unfold facts_ok; cbn; tauto]. }
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (E10 : ew E 10 = w64 (Z.of_nat (length c)))
    by (subst E; rewrite (nr_ew_reg _ _ 10 (10%bv : bv 5) eq_refl); exact R10).
  assert (E20 : ew E 20 = w64 16) by (subst E; rewrite (nr_ew_reg _ _ 20 (20%bv : bv 5) eq_refl); exact R20).
  assert (E26 : ew E 26 = w64 (nBUF cx fp)) by (subst E; rewrite (nr_ew_reg _ _ 26 (26%bv : bv 5) eq_refl); exact R26).
  assert (SHOK : sh_ok SEGS nr_Bx [] E (rdW W3 (ms_mem ms3))) by constructor.
  pose proof (paj_run_x SK B LAWS (n_G cx) HGX (n_XO cx) (n_OUT cx)) as RUN.
  pose proof (paj_run_to_x SK B LAWS (n_G cx) HGX (n_XO cx) (n_OUT cx)) as RUNTO.
  pose proof (paj_branch (PI := PI)) as BR.
  psrr_branch_tok RUN BR HS SHOK nr_span.
  { (* taken: the chunk is shorter than a header, so its walk ends at once (+0x294) *)
    nr_den Hc 10 (Z.of_nat (length c)) E10. nr_den Hc 20 16 E20. rewrite nr_bt_ltu in Hc by lia.
    apply Z.ltb_lt in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK nr_span NT_next.
    1: nr_awr_ro.
    nr_rn HS ms1. nr_nowrite HF Em1. clear HF HFr HG.
    pmkst HS.
    assert (Hregs : forall r : bv 5, In r nr_keep -> getr (ms_regs ms1) r = getr (ms_regs ms3) r)
      by nr_kreg HS HEdef.
    apply KN; [exact HJ|].
    apply (nr_next_of j f c rest cx fp k2 ly3 S3 W3 ms3 md3 _ _ HC HFD HK3 HCH (nr_walk_short c Hc)).
    - exact (nr_shape_mkst NT_next _ _).
    - cbn [ms_mem mkst]. rewrite Em1. reflexivity.
    - exact Hregs.
    - nr_md.
    - nr_md. }
  nr_den Hc 10 (Z.of_nat (length c)) E10. nr_den Hc 20 16 E20. rewrite nr_bt_ltu in Hc by lia.
  apply Z.ltb_ge in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK nr_span NT_loop.
  1: nr_awr_ro.
  nr_rn HS ms1. nr_nowrite HF Em1. clear HF HFr HG.
  pmkst HS.
  assert (Hregs : forall r : bv 5, In r nr_keep -> getr (ms_regs ms1) r = getr (ms_regs ms3) r)
    by nr_kreg HS HEdef.
  prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
  lazymatch goal with |- SRr _ _ {| cfg_ms := ?MS; cfg_model := ?MD |} _ =>
    apply (nr_msg_loop (S (length c)) j f c rest 0 (Z.of_nat (length c)) cx fp k2 ly3 S3 W3 MS MD HB HJ HFR);
    [|exact KN] end.
  apply (nr_mk_loop0 j f c rest cx fp k2 ly3 S3 W3 ms3 md3 _ _ HI Hc).
  - exact (nr_shape_mkst NT_loop _ _).
  - cbn [ms_mem mkst]. rewrite Em1. reflexivity.
  - exact Hregs.
  - cbn [ms_regs mkst]. rewrite Q10. exact E10.
  - cbn [ms_regs mkst]. rewrite Q11, Z.add_0_r. exact E26.
  - nr_md.
  - nr_md.
Qed.

(* ==========================================================================
   13. The failure arm (NT_fail_rv, +0x2ac): ___errno_location, errno's value negated into s11, NT_exit
   ========================================================================== *)

(* ___errno_location at a call site of the phase (LinkWalkErrno.v aj_gx_errno_at) *)
Lemma nr_call_errno : forall cx fp k2 ly3 S3 (W3 : world SEGS) mem3 mdc (rg : bvmap 5 word) retk
    (Q : world SEGS -> config -> Prop),
  nt_base SK B cx -> NRJ cx fp k2 ly3 S3 W3 mem3 mdc ->
  getr rg 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  getr rg 2 = w64 (n_sp1 cx) -> getr rg 4 = getr (n_regs cx) 4 ->
  (forall rg2 md4, same_but_materialized mdc md4 -> NRJ cx fp k2 ly3 S3 W3 mem3 md4 ->
     getr rg2 10 = w64 (as_errno B) ->
     (forall r, 1 <= r < 32 -> r <> 10 -> getr rg2 (Z_to_bv 5 r) = getr rg (Z_to_bv 5 r)) ->
     SRr SEGS W3 (mkCfg (mkst rg2 (Z_to_bv 64 (BASE + retk)) mem3 (seg_rom SEGS)) md4) Q) ->
  SRr SEGS W3 (mkCfg (mkst rg (Z_to_bv 64 (pa_sigma LS____errno_location)) mem3 (seg_rom SEGS)) mdc) Q.
Proof.
  intros cx fp k2 ly3 S3 W3 mem3 mdc rg retk Q HB HJ R1 Hrk Hrk2 R2 R4 K.
  pose proof HB as (HA & _ & HNP & _).
  pose proof HA as (HJc & HGX & _ & _ & _ & Hgp & Htp & _).
  pose proof HNP as (kbs & req & _ & _ & _ & _ & _ & _ & _ & (Herr & _) & _).
  destruct (nr_base_facts cx HB) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
  pose proof NL_TALK_AK_val as EK. rewrite EK in *. pose proof asan_consts as ((C1a & C1b) & _).
  assert (Hsp : spZ rg = n_sp1 cx) by (unfold spZ; rewrite R2; apply nr_uw; lia).
  eapply SRr_bind.
  { apply (aj_gx_errno_at SK SEGS B LAWS pa_segs_low (pa_sigma LS____errno_location) ERRNO (n_G cx) (n_XO cx)
      (n_OUT cx) W3 rg mem3 (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
      ((NT_CID, fp) :: n_own cx) ly3 S3 mdc k2 (Z_to_bv 64 (BASE + retk)) HGX HJ);
      [rewrite Hsp; lia | rewrite Hsp; lia | exact R1 |].
    apply ret_ok_codeptr_v; lia. }
  cbv beta. intros W4 c4 _ (-> & rg2 & mem2 & md2 & -> & HJ2 & Hsm & H10 & Hr & Hm).
  assert (Em : mem2 = mem3) by (apply functional_extensionality; exact Hm). subst mem2.
  apply (K rg2 md2 Hsm HJ2); [| exact Hr].
  rewrite H10, R4, Htp. pose proof (ts_tp B TB) as Htp'. unfold TFIB_TP in Htp'.
  unfold w64. rewrite unsigned_lit_small by (rewrite Htp'; lia). rewrite Herr. reflexivity.
Qed.

(* the exit phase's cut, when the receive found the queue empty: the answer is - end_errno *)
Lemma nr_mk_exit_fail : forall j cx fp k2 ly3 S3 W3 ms3 md3 ms' md',
  nr_fail_inv j cx fp k2 ly3 S3 W3 ms3 md3 ->
  nt_shape NT_exit ms' -> ms_mem ms' = ms_mem ms3 ->
  (forall r : bv 5, In r nr_keepc -> getr (ms_regs ms') r = getr (ms_regs ms3) r) ->
  getr (ms_regs ms') 27 = w64 (- k_end (n_K0 cx)) ->
  m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  nt_exit_inv B cx fp k2 ly3 S3 W3 ms' md'.
Proof.
  intros j cx fp k2 ly3 S3 W3 ms3 md3 ms' md' HI Hsh Hm HR R27 F1 F2.
  pose proof HI as (_ & HC & HFD & HGN & HCL & _).
  pose proof Hsh as (_ & H1 & H2 & H3 & H4 & H5).
  pose proof (nr_com_samec cx fp k2 ly3 S3 W3 ms3 md3 ms' md' HC Hm H1 H2 H3 H4 H5 HR F1 F2) as HC'.
  destruct HC' as (_ & _ & _ & _ & _ & HRG & HSV & HHD & HSL & HSH4 & HFK & R23 & R25 & R26 & HFS & HJB & HKP
    & HOW & HBS & HAB).
  destruct (nr_answer cx NlNone j HOW HCL) as (Trc & Tat & Tnx).
  pose proof (nr_gnl_same cx W3 ms3 ms' j HGN Hm) as (bs & HNK & HGO).
  split; [exact Hsh|]. split; [exact HRG|]. split; [exact HSV|]. split; [exact HHD|].
  split; [exact HSH4|]. split; [exact HFK|].
  split; [exact (nr_at_same W3 ms3 ms' _ _ HFD Hm)|].
  split; [rewrite Trc; exact R27|].
  split; [exact HFS|]. split; [exact HJB|]. split; [exact HKP|].
  split; [exists bs; split; [exact HNK | rewrite HOW, Tnx; exact HGO]|].
  split; [exact HOW|].
  apply nt_bufs_same_fin; [rewrite Tat; reflexivity | exact HBS].
Qed.

(* `negw s11, a0` on errno's value, as the engine leaves it *)
Lemma nr_neg : forall E n e, ew E n = Z_to_bv 64 e -> 0 <= e < 2 ^ 63 ->
  sv_denot E (SAlu ALU_SUB (SLit 0) (SOff n 0)) = w64 (- e).
Proof.
  intros E n e Hn He. rewrite denot_lit_U, U_SAlu, U_SLit, (U_atom E n e Hn) by lia.
  unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. cbn [zalu_raw].
  unfold zcanon, M64, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_0_l by lia. rewrite Z.mod_mod by lia. f_equal; lia.
Qed.

Definition NT_fail_ra : Z := AF_nl_talk + 0x2b0.
(* errno, read through a0 (its value is the extra atom 32) *)
Definition nr_errR : YP09.region := YP09.mkRegion (Some 10%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))].
Definition nr_efacts : facts :=
  mkFacts (nr_cf ++ [(10%nat, mkAF 0 (SHADOW_OFF - 4) 0); (32%nat, mkAF 0 (2 ^ 31 - 1) 0)]) [] [].
Definition nr_eSH : list shent := [mkSHE 10 0 4].

Lemma nr_fail_step : forall j cx fp k2 ly3 S3 W3 ms3 md3,
  nt_base SK B cx -> NRJ cx fp k2 ly3 S3 W3 (ms_mem ms3) md3 -> frames S3 = (NT_CID, fp) :: frames (n_Sc cx) ->
  nr_fail_inv j cx fp k2 ly3 S3 W3 ms3 md3 -> SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros j cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR HI.
  pose proof HI as (Hshp & HC & HFD & HGN & HCL & Herrv).
  pose proof HC as (_ & _ & _ & _ & _ & HRG & _).
  pose proof HRG as (Rsp & Rs0 & Rs1 & Rs2 & Rs5 & Rs8 & Rgp & Rtp).
  pose proof HB as (HA & _). pose proof HA as (_ & HGX & _).
  pose proof (nr_base_facts cx HB) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
  pose proof NL_TALK_AK_val as EK.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof (ts_errno B TB) as Hte. unfold TFIB_ERRNO in Hte.
  pose proof HGN as (bs0 & _ & HGO). pose proof HGO as (WF0 & _ & _ & Eee & _).
  pose proof WF0 as (_ & _ & _ & _ & _ & _ & _ & _ & Wee & _).
  assert (He : 0 <= k_end (n_K0 cx) < 2 ^ 31)
    by (unfold n_K0, nk_kstate; cbn [k_end]; rewrite <- Eee; exact Wee).
  set (e := k_end (n_K0 cx)) in *.
  (* ---- +0x2ac: `jal ___errno_location` ---- *)
  assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg (ms_regs ms3) [])) (mkSS NT_fail_rv sr_atoms [] None (mkFacts [] [] []))
                 (restrict (w_H W3) ms3))
    by (apply nr_seat; [exact Hshp | reflexivity | apply Forall_nil | exact I | unfold facts_ok; cbn; tauto]).
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (SHOK : sh_ok SEGS nr_Bx [] E (rdW W3 (ms_mem ms3))) by constructor.
  pose proof (paj_run_x SK B LAWS (n_G cx) HGX (n_XO cx) (n_OUT cx)) as RUN.
  pose proof (paj_run_to_x SK B LAWS (n_G cx) HGX (n_XO cx) (n_OUT cx)) as RUNTO.
  paj_run_tok RUN HS HJ SHOK nr_span.
  1: nr_awr_ro.
  nr_rn HS ms1. nr_nowrite HF Em1. clear HF HFr HG.
  pmkst HS.
  assert (Hregs1 : forall r : bv 5, In r nr_keep -> getr (ms_regs ms1) r = getr (ms_regs ms3) r)
    by nr_kreg HS HEdef.
  prreg HS (1%bv : bv 5) Q1.
  apply (nr_call_errno cx fp k2 ly3 S3 W3 (ms_mem ms1) _ (ms_regs ms1) NT_fail_ra (POST cx) HB HJ);
    [ exact Q1 | unfold NT_fail_ra, AF_nl_talk; lia | reflexivity
    | rewrite (Hregs1 2%bv ltac:(unfold nr_keep; cbn; tauto)); exact Rsp
    | rewrite (Hregs1 4%bv ltac:(unfold nr_keep; cbn; tauto)); exact Rtp |].
  intros rg2 md4 Hsm HJ2 H10 Hr.
  assert (HP2 : aregs_preserved (ms_regs ms1) rg2) by (intros r Hr'; apply Hr; unfold acallee_saved in Hr'; lia).
  pose proof (nr_preserved _ _ HP2) as PRS.
  assert (HK2 : forall r : bv 5, In r nr_keep -> getr rg2 r = getr (ms_regs ms3) r).
  { intros r Hr'. rewrite <- (Hregs1 r Hr'). apply PRS.
    unfold nr_keep in Hr'. cbn [In] in Hr'. repeat (destruct Hr' as [<- | Hr']; [nr_cs|]). destruct Hr'. }
  (* ---- +0x2b0: the check of errno, `lw a0, 0(a0)`, `negw s11, a0`, `j` NT_exit ---- *)
  pose proof (nr_shape_mkst NT_fail_ra rg2 (ms_mem ms1)) as Hsh2.
  pose proof (nr_aj_AR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
  destruct (zsh_errno_ard B TB SEGS ly3 S3 W3 (ms_mem ms1) md4 HAR2) as (Era & _).
  rewrite ard_aview in Era.
  assert (HS2 : st_ok_pi SEGS VAL (Eimg (Ereg rg2 [w64 e])) (mkSS NT_fail_ra sr_atoms [nr_errR] None nr_efacts)
                  (restrict (w_H W3) (mkst rg2 (Z_to_bv 64 (BASE + NT_fail_ra)) (ms_mem ms1) (seg_rom SEGS)))).
  { apply (nr_seat NT_fail_ra _ W3 [w64 e] [nr_errR] nr_efacts Hsh2); [vm_compute; reflexivity | | unfold pairwise_disjoint; cbn; tauto |];
      cbn [ms_regs ms_mem mkst].
    - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, nr_errR.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite (nr_ew_reg _ _ 10 (10%bv : bv 5) eq_refl), H10, nr_uw by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS _ _ (as_errno B) 0 4 (SOff 32 0) e);
        [ cbn [sv_denot]; rewrite (nr_ew_ext _ _ 0 ltac:(unfold A_TEXT; lia)); cbn [nth]; rewrite Z.add_0_r;
          unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | change (Z.of_N 4) with 4; lia |].
      rewrite Z.add_0_r, Em1. exact Herrv.
    - unfold facts_ok, nr_efacts. cbn [f_atoms f_conds f_alias]. split; [|split; exact I].
      apply nr_atoms_app.
      + apply (nr_cf_ok cx _ HB).
        * rewrite (nr_ew_reg _ _ 2 (2%bv : bv 5) eq_refl), (HK2 2%bv ltac:(unfold nr_keep; cbn; tauto)). exact Rsp.
        * rewrite (nr_ew_reg _ _ 9 (9%bv : bv 5) eq_refl), (HK2 9%bv ltac:(unfold nr_keep; cbn; tauto)). exact Rs1.
        * rewrite (nr_ew_reg _ _ 21 (21%bv : bv 5) eq_refl), (HK2 21%bv ltac:(unfold nr_keep; cbn; tauto)). exact Rs5.
      + cbn [atoms_ok].
        split; [apply (nr_af0 _ 10 (as_errno B)); [rewrite (nr_ew_reg _ _ 10 (10%bv : bv 5) eq_refl), H10; apply nr_uw; lia
               | unfold SHADOW_OFF; lia]|].
        split; [apply (nr_af0 _ 32 e); [rewrite (nr_ew_ext _ _ 0 ltac:(unfold A_TEXT; lia)); cbn [nth]; apply nr_uw; lia | lia]|].
        exact I. }
  remember (Eimg (Ereg rg2 [w64 e])) as E2 eqn:HEdef2.
  assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
  assert (SHOK2 : sh_ok SEGS nr_Bx nr_eSH E2 (rdW W3 (ms_mem (mkst rg2 (Z_to_bv 64 (BASE + NT_fail_ra)) (ms_mem ms1) (seg_rom SEGS))))).
  { cbn [ms_mem mkst]. apply Forall_cons; [|apply Forall_nil].
    apply (nr_shent_ok E2 W3 (ms_mem ms1) 10 (as_errno B) 4);
      [ subst E2; rewrite (nr_ew_reg _ _ 21 (21%bv : bv 5) eq_refl), (HK2 21%bv ltac:(unfold nr_keep; cbn; tauto)); exact Rs5
      | subst E2; rewrite (nr_ew_reg _ _ 10 (10%bv : bv 5) eq_refl); exact H10
      | lia | lia | left; rewrite C5; lia | lia | exact Era ]. }
  paj_run_to_tok RUNTO HS2 HJ2 SHOK2 nr_span NT_exit.
  1: nr_awr_ro.
  nr_rn HS2 ms4. nr_nowrite HF Em4. clear HF HFr HG.
  pmkst HS2.
  assert (Hregs4 : forall r : bv 5, In r nr_keepc -> getr (ms_regs ms4) r = getr rg2 r) by nr_kregc HS2 HEdef2.
  nr_creg HS2 (27%bv : bv 5) Q27.
  lazymatch type of Q27 with _ = sv_denot ?EF _ =>
    rewrite (nr_neg EF 32 e ltac:(cbn [ew ewset Nat.eqb]; rewrite HEdef2, (nr_ew_ext _ _ 0 ltac:(unfold A_TEXT; lia));
      reflexivity) ltac:(lia)) in Q27 end.
  unfold same_but_materialized in Hsm.
  lazymatch goal with |- SRr _ _ {| cfg_ms := ?MS; cfg_model := ?MD |} _ =>
    apply (NEXIT cx fp k2 ly3 S3 W3 MS MD HB HJ2 HFR) end.
  apply (nr_mk_exit_fail j cx fp k2 ly3 S3 W3 ms3 md3 _ _ HI).
  - exact (nr_shape_mkst NT_exit _ _).
  - cbn [ms_mem mkst]. rewrite Em4, Em1. reflexivity.
  - intros r Hr'. cbn [ms_regs mkst]. rewrite (Hregs4 r Hr'). apply HK2. apply nr_keep_c. exact Hr'.
  - cbn [ms_regs mkst]. exact Q27.
  - repeat rewrite (proj1 (nr_wvb _ _)). rewrite Hsm. repeat rewrite (proj1 (nr_wvb _ _)). reflexivity.
  - repeat rewrite (proj2 (nr_wvb _ _)). rewrite Hsm. repeat rewrite (proj2 (nr_wvb _ _)). reflexivity.
Qed.

(* ==========================================================================
   14. After a receive: the queue was empty (the failure arm), or chunk j is in the buffer (its walk)
   ========================================================================== *)

Lemma nr_mk_fail : forall j f cx fp k2 ly3 S3 W3 ms3 md3 ms' md',
  nr_com cx fp k2 ly3 S3 W3 ms3 md3 -> nt_at W3 ms3 (n_sp1 cx + NS_FD) NL_FD ->
  (length (nr_cs cx) <= j)%nat -> nr_gnl cx W3 ms3 j ->
  au32_at SEGS (rdW W3 (ms_mem ms3)) (as_errno B) (k_end (n_K0 cx)) ->
  nr_CL cx = chunk_loop f (nr_cs cx) j ->
  nt_shape NT_fail_rv ms' -> ms_mem ms' = ms_mem ms3 ->
  (forall r : bv 5, In r nr_keepc -> getr (ms_regs ms') r = getr (ms_regs ms3) r) ->
  m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  nr_fail_inv j cx fp k2 ly3 S3 W3 ms' md'.
Proof.
  intros j f cx fp k2 ly3 S3 W3 ms3 md3 ms' md' HC HFD Hj HGN Herr HCL Hsh Hm HR F1 F2.
  pose proof Hsh as (_ & H1 & H2 & H3 & H4 & H5).
  split; [exact Hsh|].
  split; [exact (nr_com_samec cx fp k2 ly3 S3 W3 ms3 md3 ms' md' HC Hm H1 H2 H3 H4 H5 HR F1 F2)|].
  split; [exact (nr_at_same W3 ms3 ms' _ _ HFD Hm)|].
  split; [exact (nr_gnl_same cx W3 ms3 ms' j HGN Hm)|].
  split; [rewrite HCL; exact (nr_cl_end (nr_cs cx) f j Hj)|].
  rewrite Hm. exact Herr.
Qed.

Lemma nr_mk_walk : forall j f f' c rest cx fp k2 ly3 S3 W3 ms3 md3 ms' md',
  nr_com cx fp k2 ly3 S3 W3 ms3 md3 -> nt_at W3 ms3 (n_sp1 cx + NS_FD) NL_FD ->
  nth_error (nr_cs cx) j = Some c -> nr_gnl cx W3 ms3 (S j) ->
  abytes SEGS (rdW W3 (ms_mem ms3)) (nBUF cx fp) (c ++ rest) ->
  Z.of_nat (length (c ++ rest)) = NT_BUFLEN -> (length c <= Z.to_nat NL_CHUNK_MAX)%nat ->
  nr_CL cx = chunk_loop f (nr_cs cx) j -> f = S f' -> (length (nr_cs cx) < S (j + f'))%nat ->
  nt_shape NT_walk ms' -> ms_mem ms' = ms_mem ms3 ->
  (forall r : bv 5, In r nr_keepc -> getr (ms_regs ms') r = getr (ms_regs ms3) r) ->
  nr_k3 ms' -> getr (ms_regs ms') 10 = w64 (Z.of_nat (length c)) ->
  m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  nr_walk_inv j f' c rest cx fp k2 ly3 S3 W3 ms' md'.
Proof.
  intros j f f' c rest cx fp k2 ly3 S3 W3 ms3 md3 ms' md' HC HFD Hnth HGN Hab Hlen Hcl HCL Hf Hfu Hsh Hm HR HK3 R10 F1 F2.
  pose proof Hsh as (_ & H1 & H2 & H3 & H4 & H5).
  split; [exact Hsh|].
  split; [exact (nr_com_samec cx fp k2 ly3 S3 W3 ms3 md3 ms' md' HC Hm H1 H2 H3 H4 H5 HR F1 F2)|].
  split; [exact (nr_at_same W3 ms3 ms' _ _ HFD Hm)|].
  split; [exact HK3|]. split; [exact R10|].
  unfold nr_chunk. split; [exact (nr_gnl_same cx W3 ms3 ms' (S j) HGN Hm)|].
  split; [exact Hnth|]. split; [rewrite HCL, Hf; reflexivity|]. split; [exact Hfu|].
  rewrite Hm. split; [exact Hab|]. split; [exact Hlen | exact Hcl].
Qed.

(* NT_rv_ra (+0x204), after the first receive: `bltz a0`; s4 := 16, s3 := 2, s6 := 15 *)
Lemma nr_after1 : forall j f regs0 cx fp k2 ly3 S3 W3 ms3 md3,
  nt_base SK B cx -> NRJ cx fp k2 ly3 S3 W3 (ms_mem ms3) md3 -> frames S3 = (NT_CID, fp) :: frames (n_Sc cx) ->
  nr_rcvd NT_rv_ra j regs0 cx fp k2 ly3 S3 W3 ms3 md3 ->
  nr_CL cx = chunk_loop f (nr_cs cx) j -> nr_fuel (nr_cs cx) j f ->
  (forall f' c rest ms' md', f = S f' -> NRJ cx fp k2 ly3 S3 W3 (ms_mem ms') md' ->
     nr_walk_inv j f' c rest cx fp k2 ly3 S3 W3 ms' md' -> SRr SEGS W3 (mkCfg ms' md') (POST cx)) ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros j f regs0 cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR HR HCL Hfu KW.
  pose proof HR as (Hshp & HC & HFD & _ & HCASE).
  pose proof HB as (HA & _). pose proof HA as (_ & HGX & _).
  assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg (ms_regs ms3) [])) (mkSS NT_rv_ra sr_atoms [] None (mkFacts [] [] []))
                 (restrict (w_H W3) ms3))
    by (apply nr_seat; [exact Hshp | reflexivity | apply Forall_nil | exact I | unfold facts_ok; cbn; tauto]).
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (E10 : ew E 10 = getr (ms_regs ms3) 10) by (subst E; apply (nr_ew_reg _ _ 10 (10%bv : bv 5) eq_refl)).
  assert (SHOK : sh_ok SEGS nr_Bx [] E (rdW W3 (ms_mem ms3))) by constructor.
  pose proof (paj_run_x SK B LAWS (n_G cx) HGX (n_XO cx) (n_OUT cx)) as RUN.
  pose proof (paj_run_to_x SK B LAWS (n_G cx) HGX (n_XO cx) (n_OUT cx)) as RUNTO.
  pose proof (paj_branch (PI := PI)) as BR.
  destruct HCASE as [(Hj & R10 & HGN & Herr) | (Hj & c & rest & Hnth & R10 & HGN & Hab & Hlen & Hcl)];
    rewrite R10 in E10.
  - (* the queue was empty: a0 = -1 *)
    psrr_branch_tok RUN BR HS SHOK nr_span.
    + clear Hc.
      paj_run_to_tok RUNTO HS HJ SHOK nr_span NT_fail_rv.
      1: nr_awr_ro.
      nr_rn HS ms1. nr_nowrite HF Em1. clear HF HFr HG.
      pmkst HS.
      assert (Hregs : forall r : bv 5, In r nr_keepc -> getr (ms_regs ms1) r = getr (ms_regs ms3) r)
        by nr_kregc HS HEdef.
      lazymatch goal with |- SRr _ _ {| cfg_ms := ?MS; cfg_model := ?MD |} _ =>
        apply (nr_fail_step j cx fp k2 ly3 S3 W3 MS MD HB HJ HFR) end.
      apply (nr_mk_fail j f cx fp k2 ly3 S3 W3 ms3 md3 _ _ HC HFD Hj HGN Herr HCL).
      * exact (nr_shape_mkst NT_fail_rv _ _).
      * cbn [ms_mem mkst]. rewrite Em1. reflexivity.
      * exact Hregs.
      * nr_md.
      * nr_md.
    + exfalso. nr_den Hc 10 (-1) E10. rewrite nr_den_lit, nr_bt_lt in Hc by lia. apply Z.ltb_ge in Hc. lia.
  - (* chunk j is in the buffer: a0 = its length *)
    assert (Hcl' : (length c <= 4096)%nat) by (change (Z.to_nat NL_CHUNK_MAX) with 4096%nat in Hcl; exact Hcl).
    psrr_branch_tok RUN BR HS SHOK nr_span.
    + exfalso. nr_den Hc 10 (Z.of_nat (length c)) E10. rewrite nr_den_lit, nr_bt_lt in Hc by lia.
      apply Z.ltb_lt in Hc. lia.
    + clear Hc.
      destruct (nr_cl_some (nr_cs cx) f j Hj Hfu) as (f' & c' & Hf & Hnth' & Hfu').
      rewrite Hnth in Hnth'. injection Hnth' as <-.
      paj_run_to_tok RUNTO HS HJ SHOK nr_span NT_walk.
      1: nr_awr_ro.
      nr_rn HS ms1. nr_nowrite HF Em1. clear HF HFr HG.
      pmkst HS.
      assert (Hregs : forall r : bv 5, In r nr_keepc -> getr (ms_regs ms1) r = getr (ms_regs ms3) r)
        by nr_kregc HS HEdef.
      prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22.
      prreg HS (10%bv : bv 5) Q10.
      lazymatch goal with |- SRr _ _ {| cfg_ms := ?MS; cfg_model := ?MD |} _ =>
        apply (KW f' c rest MS MD Hf HJ) end.
      apply (nr_mk_walk j f f' c rest cx fp k2 ly3 S3 W3 ms3 md3 _ _ HC HFD Hnth HGN Hab Hlen Hcl HCL Hf Hfu').
      * exact (nr_shape_mkst NT_walk _ _).
      * cbn [ms_mem mkst]. rewrite Em1. reflexivity.
      * exact Hregs.
      * unfold nr_k3. cbn [ms_regs mkst]. rewrite Q19, Q20, Q22. split; [reflexivity | split; reflexivity].
      * cbn [ms_regs mkst]. rewrite Q10. exact E10.
      * nr_md.
      * nr_md.
Qed.

(* NT_rv2_ra (+0x2a8), after a later receive: `bgez a0` to the chunk's walk, else the failure arm *)
Lemma nr_after2 : forall j f regs0 cx fp k2 ly3 S3 W3 ms3 md3,
  nt_base SK B cx -> NRJ cx fp k2 ly3 S3 W3 (ms_mem ms3) md3 -> frames S3 = (NT_CID, fp) :: frames (n_Sc cx) ->
  nr_rcvd NT_rv2_ra j regs0 cx fp k2 ly3 S3 W3 ms3 md3 -> nr_k3 ms3 ->
  nr_CL cx = chunk_loop f (nr_cs cx) j -> nr_fuel (nr_cs cx) j f ->
  (forall f' c rest ms' md', f = S f' -> NRJ cx fp k2 ly3 S3 W3 (ms_mem ms') md' ->
     nr_walk_inv j f' c rest cx fp k2 ly3 S3 W3 ms' md' -> SRr SEGS W3 (mkCfg ms' md') (POST cx)) ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros j f regs0 cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR HR HK3 HCL Hfu KW.
  pose proof HR as (Hshp & HC & HFD & _ & HCASE).
  pose proof HB as (HA & _). pose proof HA as (_ & HGX & _).
  assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg (ms_regs ms3) [])) (mkSS NT_rv2_ra sr_atoms [] None (mkFacts [] [] []))
                 (restrict (w_H W3) ms3))
    by (apply nr_seat; [exact Hshp | reflexivity | apply Forall_nil | exact I | unfold facts_ok; cbn; tauto]).
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (E10 : ew E 10 = getr (ms_regs ms3) 10) by (subst E; apply (nr_ew_reg _ _ 10 (10%bv : bv 5) eq_refl)).
  assert (SHOK : sh_ok SEGS nr_Bx [] E (rdW W3 (ms_mem ms3))) by constructor.
  pose proof (paj_run_x SK B LAWS (n_G cx) HGX (n_XO cx) (n_OUT cx)) as RUN.
  pose proof (paj_run_to_x SK B LAWS (n_G cx) HGX (n_XO cx) (n_OUT cx)) as RUNTO.
  pose proof (paj_branch (PI := PI)) as BR.
  destruct HCASE as [(Hj & R10 & HGN & Herr) | (Hj & c & rest & Hnth & R10 & HGN & Hab & Hlen & Hcl)];
    rewrite R10 in E10.
  - psrr_branch_tok RUN BR HS SHOK nr_span.
    + exfalso. nr_den Hc 10 (-1) E10. rewrite nr_den_lit, nr_bt_ge in Hc by lia. apply negb_true_iff, Z.ltb_ge in Hc. lia.
    + clear Hc.
      paj_run_to_tok RUNTO HS HJ SHOK nr_span NT_fail_rv.
      1: nr_awr_ro.
      nr_rn HS ms1. nr_nowrite HF Em1. clear HF HFr HG.
      pmkst HS.
      assert (Hregs : forall r : bv 5, In r nr_keepc -> getr (ms_regs ms1) r = getr (ms_regs ms3) r)
        by nr_kregc HS HEdef.
      lazymatch goal with |- SRr _ _ {| cfg_ms := ?MS; cfg_model := ?MD |} _ =>
        apply (nr_fail_step j cx fp k2 ly3 S3 W3 MS MD HB HJ HFR) end.
      apply (nr_mk_fail j f cx fp k2 ly3 S3 W3 ms3 md3 _ _ HC HFD Hj HGN Herr HCL).
      * exact (nr_shape_mkst NT_fail_rv _ _).
      * cbn [ms_mem mkst]. rewrite Em1. reflexivity.
      * exact Hregs.
      * nr_md.
      * nr_md.
  - assert (Hcl' : (length c <= 4096)%nat) by (change (Z.to_nat NL_CHUNK_MAX) with 4096%nat in Hcl; exact Hcl).
    psrr_branch_tok RUN BR HS SHOK nr_span.
    + clear Hc.
      destruct (nr_cl_some (nr_cs cx) f j Hj Hfu) as (f' & c' & Hf & Hnth' & Hfu').
      rewrite Hnth in Hnth'. injection Hnth' as <-.
      paj_run_to_tok RUNTO HS HJ SHOK nr_span NT_walk.
      1: nr_awr_ro.
      nr_rn HS ms1. nr_nowrite HF Em1. clear HF HFr HG.
      pmkst HS.
      assert (Hregs : forall r : bv 5, In r nr_keep -> getr (ms_regs ms1) r = getr (ms_regs ms3) r)
        by nr_kreg HS HEdef.
      prreg HS (10%bv : bv 5) Q10.
      lazymatch goal with |- SRr _ _ {| cfg_ms := ?MS; cfg_model := ?MD |} _ =>
        apply (KW f' c rest MS MD Hf HJ) end.
      apply (nr_mk_walk j f f' c rest cx fp k2 ly3 S3 W3 ms3 md3 _ _ HC HFD Hnth HGN Hab Hlen Hcl HCL Hf Hfu').
      * exact (nr_shape_mkst NT_walk _ _).
      * cbn [ms_mem mkst]. rewrite Em1. reflexivity.
      * intros r Hr. exact (Hregs r (nr_keep_c r Hr)).
      * exact (nr_k3_same ms3 _ HK3 Hregs).
      * cbn [ms_regs mkst]. rewrite Q10. exact E10.
      * nr_md.
      * nr_md.
    + exfalso. nr_den Hc 10 (Z.of_nat (length c)) E10. rewrite nr_den_lit, nr_bt_ge in Hc by lia.
      apply negb_false_iff, Z.ltb_lt in Hc. lia.
Qed.

(* ==========================================================================
   15. The cut predicates across the spill of the socket (`sd s6, 0x28(s1)`, +0x1f0)
   ========================================================================== *)

Lemma nr_av_raw : forall (H : word -> bool) (m m' : word -> option byte) a,
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> aview SEGS H m' a = aview SEGS H m a.
Proof. intros H m m' a E. unfold aview, mbyte, mrestrict. rewrite E. reflexivity. Qed.

Lemma nr_mb_raw : forall (H : word -> bool) (m m' : word -> option byte) a,
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> mbyte SEGS (mrestrict H m') a = mbyte SEGS (mrestrict H m) a.
Proof. intros H m m' a E. unfold mbyte, mrestrict. rewrite E. reflexivity. Qed.

Lemma nr_wr_raw : forall (H : word -> bool) (m m' : word -> option byte) a,
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> writable_at SEGS (mrestrict H m) a -> writable_at SEGS (mrestrict H m') a.
Proof. intros H m m' a E Hw. unfold writable_at, wview, mrestrict in *. rewrite E. exact Hw. Qed.

(* the memories agree at every address but the eight bytes of the socket's spill slot *)
Definition nr_agw (cx : ntcx) (m m' : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ (n_sp1 cx + 40 <= a < n_sp1 cx + 48) -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).

Lemma nr_at_agw : forall cx (W : world SEGS) ms ms' a v, nr_agw cx (ms_mem ms) (ms_mem ms') ->
  0 <= a -> a + 8 <= 2 ^ 64 -> (a + 8 <= n_sp1 cx + 40 \/ n_sp1 cx + 48 <= a) ->
  nt_at W ms a v -> nt_at W ms' a v.
Proof.
  intros cx W ms ms' a v HA H0 H1 Hd Hat. unfold nt_at in *.
  apply (nr_rdword_kept (aview SEGS (w_H W) (ms_mem ms)) (aview SEGS (w_H W) (ms_mem ms')) a v); [|exact Hat].
  intros i Hi. apply nr_av_raw. apply HA; lia.
Qed.

Lemma nr_abytes_raw : forall (H : word -> bool) (m m' : word -> option byte) p bs,
  (forall a, p <= a < p + Z.of_nat (length bs) -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  abytes SEGS (mrestrict H m) p bs -> abytes SEGS (mrestrict H m') p bs.
Proof.
  intros H m m' p bs HA (H0 & H1 & H2). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite (nr_mb_raw H m m') by (apply HA; lia). exact (H2 i Hi).
Qed.

Lemma nr_awrange_raw : forall (H : word -> bool) (m m' : word -> option byte) p n,
  (forall a, p <= a < p + n -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  awrange SEGS (mrestrict H m) p n -> awrange SEGS (mrestrict H m') p n.
Proof. intros H m m' p n HA Hw i Hi. apply (nr_wr_raw H m m'); [apply HA; lia | exact (Hw i Hi)]. Qed.

Lemma nr_abuf_raw : forall (H : word -> bool) (m m' : word -> option byte) p n,
  (forall a, p <= a < p + n -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  abuf SEGS (mrestrict H m) p n -> abuf SEGS (mrestrict H m') p n.
Proof.
  intros H m m' p n HA (junk & Hl & Hb & Hw). subst n. exists junk. split; [reflexivity|].
  split; [apply (nr_abytes_raw H m m' p junk); [intros a Ha; apply HA; lia | exact Hb]|].
  exact (nr_awrange_raw H m m' p _ HA Hw).
Qed.

Lemma nr_anlk_raw : forall (H : word -> bool) (m m' : word -> option byte) bs,
  (forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  anlk_at SEGS (mrestrict H m) LA_G_NL bs -> anlk_at SEGS (mrestrict H m') LA_G_NL bs.
Proof.
  intros H m m' bs HA ((Hb & Hw) & Hl). split; [split|exact Hl].
  - apply (nr_abytes_raw H m m' LA_G_NL bs); [intros a Ha; apply HA; lia | exact Hb].
  - apply (nr_awrange_raw H m m' LA_G_NL _); [intros a Ha; apply HA; lia | exact Hw].
Qed.

Lemma nr_gnl_agw : forall cx (W3 : world SEGS) ms ms' j, nr_agw cx (ms_mem ms) (ms_mem ms') ->
  alloc_ceiling <= n_sp1 cx -> nr_gnl cx W3 ms j -> nr_gnl cx W3 ms' j.
Proof.
  intros cx W3 ms ms' j HA Hc (bs & HNK & HGO). exists bs. split; [|exact HGO].
  apply (nr_anlk_raw (w_H W3) (ms_mem ms) (ms_mem ms') bs); [|exact HNK].
  intros a Ha. pose proof asan_consts as ((C1a & C1b) & _). apply HA; unfold LA_G_NL, NK_SIZE in *; lia.
Qed.

(* the spill of the socket keeps every cut predicate but the slot's own *)
Lemma nr_com_write : forall cx fp k2 ly3 S3 W3 ms md ms' md',
  nt_base SK B cx -> NRJ cx fp k2 ly3 S3 W3 (ms_mem ms) md -> frames S3 = (NT_CID, fp) :: frames (n_Sc cx) ->
  nr_com cx fp k2 ly3 S3 W3 ms md ->
  nr_agw cx (ms_mem ms) (ms_mem ms') ->
  mem_grows (rdW W3 (ms_mem ms)) (rdW W3 (ms_mem ms')) ->
  ms_resv ms' = None -> ms_svc_pending ms' = None -> ms_rom ms' = seg_rom SEGS ->
  ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr ->
  (forall r : bv 5, In r nr_keepc -> getr (ms_regs ms') r = getr (ms_regs ms) r) ->
  m_fds md' = m_fds md -> m_fs md' = m_fs md ->
  nr_com cx fp k2 ly3 S3 W3 ms' md'.
Proof.
  intros cx fp k2 ly3 S3 W3 ms md ms' md' HB HJ HFR HC HA HG H1 H2 H3 H4 H5 HR F1 F2.
  pose proof (nr_cut_nums cx fp k2 ly3 S3 W3 ms md HB HJ HFR HC) as
    (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & G1 & G2 & G3 & G4 & G5 & G6 & HAR & Hin & Hfa).
  destruct HC as (_ & _ & _ & _ & _ & HRG & HSV & HHD & HSL & HSH4 & HFK & R23 & R25 & R26 & HFS & HJB & HKP
    & HOW & HBS & HAB).
  pose proof NL_TALK_AK_val as EK. rewrite EK in *.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HAV : forall a, 0 <= a < 2 ^ 64 -> ~ (n_sp1 cx + 40 <= a < n_sp1 cx + 48) ->
            aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms) a)
    by (intros a Ha Hn; apply nr_av_raw; apply HA; assumption).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split.
  { unfold nt_regs in *. rewrite !HR by (unfold nr_keepc; cbn; tauto). exact HRG. }
  split.
  { destruct HSV as (S1 & S2). split.
    - apply (nr_at_agw cx W3 ms ms' _ _ HA); [lia | lia | lia | exact S1].
    - intros jj Hjj. apply (nr_at_agw cx W3 ms ms' _ _ HA); [lia | lia | lia | exact (S2 jj Hjj)]. }
  split.
  { destruct HHD as (D1 & D2 & D3 & D4). unfold nt_header. change (fs_frame_bytes NT_CID) with 32768 in *.
    split; [apply (nr_at_agw cx W3 ms ms' _ _ HA); [lia | lia | lia | exact D1]|].
    split; [apply (nr_at_agw cx W3 ms ms' _ _ HA); [lia | lia | lia | exact D2]|].
    split; [apply (nr_at_agw cx W3 ms ms' _ _ HA); [lia | lia | lia | exact D3]|].
    apply (nr_at_agw cx W3 ms ms' _ _ HA); [lia | lia | lia | exact D4]. }
  split.
  { destruct HSL as (L1 & L2 & L3). unfold nt_slots0. unfold NS_KIND, NS_KINDN, NS_F in *.
    split; [apply (nr_at_agw cx W3 ms ms' _ _ HA); [lia | lia | lia | exact L1]|].
    split; [apply (nr_at_agw cx W3 ms ms' _ _ HA); [lia | lia | lia | exact L2]|].
    apply (nr_at_agw cx W3 ms ms' _ _ HA); [lia | lia | lia | exact L3]. }
  split; [unfold NS_SH4 in *; apply (nr_at_agw cx W3 ms ms' _ _ HA); [lia | lia | lia | exact HSH4]|].
  split; [unfold NS_FK in *; apply (nr_at_agw cx W3 ms ms' _ _ HA); [lia | lia | lia | exact HFK]|].
  split; [rewrite HR by (unfold nr_keepc; cbn; tauto); exact R23|].
  split; [rewrite HR by (unfold nr_keepc; cbn; tauto); exact R25|].
  split; [rewrite HR by (unfold nr_keepc; cbn; tauto); exact R26|].
  split.
  { destruct HFS as (S1 & S2 & S4). unfold nt_frame_shadow. rewrite G4 in *.
    unfold SHADOW_OFF in *.
    split; [intros i Hi; rewrite HAV by lia; exact (S1 i Hi)|].
    split; [intros i Hi; rewrite HAV by lia; exact (S2 i Hi)|].
    intros i Hi; rewrite HAV by lia; exact (S4 i Hi). }
  split.
  { pose proof HJB as (J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9).
    unfold nt_jbk. split; [exact J1|]. split; [exact J2|]. split; [exact J3|]. split; [exact J4|].
    split; [exact J5|]. split; [exact J6|]. split; [exact J7|]. split; [rewrite F1; exact J8 | rewrite F2; exact J9]. }
  split.
  { destruct HKP as (HKc & HRO & HEn). split; [|split; [|exact HEn]].
    - pose proof HB as (HAp & _). pose proof HAp as (HJc & _).
      assert (HARc : AR SEGS B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx))
        by (destruct HJc as (_ & _ & (memS & HJi & _) & _); exact (proj1 HJi)).
      apply (akept_step SK SEGS B LAWS pa_segs_low (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) W3
        (ms_mem ms) W3 (ms_mem ms') (spZ (n_regs cx) - 8448) (spZ (n_regs cx)) _ _
        (fun a => n_sp1 cx + 40 <= a < n_sp1 cx + 48) HARc ltac:(lia) ltac:(lia) HKc).
      + intros a Ha Hn. exact (HAV a Ha Hn).
      + intros a Ha Hp. eapply apresent_grows; [exact HG | exact Hp].
      + intros a Ha. exact Ha.
      + intros a Ha. right. lia.
    - apply (nr_ro_kept _ _ HRO). intros a Hro Hns Her.
      pose proof (pa_segs_low a (nr_ro_img a Hro)) as Hl. rewrite C5 in Hl. apply HAV; lia. }
  split; [exact HOW|].
  split.
  { pose proof HB as (_ & _ & HNP & _).
    pose proof HNP as (kbs & req & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
      & _ & _ & _ & Hka & Haa & Hck & Hca).
    apply (nr_bufs_frame cx (rdW W3 (ms_mem ms)) (rdW W3 (ms_mem ms'))); [| | exact HBS].
    - intros Hk Hn a Ha. destruct (Hka Hk) as (Hkf & _). destruct (Hck Hk Hn) as (Hkr & _ & _).
      unfold apart_frame in Hkf. rewrite EK in Hkf. unfold amem_range in Hkr. rewrite C3, C4, C5 in Hkr.
      assert (Hk0 : 0 <= n_kind cx) by exact (proj1 (bv_unsigned_in_range _ _)).
      unfold n_kind, n_kindn in Ha, Hk0.
      assert (Hraw : ms_mem ms' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)) by (apply HA; lia).
      split; [exact (nr_mb_raw _ _ _ a Hraw) | exact (nr_wr_raw _ _ _ a Hraw)].
    - intros Hk Hn a Ha. destruct (Haa Hk) as (Hkf & _). destruct (Hca Hk Hn) as (Hkr & _ & _).
      unfold apart_frame in Hkf. rewrite EK in Hkf. unfold amem_range in Hkr. rewrite C3, C4, C5 in Hkr.
      assert (Hk0 : 0 <= n_alias cx) by exact (proj1 (bv_unsigned_in_range _ _)).
      unfold n_alias, n_aliasn in Ha, Hk0.
      assert (Hraw : ms_mem ms' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)) by (apply HA; lia).
      split; [exact (nr_mb_raw _ _ _ a Hraw) | exact (nr_wr_raw _ _ _ a Hraw)]. }
  apply (nr_abuf_raw (w_H W3) (ms_mem ms) (ms_mem ms') (nBUF cx fp) NT_BUFLEN); [|exact HAB].
  intros a Ha. unfold nBUF, NT_BUFOFF, NT_BUFLEN in Ha. apply HA; lia.
Qed.

(* the spilled socket, read off the final state's spill region *)
Lemma nr_spill_at : forall EF ss (W : world SEGS) ms r v val,
  st_ok SEGS EF ss (restrict (w_H W) ms) ->
  In r (ss_mem ss) -> YP09.r_base r = Some 9%nat -> In (YP09.mkChunk 40 (CVal 8 v)) (YP09.r_chunks r) ->
  sv_denot EF v = Z_to_bv 64 val -> 0 <= val < 2 ^ 64 ->
  nt_at W ms (bv_unsigned (ew EF 9) + 40) val.
Proof.
  intros EF ss W ms r v val HS Hr Hb Hc Hv Hval.
  pose proof (st_ok_mem_ok SEGS EF ss _ HS) as HM.
  pose proof (mem_ok_region SEGS EF _ _ r HM Hr) as HRo.
  pose proof (region_ok_chunk SEGS EF _ r _ HRo Hc) as HCk.
  rewrite Hb in HCk. cbn [base_val] in HCk.
  pose proof (YN0h.word_mem_of_chunk SEGS EF _ _ 40 v val HCk Hv) as HW.
  apply val_mem_word_mem in HW. cbn [ms_mem restrict] in HW.
  unfold nt_at. exact (rdword_of_val_mem SEGS (w_H W) (ms_mem ms) _ val HW Hval).
Qed.

(* ==========================================================================
   16. The two calls of fuzz_recv: the first (+0x1ec .. +0x200) and the next (+0x294 .. +0x2a4)
   ========================================================================== *)

Lemma nr_stack_writable : forall cx fp k2 ly3 S3 (W3 : world SEGS) mem3 md3 a,
  NRJ cx fp k2 ly3 S3 W3 mem3 md3 -> n_sp0 cx - n_STK cx <= a < n_sp0 cx -> writable_at SEGS (rdW W3 mem3) a.
Proof.
  intros cx fp k2 ly3 S3 W3 mem3 md3 a HJ Ha. pose proof HJ as (_ & _ & (memS & HJi & _) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
  destruct (nr_aj_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (_ & _ & _ & HXO).
  apply apresent_writable. apply Hpres. lia.
Qed.

(* the spill slot of the socket: written at +0x1f0, read at +0x294 *)
Definition nr_spW : YP09.region := YP09.mkRegion (Some 9%nat) 40 48 40 48 [].
Definition nr_spR : YP09.region := YP09.mkRegion (Some 9%nat) 40 48 0 0 [YP09.mkChunk 40 (CVal 8 (SOff 32 0))].

(* NT_mf0_ra (+0x1ec): a2 := 16384, `sd s6, 0x28(s1)`, a0 := s6, a1 := s10, a3 := 0, `jal fuzz_recv` *)
Lemma nr_first : forall cx fp k2 ly3 S3 W3 ms3 md3,
  nt_base SK B cx -> NRJ cx fp k2 ly3 S3 W3 (ms_mem ms3) md3 -> frames S3 = (NT_CID, fp) :: frames (n_Sc cx) ->
  nt_recv_inv B cx fp k2 ly3 S3 W3 ms3 md3 ->
  (forall regs0 ly2 S2 W2 ms2 md2, NRJ cx fp k2 ly2 S2 W2 (ms_mem ms2) md2 ->
     frames S2 = (NT_CID, fp) :: frames (n_Sc cx) ->
     nr_rcvd NT_rv_ra (k_next (n_K0 cx)) regs0 cx fp k2 ly2 S2 W2 ms2 md2 -> SRr SEGS W2 (mkCfg ms2 md2) (POST cx)) ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR HI K.
  destruct HI as (Hshp & HRG & HSV & HHD & HSL & HSH4 & HFK & R19 & R20 & R22 & R23 & R25 & R26 & HFS & HJB & HKP
    & HGN & HOW & HBS & HAB).
  pose proof Hshp as (Hpc & H1 & H2 & H3 & H4 & H5).
  assert (HC : nr_com cx fp k2 ly3 S3 W3 ms3 md3).
  { split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
    split; [exact HRG|]. split; [exact HSV|]. split; [exact HHD|]. split; [exact HSL|]. split; [exact HSH4|].
    split; [exact HFK|]. split; [exact R23|]. split; [exact R25|]. split; [exact R26|]. split; [exact HFS|].
    split; [exact HJB|]. split; [exact HKP|]. split; [exact HOW|]. split; [exact HBS | exact HAB]. }
  pose proof (nr_cut_nums cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR HC) as
    (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & G1 & G2 & G3 & G4 & G5 & G6 & HAR & Hin & Hfa).
  pose proof HRG as (Rsp & Rs0 & Rs1 & Rs2 & Rs5 & Rs8 & Rgp & Rtp).
  pose proof HB as (HA & _). pose proof HA as (_ & HGX & _).
  pose proof NL_TALK_AK_val as EK. rewrite EK in *.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct nr_vals as (VB & VR & VE).
  assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg (ms_regs ms3) [])) (mkSS NT_mf0_ra sr_atoms [nr_spW] None (mkFacts nr_cf [] []))
                 (restrict (w_H W3) ms3)).
  { apply nr_seat; [exact Hshp | vm_compute; reflexivity | | unfold pairwise_disjoint; cbn; tauto |].
    - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, nr_spW.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite (nr_ew_reg _ _ 9 (9%bv : bv 5) eq_refl), Rs1, nr_uw by lia.
      split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (nr_stack_writable cx fp k2 ly3 S3 W3 (ms_mem ms3) md3 _ HJ). lia.
    - unfold facts_ok. cbn [f_atoms f_conds f_alias]. split; [|split; exact I].
      apply (nr_cf_ok cx _ HB);
        [ rewrite (nr_ew_reg _ _ 2 (2%bv : bv 5) eq_refl); exact Rsp
        | rewrite (nr_ew_reg _ _ 9 (9%bv : bv 5) eq_refl); exact Rs1
        | rewrite (nr_ew_reg _ _ 21 (21%bv : bv 5) eq_refl); exact Rs5 ]. }
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (E9u : bv_unsigned (ew E 9) = n_sp1 cx)
    by (subst E; rewrite (nr_ew_reg _ _ 9 (9%bv : bv 5) eq_refl), Rs1; apply nr_uw; lia).
  assert (E22 : ew E 22 = w64 NL_FD) by (subst E; rewrite (nr_ew_reg _ _ 22 (22%bv : bv 5) eq_refl); exact R22).
  assert (E26 : ew E 26 = w64 (nBUF cx fp)) by (subst E; rewrite (nr_ew_reg _ _ 26 (26%bv : bv 5) eq_refl); exact R26).
  assert (SHOK : sh_ok SEGS nr_Bx [] E (rdW W3 (ms_mem ms3))) by constructor.
  pose proof (paj_run_x SK B LAWS (n_G cx) HGX (n_XO cx) (n_OUT cx)) as RUN.
  pose proof HJ as HJ0.
  paj_run_tok RUN HS HJ SHOK nr_span.
  1: { lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ =>
         let rs' := eval vm_compute in rs in change rs with rs' end.
       apply awr_ok_x_cons; [|apply awr_ok_x_nil]. intros a Ha.
       cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite E9u in Ha.
       left. split; [left; lia | lia]. }
  nr_rn HS ms1.
  assert (HAG : nr_agw cx (ms_mem ms3) (ms_mem ms1)).
  { intros a Ha Hn. apply HF. rewrite unsigned_lit_small by lia. intros (r & Hinr & Hr).
    vm_compute in Hinr. destruct Hinr as [<- | []].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite E9u in Hr. lia. }
  clear HF HFr.
  (* the spilled socket *)
  assert (HFD1 : nt_at W3 ms1 (n_sp1 cx + NS_FD) NL_FD).
  { lazymatch type of HS with st_ok _ ?EF _ _ =>
      assert (U9F : bv_unsigned (ew EF 9) = n_sp1 cx) by (cbn [ew ewset Nat.eqb]; exact E9u);
      rewrite <- U9F; unfold NS_FD;
      apply (nr_spill_at EF _ W3 ms1 (YP09.mkRegion (Some 9%nat) 40 48 40 48 [YP09.mkChunk 40 (CVal 8 (SOff 22 0))])
        (SOff 22 0) NL_FD HS);
      [ vm_compute; left; reflexivity | reflexivity | cbn; left; reflexivity
      | apply nr_den_atom; cbn [ew ewset Nat.eqb]; exact E22 | unfold NL_FD; lia ] end. }
  pmkst HS.
  assert (Hregs : forall r : bv 5, In r nr_keepc -> getr (ms_regs ms1) r = getr (ms_regs ms3) r)
    by nr_kregc HS HEdef.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  lazymatch goal with |- SRr _ _ {| cfg_ms := ?MS; cfg_model := ?MD |} _ =>
    apply (nr_call POST NT_rv_ra (k_next (n_K0 cx)) cx fp k2 ly3 S3 W3 MS MD HB HJ HFR) end.
  - unfold nr_pre. cbn [ms_pc_val ms_regs ms_mem mkst].
    split; [rewrite VR; reflexivity|].
    split.
    { apply (nr_com_write cx fp k2 ly3 S3 W3 ms3 md3 _ _ HB HJ0 HFR HC); cbn [ms_mem ms_regs ms_resv ms_svc_pending
        ms_rom ms_fregs ms_fcsr mkst]; [exact HAG | exact HG | reflexivity | reflexivity | reflexivity | reflexivity
        | reflexivity | exact Hregs | nr_md | nr_md]. }
    split; [exact HFD1|].
    split; [exact (nr_gnl_agw cx W3 ms3 _ _ HAG ltac:(lia) HGN)|].
    split; [rewrite Q1; reflexivity|].
    split; [rewrite Q10; exact E22|].
    split; [rewrite Q11; exact E26|].
    rewrite Q12. reflexivity.
  - unfold NT_rv_ra, AF_nl_talk. lia.
  - reflexivity.
  - intros ly2 S2 W2 ms2 md2 HJ2 HFR2 HR2. exact (K _ ly2 S2 W2 ms2 md2 HJ2 HFR2 HR2).
Qed.

(* NT_next (+0x294): a2 := 16384, a0 := the socket from 0x28(s1), a1 := s10, a3 := 0, `jal fuzz_recv` *)
Lemma nr_next_step : forall j f cx fp k2 ly3 S3 W3 ms3 md3,
  nt_base SK B cx -> NRJ cx fp k2 ly3 S3 W3 (ms_mem ms3) md3 -> frames S3 = (NT_CID, fp) :: frames (n_Sc cx) ->
  nr_next_inv j f cx fp k2 ly3 S3 W3 ms3 md3 ->
  (forall regs0 ly2 S2 W2 ms2 md2, NRJ cx fp k2 ly2 S2 W2 (ms_mem ms2) md2 ->
     frames S2 = (NT_CID, fp) :: frames (n_Sc cx) -> nr_k3 ms2 ->
     nr_rcvd NT_rv2_ra j regs0 cx fp k2 ly2 S2 W2 ms2 md2 -> SRr SEGS W2 (mkCfg ms2 md2) (POST cx)) ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros j f cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR HI K.
  pose proof HI as (Hshp & HC & HFD & HK3 & HGN & HCL & Hfu).
  pose proof HC as (_ & _ & _ & _ & _ & HRG & _ & _ & _ & _ & _ & _ & _ & R26 & _).
  pose proof HRG as (Rsp & Rs0 & Rs1 & Rs2 & Rs5 & Rs8 & Rgp & Rtp).
  pose proof HK3 as (R19 & R20 & R22).
  pose proof HB as (HA & _). pose proof HA as (_ & HGX & _).
  pose proof (nr_base_facts cx HB) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
  pose proof NL_TALK_AK_val as EK. rewrite EK in *.
  pose proof asan_consts as ((C1a & C1b) & _).
  destruct nr_vals as (VB & VR & VE).
  assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg (ms_regs ms3) [w64 NL_FD]))
                 (mkSS NT_next sr_atoms [nr_spR] None (mkFacts nr_cf [] [])) (restrict (w_H W3) ms3)).
  { apply nr_seat; [exact Hshp | vm_compute; reflexivity | | unfold pairwise_disjoint; cbn; tauto |].
    - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, nr_spR.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite (nr_ew_reg _ _ 9 (9%bv : bv 5) eq_refl), Rs1, nr_uw by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS _ _ (n_sp1 cx) 40 8 (SOff 32 0) NL_FD);
        [ cbn [sv_denot]; rewrite (nr_ew_ext _ _ 0 ltac:(unfold A_TEXT; lia)); cbn [nth]; rewrite Z.add_0_r;
          unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
        | unfold NL_FD; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | change (Z.of_N 8) with 8; lia |].
      apply val_mem_of_rdword. exact HFD.
    - unfold facts_ok. cbn [f_atoms f_conds f_alias]. split; [|split; exact I].
      apply (nr_cf_ok cx _ HB);
        [ rewrite (nr_ew_reg _ _ 2 (2%bv : bv 5) eq_refl); exact Rsp
        | rewrite (nr_ew_reg _ _ 9 (9%bv : bv 5) eq_refl); exact Rs1
        | rewrite (nr_ew_reg _ _ 21 (21%bv : bv 5) eq_refl); exact Rs5 ]. }
  remember (Eimg (Ereg (ms_regs ms3) [w64 NL_FD])) as E eqn:HEdef.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (E32 : ew E 32 = w64 NL_FD) by (subst E; exact (nr_ew_ext _ _ 0 ltac:(unfold A_TEXT; lia))).
  assert (E26 : ew E 26 = w64 (nBUF cx fp)) by (subst E; rewrite (nr_ew_reg _ _ 26 (26%bv : bv 5) eq_refl); exact R26).
  assert (SHOK : sh_ok SEGS nr_Bx [] E (rdW W3 (ms_mem ms3))) by constructor.
  pose proof (paj_run_x SK B LAWS (n_G cx) HGX (n_XO cx) (n_OUT cx)) as RUN.
  paj_run_tok RUN HS HJ SHOK nr_span.
  1: nr_awr_ro.
  nr_rn HS ms1. nr_nowrite HF Em1. clear HF HFr HG.
  pmkst HS.
  assert (Hregs : forall r : bv 5, In r nr_keep -> getr (ms_regs ms1) r = getr (ms_regs ms3) r)
    by nr_kreg HS HEdef.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  lazymatch goal with |- SRr _ _ {| cfg_ms := ?MS; cfg_model := ?MD |} _ =>
    apply (nr_call POST NT_rv2_ra j cx fp k2 ly3 S3 W3 MS MD HB HJ HFR) end.
  - unfold nr_pre. cbn [ms_pc_val ms_regs ms_mem mkst].
    split; [rewrite VR; reflexivity|].
    split.
    { apply (nr_com_same cx fp k2 ly3 S3 W3 ms3 md3 _ _ HC); cbn [ms_mem ms_regs ms_resv ms_svc_pending
        ms_rom ms_fregs ms_fcsr mkst]; [exact Em1 | reflexivity | reflexivity | reflexivity | reflexivity
        | reflexivity | exact Hregs | nr_md | nr_md]. }
    split; [exact (nr_at_same W3 ms3 _ _ _ HFD Em1)|].
    split; [exact (nr_gnl_same cx W3 ms3 _ j HGN Em1)|].
    split; [rewrite Q1; reflexivity|].
    split; [rewrite Q10; exact E32|].
    split; [rewrite Q11; exact E26|].
    rewrite Q12. reflexivity.
  - unfold NT_rv2_ra, AF_nl_talk. lia.
  - reflexivity.
  - intros ly2 S2 W2 ms2 md2 HJ2 HFR2 HR2.
    refine (K _ ly2 S2 W2 ms2 md2 HJ2 HFR2 _ HR2).
    pose proof HR2 as (_ & _ & _ & HCS & _).
    assert (PRS : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr (ms_regs ms2) r = getr (ms_regs ms1) r).
    { intros r Hr. rewrite <- (Z_to_bv_bv_unsigned 5 r). apply HCS. exact Hr. }
    unfold nr_k3. rewrite !PRS by nr_cs. rewrite !Hregs by (unfold nr_keep; cbn; tauto).
    exact (conj R19 (conj R20 R22)).
Qed.

(* ==========================================================================
   17. The receive loop, by induction on the chunk loop's fuel, and the phase
   ========================================================================== *)

Lemma nr_chunks : forall f j cx fp k2 ly3 S3 W3 ms3 md3,
  nt_base SK B cx -> NRJ cx fp k2 ly3 S3 W3 (ms_mem ms3) md3 -> frames S3 = (NT_CID, fp) :: frames (n_Sc cx) ->
  nr_next_inv j f cx fp k2 ly3 S3 W3 ms3 md3 -> SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  induction f as [|f IHf]; intros j cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR HI;
    pose proof HI as (_ & _ & _ & _ & _ & HCL & Hfu);
    apply (nr_next_step j _ cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR HI);
    intros regs0 ly2 S2 W2 ms2 md2 HJ2 HFR2 HK3 HR;
    apply (nr_after2 j _ regs0 cx fp k2 ly2 S2 W2 ms2 md2 HB HJ2 HFR2 HR HK3 HCL Hfu);
    intros f' c rest ms' md' Hf HJ' HW.
  - discriminate Hf.
  - injection Hf as <-.
    apply (nr_walk_step j f c rest cx fp k2 ly2 S2 W2 ms' md' HB HJ' HFR2 HW).
    intros ms'' md'' HJ'' HN. exact (IHf (S j) cx fp k2 ly2 S2 W2 ms'' md'' HB HJ'' HFR2 HN).
Qed.

Lemma nr_recv_w : nt_from SK B POST (nt_recv_inv B).
Proof.
  intros cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR HI.
  apply (nr_first cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR HI).
  intros regs0 ly2 S2 W2 ms2 md2 HJ2 HFR2 HR.
  apply (nr_after1 (k_next (n_K0 cx)) (S (length (nr_cs cx))) regs0 cx fp k2 ly2 S2 W2 ms2 md2 HB HJ2 HFR2 HR);
    [reflexivity | apply nr_fuel_start |].
  intros f' c rest ms' md' Hf HJ' HW. injection Hf as <-.
  apply (nr_walk_step (k_next (n_K0 cx)) (length (nr_cs cx)) c rest cx fp k2 ly2 S2 W2 ms' md' HB HJ' HFR2 HW).
  intros ms'' md'' HJ'' HN.
  exact (nr_chunks (length (nr_cs cx)) (S (k_next (n_K0 cx))) cx fp k2 ly2 S2 W2 ms'' md'' HB HJ'' HFR2 HN).
Qed.

End w.

(* THE RECEIVE PHASE: from NT_mf0_ra (+0x1ec), the walk reaches the attribute phase's cut NT_attr at the first
   RTM_NEWLINK, or the exit phase's cut NT_exit. *)
Theorem nt_recv : forall POST,
  nt_from SK B POST (nt_attr_inv B) -> nt_from SK B POST (nt_exit_inv B) -> nt_from SK B POST (nt_recv_inv B).
Proof. intros POST HA HE. exact (nr_recv_w POST HA HE). Qed.

End b.
End a.

About nt_recv.
Print Assumptions nt_recv.
