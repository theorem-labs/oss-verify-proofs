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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/fuzz_recv_entry.v, with its module names changed; 1450 of its 1521 lines of code are new or changed and 654 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the walk of kernel (fuzz_link.asan 0x83d30): the FRAME of the cut invariant
   (kernel_defs.v `kat`), which every phase shares (the phases' brief
   link-a/plan/kernel-lanes.md (internal record, sha256 18c8d69749d5)).

   THE LEMMA `kat_frame`: after a run or a call that changes memory only at a set X of bytes, every part of kat
   holds at the new state with the same F shadow bytes, cursor advance and g_nl state, when
   - X meets no byte kat reads (`kX_miss`: the 13 saved words [sp - 104, sp), the kept spill slots, F's header
     words and its flag word, the positions of F's shadow bytes, the cursor's 16 bytes, g_nl, long_alias), and
   - every byte of X is one kernel may write (`kX_in`: its write set kE, a byte of its side frame F or of F's
     shadow, or a byte of kernel's window [sp - K, sp)). So kkept's akept moves by LinkWalkSide.v akept_step and
     arodata_okP moves because no byte of X is read-only (`kX_not_ro`: kE by apre's last conjunct, F by YCbq.v
     frm_img and LinkWalkPi.v frm_off_imgP, F's shadow and the window by their height).
   Each part of kat moves by its own lemma (`ksaved_frame` .. `kla_frame`), so a phase that writes the cursor,
   g_nl or F's shadow moves the other parts with them and states its own; `kat_reframe` takes the new F shadow,
   slots and cursor as given.

   THE PIECES of X: inside F between its header and its flag word (w1, w2 and parts of them: a put, a
   checked_memset or a checked_memcpy into a buffer), inside a callee's window [s1 - ESTACK, s1), inside the
   spill slots [s1 + lo, s1 + hi) the kept slots avoid (`kX_miss_F`, `kX_miss_win`, `kX_miss_sl`, `kX_in_F`,
   `kX_in_win`, `kX_in_sl`), and their unions (`kX_miss_or`, `kX_miss_mono`); the named corollaries
   `kat_frame_w2`, `kat_frame_w2s` (w2 and the window), `kat_frame_w1`, `kat_frame_w1s`, `kat_frame_sl` and
   `kat_frame_0` (no write: the same memory).

   THE SEPARATIONS: every byte of the read set kernel_ard lies in [0, 2 ^ 47), outside kernel's window
   (`kn_ard_bound`) and outside F (`kn_ard_not_F`); every byte of kernel_ard or kE is outside F, F's shadow and
   F's flag byte (`kn_ard_not_side`: LinkWalkShadow.v akb_not_side; F is not a caller frame by kjbk).

   THE OTHER LANES' KIT LEMMAS, kept here once: kernel_disp.v's (kdp_*: `kn_akb`, `kn_rd_facts`,
   `kn_sp1`, `kn_spill_wr`, `kn_denot_sh`, ...), kernel_msg0_kit.v's (km_*: `kn_ard_loc`, `kn_apre`,
   the read set's shadow facts at a cut `kn_rd_saddr` / `kn_cursor_ra` / `kn_input_at`, `kn_kat_move_X`, ...),
   the exit phase's `kn_writable_of_view` with the carry `kn_wr_keep` / `kn_awrange_keep`, and w1 / w2 addressable
   from F's shadow (`kn_w1_ra`, `kn_w2_ra`).

   Proves no function (kind: invariant lemma of kernel's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import PcapImgEnd.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkNlw LinkWalkPi LinkWalkSide LinkWalkShadow LinkWalkCall.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro kernel_c kernel_img kernel_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- byte views across a step ---- *)

Lemma kk_rdword_agree : forall (rd rd' : reader) a,
  (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd' a = rdword rd a.
Proof.
  intros rd rd' a H. unfold rdword.
  pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
  rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.

(* presence kept, between two worlds, is the restricted memories' growth *)
Lemma kk_grows_of_apresent : forall (H H' : word -> bool) (m m' : word -> option byte),
  (forall a, apresent H m a -> apresent H' m' a) -> mem_grows (mrestrict H m) (mrestrict H' m').
Proof.
  intros H H' m m' Hp x Hx. unfold mrestrict in *.
  destruct (H x) eqn:Hh; [exfalso; exact (Hx eq_refl)|].
  destruct (m x) as [b|] eqn:Hm; [|exfalso; exact (Hx eq_refl)].
  assert (Ex : Z_to_bv 64 (bv_unsigned x) = x) by apply Z_to_bv_bv_unsigned.
  destruct (Hp (bv_unsigned x)) as (Hh' & b' & Hb').
  { unfold apresent. rewrite Ex. split; [exact Hh | exists b; exact Hm]. }
  rewrite Ex in Hh', Hb'. rewrite Hh', Hb'. discriminate.
Qed.

Section v.
Variable segs : list Segment.

Lemma kk_abytes_keep : forall (H H' : word -> bool) (m m' : word -> option byte) a bs,
  (forall i, 0 <= i < Z.of_nat (length bs) -> aview segs H' m' (a + i) = aview segs H m (a + i)) ->
  abytes segs (mrestrict H m) a bs -> abytes segs (mrestrict H' m') a bs.
Proof.
  intros H H' m m' a bs Hk (H0 & H1 & H2). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite (mbyte_of_aview segs H H' m m' (a + Z.of_nat i)) by (apply Hk; lia). exact (H2 i Hi).
Qed.

Lemma kk_au8arr_keep : forall (H H' : word -> bool) (m m' : word -> option byte) a bs,
  (forall i, 0 <= i < Z.of_nat (length bs) -> aview segs H' m' (a + i) = aview segs H m (a + i)) ->
  mem_grows (mrestrict H m) (mrestrict H' m') ->
  au8arr segs (mrestrict H m) a bs -> au8arr segs (mrestrict H' m') a bs.
Proof.
  intros H H' m m' a bs Hk Hg (Hb & Hw). split; [exact (kk_abytes_keep H H' m m' a bs Hk Hb)|].
  intros i Hi. exact (writable_at_grows segs _ _ _ Hg (Hw i Hi)).
Qed.

Lemma kk_nlw_present_grows : forall (m m' : word -> option byte) w,
  mem_grows m m' -> nlw_present segs m w -> nlw_present segs m' w.
Proof.
  intros m m' w Hg H i Hi. destruct (H i Hi) as ((b & Hb) & Hw).
  split; [|exact (writable_at_grows segs m m' _ Hg Hw)].
  unfold mbyte in *.
  destruct (m' (Z_to_bv 64 (w + i))) as [b'|] eqn:E'; [exists b'; reflexivity|].
  destruct (m (Z_to_bv 64 (w + i))) as [b0|] eqn:E.
  - exfalso. apply (Hg (Z_to_bv 64 (w + i))); [rewrite E; discriminate | exact E'].
  - exists b. exact Hb.
Qed.
End v.

(* ---- the spill slots a lemma may take, checked by computation (`reflexivity`) ---- *)

(* every slot inside [s1, s1 + 0xf8): below the saved words *)
Definition kslots_okb (sl : list (Z * Z)) : bool := forallb (fun ov => (0 <=? fst ov) && (fst ov <=? 0xf0)) sl.
Lemma kslots_okb_spec : forall sl, kslots_okb sl = true -> forall ov, In ov sl -> 0 <= fst ov <= 0xf0.
Proof.
  intros sl H ov Hin. unfold kslots_okb in H. rewrite forallb_forall in H. specialize (H ov Hin).
  apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

(* every slot outside [s1 + lo, s1 + hi) *)
Definition kslots_avoidb (lo hi : Z) (sl : list (Z * Z)) : bool :=
  forallb (fun ov => (fst ov + 8 <=? lo) || (hi <=? fst ov)) sl.
Lemma kslots_avoidb_spec : forall lo hi sl, kslots_avoidb lo hi sl = true ->
  forall ov, In ov sl -> fst ov + 8 <= lo \/ hi <= fst ov.
Proof.
  intros lo hi sl H ov Hin. unfold kslots_avoidb in H. rewrite forallb_forall in H. specialize (H ov Hin).
  apply orb_true_iff in H as [H|H]; [left; apply Z.leb_le; exact H | right; apply Z.leb_le; exact H].
Qed.

(* F's shadow bytes of every cut fit in F's shadow (2048 bytes) *)
Lemma kfsh_fits : forall s1v s2v r, (length (kfsh s1v s2v r) <= 2048)%nat.
Proof. intros. rewrite kfsh_length. lia. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Abbreviation SEGS := (pa_segs).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis TB : AF0m.PcapSyms B.     (* AF0m.v; discharged at the frame's B by AD2l.PcapB_syms *)

(* ---- the bytes a step may change, and the bytes kat reads ---- *)

(* a byte kernel may write: its write set, a byte of F or of F's shadow, a byte of its window [sp - K, sp) *)
Definition kX_in (cx : kcx) (fpos a : Z) : Prop :=
  kE cx a \/ (kF cx fpos <= a < kF cx fpos + fs_frame_bytes KN_CID) \/
  (kFSH cx fpos <= a < kFSH cx fpos + fs_frame_bytes KN_CID / 8) \/ (ksp cx - KERNEL_AK <= a < ksp cx).

(* X meets none of the bytes kat reads: the saved words, the slots sl (each inside [s1, s1 + 0xf8)), F's header
   and flag word, the first n shadow bytes of F, the cursor, g_nl, long_alias *)
Definition kX_miss (cx : kcx) (fpos : Z) (sl : list (Z * Z)) (n : Z) (X : Z -> Prop) : Prop :=
  (forall a, ksp cx - 104 <= a < ksp cx -> ~ X a) /\
  (forall ov, In ov sl -> 0 <= fst ov <= 0xf0 /\
     (forall a, ksp1 cx + fst ov <= a < ksp1 cx + fst ov + 8 -> ~ X a)) /\
  (forall a, kF cx fpos <= a < kF cx fpos + 24 -> ~ X a) /\
  (forall a, kF cx fpos + fs_frame_bytes KN_CID - 8 <= a < kF cx fpos + fs_frame_bytes KN_CID -> ~ X a) /\
  (forall a, kFSH cx fpos <= a < kFSH cx fpos + n -> ~ X a) /\
  (forall a, ka0 cx <= a < ka0 cx + 16 -> ~ X a) /\
  (forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> ~ X a) /\
  (forall a, LA_LONG_ALIAS <= a < LA_LONG_ALIAS + LONG_ALIAS_SIZE -> ~ X a).

(* ---- the call's window and F ---- *)

Lemma kn_base_facts : forall cx, kbase SK B cx ->
  alloc_ceiling + KERNEL_AK <= ksp cx <= 2 ^ 47 /\ ksp cx - 384 < ksp1 cx <= ksp cx - 352 /\
  alloc_ceiling <= ly_stk_lo (k_lyc cx) /\ ly_stk_hi (k_lyc cx) <= 2 ^ 47.
Proof.
  intros cx HB.
  pose proof HB as HB'. unfold kbase in HB'. destruct HB' as (HPRE & _).
  pose proof HPRE as (HJ0 & _ & _ & _ & _ & _ & _ & _ & Hwlo & Hwhi & _).
  pose proof HJ0 as (HSTK0 & HXO0 & _).
  pose proof HJ0 as HROW. eapply ajournal_gx_row in HROW. destruct HROW as (Hrow1 & Hrow2 & Hrow3 & Hrow4).
  assert (HKA : KERNEL_AK = 4640) by reflexivity.
  change (spZ (k_regs cx)) with (ksp cx) in Hwlo, Hwhi.
  assert (Hsp : alloc_ceiling + KERNEL_AK <= ksp cx <= 2 ^ 47) by lia.
  split; [exact Hsp|]. split; [|split; [exact Hrow1 | exact Hrow2]].
  unfold ksp1, ksp1_of, KN_MFRAME. lia.
Qed.

(* F, from kjbk's witness of the state just after frame_alloc_8 *)
Lemma kn_F_facts : forall cx fpos k2 ly3 S3 md3, kjbk B cx fpos k2 ly3 S3 md3 ->
  4096 <= kF cx fpos /\ kF cx fpos + fs_frame_bytes KN_CID <= alloc_ceiling /\
  in_app (kF cx fpos) (fs_frame_bytes KN_CID) /\ kF cx fpos mod 64 = 0 /\
  off_img (kF cx fpos) (fs_frame_bytes KN_CID) /\
  (forall a, kF cx fpos <= a < kF cx fpos + fs_frame_bytes KN_CID -> ~ in_img SEGS a) /\
  0 <= fpos < fs_frames KN_CID.
Proof.
  intros cx fpos k2 ly3 S3 md3 (_ & _ & _ & _ & (S1 & W1 & mem1 & md1 & HAR & Hfr & _) & _).
  assert (Hin : In (KN_CID, fpos) (frames S1)) by (rewrite Hfr; left; reflexivity).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR Hin) as (H4 & Hc & Happ).
  destruct (frame_al64 SEGS B _ _ _ _ _ _ _ HAR Hin) as (Ha64 & _).
  pose proof (frm_off_imgP B _ _ _ _ _ _ _ HAR Hin) as Hoff.
  assert (Hpos : 0 <= fpos < fs_frames KN_CID).
  { pose proof (proj1 HAR) as HARm.
    match type of HARm with ARm ?B' ?ly ?S ?rd =>
      first [ destruct (frame_facts B' ly S rd KN_CID fpos HARm Hin) as (_ & Hp & _); exact Hp
            | destruct (frame_facts SEGS B' ly S rd KN_CID fpos HARm Hin) as (_ & Hp & _); exact Hp ] end. }
  unfold kF. refine (conj H4 (conj Hc (conj Happ (conj Ha64 (conj Hoff (conj _ Hpos)))))).
  intros a Ha. exact (frm_img SEGS B LAWS _ _ _ _ _ _ _ a HAR Hin Ha).
Qed.

(* every byte of the read set lies in [0, 2 ^ 47) and outside kernel's window *)
Lemma kn_ard_bound : forall cx a, kbase SK B cx -> kernel_ard SEGS (k_regs cx) (km0 cx) a ->
  0 <= a < 2 ^ 47 /\ ~ (ksp cx - KERNEL_AK <= a < ksp cx).
Proof.
  intros cx a HB Hrd.
  pose proof HB as HB'. unfold kbase in HB'. destruct HB' as (HPRE & HRD & _).
  pose proof (HRD a Hrd) as Hakb. clear HRD Hrd.
  pose proof HPRE as (HJ0 & _).
  pose proof HJ0 as (_ & _ & (memS0 & HJi0 & _) & _). pose proof HJi0 as (HAR0 & _).
  pose proof HJ0 as HROW. eapply ajournal_gx_row in HROW. destruct HROW as (Hrow1 & Hrow2 & _ & _).
  destruct (kn_base_facts cx HB) as (Hsp & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HKA : KERNEL_AK = 4640) by reflexivity.
  destruct Hakb as [(H1 & H2) | [(b & m & Hbm & Hr) | [(Hi & _ & _) | (cid & pos & Hinc & Hr)]]].
  - split; [lia | exact H2].
  - destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR0 Hbm) as (_ & Hb4096 & Hbceil & _). lia.
  - pose proof (pa_segs_low a Hi). lia.
  - destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR0 Hinc) as (Hf4 & Hfc & _).
    pose proof (fs_frame_bytes_nonneg cid). unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr. lia.
Qed.

(* every byte of the read set lies outside F *)
Lemma kn_ard_not_F : forall cx fpos k2 ly3 S3 md3 a,
  kbase SK B cx -> kjbk B cx fpos k2 ly3 S3 md3 -> kernel_ard SEGS (k_regs cx) (km0 cx) a ->
  ~ (kF cx fpos <= a < kF cx fpos + fs_frame_bytes KN_CID).
Proof.
  intros cx fpos k2 ly3 S3 md3 a HB HJB Hrd Ha.
  pose proof HB as HB'. unfold kbase in HB'. destruct HB' as (HPRE & HRD & _).
  pose proof (HRD a Hrd) as Hakb. clear HRD Hrd.
  pose proof HPRE as (HJ0 & _).
  pose proof HJ0 as HROW. eapply ajournal_gx_row in HROW. destruct HROW as (Hrow1 & _ & _ & _).
  pose proof HJB as (_ & _ & _ & _ & (S1 & W1 & mem1 & md1 & HAR1 & Hfr1 & Hbl1) & _).
  assert (Hin : In (KN_CID, fpos) (frames S1)) by (rewrite Hfr1; left; reflexivity).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR1 Hin) as (H4 & Hc & _).
  unfold kF in Ha.
  destruct Hakb as [(H1 & _) | [(b & m & Hbm & Hr) | [(Hi & _ & _) | (cid & pos & Hinc & Hr)]]].
  - lia.
  - rewrite <- Hbl1 in Hbm.
    pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR1 Hbm Hin) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. destruct Hd as [Hd|Hd]; lia.
  - exact (frm_img SEGS B LAWS _ _ _ _ _ _ _ a HAR1 Hin Ha Hi).
  - destruct (in_split _ _ Hinc) as (l2 & l3 & Hl).
    assert (Hfr' : frames S1 = [] ++ (KN_CID, fpos) :: l2 ++ (cid, pos) :: l3) by (rewrite Hfr1, Hl; reflexivity).
    pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ _ _ _ _ _ HAR1 Hfr') as Hd.
    unfold zdisjoint, frame_rng in Hd. unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hd, Hr.
    destruct Hd as [Hd|Hd]; lia.
Qed.

(* the write set lies in the read set *)
Lemma kn_kE_ard : forall cx a, kE cx a -> kernel_ard SEGS (k_regs cx) (km0 cx) a.
Proof.
  intros cx a (r & Hin & Hr). unfold kernel_awr in Hin. cbn [In] in Hin.
  unfold kernel_ard.
  destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr.
  - right; right; left. unfold NK_CHUNK, NK_OPEN, NK_SIZE in *. lia.
  - do 9 right. left. exact Hr.
  - left. exact Hr.
Qed.

(* THE SEPARATION OF THE READ AND WRITE SETS FROM F: no byte of kernel_ard or kE is a byte of F, of F's shadow
   or F's flag byte (LinkWalkShadow.v akb_not_side over kbase's akb; F is not a caller frame by kjbk) *)
Lemma kn_ard_not_side : forall cx fpos k2 ly3 S3 md3 a,
  kbase SK B cx -> kjbk B cx fpos k2 ly3 S3 md3 ->
  kernel_ard SEGS (k_regs cx) (km0 cx) a \/ kE cx a -> ~ aside_rng (k_lyc cx) KN_CID fpos a.
Proof.
  intros cx fpos k2 ly3 S3 md3 a HB HJB Ha.
  assert (Hrd : kernel_ard SEGS (k_regs cx) (km0 cx) a) by (destruct Ha as [H|H]; [exact H | exact (kn_kE_ard cx a H)]).
  pose proof HB as HB'. unfold kbase in HB'. destruct HB' as (HPRE & HRD & _).
  pose proof HPRE as (HJ0 & _).
  pose proof HJB as (_ & _ & _ & Hnin & _).
  destruct (kn_F_facts cx fpos k2 ly3 S3 md3 HJB) as (_ & _ & _ & _ & _ & _ & Hpos).
  exact (akb_not_side SK SEGS B pa_img_range
    (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx) (k_mem0 cx)
    (k_md0 cx) (k_own cx) (k_lyc cx) (k_Sc cx) (k_W cx) (k_memc cx) (k_mdc cx) (k_k cx)
    (ksp cx - KERNEL_AK) (ksp cx) KN_CID fpos a HJ0 ltac:(unfold KN_CID; lia) Hpos Hnin (HRD a Hrd)).
Qed.

(* ---- no byte kernel may write is read-only ---- *)

Lemma kn_ro_low : forall a, in_roP SEGS PCAP_RLO PCAP_RHI a -> 0 <= a < 0x7fff8000.
Proof.
  intros a [(s & Hs & _ & Hr) | Hr].
  - pose proof (pa_segs_low a (ex_intro _ s (conj Hs Hr))) as Hl.
    pose proof asan_consts as (_ & _ & _ & _ & C5). rewrite C5 in Hl. exact Hl.
  - unfold PCAP_RLO, PCAP_RHI in Hr. lia.
Qed.

Lemma kX_not_ro : forall cx fpos k2 ly3 S3 md3 a,
  kbase SK B cx -> kjbk B cx fpos k2 ly3 S3 md3 -> kX_in cx fpos a -> ~ in_roP SEGS PCAP_RLO PCAP_RHI a.
Proof.
  intros cx fpos k2 ly3 S3 md3 a HB HJB Ha Hro.
  pose proof (kn_ro_low a Hro) as Hlow.
  destruct Ha as [H1 | [H1 | [H1 | H1]]].
  - pose proof HB as HB'. unfold kbase in HB'. destruct HB' as (HPRE & _).
    pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HWRO).
    exact (HWRO a H1 Hro).
  - destruct (kn_F_facts cx fpos k2 ly3 S3 md3 HJB) as (HF4 & HFc & _ & _ & Hoff & Himg & _).
    destruct Hro as [(s & Hs & _ & Hr) | Hr].
    + exact (Himg a H1 (ex_intro _ s (conj Hs Hr))).
    + assert (Hfb : fs_frame_bytes KN_CID = 16384) by reflexivity.
      unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, PCAP_RLO, PCAP_RHI in Hoff, Hr.
      destruct Hoff as [Ho|Ho]; lia.
  - destruct (kn_F_facts cx fpos k2 ly3 S3 md3 HJB) as (HF4 & _).
    unfold kFSH, shadow_of_addr, SHADOW_OFF in H1. lia.
  - destruct (kn_base_facts cx HB) as (Hsp & _).
    pose proof asan_consts as ((C1a & _) & _). lia.
Qed.

(* ---- each part of kat across a step that changes memory only at X ---- *)

Lemma ksaved_frame : forall (X : Z -> Prop) cx W3 ms3 W4 ms4,
  kbase SK B cx ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview SEGS (w_H W4) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, ksp cx - 104 <= a < ksp cx -> ~ X a) ->
  ksaved cx W3 ms3 -> ksaved cx W4 ms4.
Proof.
  intros X cx W3 ms3 W4 ms4 HB UN HM (Hra & Hsv).
  destruct (kn_base_facts cx HB) as (Hsp & _).
  pose proof asan_consts as ((C1a & _) & _).
  assert (HKA : KERNEL_AK = 4640) by reflexivity.
  assert (RW : forall a, ksp cx - 104 <= a -> a + 8 <= ksp cx ->
            rdword (aview SEGS (w_H W4) (ms_mem ms4)) a = rdword (aview SEGS (w_H W3) (ms_mem ms3)) a).
  { intros a H1 H2. apply kk_rdword_agree. intros i Hi. apply UN; [lia | apply HM; lia]. }
  split.
  - rewrite RW by lia. exact Hra.
  - intros j Hj. rewrite RW by lia. exact (Hsv j Hj).
Qed.

Lemma kframe_frame : forall (X : Z -> Prop) cx fpos live k2 ly3 S3 md3 W3 ms3 W4 ms4,
  kjbk B cx fpos k2 ly3 S3 md3 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview SEGS (w_H W4) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W4) (ms_mem ms4) a) ->
  (forall a, kF cx fpos <= a < kF cx fpos + 24 -> ~ X a) ->
  (forall a, kF cx fpos + fs_frame_bytes KN_CID - 8 <= a < kF cx fpos + fs_frame_bytes KN_CID -> ~ X a) ->
  kframe cx fpos live W3 ms3 -> kframe cx fpos live W4 ms4.
Proof.
  intros X cx fpos live k2 ly3 S3 md3 W3 ms3 W4 ms4 HJB UN HP M1 M2 (Hf0 & Hf8 & Hf16 & Hfl & Hp1 & Hp2).
  destruct (kn_F_facts cx fpos k2 ly3 S3 md3 HJB) as (HF4 & HFc & _).
  pose proof asan_consts as ((C1a & C1b) & _).
  assert (Hfb : fs_frame_bytes KN_CID = 16384) by reflexivity.
  assert (RW1 : forall a, kF cx fpos <= a -> a + 8 <= kF cx fpos + 24 ->
            rdword (aview SEGS (w_H W4) (ms_mem ms4)) a = rdword (aview SEGS (w_H W3) (ms_mem ms3)) a).
  { intros a H1 H2. apply kk_rdword_agree. intros i Hi. apply UN; [lia | apply M1; lia]. }
  assert (RW2 : rdword (aview SEGS (w_H W4) (ms_mem ms4)) (kF cx fpos + fs_frame_bytes KN_CID - 8) =
                rdword (aview SEGS (w_H W3) (ms_mem ms3)) (kF cx fpos + fs_frame_bytes KN_CID - 8)).
  { apply kk_rdword_agree. intros i Hi. apply UN; [lia | apply M2; lia]. }
  split; [rewrite RW1 by lia; exact Hf0|].
  split; [rewrite RW1 by lia; exact Hf8|].
  split; [rewrite RW1 by lia; exact Hf16|].
  split; [rewrite RW2; exact Hfl|].
  split; intros a Ha; [exact (HP a (Hp1 a Ha)) | exact (HP a (Hp2 a Ha))].
Qed.

Lemma kshadow_frame : forall (X : Z -> Prop) cx fpos sh k2 ly3 S3 md3 W3 ms3 W4 ms4,
  kjbk B cx fpos k2 ly3 S3 md3 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview SEGS (w_H W4) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (length sh <= 2048)%nat ->
  (forall a, kFSH cx fpos <= a < kFSH cx fpos + Z.of_nat (length sh) -> ~ X a) ->
  kshadow cx fpos W3 ms3 sh -> kshadow cx fpos W4 ms4 sh.
Proof.
  intros X cx fpos sh k2 ly3 S3 md3 W3 ms3 W4 ms4 HJB UN Hl M HSH i Hi.
  destruct (kn_F_facts cx fpos k2 ly3 S3 md3 HJB) as (HF4 & HFc & _).
  pose proof asan_consts as ((C1a & C1b) & _).
  assert (Hfb : fs_frame_bytes KN_CID = 16384) by reflexivity.
  rewrite UN; [exact (HSH i Hi) | | apply M; lia].
  unfold kFSH, shadow_of_addr, SHADOW_OFF. lia.
Qed.

Lemma kslots_frame : forall (X : Z -> Prop) cx sl sl' W3 ms3 W4 ms4,
  kbase SK B cx ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview SEGS (w_H W4) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  incl sl' sl ->
  (forall ov, In ov sl' -> 0 <= fst ov <= 0xf0 /\
     (forall a, ksp1 cx + fst ov <= a < ksp1 cx + fst ov + 8 -> ~ X a)) ->
  kslots_eq cx W3 ms3 sl -> kslots_eq cx W4 ms4 sl'.
Proof.
  intros X cx sl sl' W3 ms3 W4 ms4 HB UN Hinc M HSL.
  destruct (kn_base_facts cx HB) as (Hsp & Hs1 & _).
  pose proof asan_consts as ((C1a & _) & _).
  assert (HKA : KERNEL_AK = 4640) by reflexivity.
  unfold kslots_eq in HSL |- *. rewrite Forall_forall in HSL |- *. intros ov Hov.
  destruct (M ov Hov) as (Hb & Mx).
  rewrite <- (HSL ov (Hinc ov Hov)). apply kk_rdword_agree. intros i Hi. apply UN; [lia | apply Mx; lia].
Qed.

Lemma kjbk_md : forall cx fpos k2 ly3 S3 md3 md4,
  kjbk B cx fpos k2 ly3 S3 md3 -> m_fds md4 = m_fds md3 -> m_fs md4 = m_fs md3 -> kjbk B cx fpos k2 ly3 S3 md4.
Proof.
  intros cx fpos k2 ly3 S3 md3 md4 (J1 & J2 & J3 & J4 & J5 & J6 & J7) Hfds Hfs. unfold kjbk.
  refine (conj J1 (conj J2 (conj J3 (conj J4 (conj J5 (conj _ _)))))); [rewrite Hfds; exact J6 | rewrite Hfs; exact J7].
Qed.

(* a call's model keeps the descriptors and the file system *)
Lemma kn_sbm_fds_fs : forall md3 md4, same_but_materialized md3 md4 -> m_fds md4 = m_fds md3 /\ m_fs md4 = m_fs md3.
Proof.
  intros md3 md4 H. unfold same_but_materialized in H. rewrite H. exact (wvb_fds_fs _ _ _).
Qed.

Lemma kkept_frame : forall (X : Z -> Prop) cx fpos k2 ly3 S3 md3 W3 ms3 W4 ms4,
  kbase SK B cx -> kjbk B cx fpos k2 ly3 S3 md3 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview SEGS (w_H W4) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W4) (ms_mem ms4) a) ->
  (forall a, X a -> kX_in cx fpos a) ->
  kkept B cx fpos W3 ms3 -> kkept B cx fpos W4 ms4.
Proof.
  intros X cx fpos k2 ly3 S3 md3 W3 ms3 W4 ms4 HB HJB UN HP HXin (HAK & HROD).
  pose proof HB as HB'. unfold kbase in HB'. destruct HB' as (HPRE & _).
  pose proof HPRE as (HJ0 & _).
  pose proof HJ0 as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (HAR0 & _).
  destruct (kn_base_facts cx HB) as (Hsp & _).
  pose proof asan_consts as ((C1a & C1b) & _).
  assert (HKA : KERNEL_AK = 4640) by reflexivity.
  split.
  - apply (akept_step SK SEGS B LAWS pa_segs_low (k_lyc cx) (k_Sc cx) (k_W cx) (k_memc cx) (k_mdc cx)
      W3 (ms_mem ms3) W4 (ms_mem ms4) (ksp cx - KERNEL_AK) (ksp cx)
      (fun a => kE cx a \/ aside_rng (k_lyc cx) KN_CID fpos a)
      (fun a => kE cx a \/ aside_rng (k_lyc cx) KN_CID fpos a) X HAR0).
    + lia.
    + lia.
    + exact HAK.
    + exact UN.
    + intros a _ Hp. exact (HP a Hp).
    + intros a Ha. exact Ha.
    + intros a Ha. cbv beta. unfold aside_rng, in_zr, frame_rng. cbn [fst snd].
      destruct (HXin a Ha) as [H1 | [H1 | [H1 | H1]]].
      * left; left. exact H1.
      * left; right; left. exact H1.
      * left; right; right; left. unfold kFSH, shadow_of_addr in H1. unfold shadow_addr. exact H1.
      * right. exact H1.
  - intros a Hro Hno Her.
    pose proof (kn_ro_low a Hro) as Hlow.
    rewrite UN; [exact (HROD a Hro Hno Her) | lia |].
    intros HXa. exact (kX_not_ro cx fpos k2 ly3 S3 md3 a HB HJB (HXin a HXa) Hro).
Qed.

Lemma kcursor_frame : forall (X : Z -> Prop) cx adv W3 ms3 W4 ms4,
  kbase SK B cx ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview SEGS (w_H W4) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W4) (ms_mem ms4) a) ->
  (forall a, ka0 cx <= a < ka0 cx + 16 -> ~ X a) ->
  kcursor cx W3 ms3 adv -> kcursor cx W4 ms4 adv.
Proof.
  intros X cx adv W3 ms3 W4 ms4 HB UN HP M (Hadv & Hc0 & Hc8 & Hcw).
  pose proof (kk_grows_of_apresent _ _ _ _ HP) as HG.
  assert (Hb : 0 <= ka0 cx /\ ka0 cx + 16 <= 2 ^ 47).
  { destruct (kn_ard_bound cx (ka0 cx) HB ltac:(unfold kernel_ard; left; unfold ka0; lia)) as (H0 & _).
    destruct (kn_ard_bound cx (ka0 cx + 15) HB ltac:(unfold kernel_ard; left; unfold ka0; lia)) as (H1 & _).
    lia. }
  assert (CB : forall k, 0 <= k < 16 ->
            aview SEGS (w_H W4) (ms_mem ms4) (ka0 cx + k) = aview SEGS (w_H W3) (ms_mem ms3) (ka0 cx + k)).
  { intros k Hk. apply UN; [lia | apply M; lia]. }
  split; [exact Hadv|]. split; [|split].
  - apply (val_mem_moved SEGS (w_H W3) (w_H W4) (ms_mem ms3) (ms_mem ms4) (ka0 cx) (ka0 cx) 8 (k_wp cx + adv));
      [|exact Hc0].
    intros k Hk. apply CB. lia.
  - apply (val_mem_moved SEGS (w_H W3) (w_H W4) (ms_mem ms3) (ms_mem ms4) (ka0 cx + 8) (ka0 cx + 8) 8
             (k_wn cx - adv)); [|exact Hc8].
    intros k Hk. replace (ka0 cx + 8 + k) with (ka0 cx + (8 + k)) by lia. apply CB. lia.
  - intros i Hi. exact (writable_at_grows SEGS _ _ _ HG (Hcw i Hi)).
Qed.

Lemma kgnl_frame : forall (X : Z -> Prop) cx g W3 ms3 W4 ms4,
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview SEGS (w_H W4) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W4) (ms_mem ms4) a) ->
  (forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> ~ X a) ->
  kgnl_at cx W3 ms3 g -> kgnl_at cx W4 ms4 g.
Proof.
  intros X cx g W3 ms3 W4 ms4 UN HP M HGNL.
  pose proof (kk_grows_of_apresent _ _ _ _ HP) as HG.
  assert (GB : forall bs : list byte, Z.of_nat (length bs) = NK_SIZE -> forall i, 0 <= i < Z.of_nat (length bs) ->
            aview SEGS (w_H W4) (ms_mem ms4) (LA_G_NL + i) = aview SEGS (w_H W3) (ms_mem ms3) (LA_G_NL + i)).
  { intros bs Hl i Hi. rewrite Hl in Hi. apply UN; [unfold LA_G_NL, NK_SIZE in *; lia | apply M; lia]. }
  destruct g as [j|]; cbn [kgnl_at] in HGNL |- *.
  - destruct HGNL as (kbs3 & (Hau & Hl) & Hk). exists kbs3.
    split; [split; [exact (kk_au8arr_keep SEGS _ _ _ _ _ _ (GB kbs3 Hl) HG Hau) | exact Hl] | exact Hk].
  - destruct HGNL as (Hau & Hl). split; [exact (kk_au8arr_keep SEGS _ _ _ _ _ _ (GB _ Hl) HG Hau) | exact Hl].
Qed.

Lemma kla_frame : forall (X : Z -> Prop) W3 ms3 W4 ms4,
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview SEGS (w_H W4) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W4) (ms_mem ms4) a) ->
  (forall a, LA_LONG_ALIAS <= a < LA_LONG_ALIAS + LONG_ALIAS_SIZE -> ~ X a) ->
  kla_at W3 ms3 -> kla_at W4 ms4.
Proof.
  intros X W3 ms3 W4 ms4 UN HP M (la3 & Hau & Hl).
  pose proof (kk_grows_of_apresent _ _ _ _ HP) as HG.
  exists la3. split; [|exact Hl].
  apply (kk_au8arr_keep SEGS (w_H W3) (w_H W4) (ms_mem ms3) (ms_mem ms4) LA_LONG_ALIAS (la3 ++ [zb 0]));
    [|exact HG | exact Hau].
  intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  apply UN; [unfold LA_LONG_ALIAS; lia | apply M; unfold LONG_ALIAS_SIZE; lia].
Qed.

(* ---- THE FRAME OF THE CUT INVARIANT ---- *)
Lemma kat_frame : forall (X : Z -> Prop) cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 pc' rl' sl' W4 ms4 md4,
  kbase SK B cx ->
  kat B cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 ->
  kms pc' ms4 -> kregs0 cx ms4 -> kregs_eq ms4 rl' -> incl sl' sl -> (length sh <= 2048)%nat ->
  m_fds md4 = m_fds md3 -> m_fs md4 = m_fs md3 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview SEGS (w_H W4) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W4) (ms_mem ms4) a) ->
  (forall a, X a -> kX_in cx fpos a) ->
  kX_miss cx fpos sl' (Z.of_nat (length sh)) X ->
  kat B cx fpos pc' rl' sl' sh live adv g k2 ly3 S3 W4 ms4 md4.
Proof.
  intros X cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 pc' rl' sl' W4 ms4 md4
    HB HK HMS HR0 HRL Hsl Hsh Hfds Hfs UN HP HXin HXm.
  destruct HXm as (Msv & Msl & Mhd & Mfl & Msh & Mcu & Mgn & Mla).
  destruct HK as (_ & _ & _ & HSAV & HFR & HSH & HSL & HJB & HKEPT & HCUR & HGNL & HLA).
  unfold kat.
  refine (conj HMS (conj HR0 (conj HRL (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))).
  - exact (ksaved_frame X cx W3 ms3 W4 ms4 HB UN Msv HSAV).
  - exact (kframe_frame X cx fpos live k2 ly3 S3 md3 W3 ms3 W4 ms4 HJB UN HP Mhd Mfl HFR).
  - exact (kshadow_frame X cx fpos sh k2 ly3 S3 md3 W3 ms3 W4 ms4 HJB UN Hsh Msh HSH).
  - exact (kslots_frame X cx sl sl' W3 ms3 W4 ms4 HB UN Hsl Msl HSL).
  - exact (kjbk_md cx fpos k2 ly3 S3 md3 md4 HJB Hfds Hfs).
  - exact (kkept_frame X cx fpos k2 ly3 S3 md3 W3 ms3 W4 ms4 HB HJB UN HP HXin HKEPT).
  - exact (kcursor_frame X cx adv W3 ms3 W4 ms4 HB UN HP Mcu HCUR).
  - exact (kgnl_frame X cx g W3 ms3 W4 ms4 UN HP Mgn HGNL).
  - exact (kla_frame X W3 ms3 W4 ms4 UN HP Mla HLA).
Qed.


(* ---- the pieces of X: inside F between its header and its flag word, a callee's window below s1, the spill
   slots, and their unions ---- *)

Lemma kX_in_F : forall cx fpos lo hi a, 0 <= lo -> hi <= fs_frame_bytes KN_CID ->
  kF cx fpos + lo <= a < kF cx fpos + hi -> kX_in cx fpos a.
Proof. intros cx fpos lo hi a H1 H2 Ha. right; left. lia. Qed.

Lemma kX_in_win : forall cx fpos a, kbase SK B cx -> ksp1 cx - ESTACK <= a < ksp1 cx -> kX_in cx fpos a.
Proof.
  intros cx fpos a HB Ha. destruct (kn_base_facts cx HB) as (Hsp & Hs1 & _).
  assert (HKA : KERNEL_AK = 4640) by reflexivity. right; right; right. unfold ESTACK in Ha. lia.
Qed.

Lemma kX_in_sl : forall cx fpos lo hi a, kbase SK B cx -> 0 <= lo -> hi <= 0xf8 ->
  ksp1 cx + lo <= a < ksp1 cx + hi -> kX_in cx fpos a.
Proof.
  intros cx fpos lo hi a HB H1 H2 Ha. destruct (kn_base_facts cx HB) as (Hsp & Hs1 & _).
  assert (HKA : KERNEL_AK = 4640) by reflexivity. right; right; right. lia.
Qed.

Lemma kX_miss_or : forall cx fpos sl n (X1 X2 : Z -> Prop),
  kX_miss cx fpos sl n X1 -> kX_miss cx fpos sl n X2 -> kX_miss cx fpos sl n (fun a => X1 a \/ X2 a).
Proof.
  intros cx fpos sl n X1 X2 (A1 & B1 & C1 & D1 & E1 & F1 & G1 & H1) (A2 & B2 & C2 & D2 & E2 & F2 & G2 & H2).
  split; [intros a Ha Hx; destruct Hx as [Hx|Hx]; [exact (A1 a Ha Hx) | exact (A2 a Ha Hx)]|].
  split.
  { intros ov Hov. destruct (B1 ov Hov) as (Hb & M1). destruct (B2 ov Hov) as (_ & M2).
    split; [exact Hb | intros a Ha Hx; destruct Hx as [Hx|Hx]; [exact (M1 a Ha Hx) | exact (M2 a Ha Hx)]]. }
  split; [intros a Ha Hx; destruct Hx as [Hx|Hx]; [exact (C1 a Ha Hx) | exact (C2 a Ha Hx)]|].
  split; [intros a Ha Hx; destruct Hx as [Hx|Hx]; [exact (D1 a Ha Hx) | exact (D2 a Ha Hx)]|].
  split; [intros a Ha Hx; destruct Hx as [Hx|Hx]; [exact (E1 a Ha Hx) | exact (E2 a Ha Hx)]|].
  split; [intros a Ha Hx; destruct Hx as [Hx|Hx]; [exact (F1 a Ha Hx) | exact (F2 a Ha Hx)]|].
  split; [intros a Ha Hx; destruct Hx as [Hx|Hx]; [exact (G1 a Ha Hx) | exact (G2 a Ha Hx)]|].
  intros a Ha Hx; destruct Hx as [Hx|Hx]; [exact (H1 a Ha Hx) | exact (H2 a Ha Hx)].
Qed.

Lemma kX_miss_mono : forall cx fpos sl n (X Y : Z -> Prop),
  (forall a, X a -> Y a) -> kX_miss cx fpos sl n Y -> kX_miss cx fpos sl n X.
Proof.
  intros cx fpos sl n X Y HXY (A & Bs & C & D & E & F & G & H).
  split; [intros a Ha Hx; exact (A a Ha (HXY a Hx))|].
  split.
  { intros ov Hov. destruct (Bs ov Hov) as (Hb & M).
    split; [exact Hb | intros a Ha Hx; exact (M a Ha (HXY a Hx))]. }
  split; [intros a Ha Hx; exact (C a Ha (HXY a Hx))|].
  split; [intros a Ha Hx; exact (D a Ha (HXY a Hx))|].
  split; [intros a Ha Hx; exact (E a Ha (HXY a Hx))|].
  split; [intros a Ha Hx; exact (F a Ha (HXY a Hx))|].
  split; [intros a Ha Hx; exact (G a Ha (HXY a Hx))|].
  intros a Ha Hx; exact (H a Ha (HXY a Hx)).
Qed.

(* X inside F, between its three header words and its flag word: w1, w2 and their parts *)
Lemma kX_miss_F : forall cx fpos k2 ly3 S3 md3 sl n lo hi (X : Z -> Prop),
  kbase SK B cx -> kjbk B cx fpos k2 ly3 S3 md3 -> kslots_okb sl = true -> n <= 2048 ->
  24 <= lo -> hi <= fs_frame_bytes KN_CID - 8 ->
  (forall a, X a -> kF cx fpos + lo <= a < kF cx fpos + hi) -> kX_miss cx fpos sl n X.
Proof.
  intros cx fpos k2 ly3 S3 md3 sl n lo hi X HB HJB Hsl Hn Hlo Hhi HX.
  destruct (kn_base_facts cx HB) as (Hsp & Hs1 & _).
  destruct (kn_F_facts cx fpos k2 ly3 S3 md3 HJB) as (HF4 & HFc & Happ & _).
  pose proof asan_consts as ((C1a & C1b) & _).
  assert (Hfb : fs_frame_bytes KN_CID = 16384) by reflexivity.
  assert (HKA : KERNEL_AK = 4640) by reflexivity.
  assert (RD : forall a, kernel_ard SEGS (k_regs cx) (km0 cx) a -> ~ X a).
  { intros a Hrd Hx. apply (kn_ard_not_F cx fpos k2 ly3 S3 md3 a HB HJB Hrd). specialize (HX a Hx). lia. }
  split; [intros a Ha Hx; specialize (HX a Hx); lia|].
  split.
  { intros ov Hov. pose proof (kslots_okb_spec sl Hsl ov Hov) as Hb.
    split; [exact Hb | intros a Ha Hx; specialize (HX a Hx); lia]. }
  split; [intros a Ha Hx; specialize (HX a Hx); lia|].
  split; [intros a Ha Hx; specialize (HX a Hx); lia|].
  split.
  { intros a Ha Hx. specialize (HX a Hx). rewrite Hfb in Happ.
    unfold kFSH, shadow_of_addr, SHADOW_OFF in Ha.
    apply (fshadow_not_app (kF cx fpos) 2048 (kF cx fpos) 16384 a); [lia | lia | exact Happ | lia | lia]. }
  split; [intros a Ha; apply RD; unfold kernel_ard; left; exact Ha|].
  split; [intros a Ha; apply RD; unfold kernel_ard; right; right; left; exact Ha|].
  intros a Ha; apply RD; unfold kernel_ard; do 9 right; left; exact Ha.
Qed.

(* X inside a callee's window [s1 - ESTACK, s1) (a checked_memset / checked_memcpy / meta_fill call from s1) *)
Lemma kX_miss_win : forall cx fpos k2 ly3 S3 md3 sl n (X : Z -> Prop),
  kbase SK B cx -> kjbk B cx fpos k2 ly3 S3 md3 -> kslots_okb sl = true -> n <= 2048 ->
  (forall a, X a -> ksp1 cx - ESTACK <= a < ksp1 cx) -> kX_miss cx fpos sl n X.
Proof.
  intros cx fpos k2 ly3 S3 md3 sl n X HB HJB Hsl Hn HX.
  destruct (kn_base_facts cx HB) as (Hsp & Hs1 & _).
  destruct (kn_F_facts cx fpos k2 ly3 S3 md3 HJB) as (HF4 & HFc & _).
  pose proof asan_consts as ((C1a & C1b) & _).
  assert (Hfb : fs_frame_bytes KN_CID = 16384) by reflexivity.
  assert (HKA : KERNEL_AK = 4640) by reflexivity.
  assert (RD : forall a, kernel_ard SEGS (k_regs cx) (km0 cx) a -> ~ X a).
  { intros a Hrd Hx. destruct (kn_ard_bound cx a HB Hrd) as (_ & Hw). apply Hw.
    specialize (HX a Hx). unfold ESTACK in HX. lia. }
  split; [intros a Ha Hx; specialize (HX a Hx); lia|].
  split.
  { intros ov Hov. pose proof (kslots_okb_spec sl Hsl ov Hov) as Hb.
    split; [exact Hb | intros a Ha Hx; specialize (HX a Hx); lia]. }
  split; [intros a Ha Hx; specialize (HX a Hx); unfold ESTACK in HX; lia|].
  split; [intros a Ha Hx; specialize (HX a Hx); unfold ESTACK in HX; lia|].
  split; [intros a Ha Hx; specialize (HX a Hx); unfold ESTACK in HX;
          unfold kFSH, shadow_of_addr, SHADOW_OFF in Ha; lia|].
  split; [intros a Ha; apply RD; unfold kernel_ard; left; exact Ha|].
  split; [intros a Ha; apply RD; unfold kernel_ard; right; right; left; exact Ha|].
  intros a Ha; apply RD; unfold kernel_ard; do 9 right; left; exact Ha.
Qed.

(* X inside the spill slots [s1 + lo, s1 + hi) that the kept slots avoid *)
Lemma kX_miss_sl : forall cx fpos k2 ly3 S3 md3 sl n lo hi (X : Z -> Prop),
  kbase SK B cx -> kjbk B cx fpos k2 ly3 S3 md3 -> kslots_okb sl = true -> kslots_avoidb lo hi sl = true ->
  n <= 2048 -> 0 <= lo -> hi <= 0xf8 ->
  (forall a, X a -> ksp1 cx + lo <= a < ksp1 cx + hi) -> kX_miss cx fpos sl n X.
Proof.
  intros cx fpos k2 ly3 S3 md3 sl n lo hi X HB HJB Hsl Hav Hn Hlo Hhi HX.
  destruct (kn_base_facts cx HB) as (Hsp & Hs1 & _).
  destruct (kn_F_facts cx fpos k2 ly3 S3 md3 HJB) as (HF4 & HFc & _).
  pose proof asan_consts as ((C1a & C1b) & _).
  assert (Hfb : fs_frame_bytes KN_CID = 16384) by reflexivity.
  assert (HKA : KERNEL_AK = 4640) by reflexivity.
  assert (RD : forall a, kernel_ard SEGS (k_regs cx) (km0 cx) a -> ~ X a).
  { intros a Hrd Hx. destruct (kn_ard_bound cx a HB Hrd) as (_ & Hw). apply Hw.
    specialize (HX a Hx). lia. }
  split; [intros a Ha Hx; specialize (HX a Hx); lia|].
  split.
  { intros ov Hov. pose proof (kslots_okb_spec sl Hsl ov Hov) as Hb.
    pose proof (kslots_avoidb_spec lo hi sl Hav ov Hov) as Hv.
    split; [exact Hb | intros a Ha Hx; specialize (HX a Hx); destruct Hv as [Hv|Hv]; lia]. }
  split; [intros a Ha Hx; specialize (HX a Hx); lia|].
  split; [intros a Ha Hx; specialize (HX a Hx); lia|].
  split; [intros a Ha Hx; specialize (HX a Hx); unfold kFSH, shadow_of_addr, SHADOW_OFF in Ha; lia|].
  split; [intros a Ha; apply RD; unfold kernel_ard; left; exact Ha|].
  split; [intros a Ha; apply RD; unfold kernel_ard; right; right; left; exact Ha|].
  intros a Ha; apply RD; unfold kernel_ard; do 9 right; left; exact Ha.
Qed.

(* ---- the corollaries ---- *)

(* X = [F + lo, F + hi) between F's header and its flag word *)
Lemma kat_frame_F : forall lo hi cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 pc' rl' sl' W4 ms4 md4,
  kbase SK B cx ->
  kat B cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 ->
  kms pc' ms4 -> kregs0 cx ms4 -> kregs_eq ms4 rl' -> incl sl' sl -> kslots_okb sl' = true ->
  (length sh <= 2048)%nat -> m_fds md4 = m_fds md3 -> m_fs md4 = m_fs md3 ->
  24 <= lo -> hi <= fs_frame_bytes KN_CID - 8 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (kF cx fpos + lo <= a < kF cx fpos + hi) ->
     aview SEGS (w_H W4) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W4) (ms_mem ms4) a) ->
  kat B cx fpos pc' rl' sl' sh live adv g k2 ly3 S3 W4 ms4 md4.
Proof.
  intros lo hi cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 pc' rl' sl' W4 ms4 md4
    HB HK HMS HR0 HRL Hsl Hok Hsh Hfds Hfs Hlo Hhi UN HP.
  pose proof HK as (_ & _ & _ & _ & _ & _ & _ & HJB & _).
  apply (kat_frame (fun a => kF cx fpos + lo <= a < kF cx fpos + hi) cx fpos pc rl sl sh live adv g k2 ly3 S3
           W3 ms3 md3 pc' rl' sl' W4 ms4 md4 HB HK HMS HR0 HRL Hsl Hsh Hfds Hfs UN HP).
  - intros a Ha. apply (kX_in_F cx fpos lo hi a); [lia | lia | exact Ha].
  - apply (kX_miss_F cx fpos k2 ly3 S3 md3 sl' _ lo hi); [exact HB | exact HJB | exact Hok | lia | exact Hlo | exact Hhi |].
    intros a Ha. exact Ha.
Qed.

(* X = [F + lo, F + hi) and a callee's window [s1 - ESTACK, s1) *)
Lemma kat_frame_Fs : forall lo hi cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 pc' rl' sl' W4 ms4 md4,
  kbase SK B cx ->
  kat B cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 ->
  kms pc' ms4 -> kregs0 cx ms4 -> kregs_eq ms4 rl' -> incl sl' sl -> kslots_okb sl' = true ->
  (length sh <= 2048)%nat -> m_fds md4 = m_fds md3 -> m_fs md4 = m_fs md3 ->
  24 <= lo -> hi <= fs_frame_bytes KN_CID - 8 ->
  (forall a, 0 <= a < 2 ^ 64 ->
     ~ ((kF cx fpos + lo <= a < kF cx fpos + hi) \/ (ksp1 cx - ESTACK <= a < ksp1 cx)) ->
     aview SEGS (w_H W4) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W4) (ms_mem ms4) a) ->
  kat B cx fpos pc' rl' sl' sh live adv g k2 ly3 S3 W4 ms4 md4.
Proof.
  intros lo hi cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 pc' rl' sl' W4 ms4 md4
    HB HK HMS HR0 HRL Hsl Hok Hsh Hfds Hfs Hlo Hhi UN HP.
  pose proof HK as (_ & _ & _ & _ & _ & _ & _ & HJB & _).
  apply (kat_frame (fun a => (kF cx fpos + lo <= a < kF cx fpos + hi) \/ (ksp1 cx - ESTACK <= a < ksp1 cx))
           cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 pc' rl' sl' W4 ms4 md4
           HB HK HMS HR0 HRL Hsl Hsh Hfds Hfs UN HP).
  - intros a Ha. destruct Ha as [Ha|Ha].
    + apply (kX_in_F cx fpos lo hi a); [lia | lia | exact Ha].
    + exact (kX_in_win cx fpos a HB Ha).
  - apply kX_miss_or.
    + apply (kX_miss_F cx fpos k2 ly3 S3 md3 sl' _ lo hi); [exact HB | exact HJB | exact Hok | lia | exact Hlo | exact Hhi |].
      intros a Ha. exact Ha.
    + apply (kX_miss_win cx fpos k2 ly3 S3 md3 sl' _); [exact HB | exact HJB | exact Hok | lia |].
      intros a Ha. exact Ha.
Qed.

(* X = [w2 + lo, w2 + hi): a put, a checked_memset or a checked_memcpy into w2, or w2's fields *)
Lemma kat_frame_w2 : forall lo hi cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 pc' rl' sl' W4 ms4 md4,
  kbase SK B cx ->
  kat B cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 ->
  kms pc' ms4 -> kregs0 cx ms4 -> kregs_eq ms4 rl' -> incl sl' sl -> kslots_okb sl' = true ->
  (length sh <= 2048)%nat -> m_fds md4 = m_fds md3 -> m_fs md4 = m_fs md3 ->
  0 <= lo -> hi <= NW_SIZE ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (kW2 cx fpos + lo <= a < kW2 cx fpos + hi) ->
     aview SEGS (w_H W4) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W4) (ms_mem ms4) a) ->
  kat B cx fpos pc' rl' sl' sh live adv g k2 ly3 S3 W4 ms4 md4.
Proof.
  intros lo hi cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 pc' rl' sl' W4 ms4 md4
    HB HK HMS HR0 HRL Hsl Hok Hsh Hfds Hfs Hlo Hhi UN HP.
  assert (Hfb : fs_frame_bytes KN_CID = 16384) by reflexivity.
  apply (kat_frame_F (KN_W2 + lo) (KN_W2 + hi) cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 pc' rl' sl'
           W4 ms4 md4 HB HK HMS HR0 HRL Hsl Hok Hsh Hfds Hfs); [unfold KN_W2; lia | | | exact HP].
  - rewrite Hfb. unfold KN_W2, NW_SIZE in *. lia.
  - intros a Ha Hn. apply UN; [exact Ha|]. unfold kW2. intros Hc. apply Hn. lia.
Qed.

(* X = [w2 + lo, w2 + hi) and a callee's window [s1 - ESTACK, s1): checked_memset / checked_memcpy into w2 *)
Lemma kat_frame_w2s : forall lo hi cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 pc' rl' sl' W4 ms4 md4,
  kbase SK B cx ->
  kat B cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 ->
  kms pc' ms4 -> kregs0 cx ms4 -> kregs_eq ms4 rl' -> incl sl' sl -> kslots_okb sl' = true ->
  (length sh <= 2048)%nat -> m_fds md4 = m_fds md3 -> m_fs md4 = m_fs md3 ->
  0 <= lo -> hi <= NW_SIZE ->
  (forall a, 0 <= a < 2 ^ 64 ->
     ~ ((kW2 cx fpos + lo <= a < kW2 cx fpos + hi) \/ (ksp1 cx - ESTACK <= a < ksp1 cx)) ->
     aview SEGS (w_H W4) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W4) (ms_mem ms4) a) ->
  kat B cx fpos pc' rl' sl' sh live adv g k2 ly3 S3 W4 ms4 md4.
Proof.
  intros lo hi cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 pc' rl' sl' W4 ms4 md4
    HB HK HMS HR0 HRL Hsl Hok Hsh Hfds Hfs Hlo Hhi UN HP.
  assert (Hfb : fs_frame_bytes KN_CID = 16384) by reflexivity.
  apply (kat_frame_Fs (KN_W2 + lo) (KN_W2 + hi) cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 pc' rl' sl'
           W4 ms4 md4 HB HK HMS HR0 HRL Hsl Hok Hsh Hfds Hfs); [unfold KN_W2; lia | | | exact HP].
  - rewrite Hfb. unfold KN_W2, NW_SIZE in *. lia.
  - intros a Ha Hn. apply UN; [exact Ha|]. unfold kW2. intros Hc. apply Hn.
    destruct Hc as [Hc|Hc]; [left; lia | right; exact Hc].
Qed.

(* X = [w1 + lo, w1 + hi) *)
Lemma kat_frame_w1 : forall lo hi cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 pc' rl' sl' W4 ms4 md4,
  kbase SK B cx ->
  kat B cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 ->
  kms pc' ms4 -> kregs0 cx ms4 -> kregs_eq ms4 rl' -> incl sl' sl -> kslots_okb sl' = true ->
  (length sh <= 2048)%nat -> m_fds md4 = m_fds md3 -> m_fs md4 = m_fs md3 ->
  0 <= lo -> hi <= NW_SIZE ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (kW1 cx fpos + lo <= a < kW1 cx fpos + hi) ->
     aview SEGS (w_H W4) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W4) (ms_mem ms4) a) ->
  kat B cx fpos pc' rl' sl' sh live adv g k2 ly3 S3 W4 ms4 md4.
Proof.
  intros lo hi cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 pc' rl' sl' W4 ms4 md4
    HB HK HMS HR0 HRL Hsl Hok Hsh Hfds Hfs Hlo Hhi UN HP.
  assert (Hfb : fs_frame_bytes KN_CID = 16384) by reflexivity.
  apply (kat_frame_F (KN_W1 + lo) (KN_W1 + hi) cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 pc' rl' sl'
           W4 ms4 md4 HB HK HMS HR0 HRL Hsl Hok Hsh Hfds Hfs); [unfold KN_W1; lia | | | exact HP].
  - rewrite Hfb. unfold KN_W1, NW_SIZE in *. lia.
  - intros a Ha Hn. apply UN; [exact Ha|]. unfold kW1. intros Hc. apply Hn. lia.
Qed.

(* X = [w1 + lo, w1 + hi) and a callee's window [s1 - ESTACK, s1) *)
Lemma kat_frame_w1s : forall lo hi cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 pc' rl' sl' W4 ms4 md4,
  kbase SK B cx ->
  kat B cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 ->
  kms pc' ms4 -> kregs0 cx ms4 -> kregs_eq ms4 rl' -> incl sl' sl -> kslots_okb sl' = true ->
  (length sh <= 2048)%nat -> m_fds md4 = m_fds md3 -> m_fs md4 = m_fs md3 ->
  0 <= lo -> hi <= NW_SIZE ->
  (forall a, 0 <= a < 2 ^ 64 ->
     ~ ((kW1 cx fpos + lo <= a < kW1 cx fpos + hi) \/ (ksp1 cx - ESTACK <= a < ksp1 cx)) ->
     aview SEGS (w_H W4) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W4) (ms_mem ms4) a) ->
  kat B cx fpos pc' rl' sl' sh live adv g k2 ly3 S3 W4 ms4 md4.
Proof.
  intros lo hi cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 pc' rl' sl' W4 ms4 md4
    HB HK HMS HR0 HRL Hsl Hok Hsh Hfds Hfs Hlo Hhi UN HP.
  assert (Hfb : fs_frame_bytes KN_CID = 16384) by reflexivity.
  apply (kat_frame_Fs (KN_W1 + lo) (KN_W1 + hi) cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 pc' rl' sl'
           W4 ms4 md4 HB HK HMS HR0 HRL Hsl Hok Hsh Hfds Hfs); [unfold KN_W1; lia | | | exact HP].
  - rewrite Hfb. unfold KN_W1, NW_SIZE in *. lia.
  - intros a Ha Hn. apply UN; [exact Ha|]. unfold kW1. intros Hc. apply Hn.
    destruct Hc as [Hc|Hc]; [left; lia | right; exact Hc].
Qed.

(* X = the spill slots [s1 + lo, s1 + hi) the kept slots avoid (a run that writes slots) *)
Lemma kat_frame_sl : forall lo hi cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 pc' rl' sl' W4 ms4 md4,
  kbase SK B cx ->
  kat B cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 ->
  kms pc' ms4 -> kregs0 cx ms4 -> kregs_eq ms4 rl' -> incl sl' sl -> kslots_okb sl' = true ->
  kslots_avoidb lo hi sl' = true ->
  (length sh <= 2048)%nat -> m_fds md4 = m_fds md3 -> m_fs md4 = m_fs md3 ->
  0 <= lo -> hi <= 0xf8 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (ksp1 cx + lo <= a < ksp1 cx + hi) ->
     aview SEGS (w_H W4) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W4) (ms_mem ms4) a) ->
  kat B cx fpos pc' rl' sl' sh live adv g k2 ly3 S3 W4 ms4 md4.
Proof.
  intros lo hi cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 pc' rl' sl' W4 ms4 md4
    HB HK HMS HR0 HRL Hsl Hok Hav Hsh Hfds Hfs Hlo Hhi UN HP.
  pose proof HK as (_ & _ & _ & _ & _ & _ & _ & HJB & _).
  apply (kat_frame (fun a => ksp1 cx + lo <= a < ksp1 cx + hi) cx fpos pc rl sl sh live adv g k2 ly3 S3
           W3 ms3 md3 pc' rl' sl' W4 ms4 md4 HB HK HMS HR0 HRL Hsl Hsh Hfds Hfs UN HP).
  - intros a Ha. exact (kX_in_sl cx fpos lo hi a HB Hlo Hhi Ha).
  - apply (kX_miss_sl cx fpos k2 ly3 S3 md3 sl' _ lo hi);
      [exact HB | exact HJB | exact Hok | exact Hav | lia | exact Hlo | exact Hhi |].
    intros a Ha. exact Ha.
Qed.

(* X empty: the same memory (a run with no writable window) *)
Lemma kat_frame_0 : forall cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 pc' rl' sl' ms4 md4,
  kat B cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 ->
  kms pc' ms4 -> kregs0 cx ms4 -> kregs_eq ms4 rl' -> ms_mem ms4 = ms_mem ms3 -> incl sl' sl ->
  m_fds md4 = m_fds md3 -> m_fs md4 = m_fs md3 ->
  kat B cx fpos pc' rl' sl' sh live adv g k2 ly3 S3 W3 ms4 md4.
Proof.
  intros cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 pc' rl' sl' ms4 md4
    (_ & _ & _ & HSV & HFRM & HSH & HSL & HJB & HKP & HCU & HGN & HLA) HMS HR0 HRL Hmem Hincl Hfds Hfs.
  unfold kat.
  unfold ksaved, kframe, kshadow, kslots_eq, kkept, kcursor, kgnl_at, kla_at in *.
  rewrite Hmem.
  split; [exact HMS|]. split; [exact HR0|]. split; [exact HRL|]. split; [exact HSV|].
  split; [exact HFRM|]. split; [exact HSH|].
  split; [rewrite Forall_forall in HSL |- *; intros ov Hov; exact (HSL ov (Hincl ov Hov))|].
  split; [exact (kjbk_md cx fpos k2 ly3 S3 md3 md4 HJB Hfds Hfs)|].
  exact (conj HKP (conj HCU (conj HGN HLA))).
Qed.

(* the slots a step wrote, added to a cut *)
Lemma kat_slots : forall cx fpos pc rl sl sl2 sl' sh live adv g k2 ly3 S3 W3 ms3 md3,
  kat B cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 -> kslots_eq cx W3 ms3 sl2 ->
  incl sl' (sl ++ sl2) -> kat B cx fpos pc rl sl' sh live adv g k2 ly3 S3 W3 ms3 md3.
Proof.
  intros cx fpos pc rl sl sl2 sl' sh live adv g k2 ly3 S3 W3 ms3 md3
    (H1 & H2 & H3 & H4 & H5 & H6 & HSL & H8 & H9 & H10 & H11 & H12) HSL2 Hinc.
  unfold kat.
  refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj _ (conj H8 (conj H9 (conj H10
    (conj H11 H12))))))))))).
  unfold kslots_eq in *. rewrite Forall_forall in HSL, HSL2 |- *. intros ov Hov.
  destruct (in_app_or _ _ _ (Hinc ov Hov)) as [H|H]; [exact (HSL ov H) | exact (HSL2 ov H)].
Qed.

(* the journal's bookkeeping replaced (an own callee's post returns at a fresh layout) *)
Lemma kat_jbk : forall cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 k2' ly4 S4 md4,
  kat B cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 -> kjbk B cx fpos k2' ly4 S4 md4 ->
  kat B cx fpos pc rl sl sh live adv g k2' ly4 S4 W3 ms3 md4.
Proof.
  intros cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 k2' ly4 S4 md4
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & _ & H9 & H10 & H11 & H12) HJ.
  unfold kat.
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj HJ (conj H9 (conj H10
    (conj H11 H12))))))))))).
Qed.

(* the struct nl_w at w kept, when X misses its two fields (n, full) *)
Lemma kw_frame : forall (X : Z -> Prop) W3 ms3 W4 ms4 w n f,
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview SEGS (w_H W4) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W4) (ms_mem ms4) a) ->
  (forall a, w + NW_N <= a < w + NW_FULL + 4 -> ~ X a) ->
  kw_at W3 ms3 w n f -> kw_at W4 ms4 w n f.
Proof.
  intros X W3 ms3 W4 ms4 w n f UN HP M (Hw0 & Hwl & Hp & Hn & Hf & Hnr & Hfr).
  pose proof (kk_grows_of_apresent _ _ _ _ HP) as HG.
  unfold kw_at, nlw_fields.
  refine (conj Hw0 (conj Hwl (conj (kk_nlw_present_grows SEGS _ _ _ HG Hp) (conj _ (conj _ (conj Hnr Hfr)))))).
  - apply (val_mem_moved SEGS (w_H W3) (w_H W4) (ms_mem ms3) (ms_mem ms4) (w + NW_N) (w + NW_N) 8 n); [|exact Hn].
    intros k Hk. apply UN; [unfold NW_N, NW_SIZE in *; lia | apply M; unfold NW_N, NW_FULL; lia].
  - apply (val_mem_moved SEGS (w_H W3) (w_H W4) (ms_mem ms3) (ms_mem ms4) (w + NW_FULL) (w + NW_FULL) 4 f);
      [|exact Hf].
    intros k Hk. apply UN; [unfold NW_FULL, NW_SIZE in *; lia | apply M; unfold NW_N, NW_FULL; lia].
Qed.

(* the struct nl_w at w with new fields read off the step's end *)
Lemma kw_move : forall W3 ms3 W4 ms4 w n f n' f',
  kw_at W3 ms3 w n f -> (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W4) (ms_mem ms4) a) ->
  val_mem SEGS (rdW W4 (ms_mem ms4)) (w + NW_N) 8 n' -> val_mem SEGS (rdW W4 (ms_mem ms4)) (w + NW_FULL) 4 f' ->
  0 <= n' <= NL_CHUNK_MAX -> 0 <= f' <= 1 -> kw_at W4 ms4 w n' f'.
Proof.
  intros W3 ms3 W4 ms4 w n f n' f' (Hw0 & Hwl & Hp & _) HP Hn Hf Hnr Hfr.
  pose proof (kk_grows_of_apresent _ _ _ _ HP) as HG.
  exact (conj Hw0 (conj Hwl (conj (kk_nlw_present_grows SEGS _ _ _ HG Hp) (conj Hn (conj Hf (conj Hnr Hfr)))))).
Qed.

(* ---- the dispatch phase's read-set facts (kernel_disp.v 5365315da590 kdp_*, the same proofs under kn_ names) ---- *)

(* the bytes of kernel's class-8 frame F at slot fpos, and its shadow bytes *)
Definition kn_fside (cx : kcx) (fpos a : Z) : Prop :=
  in_zr a (frame_rng (k_lyc cx) (KN_CID, fpos)) \/
  in_zr a (shadow_addr (kF cx fpos), fs_frame_bytes KN_CID / 8).

Lemma kn_fside_aside : forall cx fpos a, kn_fside cx fpos a -> aside_rng (k_lyc cx) KN_CID fpos a.
Proof. intros cx fpos a [H | H]; [left; exact H | right; left; exact H]. Qed.

(* the shadow band is exactly [kLowMemEnd, kHighMemBeg) *)
Lemma kn_band : SHADOW_OFF + 2 ^ 44 = kHighMemBeg /\ SHADOW_OFF = kLowMemEnd.
Proof. split; reflexivity. Qed.

Lemma kn_akb : forall (cx : kcx) (fpos : Z) S1 W1 mem1 md1 slo shi a,
  alloc_ceiling <= ly_stk_lo (k_lyc cx) -> ly_stk_hi (k_lyc cx) <= 2 ^ 47 ->
  AR SEGS B (k_lyc cx) S1 W1 mem1 md1 ->
  frames S1 = (KN_CID, fpos) :: frames (k_Sc cx) ->
  ablocks B (k_lyc cx) S1 = ablocks B (k_lyc cx) (k_Sc cx) ->
  akb SEGS B (k_lyc cx) (k_Sc cx) slo shi a ->
  4096 <= a < 2 ^ 47 /\ ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44) /\ ~ kn_fside cx fpos a.
Proof.
  intros cx fpos S1 W1 mem1 md1 slo shi a Hrlo Hrhi HAR Hfr Hbl Hb.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (Hin1 : In (KN_CID, fpos) (frames S1)) by (rewrite Hfr; left; reflexivity).
  destruct (frames_bounds SEGS B LAWS (k_lyc cx) S1 W1 mem1 md1 KN_CID fpos HAR Hin1) as (HF0 & HFc & HFapp).
  assert (HFB : fs_frame_bytes KN_CID = 16384) by reflexivity.
  assert (HFsh : forall x, in_zr x (shadow_addr (kF cx fpos), fs_frame_bytes KN_CID / 8) ->
                   SHADOW_OFF <= x < SHADOW_OFF + 2 ^ 44).
  { intros x Hx. unfold in_zr, shadow_addr, kF in *. cbn [fst snd] in Hx.
    unfold SHADOW_OFF in *. rewrite HFB in Hx.
    pose proof (Z.div_pos (frame_addr (k_lyc cx) KN_CID fpos) 8 ltac:(unfold kF in HF0; lia) ltac:(lia)).
    pose proof (Z.div_le_mono (frame_addr (k_lyc cx) KN_CID fpos) alloc_ceiling 8 ltac:(lia)
                  ltac:(unfold kF in HFc; rewrite HFB in HFc; lia)).
    unfold alloc_ceiling in *. lia. }
  assert (HFrng : forall x, in_zr x (frame_rng (k_lyc cx) (KN_CID, fpos)) -> 4096 <= x < alloc_ceiling).
  { intros x Hx. unfold in_zr, frame_rng in Hx. cbn [fst snd] in Hx.
    unfold kF in HF0, HFc. rewrite HFB in HFc, Hx. lia. }
  destruct Hb as [(H1 & H2) | [(b & m & Hin & Hr) | [(H1 & H2 & H3) | (c2 & p2 & Hin & Hr)]]].
  - split; [unfold alloc_ceiling in *; lia|].
    split; [unfold SHADOW_OFF, alloc_ceiling in *; lia|].
    intros [Hx | Hx]; [pose proof (HFrng a Hx) | pose proof (HFsh a Hx)];
      unfold SHADOW_OFF, alloc_ceiling in *; lia.
  - assert (Hin' : In (b, m) (ablocks B (k_lyc cx) S1)) by (rewrite Hbl; exact Hin).
    destruct (al_blocks _ _ LAWS (k_lyc cx) S1 W1 mem1 md1 b m HAR Hin')
      as (_ & Hb0 & Hbc & Hia & _).
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hia.
    split; [unfold alloc_ceiling in *; lia|].
    split; [unfold SHADOW_OFF in *; lia|].
    intros [Hx | Hx].
    + pose proof (sep_block_frame SEGS B LAWS (k_lyc cx) S1 W1 mem1 md1 b m KN_CID fpos HAR Hin' Hin1) as Hd.
      unfold zdisjoint, in_zr, frame_rng in Hd, Hx. cbn [fst snd] in Hd, Hx. lia.
    + pose proof (HFsh a Hx). unfold SHADOW_OFF in *. lia.
  - pose proof (pa_segs_low a H1) as Hlow.
    pose proof (pa_img_range a H1) as Hrng.
    split; [unfold kLowMemEnd, YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia|].
    split; [unfold SHADOW_OFF, kLowMemEnd in *; lia|].
    intros [Hx | Hx].
    + pose proof (frm_off_imgP B (k_lyc cx) S1 W1 mem1 md1 KN_CID fpos HAR Hin1) as Hoff.
      unfold off_img, in_zr, frame_rng in Hoff, Hx. cbn [fst snd] in Hx.
      rewrite HFB in Hoff, Hx.
      unfold pcap_img_end, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hoff, Hrng.
      destruct Hoff as [Hoff | Hoff]; lia.
    + pose proof (HFsh a Hx). unfold SHADOW_OFF, kLowMemEnd in *. lia.
  - assert (Hin' : In (c2, p2) (frames S1)) by (rewrite Hfr; right; exact Hin).
    destruct (frames_bounds SEGS B LAWS (k_lyc cx) S1 W1 mem1 md1 c2 p2 HAR Hin') as (H20 & H2c & H2app).
    pose proof (fs_frame_bytes_nonneg c2) as Hnn2.
    unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr.
    split; [unfold alloc_ceiling in *; lia|].
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in H2app.
    split; [unfold SHADOW_OFF, alloc_ceiling in *; lia|].
    intros [Hx | Hx].
    + apply in_split in Hin as (l2 & l3 & El).
      pose proof (sep_frames_pos SEGS B LAWS (k_lyc cx) S1 W1 mem1 md1 (KN_CID, fpos) (c2, p2) [] l2 l3 HAR
                    ltac:(rewrite Hfr, El; reflexivity)) as Hd.
      unfold zdisjoint, frame_rng, in_zr in Hd, Hx. cbn [fst snd] in Hd, Hx. lia.
    + pose proof (HFsh a Hx).
      unfold SHADOW_OFF, alloc_ceiling in *. lia.
Qed.

(* a register the symbolic state names by a value the machine already has (attr_text.v at_regs_ok_set) *)
Lemma kn_regs_ok_set : forall E sr regs (rd : bv 5) e,
  regs_ok E sr regs -> bv_eqb rd 0 = false -> sv_denot E e = getr regs rd ->
  regs_ok E (sr_set sr rd e) regs.
Proof.
  intros E sr regs rd e H H0 He r. destruct (bv_eqb r rd) eqn:Heq.
  - unfold bv_eqb in Heq. apply Z.eqb_eq, bv_eq in Heq. subst r. rewrite sr_get_set_same by exact H0.
    rewrite He. reflexivity.
  - rewrite sr_get_set_other by (intros ->; rewrite bv_eqb_refl in Heq; discriminate). apply H.
Qed.

(* the shadow cell of an atom at an offset: ((x + c) >> 3) + B (LinkWalkPi denot_shadow_cell, with the offset) *)
Lemma kn_denot_sh : forall (E : env) (nn mm : nat) (v c base : Z),
  ew E nn = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  ew E mm = Z_to_bv 64 base -> 0 <= base -> base + (v + c) / 8 < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff nn c) (SLit 3)) (SOff mm 0)) =
  Z_to_bv 64 (base + (v + c) / 8).
Proof.
  intros E nn mm v c base Hn Hv Hvc Hm Hb Hs. rewrite denot_lit_U. f_equal.
  assert (Hd : 0 <= (v + c) / 8) by (apply Z.div_pos; lia).
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
  change (Z.land (zcanon 3) 63) with 3.
  rewrite (U_atom_off E nn v c Hn ltac:(lia) ltac:(lia)),
          (U_atom_off E mm base 0 Hm ltac:(lia) ltac:(lia)).
  rewrite Z.add_0_r. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  rewrite (zcanon_id ((v + c) / 8)) by (unfold M64; lia).
  rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

(* two ranges are disjoint when no byte of the first lies in the second *)
Lemma kn_disj_of : forall lo1 n1 lo2 n2, 0 < n1 -> 0 < n2 ->
  (forall x, lo1 <= x < lo1 + n1 -> ~ (lo2 <= x < lo2 + n2)) ->
  lo1 + n1 <= lo2 \/ lo2 + n2 <= lo1.
Proof.
  intros lo1 n1 lo2 n2 H1 H2 H.
  destruct (Z.le_gt_cases (lo1 + n1) lo2) as [Hle | Hgt]; [left; exact Hle|].
  destruct (Z.le_gt_cases (lo2 + n2) lo1) as [Hle2 | Hgt2]; [right; exact Hle2|].
  exfalso. apply (H (Z.max lo1 lo2)); lia.
Qed.

Lemma kn_reg_of : forall ms3 rl r v,
  kregs_eq ms3 rl -> In (r, v) rl -> getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat r)) = w64 v.
Proof. intros ms3 rl r v H Hin. unfold kregs_eq in H. rewrite Forall_forall in H. exact (H (r, v) Hin). Qed.

Lemma kn_slot_of : forall cx W3 ms3 sl o v,
  kslots_eq cx W3 ms3 sl -> In (o, v) sl ->
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (ksp1 cx + o) = Some v.
Proof.
  intros cx W3 ms3 sl o v H Hin. unfold kslots_eq in H. rewrite Forall_forall in H. exact (H (o, v) Hin).
Qed.

Lemma kn_row : forall cx, kbase SK B cx ->
  alloc_ceiling <= ly_stk_lo (k_lyc cx) /\ ly_stk_hi (k_lyc cx) <= 2 ^ 47.
Proof.
  intros cx HB. destruct HB as (HPRE & _). destruct HPRE as (HJ & _).
  destruct (ajournal_gx_row SK SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx)
              (k_S cx) (k_W0 cx) (k_mem0 cx) (k_md0 cx) (k_own cx) (k_lyc cx) (k_Sc cx) (k_W cx)
              (k_memc cx) (k_mdc cx) (k_k cx) HJ) as (H1 & H2 & _).
  split; [exact H1 | exact H2].
Qed.

(* every byte of the read set: in [4096, 2 ^ 47), off the shadow band, off F and F's shadow *)
Lemma kn_rd_facts : forall cx fpos k2 ly3 S3 md3 a,
  kbase SK B cx -> kjbk B cx fpos k2 ly3 S3 md3 ->
  kernel_ard SEGS (k_regs cx) (km0 cx) a ->
  4096 <= a < 2 ^ 47 /\ ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44) /\ ~ kn_fside cx fpos a.
Proof.
  intros cx fpos k2 ly3 S3 md3 a HB HJB HRD.
  destruct (kn_row cx HB) as (Hlo & Hhi).
  pose proof HB as (_ & HRDset & _).
  destruct HJB as (_ & _ & _ & _ & (S1 & W1 & mem1 & md1 & HAR & Hfr & Hbl) & _).
  exact (kn_akb cx fpos S1 W1 mem1 md1 _ _ a Hlo Hhi HAR Hfr Hbl (HRDset a HRD)).
Qed.

(* the cursor's own 16 bytes are a read-set byte *)
Lemma kn_ard_cur : forall cx a, ka0 cx <= a < ka0 cx + 16 -> kernel_ard SEGS (k_regs cx) (km0 cx) a.
Proof. intros cx a Ha. left. unfold ka0 in Ha. exact Ha. Qed.

(* so is a byte of the input the cursor points into *)
Lemma kn_ard_inp : forall cx a, k_wp cx <= a < k_wp cx + k_wn cx ->
  kbase SK B cx -> kernel_ard SEGS (k_regs cx) (km0 cx) a.
Proof.
  intros cx a Ha HB.
  destruct HB as (_ & _ & _ & _ & _ & HWP & HWN & HWPr & HWNr & _).
  right. left. exists (k_wp cx), (k_wn cx).
  refine (conj HWP (conj HWN (conj HWPr (conj HWNr Ha)))).
Qed.

(* s1 lies in [sp - 368, sp - 352], so the spill area [s1 + 0x18, s1 + 0xf8) is inside kernel's window
   [sp - KERNEL_AK, sp) and below the thirteen saved words at [sp - 104, sp) *)
Lemma kn_sp1 : forall cx, kbase SK B cx ->
  ksp cx - 368 <= ksp1 cx <= ksp cx - 352 /\ ksp1 cx mod 32 = 0 /\
  2 ^ 46 <= ksp1 cx /\ ksp1 cx + 0xf8 <= ksp cx - 104 /\
  ksp cx - KERNEL_AK <= ksp1 cx + 0x18 /\ ksp cx <= 2 ^ 47 /\
  k_sp0 cx - k_STK cx <= ksp cx - KERNEL_AK /\ ksp cx <= k_sp0 cx.
Proof.
  intros cx HB.
  pose proof (kn_row cx HB) as (Hrlo & Hrhi).
  destruct HB as (HPRE & _).
  pose proof HPRE as (HJ & _ & _ & _ & _ & _ & _ & Hal16 & Hwlo & Hwhi & _).
  destruct (ajournal_gx_row SK SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx)
              (k_ly cx) (k_S cx) (k_W0 cx) (k_mem0 cx) (k_md0 cx) (k_own cx) (k_lyc cx) (k_Sc cx)
              (k_W cx) (k_memc cx) (k_mdc cx) (k_k cx) HJ) as (_ & _ & Hrow1 & Hrow2).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK : KERNEL_AK = 4640) by reflexivity.
  unfold ksp1, ksp1_of, KN_MFRAME in *. unfold ksp in *. rewrite HK in Hwlo |- *.
  assert (Hsp0 : 0 <= spZ (k_regs cx) < 2 ^ 64) by (unfold spZ; apply getr_rng).
  assert (Hx : 0 <= spZ (k_regs cx) - 352) by (unfold alloc_ceiling in *; lia).
  assert (Hxm : (spZ (k_regs cx) - 352) mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
  destruct (sp1_facts (spZ (k_regs cx) - 352) Hx Hxm) as (Hr & Hal32 & _).
  pose proof HJ as (HSTK & HXO & _).
  split; [revert Hr; clear; intros; lia|].
  split; [exact Hal32|].
  split; [revert Hr Hwlo Hrow1 Hrlo C1a; clear; intros; lia|].
  split; [revert Hr; clear; intros; lia|].
  split; [revert Hr; clear; intros; lia|].
  split; [revert Hwhi Hrow2 Hrhi HXO; clear; intros; lia|].
  split; [exact Hwlo | exact Hwhi].
Qed.

(* every byte of the spill area is present, so writable: it is inside the journal's window *)
Lemma kn_spill_wr : forall cx fpos k2 ly3 S3 W3 ms3 md3,
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx)
    (k_W0 cx) (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  forall o, 0x18 <= o < 0xf8 -> writable_at SEGS (mrestrict (w_H W3) (ms_mem ms3)) (ksp1 cx + o).
Proof.
  intros cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ o Ho.
  destruct (kn_sp1 cx HB) as (_ & _ & _ & Hhi & Hlo & _ & Hw1 & Hw2).
  apply (apresent_writable SEGS).
  apply (aj_gx_present SK SEGS B LAWS pa_segs_low (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx)
           (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx) (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx)
           ly3 S3 W3 (ms_mem ms3) md3 k2 HJ).
  lia.
Qed.

(* ---- kernel_msg0_kit.v's kit (a09af0a0165f, km_* / kat_move / kshadow_w2 / kslots_*: the same proofs
   under kn_ names): the call's numbers, the read set's places, the moves of a cut's views, the read set's
   shadow facts and values at a cut ---- *)
Lemma kn_nth_rep : forall (a d : Z) m n, (n < m)%nat -> nth n (repeat a m) d = a.
Proof.
  intros a d m. induction m as [|m IH]; intros n Hn; [lia|].
  destruct n as [|n]; [reflexivity|]. cbn [repeat nth]. apply IH. lia.
Qed.

(* F's shadow list: the five runs *)
Lemma kn_kfsh_nth : forall s1v s2v r (i : nat),
  nth i (kfsh s1v s2v r) 0 =
    if (i <? 4)%nat then 0xf1 else if (i <? 0x206)%nat then s1v else if (i <? 0x226)%nat then 0xf2
    else if (i <? 0x428)%nat then s2v else if (i <? 0x448)%nat then r else 0.
Proof.
  intros s1v s2v r i. unfold kfsh.
  destruct (Nat.ltb_spec i 4) as [H1|H1].
  { rewrite app_nth1 by (rewrite repeat_length; lia). apply kn_nth_rep; lia. }
  rewrite app_nth2 by (rewrite repeat_length; lia). rewrite repeat_length.
  destruct (Nat.ltb_spec i 0x206) as [H2|H2].
  { rewrite app_nth1 by (rewrite repeat_length; lia). apply kn_nth_rep; lia. }
  rewrite app_nth2 by (rewrite repeat_length; lia). rewrite repeat_length.
  destruct (Nat.ltb_spec i 0x226) as [H3|H3].
  { rewrite app_nth1 by (rewrite repeat_length; lia). apply kn_nth_rep; lia. }
  rewrite app_nth2 by (rewrite repeat_length; lia). rewrite repeat_length.
  destruct (Nat.ltb_spec i 0x428) as [H4|H4].
  { rewrite app_nth1 by (rewrite repeat_length; lia). apply kn_nth_rep; lia. }
  rewrite app_nth2 by (rewrite repeat_length; lia). rewrite repeat_length.
  destruct (Nat.ltb_spec i 0x448) as [H5|H5].
  { apply kn_nth_rep; lia. }
  apply nth_overflow. rewrite repeat_length. lia.
Qed.

Lemma kn_fsb8 : fs_frame_bytes KN_CID = 16384.
Proof. reflexivity. Qed.

(* the bytes the phases of this lane change: the window below s1 + 0xf8 (the spill slots and every callee window),
   the cursor, w2, and w2's 0x202 shadow bytes *)
Definition kn_X (cx : kcx) (fpos a : Z) : Prop :=
  (ksp cx - KERNEL_AK <= a < ksp1 cx + 0xf8) \/ (ka0 cx <= a < ka0 cx + 16) \/
  (kW2 cx fpos <= a < kW2 cx fpos + NW_SIZE) \/ (kFSH cx fpos + 0x226 <= a < kFSH cx fpos + 0x428).

(* ---- the stack numbers of the call ---- *)
Lemma kn_sp : forall cx, kbase SK B cx ->
  alloc_ceiling + KERNEL_AK <= ksp cx /\ ksp cx <= 2 ^ 47 /\ ksp cx mod 16 = 0 /\
  ksp cx - 368 <= ksp1 cx <= ksp cx - 352 /\ ksp1 cx mod 32 = 0 /\
  k_sp0 cx - k_STK cx <= ksp cx - KERNEL_AK /\ ksp cx <= k_sp0 cx /\
  alloc_ceiling <= k_sp0 cx - k_STK cx /\ k_sp0 cx <= 2 ^ 47 /\
  alloc_ceiling <= ly_stk_lo (k_lyc cx) /\ ly_stk_hi (k_lyc cx) <= 2 ^ 47.
Proof.
  intros cx HB. destruct HB as (HPRE & _).
  destruct HPRE as (HJ & _ & _ & _ & _ & _ & _ & Hal16 & Hwlo & Hwhi & _).
  destruct (ajournal_gx_row SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (Hlo & Hhi & H1 & H2).
  pose proof HJ as (HSTK & HXO & _).
  pose proof asan_consts as ((C1a & C1b) & _).
  assert (HK : KERNEL_AK = 4640) by reflexivity.
  unfold ksp1, ksp1_of, KN_MFRAME, ksp. rewrite HK in Hwlo |- *. repeat split; lia.
Qed.

(* ---- F, from kjbk's witness state S1 (AR, F on top of the call's frames, the call's blocks) ---- *)
Lemma kn_F : forall cx fpos k2 ly3 S3 md3, kbase SK B cx -> kjbk B cx fpos k2 ly3 S3 md3 ->
  4096 <= kF cx fpos /\ kF cx fpos + 16384 <= alloc_ceiling /\ kF cx fpos mod 64 = 0 /\
  (kF cx fpos + 16384 <= kLowShadowBeg \/ kHighMemBeg <= kF cx fpos).
Proof.
  intros cx fpos k2 ly3 S3 md3 HB HJB.
  destruct HJB as (_ & _ & _ & _ & (S1 & W1 & mem1 & md1 & HAR1 & HF1 & _) & _).
  assert (Hin : In (KN_CID, fpos) (frames S1)) by (rewrite HF1; left; reflexivity).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR1 Hin) as (H1 & H2 & H3).
  destruct (frame_al64 SEGS B _ _ _ _ _ _ _ HAR1 Hin) as (H4 & _).
  rewrite kn_fsb8 in H2, H3. unfold in_app, ASAN_CEIL in H3. unfold kF.
  split; [lia|]. split; [lia|]. split; [exact H4|].
  destruct H3 as (_ & [H3|(H3 & _)]); [left | right]; lia.
Qed.

(* ---- every byte of kernel's read set: below 2 ^ 47, in the application memory, outside F and the window ---- *)
Lemma kn_ard_loc : forall cx fpos k2 ly3 S3 md3 x, kbase SK B cx -> kjbk B cx fpos k2 ly3 S3 md3 ->
  kernel_ard SEGS (k_regs cx) (km0 cx) x ->
  0 <= x < 2 ^ 47 /\ (x < kLowMemEnd \/ kHighMemBeg <= x) /\
  ~ (kF cx fpos <= x < kF cx fpos + 16384) /\ ~ (ksp cx - KERNEL_AK <= x < ksp cx).
Proof.
  intros cx fpos k2 ly3 S3 md3 x HB HJB Hx.
  pose proof (kn_sp cx HB) as (S1' & S2' & _ & _ & _ & _ & _ & _ & _ & Slo & Shi).
  pose proof (kn_F cx fpos k2 ly3 S3 md3 HB HJB) as (F1 & F2 & _ & _).
  pose proof HB as (HPRE & HRD & _).
  pose proof HPRE as (HJ & _).
  pose proof HJ as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (HAR0 & _).
  destruct HJB as (_ & _ & _ & _ & (S1 & W1 & mem1 & md1 & HAR1 & HF1 & HBL1) & _).
  assert (Hin : In (KN_CID, fpos) (frames S1)) by (rewrite HF1; left; reflexivity).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof (HRD x Hx) as Hk.
  destruct Hk as [(Ha1 & Ha2) | [(b & m & Hbm & Hbx) | [(Himg & _ & _) | (cid & pos & Hcp & Hcx)]]].
  - repeat split; lia.
  - destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR0 Hbm) as (_ & Hb4096 & Hbceil & Hia & _).
    assert (Hbm1 : In (b, m) (ablocks B (k_lyc cx) S1)) by (rewrite HBL1; exact Hbm).
    pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b m KN_CID fpos HAR1 Hbm1 Hin) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite kn_fsb8 in Hd. fold (kF cx fpos) in Hd.
    unfold in_app, kLowShadowBeg, ASAN_CEIL in Hia. repeat split; lia.
  - pose proof (pa_segs_low x Himg) as Hl.
    assert (HnF : ~ (kF cx fpos <= x < kF cx fpos + 16384)).
    { intros Hf.
      assert (Hrng : aside_rng (k_lyc cx) KN_CID fpos x)
        by (left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite kn_fsb8; exact Hf).
      destruct (aside_rng_low SK SEGS B LAWS pa_segs_low _ _ _ _ _ KN_CID fpos x HAR1 Hin Hrng) as (_ & Hni).
      exact (Hni Himg). }
    split; [lia|]. split; [lia|]. split; [exact HnF | lia].
  - assert (Hcp1 : In (cid, pos) (frames S1)) by (rewrite HF1; right; exact Hcp).
    destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR1 Hcp1) as (G1 & G2 & G3).
    destruct (in_split _ _ Hcp) as (l2 & l3 & El).
    pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (KN_CID, fpos) (cid, pos) [] l2 l3 HAR1
      ltac:(rewrite HF1, El; reflexivity)) as Hd.
    unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite kn_fsb8 in Hd. fold (kF cx fpos) in Hd.
    unfold in_zr, frame_rng in Hcx. cbn [fst snd] in Hcx.
    pose proof (fs_frame_bytes_nonneg cid).
    unfold in_app, kLowShadowBeg, ASAN_CEIL in G3. repeat split; lia.
Qed.

(* the cut's facts, by name *)
Lemma kn_apre : forall cx, kbase SK B cx ->
  apart_gnl LA_G_NL (ka0 cx) 16 /\ apart (ka0 cx) 16 LA_LONG_ALIAS (LONG_ALIAS_SIZE + 3) /\
  range_addressable (ard SEGS (km0 cx)) SHADOW_OFF (ka0 cx) 16 /\
  range_addressable (ard SEGS (km0 cx)) SHADOW_OFF (k_wp cx) (k_wn cx) /\
  amem_range (k_wp cx) (k_wn cx) /\ kernel_apart (k_regs cx) (k_wp cx) (k_wn cx).
Proof.
  intros cx HB.
  destruct HB as (_ & _ & HKP & _ & _ & HWP & HWN & HWPr & HWNr & _).
  destruct HKP as (kbs & _ & _ & _ & _ & (wp & wn & Hwp & Hwn & Hwpr & Hwnr & _ & Hamr & Hra & _ & Hap) &
    _ & Hra0 & _ & Hgnl & Hla & _).
  assert (E1 : wp = k_wp cx).
  { pose proof (rdword_of_val_mem SEGS (w_H (k_W cx)) (k_memc cx) _ _ Hwp Hwpr) as R1.
    pose proof (rdword_of_val_mem SEGS (w_H (k_W cx)) (k_memc cx) _ _ HWP HWPr) as R2.
    unfold ka0 in *. rewrite R1 in R2. injection R2 as R2. exact R2. }
  assert (E2 : wn = k_wn cx).
  { pose proof (rdword_of_val_mem SEGS (w_H (k_W cx)) (k_memc cx) _ _ Hwn Hwnr) as R1.
    pose proof (rdword_of_val_mem SEGS (w_H (k_W cx)) (k_memc cx) _ _ HWN HWNr) as R2.
    unfold ka0 in *. rewrite R1 in R2. injection R2 as R2. exact R2. }
  subst wp wn. unfold ka0. exact (conj Hgnl (conj Hla (conj Hra0 (conj Hra (conj Hamr Hap))))).
Qed.

(* the bytes kn_X names, against the places a cut's facts sit *)
Lemma kn_X_hi : forall cx fpos k2 ly3 S3 md3 a, kbase SK B cx -> kjbk B cx fpos k2 ly3 S3 md3 ->
  ksp1 cx + 0xf8 <= a < ksp cx -> ~ kn_X cx fpos a.
Proof.
  intros cx fpos k2 ly3 S3 md3 a HB HJB Ha.
  pose proof (kn_sp cx HB) as (S1 & S2 & _ & S4 & _).
  pose proof (kn_F cx fpos k2 ly3 S3 md3 HB HJB) as (F1 & F2 & F3 & F4).
  assert (HK : KERNEL_AK = 4640) by reflexivity.
  assert (Hc : ~ (ka0 cx <= a < ka0 cx + 16)).
  { intros Hc.
    assert (Hx : kernel_ard SEGS (k_regs cx) (km0 cx) a) by (left; unfold ka0 in *; lia).
    destruct (kn_ard_loc cx fpos k2 ly3 S3 md3 a HB HJB Hx) as (_ & _ & _ & Hw).
    apply Hw. rewrite HK. lia. }
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (Hf8 : kF cx fpos / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
  rewrite HK in S1.
  unfold kn_X, kW2, kFSH, shadow_of_addr, KN_W2, NW_SIZE, SHADOW_OFF.
  intros [H|[H|[H|H]]]; [lia | exact (Hc H) | lia | lia].
Qed.

(* a byte of the read set is no byte of kn_X *)
Lemma kn_X_ard : forall cx fpos k2 ly3 S3 md3 x, kbase SK B cx -> kjbk B cx fpos k2 ly3 S3 md3 ->
  kernel_ard SEGS (k_regs cx) (km0 cx) x -> ~ (ka0 cx <= x < ka0 cx + 16) -> ~ kn_X cx fpos x.
Proof.
  intros cx fpos k2 ly3 S3 md3 x HB HJB Hx Hc.
  pose proof (kn_sp cx HB) as (S1 & S2 & _ & S4 & _).
  pose proof (kn_F cx fpos k2 ly3 S3 md3 HB HJB) as (F1 & F2 & F3 & F4).
  destruct (kn_ard_loc cx fpos k2 ly3 S3 md3 x HB HJB Hx) as (L1 & L2 & L3 & L4).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK : KERNEL_AK = 4640) by reflexivity.
  assert (Hf8 : kF cx fpos / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
  unfold kn_X, kW2, kFSH, shadow_of_addr, KN_W2, NW_SIZE, SHADOW_OFF.
  rewrite HK in *. unfold kHighMemBeg, kLowMemEnd in *. intros [H|[H|[H|H]]]; lia.
Qed.

(* a byte of F outside w2 is no byte of kn_X *)
Lemma kn_X_F : forall cx fpos k2 ly3 S3 md3 a, kbase SK B cx -> kjbk B cx fpos k2 ly3 S3 md3 ->
  kF cx fpos <= a < kF cx fpos + 16384 -> ~ (kW2 cx fpos <= a < kW2 cx fpos + NW_SIZE) -> ~ kn_X cx fpos a.
Proof.
  intros cx fpos k2 ly3 S3 md3 a HB HJB Ha Hw.
  pose proof (kn_sp cx HB) as (S1 & S2 & _ & S4 & _).
  pose proof (kn_F cx fpos k2 ly3 S3 md3 HB HJB) as (F1 & F2 & F3 & F4).
  assert (Hc : ~ (ka0 cx <= a < ka0 cx + 16)).
  { intros Hc.
    assert (Hx : kernel_ard SEGS (k_regs cx) (km0 cx) a) by (left; unfold ka0 in *; lia).
    destruct (kn_ard_loc cx fpos k2 ly3 S3 md3 a HB HJB Hx) as (_ & _ & HnF & _).
    exact (HnF Ha). }
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK : KERNEL_AK = 4640) by reflexivity.
  assert (Hf8 : kF cx fpos / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
  unfold kn_X, kFSH, shadow_of_addr. rewrite HK in *.
  unfold kHighMemBeg, kLowShadowBeg, kLowMemEnd, SHADOW_OFF in *.
  intros [H|[H|[H|H]]]; first [lia | exact (Hc H) | exact (Hw H)].
Qed.

(* ---- moving the views of a cut ---- *)
Lemma kn_au8arr_move : forall (W : world SEGS) m m' a bs,
  au8arr SEGS (rdW W m) a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> aview SEGS (w_H W) m' (a + i) = aview SEGS (w_H W) m (a + i)) ->
  (forall x, apresent (w_H W) m x -> apresent (w_H W) m' x) ->
  au8arr SEGS (rdW W m') a bs.
Proof.
  intros W m m' a bs ((H0 & H1 & Hb) & Hw) Hag Hp. split; [split; [exact H0 | split; [exact H1 |]] |].
  - intros i Hi. rewrite <- (Hb i Hi). apply mbyte_of_aview. apply Hag. lia.
  - intros i Hi. apply (writable_kept (w_H W) m m' (a + i) (Hp (a + i))). exact (Hw i Hi).
Qed.

Lemma kn_val_mem_move : forall (W : world SEGS) m m' a (n : nat) v,
  val_mem SEGS (rdW W m) a n v ->
  (forall i, 0 <= i < Z.of_nat n -> aview SEGS (w_H W) m' (a + i) = aview SEGS (w_H W) m (a + i)) ->
  val_mem SEGS (rdW W m') a n v.
Proof.
  intros W m m' a n v Hv Hag k Hk. rewrite <- (Hv k Hk). apply mbyte_of_aview. apply Hag. lia.
Qed.

(* ---- F's shadow after meta_fill_00 on w2's 0x202 shadow bytes ---- *)
Lemma kn_kshadow_w2 : forall cx fpos W3 ms3 ms' s1v s2v r,
  kshadow cx fpos W3 ms3 (kfsh s1v s2v r) ->
  (forall i, 0 <= i < 0x448 -> ~ (0x226 <= i < 0x428) ->
     aview SEGS (w_H W3) (ms_mem ms') (kFSH cx fpos + i) = aview SEGS (w_H W3) (ms_mem ms3) (kFSH cx fpos + i)) ->
  (forall i, 0 <= i < 0x202 -> aview SEGS (w_H W3) (ms_mem ms') (kFSH cx fpos + 0x226 + i) = Some 0) ->
  kshadow cx fpos W3 ms' (kfsh s1v 0 r).
Proof.
  intros cx fpos W3 ms3 ms' s1v s2v r Hsh Hk H0 i Hi. rewrite kfsh_length in Hi.
  rewrite kn_kfsh_nth.
  destruct (Nat.ltb_spec i 0x226) as [Hq1|Hq1].
  - rewrite Hk by lia. rewrite (Hsh i ltac:(rewrite kfsh_length; lia)). rewrite kn_kfsh_nth.
    destruct (Nat.ltb_spec i 4); [reflexivity|]. destruct (Nat.ltb_spec i 0x206); [reflexivity|].
    destruct (Nat.ltb_spec i 0x226); [reflexivity | lia].
  - destruct (Nat.ltb_spec i 4); [lia|]. destruct (Nat.ltb_spec i 0x206); [lia|].
    destruct (Nat.ltb_spec i 0x428) as [Hq2|Hq2].
    + replace (kFSH cx fpos + Z.of_nat i) with (kFSH cx fpos + 0x226 + (Z.of_nat i - 0x226)) by lia.
      apply H0. lia.
    + rewrite Hk by lia. rewrite (Hsh i ltac:(rewrite kfsh_length; lia)). rewrite kn_kfsh_nth.
      destruct (Nat.ltb_spec i 4); [lia|]. destruct (Nat.ltb_spec i 0x206); [lia|].
      destruct (Nat.ltb_spec i 0x226); [lia|]. destruct (Nat.ltb_spec i 0x428); [lia | reflexivity].
Qed.

(* ---- the slot values of a cut, as kslots_eq of a sub-list ---- *)
Lemma kn_kslots_sub : forall cx W3 ms3 sl sl',
  kslots_eq cx W3 ms3 sl -> (forall ov, In ov sl' -> In ov sl) -> kslots_eq cx W3 ms3 sl'.
Proof.
  intros cx W3 ms3 sl sl' H Hs. unfold kslots_eq in *. rewrite Forall_forall in *.
  intros ov Hov. exact (H ov (Hs ov Hov)).
Qed.

(* the slots of a cut, kept where the memory did not change: slot bytes lie below s1 + 0xf8 *)
Lemma kn_kslots_keep : forall cx W3 ms3 ms' sl,
  kslots_eq cx W3 ms3 sl ->
  (forall ov, In ov sl -> forall i, 0 <= i < 8 ->
     aview SEGS (w_H W3) (ms_mem ms') (ksp1 cx + fst ov + i) = aview SEGS (w_H W3) (ms_mem ms3) (ksp1 cx + fst ov + i)) ->
  kslots_eq cx W3 ms' sl.
Proof.
  intros cx W3 ms3 ms' sl H Hk. unfold kslots_eq in *. rewrite Forall_forall in *.
  intros ov Hov. rewrite <- (H ov Hov). apply kk_rdword_agree. intros i Hi. exact (Hk ov Hov i Hi).
Qed.

(* ---- the read set's shadow bytes and values at a cut, from the call (LinkWalkShadow.v's classes) ---- *)

(* one byte's shadow fact moves from the call to a later AR state the step's akept reaches: LinkWalkShadow.v
   sbyte_transport without its group-visibility half (the cursor's 16 bytes carry no hull fact in kernel_apre) *)
Lemma kn_saddr_transport : forall lyc Sc (W : world SEGS) memc mdc ly2 S2 (W2 : world SEGS) mem2 md2 slo shi
    (E : Z -> Prop) x,
  AR SEGS B lyc Sc W memc mdc -> AR SEGS B ly2 S2 W2 mem2 md2 ->
  ly_stk_lo ly2 = ly_stk_lo lyc -> ly_stk_hi ly2 = ly_stk_hi lyc ->
  (forall b m, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly2 S2)) ->
  akept SEGS B lyc Sc W memc W2 mem2 slo shi E -> fmiss lyc Sc E ->
  sclass SEGS B lyc Sc x ->
  saddr (aview SEGS (w_H W) memc) x -> saddr (aview SEGS (w_H W2) mem2) x.
Proof.
  intros lyc Sc W memc mdc ly2 S2 W2 mem2 md2 slo shi E x HAR1 HAR2 Elo Ehi Hbl HK HE Hc Hs1.
  pose proof HAR1 as (M1 & _). pose proof HAR2 as (M2 & _).
  destruct Hc as [Hst | [(b & m & Hin & Hb) | [Hi | (c & q & Hin & Hf)]]].
  - pose proof (proj1 (Forall_forall _ _) (am_zshadow B ly2 S2 _ M2) (ly_stk_lo ly2, ly_stk_hi ly2 - ly_stk_lo ly2)
      ltac:(unfold zero_shadow_ranges; left; reflexivity)) as HZ.
    cbn [fst snd] in HZ. unfold zero_shadow, shadow_of_addr in HZ.
    pose proof (am_layout B ly2 S2 _ M2) as LO. destruct (lo_top _ LO) as (_ & _ & _ & _ & Pl & Ph & _).
    unfold page_aligned in Pl, Ph. rewrite Elo, Ehi in *.
    exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
    replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + ly_stk_lo lyc / 8 + (x / 8 - ly_stk_lo lyc / 8)) by lia.
    apply HZ. lia.
  - pose proof (Hbl b m Hin) as Hin2.
    destruct (al_shadow _ _ LAWS ly2 S2 W2 mem2 md2 b m HAR2 Hin2) as [HBS _].
    exact (block_shadow_range _ _ _ _ x 1 HBS ltac:(lia) ltac:(lia) x ltac:(lia)).
  - pose proof (pa_img_range x Hi) as Hi'. rewrite img_end_val in Hi'.
    assert (Hsx : SHADOW_OFF + 0x2000 <= shadow_of_addr SHADOW_OFF x < SHADOW_OFF + 0xca800)
      by (unfold shadow_of_addr; lia).
    destruct (img_sh_eq B TB lyc Sc _ ly2 S2 _ _ M1 M2 Hsx) as [Eq _].
    destruct Hs1 as (v & Hv & Hok). exists v. rewrite Eq. split; [exact Hv | exact Hok].
  - pose proof HK as (_ & _ & _ & K4 & _).
    destruct (frame_facts B lyc Sc _ c q M1 Hin) as (_ & _ & Happ & _ & PF & _ & _ & Hoff & H64 & Hb64 & _).
    unfold page_aligned in PF.
    assert (HF64 : frame_addr lyc c q mod 64 = 0) by (unfold frame_addr; lia).
    destruct Hs1 as (v & Hv & Hok). exists v. split; [|exact Hok].
    assert (Hsf : shadow_addr (frame_addr lyc c q) <= shadow_of_addr SHADOW_OFF x <
                  shadow_addr (frame_addr lyc c q) + fs_frame_bytes c / 8)
      by (unfold shadow_addr, shadow_of_addr, SHADOW_OFF in *; lia).
    rewrite (K4 c q (shadow_of_addr SHADOW_OFF x) Hin); [exact Hv | | exact (HE c q _ Hin Hsf)].
    right. unfold in_zr. cbn [fst snd]. exact Hsf.
Qed.

(* a read-set byte's shadow fact at a cut *)
Lemma kn_rd_saddr : forall cx fpos k2 ly3 S3 W3 ms3 md3 x,
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  kjbk B cx fpos k2 ly3 S3 md3 -> kkept B cx fpos W3 ms3 ->
  kernel_ard SEGS (k_regs cx) (km0 cx) x ->
  saddr (aview SEGS (w_H (k_W cx)) (k_memc cx)) x ->
  saddr (aview SEGS (w_H W3) (ms_mem ms3)) x.
Proof.
  intros cx fpos k2 ly3 S3 W3 ms3 md3 x HB HJ Hjb Hkk Hx Hs.
  pose proof HB as (HPRE & HRD & _). pose proof HPRE as (HJ0 & _).
  pose proof HJ0 as (_ & _ & (memS0 & HJi0 & _) & _). pose proof HJi0 as (HAR0 & _).
  pose proof HJ as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (HAR3 & _).
  destruct (aj_stk_row_eq SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as (R0lo & R0hi).
  destruct (aj_stk_row_eq SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (R3lo & R3hi).
  pose proof Hjb as (_ & _ & Hperm & Hnin & (S1 & W1 & mem1 & md1 & HAR1 & HF1 & _) & _).
  assert (Hin1 : In (KN_CID, fpos) (frames S1)) by (rewrite HF1; left; reflexivity).
  pose proof HAR1 as (M1 & _).
  destruct (frame_facts B _ _ _ KN_CID fpos M1 Hin1) as (_ & Hpos & _).
  destruct Hkk as (Hak & _).
  apply (kn_saddr_transport (k_lyc cx) (k_Sc cx) (k_W cx) (k_memc cx) (k_mdc cx) ly3 S3 W3 (ms_mem ms3) md3
    (ksp cx - KERNEL_AK) (ksp cx) (fun a => kE cx a \/ aside_rng (k_lyc cx) KN_CID fpos a) x HAR0 HAR3);
    [congruence | congruence | | exact Hak | | | exact Hs].
  - intros b m Hbm. apply (Permutation_in _ (Permutation_sym Hperm)). exact Hbm.
  - apply fmiss_or.
    + apply (fmiss_app SEGS B LAWS _ _ _ _ _ _ HAR0). intros a Ha.
      destruct (kn_ard_loc cx fpos k2 ly3 S3 md3 a HB Hjb (kn_kE_ard cx a Ha)) as (_ & Happ & _). exact Happ.
    + apply (fmiss_side SEGS B _ _ _ _ _ KN_CID fpos HAR0); [unfold KN_CID; lia | exact Hpos | exact Hnin].
  - exact (sclass_of_akb SEGS B _ _ _ _ x (HRD x Hx)).
Qed.

(* the cursor's 16 bytes are addressable at a cut *)
Lemma kn_cursor_ra : forall cx fpos k2 ly3 S3 W3 ms3 md3,
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  kjbk B cx fpos k2 ly3 S3 md3 -> kkept B cx fpos W3 ms3 ->
  range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF (ka0 cx) 16.
Proof.
  intros cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ Hjb Hkk.
  pose proof (kn_apre cx HB) as (_ & _ & Hra & _).
  apply ra_of_saddr. intros x Hx.
  apply (kn_rd_saddr cx fpos k2 ly3 S3 W3 ms3 md3 x HB HJ Hjb Hkk).
  - left. unfold ka0 in Hx. exact Hx.
  - apply (saddr_of_ra _ (ka0 cx) 16 x); [|exact Hx]. rewrite <- ard_aview. exact Hra.
Qed.

(* an input byte at a cut: its shadow fact, and its value the call's *)
Lemma kn_input_at : forall cx fpos k2 ly3 S3 W3 ms3 md3 x,
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  kjbk B cx fpos k2 ly3 S3 md3 -> kkept B cx fpos W3 ms3 ->
  k_wp cx <= x < k_wp cx + k_wn cx ->
  saddr (aview SEGS (w_H W3) (ms_mem ms3)) x /\
  aview SEGS (w_H W3) (ms_mem ms3) x = aview SEGS (w_H (k_W cx)) (k_memc cx) x.
Proof.
  intros cx fpos k2 ly3 S3 W3 ms3 md3 x HB HJ Hjb Hkk Hx.
  pose proof (kn_apre cx HB) as (_ & _ & _ & Hra & _ & Hap).
  pose proof HB as (HPRE & HRD & _ & _ & _ & HWP & HWN & HWPr & HWNr & _).
  pose proof HPRE as (HJ0 & _).
  assert (Hxa : kernel_ard SEGS (k_regs cx) (km0 cx) x).
  { right. left. exists (k_wp cx), (k_wn cx). unfold ka0 in *.
    exact (conj HWP (conj HWN (conj HWPr (conj HWNr Hx)))). }
  split.
  - apply (kn_rd_saddr cx fpos k2 ly3 S3 W3 ms3 md3 x HB HJ Hjb Hkk Hxa).
    apply (saddr_of_ra _ (k_wp cx) (k_wn cx) x); [|exact Hx]. rewrite <- ard_aview. exact Hra.
  - pose proof Hjb as (_ & _ & _ & Hnin & (S1 & W1 & mem1 & md1 & HAR1 & HF1 & _) & _).
    assert (Hin1 : In (KN_CID, fpos) (frames S1)) by (rewrite HF1; left; reflexivity).
    pose proof HAR1 as (M1 & _).
    destruct (frame_facts B _ _ _ KN_CID fpos M1 Hin1) as (_ & Hpos & _).
    destruct Hkk as (Hak & _).
    eapply (akept_akb_gx SK SEGS B); [exact HJ0 | exact Hak | exact (HRD x Hxa) |].
    intros [HE | HS].
    + unfold kE, inFP in HE. destruct HE as (r & Hin & Hr). unfold kernel_awr in Hin. cbn [In] in Hin.
      destruct Hap as (_ & Hg & Hl & Hc).
      unfold apart_gnl, apart in *. unfold NK_CHUNK, NK_OPEN, NK_SIZE, LONG_ALIAS_SIZE in *.
      destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr; lia.
    + exact (akb_not_side SK SEGS B pa_img_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KN_CID fpos x HJ0
        ltac:(unfold KN_CID; lia) Hpos Hnin (HRD x Hxa) HS).
Qed.

(* ---- the cursor and w2, kept where their bytes did not change ---- *)
Lemma kn_kcursor_keep : forall cx W3 ms3 ms' adv,
  kcursor cx W3 ms3 adv ->
  (forall i, 0 <= i < 16 ->
     aview SEGS (w_H W3) (ms_mem ms') (ka0 cx + i) = aview SEGS (w_H W3) (ms_mem ms3) (ka0 cx + i)) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) (ms_mem ms') a) ->
  kcursor cx W3 ms' adv.
Proof.
  intros cx W3 ms3 ms' adv (Hadv & HP & HN & HW) Hag Hpr.
  split; [exact Hadv|]. split; [|split].
  - apply (kn_val_mem_move W3 (ms_mem ms3) (ms_mem ms') _ 8 _ HP). intros i Hi. apply Hag. lia.
  - apply (kn_val_mem_move W3 (ms_mem ms3) (ms_mem ms') _ 8 _ HN). intros i Hi.
    replace (ka0 cx + 8 + i) with (ka0 cx + (8 + i)) by lia. apply Hag. lia.
  - intros i Hi. apply (writable_kept (w_H W3) (ms_mem ms3) (ms_mem ms') (ka0 cx + i) (Hpr _)). exact (HW i Hi).
Qed.

Lemma kn_kw_keep : forall W3 ms3 ms' w n f,
  kw_at W3 ms3 w n f ->
  (forall i, 0 <= i < NW_SIZE ->
     aview SEGS (w_H W3) (ms_mem ms') (w + i) = aview SEGS (w_H W3) (ms_mem ms3) (w + i)) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) (ms_mem ms') a) ->
  kw_at W3 ms' w n f.
Proof.
  intros W3 ms3 ms' w n f H Hag Hpr. unfold kw_at in *.
  apply (nlw_fields_agree SEGS _ _ w n f H). intros i Hi. split.
  - apply mbyte_of_aview. apply Hag. exact Hi.
  - intros Hw. exact (writable_kept (w_H W3) (ms_mem ms3) (ms_mem ms') (w + i) (Hpr _) Hw).
Qed.

Lemma kn_mbyte0 : forall (H : word -> bool) (m : word -> option byte) a,
  aview SEGS H m a = Some 0 -> mbyte SEGS (mrestrict H m) a = Some (Z_to_bv 8 0).
Proof.
  intros H m a Ha. unfold aview in Ha.
  destruct (mbyte SEGS (mrestrict H m) a) as [b|]; cbn [option_map] in Ha; [|discriminate Ha].
  injection Ha as Hb. rewrite <- Hb, Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* w2 after checked_memset(w2, 0, 4112): every byte 0, so n = 0 and full = 0 *)
Lemma kn_kw_zero : forall W3 ms' w,
  0 <= w -> w + NW_SIZE <= 2 ^ 64 ->
  (forall i, 0 <= i < NW_SIZE -> aview SEGS (w_H W3) (ms_mem ms') (w + i) = Some 0) ->
  (forall i, 0 <= i < NW_SIZE -> apresent (w_H W3) (ms_mem ms') (w + i)) ->
  kw_at W3 ms' w 0 0.
Proof.
  intros W3 ms' w H0 H1 Hz Hp. unfold kw_at, nlw_fields.
  split; [exact H0|]. split; [exact H1|]. split.
  { intros i Hi. split.
    - exists (Z_to_bv 8 0). exact (kn_mbyte0 _ _ _ (Hz i Hi)).
    - apply apresent_writable. exact (Hp i Hi). }
  split; [|split; [|unfold NL_CHUNK_MAX; lia]].
  - intros k Hk.
    destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; [| | | | | | | | lia];
      match goal with |- _ = Some (Z_to_bv 8 ?e) => change (Z_to_bv 8 e) with (Z_to_bv 8 0) end;
      apply kn_mbyte0; rewrite <- Z.add_assoc; apply Hz; unfold NW_N, NW_SIZE; lia.
  - intros k Hk.
    destruct k as [|[|[|[|k]]]]; [| | | | lia];
      match goal with |- _ = Some (Z_to_bv 8 ?e) => change (Z_to_bv 8 e) with (Z_to_bv 8 0) end;
      apply kn_mbyte0; rewrite <- Z.add_assoc; apply Hz; unfold NW_FULL, NW_SIZE; lia.
Qed.

(* ---- a cut at a state where the step also wrote F's shadow, the slots and the cursor: the new ones given ---- *)
Lemma kat_reframe : forall (X : Z -> Prop) cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3
    pc' rl' sl' sh' adv' W4 ms4 md4,
  kbase SK B cx ->
  kat B cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 ->
  kms pc' ms4 -> kregs0 cx ms4 -> kregs_eq ms4 rl' -> m_fds md4 = m_fds md3 -> m_fs md4 = m_fs md3 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview SEGS (w_H W4) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W4) (ms_mem ms4) a) ->
  (forall a, X a -> kX_in cx fpos a) ->
  (forall a, ksp cx - 104 <= a < ksp cx -> ~ X a) ->
  (forall a, kF cx fpos <= a < kF cx fpos + 24 -> ~ X a) ->
  (forall a, kF cx fpos + fs_frame_bytes KN_CID - 8 <= a < kF cx fpos + fs_frame_bytes KN_CID -> ~ X a) ->
  (forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> ~ X a) ->
  (forall a, LA_LONG_ALIAS <= a < LA_LONG_ALIAS + LONG_ALIAS_SIZE -> ~ X a) ->
  kshadow cx fpos W4 ms4 sh' -> kslots_eq cx W4 ms4 sl' -> kcursor cx W4 ms4 adv' ->
  kat B cx fpos pc' rl' sl' sh' live adv' g k2 ly3 S3 W4 ms4 md4.
Proof.
  intros X cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 pc' rl' sl' sh' adv' W4 ms4 md4
    HB HK HMS HR0 HRL Hfds Hfs UN HP HXin Msv Mhd Mfl Mgn Mla HSH' HSL' HCUR'.
  destruct HK as (_ & _ & _ & HSAV & HFR & _ & _ & HJB & HKEPT & _ & HGNL & HLA).
  unfold kat.
  refine (conj HMS (conj HR0 (conj HRL (conj _ (conj _ (conj HSH' (conj HSL' (conj _ (conj _ (conj HCUR'
    (conj _ _))))))))))).
  - exact (ksaved_frame X cx W3 ms3 W4 ms4 HB UN Msv HSAV).
  - exact (kframe_frame X cx fpos live k2 ly3 S3 md3 W3 ms3 W4 ms4 HJB UN HP Mhd Mfl HFR).
  - exact (kjbk_md cx fpos k2 ly3 S3 md3 md4 HJB Hfds Hfs).
  - exact (kkept_frame X cx fpos k2 ly3 S3 md3 W3 ms3 W4 ms4 HB HJB UN HP HXin HKEPT).
  - exact (kgnl_frame X cx g W3 ms3 W4 ms4 UN HP Mgn HGNL).
  - exact (kla_frame X W3 ms3 W4 ms4 UN HP Mla HLA).
Qed.

(* kernel_msg0_kit.v's move (kat_move): a cut at a state whose memory is the old one's outside kn_X (the
   window below s1 + 0xf8, the cursor, w2, w2's shadow bytes), with the new F shadow, slots and cursor *)
Lemma kn_kat_move_X : forall cx fpos pc rl sl sh adv g k2 ly3 S3 W3 ms3 md3 pc' rl' sl' sh' adv' ms' md',
  kbase SK B cx ->
  kat B cx fpos pc rl sl sh true adv g k2 ly3 S3 W3 ms3 md3 ->
  kms pc' ms' -> kregs0 cx ms' -> kregs_eq ms' rl' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ kn_X cx fpos a ->
     aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) (ms_mem ms') a) ->
  kshadow cx fpos W3 ms' sh' -> kslots_eq cx W3 ms' sl' -> kcursor cx W3 ms' adv' ->
  m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  kat B cx fpos pc' rl' sl' sh' true adv' g k2 ly3 S3 W3 ms' md'.
Proof.
  intros cx fpos pc rl sl sh adv g k2 ly3 S3 W3 ms3 md3 pc' rl' sl' sh' adv' ms' md'
    HB HK Hms' Hr0' Hrl' UN HP Hsh' Hsl' Hcur' Hfds Hfs.
  pose proof HK as (_ & _ & _ & _ & _ & _ & _ & Hjb & _).
  pose proof (kn_sp cx HB) as (S1 & S2 & _ & S4 & _).
  pose proof (kn_F cx fpos k2 ly3 S3 md3 HB Hjb) as (F1 & F2 & F3 & F4).
  pose proof (kn_apre cx HB) as (Agnl & Ala & _).
  assert (HK4 : KERNEL_AK = 4640) by reflexivity.
  assert (Hfb : fs_frame_bytes KN_CID = 16384) by reflexivity.
  apply (kat_reframe (kn_X cx fpos) cx fpos pc rl sl sh true adv g k2 ly3 S3 W3 ms3 md3 pc' rl' sl' sh' adv'
           W3 ms' md' HB HK Hms' Hr0' Hrl' Hfds Hfs UN HP); [| | | | | | exact Hsh' | exact Hsl' | exact Hcur'].
  - intros a Ha. destruct Ha as [H|[H|[H|H]]].
    + right; right; right. lia.
    + left. unfold kE, inFP. exists (aarg (k_regs cx) 0, aarg (k_regs cx) 0 + 16).
      split; [cbn [In kernel_awr]; right; right; left; reflexivity|].
      cbn [fst snd]. unfold ka0 in H. exact H.
    + right; left. unfold kW2, KN_W2, NW_SIZE in H. lia.
    + right; right; left. lia.
  - intros a Ha. apply (kn_X_hi cx fpos k2 ly3 S3 md3 a HB Hjb). lia.
  - intros a Ha. apply (kn_X_F cx fpos k2 ly3 S3 md3 a HB Hjb); [lia | unfold kW2, KN_W2, NW_SIZE; lia].
  - intros a Ha. apply (kn_X_F cx fpos k2 ly3 S3 md3 a HB Hjb); [lia | unfold kW2, KN_W2, NW_SIZE; lia].
  - intros a Ha. apply (kn_X_ard cx fpos k2 ly3 S3 md3 a HB Hjb).
    + unfold kernel_ard. right. right. left. exact Ha.
    + unfold apart_gnl in Agnl. lia.
  - intros a Ha. apply (kn_X_ard cx fpos k2 ly3 S3 md3 a HB Hjb).
    + unfold kernel_ard. do 9 right. left. exact Ha.
    + unfold apart, LONG_ALIAS_SIZE in Ala. unfold LONG_ALIAS_SIZE in Ha. lia.
Qed.

(* ---- writability across a step whose contract keeps presence only above the allocator's ceiling (frame_alloc_8,
   frame_release_8): kernel_exit_post.v kx_writable_of_view, and the carry the kernel walk's lead asked for ---- *)

(* A VISIBLE byte that is not read-only is WRITABLE, at any memory.  `wview` and `seg_rom` pick the same segment
   (the first one holding the address), so a byte the view reads out of the segments lies in a segment whose
   bytes are there; `~ in_roP` says that segment is writable. *)
Lemma kn_writable_of_view : forall (H : word -> bool) (m : word -> option byte) a,
  0 <= a < 2 ^ 64 -> aview SEGS H m a <> None -> ~ in_roP SEGS PCAP_RLO PCAP_RHI a ->
  writable_at SEGS (mrestrict H m) a.
Proof.
  intros H m a Ha Hv Hro.
  assert (Hu : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; lia).
  unfold writable_at, wview.
  destruct (mrestrict H m (Z_to_bv 64 a)) as [b0|] eqn:Em; [discriminate|].
  unfold aview, mbyte in Hv. rewrite Em in Hv.
  destruct (seg_rom SEGS (Z_to_bv 64 a)) as [b1|] eqn:Er; [|cbn [option_map] in Hv; exfalso; exact (Hv eq_refl)].
  clear Hv. unfold seg_rom, memory_read in Er. change (Z.of_N 1) with 1 in Er.
  destruct (find_segment SEGS (bv_unsigned (Z_to_bv 64 a)) 1) as [seg|] eqn:Ef; [|discriminate Er].
  destruct (seg_readable seg) eqn:Erd; [|discriminate Er].
  destruct (find_segment_hit SEGS (bv_unsigned (Z_to_bv 64 a)) 1 seg Ef) as (Hin & Hlo & Hhi).
  rewrite Hu in Hlo, Hhi.
  assert (Hw : seg_writable seg = true).
  { destruct (seg_writable seg) eqn:Ew; [reflexivity|].
    exfalso. apply Hro. left. exists seg. split; [exact Hin | split; [exact Ew | lia]]. }
  rewrite Hw.
  change (N.to_nat 1) with 1%nat in Er. cbn [segment_read_bytes] in Er.
  destruct (segment_byte_at (seg_bytes seg)
              (Z.to_N (bv_unsigned (Z_to_bv 64 a) - Z.of_N (seg_base seg)))) as [b2|] eqn:Eb;
    [discriminate | cbn in Er; discriminate Er].
Qed.

(* a writable byte the step leaves as it was (the same view) and that is not read-only stays writable *)
Lemma kn_wr_keep : forall (H H' : word -> bool) (m m' : word -> option byte) a,
  0 <= a < 2 ^ 64 ->
  writable_at SEGS (mrestrict H m) a -> aview SEGS H' m' a = aview SEGS H m a ->
  ~ in_roP SEGS PCAP_RLO PCAP_RHI a -> writable_at SEGS (mrestrict H' m') a.
Proof.
  intros H H' m m' a Ha Hw Hv Hro.
  destruct (aview SEGS H m a) as [v|] eqn:Ev.
  - apply kn_writable_of_view; [exact Ha | rewrite Hv; discriminate | exact Hro].
  - assert (E1 : mrestrict H m (Z_to_bv 64 a) = None).
    { destruct (mrestrict H m (Z_to_bv 64 a)) as [b|] eqn:E; [|reflexivity].
      exfalso. unfold aview, mbyte in Ev. rewrite E in Ev. discriminate Ev. }
    assert (E2 : mrestrict H' m' (Z_to_bv 64 a) = None).
    { destruct (mrestrict H' m' (Z_to_bv 64 a)) as [b|] eqn:E; [|reflexivity].
      exfalso. unfold aview, mbyte in Hv. rewrite E in Hv. discriminate Hv. }
    unfold writable_at, wview in Hw |- *. rewrite E1 in Hw. rewrite E2. exact Hw.
Qed.

(* the same for a range (awrange: the cursor's 16 bytes, a buffer) *)
Lemma kn_awrange_keep : forall (H H' : word -> bool) (m m' : word -> option byte) a n,
  0 <= a -> a + n <= 2 ^ 64 -> awrange SEGS (mrestrict H m) a n ->
  (forall i, 0 <= i < n -> aview SEGS H' m' (a + i) = aview SEGS H m (a + i)) ->
  (forall i, 0 <= i < n -> ~ in_roP SEGS PCAP_RLO PCAP_RHI (a + i)) ->
  awrange SEGS (mrestrict H' m') a n.
Proof.
  intros H H' m m' a n H0 Hn Hw Hv Hro i Hi.
  exact (kn_wr_keep H H' m m' (a + i) ltac:(lia) (Hw i Hi) (Hv i Hi) (Hro i Hi)).
Qed.

(* ---- a buffer of F whose 0x202 shadow bytes are 0 is addressable (the instrumented checks on w1 / w2) ---- *)
Lemma kn_wbuf_ra : forall cx fpos k2 ly3 S3 md3 W3 ms3 sh j,
  kjbk B cx fpos k2 ly3 S3 md3 -> kshadow cx fpos W3 ms3 sh -> 0 <= j -> j + 514 <= Z.of_nat (length sh) ->
  (forall i : nat, j <= Z.of_nat i < j + 514 -> nth i sh 0 = 0) ->
  range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF (kF cx fpos + 8 * j) NW_SIZE.
Proof.
  intros cx fpos k2 ly3 S3 md3 W3 ms3 sh j HJB HSH Hj0 Hjl Hz x Hx.
  destruct (kn_F_facts cx fpos k2 ly3 S3 md3 HJB) as (HF4 & _ & _ & H64 & _).
  unfold NW_SIZE in Hx.
  assert (Hi : j <= x / 8 - kF cx fpos / 8 < j + 514) by lia.
  pose proof (HSH (Z.to_nat (x / 8 - kF cx fpos / 8)) ltac:(lia)) as Hb.
  rewrite (Hz (Z.to_nat (x / 8 - kF cx fpos / 8))) in Hb by lia.
  rewrite Z2Nat.id in Hb by lia.
  exists 0. split; [|left; reflexivity].
  unfold kFSH, shadow_of_addr in Hb |- *.
  replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + kF cx fpos / 8 + (x / 8 - kF cx fpos / 8)) by lia.
  exact Hb.
Qed.

(* w2 at a cut whose F shadow is kfsh _ 0 _ (the message path) *)
Lemma kn_w2_ra : forall cx fpos k2 ly3 S3 md3 W3 ms3 s1v r,
  kjbk B cx fpos k2 ly3 S3 md3 -> kshadow cx fpos W3 ms3 (kfsh s1v 0 r) ->
  range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF (kW2 cx fpos) NW_SIZE.
Proof.
  intros cx fpos k2 ly3 S3 md3 W3 ms3 s1v r HJB HSH.
  replace (kW2 cx fpos) with (kF cx fpos + 8 * 550) by (unfold kW2, KN_W2; lia).
  apply (kn_wbuf_ra cx fpos k2 ly3 S3 md3 W3 ms3 _ 550 HJB HSH); [lia | rewrite kfsh_length; lia |].
  intros i Hi. rewrite kn_kfsh_nth.
  destruct (Nat.ltb_spec i 4); [lia|]. destruct (Nat.ltb_spec i 0x206); [lia|].
  destruct (Nat.ltb_spec i 0x226); [lia|]. destruct (Nat.ltb_spec i 0x428); [reflexivity | lia].
Qed.

(* w1 at a cut whose F shadow is kfsh 0 _ _ (the raw path) *)
Lemma kn_w1_ra : forall cx fpos k2 ly3 S3 md3 W3 ms3 s2v r,
  kjbk B cx fpos k2 ly3 S3 md3 -> kshadow cx fpos W3 ms3 (kfsh 0 s2v r) ->
  range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF (kW1 cx fpos) NW_SIZE.
Proof.
  intros cx fpos k2 ly3 S3 md3 W3 ms3 s2v r HJB HSH.
  replace (kW1 cx fpos) with (kF cx fpos + 8 * 4) by (unfold kW1, KN_W1; lia).
  apply (kn_wbuf_ra cx fpos k2 ly3 S3 md3 W3 ms3 _ 4 HJB HSH); [lia | rewrite kfsh_length; lia |].
  intros i Hi. rewrite kn_kfsh_nth.
  destruct (Nat.ltb_spec i 4); [lia|]. destruct (Nat.ltb_spec i 0x206); [reflexivity | lia].
Qed.

End b.
End a.

Print Assumptions kat_frame.
Print Assumptions kn_ard_not_side.
Print Assumptions kat_frame_w2s.
Print Assumptions kn_kat_move_X.
Print Assumptions kn_input_at.
