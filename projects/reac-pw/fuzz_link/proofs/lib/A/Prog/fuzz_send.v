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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/fuzz_recv_entry.v, with its numbers changed; 1188 of its 1305 lines of code are new or changed and 608 lines of the source are left out. *)
(* fuzz_send on image A (fuzz_link.asan 0x82290, listing offset AF_fuzz_send = 0xc4; listing
   (internal path) (internal record, sha256 a64d77d6e373)): the walk of its contract
   lib/A/Prog/fuzz_send_c.v `fuzz_send_acontract` (link_amem.v `aleaf_rd`, K = 48 + ESTACK = 4144, EV 0, SIDE []).

   The walk runs the image's instructions symbolically at link's listing on the caller's journal ajournal_gx
   (LinkWalkErrno.v paj_run_xe / paj_run_to_xe, LinkPaLib.v tactics):
   - entry state fs_ss: the 48-byte frame (stack_region 48), the .got word of the shadow base and its cell, and
     g_nl's send_errno, open, misuse and n_sent words (atoms 33, 34, 36, 35; g_nl's address is the image atom
     A_OBJ 2). Two aliases name the two addresses the code forms from n = n_sent: sent_len[n] = g + 0x42228 + 8 n
     (atom 37) and sent[n] = g + 0x40224 + 512 n (atom 38).
   - +0x30 `bne a0, 7` (the whole register) and +0x40 `bnez` on open: three ways to +0x64, two of them storing
     misuse := 1 at +0x50. Each is brought to the one state SS64 (a3 forgotten, open's and misuse's words dropped,
     the branch conditions dropped); misuse's word is carried as a val_mem fact.
   - +0x64 `beqz s3` on send_errno:
     * not 0: the call +0x68 of ___errno_location (LinkWalkErrno.v aj_gx_errno_at), then a 4-byte region at
       a0 = tp - 164 = errno with its shadow entry, the instrumented check +0x6c..+0x78, the store +0x7c to errno,
       send_errno := 0, a0 := -1, `ret`;
     * 0: +0xa4 `blt 15, n`: a full ring returns len at once; else +0xb0 `bltu len, 512` (both ways reach +0xb8
       with a2 = len, as len <= 512), the call +0xcc of checked_memcpy(g + 0x40224 + 512 n, buf, len)
       (link_ajkit.v aj_gx_intrin_at), n_sent := n + 1, the instrumented check +0xf4..+0x100 of sent_len[n] and its
       store +0x104, `ret`.
   - each path ends at LinkWalk.v apost_leaf (the errno path through LinkWalkErrno.v apost_errno); the Post's g_nl
     list is the end memory's (LinkWalkNlk.v anlk_after) and lib/A/Prog/fuzz_send_post.v gives its fields.

   Section hypotheses: LAWS, TL (PALib), LV (LinkVals) are the image instance's facts (as fuzz_socket.v); ERRF
   (errno is not in the runtime's owned static table), discharged on the image by LinkWalkErrnoInst.v
   `link_errno_not_static`; ERRNO, ___errno_location's contract, by lib/A/Rt/RtErrnoLocClosed.v
   `link_errno_location_closed` (0x90a7c); MEMCPY, checked_memcpy's contract, by lib/A/AE2q.v
   `asan_memcpy_realizes` (0x52d78).

   Proves fuzz_send (kind: function proof). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality Classical.
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import RtErrnoLoc.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC81 YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkNlk LinkWalkErrno fuzz_send_c fuzz_send_post.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ---- the states ---------------------------------------------------------- *)
Definition fs_se : YP09.region := YP09.mkRegion (Some (A_OBJ 2)) 262672 262676 262672 262676
  [YP09.mkChunk 262672 (CVal 4 (SOff 33 0))].
Definition fs_op : YP09.region := YP09.mkRegion (Some (A_OBJ 2)) 262676 262680 262676 262676
  [YP09.mkChunk 262676 (CVal 4 (SOff 34 0))].
Definition fs_mi : YP09.region := YP09.mkRegion (Some (A_OBJ 2)) 262688 262692 262688 262692
  [YP09.mkChunk 262688 (CVal 4 (SOff 36 0))].
Definition fs_ns : YP09.region := YP09.mkRegion (Some (A_OBJ 2)) 271016 271020 271016 271020
  [YP09.mkChunk 271016 (CVal 4 (SOff 35 0))].
Definition fs_regions : smem := [stack_region 48; got_regionP; bcell_regionP 32; fs_se; fs_op; fs_mi; fs_ns].
(* sent_len[n] and sent[n], as the code forms them from n = n_sent *)
Definition fs_aX : sv := SAlu ALU_ADD (SOff (A_OBJ 2) 270888) (SAlu ALU_SLL (SOff 35 0) (SLit 3)).
Definition fs_aD : sv := SAlu ALU_ADD (SOff (A_OBJ 2) 262692) (SAlu ALU_SLL (SOff 35 0) (SLit 9)).
Definition fs_atoms : list (nat * afact) :=
  [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0); (A_OBJ 2, mkAF LA_G_NL LA_G_NL 0);
   (12%nat, mkAF 0 512 0); (33%nat, mkAF 0 (2 ^ 31 - 1) 0); (34%nat, mkAF 0 1 0);
   (35%nat, mkAF 0 16 0); (36%nat, mkAF 0 1 0); (37%nat, mkAF (LA_G_NL + 270888) (LA_G_NL + 271016) 3)].
Definition fs_facts : facts := mkFacts fs_atoms [] [(fs_aX, SOff 37 0); (fs_aD, SOff 38 0)].
Definition fs_ss : sstate := mkSS AF_fuzz_send sr_atoms fs_regions None fs_facts.
Definition fs_extra (bs : list byte) : list word :=
  map (Z_to_bv 64) [SB; nk_send_errno bs; nk_open bs; nk_n_sent bs; nk_misuse bs;
                    LA_G_NL + 270888 + 8 * nk_n_sent bs; LA_G_NL + 262692 + 512 * nk_n_sent bs].

(* the frame after the push (+0x04..+0x14 save ra, s0..s3) *)
Definition fs_stk48 : YP09.region := YP09.mkRegion (Some 2%nat) (-48) 0 (-48) 0
  [YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
   YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
   YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
Definition fs_rest : smem := [fs_stk48; got_regionP; bcell_regionP 32; fs_se; fs_ns].
(* +0x64: the one state the three ways reach (a3 forgotten to atom 40) *)
Definition fs_regs64 : list sv :=
  [SLit 0; SOff 1 0; SOff 2 (-48); SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0; SOff 12 0; SOff 243 0;
   SOff 243 262144; SOff 11 0; SOff 305 0; SOff 40 0; SOff 323 0; SOff 15 0; SOff 16 0; SOff 17 0;
   SOff 32 0; SOff 33 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0;
   SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].
Definition SS64 : sstate := mkSS (AF_fuzz_send + 0x64) fs_regs64 fs_rest None fs_facts.
(* +0xb8: the one state both ways of the clamp reach (a2 = len) *)
Definition fs_regsB8 : list sv :=
  [SLit 0; SOff 1 0; SOff 2 (-48); SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0; SOff 12 0; SOff 243 0;
   SOff 35 0; SOff 11 0; SOff 40 0; SLit 512; SOff 323 0; SOff 15 0; SOff 16 0; SOff 17 0;
   SOff 32 0; SOff 33 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0;
   SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].
Definition SSB8 : sstate := mkSS (AF_fuzz_send + 0xb8) fs_regsB8 fs_rest None fs_facts.
(* after ___errno_location: errno's 4 bytes at a0's havoc atom 48 + 4 *)
Definition fs_er : YP09.region := YP09.mkRegion (Some 52%nat) 0 4 0 4 [].
Definition fs_erSH : list shent := [mkSHE 52 0 4].
(* after checked_memcpy: sent_len[n] at atom 37 *)
Definition fs_X : YP09.region := YP09.mkRegion (Some 37%nat) 0 8 0 8 [].
Definition fs_XSH : list shent := [mkSHE 37 0 8].

(* the bytes a run of fuzz_send may change: the 4144 bytes below sp (the frame and checked_memcpy's window), the
   bytes of g_nl at the offsets P, and Er (errno, or nothing) *)
Definition fs_Zs (sp : Z) (P Er : Z -> Prop) (a : Z) : Prop :=
  (sp - 4144 <= a < sp) \/ (LA_G_NL <= a < LA_G_NL + NK_SIZE /\ P (a - LA_G_NL)) \/ Er a.
Definition NoE (a : Z) : Prop := False.
(* the g_nl offsets the code writes after +0x64: send_errno and n_sent, and on the recording path sent[n] (len bytes)
   and sent_len[n] *)
Definition P_sn (i : Z) : Prop := (NK_SEND_ERRNO <= i < NK_SEND_ERRNO + 4) \/ (NK_N_SENT <= i < NK_N_SENT + 4).
Definition P_cp (n len i : Z) : Prop := P_sn i \/ (NK_SENT + NL_SENT_LEN * n <= i < NK_SENT + NL_SENT_LEN * n + len)
  \/ (NK_SENT_LEN + 8 * n <= i < NK_SENT_LEN + 8 * n + 8).

Lemma fs_Zs_mono : forall sp (P Q Er Er' : Z -> Prop) a, (forall i, P i -> Q i) -> (forall x, Er x -> Er' x) ->
  fs_Zs sp P Er a -> fs_Zs sp Q Er' a.
Proof. intros sp P Q Er Er' a HP HE [H | [[H1 H2] | H]]; [left | right; left | right; right]; auto. Qed.
Lemma NoE_any : forall (Er : Z -> Prop) x, NoE x -> Er x.
Proof. intros Er x H. exact (False_ind _ H). Qed.
Lemma Psn_cp : forall n len i, P_sn i -> P_cp n len i.
Proof. intros n len i H. left. exact H. Qed.
Lemma Pz_cp : forall n len i, P_sn i \/ (NK_SENT_LEN + 8 * n <= i < NK_SENT_LEN + 8 * n + 8) -> P_cp n len i.
Proof. intros n len i [H | H]; [left; exact H | right; right; exact H]. Qed.
Lemma Pbase_copy : forall n len i, P_base i -> P_copy n len i.
Proof. intros n len i H. left. exact H. Qed.
Lemma Pcp_copy : forall n len i, P_cp n len i -> P_copy n len i.
Proof. intros n len i [H | H]; [left; unfold P_sn, P_base in *; tauto | right; exact H]. Qed.

(* every byte of such a set lies in the window or below the shadow *)
Lemma fs_Zs_lowhigh : forall sp (P Er : Z -> Prop) a, (forall x, Er x -> x < SHADOW_OFF) ->
  fs_Zs sp P Er a -> sp - 4144 <= a \/ a < SHADOW_OFF.
Proof.
  intros sp P Er a HE [H | [[H _] | H]]; [left; lia | right; unfold LA_G_NL, NK_SIZE, SHADOW_OFF in *; lia |].
  right. exact (HE a H).
Qed.

Lemma fs_grows_of_present : forall (H : word -> bool) (m m' : word -> option byte),
  (forall a, apresent H m a -> apresent H m' a) -> mem_grows (mrestrict H m) (mrestrict H m').
Proof.
  intros H m m' Hp x Hx. unfold mrestrict in *. destruct (H x) eqn:Hh; [exact Hx|].
  destruct (m x) as [b|] eqn:Hm; [|contradiction].
  assert (Ha : apresent H m (bv_unsigned x))
    by (split; rewrite Z_to_bv_bv_unsigned; [exact Hh | exists b; exact Hm]).
  destruct (Hp _ Ha) as [_ [b' Hb']]. rewrite Z_to_bv_bv_unsigned in Hb'. rewrite Hb'. discriminate.
Qed.

Lemma fs_val_some : forall segs m a (n : nat) v, val_mem segs m a n v ->
  forall j, a <= j < a + Z.of_nat n -> exists b, mbyte segs m j = Some b.
Proof.
  intros segs m a n v H j Hj.
  pose proof (H (Z.to_nat (j - a)) ltac:(lia)) as Hb.
  replace (a + Z.of_nat (Z.to_nat (j - a))) with j in Hb by lia.
  eexists; exact Hb.
Qed.

Lemma fs_abytes_unique : forall segs m a l1 l2,
  abytes segs m a l1 -> abytes segs m a l2 -> length l1 = length l2 -> l1 = l2.
Proof.
  intros segs m a l1 l2 (_ & _ & H1) (_ & _ & H2) Hl.
  apply lw_list_ext; [exact Hl|]. intros k Hk. rewrite <- (H1 k Hk), <- (H2 k ltac:(lia)). reflexivity.
Qed.

Lemma fs_region_kept_same : forall segs E m r, region_kept segs E m m r.
Proof. intros segs E m r. split; intros a Ha; [reflexivity | intros H; exact H]. Qed.

Ltac zrng := try change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); try change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32);
  try change (Z.of_N 8) with 8; try change (Z.of_N 4) with 4; lia.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis LV : LinkVals.
Hypothesis ERRF : forall a, as_errno B <= a < as_errno B + 4 -> ~ Exists (in_zr a) (as_owned_static B).
Hypothesis ERRNO : aerrno_location_realizes SEGS B (pa_sigma LS____errno_location).
Hypothesis MEMCPY : aintrin_realizes SEGS B OCpy (pa_sigma LS___asan_memcpy).

Lemma fs_vals : VAL (A_OBJ 1) = 0xa19d0 /\ VAL (A_OBJ 2) = LA_G_NL /\ VAL (A_OBJ 64) = 0xaa438 /\
  BASE = 0x821cc /\ pa_sigma LS____errno_location = 0x90a7c /\ pa_sigma LS___asan_memcpy = 0x52d78.
Proof.
  split; [rewrite (lv_obj LV 1) by (unfold link_nobj; lia); reflexivity|].
  split; [rewrite (lv_obj LV 2) by (unfold link_nobj; lia); reflexivity|].
  split; [rewrite (lv_obj LV 64) by (unfold link_nobj; lia); reflexivity|].
  split; [exact (lv_text LV)|].
  split; rewrite (lv_sigma LV); reflexivity.
Qed.

Lemma fs_U243 : forall E, img_env VAL A_LIM E -> bv_unsigned (ew E 243) = LA_G_NL.
Proof.
  intros E HE. change 243%nat with (A_OBJ 2). rewrite (HE (A_OBJ 2) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  destruct fs_vals as (_ & V2 & _). exact V2.
Qed.

Lemma st_ok_pi_region : forall E ss ms i r,
  st_ok_pi SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok SEGS E (ms_mem ms) r.
Proof. intros E ss ms i r HS Hi. exact (st_ok_region_nth (segs := SEGS) E (abs_ss VAL ss) ms i r HS Hi). Qed.

(* the two aliases of fs_facts *)
Lemma fs_alias : forall E (n : Z),
  bv_unsigned (ew E 243) = LA_G_NL -> ew E 35 = Z_to_bv 64 n -> 0 <= n <= 16 ->
  ew E 37 = Z_to_bv 64 (LA_G_NL + 270888 + 8 * n) -> ew E 38 = Z_to_bv 64 (LA_G_NL + 262692 + 512 * n) ->
  sv_denot E fs_aX = sv_denot E (SOff 37 0) /\ sv_denot E fs_aD = sv_denot E (SOff 38 0).
Proof.
  intros E n Hg H35 Hn H37 H38. unfold fs_aX, fs_aD.
  assert (Un : bv_unsigned (ew E 35) = n) by (rewrite H35; apply unsigned_lit_small; lia).
  split; apply U_inj; rewrite U_SAlu; cbn [zalu_raw]; rewrite U_SAlu; cbn [zalu_raw];
    rewrite !U_SOff, !U_SLit; [rewrite H37 | rewrite H38]; change (A_OBJ 2) with 243%nat; rewrite Hg, Un;
    rewrite !unsigned_lit_small by (unfold LA_G_NL; lia).
  - change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
    unfold zcanon, M64, LA_G_NL. lia.
  - change (Z.land (zcanon 9) 63) with 9. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 9) with 512.
    unfold zcanon, M64, LA_G_NL. lia.
Qed.

(* THE ENTRY STATE *)
Lemma fs_entry : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) bs,
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - 48 -> spZ regs <= sp0 ->
  anlk_at SEGS (rdW W memc) LA_G_NL bs -> nlk_wf bs -> 0 <= bv_unsigned (getr regs 12) <= 512 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (fs_extra bs))) fs_ss
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_fuzz_send)) memc (seg_rom SEGS))).
Proof.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs bs HJ H16 Hwlo Hwhi HNK WF HL5.
destruct HJ as (HSTK & HXO & (memS & HJi & _) & _).
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL) in Kgot. rewrite (pal_cell B TL) in Kgot, Kcell.
destruct fs_vals as (V1 & V2 & V64 & VB & _).
rewrite V1, V64 in Kgot. rewrite V64 in Kcell.
pose proof WF as (Wnc & Wnx & Wns & Wni & Wop & Won & Wcl & Wmi & Wee & Wse & Wsd & _ & _).
pose proof HNK as [[Hab Hwr] HL].
assert (Hfld : forall off v, 0 <= off -> off + 4 <= NK_SIZE -> rdn bs off 4 = v ->
          val_mem SEGS (rdW W memc) (LA_G_NL + off) 4 v).
{ intros off v H0 H1 <-. exact (anlk_field SEGS (rdW W memc) LA_G_NL bs off 4 HNK H0 H1). }
set (E := Eimg (Ereg regs (fs_extra bs))).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (fs_extra bs)) n)
  by (intros n Hn; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E12 : ew E 12 = getr regs 12) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 12 12%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (nk_send_errno bs)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (nk_open bs)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (nk_n_sent bs)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (nk_misuse bs)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 (LA_G_NL + 270888 + 8 * nk_n_sent bs))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 (LA_G_NL + 262692 + 512 * nk_n_sent bs))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6)).
assert (Eg : ew E (A_OBJ 2) = Z_to_bv 64 LA_G_NL)
  by (unfold E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V2; reflexivity).
assert (Egot : ew E (A_OBJ 1) = Z_to_bv 64 0xa19d0)
  by (unfold E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V1; reflexivity).
assert (Ecell : ew E (A_OBJ 64) = Z_to_bv 64 0xaa438)
  by (unfold E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V64; reflexivity).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Ug : bv_unsigned (ew E 243) = LA_G_NL)
  by (change 243%nat with (A_OBJ 2); rewrite Eg; apply unsigned_lit_small; unfold LA_G_NL; lia).
assert (VBv : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
unfold NL_SENT_MAX in Wns.
rewrite restrict_mkst_fx. unfold fs_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold fs_regions, stack_region, got_regionP, bcell_regionP, fs_se, fs_op, fs_mi, fs_ns.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. fold E. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + fold E. rewrite (VBv _ _ Egot) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ 0xa19d0 0 8 (SOff (A_OBJ 64) 0) 0xaa438);
      [cbn [sv_denot]; rewrite Ecell, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zrng | zrng |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
  + fold E. rewrite (VBv _ _ Ecell) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ 0xaa438 0 8 (SOff 32 0) SB);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zrng | zrng |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
  + fold E. rewrite (VBv _ _ Eg) by (unfold LA_G_NL; lia).
    split; [unfold LA_G_NL; lia|]. split; [unfold LA_G_NL; lia|].
    split; [intros o Ho; apply Hwr; rewrite HL; unfold NK_SIZE; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ LA_G_NL 262672 4 (SOff 33 0) (nk_send_errno bs));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zrng | zrng |].
    apply Hfld; [lia | unfold NK_SIZE; lia | reflexivity].
  + fold E. rewrite (VBv _ _ Eg) by (unfold LA_G_NL; lia).
    split; [unfold LA_G_NL; lia|]. split; [unfold LA_G_NL; lia|].
    split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ LA_G_NL 262676 4 (SOff 34 0) (nk_open bs));
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zrng | zrng |].
    apply Hfld; [lia | unfold NK_SIZE; lia | reflexivity].
  + fold E. rewrite (VBv _ _ Eg) by (unfold LA_G_NL; lia).
    split; [unfold LA_G_NL; lia|]. split; [unfold LA_G_NL; lia|].
    split; [intros o Ho; apply Hwr; rewrite HL; unfold NK_SIZE; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ LA_G_NL 262688 4 (SOff 36 0) (nk_misuse bs));
      [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zrng | zrng |].
    apply Hfld; [lia | unfold NK_SIZE; lia | reflexivity].
  + fold E. rewrite (VBv _ _ Eg) by (unfold LA_G_NL; lia).
    split; [unfold LA_G_NL; lia|]. split; [unfold LA_G_NL; lia|].
    split; [intros o Ho; apply Hwr; rewrite HL; unfold NK_SIZE; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ LA_G_NL 271016 4 (SOff 35 0) (nk_n_sent bs));
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zrng | zrng |].
    apply Hfld; [lia | unfold NK_SIZE; lia | reflexivity].
- apply pairwise_disjoint_of_extents.
  unfold fs_regions, stack_region, got_regionP, bcell_regionP, fs_se, fs_op, fs_mi, fs_ns, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  fold E. rewrite (VBv _ _ Egot), (VBv _ _ Ecell), (VBv _ _ Eg) by (unfold LA_G_NL; lia).
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold LA_G_NL.
  repeat split; lia.
- unfold fs_facts. split; [|split; [exact I|]].
  + cbn [fs_atoms f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    fold E. rewrite Usp, E32, E33, E34, E35, E36, E37, Eg, E12.
    rewrite !unsigned_lit_small by (unfold SB, LA_G_NL; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB, LA_G_NL.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
  + cbn [f_alias alias_ok]. fold E.
    destruct (fs_alias E (nk_n_sent bs) Ug E35 ltac:(lia) E37 E38) as [A1 A2].
    exact (conj A1 (conj A2 I)).
Qed.

(* THE POST, from the end memory: its g_nl list (LinkWalkNlk.v anlk_after) agrees with the entry's outside the
   offsets P the run may have written, and reads the values the run left there *)
Lemma fs_after : forall (m m' : word -> option byte) bs (P : Z -> Prop),
  anlk_at SEGS m LA_G_NL bs ->
  (forall i, P i -> NK_SEND_ERRNO <= i < NK_N_SENT + 4) ->
  (forall i, 0 <= i < NK_SIZE -> ~ P i -> mbyte SEGS m' (LA_G_NL + i) = mbyte SEGS m (LA_G_NL + i)) ->
  (forall i, 0 <= i < NK_SIZE -> P i -> exists b, mbyte SEGS m' (LA_G_NL + i) = Some b) ->
  (forall i, 0 <= i < NK_SIZE -> writable_at SEGS m' (LA_G_NL + i)) ->
  anlk_at SEGS m' LA_G_NL (abytes_of SEGS m' LA_G_NL (Z.to_nat NK_SIZE)) /\
  agree_out bs (abytes_of SEGS m' LA_G_NL (Z.to_nat NK_SIZE)) P /\
  (forall off (n : nat) v, 0 <= off -> off + Z.of_nat n <= NK_SIZE -> 0 <= v < 2 ^ (8 * Z.of_nat n) ->
     val_mem SEGS m' (LA_G_NL + off) n v -> rdn (abytes_of SEGS m' LA_G_NL (Z.to_nat NK_SIZE)) off (Z.of_nat n) = v).
Proof.
intros m m' bs P HNK HP Hout Hin Hwr.
pose proof HNK as [[(Hb0 & Hblen & Hb) _] HL].
assert (Hm : forall i, 0 <= i < NK_SIZE ->
          exists b, mbyte SEGS m (LA_G_NL + i) = Some b /\ nth_error bs (Z.to_nat i) = Some b).
{ intros i Hi. pose proof (Hb (Z.to_nat i) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia.
  destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:En; [exists b; split; [exact E | reflexivity]|].
  apply nth_error_None in En. lia. }
destruct (anlk_after SEGS m m' LA_G_NL bs NK_SEND_ERRNO (NK_N_SENT + 4) HNK) as (HNK' & _ & Hval).
- intros i Hi Hn. apply Hout; [exact Hi|]. intros HPi. exact (Hn (HP i HPi)).
- intros i Hi Hlh. destruct (classic (P i)) as [HPi | HPi]; [exact (Hin i Hi HPi)|].
  rewrite (Hout i Hi HPi). destruct (Hm i Hi) as (b & Hb' & _). exists b. exact Hb'.
- exact Hwr.
- split; [exact HNK'|]. split; [|exact Hval].
  intros i Hi HPi. destruct (Hm i Hi) as (b & Hb1 & Hb2). rewrite Hb2.
  apply abytes_of_nth; [unfold NK_SIZE in *; lia|]. rewrite Z2Nat.id by lia. rewrite (Hout i Hi HPi). exact Hb1.
Qed.

Ltac fs_nums := unfold NK_SEND_ERRNO, NK_MISUSE, NK_N_SENT, NK_SENT, NK_SENT_LEN, NK_SIZE, NL_SENT_LEN in *.
Ltac vrng := fs_nums; try change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32);
  try change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); lia.

(* the recording path *)
Lemma fs_post_copy : forall (m m' : word -> option byte) (regs regs2 : bvmap 5 word) bs req,
  anlk_at SEGS m LA_G_NL bs -> nlk_wf bs ->
  abytes SEGS m (aarg regs 1) req -> Z.of_nat (length req) = aarg regs 2 -> aarg regs 2 <= NL_SENT_LEN ->
  nk_send_errno bs = 0 -> nk_n_sent bs <= 15 ->
  (forall i, 0 <= i < NK_SIZE -> ~ P_copy (nk_n_sent bs) (aarg regs 2) i ->
     mbyte SEGS m' (LA_G_NL + i) = mbyte SEGS m (LA_G_NL + i)) ->
  (forall i, 0 <= i < NK_SIZE -> writable_at SEGS m' (LA_G_NL + i)) ->
  val_mem SEGS m' (LA_G_NL + NK_SEND_ERRNO) 4 (nk_send_errno bs) ->
  val_mem SEGS m' (LA_G_NL + NK_MISUSE) 4 (snd_mis (aarg regs 0) bs) ->
  val_mem SEGS m' (LA_G_NL + NK_N_SENT) 4 (nk_n_sent bs + 1) ->
  val_mem SEGS m' (LA_G_NL + (NK_SENT_LEN + 8 * nk_n_sent bs)) 8 (aarg regs 2) ->
  (forall k, 0 <= k < aarg regs 2 ->
     mbyte SEGS m' (LA_G_NL + (NK_SENT + NL_SENT_LEN * nk_n_sent bs) + k) = mbyte SEGS m (aarg regs 1 + k)) ->
  getr regs2 10 = getr regs 12 ->
  fuzz_send_apost SEGS B regs m regs2 m'.
Proof.
intros m m' regs regs2 bs req HNK WF RQ LR L5 SE0 N15 Hout Hwr Vse Vmi Vns Vsl Vrq R10.
unfold fuzz_send_apost. intros bs0 req0 HNK0 RQ0 LR0.
rewrite (anlk_at_unique SEGS m LA_G_NL bs0 bs HNK0 HNK). clear bs0 HNK0.
assert (Er : req0 = req) by (apply (fs_abytes_unique SEGS m (aarg regs 1)); [exact RQ0 | exact RQ | lia]).
subst req0. clear RQ0 LR0.
pose proof WF as (_ & _ & Wns & _). unfold NL_SENT_MAX in Wns.
pose proof RQ as (Hq0 & Hqlen & Hq).
rewrite <- LR in *.
set (n := nk_n_sent bs) in *.
assert (Hreq : forall k, (k < length req)%nat ->
          mbyte SEGS m' (LA_G_NL + (NK_SENT + NL_SENT_LEN * n) + Z.of_nat k) = nth_error req k).
{ intros k Hk. rewrite Vrq by lia. exact (Hq k Hk). }
destruct (fs_after m m' bs (P_copy n (Z.of_nat (length req))) HNK) as (HNK' & HAG & Hval).
- intros i Hi. unfold P_copy, P_base in Hi. fs_nums. lia.
- exact Hout.
- intros i Hi HPi. unfold P_copy, P_base in HPi. destruct HPi as [[H | [H | H]] | [H | H]].
  + apply (fs_val_some _ _ _ _ _ Vse). cbn. lia.
  + apply (fs_val_some _ _ _ _ _ Vmi). cbn. lia.
  + apply (fs_val_some _ _ _ _ _ Vns). cbn. lia.
  + pose proof (Hreq (Z.to_nat (i - (NK_SENT + NL_SENT_LEN * n))) ltac:(lia)) as Hk.
    replace (LA_G_NL + (NK_SENT + NL_SENT_LEN * n) + Z.of_nat (Z.to_nat (i - (NK_SENT + NL_SENT_LEN * n))))
      with (LA_G_NL + i) in Hk by lia.
    destruct (nth_error req _) as [b|] eqn:Eb; [exists b; exact Hk|]. apply nth_error_None in Eb. lia.
  + apply (fs_val_some _ _ _ _ _ Vsl). cbn. lia.
- exact Hwr.
- set (bs' := abytes_of SEGS m' LA_G_NL (Z.to_nat NK_SIZE)) in *.
  assert (Hl' : Z.of_nat (length bs') = NK_SIZE) by (unfold bs'; rewrite abytes_of_length; unfold NK_SIZE; lia).
  pose proof HNK as [_ Hl].
  pose proof (snd_mis_range (aarg regs 0) bs WF) as Mb.
  destruct (post_copy_b (aarg regs 0) bs bs' req Hl Hl' WF SE0 N15 ltac:(lia) HAG) as (WF' & COM & SE' & SENT & NS').
  + exact (Hval NK_MISUSE 4%nat (snd_mis (aarg regs 0) bs) ltac:(fs_nums; lia) ltac:(fs_nums; lia) ltac:(vrng) Vmi).
  + exact (Hval NK_SEND_ERRNO 4%nat (nk_send_errno bs) ltac:(fs_nums; lia) ltac:(fs_nums; lia)
      ltac:(rewrite SE0; vrng) Vse).
  + exact (Hval NK_N_SENT 4%nat (n + 1) ltac:(fs_nums; lia) ltac:(fs_nums; lia) ltac:(vrng) Vns).
  + exact (Hval (NK_SENT_LEN + 8 * n) 8%nat (Z.of_nat (length req)) ltac:(fs_nums; lia) ltac:(fs_nums; lia)
      ltac:(vrng) Vsl).
  + intros k Hk. destruct (nth_error req k) as [b|] eqn:Eb; [|apply nth_error_None in Eb; lia].
    apply abytes_of_nth; [fs_nums; lia|].
    rewrite <- Eb, <- (Hreq k Hk). f_equal. fs_nums. lia.
  + exists bs'. destruct COM as (C1 & C2 & C3 & C4 & C5 & C6).
    refine (conj HNK' (conj WF' (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj _ _))))))))).
    * intros H. exfalso. exact (H SE0).
    * intros _. exact (conj R10 (conj SE' (conj SENT NS'))).
Qed.

(* the full ring: nothing recorded *)
Lemma fs_post_full : forall (m m' : word -> option byte) (regs regs2 : bvmap 5 word) bs req,
  anlk_at SEGS m LA_G_NL bs -> nlk_wf bs ->
  abytes SEGS m (aarg regs 1) req -> Z.of_nat (length req) = aarg regs 2 ->
  nk_send_errno bs = 0 -> 15 < nk_n_sent bs ->
  (forall i, 0 <= i < NK_SIZE -> ~ P_base i -> mbyte SEGS m' (LA_G_NL + i) = mbyte SEGS m (LA_G_NL + i)) ->
  (forall i, 0 <= i < NK_SIZE -> writable_at SEGS m' (LA_G_NL + i)) ->
  val_mem SEGS m' (LA_G_NL + NK_SEND_ERRNO) 4 (nk_send_errno bs) ->
  val_mem SEGS m' (LA_G_NL + NK_MISUSE) 4 (snd_mis (aarg regs 0) bs) ->
  val_mem SEGS m' (LA_G_NL + NK_N_SENT) 4 (nk_n_sent bs) ->
  getr regs2 10 = getr regs 12 ->
  fuzz_send_apost SEGS B regs m regs2 m'.
Proof.
intros m m' regs regs2 bs req HNK WF RQ LR SE0 N15 Hout Hwr Vse Vmi Vns R10.
unfold fuzz_send_apost. intros bs0 req0 HNK0 RQ0 LR0.
rewrite (anlk_at_unique SEGS m LA_G_NL bs0 bs HNK0 HNK). clear bs0 HNK0.
assert (Er : req0 = req) by (apply (fs_abytes_unique SEGS m (aarg regs 1)); [exact RQ0 | exact RQ | lia]).
subst req0. clear RQ0 LR0.
pose proof WF as (_ & _ & Wns & _). unfold NL_SENT_MAX in Wns.
destruct (fs_after m m' bs P_base HNK) as (HNK' & HAG & Hval).
- intros i Hi. unfold P_base in Hi. fs_nums. lia.
- exact Hout.
- intros i Hi HPi. unfold P_base in HPi. destruct HPi as [H | [H | H]].
  + apply (fs_val_some _ _ _ _ _ Vse). cbn. lia.
  + apply (fs_val_some _ _ _ _ _ Vmi). cbn. lia.
  + apply (fs_val_some _ _ _ _ _ Vns). cbn. lia.
- exact Hwr.
- set (bs' := abytes_of SEGS m' LA_G_NL (Z.to_nat NK_SIZE)) in *.
  assert (Hl' : Z.of_nat (length bs') = NK_SIZE) by (unfold bs'; rewrite abytes_of_length; unfold NK_SIZE; lia).
  pose proof HNK as [_ Hl].
  pose proof (snd_mis_range (aarg regs 0) bs WF) as Mb.
  destruct (post_full_b (aarg regs 0) bs bs' req Hl Hl' WF SE0 N15 HAG) as (WF' & COM & SE' & SENT & NS').
  + exact (Hval NK_MISUSE 4%nat (snd_mis (aarg regs 0) bs) ltac:(fs_nums; lia) ltac:(fs_nums; lia) ltac:(vrng) Vmi).
  + exact (Hval NK_SEND_ERRNO 4%nat (nk_send_errno bs) ltac:(fs_nums; lia) ltac:(fs_nums; lia)
      ltac:(rewrite SE0; vrng) Vse).
  + exact (Hval NK_N_SENT 4%nat (nk_n_sent bs) ltac:(fs_nums; lia) ltac:(fs_nums; lia) ltac:(vrng) Vns).
  + exists bs'. destruct COM as (C1 & C2 & C3 & C4 & C5 & C6).
    refine (conj HNK' (conj WF' (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj _ _))))))))).
    * intros H. exfalso. exact (H SE0).
    * intros _. exact (conj R10 (conj SE' (conj SENT NS'))).
Qed.

(* the error path: errno := send_errno, send_errno := 0, -1 *)
Lemma fs_post_err : forall (m m' : word -> option byte) (regs regs2 : bvmap 5 word) bs req,
  anlk_at SEGS m LA_G_NL bs -> nlk_wf bs ->
  abytes SEGS m (aarg regs 1) req -> Z.of_nat (length req) = aarg regs 2 ->
  nk_send_errno bs <> 0 ->
  (forall i, 0 <= i < NK_SIZE -> ~ P_base i -> mbyte SEGS m' (LA_G_NL + i) = mbyte SEGS m (LA_G_NL + i)) ->
  (forall i, 0 <= i < NK_SIZE -> writable_at SEGS m' (LA_G_NL + i)) ->
  val_mem SEGS m' (LA_G_NL + NK_SEND_ERRNO) 4 0 ->
  val_mem SEGS m' (LA_G_NL + NK_MISUSE) 4 (snd_mis (aarg regs 0) bs) ->
  val_mem SEGS m' (LA_G_NL + NK_N_SENT) 4 (nk_n_sent bs) ->
  au32_at SEGS m' (as_errno B) (nk_send_errno bs) ->
  getr regs2 10 = w64 (-1) ->
  fuzz_send_apost SEGS B regs m regs2 m'.
Proof.
intros m m' regs regs2 bs req HNK WF RQ LR SE Hout Hwr Vse Vmi Vns HE R10.
unfold fuzz_send_apost. intros bs0 req0 HNK0 RQ0 LR0.
rewrite (anlk_at_unique SEGS m LA_G_NL bs0 bs HNK0 HNK). clear bs0 HNK0.
pose proof WF as (_ & _ & Wns & _). unfold NL_SENT_MAX in Wns.
destruct (fs_after m m' bs P_base HNK) as (HNK' & HAG & Hval).
- intros i Hi. unfold P_base in Hi. fs_nums. lia.
- exact Hout.
- intros i Hi HPi. unfold P_base in HPi. destruct HPi as [H | [H | H]].
  + apply (fs_val_some _ _ _ _ _ Vse). cbn. lia.
  + apply (fs_val_some _ _ _ _ _ Vmi). cbn. lia.
  + apply (fs_val_some _ _ _ _ _ Vns). cbn. lia.
- exact Hwr.
- set (bs' := abytes_of SEGS m' LA_G_NL (Z.to_nat NK_SIZE)) in *.
  assert (Hl' : Z.of_nat (length bs') = NK_SIZE) by (unfold bs'; rewrite abytes_of_length; unfold NK_SIZE; lia).
  pose proof HNK as [_ Hl].
  pose proof (snd_mis_range (aarg regs 0) bs WF) as Mb.
  destruct (post_err_b (aarg regs 0) bs bs' Hl Hl' WF HAG) as (WF' & COM & SE' & NS' & SENT).
  + exact (Hval NK_MISUSE 4%nat (snd_mis (aarg regs 0) bs) ltac:(fs_nums; lia) ltac:(fs_nums; lia) ltac:(vrng) Vmi).
  + exact (Hval NK_SEND_ERRNO 4%nat 0 ltac:(fs_nums; lia) ltac:(fs_nums; lia) ltac:(vrng) Vse).
  + exact (Hval NK_N_SENT 4%nat (nk_n_sent bs) ltac:(fs_nums; lia) ltac:(fs_nums; lia) ltac:(vrng) Vns).
  + exists bs'. destruct COM as (C1 & C2 & C3 & C4 & C5 & C6).
    refine (conj HNK' (conj WF' (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj _ _))))))))).
    * intros _. exact (conj R10 (conj SE' (conj HE (conj NS' SENT)))).
    * intros H. exfalso. exact (SE H).
Qed.

(* a signed `blt` between two small values *)
Lemma fs_lt : forall E a b x y, sv_denot E a = Z_to_bv 64 x -> sv_denot E b = Z_to_bv 64 y ->
  0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 -> branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (x <? y).
Proof.
  intros E a b x y Ha Hb Hx Hy. rewrite Ha, Hb, YO0c.branch_lt, !unsigned_lit_small by lia.
  rewrite !YO0b.s64_small by lia. reflexivity.
Qed.

(* a byte of g_nl's send_errno .. n_sent words is a byte of the write set, and every byte of it lies there *)
Lemma fs_inwr : forall regs m a, LA_G_NL + NK_SEND_ERRNO <= a < LA_G_NL + NK_N_SENT + 4 ->
  inFP (fuzz_send_awr regs m) a.
Proof.
  intros regs m a Ha. exists (LA_G_NL + NK_SEND_ERRNO, LA_G_NL + NK_N_SENT + 4).
  split; [left; reflexivity | cbn [fst snd]; exact Ha].
Qed.
Lemma fs_wr_in : forall regs m x, inFP (fuzz_send_awr regs m) x ->
  LA_G_NL + NK_SEND_ERRNO <= x < LA_G_NL + NK_N_SENT + 4.
Proof. intros regs m x (r & [<- | []] & Hr). exact Hr. Qed.

(* the journal's window is present *)
Lemma fs_win_present : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m md k,
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m md k ->
  forall a, sp0 - STK <= a < sp0 -> apresent (w_H W) m a.
Proof.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m md k (HSTK & HXO & (memS & HJi & _) & _) a Ha.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _). apply Hpres. lia.
Qed.

(* a value whose bytes did not change *)
Lemma fs_val_move : forall (m m' : word -> option byte) a (n : nat) v,
  val_mem SEGS m a n v -> (forall j, a <= j < a + Z.of_nat n -> mbyte SEGS m' j = mbyte SEGS m j) ->
  val_mem SEGS m' a n v.
Proof. intros m m' a n v H Hm k Hk. rewrite Hm by lia. exact (H k Hk). Qed.

(* the shadow facts of a sub-range, at a memory whose shadow bytes are the same *)
Lemma fs_ra_move : forall (rd rd' : reader) p n q k,
  range_addressable rd SHADOW_OFF p n -> p <= q -> q + k <= p + n -> 0 <= q ->
  (forall s, SHADOW_OFF + q / 8 <= s <= SHADOW_OFF + (q + k) / 8 -> rd' s = rd s) ->
  range_addressable rd' SHADOW_OFF q k.
Proof.
  intros rd rd' p n q k HR H1 H2 H0 Hs. apply (ra_shadow_eq rd rd' q k).
  - intros x Hx. apply HR. lia.
  - intros x Hx. apply Hs. unfold shadow_addr.
    split; apply Z.add_le_mono_l; apply Z.div_le_mono; lia.
Qed.
Lemma fs_hull_move : forall (rd rd' : reader) p n q k,
  shadow_hull_vis rd p n -> p <= q -> 0 < k -> q + k <= p + n -> 0 <= p ->
  (forall s, shadow_addr q / 8 * 8 <= s < shadow_addr (q + k - 1) / 8 * 8 + 8 -> rd' s = rd s) ->
  shadow_hull_vis rd' q k.
Proof.
  intros rd rd' p n q k HH H1 H0 H2 Hp Hs s Hsr. rewrite (Hs s Hsr). apply HH.
  assert (A1 : shadow_addr p / 8 * 8 <= shadow_addr q / 8 * 8).
  { apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|].
    unfold shadow_addr. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
  assert (A2 : shadow_addr (q + k - 1) / 8 * 8 <= shadow_addr (p + n - 1) / 8 * 8).
  { apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|].
    unfold shadow_addr. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
  lia.
Qed.

(* one instrumented check's shadow entry (pcap PcapSourceClose.v shent_ps_ok) *)
Lemma fs_shent_ok : forall E (m : word -> option byte) (nn : nat) x len,
  U E (SOff 32 0) = SHADOW_OFF -> U E (SOff nn 0) = x -> 0 <= x -> 0 <= len -> x + len <= SHADOW_OFF ->
  range_addressable (YCbn.rd_of SEGS m) SHADOW_OFF x len ->
  sh_ok SEGS (SOff 32 0) [mkSHE nn 0 len] E m.
Proof.
  intros E m nn x len HB Hq H0 Hl H1 HR. unfold sh_ok. apply Forall_cons; [|apply Forall_nil].
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hq. split.
  - rewrite Z.add_0_r, Z.sub_0_r. exact HR.
  - intros a Ha. unfold SHADOW_OFF in *. lia.
Qed.

(* the shadow facts of a byte range move to a memory that agrees off a set Zs above the window or below the shadow *)
Lemma fs_ra_tr : forall (W : world SEGS) (m m2 : word -> option byte) (Zs : Z -> Prop) sp p n q k,
  SHADOW_OFF + 2 ^ 44 + 8 < sp - 4144 -> (forall a, Zs a -> sp - 4144 <= a \/ a < SHADOW_OFF) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m a) ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF p n -> p <= q -> q + k <= p + n -> 0 <= q -> q + k <= 2 ^ 47 ->
  range_addressable (aview SEGS (w_H W) m2) SHADOW_OFF q k.
Proof.
  intros W m m2 Zs sp p n q k Hsp HZ UN HR H1 H2 H0 H47.
  apply (fs_ra_move _ _ p n q k HR H1 H2 H0). intros s Hs.
  assert (Hq : 0 <= q / 8) by (apply Z.div_pos; lia).
  assert (Hqk : (q + k) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
  apply UN; [unfold SHADOW_OFF in *; lia|].
  intros HZs. destruct (HZ s HZs); unfold SHADOW_OFF in *; lia.
Qed.
Lemma fs_hull_tr : forall (W : world SEGS) (m m2 : word -> option byte) (Zs : Z -> Prop) sp p n q k,
  SHADOW_OFF + 2 ^ 44 + 8 < sp - 4144 -> (forall a, Zs a -> sp - 4144 <= a \/ a < SHADOW_OFF) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m a) ->
  shadow_hull_vis (aview SEGS (w_H W) m) p n -> p <= q -> 0 < k -> q + k <= p + n -> 0 <= p -> q + k <= 2 ^ 47 ->
  shadow_hull_vis (aview SEGS (w_H W) m2) q k.
Proof.
  intros W m m2 Zs sp p n q k Hsp HZ UN HH H1 H0 H2 Hp H47.
  apply (fs_hull_move _ _ p n q k HH H1 H0 H2 Hp). intros s Hs.
  unfold shadow_addr in Hs.
  assert (Hq : 0 <= q / 8) by (apply Z.div_pos; lia).
  assert (Hqk : (q + k - 1) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
  pose proof (Z.mul_div_le (SHADOW_OFF + (q + k - 1) / 8) 8 ltac:(lia)) as Hm1.
  assert (A1 : SHADOW_OFF <= (SHADOW_OFF + q / 8) / 8 * 8) by (unfold SHADOW_OFF in *; lia).
  apply UN; [unfold SHADOW_OFF in *; lia|].
  intros HZs. destruct (HZ s HZs); lia.
Qed.

(* a value whose bytes lie off the set a run changed *)
Lemma fs_val_keep : forall (W : world SEGS) (m m2 : word -> option byte) (Zs : Z -> Prop) a (n : nat) v,
  (forall x, 0 <= x < 2 ^ 64 -> ~ Zs x -> aview SEGS (w_H W) m2 x = aview SEGS (w_H W) m x) ->
  (forall j, a <= j < a + Z.of_nat n -> 0 <= j < 2 ^ 64 /\ ~ Zs j) ->
  val_mem SEGS (rdW W m) a n v -> val_mem SEGS (rdW W m2) a n v.
Proof.
  intros W m m2 Zs a n v UN Hj H. apply (fs_val_move _ _ a n v H). intros j Hjr.
  destruct (Hj j Hjr) as [H1 H2]. apply (mbyte_of_aview SEGS). exact (UN j H1 H2).
Qed.

(* a byte of a read list is present *)
Lemma fs_abytes_some : forall (W : world SEGS) (m : word -> option byte) x l a, abytes SEGS (rdW W m) x l ->
  x <= a < x + Z.of_nat (length l) -> aview SEGS (w_H W) m a <> None.
Proof.
  intros W m x l a (_ & _ & Hq) Ha. pose proof (Hq (Z.to_nat (a - x)) ltac:(lia)) as Hk.
  replace (x + Z.of_nat (Z.to_nat (a - x))) with a in Hk by lia.
  unfold aview. rewrite Hk.
  destruct (nth_error l (Z.to_nat (a - x))) eqn:Eb; [cbn; discriminate | apply nth_error_None in Eb; lia].
Qed.

(* the byte at a and the byte at b, when the views agree *)
Lemma fs_mbyte_of_aview2 : forall (H H' : word -> bool) (m m' : word -> option byte) a b,
  aview SEGS H m a = aview SEGS H' m' b -> mbyte SEGS (mrestrict H m) a = mbyte SEGS (mrestrict H' m') b.
Proof.
  intros H H' m m' a b E. unfold aview in E.
  destruct (mbyte SEGS (mrestrict H m) a) as [x|], (mbyte SEGS (mrestrict H' m') b) as [y|];
    cbn [option_map] in E; try discriminate; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* g_nl's bytes off P, and its writability, at the end memory *)
Lemma fs_gout : forall (W : world SEGS) (m m2 : word -> option byte) sp (P Er : Z -> Prop),
  LA_G_NL + NK_SIZE <= sp - 4144 -> (forall a, Er a -> aerrno B a) -> apart_gnl LA_G_NL (as_errno B) 4 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ fs_Zs sp P Er a -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m a) ->
  forall i, 0 <= i < NK_SIZE -> ~ P i -> mbyte SEGS (rdW W m2) (LA_G_NL + i) = mbyte SEGS (rdW W m) (LA_G_NL + i).
Proof.
  intros W m m2 sp P Er Hsp HEr HG UN i Hi HP. apply (mbyte_of_aview SEGS). apply UN.
  - unfold LA_G_NL, NK_SIZE in *. lia.
  - unfold fs_Zs. intros [H | [[_ H] | H]].
    + lia.
    + replace (LA_G_NL + i - LA_G_NL) with i in H by lia. exact (HP H).
    + apply HEr in H. unfold aerrno, apart_gnl in *. lia.
Qed.
Lemma fs_gwr : forall (W : world SEGS) (m m2 : word -> option byte) bs, anlk_at SEGS (rdW W m) LA_G_NL bs ->
  mem_grows (rdW W m) (rdW W m2) -> forall i, 0 <= i < NK_SIZE -> writable_at SEGS (rdW W m2) (LA_G_NL + i).
Proof.
  intros W m m2 bs HNK Hg i Hi. destruct HNK as [[_ Hw] HL].
  apply (writable_kept (segs := SEGS) (w_H W) m m2); [intros Hp; exact (apresent_grows _ _ _ _ Hg Hp)|].
  apply Hw. rewrite HL. exact Hi.
Qed.

(* THE END of every path: the contract's apost from the end state of the walk *)
Lemma fs_finish : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs regs2 : bvmap 5 word)
    mem2 md2 (P Er : Z -> Prop),
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k ->
  sp0 - STK <= spZ regs - FUZZ_SEND_AK -> spZ regs <= sp0 ->
  m_fds md2 = m_fds mdc -> m_fs md2 = m_fs mdc ->
  aregs_preserved regs regs2 ->
  (forall i, P i -> NK_SEND_ERRNO <= i < NK_N_SENT + 4) -> (forall a, Er a -> aerrno B a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ fs_Zs (spZ regs) P Er a ->
     aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a) ->
  mem_grows (rdW W memc) (rdW W mem2) ->
  fuzz_send_apost SEGS B regs (rdW W memc) regs2 (rdW W mem2) ->
  apost SK SEGS B FUZZ_SEND_AK 0 (fun a => inFP (fuzz_send_awr regs (rdW W memc)) a) G XO OUT STK sp0 FP ly S W0
    mem0 md0 own lyc Sc W memc mdc k regs
    (fun ly2 S2 W2 regs2 mem2 md2 => S2 = set_fs (st_fs S2) Sc /\ Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
       fuzz_send_apost SEGS B regs (rdW W memc) regs2 (rdW W2 mem2))
    W (mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2).
Proof.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regs2 mem2 md2 P Er
  HJ HJ2 Hlo Hhi Hfd Hfs HP HPw HEr UN HGr HPost.
pose proof FUZZ_SEND_AK_val as HK.
pose proof HJ as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (HAR & _).
pose proof HJ2 as (_ & _ & (memS2 & HJ2i & _) & _).
pose proof HJ2i as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
pose proof (pal_env B TL) as ENV. pose proof (proj1 ENV) as [Ee0 Ee1].
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
apply (apost_errno SK SEGS B LAWS ENV FUZZ_SEND_AK 0 _ G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  regs _ W _ HAR).
apply (apost_leaf SK SEGS B LAWS pa_segs_low FUZZ_SEND_AK 0
  (fun a => inFP (fuzz_send_awr regs (rdW W memc)) a \/ aerrno B a)
  G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regs2 mem2 md2 _ HJ HJ2);
  [lia | lia | lia | exact Hfd | exact Hfs | exact HP | | | | | ].
- intros a Ha Hw HE. apply UN; [exact Ha|]. unfold fs_Zs. intros [H|[[H1 H2]|H]].
  + apply Hw. lia.
  + apply HE. left. apply fs_inwr. pose proof (HPw _ H2). lia.
  + apply HE. right. exact (HEr a H).
- intros a Hp. exact (apresent_grows _ _ _ _ HGr Hp).
- intros a Ha. apply Hpres2. pose proof HJ2 as (_ & HXO2 & _). clear - Ha Hlo Hhi HXO2 HK. lia.
- intros x [Hx | Hx].
  + apply fs_wr_in in Hx. unfold LA_G_NL, NK_SEND_ERRNO, NK_N_SENT, SHADOW_OFF in *. lia.
  + unfold aerrno in Hx. unfold kLowMemEnd, SHADOW_OFF in *. lia.
- cbv beta. split; [destruct Sc; reflexivity|]. split; [apply Permutation_refl | exact HPost].
Qed.

(* the run's write permission: the frame, g_nl's write set (the contract's Wr, apre's `ajw`), errno *)
Ltac fs_awr Hajw :=
  lazymatch goal with |- awr_ok_xe _ _ ?rs _ _ _ _ _ _ _ _ _ _ =>
    let rs' := eval vm_compute in rs in change rs with rs' end;
  repeat (apply awr_ok_xe_cons;
    [ intros ?a ?Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      first
      [ lia
      | lazymatch type of Ha with context [ew _ 2%nat] =>
          match goal with U : bv_unsigned (ew _ 2%nat) = _ |- _ => rewrite U in Ha end;
          left; left; split; [left; lia | lia] end
      | lazymatch type of Ha with context [ew _ 243%nat] =>
          match goal with U : bv_unsigned (ew _ 243%nat) = _ |- _ => rewrite U in Ha end;
          left; apply Hajw; apply fs_inwr; unfold NK_SEND_ERRNO, NK_N_SENT; lia end
      | lazymatch type of Ha with context [ew _ 37%nat] =>
          match goal with U : bv_unsigned (ew _ 37%nat) = _ |- _ => rewrite U in Ha end;
          left; apply Hajw; apply fs_inwr; unfold NK_SEND_ERRNO, NK_N_SENT; lia end
      | lazymatch type of Ha with context [ew _ 52%nat] =>
          match goal with U : bv_unsigned (ew _ 52%nat) = _ |- _ => rewrite U in Ha end;
          right; unfold aerrno; lia end ]
    | ]);
  apply awr_ok_xe_nil.

(* the bytes a run left as they were: every byte outside its write windows (YC4b.v kept_of_frame) *)
Ltac fs_kept HFr Zs UN :=
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ Zs HFr
    ltac:(intros ?bb ?wlo ?whi ?aa ?Hin ?Hrr; vm_compute in Hin;
          repeat (destruct Hin as [?Hq | Hin];
                  [injection Hq as <- <- <-; cbn [base_val] in Hrr;
                   repeat match goal with U : bv_unsigned (ew _ ?n) = _ |- _ =>
                     lazymatch type of Hrr with context [ew _ n] => rewrite U in Hrr end end;
                   cbv beta; (try unfold Zs); unfold fs_Zs, P_base, P_sn, P_cp, NoE, aerrno, NK_SEND_ERRNO, NK_MISUSE,
                     NK_N_SENT, NK_SENT, NK_SENT_LEN, NL_SENT_LEN, NK_SIZE, LA_G_NL in *; cbv beta; lia |]);
          destruct Hin)) as UN.

(* chain a run's kept bytes and growth onto those since m0 *)
Ltac fs_fold UN HGc UNk HG W m0 Zs :=
  lazymatch type of UNk with forall a, _ -> _ -> aview _ _ ?mN a = aview _ _ ?mO a =>
    let UN' := fresh "UN" in
    assert (UN' : forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS (w_H W) mN a = aview SEGS (w_H W) m0 a)
      by (intros ?a ?Ha ?Hz; rewrite (UNk _ Ha Hz); exact (UN _ Ha Hz));
    clear UN UNk; rename UN' into UN end;
  lazymatch type of HG with mem_grows _ (mrestrict _ ?mN) =>
    let HG' := fresh "HGc" in
    assert (HG' : mem_grows (mrestrict (w_H W) m0) (mrestrict (w_H W) mN))
      by (eapply mem_grows_trans; [exact HGc | exact HG]);
    clear HGc HG; rename HG' into HGc end.

(* a field the run left in a region: its value at the end memory *)
Ltac fs_den :=
  cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
  repeat match goal with Eq : ew ?E0 ?n = Z_to_bv 64 _ |- context [ew ?E0 ?n] => rewrite Eq end;
  rewrite ?unsigned_lit_small by (unfold LA_G_NL in *; lia); rewrite ?Z.add_0_r; reflexivity.
Ltac fs_vfield HR U :=
  eapply (field_of_region (segs := SEGS) _ _ _ _ _ _ _ _ _ _ 4%N);
  [ exact HR | exact U | repeat (first [left; reflexivity | right]) | fs_den | zrng | zrng ].
Ltac fs_vfield8 HR U :=
  eapply (field_of_region (segs := SEGS) _ _ _ _ _ _ _ _ _ _ 8%N);
  [ exact HR | exact U | repeat (first [left; reflexivity | right]) | fs_den | zrng | zrng ].

(* misuse's word (value v), read off region 5 (fs_mi) of a state before +0x64 *)
Ltac fs_mis HS Ug Hv v VMI :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    let HR := fresh "HR" in
    pose proof (st_ok_pi_region Ex ssx _ 5 _ HS eq_refl) as HR;
    cbn [ms_mem restrict] in HR;
    assert (VMI : val_mem SEGS (mrestrict Hh (ms_mem msx)) (LA_G_NL + 262688) 4 v)
      by (eapply (field_of_region (segs := SEGS) _ _ _ _ _ _ _ _ _ _ 4%N);
          [ exact HR | exact Ug | left; reflexivity | exact Hv | zrng | zrng ]);
    clear HR
  end.

(* the join of several ways into one state SST at listing offset pc: the registers clob forgotten to atoms from
   40 (LinkPaLib.v st_ok_pi_after_stretch), the regions idx kept, the branch conditions dropped (YP03.v prune) *)
Ltac fs_norm HS idx pc clob SST HS4 :=
  lazymatch type of HS with st_ok_pi ?segs ?val ?Ex ?ssx (restrict (w_H ?Wx) ?msx) =>
    let rs := eval vm_compute in (YP03.pick (ss_mem ssx) idx) in
    let HS2 := fresh "HS2" in
    pose proof (st_ok_pi_after_stretch 40 Ex (abs_ss val ssx) (restrict (w_H Wx) msx) (ms_regs msx)
      (mrestrict (w_H Wx) (ms_mem msx)) rs pc clob HS eq_refl ltac:(cbv; lia)
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(submem_tac) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) (fun r _ => eq_refl)
      ltac:(apply Forall_forall; intros; apply fs_region_kept_same)) as HS2;
    apply YP03.st_ok_prune with (ci := []) (ai := [0; 1]%nat) in HS2;
    assert (HS4 : st_ok_pi segs val (havoc Ex 40 (map (getr (ms_regs msx)) clob)) SST
      (restrict (w_H Wx) (mkst (ms_regs msx) (Z_to_bv 64 (BASE + pc)) (ms_mem msx) (seg_rom SEGS))))
      by (rewrite restrict_mkst_fx; exact HS2);
    clear HS2;
    assert (HEIn : img_env VAL A_LIM (havoc Ex 40 (map (getr (ms_regs msx)) clob)))
      by (apply img_env_havoc; [assumption | cbv; lia])
  end.

Theorem fuzz_send_aproof : forall rlo rhi, fuzz_send_acontract SK SEGS rlo rhi B.
Proof.
intros rlo rhi. unfold fuzz_send_acontract, aleaf_rd.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HA HRD HP.
destruct HA as (HJ & HGX & HROD & Hret & Hra4 & Hgp & Htp & H16 & Hwlo & Hwhi & Hev & Hside & Hajw & Hro).
destruct HP as (bs & req & HNK & WF & RAG & HULLG & ERRA & ERRW & ERRS & ERRFR & ERRG & RQ & LR & L5
  & AMR & RAR & HULLR & RG & RF).
clear HRD HROD Hro Hev Hside.
pose proof FUZZ_SEND_AK_val as HK.
unfold YK0s.ret_ok in Hret. unfold apart_frame in ERRFR, RF. unfold NL_SENT_LEN in L5.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof HJ as (HSTK & HXO & (memS & HJi & _) & _).
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi Hstk.
destruct fs_vals as (V1 & V2 & V64 & VB & Vser & Vmc).
pose proof (pal_env B TL) as ENV. pose proof (proj1 ENV) as [Ee0 Ee1].
pose proof WF as (Wnc & Wnx & Wns & Wni & Wop & Won & Wcl & Wmi & Wee & Wse & Wsd & _ & _).
unfold NL_SENT_MAX in Wns.
pose proof (snd_mis_range (aarg regs 0) bs WF) as Mb.
assert (A0 : getr regs 10 = Z_to_bv 64 (aarg regs 0)).
{ unfold aarg, argZ. replace (Z_to_bv 5 (10 + 0)) with (10%bv : bv 5) by (apply bv_eq; reflexivity).
  symmetry. apply Z_to_bv_bv_unsigned. }
assert (A1 : getr regs 11 = Z_to_bv 64 (aarg regs 1)).
{ unfold aarg, argZ. replace (Z_to_bv 5 (10 + 1)) with (11%bv : bv 5) by (apply bv_eq; reflexivity).
  symmetry. apply Z_to_bv_bv_unsigned. }
assert (A2 : getr regs 12 = Z_to_bv 64 (aarg regs 2)).
{ unfold aarg, argZ. replace (Z_to_bv 5 (10 + 2)) with (12%bv : bv 5) by (apply bv_eq; reflexivity).
  symmetry. apply Z_to_bv_bv_unsigned. }
assert (RA0 : 0 <= aarg regs 0 < 2 ^ 64) by (unfold aarg, argZ; apply u64_range).
assert (RA1 : 0 <= aarg regs 1 < 2 ^ 64) by (unfold aarg, argZ; apply u64_range).
assert (Hsp64 : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; apply u64_range).
assert (Hspw : SHADOW_OFF + 2 ^ 44 + 8 < spZ regs - 4144) by (unfold SHADOW_OFF; lia).
assert (Hgw : LA_G_NL + NK_SIZE <= spZ regs - 4144) by (unfold LA_G_NL, NK_SIZE; lia).
assert (HX47 : aarg regs 1 + aarg regs 2 <= 2 ^ 47) by (unfold amem_range in AMR; unfold kLowMemEnd in *; lia).
pose proof (fs_entry G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs bs HJ H16 ltac:(lia) Hwhi
  HNK WF ltac:(rewrite A2, unsigned_lit_small by lia; lia)) as HS.
replace (cfg_at SEGS FUZZ_SEND_A regs memc mdc)
  with (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_fuzz_send)) memc (seg_rom SEGS)) mdc)
  by (unfold cfg_at, w64, FUZZ_SEND_A, AF_fuzz_send; rewrite VB; reflexivity).
remember (Eimg (Ereg regs (fs_extra bs))) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (fs_extra bs)) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (Er2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Er3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 (aarg regs 0))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact A0).
assert (E11 : ew E 11 = Z_to_bv 64 (aarg regs 1))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact A1).
assert (E12 : ew E 12 = Z_to_bv 64 (aarg regs 2))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact A2).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (nk_send_errno bs)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (nk_open bs)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (nk_n_sent bs)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (nk_misuse bs)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 (LA_G_NL + 270888 + 8 * nk_n_sent bs))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 (LA_G_NL + 262692 + 512 * nk_n_sent bs))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6)).
assert (HAE : env_agree 32 (Ereg regs (fs_extra bs)) E)
  by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite Er2; reflexivity).
assert (Ug : bv_unsigned (ew E 243) = LA_G_NL) by exact (fs_U243 E HEI).
clear HEdef EL.
match goal with |- SRr _ _ _ ?Q => set (POST := Q) end.
pose proof (paj_run_xe SK B LAWS ENV ERRF G HGX XO OUT) as RUN.
pose proof (paj_run_to_xe SK B LAWS ENV ERRF G HGX XO OUT) as RUNTO.
pose proof (paj_branch (PI := PI)) as BR.
(* the end of every path, from the facts the paths share *)
assert (FIN : forall (P Er : Z -> Prop) (rgF : bvmap 5 word) (mF : word -> option byte) mdF,
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mF mdF k ->
  m_fds mdF = m_fds mdc -> m_fs mdF = m_fs mdc -> aregs_preserved regs rgF ->
  (forall i, P i -> NK_SEND_ERRNO <= i < NK_N_SENT + 4) -> (forall a, Er a -> aerrno B a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ fs_Zs (spZ regs) P Er a -> aview SEGS (w_H W) mF a = aview SEGS (w_H W) memc a) ->
  mem_grows (rdW W memc) (rdW W mF) ->
  fuzz_send_apost SEGS B regs (rdW W memc) rgF (rdW W mF) ->
  POST W (mkCfg (mkst rgF (getr regs 1) mF (seg_rom SEGS)) mdF)).
{ intros P Er rgF mF mdF HJF Hfd Hfs HPr HP HEr UNF HGF HPost. unfold POST.
  exact (fs_finish G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs rgF mF mdF P Er HJ HJF
    Hwlo Hwhi Hfd Hfs HPr HP HEr UNF HGF HPost). }
(* the request's bytes lie off every set a run of fuzz_send changes (but errno) *)
assert (RQZ : forall (P : Z -> Prop) a, aarg regs 1 <= a < aarg regs 1 + aarg regs 2 -> ~ fs_Zs (spZ regs) P NoE a).
{ intros P a Ha [H | [[H _] | H]]; [lia | unfold apart_gnl in RG; lia | exact H]. }
assert (NoEe : forall a, NoE a -> aerrno B a) by (intros a H; destruct H).
assert (NoEs : forall a, NoE a -> a < SHADOW_OFF) by (intros a H; destruct H).
assert (PsnB : forall i, P_sn i -> P_base i) by (intros i Hi; unfold P_sn, P_base in *; tauto).
assert (HES : ESTACK = 4096) by reflexivity.
assert (ERRSH : forall a, aerrno B a -> a < SHADOW_OFF) by (intros a Ha; unfold aerrno in Ha; unfold kLowMemEnd, SHADOW_OFF in *; lia).
(* from +0x64 on *)
assert (CONT64 : forall E' (rg : bvmap 5 word) (mm : word -> option byte) md',
  img_env VAL A_LIM E' -> (forall n, (n < 40)%nat -> ew E' n = ew E n) ->
  env_agree 32 (Ereg regs (fs_extra bs)) E' ->
  st_ok_pi SEGS VAL E' SS64
    (restrict (w_H W) (mkst rg (Z_to_bv 64 (BASE + (AF_fuzz_send + 0x64))) mm (seg_rom SEGS))) ->
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mm md' k ->
  m_fds md' = m_fds mdc -> m_fs md' = m_fs mdc ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ fs_Zs (spZ regs) P_base NoE a ->
     aview SEGS (w_H W) mm a = aview SEGS (w_H W) memc a) ->
  mem_grows (rdW W memc) (rdW W mm) ->
  val_mem SEGS (rdW W mm) (LA_G_NL + NK_MISUSE) 4 (snd_mis (aarg regs 0) bs) ->
  SRr SEGS W (mkCfg (mkst rg (Z_to_bv 64 (BASE + (AF_fuzz_send + 0x64))) mm (seg_rom SEGS)) md') POST).
{ clear HS. intros E' rg mm md' HEI' OLD HAE' HS HJm Hfdm Hfsm UNm HGm VMI.
  assert (E1' : ew E' 1 = getr regs 1) by (rewrite OLD by lia; exact E1).
  assert (Usp' : bv_unsigned (ew E' 2) = spZ regs) by (rewrite OLD by lia; exact Usp).
  assert (E4' : ew E' 4 = getr regs 4) by (rewrite OLD by lia; exact E4).
  assert (E12' : ew E' 12 = Z_to_bv 64 (aarg regs 2)) by (rewrite OLD by lia; exact E12).
  assert (E32' : ew E' 32 = Z_to_bv 64 SB) by (rewrite OLD by lia; exact E32).
  assert (E33' : ew E' 33 = Z_to_bv 64 (nk_send_errno bs)) by (rewrite OLD by lia; exact E33).
  assert (E35' : ew E' 35 = Z_to_bv 64 (nk_n_sent bs)) by (rewrite OLD by lia; exact E35).
  assert (Ug' : bv_unsigned (ew E' 243) = LA_G_NL) by exact (fs_U243 E' HEI').
  assert (SHOK : sh_ok SEGS (SOff 32 0) [] E' (mrestrict (w_H W) mm)) by constructor.
  (* misuse is left as it is after +0x64 *)
  assert (MIS : forall (P Er : Z -> Prop) (m2 : word -> option byte),
     (forall i, P i -> ~ (NK_MISUSE <= i < NK_MISUSE + 4)) -> (forall x, Er x -> aerrno B x) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ fs_Zs (spZ regs) P Er a -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) mm a) ->
     val_mem SEGS (rdW W m2) (LA_G_NL + NK_MISUSE) 4 (snd_mis (aarg regs 0) bs)).
  { intros P Er m2 HP HEr UN2. apply (fs_val_keep W mm m2 _ _ _ _ UN2); [|exact VMI].
    intros j Hj. change (Z.of_nat 4) with 4 in Hj. unfold apart_gnl in ERRG.
    split; [unfold LA_G_NL, NK_MISUSE in *; lia|].
    unfold fs_Zs. unfold LA_G_NL, NK_MISUSE, NK_SIZE in *. intros [H | [[_ H] | H]]; [lia | apply (HP _ H); lia |].
    apply HEr in H. unfold aerrno in H. lia. }
  (* the final agreement with memc, from the one with mm *)
  assert (UNF : forall (P Er PF : Z -> Prop) (m2 : word -> option byte),
     (forall i, P_base i -> PF i) -> (forall i, P i -> PF i) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ fs_Zs (spZ regs) P Er a -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) mm a) ->
     forall a, 0 <= a < 2 ^ 64 -> ~ fs_Zs (spZ regs) PF Er a -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) memc a).
  { intros P Er PF m2 H1 H2 UN2 a Ha Hz.
    rewrite (UN2 a Ha (fun H => Hz (fs_Zs_mono _ _ _ _ _ a H2 (fun x Hx => Hx) H))).
    apply UNm; [exact Ha|]. intros H. apply Hz. exact (fs_Zs_mono _ _ _ _ _ a H1 (NoE_any Er) H). }
  psrr_branch_tok RUN BR HS SHOK Bspan.
  - (* send_errno = 0: the recording arm *)
    rewrite branch_eq_U, (U_atom E' 33 (nk_send_errno bs) E33'), U_lit in Hc by lia.
    apply Z.eqb_eq in Hc. rename Hc into SE0.
    set (Z1 := fs_Zs (spZ regs) P_sn NoE).
    assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ Z1 a -> aview SEGS (w_H W) mm a = aview SEGS (w_H W) mm a)
      by reflexivity.
    assert (HGc : mem_grows (rdW W mm) (rdW W mm)) by apply mem_grows_refl.
    (* +0x94 .. +0xa4: n_sent, `blt 15, a0` *)
    paj_run_tok RUN HS HJm SHOK Bspan; [fs_awr Hajw |].
    fs_kept HFr Z1 UNk. clear HF HFr. fs_fold UN HGc UNk HG W mm Z1.
    assert (D15 : sv_denot E' (SLit 15) = Z_to_bv 64 15) by reflexivity.
    assert (D35 : sv_denot E' (SOff 35 0) = Z_to_bv 64 (nk_n_sent bs))
      by (cbn [sv_denot]; rewrite E35', Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    psrr_branch_tok RUN BR HS SHOK Bspan.
    + (* 15 < n_sent: the ring is full, nothing is recorded *)
      rewrite (fs_lt E' _ _ 15 (nk_n_sent bs) D15 D35) in Hc by lia.
      apply Z.ltb_lt in Hc. rename Hc into N16.
      paj_run_tok RUN HS HJm SHOK Bspan; [fs_awr Hajw |].
      fs_kept HFr Z1 UNk. clear HF HFr. fs_fold UN HGc UNk HG W mm Z1.
      lazymatch type of HS with st_ok_pi _ _ ?Ef _ (restrict _ ?msF) =>
        pose proof (st_ok_pi_region _ _ _ 3 _ HS eq_refl) as HR3;
        pose proof (st_ok_pi_region _ _ _ 4 _ HS eq_refl) as HR4;
        cbn [ms_mem restrict] in HR3, HR4;
        assert (Vse : val_mem SEGS (rdW W (ms_mem msF)) (LA_G_NL + 262672) 4 (nk_send_errno bs)) by fs_vfield HR3 Ug';
        assert (Vns : val_mem SEGS (rdW W (ms_mem msF)) (LA_G_NL + 271016) 4 (nk_n_sent bs)) by fs_vfield HR4 Ug';
        prreg HS (1%bv : bv 5) R1; prreg HS (10%bv : bv 5) R10;
        pose proof (aregs_preserved_of_st_ok SEGS _ Ef _ _ regs (fs_extra bs) HS HAE' ltac:(vm_compute; reflexivity)) as HPr;
        eapply (paj_ret_at (PL := PL_link) (PI := PI) W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
        intros mat';
        rewrite R1, ?E1', Hret;
        assert (UNE : forall a, 0 <= a < 2 ^ 64 -> ~ fs_Zs (spZ regs) P_base NoE a ->
                  aview SEGS (w_H W) (ms_mem msF) a = aview SEGS (w_H W) memc a)
          by exact (UNF P_sn NoE P_base (ms_mem msF) (fun i H => H) PsnB UN);
        apply (FIN P_base NoE (ms_regs msF) (ms_mem msF) _);
        [ apply (ajournal_gx_materialize SEGS B LAWS pa_segs_low); exact HJm
        | repeat rewrite (proj1 (wvb_fds_fs _ _ _)); exact Hfdm
        | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); exact Hfsm
        | exact HPr
        | intros i Hi; unfold P_base in Hi; unfold NK_SEND_ERRNO, NK_MISUSE, NK_N_SENT in *; lia
        | exact NoEe
        | exact UNE
        | exact (mem_grows_trans _ _ _ HGm HGc)
        | apply (fs_post_full (rdW W memc) (rdW W (ms_mem msF)) regs (ms_regs msF) bs req HNK WF RQ LR SE0 N16
            (fs_gout W memc (ms_mem msF) (spZ regs) P_base NoE Hgw NoEe ERRG UNE)
            (fs_gwr W memc (ms_mem msF) bs HNK (mem_grows_trans _ _ _ HGm HGc)) Vse
            (MIS P_sn NoE (ms_mem msF)
               ltac:(intros i Hi; unfold P_sn in Hi; unfold NK_SEND_ERRNO, NK_MISUSE, NK_N_SENT in *; lia) NoEe UN)
            Vns);
          rewrite R10; rewrite ?E12'; exact (eq_sym A2) ]
      end.
    + (* n_sent <= 15: the request is recorded *)
      rewrite (fs_lt E' _ _ 15 (nk_n_sent bs) D15 D35) in Hc by lia.
      apply Z.ltb_ge in Hc. rename Hc into N15.
      (* +0xa8 .. +0xb0: a3 := 512, `bltu a2, a3` *)
      paj_run_tok RUN HS HJm SHOK Bspan; [fs_awr Hajw |].
      fs_kept HFr Z1 UNk. clear HF HFr. fs_fold UN HGc UNk HG W mm Z1.
      assert (CONTB8 : forall E2 (rg2 : bvmap 5 word) (mm2 : word -> option byte) mdB,
        img_env VAL A_LIM E2 -> (forall n, (n < 40)%nat -> ew E2 n = ew E n) ->
        ew E2 40 = Z_to_bv 64 (aarg regs 2) -> env_agree 32 (Ereg regs (fs_extra bs)) E2 ->
        st_ok_pi SEGS VAL E2 SSB8
          (restrict (w_H W) (mkst rg2 (Z_to_bv 64 (BASE + (AF_fuzz_send + 0xb8))) mm2 (seg_rom SEGS))) ->
        ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mm2 mdB k ->
        m_fds mdB = m_fds mdc -> m_fs mdB = m_fs mdc ->
        (forall a, 0 <= a < 2 ^ 64 -> ~ Z1 a -> aview SEGS (w_H W) mm2 a = aview SEGS (w_H W) mm a) ->
        mem_grows (rdW W mm) (rdW W mm2) ->
        SRr SEGS W (mkCfg (mkst rg2 (Z_to_bv 64 (BASE + (AF_fuzz_send + 0xb8))) mm2 (seg_rom SEGS)) mdB) POST).
      { clear UN HGc HS HJm SHOK.
        intros E2 rg2 mm2 mdB HEI2 OLD2 E40 HAE2 HS HJB HfdB HfsB UN HGc.
        assert (E1x : ew E2 1 = getr regs 1) by (rewrite OLD2 by lia; exact E1).
        assert (Usp2 : bv_unsigned (ew E2 2) = spZ regs) by (rewrite OLD2 by lia; exact Usp).
        assert (E3x : ew E2 3 = getr regs 3) by (rewrite OLD2 by lia; exact Er3).
        assert (E4x : ew E2 4 = getr regs 4) by (rewrite OLD2 by lia; exact E4).
        assert (E11x : ew E2 11 = Z_to_bv 64 (aarg regs 1)) by (rewrite OLD2 by lia; exact E11).
        assert (E38x : ew E2 38 = Z_to_bv 64 (LA_G_NL + 262692 + 512 * nk_n_sent bs)) by (rewrite OLD2 by lia; exact E38).
        assert (Ug2 : bv_unsigned (ew E2 243) = LA_G_NL) by exact (fs_U243 E2 HEI2).
        assert (SHOK2 : sh_ok SEGS (SOff 32 0) [] E2 (mrestrict (w_H W) mm2)) by constructor.
        (* +0xb8 .. +0xc8: a0 := g + 0x40224 + 512 n; +0xcc the call of checked_memcpy *)
        paj_run_tok RUN HS HJB SHOK2 Bspan; [fs_awr Hajw |].
        fs_kept HFr Z1 UNk. clear HF HFr. fs_fold UN HGc UNk HG W mm Z1.
        lazymatch type of HS with st_ok _ _ _ (restrict _ ?msC) => rename msC into ms1 end.
        pmkst HS.
        prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3.
        prreg HS (4%bv : bv 5) R4. prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11.
        prreg HS (12%bv : bv 5) R12.
        rewrite Usp2 in R2. rewrite E3x, Hgp in R3. rewrite E4x, Htp in R4. rewrite E38x in R10.
        rewrite E11x in R11. rewrite E40 in R12.
        assert (Usp1 : spZ (ms_regs ms1) = spZ regs - 48)
          by (unfold spZ at 1; rewrite R2; apply unsigned_lit_small; lia).
        set (d := LA_G_NL + 262692 + 512 * nk_n_sent bs) in R10.
        set (Zc := fun a => fs_Zs (spZ regs) P_base NoE a \/ Z1 a).
        assert (HZc : forall a, Zc a -> spZ regs - 4144 <= a \/ a < SHADOW_OFF)
          by (intros a [H | H]; apply (fs_Zs_lowhigh _ _ _ a NoEs) in H; exact H).
        assert (UNc : forall a, 0 <= a < 2 ^ 64 -> ~ Zc a ->
                  aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) memc a)
          by (intros a Ha Hz; rewrite (UN a Ha (fun H => Hz (or_intror H))); exact (UNm a Ha (fun H => Hz (or_introl H)))).
        assert (HGx : mem_grows (rdW W memc) (rdW W (ms_mem ms1))) by exact (mem_grows_trans _ _ _ HGm HGc).
        eapply SRr_bind.
        { eapply (aj_gx_intrin_at SK SEGS B LAWS pa_segs_low OCpy (pa_sigma LS___asan_memcpy) MEMCPY G XO OUT W
            (ms_regs ms1) (ms_mem ms1) STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k d (aarg regs 1) (aarg regs 2) _
            HGX HJB);
          [ exact R10 | exact R11 | exact R12 | lia | unfold d, LA_G_NL; lia | unfold d, LA_G_NL; lia
          | rewrite Usp1; lia | rewrite Usp1, HES; lia | rewrite Usp1; lia
          | exact R3 | exact R4 | exact R1 | apply ret_ok_codeptr_v; lia
          | | | | | ].
          - intros a Ha.
            destruct (Hajw a (fs_inwr regs (rdW W memc) a ltac:(unfold d, NK_SEND_ERRNO, NK_N_SENT, LA_G_NL in *; lia)))
              as [[H1 H2] | [H1 | H1]].
            + left. split; [exact H1|]. split; [exact H2|]. rewrite Usp1. unfold d, LA_G_NL in *. lia.
            + right; left. split; [exact H1|].
              replace a with (LA_G_NL + (a - LA_G_NL)) by lia.
              apply (fs_gwr W memc (ms_mem ms1) bs HNK HGx). unfold d, NK_SIZE, LA_G_NL in *. lia.
            + right; right. exact H1.
          - unfold amem_range. left. unfold d, LA_G_NL, kLowMemEnd in *. lia.
          - exact (fs_ra_tr W memc (ms_mem ms1) Zc (spZ regs) LA_G_NL NK_SIZE d (aarg regs 2) Hspw HZc UNc RAG
              ltac:(unfold d; lia) ltac:(unfold d, NK_SIZE; lia) ltac:(unfold d, LA_G_NL; lia)
              ltac:(unfold d, LA_G_NL; lia)).
          - intros Hpos. exact (fs_hull_tr W memc (ms_mem ms1) Zc (spZ regs) LA_G_NL NK_SIZE d (aarg regs 2) Hspw HZc
              UNc HULLG ltac:(unfold d; lia) Hpos ltac:(unfold d, NK_SIZE; lia) ltac:(unfold LA_G_NL; lia)
              ltac:(unfold d, LA_G_NL; lia)).
          - split; [lia|]. split; [unfold amem_range, kLowMemEnd, kHighMemEnd in *; lia|].
            split; [|split; [unfold apart_gnl in RG; unfold d, NK_SIZE in *; lia | split; [exact AMR | split]]].
            + intros a Ha. split.
              * rewrite (UNc a ltac:(lia) ltac:(intros [H | H]; exact (RQZ _ a Ha H))).
                exact (fs_abytes_some W memc (aarg regs 1) req a RQ ltac:(lia)).
              * rewrite Usp1, HES. lia.
            + exact (fs_ra_tr W memc (ms_mem ms1) Zc (spZ regs) (aarg regs 1) (aarg regs 2) (aarg regs 1) (aarg regs 2)
                Hspw HZc UNc RAR ltac:(lia) ltac:(lia) ltac:(lia) HX47).
            + intros Hpos. exact (fs_hull_tr W memc (ms_mem ms1) Zc (spZ regs) (aarg regs 1) (aarg regs 2) (aarg regs 1)
                (aarg regs 2) Hspw HZc UNc (HULLR Hpos) ltac:(lia) Hpos ltac:(lia) ltac:(lia) HX47). }
        cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ3 & HP2 & H10c & Hcp & Hun & Hpr & Hsm).
        jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 3; 4]%nat HS2.
        match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
        { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil; (split;
            cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
            [ intros a Ha; apply (mbyte_of_aview SEGS);
              repeat match goal with U : bv_unsigned (ew _ ?n) = _ |- _ =>
                lazymatch type of Ha with context [ew _ n] => rewrite U in Ha end end;
              apply Hun; [unfold LA_G_NL in *; lia | unfold d, LA_G_NL in *; lia
                         | rewrite Usp1, HES; unfold LA_G_NL, NK_SIZE in *; lia]
            | intros a Ha Hw; exact (writable_kept (segs := SEGS) (w_H W) (ms_mem ms1) mem2 a (Hpr a) Hw) ]). }
        clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
        remember (havoc E2 48 (map (getr regs2) CLOB)) as E3 eqn:HE3 in HS.
        assert (HEIc : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc; [exact HEI2 | cbv; lia]).
        assert (OLD3 : forall n, (n < 40)%nat -> ew E3 n = ew E n)
          by (intros n Hn; rewrite HE3, YN3v.ew_havoc_old by lia; apply OLD2; exact Hn).
        assert (HAE3 : env_agree 32 (Ereg regs (fs_extra bs)) E3)
          by (rewrite HE3; apply env_agree_havoc_ge; [lia | exact HAE2]).
        clear HE3.
        assert (E1y : ew E3 1 = getr regs 1) by (rewrite OLD3 by lia; exact E1).
        assert (Usp3 : bv_unsigned (ew E3 2) = spZ regs) by (rewrite OLD3 by lia; exact Usp).
        assert (E12y : ew E3 12 = Z_to_bv 64 (aarg regs 2)) by (rewrite OLD3 by lia; exact E12).
        assert (E32y : ew E3 32 = Z_to_bv 64 SB) by (rewrite OLD3 by lia; exact E32).
        assert (E33y : ew E3 33 = Z_to_bv 64 (nk_send_errno bs)) by (rewrite OLD3 by lia; exact E33).
        assert (E35y : ew E3 35 = Z_to_bv 64 (nk_n_sent bs)) by (rewrite OLD3 by lia; exact E35).
        assert (E37y : ew E3 37 = Z_to_bv 64 (LA_G_NL + 270888 + 8 * nk_n_sent bs)) by (rewrite OLD3 by lia; exact E37).
        assert (U37 : bv_unsigned (ew E3 37) = LA_G_NL + 270888 + 8 * nk_n_sent bs)
          by (rewrite E37y; apply unsigned_lit_small; unfold LA_G_NL; lia).
        assert (Ug3 : bv_unsigned (ew E3 243) = LA_G_NL) by exact (fs_U243 E3 HEIc).
        assert (HGx2 : mem_grows (rdW W memc) (rdW W mem2))
          by exact (mem_grows_trans _ _ _ HGx (fs_grows_of_present _ _ _ Hpr)).
        (* sent_len[n]: an 8-byte region at atom 37, and its shadow entry *)
        lazymatch type of HS with st_ok_pi _ _ _ ?ss2 (restrict _ ?ms2) =>
          assert (HS3 : st_ok_pi SEGS VAL E3 (mkSS (ss_pc ss2) (ss_regs ss2) (fs_X :: ss_mem ss2) (ss_resv ss2)
                     (ss_facts ss2)) (restrict (w_H W) ms2))
        end.
        { apply st_ok_pi_add_region; [exact HS | vm_compute; reflexivity | |].
          + unfold region_ok, fs_X. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
            rewrite U37. split; [unfold LA_G_NL; lia|]. split; [unfold LA_G_NL; lia|]. split; [|constructor].
            intros o Ho. cbn [ms_mem restrict mkst].
            replace (LA_G_NL + 270888 + 8 * nk_n_sent bs + o) with (LA_G_NL + (270888 + 8 * nk_n_sent bs + o)) by lia.
            apply (fs_gwr W memc mem2 bs HNK HGx2). unfold NK_SIZE. lia.
          + apply all_disjoint_of_extents. unfold fs_X, extent_of_region.
            cbn [ss_mem map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U37, Usp3, Ug3.
            cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold LA_G_NL in *. repeat split; lia. }
        clear HS. rename HS3 into HS.
        lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
        assert (SHOK3 : sh_ok SEGS (SOff 32 0) fs_XSH E3 (mrestrict (w_H W) mem2)).
        { apply (fs_shent_ok E3 _ 37 (LA_G_NL + 270888 + 8 * nk_n_sent bs) 8).
          - rewrite (U_atom E3 32 SB E32y) by (unfold SB; lia). reflexivity.
          - apply U_atom; [exact E37y | unfold LA_G_NL; lia].
          - unfold LA_G_NL; lia. - lia. - unfold LA_G_NL, SHADOW_OFF; lia.
          - rewrite <- (aview_rd_of SEGS).
            apply (fs_ra_tr W memc mem2
              (fun a => Zc a \/ (d <= a < d + aarg regs 2) \/ (spZ regs - 48 - 4096 <= a < spZ regs - 48))
              (spZ regs) LA_G_NL NK_SIZE (LA_G_NL + 270888 + 8 * nk_n_sent bs) 8 Hspw).
            + intros a [H | [H | H]]; [exact (HZc a H) | right; unfold d, LA_G_NL, SHADOW_OFF in *; lia | left; lia].
            + intros a Ha Hz.
              rewrite (Hun a Ha (fun H => Hz (or_intror (or_introl H)))
                ltac:(rewrite Usp1, HES; intros H; apply Hz; right; right; lia)).
              exact (UNc a Ha (fun H => Hz (or_introl H))).
            + exact RAG.
            + lia. + unfold NK_SIZE; lia. + unfold LA_G_NL; lia. + unfold LA_G_NL; lia. }
        clear SHOK2.
        set (Z2 := fs_Zs (spZ regs) (P_cp (nk_n_sent bs) (aarg regs 2)) NoE).
        assert (UN2 : forall a, 0 <= a < 2 ^ 64 -> ~ Z2 a -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mm a).
        { intros a Ha Hz. rewrite (Hun a Ha).
          - apply UN; [exact Ha|]. intros H. apply Hz.
            exact (fs_Zs_mono _ _ _ _ _ a (Psn_cp _ _) (fun x Hx => Hx) H).
          - intros Hda. apply Hz. right; left. split; [unfold d, NK_SIZE, LA_G_NL in *; lia|].
            unfold P_cp. right; left. unfold d, NK_SENT, NL_SENT_LEN in *. lia.
          - rewrite Usp1, HES. intros Hw. apply Hz. left. lia. }
        assert (HG2 : mem_grows (rdW W mm) (rdW W mem2))
          by exact (mem_grows_trans _ _ _ HGc (fs_grows_of_present _ _ _ Hpr)).
        clear UN HGc. rename UN2 into UN, HG2 into HGc.
        set (Z3 := fs_Zs (spZ regs)
          (fun i => P_sn i \/ (NK_SENT_LEN + 8 * nk_n_sent bs <= i < NK_SENT_LEN + 8 * nk_n_sent bs + 8)) NoE).
        (* +0xd0 .. +0x124: n_sent := n + 1, the instrumented check of sent_len[n], sent_len[n] := len, ret *)
        paj_run_tok RUN HS HJ3 SHOK3 Bspan; [fs_awr Hajw |].
        fs_kept HFr Z3 UNlast. clear HF HFr.
        lazymatch type of HS with st_ok_pi _ _ ?Ef _ (restrict _ ?msF) =>
          assert (HAEf : env_agree 32 (Ereg regs (fs_extra bs)) Ef)
            by (split; [intros nn Hnn; rewrite ?ew_ewset_other by lia; exact (proj1 HAE3 nn Hnn) | exact (proj2 HAE3)]);
          pose proof (st_ok_pi_region _ _ _ 0 _ HS eq_refl) as HR0;
          pose proof (st_ok_pi_region _ _ _ 2 _ HS eq_refl) as HR2;
          pose proof (st_ok_pi_region _ _ _ 3 _ HS eq_refl) as HR3;
          cbn [ms_mem restrict] in HR0, HR2, HR3;
          assert (Vse : val_mem SEGS (rdW W (ms_mem msF)) (LA_G_NL + 262672) 4 (nk_send_errno bs)) by fs_vfield HR2 Ug3;
          assert (Vns : val_mem SEGS (rdW W (ms_mem msF)) (LA_G_NL + 271016) 4 (nk_n_sent bs + 1)) by fs_vfield HR3 Ug3;
          assert (Vsl : val_mem SEGS (rdW W (ms_mem msF)) (LA_G_NL + (NK_SENT_LEN + 8 * nk_n_sent bs)) 8 (aarg regs 2))
            by (replace (LA_G_NL + (NK_SENT_LEN + 8 * nk_n_sent bs)) with (LA_G_NL + 270888 + 8 * nk_n_sent bs + 0)
                  by (unfold NK_SENT_LEN; lia); fs_vfield8 HR0 U37);
          prreg HS (1%bv : bv 5) R1'; prreg HS (10%bv : bv 5) R10';
          pose proof (aregs_preserved_of_st_ok SEGS _ Ef _ _ regs (fs_extra bs) HS HAEf ltac:(vm_compute; reflexivity))
            as HPr;
          eapply (paj_ret_at (PL := PL_link) (PI := PI) W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
          intros mat';
          rewrite R1', ?E1y, Hret;
          assert (UNz : forall a, 0 <= a < 2 ^ 64 -> ~ Z2 a ->
                    aview SEGS (w_H W) (ms_mem msF) a = aview SEGS (w_H W) mm a)
            by (intros a Ha Hz; rewrite (UNlast a Ha (fun H => Hz (fs_Zs_mono _ _ _ _ _ a
                  (fun i Hi => Pz_cp (nk_n_sent bs) (aarg regs 2) i Hi)
                  (fun x Hx => Hx) H))); exact (UN a Ha Hz));
          assert (UNE : forall a, 0 <= a < 2 ^ 64 -> ~ fs_Zs (spZ regs) (P_copy (nk_n_sent bs) (aarg regs 2)) NoE a ->
                    aview SEGS (w_H W) (ms_mem msF) a = aview SEGS (w_H W) memc a)
            by exact (UNF (P_cp (nk_n_sent bs) (aarg regs 2)) NoE (P_copy (nk_n_sent bs) (aarg regs 2)) (ms_mem msF)
                 (Pbase_copy _ _) (Pcp_copy _ _)
                 UNz);
          assert (Vrq : forall kk, 0 <= kk < aarg regs 2 ->
              mbyte SEGS (rdW W (ms_mem msF)) (LA_G_NL + (NK_SENT + NL_SENT_LEN * nk_n_sent bs) + kk) =
              mbyte SEGS (rdW W memc) (aarg regs 1 + kk));
          [ intros kk Hk; apply fs_mbyte_of_aview2;
            replace (LA_G_NL + (NK_SENT + NL_SENT_LEN * nk_n_sent bs) + kk) with (d + kk)
              by (unfold d, NK_SENT, NL_SENT_LEN; lia);
            rewrite (UNlast (d + kk) ltac:(unfold d, LA_G_NL; lia));
            [ rewrite (Hcp kk Hk); apply UNc; [lia|]; intros [H | H]; exact (RQZ _ (aarg regs 1 + kk) ltac:(lia) H)
            | unfold Z3, fs_Zs, P_sn, NoE; unfold d, NK_SEND_ERRNO, NK_N_SENT, NK_SENT_LEN, NK_SIZE, LA_G_NL in *;
              cbv beta; lia ]
          | ];
          apply (FIN (P_copy (nk_n_sent bs) (aarg regs 2)) NoE (ms_regs msF) (ms_mem msF) _);
          [ apply (ajournal_gx_materialize SEGS B LAWS pa_segs_low); exact HJ3
          | repeat rewrite (proj1 (wvb_fds_fs _ _ _)); rewrite (same_but_materialized_wvb _ _ Hsm);
            repeat rewrite (proj1 (wvb_fds_fs _ _ _)); exact HfdB
          | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); rewrite (same_but_materialized_wvb _ _ Hsm);
            repeat rewrite (proj2 (wvb_fds_fs _ _ _)); exact HfsB
          | exact HPr
          | intros i Hi; unfold P_copy, P_base in Hi;
            unfold NK_SEND_ERRNO, NK_MISUSE, NK_N_SENT, NK_SENT, NK_SENT_LEN, NL_SENT_LEN in *; lia
          | exact NoEe
          | exact UNE
          | exact (mem_grows_trans _ _ _ (mem_grows_trans _ _ _ HGm HGc) HG)
          | apply (fs_post_copy (rdW W memc) (rdW W (ms_mem msF)) regs (ms_regs msF) bs req HNK WF RQ LR
              ltac:(unfold NL_SENT_LEN; lia) SE0 N15
              (fs_gout W memc (ms_mem msF) (spZ regs) _ NoE Hgw NoEe ERRG UNE)
              (fs_gwr W memc (ms_mem msF) bs HNK (mem_grows_trans _ _ _ (mem_grows_trans _ _ _ HGm HGc) HG)) Vse
              (MIS (P_cp (nk_n_sent bs) (aarg regs 2)) NoE (ms_mem msF)
                 ltac:(intros i Hi; unfold P_cp, P_sn in Hi;
                       unfold NK_SEND_ERRNO, NK_MISUSE, NK_N_SENT, NK_SENT, NK_SENT_LEN, NL_SENT_LEN in *; lia)
                 NoEe UNz)
              Vns Vsl Vrq);
            rewrite R10'; rewrite ?E12y; exact (eq_sym A2) ]
        end. }
      psrr_branch_tok RUN BR HS SHOK Bspan.
      * (* len < 512: +0xb8 with a2 = len *)
        rewrite branch_ltu_U, (U_atom E' 12 (aarg regs 2) E12'), U_lit in Hc by lia.
        paj_run_to_tok RUNTO HS HJm SHOK Bspan (AF_fuzz_send + 0xb8); [fs_awr Hajw |].
        fs_kept HFr Z1 UNk. clear HF HFr. fs_fold UN HGc UNk HG W mm Z1.
        lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msB) => rename msB into msb end.
        pmkst HS. prreg HS (12%bv : bv 5) R12.
        fs_norm HS [0; 1; 2; 3; 4]%nat (AF_fuzz_send + 0xb8) [(12%bv : bv 5)] SSB8 HS4.
        apply (CONTB8 _ _ _ _ HEIn
          (fun n Hn => eq_trans (YN3v.ew_havoc_old E' 40 _ n Hn) (OLD n Hn))
          ltac:(transitivity (getr (ms_regs msb) 12%bv); [reflexivity | rewrite R12; exact E12'])
          (env_agree_havoc_ge 32 40 _ E' _ ltac:(lia) HAE') HS4 HJm);
          [ repeat rewrite (proj1 (wvb_fds_fs _ _ _)); exact Hfdm
          | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); exact Hfsm
          | exact UN | exact HGc ].
      * (* len = 512: +0xb4 a2 := 512 *)
        rewrite branch_ltu_U, (U_atom E' 12 (aarg regs 2) E12'), U_lit in Hc by lia.
        apply Z.ltb_ge in Hc. assert (L512 : aarg regs 2 = 512) by lia.
        paj_run_to_tok RUNTO HS HJm SHOK Bspan (AF_fuzz_send + 0xb8); [fs_awr Hajw |].
        fs_kept HFr Z1 UNk. clear HF HFr. fs_fold UN HGc UNk HG W mm Z1.
        lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msB) => rename msB into msb end.
        pmkst HS. prreg HS (12%bv : bv 5) R12.
        fs_norm HS [0; 1; 2; 3; 4]%nat (AF_fuzz_send + 0xb8) [(12%bv : bv 5)] SSB8 HS4.
        apply (CONTB8 _ _ _ _ HEIn
          (fun n Hn => eq_trans (YN3v.ew_havoc_old E' 40 _ n Hn) (OLD n Hn))
          ltac:(transitivity (getr (ms_regs msb) 12%bv); [reflexivity | rewrite R12, L512; reflexivity])
          (env_agree_havoc_ge 32 40 _ E' _ ltac:(lia) HAE') HS4 HJm);
          [ repeat rewrite (proj1 (wvb_fds_fs _ _ _)); exact Hfdm
          | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); exact Hfsm
          | exact UN | exact HGc ].
  - (* send_errno <> 0: +0x68 the call of ___errno_location *)
    rewrite branch_eq_U, (U_atom E' 33 (nk_send_errno bs) E33'), U_lit in Hc by lia.
    apply Z.eqb_neq in Hc. rename Hc into SE.
    set (ZE := fs_Zs (spZ regs) P_sn (aerrno B)).
    assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ ZE a -> aview SEGS (w_H W) mm a = aview SEGS (w_H W) mm a)
      by reflexivity.
    assert (HGc : mem_grows (rdW W mm) (rdW W mm)) by apply mem_grows_refl.
    paj_run_tok RUN HS HJm SHOK Bspan; [fs_awr Hajw |].
    fs_kept HFr ZE UNk. clear HF HFr. fs_fold UN HGc UNk HG W mm ZE.
    lazymatch type of HS with st_ok _ _ _ (restrict _ ?msC) => rename msC into ms1 end.
    pmkst HS.
    prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (4%bv : bv 5) R4.
    rewrite Usp' in R2. rewrite E4' in R4.
    assert (Usp1 : spZ (ms_regs ms1) = spZ regs - 48)
      by (unfold spZ at 1; rewrite R2; apply unsigned_lit_small; lia).
    eapply SRr_bind.
    { eapply (aj_gx_errno_at SK SEGS B LAWS pa_segs_low (pa_sigma LS____errno_location) ERRNO G XO OUT W (ms_regs ms1)
        (ms_mem ms1) STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k _ HGX HJm);
        [rewrite Usp1; lia | rewrite Usp1; lia | exact R1 | apply ret_ok_codeptr_v; lia]. }
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & Hsm & H10 & Hrk & Hm).
    assert (Emem : mem2 = ms_mem ms1) by (apply functional_extensionality; exact Hm). subst mem2. clear Hm.
    assert (HP2 : aregs_preserved (ms_regs ms1) regs2) by (intros r Hr; apply Hrk; unfold acallee_saved in Hr; lia).
    jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W) (ms_mem ms1)) HP2 [0; 3; 4]%nat HS2.
    match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
    { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil;
      (split; [intros; reflexivity | intros; assumption]). }
    clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
    remember (havoc E' 48 (map (getr regs2) CLOB)) as E3 eqn:HE3 in HS.
    assert (HEIe : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc; [exact HEI' | cbv; lia]).
    assert (OLD3 : forall n, (n < 40)%nat -> ew E3 n = ew E n)
      by (intros n Hn; rewrite HE3, YN3v.ew_havoc_old by lia; apply OLD; exact Hn).
    assert (HAE3 : env_agree 32 (Ereg regs (fs_extra bs)) E3)
      by (rewrite HE3; apply env_agree_havoc_ge; [lia | exact HAE']).
    assert (E1x : ew E3 1 = getr regs 1) by (rewrite OLD3 by lia; exact E1).
    assert (Usp3 : bv_unsigned (ew E3 2) = spZ regs) by (rewrite OLD3 by lia; exact Usp).
    assert (E32x : ew E3 32 = Z_to_bv 64 SB) by (rewrite OLD3 by lia; exact E32).
    assert (E33x : ew E3 33 = Z_to_bv 64 (nk_send_errno bs)) by (rewrite OLD3 by lia; exact E33).
    assert (E35x : ew E3 35 = Z_to_bv 64 (nk_n_sent bs)) by (rewrite OLD3 by lia; exact E35).
    assert (Ug3 : bv_unsigned (ew E3 243) = LA_G_NL) by exact (fs_U243 E3 HEIe).
    assert (E52 : ew E3 52 = Z_to_bv 64 (as_errno B)).
    { rewrite HE3. transitivity (getr regs2 10%bv); [reflexivity|].
      transitivity (w64 (bv_unsigned (getr (ms_regs ms1) 4) - 164)); [exact H10|].
      rewrite R4, Htp. unfold w64. rewrite unsigned_lit_small by lia. rewrite ERRA. reflexivity. }
    assert (Uerr : bv_unsigned (ew E3 52) = as_errno B) by (rewrite E52; apply unsigned_lit_small; lia).
    clear HE3.
    (* errno: a 4-byte region at a0 = tp - 164, its range fact and its shadow entry *)
    lazymatch type of HS with st_ok_pi _ _ _ ?ss2 (restrict _ ?ms2) =>
      assert (HS3 : st_ok_pi SEGS VAL E3 (add_atom (mkSS (ss_pc ss2) (ss_regs ss2) (fs_er :: ss_mem ss2)
                 (ss_resv ss2) (ss_facts ss2)) 52 (mkAF 0 (SB - 4) 0)) (restrict (w_H W) ms2))
    end.
    { apply st_ok_pi_add_fact.
      - apply st_ok_pi_add_region; [exact HS | vm_compute; reflexivity | |].
        + unfold region_ok, fs_er. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
          rewrite Uerr. split; [lia|]. split; [lia|]. split; [|constructor].
          intros o Ho. cbn [ms_mem restrict mkst].
          apply (writable_at_grows SEGS (rdW W memc)); [exact (mem_grows_trans _ _ _ HGm HGc) | apply ERRW; lia].
        + apply all_disjoint_of_extents. unfold fs_er, extent_of_region.
          cbn [ss_mem map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Uerr, Usp3, Ug3.
          cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold apart_gnl in ERRG. unfold LA_G_NL, NK_SIZE in *.
          repeat split; lia.
      - unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Uerr. rewrite Z.pow_0_r, Z.mod_1_r.
        unfold SB, kLowMemEnd in *. lia. }
    clear HS. rename HS3 into HS.
    lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
    assert (SHOK3 : sh_ok SEGS (SOff 32 0) fs_erSH E3 (mrestrict (w_H W) (ms_mem ms1))).
    { apply (fs_shent_ok E3 _ 52 (as_errno B) 4).
      - rewrite (U_atom E3 32 SB E32x) by (unfold SB; lia). reflexivity.
      - apply U_atom; [exact E52 | lia].
      - lia. - lia. - unfold kLowMemEnd, SHADOW_OFF in *. lia.
      - rewrite <- (aview_rd_of SEGS).
        apply (fs_ra_tr W memc (ms_mem ms1) (fun a => fs_Zs (spZ regs) P_base NoE a \/ ZE a) (spZ regs)
          (as_errno B) 4 (as_errno B) 4 Hspw).
        + intros a [H | H]; apply (fs_Zs_lowhigh _ _ _ a) in H; [exact H | exact NoEs | exact H | exact ERRSH].
        + intros a Ha Hz. rewrite (UN a Ha (fun H => Hz (or_intror H))). exact (UNm a Ha (fun H => Hz (or_introl H))).
        + exact ERRS.
        + lia. + lia. + lia. + unfold kLowMemEnd in *. lia. }
    clear SHOK.
    (* +0x6c .. +0x124: the instrumented check, errno := send_errno, send_errno := 0, a0 := -1, ret *)
    paj_run_tok RUN HS HJ2 SHOK3 Bspan; [fs_awr Hajw |].
    fs_kept HFr ZE UNk. clear HF HFr. fs_fold UN HGc UNk HG W mm ZE.
    lazymatch type of HS with st_ok_pi _ _ ?Ef _ (restrict _ ?msF) =>
      assert (HAEf : env_agree 32 (Ereg regs (fs_extra bs)) Ef)
        by (split; [intros nn Hnn; rewrite ?ew_ewset_other by lia; exact (proj1 HAE3 nn Hnn) | exact (proj2 HAE3)]);
      pose proof (st_ok_pi_region _ _ _ 2 _ HS eq_refl) as HR2;
      pose proof (st_ok_pi_region _ _ _ 3 _ HS eq_refl) as HR3;
      pose proof (st_ok_pi_region _ _ _ 0 _ HS eq_refl) as HR0;
      cbn [ms_mem restrict] in HR0, HR2, HR3;
      assert (Vse : val_mem SEGS (rdW W (ms_mem msF)) (LA_G_NL + 262672) 4 0) by fs_vfield HR2 Ug3;
      assert (Vns : val_mem SEGS (rdW W (ms_mem msF)) (LA_G_NL + 271016) 4 (nk_n_sent bs)) by fs_vfield HR3 Ug3;
      assert (Verr : val_mem SEGS (rdW W (ms_mem msF)) (as_errno B + 0) 4 (nk_send_errno bs)) by fs_vfield HR0 Uerr;
      rewrite Z.add_0_r in Verr;
      prreg HS (1%bv : bv 5) R1'; prreg HS (10%bv : bv 5) R10;
      pose proof (aregs_preserved_of_st_ok SEGS _ Ef _ _ regs (fs_extra bs) HS HAEf ltac:(vm_compute; reflexivity)) as HPr;
      eapply (paj_ret_at (PL := PL_link) (PI := PI) W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
      intros mat';
      rewrite R1', ?E1x, Hret;
      assert (UNE : forall a, 0 <= a < 2 ^ 64 -> ~ fs_Zs (spZ regs) P_base (aerrno B) a ->
                aview SEGS (w_H W) (ms_mem msF) a = aview SEGS (w_H W) memc a)
        by exact (UNF P_sn (aerrno B) P_base (ms_mem msF) (fun i H => H) PsnB UN);
      apply (FIN P_base (aerrno B) (ms_regs msF) (ms_mem msF) _);
      [ apply (ajournal_gx_materialize SEGS B LAWS pa_segs_low); exact HJ2
      | repeat rewrite (proj1 (wvb_fds_fs _ _ _)); rewrite (same_but_materialized_wvb _ _ Hsm);
        repeat rewrite (proj1 (wvb_fds_fs _ _ _)); exact Hfdm
      | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); rewrite (same_but_materialized_wvb _ _ Hsm);
        repeat rewrite (proj2 (wvb_fds_fs _ _ _)); exact Hfsm
      | exact HPr
      | intros i Hi; unfold P_base in Hi; unfold NK_SEND_ERRNO, NK_MISUSE, NK_N_SENT in *; lia
      | exact (fun a H => H)
      | exact UNE
      | exact (mem_grows_trans _ _ _ HGm HGc)
      | apply (fs_post_err (rdW W memc) (rdW W (ms_mem msF)) regs (ms_regs msF) bs req HNK WF RQ LR SE
          (fs_gout W memc (ms_mem msF) (spZ regs) P_base (aerrno B) Hgw (fun a H => H) ERRG UNE)
          (fs_gwr W memc (ms_mem msF) bs HNK (mem_grows_trans _ _ _ HGm HGc)) Vse
          (MIS P_sn (aerrno B) (ms_mem msF) ltac:(intros i Hi; unfold P_sn in Hi; unfold NK_SEND_ERRNO, NK_MISUSE, NK_N_SENT in *; lia)
             (fun a H => H) UN)
          Vns Verr);
        rewrite R10; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity ]
    end. }
(* +0x00 .. +0x30: the frame, the shadow cell's address, s1 := g, `bne a0, 7` *)
set (Z0 := fs_Zs (spZ regs) P_base NoE).
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W) memc)) by constructor.
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ Z0 a -> aview SEGS (w_H W) memc a = aview SEGS (w_H W) memc a)
  by reflexivity.
assert (HGc : mem_grows (rdW W memc) (rdW W memc)) by apply mem_grows_refl.
paj_run_tok RUN HS HJ SHOK Bspan; [fs_awr Hajw |].
fs_kept HFr Z0 UNk. clear HF HFr. fs_fold UN HGc UNk HG W memc Z0.
(* the three ways to +0x64, each normalized to SS64 *)
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* a0 <> 7: misuse := 1 *)
  rewrite branch_ne_U, (U_atom E 10 (aarg regs 0) E10), U_lit in Hc by lia.
  apply negb_true_iff, Z.eqb_neq in Hc.
  paj_run_tok RUN HS HJ SHOK Bspan; [fs_awr Hajw |].
  fs_kept HFr Z0 UNk. clear HF HFr. fs_fold UN HGc UNk HG W memc Z0.
  assert (Hv : sv_denot E (SLit 1) = Z_to_bv 64 (snd_mis (aarg regs 0) bs))
    by (unfold snd_mis, NL_FD; rewrite (proj2 (Z.eqb_neq _ _) Hc); reflexivity).
  fs_mis HS Ug Hv (snd_mis (aarg regs 0) bs) VMI.
  pmkst HS. fs_norm HS [0; 1; 2; 3; 6]%nat (AF_fuzz_send + 0x64) [(13%bv : bv 5)] SS64 HS4.
  apply (CONT64 _ _ _ _ HEIn
    (fun n Hn => YN3v.ew_havoc_old E 40 _ n Hn) (env_agree_havoc_ge 32 40 _ E _ ltac:(lia) HAE) HS4 HJ);
    [ repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
    | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity
    | exact UN | exact HGc | exact VMI ].
- (* a0 = 7: +0x34..+0x40 load open, `bnez` *)
  rewrite branch_ne_U, (U_atom E 10 (aarg regs 0) E10), U_lit in Hc by lia.
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hfd.
  paj_run_tok RUN HS HJ SHOK Bspan; [fs_awr Hajw |].
  fs_kept HFr Z0 UNk. clear HF HFr. fs_fold UN HGc UNk HG W memc Z0.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* open <> 0: misuse is left *)
    rewrite branch_ne_U, (U_atom E 34 (nk_open bs) E34), U_lit in Hc by lia.
    apply negb_true_iff, Z.eqb_neq in Hc.
    paj_run_tok RUN HS HJ SHOK Bspan; [fs_awr Hajw |].
    fs_kept HFr Z0 UNk. clear HF HFr. fs_fold UN HGc UNk HG W memc Z0.
    assert (Hv : sv_denot E (SOff 36 0) = Z_to_bv 64 (snd_mis (aarg regs 0) bs))
      by (unfold snd_mis, NL_FD; rewrite Hfd, (proj2 (Z.eqb_neq _ _) Hc);
          cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    fs_mis HS Ug Hv (snd_mis (aarg regs 0) bs) VMI.
    pmkst HS. fs_norm HS [0; 1; 2; 3; 6]%nat (AF_fuzz_send + 0x64) [(13%bv : bv 5)] SS64 HS4.
    apply (CONT64 _ _ _ _ HEIn
      (fun n Hn => YN3v.ew_havoc_old E 40 _ n Hn) (env_agree_havoc_ge 32 40 _ E _ ltac:(lia) HAE) HS4 HJ);
      [ repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
      | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity
      | exact UN | exact HGc | exact VMI ].
  + (* open = 0: misuse := 1 *)
    rewrite branch_ne_U, (U_atom E 34 (nk_open bs) E34), U_lit in Hc by lia.
    apply negb_false_iff, Z.eqb_eq in Hc.
    paj_run_tok RUN HS HJ SHOK Bspan; [fs_awr Hajw |].
    fs_kept HFr Z0 UNk. clear HF HFr. fs_fold UN HGc UNk HG W memc Z0.
    assert (Hv : sv_denot E (SLit 1) = Z_to_bv 64 (snd_mis (aarg regs 0) bs))
      by (unfold snd_mis, NL_FD; rewrite Hfd, Hc; reflexivity).
    fs_mis HS Ug Hv (snd_mis (aarg regs 0) bs) VMI.
    pmkst HS. fs_norm HS [0; 1; 2; 3; 6]%nat (AF_fuzz_send + 0x64) [(13%bv : bv 5)] SS64 HS4.
    apply (CONT64 _ _ _ _ HEIn
      (fun n Hn => YN3v.ew_havoc_old E 40 _ n Hn) (env_agree_havoc_ge 32 40 _ E _ ltac:(lia) HAE) HS4 HJ);
      [ repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
      | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity
      | exact UN | exact HGc | exact VMI ].
Qed.
End w.

Print Assumptions fuzz_send_aproof.
