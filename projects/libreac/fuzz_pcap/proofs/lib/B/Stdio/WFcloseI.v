From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10 (a Theorem Labs lane): fclose at the ASAN-UBSAN interceptor entry on
   libreac/fuzz_pcap's v1.9.0 asan-ubsan image, for the fmemopen READ stream: PFclose.v's
   afclose_source_spec at IC_ENTRY_U = __interceptor_trampoline_fclose 0x4161c (lib/B/Stdio/PStdioImgB.v).

   This is the asan-ubsan twin of a Theorem Labs lane's own proved ASan walk lib/A/Stdio/WFcloseI.v
   (a working branch c5c211d4244, theorem afclose_source_spec_icpt): the STRUCTURE is ported from
   that file, every ADDRESS is measured on this image, and no released proof was read for the structure
   (rule 24 lookup, CONFIRMED: at ossv/recipes 25e3d17bdb50 (2026-10-29), no released proof stated fclose on ANY pcap ASan image; pcap's released
   hits were the PLAIN lib/Prog and UBSAN lib/U/Prog images only, output
   fclose.out (sha256 e903a25b7bc1; internal record)). The released PLAIN files were read for
   facts and pcs only, never imported, and no PLAIN-model file is imported here.

   NOTHING IS RE-WALKED HERE. The interceptor's two machine walks are the asan-ubsan twins in
   lib/Reusable/YE2e.v (the au twin of lib/A/AE2e.v, on a working branch 529392df4fe):
     iclose_front   0x4161c -> 0x467f0 ___interceptor_fclose (frame 96), TryAsanInitFromRtl (0x598e4),
                    the AddrHashMap metadata pair (0x47b7c acquire / 0x4839c release), up to `jalr a1`
                    at 0x46884, i.e. the pc IC_REAL = 0x8e0e0 (musl fclose) with ra = IC_RET = 0x46888;
     iclose_tail    0x46888 -> `ret` at 0x46938, on the path s3 = 0 (no metadata entry for f).
   This file composes them with musl fclose's contract, taken as the ONE callee hypothesis
   pcapu_afclose_source_spec_musl, in the interface a Theorem Labs lane ruled with a working branch c625af6eaa9
   (PFclose.v's afclose_source_spec_stk / PFCLOSE_MUSL_STK):
     afclose_source_spec_stk SK tfibsegs B pcap_KS PFCLOSE_MUSL_STK PFCLOSE_MUSL_U 0x8e184 0x8e18c rlo rhi.
   The two free return addresses are the SAME at both entries: the frees happen inside musl fclose
   (0x8e180 / 0x8e188), so the trace prefixes [pc_free_ra0; 0x8e184] and [pc_free_ra0; 0x8e18c] pass
   through.

   EVERY ADDRESS MEASURED ON THIS IMAGE, by symbol + offset, never by a delta from the asan image.
   Tools: the unit's own dumps fuzz_pcap.nm.txt and
   fuzz_pcap.objdump.txt (sha256 49b2ad826669, af7c8be930de; internal record; of the image with sha256 c969d83cdd5943a8..., the
   pinned fuzz_pcap.asan-ubsan image's unstripped twin byte for byte), and
   a Python PT_LOAD reader for the data words. That twin's PT_LOADs equal the PINNED
   fuzz_pcap.asan-ubsan image (sha256 9e66f771f22af67a..., the sha256
   projects/libreac/fuzz_pcap/harness.yaml pins for build asan-ubsan) at every byte except 24 in the ELF
   header and the build-id note (0x10029, 0x1002a, 0x1003c, 0x1003e, 0x102b8..0x102cb) -- none of them an
   address this file uses.
     trampoline     __interceptor_trampoline_fclose  0x4161c  nm 'T', size 4; `j 467f0` (objdump)
     interceptor    ___interceptor_fclose            0x467f0  nm 'T', size 0x1ac
     frame          96                               `addi sp,sp,-96` at 0x467f0 (asan: the same 96)
     call of REAL   `jalr a1` at 0x46884, a1 = the word at 0x9b4c0; IC_RET = 0x46888
     REAL(fclose)   0x8e0e0  nm 'W' fclose (a WEAK symbol: a t/T-only lookup drops it), size 0xcc
     musl frees     `jal 52c24 <__interceptor_trampoline_free>` at 0x8e180 and 0x8e188, so the two
                    return pcs are 0x8e184 and 0x8e18c
   THE THREE CheckFailed EDGES, all behind a `beqz s3`, all off the path (see THE FRONT'S PREMISES):
     0x4685c `bnez a0` -> 0x4693c and 0x46868 `bne a0,a1` -> 0x4695c, both behind `beqz s3` at 0x46854;
     0x468c4 `beqz a0` -> 0x4697c, behind `beqz s3` at 0x46888.
   Each of the three calls _ZN11__sanitizer11CheckFailedEPKciS1_yy 0x6b968. R2: no route steps past a
   report entry -- the symbolic runs stop at IC_REAL (RS_running) and at the final `ret` (SR_jalr), and
   neither reaches a CheckFailed or __asan_report_* entry at all.
   THE CONST CELLS THE FRONT READS, keyed by symbol (ic_cells of YE2e.v), each word READ OUT OF THE ELF:
     0x9b4b8  nm 'd' _ZN14__interception11real_fflushE -> 0x8e308 (nm 'W' fflush)   [asan: 0x9b5f0]
     0x9b4c0  nm 'd' _ZN14__interception11real_fcloseE -> 0x8e0e0 (nm 'W' fclose)   [asan: 0x9b5f8]
     0xa1000  nm 'b' _ZL24interceptor_metadata_map     -> 0xa1008                   [asan: 0xa1100]
              0xa1008 = nm 'b' _ZZL28InitializeCommonInterceptorsvE12metadata_mem   [asan: 0xa1108]
     0x103a0  .rodata, the AddrHashMap mask 0xafffff00000fffff, read inside acquire at 0x47be8
              (asan reads the same 0x103a0 at 0x47b98: this one cell is at the SAME address in both
              images -- MEASURED in each image's own .rodata, not assumed)
   The front's other image read, 0x103d0 (0xaaaaaaaaaaaaaaaa, at 0x46818), is not a const cell: it lies
   in YE2e's imgC window 0x103b8..0x10420 and is taken from the image itself.

   THE STACK. The interceptor runs musl fclose 96 bytes deeper (addi sp,sp,-96 at 0x467f0), so the budget
   it can grant is PFCLOSE_STK - 96 = PFCLOSE_MUSL_STK; afn_pre_at's side condition `STK1 - o <= STK`
   reads 16432 + 96 <= 16528 (exactly tight). The journals compose with ajournal_sub_tok, NOT the
   library's ajournal_sub (the footprint asource_fp f carries YI16.sink_token).

   WHY ajournal_sub_tok IS COPIED HERE. Its home is lib/A/Prog/YC85.v:33 (image-generic: a Section over
   any segs / B). Requiring that file would drag lib/A/Prog/{PcapSyms, PcapList, PcapPa, PaRun, PaShadow,
   PaSym, PaTable} -- the ASan program-walk layer, whose listing tables are this unit's ASan addresses --
   into this asan-ubsan file's Require closure, which the lib/B closure rule forbids. Section 0 below is
   that lemma's text, unchanged but for its name, over this file's own Section variables; every lemma it
   uses (ajournal, al_layout, al_blocks, sep_blocks, sep_block_frame, frames_bounds, apresent_transfer,
   aos_step_trans_fp, shadow_addr_bounds, shadow_range_end, asan_consts) is lib/Reusable/YCbq.v's, which
   is image-free and shared by both images.

   THE FRONT'S PREMISES, each derived from the statement's own premises:
     cells_hold ic_cells   the four words 0x9b4b8 / 0x9b4c0 (REAL fflush / REAL fclose), 0xa1000 (the
                           metadata map pointer) and 0x103a0 (the hash mask) are all Tfib_const cells
                           (lib/Reusable/YF0m.v), so AR's am_const pins them (YF0x.tfib_const_lookup);
                           rodata_chk checks them by vm_compute;
     ro_img                from the statement's arodata_okS, chunk by chunk (the port of cgif
                           lib/A/AE24.v:36 ffc_ro_img_of_arodata);
     meta_pre              from asrc_meta_inv: the bucket region is all zero, so the AddrHashMap lookup
                           finds no entry (s3 = 0). Every CheckFailed edge of the interceptor is then off
                           the path (the three listed above). The symbolic runs decide each branch from
                           these facts: iclose_front's run reaches IC_REAL with RS_running and ra =
                           IC_RET, iclose_tail's run stops only at the final `ret` (SR_jalr).

   SECTION HYPOTHESES (no axiom, no Admitted; AR_laws is not one: YG0q.AR_laws_ok):
     TB                             PcapSyms B: the asan-ubsan symbol record's image law
                                    (lib/Reusable/YF0m.v, the generated au base, gated PASS A+B), the hypothesis
                                    iclose_front itself carries;
     pcapu_afclose_source_spec_musl musl fclose's contract at 0x8e0e0 (proved by the theorem of this name in
                                    lib/B/Stdio/WFclose.v).
   The symbol record is pcap_KS of lib/B/Stdio/PSourceK.v (a Theorem Labs lane's asan-ubsan instance KS_U, auditor
   PASSED 18/18, on a working branch b4439851fa3) -- NOT lib/A/Stdio/PSourceK.v, whose pcap_KS
   is the ASan one.

   SOURCE OF EVERY CONSTANT NOT MEASURED HERE:
     PFCLOSE_STK 16528, PFCLOSE_MUSL_STK 16432, afclose_source_spec(_stk), asource_at, asrc_meta_inv
       a working branch c625af6eaa9 (lib/A/Stdio/PFclose.v, PSource.v, PSourceMeta.v) -- the
       image-generic statement files, used for their statement Definitions only;
     pcap_KS (KS_U)  a working branch b4439851fa3 (lib/B/Stdio/PSourceK.v);
     IC_ENTRY_U 0x4161c  a working branch b4439851fa3 (lib/B/Stdio/PStdioImgB.v, the one home of the
       asan-ubsan stdio pcs); it is YE2e's IC_ENTRY, by reflexivity (wfi_ic_entry_u below);
     IC_REAL / IC_RET / IC_FRAME / IC_STK / ic_cells / SAVEDC / KEPTC / KEPTT / iclose_front /
     iclose_tail, tfibsegs = AsanUbsan.M.loaded_segments, Tfib_const / PcapSyms, img_ro_chunks
       a working branch 83eefd767e6 (lib/Reusable/YE2e.v, YB1v.v, YF0m.v, YE3i.v, YE2y.v,
       YE2h.v, YF0x.v, YCeg.v). That sha MERGES a working branch 6927e0d899c, so the
       generated set (YF0m / YB1v / YB1k / YD2j / YB01 / YB03 / YB05 / YB12 / YB1h / YD2i) is 6927e0d899c's
       text byte for byte and 6927e0d899c is an ancestor of 83eefd767e6: the union names 83eefd767e6 alone for the au
       layer. It also carries the image-end fix in YF0x's unfold lists and YE3i rebuilt from the pin
       (IMG_RO_HI 0x2ee90, the 14-chunk complement of YF0m's owned rows).

   THE BUILD TREE, by EXACT pushed sha, never "or newer". A LOCAL union, never pushed, of
     this file's own working branch   (the branch that added this file, at 71d854e21c6)
     a working branch 83eefd767e6   (merges a working branch 6927e0d899c; it is 529392df4fe,
                                              on which this file was first proved, plus the five
                                              repairs YE3n / YE2v / YFfg / YFkz / YFkm)
     a working branch    595c3188fe3
     a working branch    b4439851fa3   (lib/B/Stdio/PSourceK.v, PStdioImgB.v; d6edf2117df
                                              is its ancestor)
   Every member is BUILD TREE ONLY: none is merged into this branch. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI04 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YE00 YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YE01 YG0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YB1v YF0m YF0x YE2y YE3i YE2h YE2e.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YCeg.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PFclose.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Stdio Require Import PStdioImgB.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Stdio Require Import PSourceK.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* 0. ajournal_sub_tok, the text of lib/A/Prog/YC85.v:33 (see WHY ... IS COPIED HERE above).        *)
(*                                                                                                  *)
(* lib/Reusable/YE2e.v turns lia's div / mod handling OFF for every file that Requires it           *)
(* (`Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).`, YE2e.v:27).  *)
(* YC85.v does not Require it, so the proof below was elaborated with that handling ON, and its     *)
(* shadow_addr steps (x / 8) need it. The flag is therefore turned on for this Section only and put *)
(* back to YE2e's value at End J, so every later proof in this file sees exactly YE2e's setting.    *)
(* Both redefinitions are LOCAL to this file: neither escapes the Require, so a file that Requires  *)
(* this one keeps its own setting.                                                                  *)
(* ---------------------------------------------------------------------------------------------- *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section J. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Lemma wfi_ajournal_sub_tok : forall STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k STK1 sp1 FP1 nf ly2 S2 W2 mem2 md2 k1,
ajournal segs B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
ajournal segs B STK1 sp1 FP1 lyc Sc Wc memc mdc nf ly2 S2 W2 mem2 md2 k1 ->
sp0 - STK <= sp1 - STK1 -> sp1 <= sp0 ->
(forall a, inFP FP1 a -> inFP FP a \/ in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
ajournal segs B STK sp0 FP ly S W mem md (nf ++ own) ly2 S2 W2 mem2 md2 (k + k1).
Proof.
intros STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k STK1 sp1 FP1 nf ly2 S2 W2 mem2 md2 k1
(HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT)
(HAR2 & Hly2 & Hsecs2 & Hwle2 & Hio2 & Hfrs2 & Hnev2 & Hk2 & G1 & G2 & G3 & G4 & Hgone2 & Hpres2 & Hstatic2 & G5 & HQT2) Hlo Hhi HF.
pose proof Hstatic as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly2 HAR Hly2) as (Eab & Efa & Eown).
split; [exact HAR2|].
split; [eapply layout_le_trans; [exact Hsecs | exact Hly | exact Hly2]|].
split; [zlia|]. split; [eapply wle_trans; eassumption|].
assert (HFo : YI16.sink_open_fp FP1 -> YI16.sink_open_fp FP).
{ intros (r & Hr & H0). destruct (HF 0 (ex_intro _ r (conj Hr H0))) as [(r' & Hr' & H0') | (b & n & Hin & _ & Hb)].
- exists r'. split; [exact Hr' | exact H0'].
- exfalso. pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & H4096 & _). zlia. }
split; [eapply aos_step_trans_fp; [exact HFo | exact Hio | exact Hio2]|].
split; [rewrite Hfrs2, Hfrs, app_assoc; reflexivity|]. split; [zlia|]. split; [zlia|].
split.
{   intros a Ha Hs. rewrite <- (F1 a Ha Hs). apply G1; [exact Ha | zlia]. }
split.
{   intros p n i H1 H2 Hi Hnf.
assert (Hc2 : In (p, n) (ablocks B lyc Sc)).
{ destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (p, n) (ablocks B lyc Sc)) as [Hc|Hc]; [exact Hc|].
exfalso. exact (Hnf (Hgone p n i H1 Hc Hi)). }
rewrite <- (F2 p n i H1 Hc2 Hi Hnf). apply (G2 p n i Hc2); [exact H2 | exact Hi |].
intros Hf1. destruct (HF _ Hf1) as [Hf | (b & m & Hbin & Hb0 & Hr)]; [exact (Hnf Hf)|].
assert (Hne : (b, m) <> (p, n)) by (intros E; rewrite E in Hb0; exact (Hb0 H1)).
pose proof (sep_blocks segs B LAWS lyc Sc Wc memc mdc b m p n HAR Hbin Hc2 Hne) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia. }
split.
{   intros a Hi Hns He Hsp. rewrite <- (F3 a Hi Hns He Hsp). apply (G3 a Hi Hns He). intros Ho1. exact (Hsp (HFo Ho1)). }
split.
{   intros cid pos a Hin Hr Hnf. rewrite <- (F4 cid pos a Hin Hr Hnf).
assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
assert (Efr : frame_addr lyc cid pos = frame_addr ly cid pos).
{ unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
apply (G4 cid pos a HinC).
- unfold frame_rng in *. cbn [fst snd] in *. rewrite Efr. exact Hr.
- intros Hf1. destruct (HF _ Hf1) as [Hf | (b & m & Hbin & Hb0 & Hrb)]; [exact (Hnf Hf)|].
destruct (frames_bounds segs B LAWS lyc Sc Wc memc mdc cid pos HAR HinC) as (Hf0 & Hfc & Hfh).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc b m HAR Hbin) as (_ & _ & _ & [Hh1 Hh2] & _).
pose proof (sep_block_frame segs B LAWS lyc Sc Wc memc mdc b m cid pos HAR Hbin HinC) as Hd.
unfold zdisjoint, frame_rng, in_zr in *. cbn [fst snd] in *. rewrite Efr in Hd.
pose proof (shadow_addr_bounds (frame_addr ly cid pos) ltac:(zlia)).
pose proof (shadow_addr_bounds (frame_addr ly cid pos + fs_frame_bytes cid) ltac:(zlia)).
pose proof (shadow_range_end (frame_addr ly cid pos) (fs_frame_bytes cid) (fs_frame_bytes_nonneg cid)).
destruct Hr as [Hr|Hr]; zlia. }
split.
{   intros p n i H1 H2 Hi.
destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (p, n) (ablocks B lyc Sc)) as [Hc|Hc]; [|exact (Hgone p n i H1 Hc Hi)].
assert (Hf1 : inFP FP1 (p + i)) by (apply (Hgone2 p n i Hc); [exact H2 | exact Hi]).
destruct (HF _ Hf1) as [Hf | (b & m & Hbin & Hb0 & Hr)]; [exact Hf|].
assert (Hne : (b, m) <> (p, n)) by (intros E; rewrite E in Hb0; exact (Hb0 H1)).
pose proof (sep_blocks segs B LAWS lyc Sc Wc memc mdc b m p n HAR Hbin Hc Hne) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia. }
split.
{   intros a Ha.
destruct (Z_lt_le_dec a (sp1 - STK1)) as [Hb|Hb]; [|destruct (Z_lt_le_dec a sp1) as [Hb2|Hb2]; [apply Hpres2; zlia|]].
- eapply (apresent_transfer segs); [zlia | intros Him; pose proof (segs_low a Him); zlia | apply G1; zlia | apply Hpres; exact Ha].
- eapply (apresent_transfer segs); [zlia | intros Him; pose proof (segs_low a Him); zlia | apply G1; zlia | apply Hpres; exact Ha]. }
split; [exact Hstatic|]. split; [|exact HQT2].
{   intros a HXa He. rewrite <- (F5 a HXa He).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eextra & _).
apply G5; [rewrite Eextra; exact HXa | exact He]. }
Qed.
End J.
(* back to YE2e's setting for the rest of the file; LOCAL, as the one above Section J. *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* The return addresses of musl fclose's two free calls (0x8e180 / 0x8e188), MEASURED (objdump);
   a Theorem Labs lane measured the same two independently (WF_FREE1 / WF_JOIN, 03:5xZ). *)
Definition WFI_FREE1 : Z := (symaddr (Symbols.AsanUbsan.s_fclose + 0xa4)%Z).
Definition WFI_JOIN  : Z := (symaddr (Symbols.AsanUbsan.s_fclose + 0xac)%Z).

(* musl fclose's entry: PStdioImgB.v's PFCLOSE_MUSL_U, the one home of the asan-ubsan stdio pcs, as
   the hypothesis below names it, so that hypothesis is a Theorem Labs lane's theorem verbatim
   (a working branch 698f66b40c5). It is the word KS_U's icell list pins at the GOT slot
   0x9b4c0 (PSourceK.v's PCAP_REAL_FCLOSE) and the pc YE2e's front hands over to (IC_REAL); the
   statement's entry IC_ENTRY_U is the pc YE2e's front starts at (IC_ENTRY). *)
Lemma wfi_musl_entry_u : PFCLOSE_MUSL_U = PCAP_REAL_FCLOSE.
Proof. reflexivity. Qed.
Lemma wfi_real_fclose_is_IC_REAL : PCAP_REAL_FCLOSE = IC_REAL.
Proof. reflexivity. Qed.
Lemma wfi_ic_entry_u : IC_ENTRY_U = IC_ENTRY.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* 1. Small facts.                                                                                  *)
(* ---------------------------------------------------------------------------------------------- *)
(* A return address the caller vouches for (ret_ok) is even: the inverse of YK0s.ret_ok_even. *)
Lemma wfi_ret_ok_even : forall k : word, YK0s.ret_ok k -> bv_unsigned k mod 2 = 0.
Proof.
intros k Hk. unfold YK0s.ret_ok, v_jalr, jalr_tgtZ in Hk. rewrite <- Hk. rewrite Z_to_bv_unsigned.
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.add_0_r.
assert (E : Z.land (bv_unsigned k) (-2) = (bv_unsigned k / 2) * 2).
{ change (-2) with (Z.lnot (Z.ones 1)). rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity. }
rewrite E. replace (2 ^ 64) with (2 ^ 63 * 2) by reflexivity.
rewrite Z.mul_mod_distr_r by lia. apply Z_mod_mult.
Qed.

Lemma wfi_in_img_of_b : forall a,
  existsb (fun s => (Z.of_N (seg_base s) <=? a) && (a <? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs = true ->
  in_img tfibsegs a.
Proof.
intros a Hb. apply existsb_exists in Hb as (s & Hs & Hc). apply andb_prop in Hc as [H0 H1].
apply Z.leb_le in H0. apply Z.ltb_lt in H1. exists s. split; [exact Hs | lia].
Qed.

(* The last page of the image: any address the meta region must lie above. *)
Lemma wfi_img_top_page : in_img tfibsegs (symaddr Symbols.AsanUbsan.s_std_name).
Proof. apply wfi_in_img_of_b. vm_compute. reflexivity. Qed.

(* The read-only segment covers IMG_RO_LO .. IMG_RO_HI. *)
Lemma wfi_seg_ro : exists s, In s tfibsegs /\ seg_writable s = false /\
  Z.of_N (seg_base s) <= IMG_RO_LO /\ IMG_RO_HI <= Z.of_N (seg_base s) + Z.of_N (seg_size s).
Proof.
assert (Hb : existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? IMG_RO_LO) &&
  (IMG_RO_HI <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs = true) by (vm_compute; reflexivity).
apply existsb_exists in Hb as (s & Hs & Hc). apply andb_prop in Hc as [Hc H2]. apply andb_prop in Hc as [H0 H1].
exists s. split; [exact Hs|]. split; [destruct (seg_writable s); [discriminate | reflexivity]|].
split; [apply Z.leb_le; exact H1 | apply Z.leb_le; exact H2].
Qed.

Lemma wfi_ro_chunks_unowned :
  forallb (fun c => forallb (fun r => (fst r + snd r <=? YP09.c_off c) || (YP09.c_off c + c_len c <=? fst r))
    Tfib_owned_static) img_ro_chunks = true.
Proof. vm_compute. reflexivity. Qed.

Lemma wfi_ic_cells_chk : forall ly, rodata_chk ly ic_cells = true.
Proof. intros ly. vm_compute. reflexivity. Qed.

Lemma wfi_wvb_io : forall l X (m : Model), m_fds (with_vm_backing l X m) = m_fds m /\ m_fs (with_vm_backing l X m) = m_fs m.
Proof. intros l X m. destruct m. split; reflexivity. Qed.

Lemma wfi_env_low : forall a, asrc_env_addr pcap_KS a -> 0 <= a < 0x7fff8000.
Proof.
intros a Ha. cbv [asrc_env_addr pcap_KS as_threaded as_need_locks as_ofl_lock as_mode as_rwa as_canary
  PCAP_THREADED PCAP_NEED_LOCKS PCAP_OFL_LOCK PCAP_MODE PCAP_RWA PCAP_CANARY] in Ha. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* 2. The stream predicate across a change that keeps its bytes. Copied from a Theorem Labs lane's  *)
(*    lib/A/Stdio/WFflush.v (a working branch ad383186b6f): vm_fr, head_env_addr, env_tr,           *)
(*    asource_at_tr. None of them needs the stream's image laws.                                    *)
(* ---------------------------------------------------------------------------------------------- *)
Section T.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable K : asource_syms.

Lemma wfi_vm_fr : forall (m m' : word -> option byte) a (n : nat) v,
  (forall x, a <= x < a + Z.of_nat n -> mbyte segs m' x = mbyte segs m x) ->
  val_mem segs m a n v -> val_mem segs m' a n v.
Proof. intros m m' a n v Hfr Hv k Hk. rewrite Hfr by lia. exact (Hv k Hk). Qed.

Lemma wfi_head_env_addr : forall a, as_ofl_head K <= a < as_ofl_head K + 8 -> asrc_env_addr K a.
Proof. intros a Ha. unfold asrc_env_addr, as_ofl_head in *. lia. Qed.

Lemma wfi_env_tr : forall m m', asrc_stdio_env segs K m ->
  (forall a, asrc_env_addr K a -> mbyte segs m' a = mbyte segs m a) -> asrc_stdio_env segs K m'.
Proof.
intros m m' (E1 & E2 & E3 & E4 & E5 & (cv & Hcv & E6)) Hk. unfold asrc_env_addr in Hk.
split; [eapply wfi_vm_fr; [|exact E1]; intros x Hx; simpl Z.of_nat in Hx; apply Hk; lia|].
split; [eapply wfi_vm_fr; [|exact E2]; intros x Hx; simpl Z.of_nat in Hx; apply Hk; lia|].
split; [eapply wfi_vm_fr; [|exact E3]; intros x Hx; simpl Z.of_nat in Hx; apply Hk; lia|].
split; [eapply garr8_frame; [exact E4|]; intros x Hx; unfold src_mode_Z in Hx; simpl in Hx; apply Hk; lia|].
split; [eapply garr8_frame; [exact E5|]; intros x Hx; unfold src_modeset_Z in Hx; simpl in Hx; apply Hk; lia|].
exists cv. split; [exact Hcv|]. eapply wfi_vm_fr; [|exact E6]. intros x Hx. simpl Z.of_nat in Hx. apply Hk. lia.
Qed.

Ltac vfr HF H :=
  eapply wfi_vm_fr; [|exact H];
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; simpl Z.of_nat in Hx;
  unfold SRC_COOKIE_OFF, SRC_BUF_OFF, SRC_BUFSIZ, SRC_FILE_BLOCK in *; apply HF; lia.
Ltac vfr_auto HF :=
  lazymatch goal with |- val_mem _ _ ?a ?n ?v =>
    match goal with H : val_mem _ _ a n v |- _ => vfr HF H end end.

Lemma wfi_asource_at_tr : forall m m' f b C p, asource_at segs K m f b C p ->
  (forall a, f <= a < f + SRC_FILE_BLOCK -> mbyte segs m' a = mbyte segs m a) ->
  (forall a, b <= a < b + Z.of_nat (length C) -> mbyte segs m' a = mbyte segs m a) ->
  (forall a, asrc_env_addr K a -> mbyte segs m' a = mbyte segs m a) ->
  asource_at segs K m' f b C p.
Proof.
intros m m' f b C p (Wn & cpos & fl & mdv & HX) HF Hb He. cbv zeta in HX.
destruct HX as (Hp0 & Hpc & Hcn & Hn63 & Hbw & Hcp & HWd & Hbok & HC & HST & HWIN & HFL & HFL24 & HMD & HCK &
  HENV & HHD & Hfnz).
destruct HST as (S24 & S64 & S72 & S80 & S88 & S96 & Sc8 & Sc16 & Sc24 & Sc32 & S152 & S32 & S40 & S48 & S56 &
  S104 & S112 & S168 & S120 & S140 & S144 & Sf0 & Sf16 & Sb0 & Sdisj).
destruct HFL as [HFL HFLv]. destruct HMD as [HMD HMDv].
exists Wn, cpos, fl, mdv. cbv zeta.
do 8 (split; [assumption|]).
split; [eapply garr8_frame; [exact HC | exact Hb]|].
split.
{ do 21 (split; [vfr_auto HF|]). repeat split; assumption. }
split.
{ destruct HWIN as [(HW0 & H8 & H16) | (i & Hi0 & Hi1 & H8 & H16 & HG)].
  - left. split; [exact HW0|]. split; [vfr HF H8 | vfr HF H16].
  - right. exists i. split; [exact Hi0|]. split; [exact Hi1|].
    split; [vfr HF H8|]. split; [vfr HF H16|].
    eapply garr8_frame; [exact HG|]. intros a Ha. unfold SRC_BUF_OFF, SRC_BUFSIZ, SRC_FILE_BLOCK in *. apply HF. lia. }
split; [split; [vfr HF HFL | exact HFLv]|].
split; [exact HFL24|].
split; [split; [vfr HF HMD | exact HMDv]|].
split; [vfr HF HCK|].
split; [exact (wfi_env_tr m m' HENV He)|].
split; [eapply wfi_vm_fr; [|exact HHD]; intros x Hx; apply He, wfi_head_env_addr; simpl Z.of_nat in Hx; lia|].
exact Hfnz.
Qed.

End T.

(* ---------------------------------------------------------------------------------------------- *)
(* 3. The composition.                                                                              *)
(* ---------------------------------------------------------------------------------------------- *)
Section I.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} (SK : YI16.sink_head).
Variable B : asyms.
Variables rlo rhi : Z.
(* The asan-ubsan symbol record's image law (lib/Reusable/YF0m.v, the au twin of lib/A/AF0m.v):
   iclose_front's own hypothesis. *)
Hypothesis TB : PcapSyms B.
(* musl fclose's contract at its own entry and budget (owner a Theorem Labs lane, the asan-ubsan musl fclose walk). *)
Hypothesis pcapu_afclose_source_spec_musl :
  afclose_source_spec_stk SK tfibsegs B pcap_KS PFCLOSE_MUSL_STK PFCLOSE_MUSL_U WFI_FREE1 WFI_JOIN rlo rhi.
(* The allocator laws hold of ANY segs and B (YG0q.v:805, no Section hypothesis). *)
Let LAWS : AR_laws tfibsegs B := YG0q.AR_laws_ok tfibsegs B.
Local Notation rd W mem := (mrestrict (w_H W) mem).

(* The front's four image words are all Tfib_const cells, so AR's am_const pins them. *)
Lemma wfi_cells_hold_of_chk : forall l ly S (H : word -> bool) mem,
  rodata_chk ly l = true -> ARm B ly S (aview tfibsegs H mem) -> cells_hold (mrestrict H mem) l.
Proof.
intros l ly S H mem Hc HM. unfold rodata_chk in Hc. unfold cells_hold.
rewrite forallb_forall in Hc. apply Forall_forall. intros [[base sz] cs] Hin.
specialize (Hc _ Hin). cbn [fst snd] in Hc |- *. apply andb_prop in Hc as [Hc Hcs]. apply andb_prop in Hc as [H0 Hhi].
apply Z.leb_le in H0. apply Z.leb_le in Hhi.
split; [exact H0|]. split; [exact Hhi|].
rewrite forallb_forall in Hcs. apply Forall_forall. intros [[off n] v] Hc'.
specialize (Hcs _ Hc'). cbn [fst snd] in Hcs |- *.
apply andb_prop in Hcs as [Hcs H4]. apply andb_prop in Hcs as [Hcs H3]. apply andb_prop in Hcs as [H1 H2].
apply Z.leb_le in H2. apply Z.ltb_lt in H3. apply Z.leb_le in H4.
split; [exact (tfib_const_lookup B TB ly S H mem (base + off) (N.to_nat n) v HM (const_chk_sound _ _ _ _ H1))|].
split; [lia | exact H4].
Qed.

(* The port of cgif lib/A/AE24.v:36 ffc_ro_img_of_arodata: the read-only image chunks are what the statement's
   arodata_okS says they are. Each chunk avoids every owned static (wfi_ro_chunks_unowned) and the errno word. *)
Lemma wfi_ro_img_of_arodata : forall (H : word -> bool) m,
  YE01.arodata_okS tfibsegs B rlo rhi (aview tfibsegs H m) -> ro_img (mrestrict H m).
Proof.
intros H m HRO E. unfold img_ro_region.
split; [cbn; unfold IMG_RO_LO; lia|]. split; [cbn; unfold IMG_RO_HI; lia|]. split; [intros o Ho; cbn in Ho; lia|].
cbn [YP09.r_chunks YP09.r_base base_val]. apply Forall_forall. intros c Hc i Hi.
pose proof (proj1 (Forall_forall _ _) img_ro_chunks_inside c Hc) as (Hlo & Hhi & n & Hv).
pose proof (proj1 (forallb_forall _ _) wfi_ro_chunks_unowned c Hc) as Hown. cbn beta in Hown.
pose proof (proj1 (forallb_forall _ _) img_ro_bytes_ok c Hc) as Hz. cbn beta in Hz.
destruct c as [co cv]. cbn [YP09.c_off YP09.c_val] in Hv. subst cv. cbn [YP09.c_off YP09.c_val c_len cv_len] in *. rewrite !Z.add_0_l.
pose proof (YP08.zallb_sound _ _ _ (co + i) Hz ltac:(lia)) as Hb.
unfold img_byte_ok, img_byte in Hb.
assert (Hro : (exists s, In s tfibsegs /\ seg_writable s = false /\ Z.of_N (seg_base s) <= co + i < Z.of_N (seg_base s) + Z.of_N (seg_size s)) \/ (rlo <= co + i < rhi)).
{ left. destruct wfi_seg_ro as (s & Hs & Hw & Hb0 & Hb1). exists s. split; [exact Hs|]. split; [exact Hw|].
  unfold IMG_RO_LO, IMG_RO_HI in *. lia. }
assert (Hns : ~ Exists (in_zr (co + i)) (as_owned_static B)).
{ rewrite (ts_owned B TB). intros HX. apply Exists_exists in HX as (r & Hr & [Hin1 Hin2]). rewrite forallb_forall in Hown.
  specialize (Hown r Hr). cbn beta in Hown. apply Bool.orb_prop in Hown. destruct Hown as [Ho|Ho]; apply Z.leb_le in Ho; lia. }
assert (Hne : ~ (as_errno B <= co + i < as_errno B + 4)) by (rewrite (ts_errno B TB); unfold TFIB_ERRNO; unfold IMG_RO_LO, IMG_RO_HI in *; lia).
pose proof (HRO (co + i) Hro Hns Hne) as Hrd. unfold aview in Hrd.
destruct (seg_rom tfibsegs (Z_to_bv 64 (co + i))) as [b|] eqn:Eb; [|discriminate Hb].
exists b. split; [cbn [cbyte]; unfold img_byte; exact Eb|].
destruct (mbyte tfibsegs (mrestrict H m) (co + i)) as [b'|] eqn:Em; [|discriminate Hrd]. cbn in Hrd. injection Hrd as Hrd.
f_equal. apply bv_eq. exact Hrd.
Qed.

Theorem pcapu_afclose_source_spec_icpt :
  afclose_source_spec SK tfibsegs B pcap_KS IC_ENTRY_U WFI_FREE1 WFI_JOIN rlo rhi.
Proof.
unfold afclose_source_spec, afclose_source_spec_stk.
intros W ly S regs mem md ch f b M C p rest HPRE G10 Hperm HSRC Hbuf HMI HRO Hev Hu1 Hu2.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
assert (FS : PFCLOSE_STK = 16528) by reflexivity. rewrite FS in Hslo, Hpres, Hstk0, Hbot.
assert (Hsp : 2 ^ 44 <= spZ regs <= 2 ^ 47) by lia.
(* the FILE block and the data buffer are live blocks *)
assert (Hblk : In (f, SRC_FILE_BLOCK) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
destruct (al_blocks _ _ LAWS ly S W mem md f SRC_FILE_BLOCK HAR Hblk) as (Hf16 & Hf0 & Hfceil & _ & _ & _ & _).
assert (RQ : req_size SRC_FILE_BLOCK = SRC_FILE_BLOCK) by reflexivity. rewrite RQ in Hfceil.
destruct (al_blocks _ _ LAWS ly S W mem md b (Z.of_nat (length C)) HAR Hbuf) as (_ & Hb0 & Hbceil & _ & _ & _ & _).
assert (RQb : Z.of_nat (length C) <= req_size (Z.of_nat (length C))) by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat (length C)) 0); lia).
unfold SRC_FILE_BLOCK in Hfceil.
(* the meta region *)
pose proof HMI as (HX & HMimg & HMptr & HMmem & HM0 & HM47 & HMal & HMZ).
pose proof (HMimg _ wfi_img_top_page) as HMtop.
pose proof (lo_extra ly HLY) as (_ & HEX & _). pose proof (proj1 (Forall_forall _ _) HEX _ HX) as (_ & _ & _ & HMc & _).
cbn [fst snd] in HMc. pose proof (lo_stk_ceil ly HLY) as Hsc.
assert (HAS : AMETA_SIZE = 3727360) by reflexivity.
(* ---- the front: 0x4161c .. the jalr into musl fclose ---- *)
eapply SRr_bind.
{ apply (iclose_front B LAWS TB ly S W regs mem md f M HAR Hal16).
  - unfold IC_STK. lia.
  - exact Hshi.
  - intros a Ha. apply Hpres. unfold IC_STK in Ha. lia.
  - exact G10.
  - lia.
  - lia.
  - exact Hf16.
  - exact (wfi_cells_hold_of_chk ic_cells ly S (w_H W) mem (wfi_ic_cells_chk ly) (proj1 HAR)).
  - exact (wfi_ro_img_of_arodata (w_H W) mem HRO).
  - unfold meta_pre. split; [exact HMmem|]. split; [exact HMZ|].
    split; [match goal with |- ?X <= M => change X with (symaddr ImgPages.AsanUbsan.top) end;
            pose proof (Z.div_mod M 4096 ltac:(lia)) as Hd; rewrite HMal in Hd; lia|].
    split; [exact HMal|]. unfold IC_STK. lia. }
cbv beta. intros W1 c1 _ (-> & regs1 & mem1 & md1 & -> & MF1 & HAR1 & R10 & R1 & R2 & R8 & R19 & RK & RSV & AV1 & PRS1 & PM1).
assert (MB1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - IC_STK <= a < spZ regs) ->
  mbyte tfibsegs (rd W mem1) a = mbyte tfibsegs (rd W mem) a).
{ intros a Ha Hn. apply YE2y.mbyte_of_aview. exact (AV1 a Ha Hn). }
(* ---- the journal of the front: only the 272-byte window below sp0 moved ---- *)
assert (J0 : ajournal (SK:=SK) tfibsegs B PFCLOSE_STK (spZ regs) (asource_fp f) ly S W mem md [] ly S W mem1 md1 0).
{ apply (ajournal_after_write (SK:=SK) tfibsegs B LAWS YCeg.tfib_segs_low PFCLOSE_STK (spZ regs) (asource_fp f)
    ly S W mem md [] ly S W mem md 0 mem1 md1 (fun a => spZ regs - IC_STK <= a < spZ regs) S []
    (ajournal_init (SK:=SK) tfibsegs B PFCLOSE_STK (asource_fp f) ly S W regs mem md ch HPRE)).
  - intros a Ha Hn. exact (AV1 a Ha Hn).
  - exact PM1.
  - exact MF1.
  - intros a Ha. left. unfold awr_byte. left. rewrite FS. unfold IC_STK in Ha. lia.
  - exact HAR1.
  - reflexivity.
  - reflexivity.
  - lia.
  - reflexivity.
  - exact HQT. }
(* ---- musl fclose's precondition at sp0 - 96, budget PFCLOSE_MUSL_STK ---- *)
assert (Esp1 : spZ regs1 = spZ regs + -96).
{ change (spZ regs1) with (bv_unsigned (getr regs1 2)). rewrite R2. unfold YG0d.w64.
  rewrite unsigned_lit_small by (unfold IC_FRAME; lia). unfold IC_FRAME. lia. }
assert (P1 : afn_pre tfibsegs B PFCLOSE_MUSL_STK ly S W regs1 mem1 md1 []).
{ apply (afn_pre_at (SK:=SK) tfibsegs B PFCLOSE_STK (spZ regs) (asource_fp f) ly S W mem md [] ly S W mem1 md1 0
    regs1 PFCLOSE_MUSL_STK (-96) [] J0).
  - exact Esp1.
  - reflexivity.
  - lia.
  - unfold PFCLOSE_MUSL_STK, PFCLOSE_STK. lia.
  - unfold PFCLOSE_MUSL_STK, PFCLOSE_STK. lia.
  - rewrite R1. apply ret_ok_lit; unfold IC_RET; [lia | reflexivity].
  - unfold raZ. rewrite R1. unfold YG0d.w64. rewrite unsigned_lit_small by (unfold IC_RET; lia). unfold IC_RET. lia.
  - etransitivity; [exact (RK 3 ltac:(unfold KEPTC; cbn; lia)) | exact Hgp].
  - etransitivity; [exact (RK 4 ltac:(unfold KEPTC; cbn; lia)) | exact Htp].
  - unfold achain. left. split; [|reflexivity]. left. unfold s0Z. rewrite R8. unfold YG0d.w64.
    rewrite unsigned_lit_small by lia. lia. }
(* the stream, the meta region and the read-only words, carried across the front *)
assert (HSRC1 : asource_at tfibsegs pcap_KS (rd W mem1) f b C p).
{ apply (wfi_asource_at_tr tfibsegs pcap_KS (rd W mem) (rd W mem1) f b C p HSRC).
  - intros a Ha. apply MB1; unfold SRC_FILE_BLOCK, IC_STK in *; lia.
  - intros a Ha. apply MB1; unfold IC_STK; lia.
  - intros a Ha. pose proof (wfi_env_low a Ha). apply MB1; unfold IC_STK; lia. }
assert (HMI1 : asrc_meta_inv tfibsegs pcap_KS ly (rd W mem1) M).
{ split; [exact HX|]. split; [exact HMimg|]. split.
  { apply (YF0x.val_mem_ext (rd W mem)); [|exact HMptr]. intros k Hk. apply MB1;
    cbv [as_meta_ptr pcap_KS PCAP_META_PTR]; unfold IC_STK; lia. }
  split.
  { apply (YF0x.val_mem_ext (rd W mem)); [|exact HMmem]. intros k Hk. apply MB1;
    cbv [as_meta_mem pcap_KS PCAP_META_MEM]; unfold IC_STK; lia. }
  split; [exact HM0|]. split; [exact HM47|]. split; [exact HMal|].
  intros a Ha. rewrite MB1 by (unfold IC_STK; lia). exact (HMZ a Ha). }
assert (HRO1 : YE01.arodata_okS tfibsegs B rlo rhi (aview tfibsegs (w_H W) mem1)).
{ intros a Hra' Hns Hne. pose proof (HRO a Hra' Hns Hne) as Hr0.
  rewrite <- (Z_to_bv64_of_mod a) in Hr0 |- *. rewrite YE2y.aview_mod in Hr0 |- *.
  assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  set (a' := a mod 2 ^ 64) in *.
  destruct (Z_lt_le_dec a' (spZ regs - IC_STK)) as [L|L]; [rewrite AV1 by lia; exact Hr0|].
  destruct (Z_lt_le_dec a' (spZ regs)) as [L2|L2]; [|rewrite AV1 by lia; exact Hr0].
  exfalso. unfold IC_STK in L. pose proof (Hpres a' ltac:(lia)) as Hp.
  apply (YE2y.aview_some_of_apresent _ _ _ Hp). rewrite Hr0.
  rewrite YF0x.seg_rom_none_high; [reflexivity|]. change YF0x.TFIB_IMG_END with (symaddr ImgPages.AsanUbsan.top). lia. }
(* ---- musl fclose, by its contract ---- *)
eapply SRr_bind.
{ apply (pcapu_afclose_source_spec_musl W ly S regs1 mem1 md1 [] f b M C p rest P1 R10 Hperm HSRC1 Hbuf HMI1 HRO1 Hev Hu1 Hu2). }
cbv beta. intros W2 c2 _ (ly' & S' & regs' & mem' & md' & -> & Jm & AP & R10' & Hperm' & Hfr' & Hnone & Hgarr & Hfds & Hfs).
rewrite R1. change (mkCfg (mkst regs' (YG0d.w64 IC_RET) mem' (seg_rom tfibsegs)) md') with (cfg_at tfibsegs IC_RET regs' mem' md').
pose proof Jm as (_ & _ & _ & _ & _ & _ & _ & _ & F1m & _).
assert (E2' : spZ regs' = spZ regs + -96).
{ transitivity (spZ regs1); [unfold spZ; f_equal; exact (AP 2 ltac:(unfold acallee_saved; lia)) | exact Esp1]. }
assert (G19' : getr regs' 19 = YG0d.w64 0) by (etransitivity; [exact (AP 19 ltac:(unfold acallee_saved; lia)) | exact R19]).
(* the five words the front saved at sp0 - 8 .. sp0 - 40 survive musl fclose: they lie above its window *)
assert (SV : forall j rz off, nth_error SAVEDC j = Some (rz, off) ->
  val_mem tfibsegs (rd W2 mem') (spZ regs + off) 8 (bv_unsigned (getr regs (Z_to_bv 5 rz)))).
{ intros j rz off Hj. pose proof (RSV j rz off Hj) as Hv.
  assert (Hoff : -40 <= off <= -8) by (do 5 (destruct j as [|j]; [cbn in Hj; injection Hj as <- <-; lia|]); destruct j; discriminate).
  apply (YF0x.val_mem_ext (rd W mem1)); [|exact Hv]. intros k Hk.
  apply YE2y.mbyte_of_aview. apply F1m; rewrite ?Esp1; unfold PFCLOSE_MUSL_STK, PFCLOSE_STK; lia. }
(* ---- the tail: 0x46888 .. ret ---- *)
eapply SRr_bind.
{ apply (iclose_tail W2 regs' mem' md' (bv_unsigned (getr regs (Z_to_bv 5 1))) (bv_unsigned (getr regs (Z_to_bv 5 8)))
    (bv_unsigned (getr regs (Z_to_bv 5 9))) (bv_unsigned (getr regs (Z_to_bv 5 18))) (bv_unsigned (getr regs (Z_to_bv 5 19)))).
  - exact G19'.
  - rewrite E2'. lia.
  - rewrite E2'. unfold IC_FRAME. lia.
  - rewrite E2'. replace (spZ regs + -96) with (spZ regs + (-6) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16.
  - rewrite E2'. replace (spZ regs + -96 + 88) with (spZ regs + -8) by lia. exact (SV 0%nat 1 (-8) eq_refl).
  - rewrite E2'. replace (spZ regs + -96 + 80) with (spZ regs + -16) by lia. exact (SV 1%nat 8 (-16) eq_refl).
  - rewrite E2'. replace (spZ regs + -96 + 72) with (spZ regs + -24) by lia. exact (SV 2%nat 9 (-24) eq_refl).
  - rewrite E2'. replace (spZ regs + -96 + 64) with (spZ regs + -32) by lia. exact (SV 3%nat 18 (-32) eq_refl).
  - rewrite E2'. replace (spZ regs + -96 + 56) with (spZ regs + -40) by lia. exact (SV 4%nat 19 (-40) eq_refl).
  - apply u64_range.
  - apply u64_range.
  - apply u64_range.
  - apply u64_range.
  - apply u64_range.
  - exact (wfi_ret_ok_even _ Hra). }
cbv beta. intros W3 c3 _ (-> & regs2 & md2 & -> & MF2 & T1 & T2 & T8 & T9 & T18 & T19 & TK).
apply SRr_ret.
(* ---- the post ---- *)
assert (J : ajournal (SK:=SK) tfibsegs B PFCLOSE_STK (spZ regs) (asource_fp f) ly S W mem md ([] ++ []) ly' S' W2 mem' md' (0 + 2)).
{ apply (wfi_ajournal_sub_tok (SK:=SK) tfibsegs B LAWS YCeg.tfib_segs_low PFCLOSE_STK (spZ regs) (asource_fp f)
    ly S W mem md [] ly S W mem1 md1 0 PFCLOSE_MUSL_STK (spZ regs1) (asource_fp f) [] ly' S' W2 mem' md' 2 J0 Jm).
  - rewrite Esp1. unfold PFCLOSE_MUSL_STK, PFCLOSE_STK. lia.
  - rewrite Esp1. lia.
  - intros a Ha. left. exact Ha. }
assert (RKT : forall r, In r KEPTC -> In r KEPTT -> acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r H1 H2 H3. etransitivity; [exact (TK r H2)|]. etransitivity; [exact (AP r H3)|]. exact (RK r H1). }
exists ly', S', regs2, mem', md2.
split.
{ f_equal. f_equal. unfold YG0d.w64. apply Z_to_bv_bv_unsigned. }
split.
{ exact (ajournal_exec (SK:=SK) tfibsegs B LAWS YCeg.tfib_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem' md2 (fun _ => False) J
    (fun _ _ => eq_refl) (mem_grows_refl _) (fun _ _ => eq_refl) MF2 (fun a Ha => False_ind _ Ha)). }
split.
{ intros r Hr. unfold acallee_saved in Hr.
  destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
  - etransitivity; [exact T2|]. rewrite E2'. unfold IC_FRAME, YG0d.w64.
    replace (spZ regs + -96 + 96) with (spZ regs) by lia. unfold spZ. apply Z_to_bv_bv_unsigned.
  - apply RKT; [unfold KEPTC; cbn; lia | unfold KEPTT; cbn; lia | unfold acallee_saved; lia].
  - apply RKT; [unfold KEPTC; cbn; lia | unfold KEPTT; cbn; lia | unfold acallee_saved; lia].
  - etransitivity; [exact T8|]. unfold YG0d.w64. apply Z_to_bv_bv_unsigned.
  - etransitivity; [exact T9|]. unfold YG0d.w64. apply Z_to_bv_bv_unsigned.
  - assert (Hc : r = 18 \/ r = 19 \/ 20 <= r <= 27) by lia.
    destruct Hc as [-> | [-> | Hc]].
    + etransitivity; [exact T18|]. unfold YG0d.w64. apply Z_to_bv_bv_unsigned.
    + etransitivity; [exact T19|]. unfold YG0d.w64. apply Z_to_bv_bv_unsigned.
    + apply RKT; [unfold KEPTC; cbn; lia | unfold KEPTT; cbn; lia | unfold acallee_saved; lia]. }
split.
{ etransitivity; [exact (TK 10 ltac:(unfold KEPTT; cbn; lia))|]. exact R10'. }
split; [exact Hperm'|].
split; [exact Hfr'|].
split; [exact Hnone|].
split; [exact Hgarr|].
rewrite (same_but_materialized_wvb _ _ MF2), (proj1 (wfi_wvb_io _ _ _)), (proj2 (wfi_wvb_io _ _ _)), Hfds, Hfs.
rewrite (same_but_materialized_wvb _ _ MF1), (proj1 (wfi_wvb_io _ _ _)), (proj2 (wfi_wvb_io _ _ _)).
split; reflexivity.
Qed.

End I.

(* The closed statement: the two Section hypotheses are now its arguments, TB and pcapu_afclose_source_spec_musl. *)
Check (@pcapu_afclose_source_spec_icpt :
  forall {fx : YK11.FPState} {rc : YM05.RunCeil} (SK : YI16.sink_head) (B : asyms) (rlo rhi : Z),
  PcapSyms B ->
  afclose_source_spec_stk SK tfibsegs B pcap_KS PFCLOSE_MUSL_STK PFCLOSE_MUSL_U WFI_FREE1 WFI_JOIN rlo rhi ->
  afclose_source_spec SK tfibsegs B pcap_KS IC_ENTRY_U WFI_FREE1 WFI_JOIN rlo rhi).

(* The closure of every theorem in this file: no axiom outside toolchain/allowed-axioms.txt. *)
Print Assumptions wfi_ajournal_sub_tok.
Print Assumptions wfi_real_fclose_is_IC_REAL.
Print Assumptions wfi_ic_entry_u.
Print Assumptions wfi_musl_entry_u.
Print Assumptions wfi_ret_ok_even.
Print Assumptions wfi_in_img_of_b.
Print Assumptions wfi_img_top_page.
Print Assumptions wfi_seg_ro.
Print Assumptions wfi_ro_chunks_unowned.
Print Assumptions wfi_ic_cells_chk.
Print Assumptions wfi_wvb_io.
Print Assumptions wfi_env_low.
Print Assumptions wfi_vm_fr.
Print Assumptions wfi_head_env_addr.
Print Assumptions wfi_env_tr.
Print Assumptions wfi_asource_at_tr.
Print Assumptions wfi_cells_hold_of_chk.
Print Assumptions wfi_ro_img_of_arodata.
Print Assumptions pcapu_afclose_source_spec_icpt.
