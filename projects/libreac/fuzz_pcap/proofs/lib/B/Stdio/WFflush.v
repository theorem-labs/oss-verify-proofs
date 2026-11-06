From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the walk of fflush on libreac/fuzz_pcap's v1.9.0 ASAN-UBSAN image, for the fmemopen
   READ stream, at BOTH entries lib/A/Stdio/PFflush.v's pfflush_entry_ok admits:
     PFFLUSH_MUSL_U 0x8e308   musl fflush itself
     PFFLUSH_ICPT_U 0x41618   the ASan interceptor trampoline fclose and fflush go through
   The statement is PFflush.v's afflush_source_spec, UNCHANGED and not copied: this file Requires it. It is
   image-generic (the entry pc is a parameter), so the same text serves the asan and the asan-ubsan images.

   PORTED FROM a Theorem Labs lane's OWN PROVED ASAN WALK, lib/A/Stdio/WFflush.v at a working branch 2f839b241ee
   (afflush_source_spec_musl / _icpt / _pcap), for the structure, the case split and the tactics; and from the
   RELEASED PLAIN proof proofs/libreac/fuzz_pcap/lib/Prog/fflush_c.v for facts and pcs only. NEITHER IS
   IMPORTED: the first states over the asan image, the second over the plain model.
   rule 24 (lookup) was run UNPIPED and CONFIRMED by a fresh read-only checker before this file was written:
   at ossv/recipes 25e3d17bdb50 (2026-10-29), no released proof stated fflush on ANY pcap ASan image; pcap's released hits were the PLAIN (lib/Prog,
   images.Plain) and UBSAN (lib/U/Prog, images.Ubsan) images only. Output
   fflush.out (sha256 a8a821383af7; internal record), EXIT=0.

   EVERY NUMBER BELOW IS MEASURED ON THIS IMAGE, never derived from an asan address by a delta (the asan ->
   asan-ubsan delta is not uniform: .bss mostly +0x100, 67 .data rows +0x138, text +0x50).

   THE CODE. musl fflush at 0x8e308, 92 instructions, read out of
   fuzz_pcap.objdump.txt (sha256 af7c8be930de; internal record) (pin 9e66f771f22a; the unstripped twin has
   sha256 c969d83cdd59). Compared word for word with the asan
   walk's 92 at 0x8e43c: the single-FILE path is IDENTICAL instruction for instruction, and the only seven
   differing words are all on the all-streams path (a0 = 0), which this spec does not take -- the three
   self-calls `jal __interceptor_trampoline_fflush` (0x8e34c / 0x8e3f8 / 0x8e460 here, 0x415c8 -> 0x41618) and
   the four `ld` of __stdout_used / __stderr_used (0x9dfe0 -> 0x9dea8, 0x9def0 -> 0x9ddb8).
     0x8e308-0x8e318  frame of 32 bytes; ra, s0, s1, s2 saved at 24/16/8/0(sp)
     0x8e31c          beqz a0 -> 0x8e33c (the all-streams path): NOT TAKEN, asource_at gives f <> 0
     0x8e324-0x8e328  lock = lw 140(f) = -1 (source_static's U32M1), bltz TAKEN: no __lockfile, s2 = 1
     0x8e35c-0x8e364  wpos (+40) = wbase (+56) = 0 (source_static): the write flush is skipped
     0x8e384-0x8e38c  rpos (+8), rend (+16); equal -> skip the seek (CASE EMPTY), else (CASE FULL)
     0x8e390-0x8e3a0  jalr ra, 0(a3) with a3 = f->seek = as_seek K: mseek(f, rpos - rend, SEEK_CUR)
     0x8e3a4-0x8e3b8  s0 = 0; wbase = rpos = rend = wend = wpos = 0
     0x8e3bc          bnez s2 -> 0x8e410 (TAKEN, s2 = 1); a0 = 0; restore; ret at 0x8e428
   So PFFLUSH_JALR_U = 0x8e3a0 (word 0x000680e7, read off the image) and PFFLUSH_RET_MSEEK_U = 0x8e3a4.

   THE _U CONSTANTS AND THEIR SOURCE. PFFLUSH_MUSL_U 0x8e308, PFFLUSH_ICPT_U 0x41618 and PMSEEK_U 0x8eaf4 are
   a Theorem Labs lane's lib/B/Stdio/PStdioImgB.v at a working branch b4439851fa3 (the image pcs left the statement
   files at a working branch c625af6eaa9; their values there were the same), taken BY NAME, never
   redeclared here; PMSEEK_STK 48 and PFFLUSH_OWN_STK 1840 stay in lib/A/Stdio/PFmopsM.v / PFflush.v. The
   asan-ubsan symbol record KS_U is a Theorem Labs lane's lib/B/Stdio/PSourceK.v (a working branch d6edf2117df, an
   ancestor of a working branch b4439851fa3, which changes only a comment of it; auditor a Theorem Labs lane PASSED it 18/18);
   this file takes `pcap_KS` from THAT file, never from lib/A/Stdio/PSourceK.v.
   PFFLUSH_OWN_STK 1840 needs no twin: a Theorem Labs lane measured it identical in both images, and every step of
   this walk re-measured against it agrees (fflush's own frame 32, mseek 48, the interceptor front 80 and its
   tail 176 + 56, all from this image's own objdump).

   WHAT I RE-MEASURED ON THIS IMAGE FOR THE INTERCEPTOR ENTRY, with the asan value for comparison:
     REAL(fflush) GOT cell   0x9b4b8 -> 0x8e308     (asan 0x9b5f0 -> 0x8e43c)   DIFFERENT
     REAL(fclose) GOT cell   0x9b4c0 -> 0x8e0e0     (asan 0x9b5f8 -> 0x8e214)   DIFFERENT
     interceptor_metadata_map 0xa1000, metadata_mem 0xa1008  (asan 0xa1100 / 0xa1108)  DIFFERENT
     ___interceptor_fflush   0x466e4, its return site IF_RET 0x46710            (asan 0x46694 / 0x466c0)
     AddrHashMap::acquire    0x47b7c, release 0x4839c                           (asan 0x47b2c / 0x4834c)
     the .rodata word the tail reads at 0x4671c (`ld a1,-840(a0)`)      0x103d0  -- THE SAME ADDRESS as asan
     the MULTIPLIER acquire reads at 0x47c04 (`ld a2,-2036(a2)`)        0x103d8  -- THE SAME ADDRESS as asan
     the owned-static word acquire reads at 0x47be8 (`ld t0,2020(a1)`)  0x103a0  -- THE SAME ADDRESS as asan
   The three .rodata words are at the SAME addresses on both images (their pc-relative encodings differ; the
   objdump resolves both to 0x103d0 / 0x103d8 / 0x103a0) and hold the same values (0xaaaaaaaaaaaaaaaa,
   0x8713f185cccd38dd, 0xafffff00000fffff), read out of the two ELFs' PT_LOADs with a Python ELF reader. That
   is a measurement, not an assumption carried over: the meta cells and the GOT cells next to them DID move.
   0x103d0 and 0x103d8 lie in YE3i.img_ro_chunks' unowned chunk 0x103b8..0x10420, so arodata_okS reaches them;
   0x103a0 is an OWNED-STATIC row (YF0m.Tfib_owned_static) and arodata_okS excludes owned bytes, so the walk
   takes it from AR's const cells instead (YF0m.Tfib_const_abs, tied to as_const by YF0m.ts_const) --
   in_const_103a0 below.

   THE TWO CASES, as on asan.
     CASE EMPTY (rpos = rend; cpos = p): one symbolic run from the entry to the ret.
     CASE FULL (rpos <> rend): a run to the jalr, the jalr by hand, mseek's contract at as_seek K (a NAMED
       Section hypothesis: a Theorem Labs lane proves amseek_rewind_spec at PMSEEK_U in parallel, so this lane waits
       on nothing), then a run from 0x8e3a4 to the ret. The journals compose with ajournal_sub_tok.
   Both runs are generic in the stack budget STK; PFFLUSH_OWN_STK = 1840 instantiates it (wffu_spec_is: the
   generic statement IS the spec at 1840, by reflexivity). The musl entry needs STK >= 80 = 32 + PMSEEK_STK.

   THE INTERCEPTOR ENTRY uses the au twins of the asan donor's AE2f fronts: YE2f.iflush_front (0x41618 ->
   0x466e4, TryAsanInitFromRtl, up to the jalr REAL(fflush) with ra = 0x46710) and YE2f.iflush_tail (0x46710 ->
   acquire 0x47b7c / release 0x4839c -> ret), both on a working branch. Between them the musl entry
   runs with budget 1840 - 80 = 1760 (afn_pre_at), and the journals compose with ajournal_sub_tok.
   The AddrHashMap CheckFailed edges are NOT stepped: meta_pre's zero bucket decides the branches and
   iflush_tail's run reaches the ret. R2 (does any route step past a report entry): NO -- this walk contains no
   __asan_report_* call site; the only fatal edges in reach are inside iflush_tail, which refutes them.

   ajournal_sub_tok IS COPIED INTO THIS FILE (Section J), verbatim from lib/A/Prog/YC85.v at
   a working branch 02075de74ec, statement and proof unchanged, under the name wffu_aj_sub_tok. WHY: the
   lib/B closure rule. YC85 Requires lib/A/Prog/PcapSyms and PcapPa, whose closure reaches lib/A/Prog/PcapList
   -- an asan-address listing that the auditor's three-limb checker flags (limb b, twin literals), and whose
   au twin lives on a working branch, a branch this union does not need for anything else. The lemma
   itself names no image and no address. Nothing else of YC85 is used.

   THE UNION this file builds in (a LOCAL merge commit of pushed shas, never pushed), every member listed:
     a working branch     this branch (base a working branch 02075de74ec, merged c625af6eaa9)
     a working branch   83eefd767e6   (the au core: YB1v YE2f YE2h YE2y YE3i YF0m YF0x and their
                                                closure; it merges a working branch 6927e0d899c, so the generated
                                                set YF0m / YB1v / YB1k / YD2j is a Theorem Labs lane's text byte for byte
                                                and 6927e0d899c is an ANCESTOR, not a separate member)
     a working branch      595c3188fe3   (the lib/A core this branch's statement closure needs)
     a working branch      b4439851fa3   (lib/B/Stdio/PSourceK.v = KS_U, lib/B/Stdio/PStdioImgB.v)
   No -wip branch is merged into this branch.

   THE lib/B CLOSURE. The Require closure of this file reaches exactly four lib/A files, all of them the
   image-generic statement files it is proving: PSource, PSourceMeta, PFmopsM, PFflush. No lib/A image-bearing
   file is in it: not PSourceK, not PStdioImgA, not AF0m / AB1v / AE2f / AE34, no asan image module and no
   asan-only constant. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
(* For Section I (the interceptor entry); imported FIRST so the walk's own imports below keep priority. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YP08 YG0p YG0v YE00.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.libreac.fuzz_pcap.images Require AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI04 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YE01 YG0q.
(* The asan-ubsan core: the au twins of the asan walk's AB1v / AE2f / AE2h / AE2y / AE3i / AF0m / AF0x. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YB1v YE2f YE2h YE2y YE3i YF0m YF0x.
(* The statements, the asan-ubsan image pcs, and the asan-ubsan symbol record (lib/B, NOT lib/A/Stdio/PSourceK.v). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PFmopsM PFflush.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Stdio Require Import PStdioImgB.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Stdio Require Import PSourceK.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
(* lib/Reusable/YE2f.v (Required for Section I) turns lia's division/modulo equations OFF globally; this file's
   arithmetic needs them, so the Stdlib default is restored here. The redefinition is LOCAL to this file:
   it does not escape the Require, so a file that Requires this one keeps its own setting. *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* 0. ajournal_sub_tok, COPIED VERBATIM from lib/A/Prog/YC85.v (a working branch 02075de74ec),   *)
(*    statement and proof unchanged, renamed wffu_aj_sub_tok.                                        *)
(*                                                                                                   *)
(* The porter's rule is that a token-carrying footprint (asource_fp, which holds YI16.sink_token) is  *)
(* composed with ajournal_sub_tok, never with the library's ajournal_sub. The lemma lives in          *)
(* lib/A/Prog/YC85.v, which this file CANNOT Require: YC85 Requires lib/A/Prog/PcapSyms and PcapPa,   *)
(* and that closure reaches lib/A/Prog/PcapList, an asan-address listing the auditor's three-limb     *)
(* checker flags (limb b), which would put an asan image file in an asan-ubsan instantiation's        *)
(* closure. The au twin lib/B/Prog/YC85.v exists on a working branch, but pulling that whole    *)
(* branch in for one lemma is a second image's program layer in this union. The lemma names no image, *)
(* no address and no listing: it is pure journal algebra over segs and B. So it is copied, with its   *)
(* home named here, and nothing else of YC85 is taken.                                               *)
(* ---------------------------------------------------------------------------------------------- *)
Section J. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Lemma wffu_aj_sub_tok : forall STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k STK1 sp1 FP1 nf ly2 S2 W2 mem2 md2 k1,
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
End e.
End J.

(* ---------------------------------------------------------------------------------------------- *)
(* 1. The code: musl fflush's 92 words, read out of the ASAN-UBSAN image at 0x8e308.                 *)
(* ---------------------------------------------------------------------------------------------- *)
Definition ausegs : list Segment := AsanUbsan.M.loaded_segments.
Definition WFFU_LEN : nat := 92.
Definition wffu_tbl : ctable := Eval vm_compute in build_table ausegs PFFLUSH_MUSL_U WFFU_LEN TEmpty.
Lemma wffu_tbl_eq : wffu_tbl = build_table ausegs PFFLUSH_MUSL_U WFFU_LEN TEmpty.
Proof. vm_cast_no_check (eq_refl wffu_tbl). Qed.
Lemma wffu_tbl_ok : table_ok ausegs wffu_tbl.
Proof. rewrite wffu_tbl_eq. apply build_table_ok0. unfold PFFLUSH_MUSL_U. lia. Qed.
Lemma wffu_ausegs_wx : wx_segs_nowrap ausegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
(* The same shape as a Theorem Labs lane's pcapu_segs_low over this image (WMclose.v (sha256 4729121bf767; internal record),
   a working branch 9c2da15fd15), which carries the asan-ubsan twin of the asan lemma. *)
Lemma wffu_ausegs_low : forall a, in_img ausegs a -> 0 <= a < kLowMemEnd.
Proof.
  intros a (sg & Hin & Hlo & Hhi).
  assert (Hb : forallb (fun s => (0 <=? Z.of_N (seg_base s)) && (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? kLowMemEnd))
                 ausegs = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hb. specialize (Hb sg Hin).
  apply andb_prop in Hb as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2. lia.
Qed.

(* The return address of the mseek call: the instruction after `jalr a3` at 0x8e3a0. *)
Definition PFFLUSH_RET_MSEEK_U : Z := (symaddr (Symbols.AsanUbsan.s_fflush_unlocked + 0x9c)%Z).

(* ---------------------------------------------------------------------------------------------- *)
(* 2. The symbolic states.                                                                          *)
(*   atom 2 = sp, atom 9 / 10 = f, atom 32 / 33 = rpos / rend (entry), atoms 32..35 = the caller's     *)
(*   ra, s0, s1, s2 as saved in fflush's frame (tail).                                               *)
(* ---------------------------------------------------------------------------------------------- *)
Definition ck (o : Z) (n : N) (v : sv) : YP09.chunk := YP09.mkChunk o (CVal n v).
Definition stkR : YP09.region := YP09.mkRegion (Some 2%nat) (-32) 0 (-32) 0 [].
(* CASE EMPTY: rpos = rend = atom 32. The FILE is three regions: [8,24) and [32,64) are writable (the five
   window stores) and every 8-byte cell in them carries a chunk, so the final state pins them; [64,152) is
   read-only (the lock word). +24 (the close pointer) and the cookie sit in no write range. *)
Definition fileA1 : YP09.region := YP09.mkRegion (Some 10%nat) 0 24 8 24 [ck 8 8 (SOff 32 0); ck 16 8 (SOff 32 0)].
Definition fileA2 : YP09.region := YP09.mkRegion (Some 10%nat) 32 64 32 64
  [ck 32 8 (SLit 0); ck 40 8 (SLit 0); ck 48 8 (SLit 0); ck 56 8 (SLit 0)].
Definition fileA3 : YP09.region := YP09.mkRegion (Some 10%nat) 64 152 64 64 [ck 140 4 (SLit U32M1)].
Definition factsA : list (nat * afact) :=
  [(2%nat, mkAF (2^44) (2^47) 4); (10%nat, mkAF 4096 (2^47) 4); (32%nat, mkAF 0 (2^64 - 1) 0)].
Definition ssA : sstate := mkSS PFFLUSH_MUSL_U sr_atoms [stkR; fileA1; fileA2; fileA3] None (mkFacts factsA [] []).
(* CASE FULL, up to the jalr: the FILE is only READ (no writable part), rpos = atom 32, rend = atom 33, and
   the two differ; f->seek = atom 34. *)
Definition fileB : YP09.region := YP09.mkRegion (Some 10%nat) 0 152 8 8
  [ck 8 8 (SOff 32 0); ck 16 8 (SOff 33 0); ck 40 8 (SLit 0); ck 56 8 (SLit 0); ck 80 8 (SOff 34 0);
   ck 140 4 (SLit U32M1)].
Definition factsB : list (nat * afact) :=
  [(2%nat, mkAF (2^44) (2^47) 4); (10%nat, mkAF 4096 (2^47) 4); (32%nat, mkAF 0 (2^64 - 1) 0);
   (33%nat, mkAF 0 (2^64 - 1) 0); (34%nat, mkAF 0 (2^64 - 1) 0)].
Definition ssB : sstate :=
  add_cond (mkSS PFFLUSH_MUSL_U sr_atoms [stkR; fileB] None (mkFacts factsB [] [])) (mkAC BC_NE (SOff 32 0) (SOff 33 0)).
(* The call instruction, read off the image: 0x8e3a0 `jalr a3` = 0x000680e7. *)
Definition PFFLUSH_JALR_U : Z := (symaddr (Symbols.AsanUbsan.s_fflush_unlocked + 0x98)%Z).
Definition PFFLUSH_JALR_U_W : Z := 0x000680e7.
(* CASE FULL, from mseek's return: sp = atom 2 is fflush's sp (the caller's sp - 32), s1 = atom 9 = f,
   s2 = 1 (pinned), the four saved words read-only; the window cells writable in two regions. *)
Definition stkT : YP09.region := YP09.mkRegion (Some 2%nat) 0 32 0 0
  [ck 0 8 (SOff 35 0); ck 8 8 (SOff 34 0); ck 16 8 (SOff 33 0); ck 24 8 (SOff 32 0)].
Definition fileT1 : YP09.region := YP09.mkRegion (Some 9%nat) 0 24 8 24 [].
Definition fileT2 : YP09.region := YP09.mkRegion (Some 9%nat) 32 64 32 64 [ck 48 8 (SLit 0)].
Definition factsT : list (nat * afact) :=
  [(2%nat, mkAF (2^44) (2^47) 4); (9%nat, mkAF 4096 (2^47) 4); (32%nat, mkAF 0 (2^64 - 1) 0);
   (33%nat, mkAF 0 (2^64 - 1) 0); (34%nat, mkAF 0 (2^64 - 1) 0); (35%nat, mkAF 0 (2^64 - 1) 0)].
Definition ssT : sstate :=
  mkSS PFFLUSH_RET_MSEEK_U (sr_set sr_atoms 18%bv (SLit 1)) [stkT; fileT1; fileT2] None (mkFacts factsT [] []).

(* Reading a chunk back out of a computed state. *)
Definition chunk_at (ss : sstate) (i : nat) (off : Z) (n : N) (v : sv) : bool :=
  match nth_error (ss_mem ss) i with
  | Some r => existsb (fun c => (YP09.c_off c =? off) &&
                match YP09.c_val c with CVal n' e => N.eqb n' n && sv_eqb e v | _ => false end) (YP09.r_chunks r)
  | None => false
  end.
Definition rbase_at (ss : sstate) (i : nat) : option nat :=
  match nth_error (ss_mem ss) i with Some r => YP09.r_base r | None => None end.

Lemma wvb_io : forall l X (m : Model), m_fds (with_vm_backing l X m) = m_fds m /\ m_fs (with_vm_backing l X m) = m_fs m.
Proof. intros l X m. destruct m. split; reflexivity. Qed.

Section W.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} (SK : YI16.sink_head).
Variable segs : list Segment.
Variable B : asyms.
Variable K : asource_syms.
(* The allocator laws hold of ANY segs and B (YG0q.v:804, no Section hypothesis). *)
Let LAWS : AR_laws segs B := YG0q.AR_laws_ok segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis TBL : table_ok segs wffu_tbl.
Hypothesis ASIL : asource_img_laws SK segs B K.
Local Notation rd W mem := (mrestrict (w_H W) mem).

(* ---------------------------------------------------------------------------------------------- *)
(* 3. The statement, generic in the stack budget. At PFFLUSH_OWN_STK it IS afflush_source_spec.     *)
(* ---------------------------------------------------------------------------------------------- *)
Definition wffu_post (STK : Z) (W : world segs) (ly : alayout) (S : astate) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (f b : Z) (C : list Z) (p : Z) : world segs -> config -> Prop :=
  fun W' c' => exists (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
     c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
     ajournal segs B STK (spZ regs) (asource_fp f) ly S W mem md [] ly S W' mem' md' 0 /\
     aregs_preserved regs regs' /\
     getr regs' 10 = Z_to_bv 64 0 /\
     asource_unbuffered segs K (rd W' mem') f b C p /\
     val_mem segs (rd W' mem') (f + SRC_COOKIE_OFF) 8 p /\
     m_fds md' = m_fds md /\ m_fs md' = m_fs md.

Definition wffu_spec (STK pc rlo rhi : Z) : Prop :=
  forall (W : world segs) (ly : alayout) (S : astate) (regs : bvmap 5 word)
         (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z))
         (f b M : Z) (C : list Z) (p : Z),
    afn_pre segs B STK ly S W regs mem md ch ->
    getr regs 10 = Z_to_bv 64 f ->
    YE01.arodata_okS segs B rlo rhi (aview segs (w_H W) mem) ->
    asrc_meta_inv segs K ly (rd W mem) M ->
    asource_at segs K (rd W mem) f b C p ->
    In (f, SRC_FILE_BLOCK) (ablocks B ly S) ->
    (b + Z.of_nat (length C) <= spZ regs - STK \/ spZ regs <= b) ->
    SRr segs W (cfg_at segs pc regs mem md) (wffu_post STK W ly S regs mem md f b C p).

Lemma wffu_spec_is : forall pc rlo rhi, wffu_spec PFFLUSH_OWN_STK pc rlo rhi = afflush_source_spec SK segs B K pc rlo rhi.
Proof. intros pc rlo rhi. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* 4. Helpers: frames, registers, chunks.                                                           *)
(* ---------------------------------------------------------------------------------------------- *)
Lemma vm_fr : forall (m m' : word -> option byte) a (n : nat) v,
  (forall x, a <= x < a + Z.of_nat n -> mbyte segs m' x = mbyte segs m x) ->
  val_mem segs m a n v -> val_mem segs m' a n v.
Proof. intros m m' a n v Hfr Hv k Hk. rewrite Hfr by lia. exact (Hv k Hk). Qed.

Lemma mb_frame : forall E rs (m m' : word -> option byte) a,
  frame_of E rs m m' -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a -> mbyte segs m' a = mbyte segs m a.
Proof.
intros E rs m m' a HF Ha Hn. unfold mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by exact Ha. exact Hn.
Qed.

Lemma nwr2 : forall E (r1 r2 : YP09.region) a,
  ~ (base_val E (YP09.r_base r1) + YP09.r_wlo r1 <= a < base_val E (YP09.r_base r1) + YP09.r_whi r1) ->
  ~ (base_val E (YP09.r_base r2) + YP09.r_wlo r2 <= a < base_val E (YP09.r_base r2) + YP09.r_whi r2) ->
  ~ in_wrange E [r1; r2] a.
Proof. intros E r1 r2 a H1 H2 (r & Hin & Hr). destruct Hin as [<- | [<- | []]]; contradiction. Qed.

Lemma Z_to_bv64_mod_eq : forall x y, x mod 2 ^ 64 = y mod 2 ^ 64 -> Z_to_bv 64 x = Z_to_bv 64 y.
Proof.
intros x y H. rewrite <- (Z_to_bv64_canon x), <- (Z_to_bv64_canon y). unfold zcanon, M64. rewrite H. reflexivity.
Qed.

Lemma nwr_all : forall E rs a,
  Forall (fun r : YP09.region => ~ (base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r)) rs ->
  ~ in_wrange E rs a.
Proof. intros E rs a HF (r & Hin & Hr). exact (proj1 (Forall_forall _ _) HF r Hin Hr). Qed.

Lemma val_mem_mod64 : forall m a v, val_mem segs m a 8 v -> val_mem segs m a 8 (v mod 2 ^ 64).
Proof.
intros m a v H k Hk. rewrite (H k Hk). unfold YO0f.le_byte.
replace (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) by reflexivity. rewrite (Z.mod_mod v (2 ^ 64)) by lia. reflexivity.
Qed.

Lemma v_jalr_even : forall x, x mod 2 = 0 -> v_jalr (Z_to_bv 64 x) 0 = Z_to_bv 64 x.
Proof.
intros x Hx. unfold v_jalr, jalr_tgtZ. rewrite Z.add_0_r, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64).
assert (He : (x mod 2 ^ 64) mod 2 = 0).
{ pose proof (Z.mod_pos_bound x (2 ^ 64) ltac:(lia)). rewrite (Z.mod_eq x (2 ^ 64)) by lia.
  replace (x - 2 ^ 64 * (x / 2 ^ 64)) with (x + (- (2 ^ 63 * (x / 2 ^ 64))) * 2) by lia.
  rewrite Z_mod_plus_full. exact Hx. }
rewrite (land_m2_even _ He). apply Z_to_bv64_mod_eq. apply Z.mod_mod. lia.
Qed.

Lemma reg_of : forall E ss (H : word -> bool) ms (r : bv 5) v,
  st_ok segs E ss (restrict H ms) -> sr_get (ss_regs ss) r = v -> getr (ms_regs ms) r = sv_denot E v.
Proof. intros E ss H ms r v HS Hv. rewrite <- Hv. exact (st_ok_reg segs E ss (restrict H ms) r HS). Qed.

Lemma reg_kept : forall E ss (H : word -> bool) ms regs0 extra (r : Z),
  st_ok segs E ss (restrict H ms) -> E = Ereg regs0 extra -> 0 <= r < 32 ->
  sr_get (ss_regs ss) (Z_to_bv 5 r) = SOff (Z.to_nat r) 0 ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r).
Proof.
intros E ss H ms regs0 extra r HS HE Hr Hv. rewrite (reg_of E ss H ms _ _ HS Hv). subst E.
cbn [sv_denot]. rewrite Z.add_0_r, ew_Ereg_lt by lia. rewrite Z2Nat.id by lia. apply Z_to_bv_bv_unsigned.
Qed.

Lemma val_of_chunk_at : forall E ss (H : word -> bool) ms i off n v z bn,
  st_ok segs E ss (restrict H ms) -> chunk_at ss i off n v = true -> rbase_at ss i = Some bn ->
  sv_denot E v = Z_to_bv 64 z -> 0 <= z < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
  val_mem segs (mrestrict H (ms_mem ms)) (bv_unsigned (ew E bn) + off) (N.to_nat n) z.
Proof.
intros E ss H ms i off n v z bn HS Hc Hb Hv Hz Hn.
unfold chunk_at, rbase_at in *. destruct (nth_error (ss_mem ss) i) as [r|] eqn:Hi; [|discriminate].
apply existsb_exists in Hc as ([o cv] & Hin & Hck). cbn [YP09.c_off YP09.c_val] in Hck.
apply andb_prop in Hck as [Ho Hcv]. apply Z.eqb_eq in Ho. subst o.
destruct cv as [n' e|l0|l0|d0 s0 l0]; try discriminate. apply andb_prop in Hcv as [Hn' He].
apply N.eqb_eq in Hn'. apply sv_eqb_eq in He. subst n' e.
pose proof (st_ok_mem_ok segs E ss _ HS) as (_ & Hrs & _).
pose proof (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck.
rewrite Hb in Hck. cbn [base_val] in Hck.
exact (val_of_chunk_ok segs E _ _ off n v z Hck Hv Hz Hn).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* 5. The stream predicate across a walk.                                                           *)
(* ---------------------------------------------------------------------------------------------- *)
Lemma env_addr_img : forall a, asrc_env_addr K a -> in_img segs a /\ 0 <= a < 0x7fff8000.
Proof.
intros a Ha. destruct (asil_env _ _ _ _ ASIL a Ha) as (Hi & _). split; [exact Hi|].
pose proof (segs_low a Hi) as Hl. unfold kLowMemEnd in Hl. lia.
Qed.

Lemma head_env_addr : forall a, as_ofl_head K <= a < as_ofl_head K + 8 -> asrc_env_addr K a.
Proof. intros a Ha. unfold asrc_env_addr, as_ofl_head in *. lia. Qed.

Lemma env_tr : forall m m', asrc_stdio_env segs K m ->
  (forall a, asrc_env_addr K a -> mbyte segs m' a = mbyte segs m a) -> asrc_stdio_env segs K m'.
Proof.
intros m m' (E1 & E2 & E3 & E4 & E5 & (cv & Hcv & E6)) Hk. unfold asrc_env_addr in Hk.
split; [eapply vm_fr; [|exact E1]; intros x Hx; simpl Z.of_nat in Hx; apply Hk; lia|].
split; [eapply vm_fr; [|exact E2]; intros x Hx; simpl Z.of_nat in Hx; apply Hk; lia|].
split; [eapply vm_fr; [|exact E3]; intros x Hx; simpl Z.of_nat in Hx; apply Hk; lia|].
split; [eapply garr8_frame; [exact E4|]; intros x Hx; unfold src_mode_Z in Hx; simpl in Hx; apply Hk; lia|].
split; [eapply garr8_frame; [exact E5|]; intros x Hx; unfold src_modeset_Z in Hx; simpl in Hx; apply Hk; lia|].
exists cv. split; [exact Hcv|]. eapply vm_fr; [|exact E6]. intros x Hx. simpl Z.of_nat in Hx. apply Hk. lia.
Qed.

(* Transfer a FILE / buffer cell through a byte frame. *)
Ltac vfr HF H :=
  eapply vm_fr; [|exact H];
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; simpl Z.of_nat in Hx;
  unfold SRC_COOKIE_OFF, SRC_BUF_OFF, SRC_BUFSIZ, SRC_FILE_BLOCK in *; apply HF; lia.
Ltac vfr_auto HF :=
  lazymatch goal with |- val_mem _ _ ?a ?n ?v =>
    match goal with H : val_mem _ _ a n v |- _ => vfr HF H end end.

(* asource_at survives any change that keeps the FILE block, the buffer and the environment. *)
Lemma asource_at_tr : forall m m' f b C p, asource_at segs K m f b C p ->
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
split; [exact (env_tr m m' HENV He)|].
split; [eapply vm_fr; [|exact HHD]; intros x Hx; apply He, head_env_addr; simpl Z.of_nat in Hx; lia|].
exact Hfnz.
Qed.

(* The post's stream: the window cells read 0, the cookie reads p, and everything else asource_at reads is
   either unchanged (the FILE outside the window cells and the cookie) or re-established (buffer, env, head). *)
Lemma asource_unbuf_of : forall m m' f b C p,
  asource_at segs K m f b C p ->
  (forall a, f <= a < f + SRC_FILE_BLOCK -> ~ (f + 8 <= a < f + 24) -> ~ (f + 32 <= a < f + 64) ->
     ~ (f + SRC_COOKIE_OFF <= a < f + SRC_COOKIE_OFF + 8) -> mbyte segs m' a = mbyte segs m a) ->
  garr8 segs m' b C -> asrc_stdio_env segs K m' -> val_mem segs m' (as_ofl_head K) 8 f ->
  val_mem segs m' (f + 8) 8 0 -> val_mem segs m' (f + 16) 8 0 ->
  val_mem segs m' (f + 32) 8 0 -> val_mem segs m' (f + 40) 8 0 -> val_mem segs m' (f + 48) 8 0 ->
  val_mem segs m' (f + 56) 8 0 -> val_mem segs m' (f + SRC_COOKIE_OFF) 8 p ->
  asource_unbuffered segs K m' f b C p.
Proof.
intros m m' f b C p (Wn & cpos & fl & mdv & HX) HF HC' HENV' HHD' V8 V16 V32 V40 V48 V56 VCK.
cbv zeta in HX.
destruct HX as (Hp0 & Hpc & Hcn & Hn63 & Hbw & Hcp & HWd & Hbok & HC & HST & HWIN & HFL & HFL24 & HMD & HCK &
  HENV & HHD & Hfnz).
destruct HST as (S24 & S64 & S72 & S80 & S88 & S96 & Sc8 & Sc16 & Sc24 & Sc32 & S152 & S32 & S40 & S48 & S56 &
  S104 & S112 & S168 & S120 & S140 & S144 & Sf0 & Sf16 & Sb0 & Sdisj).
destruct HFL as [HFL HFLv]. destruct HMD as [HMD HMDv].
assert (HW0 : source_window segs m' f []) by (left; split; [reflexivity | split; [exact V8 | exact V16]]).
split; [|exact HW0].
exists [], p, fl, mdv. cbv zeta. cbn [length Z.of_nat].
split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hn63|]. split; [exact Hbw|]. split; [lia|].
split; [rewrite Z.sub_diag; reflexivity|]. split; [exact Hbok|]. split; [exact HC'|].
split.
{ do 11 (split; [vfr_auto HF|]).
  split; [exact V32|]. split; [exact V40|]. split; [exact V48|]. split; [exact V56|].
  do 6 (split; [vfr_auto HF|]). repeat split; assumption. }
split; [exact HW0|].
split; [split; [vfr HF HFL | exact HFLv]|].
split; [exact HFL24|].
split; [split; [vfr HF HMD | exact HMDv]|].
split; [exact VCK|]. split; [exact HENV'|]. split; [exact HHD'|]. exact Hfnz.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* 6. CASE EMPTY: rpos = rend. One run, entry to ret.                                                *)
(* ---------------------------------------------------------------------------------------------- *)
Lemma wffu_empty : forall STK (W : world segs) ly S regs mem md ch f b C p r1,
  32 <= STK -> afn_pre segs B STK ly S W regs mem md ch -> getr regs 10 = Z_to_bv 64 f ->
  asource_at segs K (rd W mem) f b C p -> In (f, SRC_FILE_BLOCK) (ablocks B ly S) ->
  (b + Z.of_nat (length C) <= spZ regs - STK \/ spZ regs <= b) ->
  val_mem segs (rd W mem) (f + 8) 8 r1 -> val_mem segs (rd W mem) (f + 16) 8 r1 -> 0 <= r1 < 2 ^ 64 ->
  val_mem segs (rd W mem) (f + SRC_COOKIE_OFF) 8 p ->
  SRr segs W (cfg_at segs PFFLUSH_MUSL_U regs mem md) (wffu_post STK W ly S regs mem md f b C p).
Proof.
intros STK W ly S regs mem md ch f b C p r1 HSTK HPRE G10 HSRC Hblk Hbd H8 H16 Hr1 HCKp.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & _).
destruct (al_blocks _ _ LAWS ly S W mem md f SRC_FILE_BLOCK HAR Hblk) as (Hf16 & Hf0 & Hfceil & _ & Hfb & _).
change (req_size SRC_FILE_BLOCK) with SRC_FILE_BLOCK in Hfceil, Hfb. unfold SRC_FILE_BLOCK in Hfceil, Hfb.
unfold YK0s.ret_ok in Hra.
pose proof HSRC as (Wn & cpos & fl & mdv & HX). cbv zeta in HX.
destruct HX as (Hp0 & Hpc & Hcn & Hn63 & Hbw & Hcp & HWd & Hbok & HC & HST & HWIN & HFL & HFL24 & HMD & HCK &
  HENV & HHD & Hfnz).
destruct HST as (S24 & S64 & S72 & S80 & S88 & S96 & Sc8 & Sc16 & Sc24 & Sc32 & S152 & S32 & S40 & S48 & S56 &
  S104 & S112 & S168 & S120 & S140 & S144 & Sf0 & Sf16 & Sb0 & Sdisj).
unfold SRC_FILE_BLOCK in Sdisj.
set (sp0 := spZ regs) in *.
remember (Ereg regs [w64 r1]) as E eqn:HE.
assert (E1 : ew E 1 = getr regs 1) by (rewrite HE; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2u : bv_unsigned (ew E 2) = sp0) by (rewrite HE, (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E10u : bv_unsigned (ew E 10) = f).
{ rewrite HE, (ew_Ereg_nat regs _ 10 10%bv eq_refl), G10. apply unsigned_lit_small. lia. }
assert (E32 : ew E 32 = Z_to_bv 64 r1) by (rewrite HE; reflexivity).
pose proof (ajournal_init segs B STK (asource_fp f) ly S W regs mem md ch HPRE) as HJ.
unfold cfg_at. change (w64 PFFLUSH_MUSL_U) with (Z_to_bv 64 PFFLUSH_MUSL_U).
assert (HS : st_ok segs E ssA (restrict (w_H W) (mkst regs (Z_to_bv 64 PFFLUSH_MUSL_U) mem (seg_rom segs)))).
{ rewrite restrict_mkst_fx. unfold ssA. rewrite HE. apply (entry_st_ok_full segs); try rewrite <- HE.
  - rewrite HE. apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
    + unfold stkR. apply (region_ok_stack segs E _ 2 sp0 (-32)); [exact E2u | lia | lia |].
      intros a Ha. apply (apresent_writable segs). apply Hpres. lia.
    + unfold fileA1, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E10u. split; [lia|]. split; [lia|]. split.
      { intros o Ho. apply (apresent_writable segs). apply (proj1 (Hfb (f + o) ltac:(lia))). }
      unfold ck.
      apply Forall_cons; [apply (chunk_ok_val segs E _ f 8 8%N (SOff 32 0) r1);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | exact H8]|].
      apply Forall_cons; [apply (chunk_ok_val segs E _ f 16 8%N (SOff 32 0) r1);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | exact H16]|].
      apply Forall_nil.
    + unfold fileA2, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E10u. split; [lia|]. split; [lia|]. split.
      { intros o Ho. apply (apresent_writable segs). apply (proj1 (Hfb (f + o) ltac:(lia))). }
      unfold ck.
      apply Forall_cons; [apply (chunk_ok_val segs E _ f 32 8%N (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact S32]|].
      apply Forall_cons; [apply (chunk_ok_val segs E _ f 40 8%N (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact S40]|].
      apply Forall_cons; [apply (chunk_ok_val segs E _ f 48 8%N (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact S48]|].
      apply Forall_cons; [apply (chunk_ok_val segs E _ f 56 8%N (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact S56]|].
      apply Forall_nil.
    + unfold fileA3, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E10u. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      unfold ck.
      apply Forall_cons; [apply (chunk_ok_val segs E _ f 140 4%N (SLit U32M1) U32M1);
        [reflexivity | unfold U32M1; cbn; lia | cbn; lia | exact S140]|].
      apply Forall_nil.
  - apply pairwise_disjoint_of_extents. unfold stkR, fileA1, fileA2, fileA3, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2u, E10u.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; exact I]. cbn [f_atoms factsA atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2u, E10u, E32, unsigned_lit_small by lia. change (2 ^ 4) with 16. change (2 ^ 0) with 1.
    rewrite Z.mod_1_r. repeat split; lia. }
aj_run TBL HS HJ.
- unfold ssA. cbn [ss_mem].
  eapply awr_ok_cons_stack; [reflexivity | exact E2u | cbn; lia | cbn; lia |].
  eapply awr_ok_cons_block; [reflexivity | exact E10u | exact Hblk | cbn; lia | unfold req_size, SRC_FILE_BLOCK; cbn; lia | |].
  { intros a Ha. unfold fileA1 in Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. exists (f, f + SRC_FILE_BLOCK).
    split; [left; reflexivity | cbn [fst snd]; unfold SRC_FILE_BLOCK; lia]. }
  eapply awr_ok_cons_block; [reflexivity | exact E10u | exact Hblk | cbn; lia | unfold req_size, SRC_FILE_BLOCK; cbn; lia | |].
  { intros a Ha. unfold fileA2 in Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. exists (f, f + SRC_FILE_BLOCK).
    split; [left; reflexivity | cbn [fst snd]; unfold SRC_FILE_BLOCK; lia]. }
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil.
- lazymatch type of HS with st_ok _ _ ?s _ => set (ssF := s) in HS end.
  eapply (SRr_ret_at segs wffu_tbl TBL Hwx W E); [exact HS | reflexivity | vm_compute; reflexivity |].
  intros mat2.
  set (m3 := mrestrict (w_H W) (ms_mem ms)).
  assert (FR : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 32 <= a < sp0) -> ~ (f + 8 <= a < f + 24) ->
    ~ (f + 32 <= a < f + 64) -> mbyte segs m3 a = mbyte segs (rd W mem) a).
  { intros a Ha H1 H2 H3. apply (mb_frame E (ss_mem ssA) _ _ a HFr Ha). unfold ssA. cbn [ss_mem]. apply nwr_all.
    repeat (apply Forall_cons; [unfold stkR, fileA1, fileA2, fileA3; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val];
      rewrite ?E2u, ?E10u; lia|]). apply Forall_nil. }
  assert (FV : forall i off z, chunk_at ssF i off 8%N (SLit z) = true -> rbase_at ssF i = Some 10%nat ->
    0 <= z < 2 ^ 64 -> val_mem segs m3 (f + off) 8 z).
  { intros i off z Hc Hb Hz.
    pose proof (val_of_chunk_at E ssF (w_H W) ms i off 8%N (SLit z) z 10 HS Hc Hb eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V.
    rewrite E10u in V. exact V. }
  pose proof (FV 1%nat 8 0 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia)) as V8.
  pose proof (FV 1%nat 16 0 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia)) as V16.
  pose proof (FV 2%nat 32 0 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia)) as V32.
  pose proof (FV 2%nat 40 0 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia)) as V40.
  pose proof (FV 2%nat 48 0 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia)) as V48.
  pose proof (FV 2%nat 56 0 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia)) as V56.
  assert (VCK : val_mem segs m3 (f + SRC_COOKIE_OFF) 8 p).
  { eapply vm_fr; [|exact HCKp]. intros x Hx. simpl Z.of_nat in Hx. unfold SRC_COOKIE_OFF in Hx. apply FR; lia. }
  assert (R1 : getr (ms_regs ms) 1 = getr regs 1).
  { rewrite (reg_of E ssF (w_H W) ms 1%bv (SOff 1 0) HS ltac:(vm_compute; reflexivity)). cbn [sv_denot].
    rewrite E1, Z.add_0_r. apply Z_to_bv_bv_unsigned. }
  unfold wffu_post. exists (ms_regs ms), (ms_mem ms). eexists.
  split; [rewrite R1, Hra; reflexivity|].
  split; [apply (ajournal_materialize segs B LAWS segs_low); exact HJ|].
  split.
  { apply (aregs_preserved_of_st_ok segs (w_H W) E ssF ms regs [w64 r1] HS);
      [rewrite HE; split; [intros; reflexivity | reflexivity] | vm_compute; reflexivity]. }
  split; [rewrite (reg_of E ssF (w_H W) ms 10%bv (SLit 0) HS ltac:(vm_compute; reflexivity)); reflexivity|].
  split.
  { apply (asource_unbuf_of (rd W mem) m3 f b C p HSRC).
    - intros a Ha H1 H2 H3. unfold SRC_FILE_BLOCK in Ha. apply FR; [lia | lia | exact H1 | exact H2].
    - eapply garr8_frame; [exact HC|]. intros a Ha. apply FR; lia.
    - apply (env_tr (rd W mem) m3 HENV). intros a Ha. destruct (env_addr_img a Ha) as [Hi Hlo].
      assert (Hnb : ~ (f <= a < f + SRC_FILE_BLOCK)).
      { intros Hr. apply (blk_img segs B LAWS ly S W mem md f SRC_FILE_BLOCK a HAR Hblk); [cbn; unfold SRC_FILE_BLOCK in *; lia | exact Hi]. }
      unfold SRC_FILE_BLOCK in Hnb. apply FR; lia.
    - eapply vm_fr; [|exact HHD]. intros x Hx. simpl Z.of_nat in Hx.
      destruct (env_addr_img x (head_env_addr x Hx)) as [Hi Hlo].
      assert (Hnb : ~ (f <= x < f + SRC_FILE_BLOCK)).
      { intros Hr. apply (blk_img segs B LAWS ly S W mem md f SRC_FILE_BLOCK x HAR Hblk); [cbn; unfold SRC_FILE_BLOCK in *; lia | exact Hi]. }
      unfold SRC_FILE_BLOCK in Hnb. apply FR; lia.
    - exact V8.
    - exact V16.
    - exact V32.
    - exact V40.
    - exact V48.
    - exact V56.
    - exact VCK. }
  split; [exact VCK|].
  split; repeat rewrite (proj1 (wvb_io _ _ _)); repeat rewrite (proj2 (wvb_io _ _ _)); reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* 7. CASE FULL: rpos <> rend. Run to mseek, mseek's contract, run from 0x8e3a4 to ret.              *)
(* ---------------------------------------------------------------------------------------------- *)
(* mseek's rewind contract, as stated by PFmopsM.v. NAMED SECTION HYPOTHESIS: a Theorem Labs lane proves it on this
   image (at PMSEEK_U = as_seek pcap_KS), so this lane does not wait on it. *)
Hypothesis MSEEK : amseek_rewind_spec SK segs B K (as_seek K).
(* jalr clears bit 0 of its target: the call reaches as_seek K only when as_seek K is even. A fact of the
   symbol record K, as MSEEK's address is; pcap_KS's as_seek is 0x8eaf4 (PMSEEK_U), which is even. *)
Hypothesis SEEK_EVEN : as_seek K mod 2 = 0.

Ltac kchain E3 HE3 ss4 ms4 regs2 HS4 HPm G E HE ss1 ms1 regs HS1 r :=
  etransitivity; [exact (reg_kept E3 ss4 _ ms4 regs2 _ r HS4 HE3 ltac:(lia) ltac:(vm_compute; reflexivity))|];
  etransitivity; [exact (HPm r ltac:(unfold acallee_saved; lia))|];
  etransitivity; [exact (G (Z_to_bv 5 r) ltac:(reg_neq_tac))|];
  exact (reg_kept E ss1 _ ms1 regs _ r HS1 HE ltac:(lia) ltac:(vm_compute; reflexivity)).

Lemma wffu_full : forall STK (W : world segs) ly S regs mem md ch f b C p r1 r2 cpos,
  80 <= STK -> afn_pre segs B STK ly S W regs mem md ch -> getr regs 10 = Z_to_bv 64 f ->
  asource_at segs K (rd W mem) f b C p -> In (f, SRC_FILE_BLOCK) (ablocks B ly S) ->
  (b + Z.of_nat (length C) <= spZ regs - STK \/ spZ regs <= b) ->
  val_mem segs (rd W mem) (f + 8) 8 r1 -> val_mem segs (rd W mem) (f + 16) 8 r2 ->
  0 <= r1 < 2 ^ 64 -> 0 <= r2 < 2 ^ 64 -> r1 <> r2 -> r2 - r1 = cpos - p ->
  val_mem segs (rd W mem) (f + SRC_COOKIE_OFF) 8 cpos -> p <= cpos ->
  SRr segs W (cfg_at segs PFFLUSH_MUSL_U regs mem md) (wffu_post STK W ly S regs mem md f b C p).
Proof.
intros STK W ly S regs mem md ch f b C p r1 r2 cpos HSTK HPRE G10 HSRC Hblk Hbd H8 H16 Hr1 Hr2 Hne H12 HCKc Hpc.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & _).
destruct (al_blocks _ _ LAWS ly S W mem md f SRC_FILE_BLOCK HAR Hblk) as (Hf16 & Hf0 & Hfceil & _ & Hfb & _).
change (req_size SRC_FILE_BLOCK) with SRC_FILE_BLOCK in Hfceil, Hfb. unfold SRC_FILE_BLOCK in Hfceil, Hfb.
unfold YK0s.ret_ok in Hra.
pose proof HSRC as (Wn & cpos' & fl & mdv & HX). cbv zeta in HX.
destruct HX as (Hp0 & Hpc' & Hcn & Hn63 & Hbw & Hcp & HWd & Hbok & HC & HST & HWIN & HFL & HFL24 & HMD & HCK &
  HENV & HHD & Hfnz).
destruct HST as (S24 & S64 & S72 & S80 & S88 & S96 & Sc8 & Sc16 & Sc24 & Sc32 & S152 & S32 & S40 & S48 & S56 &
  S104 & S112 & S168 & S120 & S140 & S144 & Sf0 & Sf16 & Sb0 & Sdisj).
unfold SRC_FILE_BLOCK in Sdisj.
set (sp0 := spZ regs) in *.
remember (Ereg regs [w64 r1; w64 r2; w64 (as_seek K)]) as E eqn:HE.
assert (E1 : ew E 1 = getr regs 1) by (rewrite HE; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2u : bv_unsigned (ew E 2) = sp0) by (rewrite HE, (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E10u : bv_unsigned (ew E 10) = f).
{ rewrite HE, (ew_Ereg_nat regs _ 10 10%bv eq_refl), G10. apply unsigned_lit_small. lia. }
assert (E32 : ew E 32 = Z_to_bv 64 r1) by (rewrite HE; reflexivity).
assert (E33 : ew E 33 = Z_to_bv 64 r2) by (rewrite HE; reflexivity).
assert (E34 : ew E 34 = Z_to_bv 64 (as_seek K)) by (rewrite HE; reflexivity).
pose proof (ajournal_init segs B STK (asource_fp f) ly S W regs mem md ch HPRE) as HJ.
unfold cfg_at. change (w64 PFFLUSH_MUSL_U) with (Z_to_bv 64 PFFLUSH_MUSL_U).
assert (HS : st_ok segs E ssB (restrict (w_H W) (mkst regs (Z_to_bv 64 PFFLUSH_MUSL_U) mem (seg_rom segs)))).
{ unfold ssB. apply st_ok_assume.
  - rewrite restrict_mkst_fx. rewrite HE. apply (entry_st_ok_full segs); try rewrite <- HE.
    + rewrite HE. apply regs_ok_Ereg.
    + vm_compute. reflexivity.
    + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * unfold stkR. apply (region_ok_stack segs E _ 2 sp0 (-32)); [exact E2u | lia | lia |].
        intros a Ha. apply (apresent_writable segs). apply Hpres. lia.
      * unfold fileB, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite E10u. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        unfold ck.
        apply Forall_cons; [apply (chunk_ok_val segs E _ f 8 8%N (SOff 32 0) r1);
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | exact H8]|].
        apply Forall_cons; [apply (chunk_ok_val segs E _ f 16 8%N (SOff 33 0) r2);
          [cbn [sv_denot]; rewrite E33, Z.add_0_r, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | exact H16]|].
        apply Forall_cons; [apply (chunk_ok_val segs E _ f 40 8%N (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact S40]|].
        apply Forall_cons; [apply (chunk_ok_val segs E _ f 56 8%N (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact S56]|].
        apply Forall_cons; [apply (chunk_ok_val segs E _ f 80 8%N (SOff 34 0) (as_seek K mod 2 ^ 64));
          [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_unsigned; reflexivity
          | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_pos_bound; lia | cbn; lia
          | exact (val_mem_mod64 _ _ _ S80)]|].
        apply Forall_cons; [apply (chunk_ok_val segs E _ f 140 4%N (SLit U32M1) U32M1);
          [reflexivity | unfold U32M1; cbn; lia | cbn; lia | exact S140]|].
        apply Forall_nil.
    + apply pairwise_disjoint_of_extents. unfold stkR, fileB, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2u, E10u.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
    + split; [|split; exact I]. cbn [f_atoms factsB atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E2u, E10u, E32, E33, E34, (unsigned_lit_small r1 Hr1), (unsigned_lit_small r2 Hr2), Z_to_bv_unsigned.
      unfold bv_wrap, bv_modulus.
      change (2 ^ Z.of_N 64) with (2 ^ 64). pose proof (Z.mod_pos_bound (as_seek K) (2 ^ 64) ltac:(lia)).
      change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
  - cbn [ac_c ac_a ac_b]. rewrite branch_ne_U, (U_atom E 32 r1 E32 Hr1), (U_atom E 33 r2 E33 Hr2).
    destruct (Z.eqb_spec r1 r2); [contradiction | reflexivity]. }
aj_run TBL HS HJ.
- unfold ssB, add_cond. cbn [ss_mem].
  eapply awr_ok_cons_stack; [reflexivity | exact E2u | cbn; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil.
- rename ms into ms1. rename HS into HS1. rename HJ into HJ1. rename HFr into HFr1.
  lazymatch type of HS1 with st_ok _ _ ?s _ => set (ss1 := s) in HS1 end.
  (* the run stops AT the call: jalr ra, 0(a3) *)
  assert (Hpc1 : ss_pc ss1 = PFFLUSH_JALR_U) by reflexivity.
  assert (R1 : getr (ms_regs ms1) 1 = getr regs 1).
  { rewrite (reg_of E ss1 _ ms1 1%bv (SOff 1 0) HS1 ltac:(vm_compute; reflexivity)). cbn [sv_denot].
    rewrite E1, Z.add_0_r. apply Z_to_bv_bv_unsigned. }
  assert (R2 : getr (ms_regs ms1) 2 = Z_to_bv 64 (sp0 - 32)).
  { rewrite (reg_of E ss1 _ ms1 2%bv (SOff 2 (-32)) HS1 ltac:(vm_compute; reflexivity)). cbn [sv_denot].
    rewrite E2u. f_equal; lia. }
  assert (R3 : getr (ms_regs ms1) 3 = getr regs 3)
    by exact (reg_kept E ss1 _ ms1 regs _ 3 HS1 HE ltac:(lia) ltac:(vm_compute; reflexivity)).
  assert (R4 : getr (ms_regs ms1) 4 = getr regs 4)
    by exact (reg_kept E ss1 _ ms1 regs _ 4 HS1 HE ltac:(lia) ltac:(vm_compute; reflexivity)).
  assert (R8 : getr (ms_regs ms1) 8 = getr regs 8)
    by exact (reg_kept E ss1 _ ms1 regs _ 8 HS1 HE ltac:(lia) ltac:(vm_compute; reflexivity)).
  assert (R9 : getr (ms_regs ms1) 9 = Z_to_bv 64 f).
  { rewrite (reg_of E ss1 _ ms1 9%bv (SOff 10 0) HS1 ltac:(vm_compute; reflexivity)). cbn [sv_denot].
    rewrite E10u, Z.add_0_r. reflexivity. }
  assert (R10 : getr (ms_regs ms1) 10 = Z_to_bv 64 f).
  { rewrite (reg_of E ss1 _ ms1 10%bv (SOff 10 0) HS1 ltac:(vm_compute; reflexivity)). cbn [sv_denot].
    rewrite E10u, Z.add_0_r. reflexivity. }
  assert (R11 : getr (ms_regs ms1) 11 = Z_to_bv 64 (- (cpos - p))).
  { rewrite (reg_of E ss1 _ ms1 11%bv (SAlu ALU_ADD (SOff 32 0) (SMd M_MUL (SOff 33 0) (SLit (-1)))) HS1
      ltac:(vm_compute; reflexivity)).
    rewrite denot_lit_U, U_SAlu, U_SMd, (U_atom E 32 r1 E32 Hr1), (U_atom E 33 r2 E33 Hr2), U_SLit.
    cbn [zalu_raw zmd_raw]. apply Z_to_bv64_mod_eq. unfold zcanon, M64.
    replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
    rewrite Z.mod_mod by lia. rewrite Zplus_mod_idemp_r.
    replace (r1 + r2 * (2 ^ 64 - 1)) with (- (cpos - p) + r2 * 2 ^ 64) by lia.
    rewrite Z_mod_plus_full. reflexivity. }
  assert (R12 : getr (ms_regs ms1) 12 = Z_to_bv 64 SEEK_CUR)
    by (rewrite (reg_of E ss1 _ ms1 12%bv (SLit 1) HS1 ltac:(vm_compute; reflexivity)); reflexivity).
  assert (R13 : getr (ms_regs ms1) 13 = Z_to_bv 64 (as_seek K)).
  { rewrite (reg_of E ss1 _ ms1 13%bv (SOff 34 0) HS1 ltac:(vm_compute; reflexivity)). cbn [sv_denot].
    rewrite E34, Z.add_0_r. apply Z_to_bv_bv_unsigned. }
  assert (R18 : getr (ms_regs ms1) 18 = Z_to_bv 64 1)
    by (rewrite (reg_of E ss1 _ ms1 18%bv (SLit 1) HS1 ltac:(vm_compute; reflexivity)); reflexivity).
  (* the memory at the call: only fflush's own frame moved *)
  assert (FR1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 32 <= a < sp0) ->
    mbyte segs (rd W (ms_mem ms1)) a = mbyte segs (rd W mem) a).
  { intros a Ha H1. apply (mb_frame E (ss_mem ssB) _ _ a HFr1 Ha). unfold ssB, add_cond. cbn [ss_mem]. apply nwr2;
    unfold stkR, fileB; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite ?E2u, ?E10u; lia. }
  assert (HSRC1 : asource_at segs K (rd W (ms_mem ms1)) f b C p).
  { apply (asource_at_tr (rd W mem) _ f b C p HSRC).
    - intros a Ha. unfold SRC_FILE_BLOCK in Ha. apply FR1; lia.
    - intros a Ha. apply FR1; lia.
    - intros a Ha. destruct (env_addr_img a Ha) as [Hi Hlo]. apply FR1; lia. }
  (* the jalr, taken by hand *)
  rewrite (st_ok_restrict_mkst segs (w_H W) E ss1 ms1 HS1 eq_refl), Hpc1.
  eapply (SRr_step segs Hwx W); [reflexivity | |].
  { rewrite restrict_mkst_fx.
    apply (step_jalr_link segs _ _ _ _ (Z_to_bv 32 PFFLUSH_JALR_U_W) 1%bv 13%bv (0%bv : bv 12) (Z_to_bv 64 (as_seek K))).
    - apply TBL. vm_compute. reflexivity.
    - vm_compute. reflexivity.
    - vm_refl_bv.
    - reflexivity.
    - exact R13. }
  intros md1 Hsame1. rewrite (same_but_materialized_wvb _ md1 Hsame1).
  cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
  pose proof (ajournal_materialize segs B LAWS segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (m_vm_materialized md1) HJ1) as HJ1'.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md1' := m) in * end.
  set (rg := regupd (ms_regs ms1) 1%bv (v_addi (Z_to_bv 64 PFFLUSH_JALR_U) 4)).
  assert (G : forall r : bv 5, r <> 1%bv -> getr rg r = getr (ms_regs ms1) r).
  { intros r Hr. unfold rg. apply getr_other. exact Hr. }
  assert (G1 : getr rg 1 = Z_to_bv 64 PFFLUSH_RET_MSEEK_U).
  { unfold rg. rewrite getr_same by reg_neq_tac. unfold v_addi. rewrite unsigned_lit_small by (unfold PFFLUSH_JALR_U; lia).
    reflexivity. }
  assert (Htgt : v_jalr (Z_to_bv 64 (as_seek K)) (bv_signed (0%bv : bv 12)) = w64 (as_seek K)).
  { change (bv_signed (0%bv : bv 12)) with 0. apply v_jalr_even. exact SEEK_EVEN. }
  rewrite Htgt.
  assert (Hsp1 : spZ rg = sp0 - 32).
  { unfold spZ. rewrite (G 2%bv ltac:(reg_neq_tac)), R2. apply unsigned_lit_small. lia. }
  eapply SRr_bind.
  { apply (MSEEK W ly S rg (ms_mem ms1) md1' ch f b C p cpos).
    - eapply (afn_pre_at segs B STK (spZ regs) (asource_fp f) ly S W mem md [] ly S W (ms_mem ms1) md1' 0
        rg PMSEEK_STK (-32) ch HJ1').
      + rewrite Hsp1. lia.
      + reflexivity.
      + lia.
      + unfold PMSEEK_STK. lia.
      + unfold PMSEEK_STK. lia.
      + rewrite G1. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity.
      + unfold raZ. rewrite G1, unsigned_lit_small; unfold PFFLUSH_RET_MSEEK_U; lia.
      + rewrite (G 3%bv ltac:(reg_neq_tac)), R3. exact Hgp.
      + rewrite (G 4%bv ltac:(reg_neq_tac)), R4. exact Htp.
      + unfold s0Z. rewrite (G 8%bv ltac:(reg_neq_tac)), R8, Hsp1.
        apply (achain_lower ly _ sp0 (sp0 - 32) _ ch); [|lia].
        apply (achain_kept ly (aview segs (w_H W) mem) _ sp0 _ ch sp0 Hch ltac:(lia) ltac:(lia)).
        intros a Ha. unfold aview. rewrite (FR1 a ltac:(lia) ltac:(lia)). reflexivity.
    - exact HSRC1.
    - exact Hblk.
    - rewrite Hsp1. unfold PMSEEK_STK. lia.
    - eapply vm_fr; [|exact HCKc]. intros x Hx. simpl Z.of_nat in Hx. unfold SRC_COOKIE_OFF in Hx. apply FR1; lia.
    - exact Hpc.
    - rewrite (G 10%bv ltac:(reg_neq_tac)). exact R10.
    - rewrite (G 11%bv ltac:(reg_neq_tac)). exact R11.
    - rewrite (G 12%bv ltac:(reg_neq_tac)). exact R12. }
  intros W2 c2 HW2 (regs2 & mem2 & md2 & -> & HJm & HPm & H10m & HCKm & HFm & HCm & HENVm & HHDm & Hfdm & Hfsm).
  rewrite Hsp1 in HJm.
  pose proof (wffu_aj_sub_tok segs B LAWS segs_low STK (spZ regs) (asource_fp f) ly S W mem md [] ly S W
    (ms_mem ms1) md1' 0 PMSEEK_STK (sp0 - 32) (asource_fp f) [] ly S W2 mem2 md2 0 HJ1' HJm
    ltac:(unfold PMSEEK_STK; lia) ltac:(lia) ltac:(intros a Ha; left; exact Ha)) as HJ2.
  cbn [app] in HJ2. change (0 + 0) with 0 in HJ2.
  pose proof HJm as (HARm & _ & _ & _ & _ & _ & _ & _ & F1m & _).
  assert (FS2 : forall a, sp0 - 32 <= a < sp0 -> mbyte segs (rd W2 mem2) a = mbyte segs (rd W (ms_mem ms1)) a).
  { intros a Ha. apply (mbyte_of_aview segs). apply F1m; unfold PMSEEK_STK; lia. }
  (* the four words fflush saved, read back after mseek *)
  set (vra := bv_unsigned (getr regs 1)). set (vs0 := bv_unsigned (getr regs 8)).
  set (vs1 := bv_unsigned (getr regs 9)). set (vs2 := bv_unsigned (getr regs 18)).
  assert (SV : forall off z v, -32 <= off <= -8 -> chunk_at ss1 0 off 8%N v = true -> sv_denot E v = Z_to_bv 64 z ->
    0 <= z < 2 ^ 64 -> val_mem segs (rd W2 mem2) (sp0 + off) 8 z).
  { intros off z v Ho Hc Hv Hz.
    pose proof (val_of_chunk_at E ss1 (w_H W) ms1 0 off 8%N v z 2 HS1 Hc eq_refl Hv ltac:(cbn; lia) ltac:(cbn; lia)) as V.
    rewrite E2u in V. eapply vm_fr; [|exact V]. intros x Hx. simpl Z.of_nat in Hx. apply FS2. lia. }
  assert (E8 : ew E 8 = getr regs 8) by (rewrite HE; exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
  assert (E9 : ew E 9 = getr regs 9) by (rewrite HE; exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
  assert (E18 : ew E 18 = getr regs 18) by (rewrite HE; exact (ew_Ereg_nat regs _ 18 18%bv eq_refl)).
  pose proof (u64_range (getr regs 1)) as U1. pose proof (u64_range (getr regs 8)) as U8.
  pose proof (u64_range (getr regs 9)) as U9. pose proof (u64_range (getr regs 18)) as U18.
  pose proof (SV (-8) vra (SOff 1 0) ltac:(lia) ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot]; rewrite E1, Z.add_0_r; reflexivity) U1) as SVra.
  pose proof (SV (-16) vs0 (SOff 8 0) ltac:(lia) ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot]; rewrite E8, Z.add_0_r; reflexivity) U8) as SVs0.
  pose proof (SV (-24) vs1 (SOff 9 0) ltac:(lia) ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot]; rewrite E9, Z.add_0_r; reflexivity) U9) as SVs1.
  pose proof (SV (-32) vs2 (SOff 18 0) ltac:(lia) ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot]; rewrite E18, Z.add_0_r; reflexivity) U18) as SVs2.
  (* the FILE after mseek: every byte but the cookie is fflush's entry value *)
  assert (TF : forall off (n : nat) v, 0 <= off -> off + Z.of_nat n <= SRC_FILE_BLOCK ->
    off + Z.of_nat n <= SRC_COOKIE_OFF \/ SRC_COOKIE_OFF + 8 <= off ->
    val_mem segs (rd W mem) (f + off) n v -> val_mem segs (rd W2 mem2) (f + off) n v).
  { intros off n v H0 H1 H2 Hv. eapply vm_fr; [|exact Hv]. intros x Hx.
    replace x with (f + (x - f)) by lia. rewrite (HFm (x - f)) by (unfold SRC_FILE_BLOCK, SRC_COOKIE_OFF in *; lia).
    replace (f + (x - f)) with x by lia. apply FR1; unfold SRC_FILE_BLOCK in *; lia. }
  pose proof (TF 48 8%nat 0 ltac:(lia) ltac:(unfold SRC_FILE_BLOCK; simpl Z.of_nat; lia)
    ltac:(left; unfold SRC_COOKIE_OFF; simpl Z.of_nat; lia) S48) as T48.
  (* the registers after mseek *)
  assert (P2 : getr regs2 2 = getr (ms_regs ms1) 2).
  { transitivity (getr rg 2); [exact (HPm 2 ltac:(unfold acallee_saved; lia)) | exact (G 2%bv ltac:(reg_neq_tac))]. }
  assert (P9 : getr regs2 9 = getr (ms_regs ms1) 9).
  { transitivity (getr rg 9); [exact (HPm 9 ltac:(unfold acallee_saved; lia)) | exact (G 9%bv ltac:(reg_neq_tac))]. }
  assert (P18 : getr regs2 18 = getr (ms_regs ms1) 18).
  { transitivity (getr rg 18); [exact (HPm 18 ltac:(unfold acallee_saved; lia)) | exact (G 18%bv ltac:(reg_neq_tac))]. }
  remember (Ereg regs2 [w64 vra; w64 vs0; w64 vs1; w64 vs2]) as E3 eqn:HE3.
  assert (E3_32 : ew E3 32 = w64 vra) by (rewrite HE3; reflexivity).
  assert (E3_33 : ew E3 33 = w64 vs0) by (rewrite HE3; reflexivity).
  assert (E3_34 : ew E3 34 = w64 vs1) by (rewrite HE3; reflexivity).
  assert (E3_35 : ew E3 35 = w64 vs2) by (rewrite HE3; reflexivity).
  assert (E3_2u : bv_unsigned (ew E3 2) = sp0 - 32).
  { rewrite HE3, (ew_Ereg_nat regs2 _ 2 2%bv eq_refl), P2, R2. apply unsigned_lit_small. lia. }
  assert (E3_9u : bv_unsigned (ew E3 9) = f).
  { rewrite HE3, (ew_Ereg_nat regs2 _ 9 9%bv eq_refl), P9, R9. apply unsigned_lit_small. lia. }
  assert (E3_18 : getr regs2 18 = sv_denot E3 (SLit 1)) by (rewrite P18; exact R18).
  rewrite G1.
  assert (HST : st_ok segs E3 ssT (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 PFFLUSH_RET_MSEEK_U) mem2 (seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold ssT. rewrite HE3. apply (entry_st_ok_full segs); try rewrite <- HE3.
    - apply regs_ok_pin; [rewrite HE3; apply regs_ok_Ereg | intros X; discriminate X | exact E3_18].
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
      + unfold stkT, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite E3_2u. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        unfold ck.
        apply Forall_cons; [apply (chunk_ok_val segs E3 _ (sp0 - 32) 0 8%N (SOff 35 0) vs2);
          [cbn [sv_denot]; rewrite E3_35; unfold w64; rewrite unsigned_lit_small by exact U18;
           rewrite Z.add_0_r; reflexivity
          | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact U18 | cbn; lia
          | replace (sp0 - 32 + 0) with (sp0 + -32) by lia; exact SVs2]|].
        apply Forall_cons; [apply (chunk_ok_val segs E3 _ (sp0 - 32) 8 8%N (SOff 34 0) vs1);
          [cbn [sv_denot]; rewrite E3_34; unfold w64; rewrite unsigned_lit_small by exact U9;
           rewrite Z.add_0_r; reflexivity
          | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact U9 | cbn; lia
          | replace (sp0 - 32 + 8) with (sp0 + -24) by lia; exact SVs1]|].
        apply Forall_cons; [apply (chunk_ok_val segs E3 _ (sp0 - 32) 16 8%N (SOff 33 0) vs0);
          [cbn [sv_denot]; rewrite E3_33; unfold w64; rewrite unsigned_lit_small by exact U8;
           rewrite Z.add_0_r; reflexivity
          | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact U8 | cbn; lia
          | replace (sp0 - 32 + 16) with (sp0 + -16) by lia; exact SVs0]|].
        apply Forall_cons; [apply (chunk_ok_val segs E3 _ (sp0 - 32) 24 8%N (SOff 32 0) vra);
          [cbn [sv_denot]; rewrite E3_32; unfold w64; rewrite unsigned_lit_small by exact U1;
           rewrite Z.add_0_r; reflexivity
          | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact U1 | cbn; lia
          | replace (sp0 - 32 + 24) with (sp0 + -8) by lia; exact SVra]|].
        apply Forall_nil.
      + unfold fileT1, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite E3_9u. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
        intros o Ho. apply (apresent_writable segs).
        destruct (al_blocks _ _ LAWS ly S W2 mem2 md2 f SRC_FILE_BLOCK HARm Hblk) as (_ & _ & _ & _ & Hfb2 & _).
        apply (proj1 (Hfb2 (f + o) ltac:(cbn; unfold SRC_FILE_BLOCK; lia))).
      + unfold fileT2, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite E3_9u. split; [lia|]. split; [lia|]. split.
        { intros o Ho. apply (apresent_writable segs).
          destruct (al_blocks _ _ LAWS ly S W2 mem2 md2 f SRC_FILE_BLOCK HARm Hblk) as (_ & _ & _ & _ & Hfb2 & _).
          apply (proj1 (Hfb2 (f + o) ltac:(cbn; unfold SRC_FILE_BLOCK; lia))). }
        unfold ck.
        apply Forall_cons; [apply (chunk_ok_val segs E3 _ f 48 8%N (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact T48]|].
        apply Forall_nil.
    - apply pairwise_disjoint_of_extents. unfold stkT, fileT1, fileT2, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E3_2u, E3_9u.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
    - split; [|split; exact I]. cbn [f_atoms factsT atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E3_2u, E3_9u, E3_32, E3_33, E3_34, E3_35. unfold w64.
      rewrite (unsigned_lit_small vra U1), (unsigned_lit_small vs0 U8), (unsigned_lit_small vs1 U9),
        (unsigned_lit_small vs2 U18).
      change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
      repeat split; lia. }
  aj_run TBL HST HJ2.
  + unfold ssT. cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|].
    eapply awr_ok_cons_block; [reflexivity | exact E3_9u | exact Hblk | cbn; lia | unfold req_size, SRC_FILE_BLOCK; cbn; lia | |].
    { intros a Ha. unfold fileT1 in Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. exists (f, f + SRC_FILE_BLOCK).
      split; [left; reflexivity | cbn [fst snd]; unfold SRC_FILE_BLOCK; lia]. }
    eapply awr_ok_cons_block; [reflexivity | exact E3_9u | exact Hblk | cbn; lia | unfold req_size, SRC_FILE_BLOCK; cbn; lia | |].
    { intros a Ha. unfold fileT2 in Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. exists (f, f + SRC_FILE_BLOCK).
      split; [left; reflexivity | cbn [fst snd]; unfold SRC_FILE_BLOCK; lia]. }
    apply awr_ok_nil.
  + rename ms into ms4. rename HST into HS4. rename HJ2 into HJ4. rename HFr into HFr4.
    lazymatch type of HS4 with st_ok _ _ ?s _ => set (ss4 := s) in HS4 end.
    eapply (SRr_ret_at segs wffu_tbl TBL Hwx W2 E3); [exact HS4 | reflexivity | vm_compute; reflexivity |].
    intros mat5.
    set (m4 := mrestrict (w_H W2) (ms_mem ms4)).
    assert (FR4 : forall a, 0 <= a < 2 ^ 64 -> ~ (f + 8 <= a < f + 24) -> ~ (f + 32 <= a < f + 64) ->
      mbyte segs m4 a = mbyte segs (rd W2 mem2) a).
    { intros a Ha H1 H2. apply (mb_frame E3 (ss_mem ssT) _ _ a HFr4 Ha). unfold ssT. cbn [ss_mem]. apply nwr_all.
      repeat (apply Forall_cons; [unfold stkT, fileT1, fileT2; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val];
        rewrite ?E3_2u, ?E3_9u; lia|]). apply Forall_nil. }
    assert (FV : forall i off z, chunk_at ss4 i off 8%N (SLit z) = true -> rbase_at ss4 i = Some 9%nat ->
      0 <= z < 2 ^ 64 -> val_mem segs m4 (f + off) 8 z).
    { intros i off z Hc Hb Hz.
      pose proof (val_of_chunk_at E3 ss4 (w_H W2) ms4 i off 8%N (SLit z) z 9 HS4 Hc Hb eq_refl
        ltac:(cbn; lia) ltac:(cbn; lia)) as V.
      rewrite E3_9u in V. exact V. }
    pose proof (FV 1%nat 8 0 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia)) as V8.
    pose proof (FV 1%nat 16 0 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia)) as V16.
    pose proof (FV 2%nat 32 0 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia)) as V32.
    pose proof (FV 2%nat 40 0 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia)) as V40.
    pose proof (FV 2%nat 48 0 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia)) as V48.
    pose proof (FV 2%nat 56 0 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia)) as V56.
    assert (VCK : val_mem segs m4 (f + SRC_COOKIE_OFF) 8 p).
    { eapply vm_fr; [|exact HCKm]. intros x Hx. simpl Z.of_nat in Hx. unfold SRC_COOKIE_OFF in Hx. apply FR4; lia. }
    assert (R41 : getr (ms_regs ms4) 1 = getr regs 1).
    { rewrite (reg_of E3 ss4 _ ms4 1%bv (SOff 32 0) HS4 ltac:(vm_compute; reflexivity)). cbn [sv_denot].
      rewrite E3_32. unfold w64. rewrite unsigned_lit_small by exact U1. rewrite Z.add_0_r.
      unfold vra. apply Z_to_bv_bv_unsigned. }
    unfold wffu_post. exists (ms_regs ms4), (ms_mem ms4). eexists.
    split; [rewrite R41, Hra; reflexivity|].
    split; [apply (ajournal_materialize segs B LAWS segs_low); exact HJ4|].
    split.
    { intros r Hr. unfold acallee_saved in Hr.
      assert (Hr' : r = 2 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 3 \/ r = 4 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
        r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      destruct Hr' as [-> | [-> | [-> | [-> | Hr']]]].
      - rewrite (reg_of E3 ss4 _ ms4 (Z_to_bv 5 2) (SOff 2 32) HS4 ltac:(vm_compute; reflexivity)). cbn [sv_denot].
        rewrite E3_2u. replace (sp0 - 32 + 32) with sp0 by lia. unfold sp0, spZ. apply Z_to_bv_bv_unsigned.
      - rewrite (reg_of E3 ss4 _ ms4 (Z_to_bv 5 8) (SOff 33 0) HS4 ltac:(vm_compute; reflexivity)). cbn [sv_denot].
        rewrite E3_33. unfold w64. rewrite unsigned_lit_small by exact U8. rewrite Z.add_0_r.
        unfold vs0. apply Z_to_bv_bv_unsigned.
      - rewrite (reg_of E3 ss4 _ ms4 (Z_to_bv 5 9) (SOff 34 0) HS4 ltac:(vm_compute; reflexivity)). cbn [sv_denot].
        rewrite E3_34. unfold w64. rewrite unsigned_lit_small by exact U9. rewrite Z.add_0_r.
        unfold vs1. apply Z_to_bv_bv_unsigned.
      - rewrite (reg_of E3 ss4 _ ms4 (Z_to_bv 5 18) (SOff 35 0) HS4 ltac:(vm_compute; reflexivity)). cbn [sv_denot].
        rewrite E3_35. unfold w64. rewrite unsigned_lit_small by exact U18. rewrite Z.add_0_r.
        unfold vs2. apply Z_to_bv_bv_unsigned.
      - destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]];
        match goal with |- getr _ (Z_to_bv 5 ?rr) = _ =>
          kchain E3 HE3 ss4 ms4 regs2 HS4 HPm G E HE ss1 ms1 regs HS1 rr end. }
    split; [rewrite (reg_of E3 ss4 _ ms4 10%bv (SLit 0) HS4 ltac:(vm_compute; reflexivity)); reflexivity|].
    split.
    { apply (asource_unbuf_of (rd W mem) m4 f b C p HSRC).
      - intros a Ha H1 H2 H3. rewrite (FR4 a ltac:(unfold SRC_FILE_BLOCK in Ha; lia) H1 H2).
        replace a with (f + (a - f)) by lia.
        rewrite (HFm (a - f)) by (unfold SRC_FILE_BLOCK, SRC_COOKIE_OFF in *; lia).
        replace (f + (a - f)) with a by lia. apply FR1; unfold SRC_FILE_BLOCK in *; lia.
      - eapply garr8_frame; [exact HCm|]. intros a Ha. apply FR4; lia.
      - apply (env_tr (rd W2 mem2) m4 HENVm). intros a Ha. destruct (env_addr_img a Ha) as [Hi Hlo].
        assert (Hnb : ~ (f <= a < f + SRC_FILE_BLOCK)).
        { intros Hr. apply (blk_img segs B LAWS ly S W mem md f SRC_FILE_BLOCK a HAR Hblk); [cbn; unfold SRC_FILE_BLOCK in *; lia | exact Hi]. }
        unfold SRC_FILE_BLOCK in Hnb. apply FR4; lia.
      - eapply vm_fr; [|exact HHDm]. intros x Hx. simpl Z.of_nat in Hx.
        destruct (env_addr_img x (head_env_addr x Hx)) as [Hi Hlo].
        assert (Hnb : ~ (f <= x < f + SRC_FILE_BLOCK)).
        { intros Hr. apply (blk_img segs B LAWS ly S W mem md f SRC_FILE_BLOCK x HAR Hblk); [cbn; unfold SRC_FILE_BLOCK in *; lia | exact Hi]. }
        unfold SRC_FILE_BLOCK in Hnb. apply FR4; lia.
      - exact V8.
      - exact V16.
      - exact V32.
      - exact V40.
      - exact V48.
      - exact V56.
      - exact VCK. }
    split; [exact VCK|].
    split; [ repeat rewrite (proj1 (wvb_io _ _ _)); rewrite Hfdm; unfold md1'; repeat rewrite (proj1 (wvb_io _ _ _)); reflexivity
           | repeat rewrite (proj2 (wvb_io _ _ _)); rewrite Hfsm; unfold md1'; repeat rewrite (proj2 (wvb_io _ _ _)); reflexivity ].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* 8. The musl entry, generic in the stack budget, and the spec itself at PFFLUSH_OWN_STK = 1840.    *)
(* ---------------------------------------------------------------------------------------------- *)
Theorem wffu_musl : forall STK, 80 <= STK -> forall rlo rhi, wffu_spec STK PFFLUSH_MUSL_U rlo rhi.
Proof.
intros STK HSTK rlo rhi W ly S regs mem md ch f b M C p HPRE G10 HRO HMI HSRC Hblk Hbd.
pose proof HPRE as (HAR & _).
pose proof asan_consts as (C1 & _).
destruct (al_blocks _ _ LAWS ly S W mem md f SRC_FILE_BLOCK HAR Hblk) as (_ & Hf0 & Hfceil & _).
change (req_size SRC_FILE_BLOCK) with SRC_FILE_BLOCK in Hfceil. unfold SRC_FILE_BLOCK in Hfceil.
pose proof HSRC as (Wn & cpos & fl & mdv & HX). cbv zeta in HX.
destruct HX as (Hp0 & Hpc & Hcn & Hn63 & Hbw & Hcp & HWd & Hbok & HC & HST & HWIN & HFL & HFL24 & HMD & HCK &
  HENV & HHD & Hfnz).
assert (HWV : exists r1 r2, val_mem segs (rd W mem) (f + 8) 8 r1 /\ val_mem segs (rd W mem) (f + 16) 8 r2 /\
  0 <= r1 < 2 ^ 64 /\ 0 <= r2 < 2 ^ 64 /\ r2 - r1 = Z.of_nat (length Wn)).
{ destruct HWIN as [(-> & H8 & H16) | (i & Hi0 & Hi1 & H8 & H16 & _)].
  - exists 0, 0. cbn [length Z.of_nat]. repeat split; try lia; assumption.
  - exists (f + SRC_BUF_OFF + i), (f + SRC_BUF_OFF + i + Z.of_nat (length Wn)).
    unfold SRC_BUF_OFF, SRC_BUFSIZ in *. repeat split; try lia; assumption. }
destruct HWV as (r1 & r2 & H8 & H16 & Hr1 & Hr2 & H12).
destruct (Z.eq_dec r1 r2) as [<- | Hne].
- refine (wffu_empty STK W ly S regs mem md ch f b C p r1 ltac:(lia) HPRE G10 HSRC Hblk Hbd H8 H16 Hr1 _).
  replace p with cpos by lia. exact HCK.
- exact (wffu_full STK W ly S regs mem md ch f b C p r1 r2 cpos HSTK HPRE G10 HSRC Hblk Hbd H8 H16 Hr1 Hr2 Hne
    ltac:(lia) HCK Hpc).
Qed.

Theorem afflush_source_spec_musl : forall rlo rhi, afflush_source_spec SK segs B K PFFLUSH_MUSL_U rlo rhi.
Proof. intros rlo rhi. rewrite <- wffu_spec_is. apply wffu_musl. unfold PFFLUSH_OWN_STK. lia. Qed.

End W.

(* The asan-ubsan image itself: segs_low, Hwx and TBL hold of AsanUbsan.M.loaded_segments by computation. What
   remains is the stream's image laws (ASIL) and mseek's contract (MSEEK), with the evenness of as_seek K. *)
Theorem pcapu_afflush_source_spec_musl_K {fx : YK11.FPState} {rc : YM05.RunCeil} :
  forall (SK : YI16.sink_head) (B : asyms) (K : asource_syms),
  asource_img_laws SK ausegs B K -> amseek_rewind_spec SK ausegs B K (as_seek K) -> as_seek K mod 2 = 0 ->
  forall rlo rhi, afflush_source_spec SK ausegs B K PFFLUSH_MUSL_U rlo rhi.
Proof.
intros SK B K ASIL MSEEK HEV.
exact (afflush_source_spec_musl SK ausegs B K wffu_ausegs_low wffu_ausegs_wx wffu_tbl_ok ASIL MSEEK HEV).
Qed.

(* The asan-ubsan image with ITS OWN symbol record, lib/B/Stdio/PSourceK.v's pcap_KS (KS_U): as_seek pcap_KS is
   PMSEEK_U 0x8eaf4 and is even, so what remains is ASIL and a Theorem Labs lane's amseek_rewind_spec at PMSEEK_U. *)
Theorem pcapu_afflush_source_spec_musl {fx : YK11.FPState} {rc : YM05.RunCeil} :
  forall (SK : YI16.sink_head) (B : asyms),
  asource_img_laws SK ausegs B pcap_KS -> amseek_rewind_spec SK ausegs B pcap_KS PMSEEK_U ->
  forall rlo rhi, afflush_source_spec SK ausegs B pcap_KS PFFLUSH_MUSL_U rlo rhi.
Proof.
intros SK B ASIL MSEEK.
exact (pcapu_afflush_source_spec_musl_K SK B pcap_KS ASIL MSEEK eq_refl).
Qed.

(* ============================================================================================== *)
(* 9. THE INTERCEPTOR ENTRY PFFLUSH_ICPT_U = 0x41618: iflush_front, the musl walk above, iflush_tail.   *)
(* ============================================================================================== *)
Section I.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} (SK : YI16.sink_head).
Variable B : asyms.
Let LAWSI : AR_laws YB1v.tfibsegs B := YG0q.AR_laws_ok YB1v.tfibsegs B.
(* The asan-ubsan symbol record: lib/Reusable/YF0m.v, a Theorem Labs lane's generated file (WIP values). *)
Hypothesis TB : YF0m.PcapSyms B.
Hypothesis ASILI : asource_img_laws SK YB1v.tfibsegs B pcap_KS.
(* mseek's contract, NAMED: a Theorem Labs lane proves it on this image in parallel. PMSEEK_U = as_seek pcap_KS. *)
Hypothesis MSEEKI : amseek_rewind_spec SK YB1v.tfibsegs B pcap_KS PMSEEK_U.
Local Notation tsegs := YB1v.tfibsegs.
Local Notation rd W mem := (mrestrict (w_H W) mem).

Lemma vmI : forall (m m' : word -> option byte) a (n : nat) v,
  (forall x, a <= x < a + Z.of_nat n -> mbyte tsegs m' x = mbyte tsegs m x) ->
  val_mem tsegs m a n v -> val_mem tsegs m' a n v.
Proof. intros m m' a n v Hfr Hv k Hk. rewrite Hfr by lia. exact (Hv k Hk). Qed.

(* An 8-byte constant cell of as_const, read through AR (the body of PSourceMeta's asrc_meta_ptr_of_AR). *)
Lemma const8_of_AR : forall ly S W mem md a v, AR tsegs B ly S W mem md ->
  In (z8 (ANum a) v) (as_const B ly) -> val_mem tsegs (rd W mem) a 8 v.
Proof.
intros ly S W mem md a v HAR Hin k Hk.
pose proof (am_const _ _ _ _ (proj1 HAR)) as HC.
pose proof (proj1 (Forall_forall _ _) HC _ Hin) as Hc. unfold z8, c8, cell_holds in Hc. cbn [c_at c_w c_val aeval] in Hc.
specialize (Hc k Hk). unfold aview in Hc.
destruct (mbyte tsegs (mrestrict (w_H W) mem) (a + Z.of_nat k)) as [b|] eqn:E; [|discriminate Hc]. cbn in Hc.
injection Hc as Hc. f_equal. apply bv_eq. rewrite Hc, Z_to_bv_unsigned. symmetry.
change (YO0f.le_byte v 8 k) with (YG0f.le_byte v 8 k). unfold YG0f.le_byte.
unfold bv_wrap. change (bv_modulus 8) with 256%Z. apply Z.mod_small. apply Z.mod_pos_bound. lia.
Qed.

(* 0x103a0 is an owned-static row, so arodata_okS does not reach it; the const list does. *)
Lemma in_const_103a0 : forall ly, In (z8 (ANum (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0xc0)%Z)) 0xafffff00000fffff) (as_const B ly).
Proof.
intros ly. rewrite (YF0m.ts_const B TB ly). unfold YF0m.Tfib_const. apply in_or_app. right. apply in_or_app. left.
unfold YF0m.Tfib_const_abs. cbn [In]. repeat (first [left; reflexivity | right]).
Qed.

Lemma cells_of_AR : forall ly S W mem md, AR tsegs B ly S W mem md -> YE2h.cells_hold (rd W mem) YE2f.if_cells.
Proof.
intros ly S W mem md HA.
assert (I1 : val_mem tsegs (rd W mem) PCAP_GOT_FFLUSH 8 PCAP_REAL_FFLUSH).
{ apply (const8_of_AR ly S W mem md _ _ HA).
  exact (asil_icells _ _ _ _ ASILI ly (PCAP_GOT_FFLUSH, PCAP_REAL_FFLUSH) ltac:(cbn; right; left; reflexivity)). }
assert (I2 : val_mem tsegs (rd W mem) PCAP_GOT_FCLOSE 8 PCAP_REAL_FCLOSE).
{ apply (const8_of_AR ly S W mem md _ _ HA).
  exact (asil_icells _ _ _ _ ASILI ly (PCAP_GOT_FCLOSE, PCAP_REAL_FCLOSE) ltac:(cbn; left; reflexivity)). }
pose proof (asrc_meta_ptr_of_AR SK tsegs B pcap_KS ASILI ly S W mem md HA) as IP.
pose proof (const8_of_AR ly S W mem md _ _ HA (in_const_103a0 ly)) as I3.
unfold YE2h.cells_hold, YE2f.if_cells, YE2f.A_META_PTR, YE2f.A_META_MEM.
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]];
  cbn [fst snd]; (split; [lia|]); (split; [lia|]).
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd];
    (split; [|split; cbn; lia]).
  + exact I1.
  + exact I2.
- apply Forall_cons; [|apply Forall_nil]; cbn [fst snd]. split; [exact IP | split; cbn; lia].
- apply Forall_cons; [|apply Forall_nil]; cbn [fst snd]. split; [exact I3 | split; cbn; lia].
Qed.

Lemma wffu_ro_chunks_unowned :
  forallb (fun c => forallb (fun r => (fst r + snd r <=? YP09.c_off c) || (YP09.c_off c + c_len c <=? fst r))
    YF0m.Tfib_owned_static) YE3i.img_ro_chunks = true.
Proof. vm_compute. reflexivity. Qed.

(* ro_img from a view that reads the rom on every unowned byte of the read-only range (the body of the
   donor's ffc_ro_img_of_arodata, cgif lib/A/AE24.v:36, with the premise abstracted). *)
Lemma ro_img_of_rom : forall (H : word -> bool) m,
  (forall a, YE3i.IMG_RO_LO <= a < YE3i.IMG_RO_HI -> ~ Exists (in_zr a) YF0m.Tfib_owned_static ->
     aview tsegs H m a = option_map (fun b : byte => bv_unsigned b) (seg_rom tsegs (Z_to_bv 64 a))) ->
  YE3i.ro_img (mrestrict H m).
Proof.
intros H m HRO E. unfold YE3i.img_ro_region.
split; [cbn; unfold YE3i.IMG_RO_LO; lia|]. split; [cbn; unfold YE3i.IMG_RO_HI; lia|]. split; [intros o Ho; cbn in Ho; lia|].
cbn [YP09.r_chunks YP09.r_base base_val]. apply Forall_forall. intros c Hc i Hi.
pose proof (proj1 (Forall_forall _ _) YE3i.img_ro_chunks_inside c Hc) as (Hlo & Hhi & n & Hv).
pose proof (proj1 (forallb_forall _ _) wffu_ro_chunks_unowned c Hc) as Hown. cbn beta in Hown.
pose proof (proj1 (forallb_forall _ _) YE3i.img_ro_bytes_ok c Hc) as Hz. cbn beta in Hz.
destruct c as [co cv]. cbn [YP09.c_off YP09.c_val] in Hv. subst cv. cbn [YP09.c_off YP09.c_val c_len cv_len] in *. rewrite !Z.add_0_l.
pose proof (zallb_sound _ _ _ (co + i) Hz ltac:(lia)) as Hb.
unfold img_byte_ok, img_byte in Hb.
assert (Hns : ~ Exists (in_zr (co + i)) YF0m.Tfib_owned_static).
{ intros HX. apply Exists_exists in HX as (r & Hr & [Hin1 Hin2]). rewrite forallb_forall in Hown.
  specialize (Hown r Hr). cbn beta in Hown. apply Bool.orb_prop in Hown. destruct Hown as [Ho|Ho]; apply Z.leb_le in Ho; lia. }
pose proof (HRO (co + i) ltac:(lia) Hns) as Hrd. unfold aview in Hrd.
destruct (seg_rom tsegs (Z_to_bv 64 (co + i))) as [b|] eqn:Eb; [|discriminate Hb].
exists b. split; [cbn [cbyte]; unfold img_byte; exact Eb|].
destruct (mbyte tsegs (mrestrict H m) (co + i)) as [b'|] eqn:Em; [|discriminate Hrd]. cbn in Hrd. injection Hrd as Hrd.
f_equal. apply bv_eq. exact Hrd.
Qed.

(* A return address that passes ret_ok is even (jalr clears bit 0). *)
Lemma ret_ok_even : forall k : word, YK0s.ret_ok k -> bv_unsigned k mod 2 = 0.
Proof.
intros k Hk. unfold YK0s.ret_ok, v_jalr, jalr_tgtZ in Hk. rewrite <- Hk.
rewrite Z.add_0_r, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
set (x := Z.land (bv_unsigned k) (-2)).
assert (Hx : x mod 2 = 0).
{ unfold x. rewrite Zmod_odd, <- Z.bit0_odd, Z.land_spec. destruct (Z.testbit (bv_unsigned k) 0); reflexivity. }
rewrite (Z.mod_eq x (2 ^ 64)) by lia.
replace (x - 2 ^ 64 * (x / 2 ^ 64)) with (x + (- (2 ^ 63 * (x / 2 ^ 64))) * 2) by lia.
rewrite Z_mod_plus_full. exact Hx.
Qed.

(* The unbuffered stream survives any change that keeps the FILE block, the buffer and the environment. *)
Lemma src_unbuf_tr : forall m m' f b C p, asource_unbuffered tsegs pcap_KS m f b C p ->
  (forall a, f <= a < f + SRC_FILE_BLOCK -> mbyte tsegs m' a = mbyte tsegs m a) ->
  (forall a, b <= a < b + Z.of_nat (length C) -> mbyte tsegs m' a = mbyte tsegs m a) ->
  (forall a, asrc_env_addr pcap_KS a -> mbyte tsegs m' a = mbyte tsegs m a) ->
  asource_unbuffered tsegs pcap_KS m' f b C p.
Proof.
intros m m' f b C p [HA HW] HF Hb He. split.
- eapply asource_at_tr; [exact HA | exact HF | exact Hb | exact He].
- destruct HW as [(HW0 & H8 & H16) | (i & Hi0 & Hi1 & H8 & H16 & HG)].
  + left. split; [exact HW0|]. unfold SRC_FILE_BLOCK in HF.
    split; (eapply vmI; [|eassumption]); intros x Hx; simpl Z.of_nat in Hx; apply HF; lia.
  + right. exists i. split; [exact Hi0|]. split; [exact Hi1|]. unfold SRC_FILE_BLOCK, SRC_BUF_OFF in *.
    split; [eapply vmI; [|exact H8]; intros x Hx; simpl Z.of_nat in Hx; apply HF; lia|].
    split; [eapply vmI; [|exact H16]; intros x Hx; simpl Z.of_nat in Hx; apply HF; lia|].
    eapply garr8_frame; [exact HG|]. intros a Ha. cbn [length Z.of_nat] in Ha. lia.
Qed.

Theorem pcapu_afflush_source_spec_icpt : forall rlo rhi, afflush_source_spec SK tsegs B pcap_KS PFFLUSH_ICPT_U rlo rhi.
Proof.
intros rlo rhi W ly S regs mem md ch f b M C p HPRE G10 HRO HMI HSRC Hblk Hbd.
unfold PFFLUSH_OWN_STK in HPRE, Hbd.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWSI ly S W mem md f SRC_FILE_BLOCK HAR Hblk) as (Hf16 & Hf0 & Hfceil & _).
change (req_size SRC_FILE_BLOCK) with SRC_FILE_BLOCK in Hfceil. unfold SRC_FILE_BLOCK in Hfceil.
pose proof HSRC as (Wn & cpos & fl & mdv & HX). cbv zeta in HX.
destruct HX as (Hp0 & Hpc & Hcn & Hn63 & Hbw & Hcp & HWd & Hbok & HC & HST & HWIN & HFL & HFL24 & HMD & HCK &
  HENV & HHD & Hfnz).
destruct HST as (S24 & S64 & S72 & S80 & S88 & S96 & Sc8 & Sc16 & Sc24 & Sc32 & S152 & S32 & S40 & S48 & S56 &
  S104 & S112 & S168 & S120 & S140 & S144 & Sf0 & Sf16 & Sb0 & Sdisj).
unfold SRC_FILE_BLOCK in Sdisj.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_stk_ceil ly HLY) as Hsc.
(* the meta region: above the image, below the stack *)
pose proof HMI as (HX & HMimg & HMptr & HMmem & HM0 & HM47 & HMal & HMZ).
assert (HMlo : YF0x.TFIB_IMG_END <= M).
{ assert (HIE : YF0x.TFIB_IMG_END = (symaddr ImgPages.AsanUbsan.top)) by reflexivity. rewrite HIE.
  assert (Hin : in_img tsegs ((symaddr ImgPages.AsanUbsan.top) - 1)) by (exists AsanUbsan.AsanUbsan_segment_003; split; [do 3 right; left; reflexivity | cbn; lia]).
  pose proof (HMimg _ Hin) as HM1. lia. }
assert (HMhi : M + AMETA_SIZE <= spZ regs - 256).
{ pose proof (lo_extra ly HLY) as (_ & HEX & _). pose proof (proj1 (Forall_forall _ _) HEX _ HX) as (_ & _ & _ & HMc & _).
  cbn [fst snd] in HMc. lia. }
(* ---- the interceptor front: 0x41618 -> 0x466e4 -> TryAsanInitFromRtl -> the jalr to REAL(fflush) ---- *)
unfold afflush_source_spec. change PFFLUSH_ICPT_U with YE2f.IF_ENTRY.
eapply SRr_bind.
{ apply (YE2f.iflush_front B LAWSI TB ly S W regs mem md f HAR Hal16).
  - unfold YE2f.IF_WIN. lia.
  - exact Hshi.
  - intros a Ha. apply Hpres. unfold YE2f.IF_WIN in Ha. lia.
  - exact G10.
  - lia.
  - lia.
  - exact Hf16.
  - exact (cells_of_AR ly S W mem md HAR). }
intros W1 c1 _ (-> & regs1 & mem1 & md1 & -> & MF1 & HAR1 & Q10 & Q1 & Q2 & Q8 & QK & QS & AV1 & PRS1 & PM1).
unfold YE2f.IF_WIN, YE2f.IF_FRAME in *.
assert (R1sp : spZ regs1 = spZ regs - 80).
{ unfold spZ at 1. rewrite Q2. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
assert (FR1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 96 <= a < spZ regs) ->
  mbyte tsegs (rd W mem1) a = mbyte tsegs (rd W mem) a).
{ intros a Ha Hn. apply YE01.mbyte_kept_of_aview. exact (AV1 a Ha Hn). }
pose proof (ajournal_init tsegs B 1840 (asource_fp f) ly S W regs mem md ch HPRE) as HJ0.
assert (HJ1 : ajournal tsegs B 1840 (spZ regs) (asource_fp f) ly S W mem md [] ly S W mem1 md1 0).
{ eapply (ajournal_after_write tsegs B LAWSI wffu_ausegs_low 1840 (spZ regs) (asource_fp f) ly S W mem md [] ly S W mem md 0
    mem1 md1 (fun a => spZ regs - 96 <= a < spZ regs) S [] HJ0).
  - intros a Ha Hn. cbv beta in Hn. exact (AV1 a Ha Hn).
  - exact PM1.
  - exact MF1.
  - intros a Ha. cbv beta in Ha. left. left. lia.
  - exact HAR1.
  - reflexivity.
  - reflexivity.
  - lia.
  - reflexivity.
  - exact HQT. }
(* ---- REAL(fflush) = musl fflush at 0x8e308, budget 1840 - 80 ---- *)
eapply SRr_bind.
{ change YE2f.IF_REAL with PFFLUSH_MUSL_U.
  apply (wffu_musl SK tsegs B pcap_KS wffu_ausegs_low wffu_ausegs_wx wffu_tbl_ok ASILI MSEEKI eq_refl 1760 ltac:(lia) 0 0
    W ly S regs1 mem1 md1 [] f b M C p).
  - eapply (afn_pre_at tsegs B 1840 (spZ regs) (asource_fp f) ly S W mem md [] ly S W mem1 md1 0 regs1 1760 (-80) [] HJ1).
    + rewrite R1sp. lia.
    + reflexivity.
    + lia.
    + lia.
    + lia.
    + rewrite Q1. apply YE2y.ret_ok_lit; unfold YE2f.IF_RET; [lia | reflexivity].
    + unfold raZ. rewrite Q1. unfold w64. rewrite unsigned_lit_small; unfold YE2f.IF_RET; lia.
    + exact (eq_trans (QK 3 ltac:(unfold YE2f.KEPTF; cbn; lia)) Hgp).
    + exact (eq_trans (QK 4 ltac:(unfold YE2f.KEPTF; cbn; lia)) Htp).
    + left. split; [left|reflexivity]. unfold s0Z. rewrite Q8. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - exact Q10.
  - intros a Ha Hown Herr. destruct Ha as [Hseg | Hr]; [|lia].
    assert (Hi : in_img tsegs a) by (destruct Hseg as (s & Hs & _ & Hb); exists s; split; [exact Hs | exact Hb]).
    pose proof (wffu_ausegs_low a Hi) as Hlow.
    rewrite (AV1 a ltac:(lia) ltac:(lia)). exact (HRO a (or_introl Hseg) Hown Herr).
  - eapply (asrc_meta_inv_kept SK tsegs B pcap_KS ASILI); [exact HJ1 | exact HMI].
  - eapply asource_at_tr; [exact HSRC | | |].
    + intros a Ha. apply FR1; unfold SRC_FILE_BLOCK in Ha; lia.
    + intros a Ha. apply FR1; lia.
    + intros a Ha. destruct (asil_env _ _ _ _ ASILI a Ha) as (Hi & _). pose proof (wffu_ausegs_low a Hi). apply FR1; lia.
  - exact Hblk.
  - rewrite R1sp. lia. }
intros W2 c2 _ Hpost. destruct Hpost as (regs2 & mem2 & md2 & -> & HJm & HPm & H10m & HUm & HCKm & Hfdm & Hfsm).
rewrite R1sp in HJm.
pose proof (wffu_aj_sub_tok tsegs B LAWSI wffu_ausegs_low 1840 (spZ regs) (asource_fp f) ly S W mem md [] ly S W
  mem1 md1 0 1760 (spZ regs - 80) (asource_fp f) [] ly S W2 mem2 md2 0 HJ1 HJm ltac:(lia) ltac:(lia)
  ltac:(intros a Ha; left; exact Ha)) as HJ2.
cbn [app] in HJ2. change (0 + 0) with 0 in HJ2.
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & F3 & F4 & _ & PRS2 & _).
pose proof HJm as (_ & _ & _ & _ & _ & _ & _ & _ & F1m & _).
assert (P2 : getr regs2 2 = getr regs1 2) by exact (HPm 2 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs2 8 = getr regs1 8) by exact (HPm 8 ltac:(unfold acallee_saved; lia)).
assert (Rsp2 : spZ regs2 = spZ regs - 80) by (unfold spZ at 1; rewrite P2; exact R1sp).
assert (SVra : val_mem tsegs (rd W2 mem2) (spZ regs2 + 72) 8 (bv_unsigned (getr regs 1))).
{ rewrite Rsp2. replace (spZ regs - 80 + 72) with (spZ regs + -8) by lia.
  eapply vmI; [|exact (QS 0%nat 1 (-8) eq_refl)].
  intros x Hx. simpl Z.of_nat in Hx. apply YE01.mbyte_kept_of_aview. apply F1m; lia. }
assert (SV8 : val_mem tsegs (rd W2 mem2) (spZ regs2 + 64) 8 (bv_unsigned (getr regs 8))).
{ rewrite Rsp2. replace (spZ regs - 80 + 64) with (spZ regs + -16) by lia.
  eapply vmI; [|exact (QS 1%nat 8 (-16) eq_refl)].
  intros x Hx. simpl Z.of_nat in Hx. apply YE01.mbyte_kept_of_aview. apply F1m; lia. }
assert (SV9 : val_mem tsegs (rd W2 mem2) (spZ regs2 + 56) 8 (bv_unsigned (getr regs 9))).
{ rewrite Rsp2. replace (spZ regs - 80 + 56) with (spZ regs + -24) by lia.
  eapply vmI; [|exact (QS 2%nat 9 (-24) eq_refl)].
  intros x Hx. simpl Z.of_nat in Hx. apply YE01.mbyte_kept_of_aview. apply F1m; lia. }
assert (HIMG2 : YE3i.ro_img (rd W2 mem2)).
{ apply ro_img_of_rom. intros a Ha Hns.
  assert (Hseg : exists s, In s tsegs /\ seg_writable s = false /\
                   Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s)).
  { exists AsanUbsan.AsanUbsan_segment_000. split; [left; reflexivity|]. split; [reflexivity|].
    unfold YE3i.IMG_RO_LO, YE3i.IMG_RO_HI in Ha. cbn. lia. }
  assert (Hi : in_img tsegs a) by (destruct Hseg as (s & Hs & _ & Hb); exists s; split; [exact Hs | exact Hb]).
  assert (Hns' : ~ Exists (in_zr a) (as_owned_static B)) by (rewrite (YF0m.ts_owned B TB); exact Hns).
  assert (Herr : ~ (as_errno B <= a < as_errno B + 4)).
  { rewrite (YF0m.ts_errno B TB). unfold YF0m.TFIB_ERRNO, YE3i.IMG_RO_LO, YE3i.IMG_RO_HI in *. lia. }
  rewrite (F3 a Hi Hns' Herr).
  - exact (HRO a (or_introl Hseg) Hns' Herr).
  - apply fp_spares_below. rewrite <- (asil_head _ _ _ _ ASILI). unfold as_ofl_head, pcap_KS, PCAP_OFL_LOCK. cbn.
    unfold YE3i.IMG_RO_LO, YE3i.IMG_RO_HI in Ha. lia. }
assert (HMI2 : asrc_meta_inv tsegs pcap_KS ly (rd W2 mem2) M)
  by (eapply (asrc_meta_inv_kept SK tsegs B pcap_KS ASILI); [exact HJ2 | exact HMI]).
destruct HMI2 as (_ & _ & _ & HMmem2 & _ & _ & _ & HMZ2).
(* ---- the interceptor tail: 0x46710 -> AddrHashMap acquire 0x47b7c / release 0x4839c -> ret ---- *)
rewrite Q1. change (mkCfg (mkst regs2 (w64 YE2f.IF_RET) mem2 (seg_rom tsegs)) md2) with (cfg_at tsegs YE2f.IF_RET regs2 mem2 md2).
eapply SRr_bind.
{ apply (YE2f.iflush_tail B LAWSI ly S W2 regs2 mem2 md2 f M (bv_unsigned (getr regs 1)) (bv_unsigned (getr regs 8))
    (bv_unsigned (getr regs 9)) HAR2).
  - rewrite Rsp2. replace (spZ regs - 80) with (spZ regs + (-5) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16.
  - rewrite Rsp2. unfold YE2f.IF_TSTK. lia.
  - rewrite Rsp2. unfold YE2f.IF_FRAME. lia.
  - intros a Ha. rewrite Rsp2 in Ha. unfold YE2f.IF_TSTK in Ha. apply PRS2. lia.
  - rewrite P8. exact Q8.
  - lia.
  - lia.
  - exact Hf16.
  - exact SVra.
  - exact SV8.
  - exact SV9.
  - apply u64_range.
  - apply u64_range.
  - apply u64_range.
  - exact (ret_ok_even _ Hra).
  - exact (cells_of_AR ly S W2 mem2 md2 HAR2).
  - exact HIMG2.
  - unfold YE2f.meta_pre. split; [exact HMmem2|]. split; [exact HMZ2|]. split; [exact HMlo|]. split; [exact HMal|].
    rewrite Rsp2. unfold YE2f.IF_TSTK. lia. }
intros W3 c3 _ (-> & regs4 & mem4 & md4 & -> & MF4 & HAR4 & T10 & T1 & T2 & T8 & T9 & TK & AV4 & PRS4 & PM4).
rewrite Rsp2 in AV4, PRS4, T2. unfold YE2f.IF_TSTK, YE2f.IF_FRAME in *.
assert (FR4 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 80 - 176 <= a < spZ regs - 80 + 56) ->
  mbyte tsegs (rd W2 mem4) a = mbyte tsegs (rd W2 mem2) a).
{ intros a Ha Hn. apply YE01.mbyte_kept_of_aview. exact (AV4 a Ha Hn). }
apply SRr_ret.
exists regs4, mem4, md4.
split; [unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write tsegs B LAWSI wffu_ausegs_low 1840 (spZ regs) (asource_fp f) ly S W mem md [] ly S W2 mem2 md2 0
    mem4 md4 (fun a => spZ regs - 256 <= a < spZ regs - 24) S [] HJ2).
  - intros a Ha Hn. cbv beta in Hn. apply AV4; [exact Ha | lia].
  - exact PM4.
  - exact MF4.
  - intros a Ha. cbv beta in Ha. left. left. lia.
  - exact HAR4.
  - reflexivity.
  - reflexivity.
  - lia.
  - reflexivity.
  - exact HQT. }
split.
{ intros r Hr.
  destruct (Z.eq_dec r 2) as [->|N2]; [| destruct (Z.eq_dec r 8) as [->|N8]; [| destruct (Z.eq_dec r 9) as [->|N9]]].
  - etransitivity; [exact T2|]. unfold w64. replace (spZ regs - 80 + 80) with (spZ regs) by lia. unfold spZ.
    apply Z_to_bv_bv_unsigned.
  - etransitivity; [exact T8|]. unfold w64. apply Z_to_bv_bv_unsigned.
  - etransitivity; [exact T9|]. unfold w64. apply Z_to_bv_bv_unsigned.
  - unfold acallee_saved in Hr.
    etransitivity; [exact (TK r ltac:(unfold YE2f.KEPTT; cbn; lia))|].
    etransitivity; [exact (HPm r ltac:(unfold acallee_saved; lia))|].
    exact (QK r ltac:(unfold YE2f.KEPTF; cbn; lia)). }
split; [rewrite T10; exact H10m|].
split.
{ eapply src_unbuf_tr; [exact HUm | | |].
  - intros a Ha. apply FR4; unfold SRC_FILE_BLOCK in Ha; lia.
  - intros a Ha. apply FR4; lia.
  - intros a Ha. destruct (asil_env _ _ _ _ ASILI a Ha) as (Hi & _). pose proof (wffu_ausegs_low a Hi). apply FR4; lia. }
split.
{ eapply vmI; [|exact HCKm]. intros x Hx. simpl Z.of_nat in Hx. unfold SRC_COOKIE_OFF in Hx. apply FR4; lia. }
split.
- rewrite (same_but_materialized_wvb _ _ MF4), (proj1 (wvb_io _ _ _)), Hfdm, (same_but_materialized_wvb _ _ MF1),
    (proj1 (wvb_io _ _ _)). reflexivity.
- rewrite (same_but_materialized_wvb _ _ MF4), (proj2 (wvb_io _ _ _)), Hfsm, (same_but_materialized_wvb _ _ MF1),
    (proj2 (wvb_io _ _ _)). reflexivity.
Qed.

End I.

(* The two entries pfflush_entry_ok admits, on the asan-ubsan image with its own symbol record KS_U. *)
Theorem pcapu_afflush_source_spec {fx : YK11.FPState} {rc : YM05.RunCeil} :
  forall (SK : YI16.sink_head) (B : asyms),
  YF0m.PcapSyms B -> asource_img_laws SK YB1v.tfibsegs B pcap_KS -> amseek_rewind_spec SK YB1v.tfibsegs B pcap_KS PMSEEK_U ->
  forall pc rlo rhi, pfflush_entry_ok PFFLUSH_ICPT_U PFFLUSH_MUSL_U pc -> afflush_source_spec SK YB1v.tfibsegs B pcap_KS pc rlo rhi.
Proof.
intros SK B TB ASIL MSEEK pc rlo rhi [-> | ->].
- exact (pcapu_afflush_source_spec_icpt SK B TB ASIL MSEEK rlo rhi).
- exact (pcapu_afflush_source_spec_musl SK B ASIL MSEEK rlo rhi).
Qed.

Check afflush_source_spec_musl.
Check pcapu_afflush_source_spec_icpt.
Check pcapu_afflush_source_spec.
Print Assumptions afflush_source_spec_musl.
Print Assumptions pcapu_afflush_source_spec_musl_K.
Print Assumptions pcapu_afflush_source_spec_musl.
Print Assumptions pcapu_afflush_source_spec_icpt.
Print Assumptions pcapu_afflush_source_spec.
