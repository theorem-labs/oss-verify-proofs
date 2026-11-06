(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B's walk of pcap_source_open in the asan-ubsan instance of fuzz_pcap
   (libreac v1.9.0; pin fuzz_pcap.asan-ubsan, sha256 9e66f771f22a...; function at 0x811e0 =
   BASE + AF_pcap_source_open, AF = 0xa58), proving lib/A's image-generic contract tpcap_source_open_specX
   (lib/A/Prog/PcapSourceOpenDefs.v) at SEGS = pa_segs, rlo / rhi = pa_relro_lo / pa_relro_hi,
   apath / alen / afile = VAL (A_OBJ 3) / VAL (A_OBJ 4) / VAL (A_OBJ 2) (0x20d00 "<fuzz-input>", g_file_len
   0x5d3e40, g_file 0x5d3e60), with FM_RA and roimg as parameters. At ossv/recipes 25e3d17bdb50 (2026-10-29), there was no released proof of this function at
   this image (rule 24 lookup, a Theorem Labs lane, 22:35Z): the v1.8 ubsan proof (lib/U/Prog/pcap_source_open.v at
   origin/ossv/recipes c8557374ad2e) serves only as the template for the UBSan guards.

   The code. Up to the fopen call it is lib/A's ASan code byte for byte at
   other pcs (asan 0x8145c.. = asan-ubsan 0x811e0..): the prologue saves ra, s0 .. s9 (0x811e0..0x81210) and
   realigns s1 = sp = (sp - 96) & -32 (0x81218); the use-after-return flag is read through the GOT (0x81228
   auipc / 0x8122c ld, listing object 0 = 0x99750) from the runtime cell at 0x81234 (object 16 = 0xa17c0): the
   walk takes it as 1 (the kit's AR_const_law through al_const, with uar_cell_regionP (A_OBJ 16) holding SLit 1;
   the pin's file holds 0 and the runtime sets 1 at init), so 0x81240 `beqz a2` is not taken;
   __asan_stack_malloc_1(0x60) at 0x81248 returns the class-1 frame F (aj_stack_malloc_atS, YC85.v:292), whose
   two caller premises are discharged at op_to_call's frame request: count_cid 1 (frames Sc) < fs_frames 1 from
   op_pre's length (frames Sc) <= 7 through count_cid_le_length and 8 <= fs_frames 1, and the apath premise by
   op_SMP (stack_malloc_progressP from lib/Reusable/YG05.v:70, as cgif_file_fuzzer lib/A/ACed.v:129-130), so
   F >= 4096, 0x8125c `bnez s2` is taken and the machine-frame arm 0x81260..0x81278 is dead; then *(s1) = F
   (0x8127c), the header (0x41b58ab3, objects 10 and 11; 0x812a4..0x812ac), the twelve shadow bytes
   (0x812b8..0x812e4: 0xf1 x4, 0xf8 x3, 0xf3 x5), the mode literal "rb" (object 12, 0x812e8 / 0x812ec; HMODE)
   and the call of libreac_fuzz_fopen (0x812f4) through cl_callS (YC85.v:383) with FOPEN as the callee.

   The cut. This file walks the head: entry -> op_to_call (a Qed checkpoint at the call, op_at_call) ->
   head_to_fopen, which makes the call and establishes PcapSourceOpenPhF.v's op_fopen_ret at the return
   0x812f8. From there PcapSourceOpenPhM.v (op_from_fopen) walks to the two cuts of PcapSourceOpenPh.v and
   PcapSourceOpenB.v (op_from_null / op_from_read) to the return; pb_pcap_source_openX composes the three.
   The three UBSan guards are therefore decided outside this file, at these pcs and against these template lines:
   in PcapSourceOpenPhM.v 0x812f8 `beqz s3` (ps = 0, not taken: ps >= 4096 from op_pre's frame bounds; template
   :114 / :334, premise :93 / :290) and 0x81300 / 0x81304 `andi a0,s3,7; bnez a0` (ps mod 8 <> 0, not taken:
   op_pre's ps mod 8 = 0; template :115 / :335); in PcapSourceOpenB.v 0x81390 / 0x81394 `addi a0,zero,-3;
   bgeu s4,a0` (F + 32 >=u 2^64 - 3, not taken: F + 128 <= alloc_ceiling < 2^47; template :408-412, premise
   :291 and :295-299); all three
   go to the `unimp` at 0x8153c, and every ASan report path 0x81540..0x815b4 is dead because ps's 24 bytes are
   addressable and ps mod 8 = 0. In the head, op_at_call carries what those walks need: ps unwritten and still
   range_addressable, and op_fopen_ret's FILE-block footprint fact for the fclose of the tail.

   The callee hypotheses, used at this image as Section hypotheses: FOPEN : tlibreac_fuzz_fopen_specX
   (lib/A/Prog/PcapFuzzFopenDefs.v), AFREAD : afread_spec (lib/A/Stdio/PFreadISpec.v:138), AFCLOSE :
   afclose_source_spec (lib/A/Stdio/PFclose.v:209), ASM1 : astack_malloc_realizes (lib/Reusable/YG0d.v:285),
   ASF : astack_free_law (lib/Reusable/YG0d.v:301) and FFL : frame_flag_lawP (lib/Reusable/YCbq.v:797), the meter laws MLAW / MLAWF /
   FM, ASIL : asource_img_laws, and the kit's LAWS / TL / TLF / ML. Four instance obligations beyond the kit:
   ROK (roimg reads only image bytes outside the runtime's statics, errno and the open-file list head; applied at
   the fopen call to carry roimg from the entry memory across the prologue and the frame setup), HPATH (the path
   literal's shadow, as a law of every AR state: the frame request's kept clauses do not keep a global's shadow,
   YG0n.v:241 makes it aowned; discharged by the instance through AR_zshadow_law, YG0d.v:435-438), HGX (g_file_len
   and g_file are image bytes outside the runtime's statics and errno; the gx_ok shape of
   lib/A/Prog/PcapEntryDefs.v:366, 395, discharged by the harness), and RO : ro_below_ofl (as
   lib/A/Prog/PcapHarnessTail.v:37). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/PcapSourceOpen.v, with its module paths and module names changed; 477 of its 520 lines of code are new or changed and 1508 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: taken from a working branch d2efa2b83ff without its uncommitted DRAFT_fopen.v (sha256 c5819f1f77c8; internal record): the image facts (segments, read-only image) and the strcmp wrapper's contract are named Section hypotheses; the strcmp window is FO_WIN's ESTACK. *)
(* Modified by Theorem Labs, 2026-10: lib/B twin of lib/A/Prog/PcapFuzzFopen.v (a working branch 25b1e6c030c, narrow FO_WIN; file unchanged since 71180e55168) for fuzz_pcap.asan-ubsan (v1.9.0, pin sha256 9e66f771f22af67aadc8b8ddcd7ee91f46c4c63442c694faaf2375f9c5b79321): the listing, its names, PAImg and the walk kit are lib/B's (PcapSyms, PcapList, PcapAddr, PcapPa, PcapPaLib, PcapFrame, YC1g, YC85); the statement is lib/A/Prog/PcapFuzzFopenDefs.v's tlibreac_fuzz_fopen_specX at this image's instance, not a copy; the image-generic Definitions of the lib/A walk (roimg_low, astrcmp_path_at, FopenImg) are restated here because that file is a walk over the ASan listing and is not Required; every image number is keyed on symbol + offset from each pin's own symtab (libreac_fuzz_fopen+0x0 = 0x80738 on asan, 0x80788 here); the address check at the end is this image's. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* libreac_fuzz_fopen (fuzz_pcap.asan-ubsan v1.9.0, libreac_fuzz_fopen+0x0 = 0x80788, 36 instructions, 144 bytes; the
   same 36 instruction words as the ASan build's but for the low 12 bits of three auipc pairs, +0x20 / +0x50 / +0x5c,
   whose targets are the same symbol + offset on both pins): the contract of the asan-ubsan build's code in cgif_file's
   per-function form, and its walk over the position-abstract listing.
   The function takes a 32-byte frame, saves ra, s0 (the mode) and s1 (the path), calls the strcmp wrapper on the path
   and the "<fuzz-input>" literal (.str+0x0 = 0x20d00), and on equality loads the 8-byte word stored in the global
   g_file_len (g_file_len+0x0 = 0x5d3e40; the input's length n): when n is 0 it returns 0 without any call
   (+0x50 = 0x807d8 `ld a1,0x66c(a0)`, +0x54 = 0x807dc `beqz a1,+0x24` to +0x78 = 0x80800 `li a0,0` ... `ret`), and
   that empty input is the only way it returns 0; otherwise it loads the 8-byte word stored in the global g_file
   (g_file+0x0 = 0x5d3e60; the input buffer's address b), pops its frame and tail-jumps to the fmemopen wrapper
   (+0x74 = 0x807fc `j` to __interceptor_trampoline_fmemopen+0x0 = 0x41614) with a0 = b and a1 = n (the two globals'
   contents, not their addresses) and a2 = the mode, so the wrapper returns to this function's caller with the new
   stream. The NULL-path branch (+0x18 = 0x807a0) and the strcmp-unequal branch (+0x2c = 0x807b4, then the tail jump
   at +0x48 to __interceptor_trampoline_fopen+0x0 = 0x41610) are not reached: the path is the literal, and strcmp
   returns 0 on it. The function ends in `ret` (+0x8c) and holds no report call and no UBSan trap. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08 YI0s YI16.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0s YC5d PcapImgEnd YImgTop.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaRun PaShadow.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSyms PcapList PcapPa PcapAddr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal PcapBase YC4b.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapPaLib PcapFrame YC1g YC85.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PFmemopenISpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapFuzzFopenDefs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
(* KS_U, this image's stdio instance (a Theorem Labs lane), for the address check at the end only; bound by its full path
   because lib/A/Stdio has a file of the same short name. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Stdio Require PSourceK.
Module KSU := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Stdio.PSourceK.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* The listing's objects this function names (PcapAddr.v): the "<fuzz-input>" literal, g_file_len and g_file. *)
Definition FO_PATH : nat := 3%nat.
Definition FO_LEN : nat := 4%nat.
Definition FO_FILE : nat := 2%nat.
Definition SB_FO : Z := 0x7fff8000.
Definition Bx_FO : sv := SLit SB_FO.
Definition Bspan_FO : Z * Z := (SB_FO, SB_FO + 2 ^ 44 - 1).

(* The symbolic state at the entry: the frame below sp, and the two globals, whose values are the atoms 32 (the
   length) and 33 (the buffer). *)
Definition fo_regions0 : smem :=
[ stack_region 32; obj8_region FO_LEN (SOff 32 0); obj8_region FO_FILE (SOff 33 0) ].
Definition ss_fo0 : sstate :=
mkSS AF_libreac_fuzz_fopen sr_atoms fo_regions0 None (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] []).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section p.
Variable segs : list Segment.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* The read-only-image fact roimg (on this image, a Theorem Labs lane's asan-ubsan ro_img, lib/Reusable/YE3i.v) depends only on the
   image bytes below alloc_ceiling; so the writes of this function and of its strcmp call, all inside FO_WIN, keep
   it. *)
Definition roimg_low (roimg : (word -> option byte) -> Prop) : Prop :=
forall m m' : word -> option byte,
(forall a, 0 <= a < alloc_ceiling -> mbyte segs m' a = mbyte segs m a) -> roimg m -> roimg m'.

Lemma roimg_kept_aview : forall (roimg : (word -> option byte) -> Prop), roimg_low roimg ->
forall (W : world segs) (m m' : word -> option byte) sp0,
(forall x, 0 <= x < 2 ^ 64 -> ~ FO_WIN sp0 x -> aview segs (w_H W) m' x = aview segs (w_H W) m x) ->
alloc_ceiling <= sp0 - 32 - ESTACK ->
roimg (rdW W m) -> roimg (rdW W m').
Proof.
intros roimg HLOW W m m' sp0 HK Hlo. apply HLOW. intros a Ha. exact (mbyte_kept_lo segs W m m' sp0 a HK Hlo Ha).
Qed.

(* The strcmp wrapper's contract at this function's one call: entered at pc with a0 = a1 = x, the address of the
   "<fuzz-input>" literal (12 bytes and the NUL: 13), with the read-only-image fact and the literal addressable in
   ASan's shadow, it returns 0, keeps memory outside [sp - ESTACK, sp), the ASan state AR, the callee-saved
   registers, and makes no event. On the ASan image it is a Theorem Labs lane's astrcmp_lit_realizes B (lib/A/Rt/StrcmpDef.v) at
   its instance; on this image it is the asan-ubsan instance of the same contract, at the listing's strcmp
   trampoline (__interceptor_trampoline_strcmp+0x0 = 0x415b4) and x := .str+0x0 = 0x20d00 (the contract's window is
   the same [sp - ESTACK, sp); a strcmp text that keeps memory only outside [sp - 2 * ESTACK, sp) does not imply
   this post). *)
Definition astrcmp_path_at (B : asyms) (roimg : (word -> option byte) -> Prop) (pc x : Z) : Prop :=
forall ly S (W : world segs) regs mem md,
ecall_pre segs B ly S W regs mem md ->
getr regs 10 = w64 x -> getr regs 11 = w64 x ->
roimg (rdW W mem) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x 13 ->
shadow_hull_vis (aview segs (w_H W) mem) x 13 ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
  c' = cfg_at segs (raZ regs) regs' mem' md' /\
  AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
  getr regs' 10 = w64 0 /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) ->
     aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
End p.

(* The image facts the walk uses, each fixed by fuzz_pcap.asan-ubsan and discharged by the image instance: the two
   globals do not overlap, the source's open-file head is the one ajournal spares, and the stdio cells
   asource_none names lie in the image. None of them names the segments. *)
Record FopenImg (A_GLEN A_GFILE : Z) (K : asource_syms) : Prop := {
fi_sep : A_GLEN + 8 <= A_GFILE \/ A_GFILE + 8 <= A_GLEN;
fi_head : as_ofl_head K = @AOFL_HEAD SK;
fi_kimg : Forall (fun a => 0 <= a /\ a + 16 <= pcap_img_end)
  [as_threaded K; as_need_locks K; as_ofl_lock K; as_mode K; as_rwa K; as_canary K]
}.
(* The record's parameters are inferable from the record argument, so the fields read as  fi_sep FI. *)
Arguments fi_sep {A_GLEN A_GFILE K} _.
Arguments fi_head {A_GLEN A_GFILE K} _.
Arguments fi_kimg {A_GLEN A_GFILE K} _.

Section f.
Context {PI : PAImg pcap_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ pcap_listing PI).
#[local] Abbreviation VAL := (@pa_val _ pcap_listing PI).
#[local] Abbreviation SIGMA := (@pa_sigma _ pcap_listing PI).
#[local] Abbreviation BASE := (@pa_val _ pcap_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Definition A_libreac_fuzz_fopenP : Z := BASE + AF_libreac_fuzz_fopen.
Section h.
Variable B : asyms.
Variable K : asource_syms.
(* The return address of the malloc call inside the C library's fmemopen (afmemopen_spec's ra; on this image the
   lib/B top's value is fmemopen+0x9c = 0x8e7d8, the return of the `jal` at fmemopen+0x98 to
   __interceptor_trampoline_malloc), and the call spines this function may be called under (afmemopen_spec's CTX:
   fmemopen's malloc records the caller's spine, because the tail jump leaves s0 the caller's frame pointer). *)
Variable FM_RA : Z.
Variable CTX : list (list Z).
Variable MT : ameter_ops.
(* The read-only-image fact the statement takes as roimg (the lib/B top instantiates it with a Theorem Labs lane's asan-ubsan
   ro_img, lib/Reusable/YE3i.v), and that it depends only on the bytes below alloc_ceiling (a Theorem Labs lane discharges
   ROIMG_LOW for that ro_img: its region [IMG_RO_LO, IMG_RO_HI) lies below alloc_ceiling and has no writable part,
   YI04.region_ok_transport). *)
Variable roimg : (word -> option byte) -> Prop.
Hypothesis ROIMG_LOW : roimg_low SEGS roimg.
(* The word-constant window afmemopen_spec asks for, and the fact that the read-only-image fact pins it; the lib/B
   top discharges MCONSTS for roimg := YE3i's ro_img at mc_lo := 0x10350, mc_hi := 0x10370 (.rodata+0x70 ..
   .rodata+0x90; .rodata starts at 0x102e0 on both pins and the 32 bytes there are the same on both) and
   SEGS = this image's tfibsegs (a Theorem Labs lane's lib/Reusable/YB1v.v). *)
Variables mc_lo mc_hi : Z.
Hypothesis MCONSTS : forall (W : world SEGS) (mem : word -> option byte), roimg (rdW W mem) ->
  forall a, mc_lo <= a < mc_hi ->
  aview SEGS (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom SEGS (Z_to_bv 64 a)).
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MLAWS : ameter_laws MT.
Hypothesis FI : FopenImg (VAL (A_OBJ FO_LEN)) (VAL (A_OBJ FO_FILE)) K.
(* The strcmp wrapper's contract at the listing's strcmp trampoline and object FO_PATH; the lib/B top discharges it
   from the asan-ubsan instance of a Theorem Labs lane's strcmp contract with SEGS = YB1v's tfibsegs, roimg = YE3i's ro_img,
   pcap_sigma PS___interceptor_trampoline_strcmp = 0x415b4 and pcap_obj FO_PATH = 0x20d00 (fopen_img_tables_B). *)
Hypothesis STRCMP : astrcmp_path_at SEGS B roimg (SIGMA PS___interceptor_trampoline_strcmp) (VAL (A_OBJ FO_PATH)).
Hypothesis AFMEMOPEN : afmemopen_spec SK SEGS B K MT CTX (SIGMA PS___interceptor_trampoline_fmemopen) FM_RA
  mc_lo mc_hi.
Let RUN := paj_run (SK := SK) B LAWS.
Let RET := paj_ret_at (PL := PL_pcap) (PI := PI).
Let BR := paj_branch (PI := PI).
Lemma ew_imgP : forall E a, img_env VAL A_LIM E -> (A_TEXT <= a < A_LIM)%nat -> ew E a = Z_to_bv 64 (VAL a).
Proof. intros E a HE Ha. rewrite <- (HE a Ha). symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma base_obj : forall E i, img_env VAL A_LIM E -> (i < 17)%nat -> base_val E (Some (A_OBJ i)) = VAL (A_OBJ i).
Proof. intros E i HE Hi. cbn [base_val]. apply HE. unfold A_OBJ, A_TEXT, A_LIM. lia. Qed.
(* The call of the strcmp wrapper, as a journal step: the wrapper writes only inside the ESTACK window below
   the caller's sp, and returns 0 on the two equal literals. *)
Lemma aj_strcmp_at : forall W (regsc : bvmap 5 word) memc STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw,
ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
getr regsc 10 = w64 (VAL (A_OBJ FO_PATH)) -> getr regsc 11 = w64 (VAL (A_OBJ FO_PATH)) ->
spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw ->
roimg (rdW W memc) ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (VAL (A_OBJ FO_PATH)) 13 ->
shadow_hull_vis (aview SEGS (w_H W) memc) (VAL (A_OBJ FO_PATH)) 13 ->
SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (SIGMA PS___interceptor_trampoline_strcmp)) memc (seg_rom SEGS)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
  c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
  aregs_preserved regsc regs2 /\ getr regs2 10 = w64 0 /\ same_but_materialized mdc md2 /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - ESTACK <= a < sp0 + o) ->
     aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a) /\
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a)).
Proof.
intros W regsc memc STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw
HJ Ha0 Ha1 Hsp Hal Hneg Hbud Hgp Htp Hra Hraw HRO HRA HHV.
assert (HPRE : ecall_pre SEGS B lyc Sc W regsc memc mdc).
{ eapply (ecall_pre_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k regsc o);
  [ exact HJ | exact Hsp | exact Hal | exact Hneg | exact Hbud | rewrite Hra; exact Hraw | exact Hgp | exact Htp ]. }
eapply SRr_mono.
{ change (mkCfg (mkst regsc (Z_to_bv 64 (SIGMA PS___interceptor_trampoline_strcmp)) memc (seg_rom SEGS)) mdc)
    with (cfg_at SEGS (SIGMA PS___interceptor_trampoline_strcmp) regsc memc mdc).
  exact (STRCMP lyc Sc W regsc memc mdc HPRE Ha0 Ha1 HRO HRA HHV). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP2 & Hsame & Hres & Heff & Hpres2).
rewrite Hsp in Heff.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write SEGS B LAWS pa_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k mem2 md2
    (fun a => sp0 + o - ESTACK <= a < sp0 + o) Sc own HJ).
  - intros a Ha Hna. apply Heff; [exact Ha | exact Hna].
  - exact Hpres2.
  - exact Hsame.
  - intros a Ha. left. left. lia.
  - exact HAR2.
  - reflexivity. - reflexivity. - lia.
  - pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _). exact Hfrs.
  - pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT). exact HQT. }
split; [exact HP2|]. split; [exact Hres|]. split; [exact Hsame|]. split; [exact Heff | exact Hpres2].
Qed.
Lemma fo_entry : forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md ch n b,
afn_pre SEGS B LIBREAC_FUZZ_FOPEN_STK ly S W regs mem md ch ->
val_mem SEGS (rdW W mem) (VAL (A_OBJ FO_LEN)) 8 n -> 0 <= n < 2 ^ 64 ->
val_mem SEGS (rdW W mem) (VAL (A_OBJ FO_FILE)) 8 b -> 0 <= b < 2 ^ 64 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs [Z_to_bv 64 n; Z_to_bv 64 b])) ss_fo0
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_libreac_fuzz_fopen)) mem (seg_rom SEGS))) /\
sh_ok SEGS Bx_FO [] (Eimg (Ereg regs [Z_to_bv 64 n; Z_to_bv 64 b])) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md ch n b HPRE Vn Rn Vb Rb. split; [|constructor].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof (fi_sep FI) as Hsep.
pose proof (pa_obj_img FO_LEN ltac:(unfold FO_LEN; lia)) as Hol.
pose proof (pa_obj_img FO_FILE ltac:(unfold FO_FILE; lia)) as Hof.
unfold pcap_img_end, YImgTop.IMG_TOP, YImgTop.IMG_LO in *.
set (E := Eimg (Ereg regs [Z_to_bv 64 n; Z_to_bv 64 b])).
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 n)
by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs [Z_to_bv 64 n; Z_to_bv 64 b] 0)).
assert (E33 : ew E 33 = Z_to_bv 64 b)
by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs [Z_to_bv 64 n; Z_to_bv 64 b] 1)).
pose proof (base_obj E FO_LEN HEI ltac:(unfold FO_LEN; lia)) as BL.
pose proof (base_obj E FO_FILE HEI ltac:(unfold FO_FILE; lia)) as BF.
rewrite restrict_mkst_fx. unfold ss_fo0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold fo_regions0, stack_region, obj8_region. fold E.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
+ cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. unfold LIBREAC_FUZZ_FOPEN_STK, AFMEMOPEN_STK in *. lia.
+ rewrite BL. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ FO_LEN)) 0 8 (SOff 32 0) n);
[ cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Vn ].
+ rewrite BF. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ FO_FILE)) 0 8 (SOff 33 0) b);
[ cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Vb ].
- apply pairwise_disjoint_of_extents. unfold fo_regions0, stack_region, obj8_region, extent_of_region. fold E.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite BL, BF. cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
unfold LIBREAC_FUZZ_FOPEN_STK, AFMEMOPEN_STK in *. unfold ESTACK in *. repeat split; lia.
- split; [|split; exact I].
cbn [f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E. rewrite Usp.
change (2 ^ 4) with 16. split; [lia|]. split; [exact Hal16 | lia].
Qed.

Ltac preg HS r Hr :=
lazymatch type of HS with
| st_ok ?sg ?Ex ?ssx (restrict ?Hh ?msy) => pose proof (st_ok_restrict_reg sg Hh Ex ssx msy r HS) as Hr
| st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msy) => pose proof (st_ok_pi_restrict_reg Hh Ex ssx msy r HS) as Hr
end;
lazymatch type of Hr with _ = sv_denot _ ?v => let v' := eval vm_compute in v in change v with v' in Hr end;
cbn [ms_regs restrict mkst] in Hr.

Ltac fo_win_tac Usp :=
intros bb wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin];
  [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp in Hrr; unfold FO_WIN, ESTACK; lia|]);
destruct Hin.
Theorem pb_libreac_fuzz_fopenX :
  tlibreac_fuzz_fopen_specX SK SEGS A_libreac_fuzz_fopenP (VAL (A_OBJ FO_PATH)) (VAL (A_OBJ FO_LEN))
    (VAL (A_OBJ FO_FILE)) roimg B K MT FM_RA CTX.
Proof.
unfold tlibreac_fuzz_fopen_specX.
intros ly S W regs mem md ch n b C HPRE HCTX H10 H11 HRO HRA HHV Vn Vb Rb HNONE HnC Hn26 HBLK Hev Hlive HMO HU1 HU2.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (Rn : 0 <= n < 2 ^ 64) by (rewrite HnC; lia).
destruct (fo_entry ly S W regs mem md ch n b HPRE Vn Rn Vb Rb) as [HS SHOK].
pose proof (ajournal_init SEGS B LIBREAC_FUZZ_FOPEN_STK afmemopen_fp ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : LIBREAC_FUZZ_FOPEN_STK = 18624) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof (pa_obj_img FO_PATH ltac:(unfold FO_PATH; lia)) as Hop.
pose proof (pa_obj_img FO_LEN ltac:(unfold FO_LEN; lia)) as Hol.
pose proof (pa_obj_img FO_FILE ltac:(unfold FO_FILE; lia)) as Hof.
unfold pcap_img_end, YImgTop.IMG_TOP, YImgTop.IMG_LO in Hop, Hol, Hof.
assert (HLO : alloc_ceiling <= spZ regs - 32 - ESTACK) by lia.
remember (Eimg (Ereg regs [Z_to_bv 64 n; Z_to_bv 64 b])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E10 : ew E 10 = getr regs 10) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (E11 : ew E 11 = getr regs 11) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 11 11%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 n) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs [Z_to_bv 64 n; Z_to_bv 64 b] 0)).
assert (E33 : ew E 33 = Z_to_bv 64 b) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs [Z_to_bv 64 n; Z_to_bv 64 b] 1)).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 n; Z_to_bv 64 b]) E) by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear HE.
unfold cfg_at, A_libreac_fuzz_fopenP.
change (w64 (BASE + AF_libreac_fuzz_fopen)) with (Z_to_bv 64 (BASE + AF_libreac_fuzz_fopen)).
(* +0x0 .. +0x18 (0x80788 .. 0x807a0): the frame, the saves of ra / s0 / s1, and the test of the path against NULL. *)
paj_run_tok RUN HS HJ SHOK Bspan_FO; [awr_ok_tac; exact Usp |].
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (FO_WIN (spZ regs)) HFr ltac:(fo_win_tac Usp)) as KF1.
clear HF HFr HG.
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
  assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ FO_WIN (spZ regs) a ->
                aview SEGS (w_H W) (ms_mem msx) a = aview SEGS (w_H W) mem a)
  by (intros a Ha Hna; exact (KF1 a Ha Hna)) end.
clear KF1.
psrr_branch_tok RUN BR HS SHOK Bspan_FO.
- (* +0x18 (0x807a0) taken: the path would be NULL, but it is the image's literal. *)
  exfalso. rewrite branch_eq_U in Hc.
  assert (U10 : U E (SOff 10 0) = VAL (A_OBJ FO_PATH))
    by (apply U_atom; [rewrite E10, H10; reflexivity | pose proof (pa_val_range (A_OBJ FO_PATH)); lia]).
  assert (U0 : U E (SLit 0) = 0) by reflexivity.
  rewrite U10, U0 in Hc. apply Z.eqb_eq in Hc. lia.
- (* +0x1c .. +0x28 (0x807a4 .. 0x807b0): the literal's address and the call of the strcmp wrapper. *)
  clear Hc.
  paj_run_tok RUN HS HJ SHOK Bspan_FO; [awr_ok_tac; exact Usp |].
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (FO_WIN (spZ regs)) HFr ltac:(fo_win_tac Usp)) as KF2.
  clear HF HFr HG.
  lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (UN2 : forall a, 0 <= a < 2 ^ 64 -> ~ FO_WIN (spZ regs) a ->
                  aview SEGS (w_H W) (ms_mem msx) a = aview SEGS (w_H W) mem a)
    by (intros a Ha Hna; rewrite (KF2 a Ha Hna); exact (UN a Ha Hna)) end.
  clear KF2 UN. rename UN2 into UN.
  pmkst HS.
  preg HS (1%bv : bv 5) Rra. preg HS (2%bv : bv 5) Rsp. preg HS (3%bv : bv 5) Rgp.
  preg HS (4%bv : bv 5) Rtp. preg HS (10%bv : bv 5) Ra0. preg HS (11%bv : bv 5) Ra1.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
    assert (Ha0 : getr rg 10 = w64 (VAL (A_OBJ FO_PATH)))
      by (rewrite Ra0; apply (sv_off0 E 10); rewrite E10; exact H10);
    assert (Ha1 : getr rg 11 = w64 (VAL (A_OBJ FO_PATH)))
      by (rewrite Ra1; apply (sv_off0 E (A_OBJ FO_PATH));
          apply (ew_imgP E (A_OBJ FO_PATH) HEI); unfold A_OBJ, A_TEXT, A_LIM, FO_PATH; lia);
    assert (Hgp2 : getr rg 3 = w64 (as_gp B)) by (rewrite Rgp; apply (sv_off0 E 3); rewrite E3; exact Hgp);
    assert (Htp2 : getr rg 4 = w64 (as_tp B)) by (rewrite Rtp; apply (sv_off0 E 4); rewrite E4; exact Htp);
    assert (Hra2 : getr rg 1 = Z_to_bv 64 (BASE + 44))
      by (rewrite Rra; exact (codeptr_val E 44 HEI));
    assert (Qsp : spZ rg = spZ regs + -32)
      by (unfold spZ at 1; rewrite Rsp; cbn [sv_denot]; rewrite Usp, unsigned_lit_small by lia; reflexivity)
  end.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ =>
    assert (FD1 : m_fds mdx = m_fds md /\ m_fs mdx = m_fs md)
      by (rewrite ?md_fds_wvb, ?md_fs_wvb; split; reflexivity) end.
  eapply SRr_bind.
  { lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
      eapply (aj_strcmp_at W rg mm LIBREAC_FUZZ_FOPEN_STK (spZ regs) afmemopen_fp ly S W mem md []
                ly S mdx 0 (-32) (Z_to_bv 64 (BASE + 44)));
      [ exact HJ | exact Ha0 | exact Ha1 | exact Qsp | reflexivity | lia | lia | exact Hgp2 | exact Htp2
      | exact Hra2 | apply ret_ok_codeptr_v; [lia | reflexivity]
      | exact (roimg_kept_aview SEGS roimg ROIMG_LOW W mem mm (spZ regs) UN HLO HRO)
      | eapply (range_addressable_kept_win _ _ (spZ regs - 32 - ESTACK) (spZ regs));
        [ intros s Hs Hns; apply UN; [exact Hs | unfold FO_WIN; exact Hns] | lia | lia | lia | exact HRA ]
      | eapply (shadow_hull_vis_kept_win _ _ (spZ regs - 32 - ESTACK) (spZ regs));
        [ intros s Hs Hns; apply UN; [exact Hs | unfold FO_WIN; exact Hns] | lia | lia | lia | lia | exact HHV ] ]
    end. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hres & Hsm2 & Heff & Hpres2).
  assert (FD2 : m_fds md2 = m_fds md /\ m_fs md2 = m_fs md)
    by (destruct (sbm_fds _ _ Hsm2) as [G1 G2]; rewrite G1, G2; exact FD1).
  clear Hsm2 FD1.
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
  assert (UN3 : forall a, 0 <= a < 2 ^ 64 -> ~ FO_WIN (spZ regs) a ->
                aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a).
  { intros a Ha Hna. rewrite (Heff a Ha ltac:(unfold FO_WIN in Hna; lia)). apply UN; [exact Ha | exact Hna]. }
  (* the state at the return of the strcmp wrapper: its own frame and the two globals are kept. *)
  jafter_call_keep_pi HS 34%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2.
  match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict].
    assert (OBL : bv_unsigned (ew E 245%nat) = VAL (A_OBJ FO_LEN)) by (apply (HEI 245%nat); unfold A_TEXT, A_LIM; lia).
    assert (OBF : bv_unsigned (ew E 243%nat) = VAL (A_OBJ FO_FILE)) by (apply (HEI 243%nat); unfold A_TEXT, A_LIM; lia).
    repeat apply Forall_cons; try apply Forall_nil; split;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha.
    - apply (mbyte_of_aview SEGS). apply Heff; rewrite Usp in Ha; lia.
    - intros _. apply (apresent_writable SEGS). apply HJpres. rewrite Usp in Ha. lia.
    - rewrite OBL in Ha. apply (mbyte_of_aview SEGS). apply Heff; lia.
    - exfalso. lia.
    - rewrite OBF in Ha. apply (mbyte_of_aview SEGS). apply Heff; lia.
    - exfalso. lia. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  remember (havoc E 34 (map (getr regs2) CLOB)) as E' eqn:HE' in HS.
  assert (HEI' : img_env VAL A_LIM E') by (rewrite HE'; apply img_env_havoc; [exact HEI | cbv; lia]).
  assert (OLD : forall k, (k < 34)%nat -> ew E' k = ew E k) by (intros k Hk; rewrite HE'; apply YN3v.ew_havoc_old; exact Hk).
  assert (HAE' : env_agree 32 (Ereg regs [Z_to_bv 64 n; Z_to_bv 64 b]) E')
    by (rewrite HE'; apply env_agree_havoc_ge; [lia | exact HAE]).
  clear HE'.
  assert (F1 : ew E' 1 = getr regs 1) by (rewrite OLD by lia; exact E1).
  assert (F2 : ew E' 2 = getr regs 2) by (rewrite OLD by lia; exact E2).
  assert (F3 : ew E' 3 = getr regs 3) by (rewrite OLD by lia; exact E3).
  assert (F4 : ew E' 4 = getr regs 4) by (rewrite OLD by lia; exact E4).
  assert (F8 : ew E' 8 = getr regs 8) by (rewrite OLD by lia; exact E8).
  assert (F11 : ew E' 11 = getr regs 11) by (rewrite OLD by lia; exact E11).
  assert (F32 : ew E' 32 = Z_to_bv 64 n) by (rewrite OLD by lia; exact E32).
  assert (F33 : ew E' 33 = Z_to_bv 64 b) by (rewrite OLD by lia; exact E33).
  assert (Usp' : bv_unsigned (ew E' 2) = spZ regs) by (rewrite F2; reflexivity).
  lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
  assert (SHOK' : sh_ok SEGS Bx_FO [] E' (mrestrict (w_H W) mem2)) by constructor.
  clear SHOK.
  (* strcmp returned 0, so the branch at +0x2c (0x807b4) is taken. *)
  assert (HS' := HS).
  apply (st_ok_pi_pin_reg' E' _ _ (10%bv : bv 5) 0) in HS';
    [| cbn [ms_regs restrict mkst]; exact Hres | reflexivity].
  lazymatch type of HS' with st_ok_pi _ _ _ ?ss4 _ => let v := eval vm_compute in ss4 in change ss4 with v in HS' end.
  clear HS. rename HS' into HS.
  (* +0x2c .. +0x54 (0x807b4 .. 0x807dc): the equal path, the read of g_file_len, and the test of the length. *)
  paj_run_tok RUN HS HJ2 SHOK' Bspan_FO; [awr_ok_tac; exact Usp' |].
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (FO_WIN (spZ regs)) HFr ltac:(fo_win_tac Usp')) as KF3.
  clear HF HFr HG.
  lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (UN4 : forall a, 0 <= a < 2 ^ 64 -> ~ FO_WIN (spZ regs) a ->
                  aview SEGS (w_H W) (ms_mem msx) a = aview SEGS (w_H W) mem a)
    by (intros a Ha Hna; rewrite (KF3 a Ha Hna); exact (UN3 a Ha Hna)) end.
  clear KF3.
  psrr_branch_tok RUN BR HS SHOK' Bspan_FO.
  + (* +0x54 (0x807dc) taken: the length is 0; +0x78 (0x80800) returns 0 with no call and no allocation. *)
    rewrite branch_eq_U in Hc.
    assert (Un : U E' (SOff 32 0) = n) by (apply U_atom; [exact F32 | lia]).
    assert (U0 : U E' (SLit 0) = 0) by reflexivity.
    rewrite Un, U0 in Hc. apply Z.eqb_eq in Hc.
    paj_run_tok RUN HS HJ2 SHOK' Bspan_FO; [awr_ok_tac; exact Usp' |].
    pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (FO_WIN (spZ regs)) HFr ltac:(fo_win_tac Usp')) as KF4.
    clear HF HFr HG.
    lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
      assert (UN5 : forall a, 0 <= a < 2 ^ 64 -> ~ FO_WIN (spZ regs) a ->
                    aview SEGS (w_H W) (ms_mem msx) a = aview SEGS (w_H W) mem a)
      by (intros a Ha Hna; rewrite (KF4 a Ha Hna); exact (UN4 a Ha Hna)) end.
    clear KF4.
    lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
      preg HS (1%bv : bv 5) R1; preg HS (10%bv : bv 5) R10;
      eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
      intros mat';
      unfold tlibreac_fuzz_fopen_post, apost_base;
      exists ly, S, (ms_regs msc), (ms_mem msc); eexists;
      split; [cbn [ms_regs]; rewrite R1, (sv_off0 E' 1 _ F1), Hra; reflexivity|];
      split; [eapply (ajournal_mono_k SEGS B);
              [eapply ajournal_materialize; (try exact LAWS); (try exact Hsegs); exact HJ2
              | unfold EV_FUZZ_FOPEN; lia]|];
      split; [eapply (aregs_preserved_of_st_ok SEGS _ E' _ _ regs [Z_to_bv 64 n; Z_to_bv 64 b] HS);
              [exact HAE' | vm_compute; reflexivity]|];
      exists 0;
      split; [cbn [ms_regs]; rewrite R10; reflexivity|];
      split; [reflexivity|];
      split; [rewrite ?md_fds_wvb; exact (proj1 FD2)|];
      split; [rewrite ?md_fs_wvb; exact (proj2 FD2)|];
      split; [intros _; split; [reflexivity|]; split; [reflexivity|]; split;
              [eapply (asource_none_kept SEGS K W mem (ms_mem msc) (spZ regs)); [exact (fi_kimg FI) | exact UN5 | exact HLO | exact HNONE]
              | exact (mo_le_refl MT MLAWS S)]|];
      intros Hge; exfalso; lia
    end.
  + (* +0x58 .. +0x74 (0x807e0 .. 0x807fc): the length is not 0; the tail jump to the fmemopen wrapper. *)
    rewrite branch_eq_U in Hc.
    assert (Un : U E' (SOff 32 0) = n) by (apply U_atom; [exact F32 | lia]).
    assert (U0 : U E' (SLit 0) = 0) by reflexivity.
    rewrite Un, U0 in Hc. apply Z.eqb_neq in Hc.
    assert (Hn1 : 1 <= n) by lia.
    destruct (HBLK Hn1) as (Hinb & Hgarr & Hbytes).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR Hinb) as (Hb16 & Hb4096 & Hbceil & _).
    pose proof (req_size_pos n ltac:(lia)) as [_ Hreq].
    paj_run_tok RUN HS HJ2 SHOK' Bspan_FO; [awr_ok_tac; exact Usp' |].
    pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (FO_WIN (spZ regs)) HFr ltac:(fo_win_tac Usp')) as KF4.
    clear HF HFr HG.
    lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
      assert (UN5 : forall a, 0 <= a < 2 ^ 64 -> ~ FO_WIN (spZ regs) a ->
                    aview SEGS (w_H W) (ms_mem msx) a = aview SEGS (w_H W) mem a)
      by (intros a Ha Hna; rewrite (KF4 a Ha Hna); exact (UN4 a Ha Hna)) end.
    clear KF4.
    pmkst HS.
    preg HS (1%bv : bv 5) Tra. preg HS (2%bv : bv 5) Tsp. preg HS (3%bv : bv 5) Tgp.
    preg HS (4%bv : bv 5) Ttp. preg HS (8%bv : bv 5) Ts0.
    preg HS (10%bv : bv 5) Ta0. preg HS (11%bv : bv 5) Ta1. preg HS (12%bv : bv 5) Ta2.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
      assert (Ta0' : getr rg 10 = w64 b) by (rewrite Ta0; apply (sv_off0 E' 33); exact F33);
      assert (Ta1' : getr rg 11 = w64 n) by (rewrite Ta1; apply (sv_off0 E' 32); exact F32);
      assert (Ta2' : getr rg 12 = w64 (as_mode K)) by (rewrite Ta2; apply (sv_off0 E' 11); rewrite F11; exact H11);
      assert (Tgp' : getr rg 3 = w64 (as_gp B)) by (rewrite Tgp; apply (sv_off0 E' 3); rewrite F3; exact Hgp);
      assert (Ttp' : getr rg 4 = w64 (as_tp B)) by (rewrite Ttp; apply (sv_off0 E' 4); rewrite F4; exact Htp);
      assert (Tra' : getr rg 1 = getr regs 1) by (rewrite Tra; apply (sv_off0 E' 1); exact F1);
      assert (Tsp' : spZ rg = spZ regs + 0)
        by (unfold spZ at 1; rewrite Tsp, (sv_off0 E' 2 _ F2); unfold spZ; lia);
      assert (Ts0' : s0Z rg = s0Z regs)
        by (unfold s0Z at 1; rewrite Ts0; rewrite (sv_off0 E' 8 _ F8); reflexivity)
    end.
    eapply SRr_mono.
    { lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
        eapply (cl_callS B LAWS W rg mm (Z_to_bv 64 (SIGMA PS___interceptor_trampoline_fmemopen))
                  LIBREAC_FUZZ_FOPEN_STK (spZ regs) afmemopen_fp ly S W mem md [] ly S mdx 0
                  AFMEMOPEN_STK afmemopen_fp 1 0 (getr regs 1) ch
                  (fun ly2 S2 W2 regs2' mem2' md2' => exists res : Z,
                     getr regs2' 10 = w64 res /\ frames S2 = frames S /\
                     mo_le MT S S2 (mo_malloc MT SRC_FILE_BLOCK) /\
                     m_fds md2' = m_fds md /\ m_fs md2' = m_fs md /\
                     4096 <= res /\ res mod 16 = 0 /\
                     ablocks B ly2 S2 = ablocks B ly S ++ [(res, SRC_FILE_BLOCK)] /\
                     asource_unbuffered SEGS K (rdW W2 mem2') res b C 0))
      end.
      all: try exact HJ2. all: try exact Tsp'. all: try exact Tgp'. all: try exact Ttp'.
      all: try exact Tra'. all: try exact Hra. all: try exact Hra4.
      all: try reflexivity. all: try lia.
      all: try (cbv [LIBREAC_FUZZ_FOPEN_STK AFMEMOPEN_STK]; lia).
      - rewrite Z.add_0_r. rewrite Ts0'.
        eapply (achain_kept ly _ _ (spZ regs) (s0Z regs) ch (spZ regs) Hch); [lia | lia |].
        intros a Ha. apply UN5; [lia | unfold FO_WIN; lia].
      - intros HPREc.
        lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
          eapply SRr_mono;
          [ exact (AFMEMOPEN W ly S rg mm mdx ch b n C (fi_head FI) HPREc HCTX Ta0' Ta1' Ta2'
                     (asource_none_kept SEGS K W mem mm (spZ regs) (fi_kimg FI) UN5 HLO HNONE) HnC (conj Hn1 Hn26) Hinb
                     (garr8_kept SEGS W mem mm (spZ regs) b C UN5 HLO ltac:(lia) ltac:(lia) Hgarr) Hbytes
                     (MCONSTS W mm (roimg_kept_aview SEGS roimg ROIMG_LOW W mem mm (spZ regs) UN5 HLO HRO))
                     Hev Hlive HMO HU1 HU2)
          | ] end.
        cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & res & -> & HJ3 & HP3 & Hres3 & Hfr3 & Hmle3 & Hfd3 & Hfs3 & Hsucc3).
        exists ly3, S3, regs3, mem3, md3.
        split; [rewrite Tra'; reflexivity|].
        split; [exact HJ3|]. split; [exact HP3|].
        exists res. split; [exact Hres3|]. split; [exact Hfr3|]. split; [exact Hmle3|].
        split; [rewrite Hfd3, ?md_fds_wvb; exact (proj1 FD2)|].
        split; [rewrite Hfs3, ?md_fs_wvb; exact (proj2 FD2)|].
        exact Hsucc3.
      - intros a Ha. left. exact Ha. }
    cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ4 & _ & HP4 & res & Hres4 & Hfr4 & Hmle4 & Hfd4 & Hfs4 & H4096 & H16 & Hbl & Hsrc).
    unfold tlibreac_fuzz_fopen_post, apost_base.
    exists ly3, S3, regs3, mem3, md3.
    split; [reflexivity|].
    split; [rewrite Z.add_0_l in HJ4; exact HJ4|].
    split.
    { eapply aregs_preserved_trans; [|exact HP4].
      lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msc) |- _ =>
        eapply (aregs_preserved_of_st_ok SEGS _ E' _ _ regs [Z_to_bv 64 n; Z_to_bv 64 b] HS);
        [exact HAE' | vm_compute; reflexivity] end. }
    exists res. split; [exact Hres4|]. split; [exact Hfr4|].
    split; [exact Hfd4|]. split; [exact Hfs4|].
    split; [intros Hz; exfalso; lia|].
    intros _. split; [exact H4096|]. split; [exact H16|]. split; [exact Hbl|]. split; [exact Hsrc | exact Hmle4].
Qed.
End h.
End f.
End d.
(* The sink-head instance is the caller's to give: the only global instance loaded with the unit is the plain
   build's (Reusable/YI5b.v src0_sink_head), whose open-file head is not this image's. *)
Arguments FopenImg SK A_GLEN A_GFILE K : clear implicits.
Check (fun (SK : YI16.sink_head) (A_GLEN A_GFILE : Z)
           (K : asource_syms) => FopenImg SK A_GLEN A_GFILE K).
Arguments pb_libreac_fuzz_fopenX {fx rc} SK {PI}.
(* The guard: the theorem's type is the shared statement at this image's instance, the type lib/B/Prog/PcapSourceOpen.v
   takes as its FOPEN hypothesis (BASE + AF_libreac_fuzz_fopen, objects 3 / 4 / 2); it fails if SK becomes implicit. *)
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) (PI : PAImg pcap_listing)
           B K FM_RA CTX MT roimg ROIMG_LOW mc_lo mc_hi MCONSTS LAWS MLAWS FI STRCMP AFMEMOPEN =>
         pb_libreac_fuzz_fopenX (fx := fx) (rc := rc) SK (PI := PI) B K FM_RA CTX MT roimg ROIMG_LOW mc_lo mc_hi
           MCONSTS LAWS MLAWS FI STRCMP AFMEMOPEN
         : tlibreac_fuzz_fopen_specX SK (@pa_segs _ pcap_listing PI)
             (@pa_val _ pcap_listing PI A_TEXT + AF_libreac_fuzz_fopen)
             (@pa_val _ pcap_listing PI (A_OBJ 3)) (@pa_val _ pcap_listing PI (A_OBJ 4))
             (@pa_val _ pcap_listing PI (A_OBJ 2)) roimg B K MT FM_RA CTX).

(* The address facts the walk's image hypotheses rest on, on the tables fuzz_pcap.asan-ubsan gives
   (lib/B/Prog/PcapAddr.v), each measured on that pin (sha256 9e66f771...) through its unstripped twin's symtab:
   the listing's strcmp trampoline is __interceptor_trampoline_strcmp+0x0 = 0x415b4 (asan: 0x41564) and its
   object FO_PATH is the "<fuzz-input>" literal .str+0x0 = 0x20d00 (asan: 0x20d00), the two globals this function
   reads, g_file_len+0x0 = 0x5d3e40 and g_file+0x0 = 0x5d3e60 (asan: 0x5d3f40 / 0x5d3f60), do not overlap
   (FopenImg's fi_sep), and KS_U's stdio cells lie in the image (fi_kimg at K := KS_U; __libc+0x1, __libc+0x3,
   ofl_lock+0x0, "rb" .rodata+0x10a60, "rwa" .rodata+0xfd46, __stack_chk_guard+0x0) with its open-file head
   ofl_head+0x0 = 0x5f4e88 (fi_head's value: the asan-ubsan sink_head's AOFL_HEAD must equal it). They are checked
   here so that the hypotheses are known to be satisfiable on this image. *)
Lemma fopen_img_tables_B :
pcap_sigma PS___interceptor_trampoline_strcmp = (symaddr Symbols.AsanUbsan.s___wrap_strcmp) /\
pcap_sigma PS___interceptor_trampoline_fmemopen = (symaddr Symbols.AsanUbsan.s___wrap_fmemopen) /\
pcap_obj FO_PATH = (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68128)%Z) /\
pcap_obj FO_LEN = (symaddr Symbols.AsanUbsan.s_g_file_len) /\ pcap_obj FO_FILE = (symaddr Symbols.AsanUbsan.s_g_file) /\
(pcap_obj FO_LEN + 8 <= pcap_obj FO_FILE \/ pcap_obj FO_FILE + 8 <= pcap_obj FO_LEN) /\
Forall (fun a => 0 <= a /\ a + 16 <= pcap_img_end)
  [as_threaded KSU.pcap_KS; as_need_locks KSU.pcap_KS; as_ofl_lock KSU.pcap_KS; as_mode KSU.pcap_KS;
   as_rwa KSU.pcap_KS; as_canary KSU.pcap_KS] /\
as_ofl_head KSU.pcap_KS = (symaddr Symbols.AsanUbsan.s_ofl_head).
Proof.
split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
split; [left; vm_compute; discriminate|].
split; [|vm_compute; reflexivity].
apply Forall_forall. intros a Ha. vm_compute in Ha.
unfold pcap_img_end, YImgTop.IMG_TOP, YImgTop.IMG_LO.
repeat (destruct Ha as [<- | Ha]; [lia|]). destruct Ha.
Qed.
