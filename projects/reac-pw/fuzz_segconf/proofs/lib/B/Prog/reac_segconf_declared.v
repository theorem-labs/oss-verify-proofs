(* The image-B port of lib/A/Prog/reac_segconf_declared.v (commit 6121a10279e4): the walk of
   reac_segconf_declared on the ASan+UBSan build of reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin
   sha256 c3796c0b38f3666f32a3ecff43c9fdb55ead356833af6013a07c404bd0254509; entry 0x89e7c =
   BASE + AF_reac_segconf_declared, 924 bytes, 231 instructions, side-stack frame class 1): it proves the contract
   reac_segconf_declared_contract of lib/B/Prog/reac_segconf_declared_c.v (image B's copy of the FINAL contract text,
   6f783602b5e3) at this image's numbers, from the five segments reac_segconf_declared_s1.v .. _s5.v chained by
   reac_segconf_declared_a.v, in the form of plugin-hostd/fuzz_command's lib/B/Prog/chain_words.v.
   Image B's code is image A's with UBSan's four tests before uses, each a branch to the one `unimp` at 0x8a1f8, and
   each refuted at its branch from a premise of the contract: c & 7 at 0x89fa4 (S1: declared_pre's c mod 16 = 0),
   i = 32 at 0x8a000 and ~c <u 356 i at 0x8a004 (S2: i < c->n <= 32 by rconf_enc; c + 356 i < 2^64), the 32-bit
   overflow of added + r at 0x8a084 (S3: 0 <= added <= i <= 31 and r in {0, 1}).
   The Section hypotheses the theorem keeps are the contract's own list (its head comment): the class-1 side-stack
   frame laws, the two callee contracts, the per-binary record facts, and - until the record's image files land -
   the image facts seg_val_relro, ro_below_ofl, seg_sig_prog and dc_sspP, each of which the record discharges.
   The image numbers this file instantiates, image B's instance file's (lib/B/Prog/SegInstB.v): the entry and the
   two callee entries stay listing terms (SegList's AF_<fn>); the stack windows SegInstB.STK_reac_segconf_declared,
   STK_reac_declared_vlan_split, STK_reac_declared_vlan_add (named DC_STK, DC_STK_SPLIT, DC_STK_ADD in
   reac_segconf_declared_d.v); the read-only window SegInstB.RLO_A / RHI_A (image B's SegGlob.SEG_RLO / SEG_RHI,
   0xa1c60 / 0xa3f08); the stack-protector GOT word and guard musl's __strtol_internal compares, which split's
   contract takes as parameters (below). The two callee contracts are stated at the numbers their walks are
   stated at, so that the close gives reac_declared_vlan_split_walk and reac_declared_vlan_add_walk for them. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable SegSyms SegList SegPa SegPaLib PaLibF PaSB SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
reac_declared_vlan_split_c reac_declared_vlan_add_c reac_segconf_declared_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
reac_segconf_declared_d reac_segconf_declared_lem reac_segconf_declared_a.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
reac_segconf_declared_s1 reac_segconf_declared_s2 reac_segconf_declared_s3 reac_segconf_declared_s4
reac_segconf_declared_s5.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
(* The stack-protector cells musl's __strtol_internal reaches under split's strtol call (image B, read from the
   twin's .symtab and .got, sha256 80e82127e8ca): __stack_chk_guard is 0x5ff838 and the one GOT word holding it is
   0xa3e98 (image A: 0x5ff078 / 0xa36d8). split's contract takes both as parameters; this walk is the image's, so it
   gives them their values, SegInstB.gotwA / guardA, under the names the proof below uses. *)
#[local] Notation DC_GOTW := SegInstB.gotwA (only parsing).
#[local] Notation DC_GUARD := SegInstB.guardA (only parsing).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
Section e.
Variable B : asyms.
(* the per-binary record facts, as fuzz_command's walks take them *)
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
(* the image facts, until the record's image files land: the read-only window's bounds, that it lies below the
   overflow head, the call targets of the program functions, and the stack-protector cells *)
Hypothesis VRELRO : seg_val_relro.
Context {RO : ro_below_ofl SEGS SegInstB.RLO_A SegInstB.RHI_A}.
Hypothesis SSP : dc_sspP B SegInstB.gotwA SegInstB.guardA.
Hypothesis SIGP : seg_sig_prog.
(* the class-1 side-stack frame: taken by the call at 0x89ef4, released by the flag store at 0x8a15c *)
Hypothesis SM1 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
(* the two program callees, at their entries and stack windows *)
Hypothesis SPLIT : forall fx0 : YK11.FPState,
  @reac_declared_vlan_split_contract fx0 rc SK SEGS B (BASE + AF_reac_declared_vlan_split)
    SegInstB.STK_reac_declared_vlan_split SegInstB.RLO_A SegInstB.RHI_A SegInstB.gotwA SegInstB.guardA.
Hypothesis ADD : forall fx0 : YK11.FPState,
  @reac_declared_vlan_add_contract fx0 rc SK SEGS B (BASE + AF_reac_declared_vlan_add)
    SegInstB.STK_reac_declared_vlan_add SegInstB.RLO_A SegInstB.RHI_A.
(* the read-only window lies in the image: the listing's relro bounds are its own *)
Lemma dc_ro_img : dc_ro_imgP SegInstB.RLO_A SegInstB.RHI_A.
Proof using VRELRO.
intros a Ha. apply pa_relro_img. destruct VRELRO as [E1 E2]. rewrite E1, E2. exact Ha.
Qed.
Theorem reac_segconf_declared_walk :
  reac_segconf_declared_contract SEGS B (BASE + AF_reac_segconf_declared) SegInstB.STK_reac_segconf_declared
    SegInstB.RLO_A SegInstB.RHI_A SegInstB.gotwA SegInstB.guardA.
Proof using TL TLF ML VRELRO RO SSP SIGP SM1 SMP ASF FFL SPLIT ADD.
unfold reac_segconf_declared_contract.
intros ly S W regs mem md ch c tab max n rcs t HPRE HROD H10 Hc64 H11 Htab64 H12 Hmax64 H13 Hn64 HDP HROOM HNEV.
pose (cx := mkDCX ly S W regs mem md ch c tab max n rcs t 0).
assert (HP : dc_pre B DC_STK SegInstB.RLO_A SegInstB.RHI_A DC_GOTW DC_GUARD cx) by (constructor; assumption).
exact (dc_run B SegInstB.RLO_A SegInstB.RHI_A DC_GOTW DC_GUARD
  (dc_S1 B SegInstB.RLO_A SegInstB.RHI_A DC_GOTW DC_GUARD TL TLF ML SM1 SMP)
  (dc_S2 B SegInstB.RLO_A SegInstB.RHI_A DC_GOTW DC_GUARD SIGP SPLIT dc_ro_img SSP)
  (dc_S3 B SegInstB.RLO_A SegInstB.RHI_A DC_GOTW DC_GUARD SIGP ADD dc_ro_img)
  (dc_S4 B SegInstB.RLO_A SegInstB.RHI_A DC_GOTW DC_GUARD)
  (dc_S5 B SegInstB.RLO_A SegInstB.RHI_A DC_GOTW DC_GUARD ML ASF FFL)
  cx HP).
Qed.
End e.
End f.
End d.
Print Assumptions reac_segconf_declared_walk.
About reac_segconf_declared_walk.
