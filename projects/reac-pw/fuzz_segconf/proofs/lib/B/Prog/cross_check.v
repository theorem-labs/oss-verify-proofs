(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the call of send_message in LLVMFuzzerTestOneInput's ASan walk (plugin-hostd/fuzz_command, jal at 0x86714, back at 0x86718), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v:122-290 (a program call through cl_callS, the callee's statement applied, the caller's facts carried past it). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/LLVMFuzzerTestOneInput_s30.v, with its module paths and module names changed; 622 of its 671 lines of code are new or changed and 292 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_s20k.v, with its module paths and module names changed; 58 of its 86 lines of code are new or changed and 643 lines of the source are left out. *)
(* The walk of cross_check on reac-pw/fuzz_segconf's ASan+UBSan IMAGE B (fuzz_segconf.asan-ubsan, pin
   c3796c0b38f3; cross_check at 0x897cc, 696 bytes, 174 instructions): the theorem `cross_check_walk`, the
   contract lib/B/Prog/cross_check_c.v at image B's values.

   The three segments of cross_check_d.v, chained by cross_check_a.v's cc_run:
     cross_check_s1.v  cc_s1  the entry 0x897cc-0x89870 (UBSan traps 0x89804 and 0x89810, inline check 1), to
                              the loop head 0x89874 or to the epilogue 0x899fc
     cross_check_s2.v  cc_s2  one pass 0x89874-0x89980 (UBSan traps 0x89878 and 0x8987c, inline checks 2-9, the
                              two refuse calls 0x89900 F_xbox and 0x89944 F_xmodel)
     cross_check_s3.v  cc_s3  the epilogue 0x899fc-0x89a34
   with cross_check_f.v (the pure model and encoding lemmas) and cross_check_r.v (the two refuse call sites).

   ADAPTED from the image-A G3 walk owner's image-A lane (a working branch) and the unit owner's UBSan walk
   lib/U/Prog/cross_check.v (a working branch), re-derived on image B's machine code.

   THE IMAGE-B VALUES THIS THEOREM STATES, and where each comes from:
     A_cross_check   BASE + AF_cross_check = 0x897cc      lib/B/Prog/SegList.v (AF_cross_check = 0x4a0c)
     A_refuse        BASE + AF_refuse      = 0x892f8      lib/B/Prog/SegList.v (AF_refuse = 0x4538)
     STK_cross_check 128 + STK_refuse      = 12592        the 128-byte frame (0x897cc) over refuse's window
     STK_refuse      160 + 16 + 3 * ESTACK = 12464        refuse's frame 160 (0x892f8), its realignment
                                                          (0x89334 andi sp,sp,-32) and the printf wrappers
     RLO / RHI       SEG_RLO / SEG_RHI = 0xa1c60/0xa3f08  lib/B/Prog/SegGlob.v
     lit F_xmodel    VAL (A_OBJ 74) = 0x21c00             0x8986c; the 103 bytes read from the pin
     lit F_xbox      VAL (A_OBJ 73) = 0x21ca0             0x8985c; the 91 bytes read from the pin
   The two object indices are image B's and are NOT image A's, where A_OBJ 73 is F_xmodel and A_OBJ 74 is
   F_xbox: the .str numbering moved by one between the two builds while the addresses did not (checked against
   lib/B/Prog/SegAddr.v's seg_objs and against the pin's bytes).

   NAMES: the image-B harness owner's lib/B/Prog/SegInstB.v will carry image B's instantiation under the image-A owner's SegInstA names
   (STK_cross_check, STK_refuse, RLO_A, RHI_A, gotwA, guardA, seg_litA_rc, A_<F>_A). Until it lands those names
   live in the section below with the same spelling, so that the switch is one Require. (the image-B G3 walk owner, the coordinating session's
   decision 17:3xZ: do not create a SegInstB file in this lane.) *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegAddr SegPa SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegGlob SegPgBase SegABase SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaFx SegPaLib PaLibF.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegRecBase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c cross_check_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import cross_check_f cross_check_d cross_check_a.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require cross_check_s1 cross_check_s2 cross_check_s3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* image B's stack numbers, read-only window, stack-protector cells and literal map are SegInstB's
   (the image-B harness owner, lib/B/Prog/SegInstB.v): STK_refuse 12464, STK_cross_check 12592, RLO_A 0xa1c60,
   RHI_A 0xa3f08, gotwA 0xa3e98, guardA 0x5ff838, seg_litA_rc. Nothing of that is defined again here. *)

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
Section e.
Variable B : asyms.
(* the literal map of reac_segconf.c: a parameter here, instantiated at SegInstB's seg_litA_rc in
   cross_check_walk_B below *)
Variable lit : list Z -> Z.
(* the stack-protector cells musl's printf_core compares (SegInstB's gotwA 0xa3e98 / guardA 0x5ff838 in
   cross_check_walk_B). cross_check does not read them: it passes them to refuse. *)
Variables gotw guard : Z.
#[local] Notation RLO := SEG_RLO.
#[local] Notation RHI := SEG_RHI.
(* the record hypotheses of a walk over the listing *)
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis HVO : seg_val_objs.
Hypothesis HSG : seg_sig_prog.
(* the image facts, as one record (the image-B listing owner's SegRecBase.seg_img_facts, image A's CmdRecBase.cmd_img_facts
   form): the walk uses its cif_relro_img, the read-only window lying in the image (cross_check_r.v
   cc_un_after). The stack-protector cells at every allocator state are not a field of that record, so they
   stay their own hypothesis, as image A's walk takes them from its separate cells record. *)
Hypothesis IMG : SegRecBase.seg_img_facts SEGS B.
Hypothesis HSSP : forall ly S (W : world SEGS) mem md,
  AR SEGS B ly S W mem md -> sa_ssp (aview SEGS (w_H W) mem) gotw guard.
(* the two formats cross_check passes, at image B's listing objects *)
Hypothesis HLM : lit F_xmodel = VAL (A_OBJ 74).
Hypothesis HLB : lit F_xbox = VAL (A_OBJ 73).
(* the one callee: refuse, at image B's entry and stack window, at every FP state (its post is apost_baseF) *)
Hypothesis REF : forall fx0 : YK11.FPState,
  @refuse_contract fx0 rc SK SEGS B (BASE + AF_refuse) STK_refuse RLO RHI lit gotw guard.

Theorem cross_check_walk :
  @cross_check_contract fx rc SK SEGS B (BASE + AF_cross_check) STK_cross_check RLO RHI lit gotw guard.
Proof.
assert (HSTK : 0 <= STK_refuse) by (unfold STK_refuse, ESTACK; lia).
pose proof (SegRecBase.cif_relro_img _ _ IMG) as HRRO.
assert (S1 : forall fx0 : YK11.FPState, @cc_S1P fx0 rc SK PI B lit gotw guard STK_refuse)
  by (intros fx0; apply cross_check_s1.cc_s1; assumption).
assert (S2 : forall fx0 : YK11.FPState, @cc_S2P fx0 rc SK PI B lit gotw guard STK_refuse)
  by (intros fx0; apply cross_check_s2.cc_s2; assumption).
assert (S3 : forall fx0 : YK11.FPState, @cc_S3P fx0 rc SK PI B lit gotw guard STK_refuse)
  by (intros fx0; apply cross_check_s3.cc_s3; assumption).
unfold cross_check_contract. intros ly S W regs mem md ch c rcs HPRE HROD H10 Hc64 HCP HRoom HNev.
pose proof HCP as (_ & _ & _ & _ & _ & _ & HFRM & _).
pose proof (cc_run B lit gotw guard STK_refuse S1 S2 S3 (mkCCX ly S W regs mem md ch c rcs)
  (cc_pre_of B lit gotw guard STK_refuse (mkCCX ly S W regs mem md ch c rcs)
     HPRE HROD H10 Hc64 HCP HRoom HNev) HFRM) as HR.
unfold cc_post, cc_Q, cc_FP, cc_STK in HR. cbn [x_ly x_S x_W x_regs x_mem x_md x_ch x_c x_rcs] in HR.
exact HR.
Qed.
End e.

(* The same theorem at SegInstB's image-B values: reac_segconf.c's literal map, the stack-protector cells and
   refuse's window, all measured on the B pin by the image-B harness owner. The two format hypotheses are discharged here by
   computation over the listing's objects, which is where image B's swap against image A shows up:
   nth 74 seg_objs = 0x21c00 = F_xmodel and nth 73 seg_objs = 0x21ca0 = F_xbox. SegInstB's A_cross_check_A /
   A_refuse_A are seg_text + AF_cross_check / seg_text + AF_refuse (its _AF lemmas), which is this entry at the
   pinned instance. *)
Theorem cross_check_walk_B : forall (Bx : asyms),
  PALib Bx -> PALibF Bx -> seg_val_objs -> seg_sig_prog ->
  SegRecBase.seg_img_facts SEGS Bx ->
  (forall ly S (W : world SEGS) mem md,
     AR SEGS Bx ly S W mem md -> sa_ssp (aview SEGS (w_H W) mem) gotwA guardA) ->
  (forall fx0 : YK11.FPState,
     @refuse_contract fx0 rc SK SEGS Bx (BASE + AF_refuse) STK_refuse RLO_A RHI_A seg_litA_rc gotwA guardA) ->
  @cross_check_contract fx rc SK SEGS Bx (BASE + AF_cross_check) STK_cross_check RLO_A RHI_A seg_litA_rc
    gotwA guardA.
Proof.
intros Bx TL TLF HVO HSG IMGx HSSP REF.
assert (L74 : (74 < length seg_objs)%nat) by (vm_compute; lia).
assert (L73 : (73 < length seg_objs)%nat) by (vm_compute; lia).
apply (cross_check_walk Bx seg_litA_rc gotwA guardA TL TLF HVO HSG IMGx HSSP);
  [rewrite (HVO 74%nat L74) | rewrite (HVO 73%nat L73) | exact REF]; vm_compute; reflexivity.
Qed.
End f.
End d.
