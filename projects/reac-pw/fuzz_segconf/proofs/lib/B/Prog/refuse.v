(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: number's walk on the ASan build of plugin-hostd/fuzz_command, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v..ACh8.v (a walk) and ACa2.v (a class-1 side-stack frame): tnumber_spec of lib/A/Prog/number_c.v, from number's entry (0x8e430) through __asan_stack_malloc_0 and strtol to strtol's return, then numberB.v's n_segB. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/numberA.v, with its module paths, module names and numbers changed; 1350 of its 1544 lines of code are new or changed and 319 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: refuse's walk on reac-pw/fuzz_segconf's ASan image A (fuzz_segconf.asan,
   refuse at 0x88da4), in the form of plugin-hostd/fuzz_command's lib/A/Prog/numberA.v at origin/ossv/recipes
   501c0d516c69 (number: a class-0 side-stack frame released inline): the entry to the call of
   __asan_stack_malloc_0 (0x88e30), the frame and its poisoning, the inline checks of c->refused, c->n_refusals
   and c->reading[0], and the branches up to the snprintf calls (0x88f5c, 0x88f74) and the n_refusals >= 8 exit
   (0x88efc -> 0x88fc4). The refuse walk, 2026-10-30. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/refuse_a.v, with its module paths and module names changed; 47 of its 84 lines of code are new or changed and 1507 lines of the source are left out. *)
(* refuse (reac_segconf.c:30-48) on reac-pw/fuzz_segconf's ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256
   c3796c0b38f3..., twin 80e82127e8ca; 0x892f8 .. 0x8963c, 210 instructions; a class-0 side-stack frame; 5
   instrumented checks; 5 UBSan trap branches; wrapper_snprintf twice and wrapper_vsnprintf once): the walk proving
   refuse_contract (lib/B/Prog/refuse_c.v, the B copy of the image-A owner's image-independent text, closed against G3 FINAL
   at 6f783602b5e3) at image B's numbers (lib/B/Prog/SegInstB.v). The image-B refuse walk lane of the image-B G3 walk owner, 2026-10-30.

    proves function refuse (reuse search, rule 24: origin/main 6e24fa4d602c, origin/ossv/recipes 3abc3740de97, origin/ossv/candidates ee89628c9971, origin/release/pau-projects-recipes b6a0088adcb4, the earlier proof delivery and the working heads, by name and by the image-B address 0x892f8 (index and path-scoped git grep); confirmed by the rule-24 checker 2026-10-30T16:55:47Z; the result is recorded with the commissioning brief).
   Verdict: none released; ADAPTED from the image-A G3 walk owner's image-A walk of refuse (commit 781e28832d34:
   lib/A/Prog/refuse_f.v, refuse_pft.v, copied as lib/B/Prog/refuse_f.v / refuse_pft.v) and fuzz_command's
   released ASan+UBSan walks of number and check_reply (origin/ossv/recipes 501c0d516c69, lib/B/Prog/numberE.v,
   numberA.v, numberB.v, numberR.v, check_reply_s4.v), re-derived on image B's code
   (refuse.fuzz_segconf.asan-ubsan.s).

   THE WALK (the B cut plan: the lane report ref.md section 1):
   - refuse_E.v: the symbolic entry state and its seed; refuse_K.v: the two cuts RB_PRE 0x894ac and RB_REL 0x89544,
     their canonical states (ss_pre, ss_rel0), the canonicalization lemma and the segment statements.
   - refuse_H.v rb_head: entry to the cuts (frame_alloc_0, the frame's shadow, checks 1-3 on c's block, traps T1
     and T2 decided by the facts, trap T3 split and refuted, the where split).
   - refuse_P*.v rb_pre (a sub-lane): 0x894ac to the release: both snprintf arms, the k test, trap T4, the
     vsnprintf of the caller's va_list, checks 4 and 5, trap T5, the n_refusals store.
   - refuse_R.v rb_rel (a sub-lane): the frame release (flag byte, shadow f5) and the return.
   - refuse_ffr.v rb_ffr (a sub-lane): the printf family fact FFR at segconf's family FR_seg, PROVED (no longer a
     hypothesis).
   Checks 5 of 5 and UBSan traps 5 of 5 discharged (T1, T2 decided by the executor from the facts; T3 in rb_head,
   T4, T5 in rb_pre refuted on their taken sides); the slow paths 0x895e4 .. 0x8963c and `unimp` 0x895e0 are never
   reached.

   SECTION HYPOTHESES (each a runtime entry, a frame law, or a record fact; none is a walk segment):
   SM0, SMP, ASF, FFL: the side-stack frame of class 0 (fuzz_command numberA.v's, at image B's frame_alloc_0
   0x3e608 = listing SS___asan_stack_malloc_0); SNP, VSNP: the image-A wrapper-layer owner's interface rows 4 and 5 (carriers
   lib/B/Rt/RtPFSeg.v of the image-B wrapper-layer owner) at the listing's snprintf / vsnprintf trampolines; TL, TLF, ML, OBJ: the
   record facts and the listing's object table over the walk's abstract PAImg instance; SSPX: the stack-protector
   cells at every AR state (used once, right after the frame take). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI08 YG0v YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YI16 YM05 YN2j.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegSyms SegList SegPa SegPaLib PaLibF PaLibG PaLibH PaSB PaDenot PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase refuse_c refuse_f refuse_E refuse_K refuse_H refuse_R SegObj SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtPFSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_pft refuse_ffr refuse_P.
Import ListNotations.
Local Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Hypothesis SM0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 0.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis OBJ : seg_val_objs (PI := PI).
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.
(* the image-A wrapper-layer owner's rows 4 and 5 at the listing's trampolines, formats in [0x10000, gotw), destinations off the image
   [0x10000, kImgEnd), over the image's read-only ranges cr (the LLVMFuzzerTestOneInput walk's snp_cr convention) *)
Variable cr : list (Z * Z).
Hypothesis SNP : forall fx0 : YK11.FPState, @seg_asnprintf_realizes fx0 rc SEGS B 0x10000 kImgEnd cr
  (pa_sigma SS___interceptor_trampoline_snprintf) gotwA guardA.
Hypothesis VSNP : forall fx0 : YK11.FPState, @seg_avsnprintf_realizes fx0 rc SEGS B 0x10000 kImgEnd cr
  (pa_sigma SS___interceptor_trampoline_vsnprintf) gotwA guardA.
Hypothesis CRP : Forall (fun r => 0x10000 <= fst r /\ 0 <= snd r /\ fst r + snd r <= kImgEnd) cr.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* image B's numbers against the walk's premises *)
Lemma rw_stk : 160 + 16 + 3 * ESTACK <= STK_refuse.
Proof. unfold STK_refuse. lia. Qed.
Lemma rw_gw : 0x10000 <= gotwA /\ gotwA + 8 <= kImgEnd /\ 0x10000 <= guardA /\ guardA + 8 <= kImgEnd.
Proof. unfold gotwA, guardA, kImgEnd. lia. Qed.
(* listing object 34 is .str.1, "reac-pw.conf" of reac_segconf.c (0x21360), seg_litA_rc's S_base *)
Lemma rw_lit34 : VAL (A_OBJ 34) = seg_litA_rc S_base.
Proof.
rewrite (OBJ 34%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)). rewrite seg_litA_rc_S_base. vm_compute. reflexivity.
Qed.

(* listing objects 71 / 72 are .str.31 "%s:%d: " (0x21aa0) and .str.32 "%s: " (0x21ac0) of reac_segconf.c *)
Lemma rw_obj71 : VAL (A_OBJ 71) = seg_litA_rc F_addr_line.
Proof. rewrite (OBJ 71%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)). vm_compute. reflexivity. Qed.
Lemma rw_obj72 : VAL (A_OBJ 72) = seg_litA_rc F_addr.
Proof. rewrite (OBJ 72%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)). vm_compute. reflexivity. Qed.
(* the 19 formats refuse renders lie in [0x10000, gotw) *)
Lemma rw_fmts : forall fmt, In fmt REFUSE_ALL_FMTS ->
  0x10000 <= seg_litA_rc fmt /\ seg_litA_rc fmt + Z.of_nat (length fmt) + 1 <= gotwA.
Proof.
assert (Hb : forallb (fun fmt => (0x10000 <=? seg_litA_rc fmt) && (seg_litA_rc fmt + Z.of_nat (length fmt) + 1 <=? gotwA))
  REFUSE_ALL_FMTS = true) by (vm_compute; reflexivity).
intros fmt Hin. pose proof (proj1 (forallb_forall _ _) Hb fmt Hin) as H. cbv beta in H.
apply andb_true_iff in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

Section w.
Context {fx : YK11.FPState}.
Theorem refuse_walk : refuse_contract SEGS B (BASE + AF_refuse) STK_refuse RLO_A RHI_A seg_litA_rc gotwA guardA.
Proof.
unfold refuse_contract.
intros ly S W regs mem md ch c line fp ln rcs f args HPRE HROD H10 Hc64 H11 Hl64 H12 Hf64 HRP HROOM HEV.
exact (rb_head B SM0 SMP TL TLF ML STK_refuse RLO_A RHI_A seg_litA_rc gotwA guardA rw_stk SSPX rw_gw rw_lit34
  (rb_pre B STK_refuse RLO_A RHI_A seg_litA_rc gotwA guardA cr SNP VSNP (rb_ffr SEGS B gotwA)
     (fun fx0 => rb_rel (fx := fx0) B ASF FFL LAWS ML) LAWS rw_obj71 rw_obj72 rw_fmts rw_gw CRP)
  (rb_rel B ASF FFL LAWS ML) ly S W regs mem md ch c line fp ln rcs f args
  (conj HPRE (conj HROD (conj H10 (conj Hc64 (conj H11 (conj Hl64 (conj H12 (conj Hf64 (conj HRP (conj HROOM HEV))))))))))).
Qed.
End w.
End e.
End f.
End d.
