(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): segment B3 of reac_segconf_parse_file
   (0x87e38), lib/B/Prog/pf_pieces.v's S_B3. The B3 segment lane of the image-B G3 walk owner, 2026-10-30.

    proves segment B3 of function reac_segconf_parse_file (reuse search, rule 24: origin/main 6e24fa4d602c, origin/ossv/recipes 3abc3740de97, origin/ossv/candidates ee89628c9971, origin/release/pau-projects-recipes b6a0088adcb4, the earlier proof delivery and the working heads, image-B address 0x87e38; output confirmed; the result is recorded with the commissioning brief)
   Verdict: none released; ADAPTED from the image-A G3 walk owner's image-A segment walks (a working branch's pf_a3_f.v,
   a working branch's pf_a2.v / pf_a2_g.v / pf_a5_k.v / pf_a8b_t.v) and the unit owner's UBSan piece walks
   (commit 04f2be60e018's lib/Prog/pfA_facts.v, Required: pf_lctx_start, L_parse_start_holds,
   pf_cnt_start), re-derived on image B's code
   (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s). Closed against G3 FINAL at 6f783602b5e3 (the contract
   lib/B/Prog/reac_segconf_parse_file_c.v, the B-kit copies at 694f3575dda2).

   The segment (PLAN-pf-asanubsan.md section 5.2, row B3): FRAME 0x88074 -> DONE 0x89114 (the empty text) or HEAD
   0x881f8 (the first line); 0x88074-0x881f8 (97 instructions) + cold 0x891cc-0x891f8 (11) = 108, 9 conditional
   branches. 97 of the 108 lie on a path the walk follows; the other 11 are behind branches the walk refutes:
   0x8807c and 0x8808c (`j unimp`, T01 / T02), 0x88108 (`j` to the text-NULL return 0x89144: t <> 0), check B#1's
   slow path 0x891cc-0x891e0 (6: the shadow byte of c->gen's granule is 0), check B#2's error stub 0x891f0-0x891f4
   (2: saddr_ok). The pieces:
     piece 1 (pf_seg_B3_p1.v): FRAME -> snprintf(c->reading, 96, "%s", label ? label : "reac-pw.conf") 0x880cc
       -> MID1 0x880d0. UBSan traps T01 (0x88078 `bnez a0` on c, else 0x8807c `j unimp`) and T02 (0x88088
       `beqz a0` on c & 7, else 0x8808c `j unimp`): both branches decided by the seed's fact on c (pf_tf: c <> 0,
       c mod 16 = 0; 16 <= c <= 2 ^ 64 - 16 from reader_pre and the block c's bounds).
     piece 2 (pf_seg_B3_p2.v): MID1 -> check B#1 (load4 of c->gen, 0x880d0 .. 0x880dc; the granule is
       addressable: sa_addr c SEG_C_SIZE) -> c->gen++ -> the text-NULL test 0x88104 (decided: t <> 0) -> cur_name in
       scope -> memset(cur_name, 0, 16) 0x88130 -> MID2 0x88134.
     piece 3 (pf_seg_B3_p3.v): MID2 -> check B#2 (load1 of *t, 0x88134 .. 0x88140 and the cold slow path 0x891e4
       `andi a1,s11,7; bge a1,a0` whose error arm is refuted by saddr_ok t s: sa_addr t (|s| + 1)) -> 0x88148.
     piece 4 (pf_seg_B3_p4.v): 0x88148 -> `bnez a0` 0x88158: t[0] = 0 -> DONE (s = []), else the setup slots
       0x88160 .. 0x881f4 -> HEAD with n = length s.
   Checks: B#1, B#2 (2 of 41). Traps: T01, T02 (2 of 34). Calls: snprintf 0x880cc, memset 0x88130.

   Section hypotheses (the ones pf_pieces.v names for B3's calls, at every FP state, and the listing's objects):
   - ASNPRINTF: RtFormat.asnprintf_realizes at pa_sigma SS___interceptor_trampoline_snprintf, gotwA, guardA;
   - AMEMSET: aintrin_realizes OSet at pa_sigma SS___asan_memset;
   - OBJ: B's SegObj seg_val_objs (the listing objects 34 .str.1 "reac-pw.conf", 35 .str "%s", 36 .str.3, 37 .str.2
     at their image addresses). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal
SegSyms SegList SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaSB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtPFPf RtPFShared RtPFSx RtPFCmd RtFormat.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_seg_B3_f pf_seg_B3_t pf_seg_B3_k pf_seg_B3_p1 pf_seg_B3_p2 pf_seg_B3_p3 pf_seg_B3_p4.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YO0a YO0c YI08.
Import ListNotations.
Open Scope Z_scope.

Section s. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
Variable B : asyms.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  @RtFormat.asnprintf_realizes fx0 rc SEGS B (pa_sigma SS___interceptor_trampoline_snprintf) gotwA guardA.
Hypothesis AMEMSET : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OSet (pa_sigma SS___asan_memset).
Hypothesis OBJ : seg_val_objs (PI := PI).

(* the post at the FP state the snprintf returned is the post at the segment's entry FP state: apost_baseF's two FP
   clauses compose with the call's fxrel (PaFx.v fxrel_trans's argument) *)
Lemma pb3_post_fx : forall (f0 fx1 : YK11.FPState) v W cfg, fxrel f0 fx1 ->
  SRr SEGS W cfg (@PF_POST fx1 rc SK PI B v) -> SRr SEGS W cfg (@PF_POST f0 rc SK PI B v).
Proof.
intros f0 fx1 v W cfg [R1 C1] H. eapply SRr_mono; [exact H|]. intros W' c' _ HQ.
unfold PF_POST, apost_baseF in *.
destruct HQ as (fx' & ly' & S' & regs' & mem' & md' & Hc & HR & HC & HR3).
exists fx', ly', S', regs', mem', md'. split; [exact Hc|].
split; [intros k Hk; rewrite (HR k Hk); exact (R1 k Hk)|].
split; [|exact HR3].
destruct HC as [E | Z1]; [destruct C1 as [E1 | Z0]; [left; rewrite E; exact E1 | right; rewrite E; exact Z0] | right; exact Z1].
Qed.

Theorem S_B3_holds : S_B3 B.
Proof.
intros f0 HH HD v pos lyc Sc Wc rX memc mdc HI.
pose proof (pb3_FA_of_frame B (fx := f0) v pos lyc Sc Wc rX memc mdc HI) as HFA.
apply (pb3_s1 B ASNPRINTF OBJ (fx := f0) v pos lyc Sc Wc rX memc mdc _ HI).
intros fx1 rX1 memc1 mdc1 Hfx HF1 HM1.
apply (pb3_post_fx f0 fx1 v Wc _ Hfx).
apply (pb3_s2 B AMEMSET (fx := fx1) v pos lyc Sc Wc memc rX1 memc1 mdc1 _ HFA HM1).
intros rX2 memc2 mdc2 HM2.
apply (pb3_s3a B (fx := fx1) v pos lyc Sc Wc memc rX2 memc2 mdc2 _ HFA HM2).
intros rX3 memc3 mdc3 HM3.
exact (pb3_s3b B OBJ (fx := fx1) v pos lyc Sc Wc memc rX3 memc3 mdc3 HF1 HFA HM3 HH HD).
Qed.
End s.
