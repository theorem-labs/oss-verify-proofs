(* The walk of m_refuse on fuzz_segconf.asan-ubsan (image B, pin sha256 c3796c0b38f3..., entry 0x8782c, 416 bytes,
   104 instructions, a 48-byte frame, no side-stack frame): m_refuse_contract of lib/B/Prog/m_refuse_c.v at image B's
   numbers (lib/B/Prog/SegInstB.v), the text the image-B m_file segment table's m_refuse row names, in plugin-hostd/fuzz_command's
   lib/A/Prog form (afn_pre at the entry, SRr of apost_baseF at the return, over `Context {PI : PAImg seg_listing}`).
   ADAPTATION: see lib/B/Prog/m_refuse_k.v's header for the templates and the code.

   The walk is cut where the code branches on the contract's data (lib/B/Prog/m_refuse_k.v MR_ARM):
     n_kept = 8        m_refuse_k.v mr_arm_full   (the blt at 0x87884 is taken: only refused++)
     n_kept < 8, line = 0  m_refuse_l0.v mr_arm_kept0  (snprintf(kept[n_kept], 112, "%s: ", c->reading) at 0x8791c)
     n_kept < 8, line > 0  m_refuse_ln.v mr_arm_keptL  (snprintf(kept[n_kept], 112, "%s:%d: ", c->reading, line) at 0x878d0)
   The six UBSan trap branches to `unimp` 0x87978, each refuted at its branch: 0x87848 `bnez a2` (a2 = c & 3; c's
   16-alignment fact), 0x87890 `bgeu a1,9` and 0x878dc `bltu 8,a1` (the n_kept fact 0 <= n_kept <= 7 from
   mconf_encp's u32_enc and the kept list's length), 0x878b0 / 0x878fc `bltu a3,a1` (the address of kept[n_kept]
   does not wrap: m_refuse_k.v mr_ub_wrap, from c + 9236 <= alloc_ceiling), 0x87930 `blt a0,a1` (n_kept + 1 <= 8, no
   signed overflow; the n_kept fact). The four instrumented checks (n_kept's 4-byte load at 0x87874, re-checked at
   0x87920 and before its store at 0x87934, and refused's at 0x87948) are decided by the two shadow entries mr_SH
   (the 4 bytes of each counter, addressable by the contract's sa_addr over the whole 9236-byte block): no error path
   (a call of errpath_load4 / errpath_store4) is reached.
   Section hypotheses: TL (PALib B), VOBJS (seg_val_objs), SNP (the snprintf wrapper, the image-B m_file segment table's row). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaArt PaArtOwn PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtPFPf RtPFShared RtPFCmd RtPFSeg RtAPI.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_refuse_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require m_refuse_f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_refuse_k m_refuse_l0 m_refuse_ln.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module SM := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec.SegModel.
Module MF := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog.m_refuse_f.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
Section e.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SNP : forall fx0 : YK11.FPState,
  @RtPFSeg.seg_asnprintf_realizes fx0 rc SEGS B RtPFCmd.CMD_IMG_LO RtPFCmd.CMD_IMG_HI RtPFCmd.CMD_SNP_CR
    (SIGMA SS___interceptor_trampoline_snprintf) RtPFCmd.CMD_GOTW RtAPI.A_SSP_GUARD.

Theorem m_refuse_walkB :
m_refuse_contract SEGS B (BASE + AF_m_refuse) SegInstB.STK_m_refuse SegInstB.RLO_A SegInstB.RHI_A
  SegInstB.seg_litA_fz SegInstB.gotwA SegInstB.guardA.
Proof.
unfold m_refuse_contract.
intros ly S W regs mem md ch c line mc knock HPRE HROD H10 Hc64 H11 HP HEV.
(* the stack-protector cells: SegInstB's names and RtPFCmd's / RtAPI's are the same two image numbers *)
assert (EG : SegInstB.gotwA = RtPFCmd.CMD_GOTW) by (vm_compute; reflexivity).
assert (EU : SegInstB.guardA = RtAPI.A_SSP_GUARD) by (vm_compute; reflexivity).
rewrite EG, EU in HP.
pose proof HP as (_ & _ & _ & _ & HMC & _ & Hline & _).
destruct (MF.mr_fields knock _ c mc HMC) as (Hk8 & _).
pose proof (mr_arm_full (fx := fx) (rc := rc) (SK := SK) (PI := PI) B TL VOBJS) as AF.
pose proof (mr_arm_kept0 (fx := fx) (rc := rc) (SK := SK) (PI := PI) B TL VOBJS SNP) as A0.
pose proof (mr_arm_keptL (fx := fx) (rc := rc) (SK := SK) (PI := PI) B TL VOBJS SNP) as AL.
unfold MR_FULL_stmt, MR_KEPT0_stmt, MR_KEPTL_stmt, MR_ARM, mr_Q in AF, A0, AL.
destruct (Nat.eq_dec (length (SM.mc_kept mc)) 8) as [H8 | H8].
- exact (AF ly S W regs mem md ch c line mc knock HPRE HROD H10 Hc64 H11 HP H8).
- destruct (Z.eq_dec line 0) as [Hl0 | Hl0].
  + assert (P0 : line = 0 /\ (length (SM.mc_kept mc) < 8)%nat) by (split; [exact Hl0 | lia]).
    exact (A0 ly S W regs mem md ch c line mc knock HPRE HROD H10 Hc64 H11 HP P0).
  + assert (PL : 0 < line /\ (length (SM.mc_kept mc) < 8)%nat) by (split; lia).
    exact (AL ly S W regs mem md ch c line mc knock HPRE HROD H10 Hc64 H11 HP PL).
Qed.
(* inside the Sections: the walk's hypotheses as its assumptions *)
About m_refuse_walkB.
Print Assumptions m_refuse_walkB.
End e.
End f.
End d.
About m_refuse_walkB.
Print Assumptions m_refuse_walkB.
