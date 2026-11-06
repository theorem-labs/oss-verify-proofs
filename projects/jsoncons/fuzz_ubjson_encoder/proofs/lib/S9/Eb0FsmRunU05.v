(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib MemSplit As0StepLib Eb0RegionPoisoned Eb0TlsGetAddr Eb0FakeStackGC Eb0FakeStackGCC
  Eb0Fsm0Gen Eb0Fsm5Gen Eb0Fsm0Post Eb0Fsm5Post Eb0Fsm0Run Eb0Fsm5Run Eb0Fsm2Gen Eb0Fsm2Post Eb0Fsm2Run Eb0FsmRunU.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

#[local] Ltac pw e := let v := eval vm_compute in e in change e with v.

Lemma fsm_run_u_0 : fsm_run_u 0 (0x5ec3c : word).
Proof.
  unfold fsm_run_u. intros fx mem0 rom sp ra a0v s tpv md off dtv ent key tsd ctx th tb te F V verb dto blk rec Hs_def Hret Hs Hok Htp Hmd Hoff Hdtv Hent Hkey Htsd Hctx Hth Htbe HF HV Hverb Hdto Hblk Hrec HC0 fs Hfs0 Hr HRfs h j pos ff top botth g40 g35 flag rs gcb Hfs Happm Hshz Hh Hj Hpos_def Hff_def Hng Hssl Hhint HF0 Hprobe Hflag Hwfs HG Hshadow_ok Htop Hth80 HCG HRS Hcol6 Hshok regs H10 H4 H2 H1.
  assert (HFF : ff = (fs + 4096 + 32768 + 0 + 64 * pos)%Z) by (rewrite Hff_def; unfold gc_fr; pw (2 ^ (6 + 0))%Z; lia).
  destruct (@fsm0_run_any fx mem0 rom sp ra a0v s tpv md off dtv ent key tsd ctx th tb te F V verb dto blk rec Hs_def Hret Hs Hok Htp Hmd Hoff Hdtv Hent Hkey Htsd Hctx Hth Htbe HF HV Hverb Hdto Hblk Hrec HC0 fs Hfs0 Hr HRfs h j pos ff top botth g40 g35 flag rs gcb Hfs Happm Hshz Hh Hj Hpos_def HFF Hng Hssl Hhint HF0 Hprobe Hflag Hwfs HG Hshadow_ok Htop Hth80 HCG HRS Hcol6 Hshok regs H10 H4 H2 H1) as (r' & Mf & RUN & Q10 & Q2 & Q1 & KCS & POST).
  exists r', Mf. split; [exact RUN|]. split; [exact Q10|]. split; [exact Q2|]. split; [exact Q1|]. split; [exact KCS|]. exact POST.
Qed.

Lemma fsm_run_u_5 : fsm_run_u 5 (0x5f288 : word).
Proof.
  unfold fsm_run_u. intros fx mem0 rom sp ra a0v s tpv md off dtv ent key tsd ctx th tb te F V verb dto blk rec Hs_def Hret Hs Hok Htp Hmd Hoff Hdtv Hent Hkey Htsd Hctx Hth Htbe HF HV Hverb Hdto Hblk Hrec HC0 fs Hfs0 Hr HRfs h j pos ff top botth g40 g35 flag rs gcb Hfs Happm Hshz Hh Hj Hpos_def Hff_def Hng Hssl Hhint HF0 Hprobe Hflag Hwfs HG Hshadow_ok Htop Hth80 HCG HRS Hcol6 Hshok regs H10 H4 H2 H1.
  assert (HFF : ff = (fs + 4096 + 32768 + 5242880 + 2048 * pos)%Z) by (rewrite Hff_def; unfold gc_fr; pw (2 ^ (6 + 5))%Z; lia).
  destruct (@fsm5_run_any fx mem0 rom sp ra a0v s tpv md off dtv ent key tsd ctx th tb te F V verb dto blk rec Hs_def Hret Hs Hok Htp Hmd Hoff Hdtv Hent Hkey Htsd Hctx Hth Htbe HF HV Hverb Hdto Hblk Hrec HC0 fs Hfs0 Hr HRfs h j pos ff top botth g40 g35 flag rs gcb Hfs Happm Hshz Hh Hj Hpos_def HFF Hng Hssl Hhint HF0 Hprobe Hflag Hwfs HG Hshadow_ok Htop Hth80 HCG HRS Hcol6 Hshok regs H10 H4 H2 H1) as (r' & Mf & RUN & Q10 & Q2 & Q1 & KCS & POST).
  exists r', Mf. split; [exact RUN|]. split; [exact Q10|]. split; [exact Q2|]. split; [exact Q1|]. split; [exact KCS|]. exact POST.
Qed.

Lemma fsm_run_u_2 : fsm_run_u 2 (0x5ef40 : word).
Proof.
  unfold fsm_run_u. intros fx mem0 rom sp ra a0v s tpv md off dtv ent key tsd ctx th tb te F V verb dto blk rec Hs_def Hret Hs Hok Htp Hmd Hoff Hdtv Hent Hkey Htsd Hctx Hth Htbe HF HV Hverb Hdto Hblk Hrec HC0 fs Hfs0 Hr HRfs h j pos ff top botth g40 g35 flag rs gcb Hfs Happm Hshz Hh Hj Hpos_def Hff_def Hng Hssl Hhint HF0 Hprobe Hflag Hwfs HG Hshadow_ok Htop Hth80 HCG HRS Hcol6 Hshok regs H10 H4 H2 H1.
  assert (HFF : ff = (fs + 4096 + 32768 + 2097152 + 256 * pos)%Z) by (rewrite Hff_def; unfold gc_fr; pw (2 ^ (6 + 2))%Z; lia).
  destruct (@fsm2_run_any fx mem0 rom sp ra a0v s tpv md off dtv ent key tsd ctx th tb te F V verb dto blk rec Hs_def Hret Hs Hok Htp Hmd Hoff Hdtv Hent Hkey Htsd Hctx Hth Htbe HF HV Hverb Hdto Hblk Hrec HC0 fs Hfs0 Hr HRfs h j pos ff top botth g40 g35 flag rs gcb Hfs Happm Hshz Hh Hj Hpos_def HFF Hng Hssl Hhint HF0 Hprobe Hflag Hwfs HG Hshadow_ok Htop Hth80 HCG HRS Hcol6 Hshok regs H10 H4 H2 H1) as (r' & Mf & RUN & Q10 & Q2 & Q1 & KCS & POST).
  exists r', Mf. split; [exact RUN|]. split; [exact Q10|]. split; [exact Q2|]. split; [exact Q1|]. split; [exact KCS|]. exact POST.
Qed.

