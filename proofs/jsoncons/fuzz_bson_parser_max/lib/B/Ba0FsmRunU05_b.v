(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib MemSplit As0StepLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0RegionPoisoned_b Ba0TlsGetAddr_b Ba0FakeStackGC_b Ba0FakeStackGCC_b
  Ba0Fsm0Gen_b Ba0Fsm5Gen_b Ba0Fsm0Post_b Ba0Fsm5Post_b Ba0Fsm0Run_b Ba0Fsm5Run_b Ba0FsmRunU_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

#[local] Ltac pw e := let v := eval vm_compute in e in change e with v.

Lemma fsm_run_u_0 : fsm_run_u 0 (0x5dc2c : word).
Proof.
  unfold fsm_run_u. intros fx mem0 rom sp ra a0v s tpv md off dtv ent key tsd ctx th tb te F V verb dto blk rec Hs_def Hret Hs Hok Htp Hmd Hoff Hdtv Hent Hkey Htsd Hctx Hth Htbe HF HV Hverb Hdto Hblk Hrec HC0 fs Hfs0 Hr HRfs h j pos ff top botth g40 g35 flag rs gcb Hfs Happm Hshz Hh Hj Hpos_def Hff_def Hng Hssl Hhint HF0 Hprobe Hflag Hwfs HG Hshadow_ok Htop Hth80 HCG HRS Hcol6 Hshok regs H10 H4 H2 H1.
  assert (HFF : ff = (fs + 4096 + 32768 + 0 + 64 * pos)%Z) by (rewrite Hff_def; unfold gc_fr; pw (2 ^ (6 + 0))%Z; lia).
  destruct (@fsm0_run_any fx mem0 rom sp ra a0v s tpv md off dtv ent key tsd ctx th tb te F V verb dto blk rec Hs_def Hret Hs Hok Htp Hmd Hoff Hdtv Hent Hkey Htsd Hctx Hth Htbe HF HV Hverb Hdto Hblk Hrec HC0 fs Hfs0 Hr HRfs h j pos ff top botth g40 g35 flag rs gcb Hfs Happm Hshz Hh Hj Hpos_def HFF Hng Hssl Hhint HF0 Hprobe Hflag Hwfs HG Hshadow_ok Htop Hth80 HCG HRS Hcol6 Hshok regs H10 H4 H2 H1) as (r' & Mf & RUN & Q10 & Q2 & Q1 & KCS & POST).
  exists r', Mf. split; [exact RUN|]. split; [exact Q10|]. split; [exact Q2|]. split; [exact Q1|]. split; [exact KCS|]. exact POST.
Qed.

Lemma fsm_run_u_5 : fsm_run_u 5 (0x5e0dc : word).
Proof.
  unfold fsm_run_u. intros fx mem0 rom sp ra a0v s tpv md off dtv ent key tsd ctx th tb te F V verb dto blk rec Hs_def Hret Hs Hok Htp Hmd Hoff Hdtv Hent Hkey Htsd Hctx Hth Htbe HF HV Hverb Hdto Hblk Hrec HC0 fs Hfs0 Hr HRfs h j pos ff top botth g40 g35 flag rs gcb Hfs Happm Hshz Hh Hj Hpos_def Hff_def Hng Hssl Hhint HF0 Hprobe Hflag Hwfs HG Hshadow_ok Htop Hth80 HCG HRS Hcol6 Hshok regs H10 H4 H2 H1.
  assert (HFF : ff = (fs + 4096 + 32768 + 5242880 + 2048 * pos)%Z) by (rewrite Hff_def; unfold gc_fr; pw (2 ^ (6 + 5))%Z; lia).
  destruct (@fsm5_run_any fx mem0 rom sp ra a0v s tpv md off dtv ent key tsd ctx th tb te F V verb dto blk rec Hs_def Hret Hs Hok Htp Hmd Hoff Hdtv Hent Hkey Htsd Hctx Hth Htbe HF HV Hverb Hdto Hblk Hrec HC0 fs Hfs0 Hr HRfs h j pos ff top botth g40 g35 flag rs gcb Hfs Happm Hshz Hh Hj Hpos_def HFF Hng Hssl Hhint HF0 Hprobe Hflag Hwfs HG Hshadow_ok Htop Hth80 HCG HRS Hcol6 Hshok regs H10 H4 H2 H1) as (r' & Mf & RUN & Q10 & Q2 & Q1 & KCS & POST).
  exists r', Mf. split; [exact RUN|]. split; [exact Q10|]. split; [exact Q2|]. split; [exact Q1|]. split; [exact KCS|]. exact POST.
Qed.

