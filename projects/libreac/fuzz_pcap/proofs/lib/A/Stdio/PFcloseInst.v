From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10 (a Theorem Labs lane, a segment lemma: no function is walked here): the fclose / meter facts that
   lib/A/Prog/PcapEntryInst.v (a working branch 8994a315428) takes as Section hypotheses, stated at its
   instance SK := PcapSinkHeads.asan_sink_head, B := AD2l.PcapB, K := PSourceK.pcap_KS, MT := YCbp.ameter_triv in its
   own terms (SK, B, MT, SEGS, PIp, SEGSp, LOp, HIp below are the instance's Local Notations, text for text), so that
   a caller passes them to pcap_entry_inst by position. Each lemma COMPOSES lemmas that are already proved; none
   re-walks a machine instruction. This file does not Require PcapEntryInst.v, so PcapEntryInst.v can Require it.

   THE POSITIONS OF pcap_entry_inst THIS FILE FILLS, and what goes there:
     FM               inst_FM rc (the donor's lemma, relocated: asrc_file_meter_trivB below).
     ra_fc1, ra_fc2   WFcloseI.WFI_FREE1 = 0x8e2b8, WFcloseI.WFI_JOIN = 0x8e2c0: the two return pcs of musl fclose's
                      two free calls, the names afclose_source_spec_icpt's own conclusion carries. No new Definition:
                      the names exist (WFcloseI.v:87-88; WFclose.v:117-118 has the same two values as WF_FREE1 /
                      WF_JOIN, used by the musl body and met by conversion below). MEASURED by symbol + offset in
                      fuzz_pcap.objdump.txt (sha256 bf9d80d6e30f; internal record):
                        line 98686  000000000008e214 <fclose>:
                        line 98727     8e2b4:  921c40ef  jal 52bd4 <__interceptor_trampoline_free>   fclose+0xa0
                        line 98728     8e2b8:  00040513  mv  a0,s0                                    fclose+0xa4 = ra_fc1
                        line 98729     8e2bc:  919c40ef  jal 52bd4 <__interceptor_trampoline_free>   fclose+0xa8
                        line 98730     8e2c0:  00996533  or  a0,s2,s1                                 fclose+0xac = ra_fc2
                      fclose (0x8e214 .. 0x8e2e0) has no other jal to the free trampoline. They are the rows of
                      ACej.TRACES_fclose (ACej.v:73-75).
     AFCLOSE          inst_AFCLOSE rc (no premise).
     HUfc1, HUfc2     inst_HUfc1, inst_HUfc2 (computation: as_universe PcapB = ACej.Tfib_universe, AD2l.v:43, whose
                      rows [0x52d14; 0x8e2b8] / [0x52d14; 0x8e2c0] are ACej.v:91-92; pc_free_ra0 (as_code PcapB) =
                      0x52d14 is the instance's inst_HFRA).
   mc_lo / mc_hi are not positions any more: the instance binds them to AE39.MC_LO / MC_HI (8994a315428).

   inst_AFCLOSE IS THE COMPOSITION (every premise is discharged by a proved lemma on the base):
     WFcloseI.afclose_source_spec_icpt  fx rc SK PcapB LOp HIp  TB  MUSL                       (WFcloseI.v:279)
       TB    := AD2l.PcapB_syms : AF0m.PcapSyms PcapB                                          (AD2l.v, PcapB_syms)
       MUSL  := WFclose.afclose_source_spec_musl fx rc SK PcapB                               (WFclose.v:1219)
                  SEGS_LOW := PcapBFacts.PcapB_segs_low                                       (PcapBFacts.v:33)
                  ENV      := PcapBFacts.PcapB_env                                            (PcapBFacts.v:51)
                  ML       := PcapBFacts.PcapB_ML                                             (PcapBFacts.v:53)
                  AFREE    := AF0q.pcap_afree_realizes rc fx                                  (AF0q.v:19)
                  K := pcap_KS, HKS := eq_refl
                  ASIL     := fci_ASIL: AD1u.tfib_ASIL at SK := asan_sink_head (AD1u.v:86), the instance's own
                              inst_ASIL proof (PcapEntryInst.v:351-355), restated here so this file does not
                              Require PcapEntryInst.v
                  HSK      := fci_HSK, HWRAPF := fci_HWRAPF, HRA0 := fci_HRA0 (computation)
                  rlo rhi := LOp HIp
                  FFLUSH := WFflush.afflush_source_spec_icpt fx rc SK PcapB TB ASIL MSEEK LOp HIp  (WFflush.v:1118)
                    MSEEK := WMseek.pcap_amseek_rewind fx rc SK PcapB ASIL                    (WMseek.v:246)
   BRIDGES, each settled by conversion (delta, with iota, of named Definitions only; the kernel checks each):
     segments   the walks state their segments as WFclose.wsegs (WFclose.v:40), AB1v.tfibsegs (AB1v.v:13),
                WMseek.msegs, and the instance as SEGSp = pa_segs PI_pcap (PcapEntryTop.v:140-141) and SEGS; every
                one is := Asan.M.loaded_segments.
     entry pc   the walk's IC_ENTRY is AE2e.IC_ENTRY := 0x415cc (AE2e.v:32; PStdioImgA.v no longer defines it, on
                a working branch d3492742814), the instance's is pa_sigma PI_pcap
                PS___interceptor_trampoline_fclose = pcap_sigma .. = 0x415cc (PcapEntryTop.v:145, PcapAddr.v:35).
     rlo / rhi  NO bridge: afclose_source_spec_icpt, afclose_source_spec_musl and afflush_source_spec_icpt are general
                in rlo rhi, so LOp / HIp are passed as they are.
     ra pair    the musl body concludes at WFclose.WF_FREE1 / WF_JOIN, the front takes WFcloseI.WFI_FREE1 / WFI_JOIN:
                both := 0x8e2b8 / 0x8e2c0.
     sink head  AOFL_HEAD at SK := asan_sink_head is sk_ofl_head asan_sink_head = 0x5f4f88 (PcapSinkHeads.v:30) =
                WFclose.WF_OFL_HEAD (WFclose.v:147).
     TL / PcapSyms   NOT NEEDED: the walks' AF0m.PcapSyms PcapB is AD2l.PcapB_syms, a proved lemma on the base; the
                instance's TL : PALib PcapB is not used.
   No Section hypothesis, no axiom, no Admitted. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YG0f YG0d YCbq YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YCbp PcapSinkHeads.
From OSSVerify.libreac.fuzz_pcap.images Require Asan.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require AD2l ACej AF0q AD1u PcapBFacts.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSyms PcapList PcapPa.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapEntryTop.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PSourceK.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require PSourceMeter PFclose WFcloseI WFclose WFflush WMseek.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- The meter law at ameter_triv: RELOCATED, not re-proved. ----
   DONOR: cgif_file_fuzzer's released lib/A/ACke.v:33-34 (origin/ossv/recipes c8557374ad2e, blob 635fd728838d)
     Lemma afile_meter_trivB : forall segs B, afile_meter segs B ameter_triv.
     Proof. intros segs B. constructor; intros; exact I. Qed.
   over the donor's record afile_meter, lib/YC5n.v:24-42 (blob 0eb130c73f3). Changed: the module paths, the names
   afile_meter -> PSourceMeter.asrc_file_meter (lib/A/Stdio/PSourceMeter.v:47, a copy of the donor's record) and
   afile_meter_trivB -> asrc_file_meter_trivB, and SK passed by position. The two records' fields are the same text
   except names; the two differences from the donor, both ruled not beyond names for this relocation (a Theorem Labs lane, 12:2xZ):
     (1) the donor's record has `Context {SK}` (implicit), pcap's has `Context (SK)` (explicit,
         PSourceMeter.v:41), so SK is a Variable here and is passed by position;
     (2) the donor's FILE_BLOCK = 1264 (cgif lib/YE00.v:12) is pcap's SRC_FILE_BLOCK = 1304 (PSource.v:57, pcap's
         measured block). At ameter_triv every field's conclusion is True, so the block size never enters the proof.
   The donor's unused Section variables K : asink_syms and XN : xnums are parameters of neither record. *)
Section fm. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Lemma asrc_file_meter_trivB : forall segs B, @PSourceMeter.asrc_file_meter rc SK segs B YCbp.ameter_triv.
Proof. intros segs B. constructor; intros; exact I. Qed.
End fm.

Section inst.
Context {rc : YM05.RunCeil}.
(* PcapEntryInst.v's Local Notations, text for text. *)
Local Notation SK := PcapSinkHeads.asan_sink_head.
Local Notation B := AD2l.PcapB.
Local Notation MT := YCbp.ameter_triv.
Local Notation SEGS := Asan.M.loaded_segments.
Local Notation PIp := (@PcapEntryTop.PI_pcap rc).
Local Notation SEGSp := (@pa_segs rc pcap_listing PIp).
Local Notation LOp := (@pa_relro_lo rc pcap_listing PIp).
Local Notation HIp := (@pa_relro_hi rc pcap_listing PIp).

(* ---- FM ---- *)
Lemma inst_FM : @PSourceMeter.asrc_file_meter rc SK SEGSp B MT.
Proof. exact (@asrc_file_meter_trivB rc SK SEGSp B). Qed.

(* ---- The musl body's image side conditions at SK, PcapB, pcap_KS. ---- *)
(* ASIL: the instance's inst_ASIL, same term (PcapEntryInst.v:348-355): AD1u.tfib_ASIL with pcap_head SK by
   computation (sk_ofl_head asan_sink_head = 0x5f4f88, AD1u.v:54, PcapSinkHeads.v:30). *)
Lemma fci_ASIL : asource_img_laws SK SEGS B pcap_KS.
Proof.
  (* conversion: AB1v.tfibsegs = Asan.M.loaded_segments (AB1v.v:13) *)
  exact (AD1u.tfib_ASIL (SK := PcapSinkHeads.asan_sink_head) (PH := eq_refl) B AD2l.PcapB_syms).
Qed.
(* HSK: AOFL_HEAD = sk_ofl_head asan_sink_head = 0x5f4f88 = WFclose.WF_OFL_HEAD (YCbq.v:84, PcapSinkHeads.v:30). *)
Lemma fci_HSK : @YCbq.AOFL_HEAD SK = WFclose.WF_OFL_HEAD.
Proof. reflexivity. Qed.
(* HWRAPF / HRA0: PcapB's code table is AF0m.Tfib_code (AD2l.v:19); by computation, as the instance's inst_HFRA. *)
Lemma fci_HWRAPF : pc_wrap_free (as_code B) = WFclose.WF_FREETR.
Proof. reflexivity. Qed.
Lemma fci_HRA0 : pc_free_ra0 (as_code B) = (symaddr (Symbols.Asan.s___interceptor_free + 0x138)%Z).
Proof. reflexivity. Qed.

(* ---- AFCLOSE ---- *)
Lemma inst_AFCLOSE : forall fx : YK11.FPState,
  @PFclose.afclose_source_spec fx rc SK SEGSp B pcap_KS
    (@pa_sigma rc pcap_listing PIp PS___interceptor_trampoline_fclose) WFcloseI.WFI_FREE1 WFcloseI.WFI_JOIN LOp HIp.
Proof.
  intros fx.
  (* conversion: AB1v.tfibsegs (AB1v.v:13) = pa_segs PI_pcap (PcapEntryTop.v:140-141) = Asan.M.loaded_segments, and
     AE2e.IC_ENTRY = 0x415cc (AE2e.v:32) = pa_sigma PI_pcap PS___interceptor_trampoline_fclose (PcapEntryTop.v:145,
     PcapAddr.v:35), in the conclusion. Inside: WFclose.wsegs / WMseek.msegs / AB1v.tfibsegs = Asan.M.loaded_segments
     at the ASIL, SEGS_LOW, ENV and AFREE arguments, and WFclose.WF_FREE1 / WF_JOIN = WFcloseI.WFI_FREE1 / WFI_JOIN
     (0x8e2b8 / 0x8e2c0) at the musl body. *)
  exact (@WFcloseI.afclose_source_spec_icpt fx rc SK B LOp HIp AD2l.PcapB_syms
    (@WFclose.afclose_source_spec_musl fx rc SK B PcapBFacts.PcapB_segs_low PcapBFacts.PcapB_env PcapBFacts.PcapB_ML
       (AF0q.pcap_afree_realizes rc fx) pcap_KS fci_ASIL eq_refl fci_HSK fci_HWRAPF fci_HRA0 LOp HIp
       (@WFflush.afflush_source_spec_icpt fx rc SK B AD2l.PcapB_syms fci_ASIL
          (@WMseek.pcap_amseek_rewind fx rc SK B fci_ASIL) LOp HIp))).
Qed.

(* ---- HUfc1 / HUfc2: by computation on the trace universe (ACej.v:91-92). ---- *)
Lemma inst_HUfc1 : In [pc_free_ra0 (as_code B); WFcloseI.WFI_FREE1] (as_universe B).
Proof.
  rewrite AD2l.PcapB_universe, fci_HRA0. unfold WFcloseI.WFI_FREE1, ACej.Tfib_universe.
  repeat first [left; reflexivity | right].
Qed.
Lemma inst_HUfc2 : In [pc_free_ra0 (as_code B); WFcloseI.WFI_JOIN] (as_universe B).
Proof.
  rewrite AD2l.PcapB_universe, fci_HRA0. unfold WFcloseI.WFI_JOIN, ACej.Tfib_universe.
  repeat first [left; reflexivity | right].
Qed.

End inst.

(* The closed statements, as a caller passes them to pcap_entry_inst. *)
About asrc_file_meter_trivB.
About inst_FM.
About inst_AFCLOSE.
About inst_HUfc1.
About inst_HUfc2.
Check (@inst_FM : forall {rc : YM05.RunCeil},
  @PSourceMeter.asrc_file_meter rc PcapSinkHeads.asan_sink_head (@pa_segs rc pcap_listing (@PcapEntryTop.PI_pcap rc))
    AD2l.PcapB YCbp.ameter_triv).
Check (@inst_AFCLOSE : forall {rc : YM05.RunCeil} (fx : YK11.FPState),
  @PFclose.afclose_source_spec fx rc PcapSinkHeads.asan_sink_head (@pa_segs rc pcap_listing (@PcapEntryTop.PI_pcap rc))
    AD2l.PcapB pcap_KS (@pa_sigma rc pcap_listing (@PcapEntryTop.PI_pcap rc) PS___interceptor_trampoline_fclose)
    WFcloseI.WFI_FREE1 WFcloseI.WFI_JOIN
    (@pa_relro_lo rc pcap_listing (@PcapEntryTop.PI_pcap rc)) (@pa_relro_hi rc pcap_listing (@PcapEntryTop.PI_pcap rc))).
Check (inst_HUfc1 : In [pc_free_ra0 (as_code AD2l.PcapB); WFcloseI.WFI_FREE1] (as_universe AD2l.PcapB)).
Check (inst_HUfc2 : In [pc_free_ra0 (as_code AD2l.PcapB); WFcloseI.WFI_JOIN] (as_universe AD2l.PcapB)).

Print Assumptions asrc_file_meter_trivB.
Print Assumptions fci_ASIL.
Print Assumptions fci_HSK.
Print Assumptions fci_HWRAPF.
Print Assumptions fci_HRA0.
Print Assumptions inst_FM.
Print Assumptions inst_AFCLOSE.
Print Assumptions inst_HUfc1.
Print Assumptions inst_HUfc2.
