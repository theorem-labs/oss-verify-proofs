(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10 (a Theorem Labs lane, a segment lemma: no function is walked here): the lib/B twin of
   lib/A/Stdio/PFcloseInst.v (a working branch c35658def122). It states the fclose / meter facts that the
   asan-ubsan top lib/B/Prog/PcapEntryTop.v (Section top, a working branch 5811b4315d4) takes as Section
   hypotheses, at the asan-ubsan instance:
     SK := PcapSinkHeads.asan_ubsan_sink_head (sk_ofl_head 0x5f4e88; lib/B/PcapDriver.v pcap_drv_SK),
     B  := YD2l.PcapB (the asan-ubsan core's symbol record, a working branch ef393153661),
     K  := lib/B/Stdio/PSourceK.pcap_KS (KS_U),
     MT := YCbp.ameter_triv,
   the instance at which Reusable/YD2o.v (pcap_drv_mainX_rc) and lib/B/PcapDriver.v (LIBX) take
   PcapEntry.tfib_lib_contract_x_all_B. Each lemma COMPOSES lemmas that are already proved; none re-walks a machine
   instruction.

   THE IMAGE TERMS. The top writes segs / entry / relro through its instance PI_pcap (PcapEntryTop.v:144-161):
     PSEGS = pa_segs PI_pcap                                   pa_segs     := AsanUbsan.M.loaded_segments
     pa_sigma PI_pcap PS___interceptor_trampoline_fclose       pa_sigma    := PcapAddr.pcap_sigma
     RLOp / RHIp = pa_relro_lo / pa_relro_hi PI_pcap           pa_relro_lo := PcapRelro.PCAP_RLO,
                                                               pa_relro_hi := PcapRelro.PCAP_RHI
   This file states its lemmas at those field values, by name. A position of Section top takes them by conversion
   (iota of PI_pcap's projections; the scratch check of the RESULT runs @PcapEntryTop.pcap_entry_top on them). This
   file does not Require PcapEntryTop.v, so PcapEntryTop.v, or an instance file, can Require this file.

   THE POSITIONS OF PcapEntryTop.v's Section top THIS FILE FILLS (a Theorem Labs lane's), and what goes there:
     AFM              inst_FM_U rc (the donor's lemma, relocated: asrc_file_meter_trivB below).
     ra_fc1, ra_fc2   WFcloseI.WFI_FREE1, WFcloseI.WFI_JOIN: the two return pcs of musl fclose's two free calls,
                      the names pcapu_afclose_source_spec_icpt's conclusion carries (lib/B/Stdio/WFcloseI.v; the
                      musl body names the same two values WFclose.WF_FREE1 / WF_JOIN). A Theorem Labs lane measured the same two
                      values (RA_FC1_U / RA_FC2_U, on pin 9e66f771). No new Definition: the names exist.
     AFCLOSE          inst_AFCLOSE_U rc (no premise).
     HUfc1, HUfc2     inst_HUfc1_U, inst_HUfc2_U: YCejSites.fclose_free_in, by conversion (as_universe PcapB is
                      YCej.Tfib_universe, pc_free_ra0 (as_code PcapB) is WFclose.WF_FREE_RA0).

   inst_AFCLOSE_U IS THE COMPOSITION (every premise is discharged by a proved lemma):
     WFcloseI.pcapu_afclose_source_spec_icpt fx rc SK PcapB rlo rhi TB MUSL                   (WFcloseI.v:445)
       TB    := YD2l.TfibB_syms : YF0m.PcapSyms PcapB                                          (YD2l.v:71)
       MUSL  := WFclose.pcapu_afclose_source_spec_musl fx rc SK PcapB                          (WFclose.v:1367)
                  ENV   := fcu_ENV: YCeh.tl_env at lib/B/PcapBFacts.v PcapB_lib (the lib/B twin of pcap's
                           lib/A/PcapBFacts.v PcapB_lib / PcapB_env, at the asan-ubsan PcapB)
                  ML    := fcu_ML: YG05.model_laws_ok at YF0m.ts_universe (pcap's PcapBFacts.PcapB_ML, restated)
                  AFREE := YF0q.afree_realizes_closed PcapB TfibB_syms (fun _ => eq_refl) (as AF0q.v's
                           pcap_afree_realizes; as_dhash PcapB is tfib_dhash, YD2l.v:31)
                  K := pcap_KS, HKS := eq_refl
                  ASIL  := fcu_ASIL: YD1u.tfib_ASIL at SK := asan_ubsan_sink_head (YD1u.v:87; its pcap_head
                           class by eq_refl, sk_ofl_head asan_ubsan_sink_head = 0x5f4e88)
                  HSK / HWRAPF / HRA0 := fcu_HSK / fcu_HWRAPF / fcu_HRA0 (computation)
                  rlo rhi := PCAP_RLO PCAP_RHI
                  FFLUSH := WFflush.pcapu_afflush_source_spec_icpt fx rc SK PcapB TB ASIL MSEEK     (WFflush.v:1231)
                    MSEEK := WMseek.pcapu_amseek_rewind fx rc SK PcapB ASIL                     (WMseek.v:278)
   BRIDGES, each settled by conversion (delta, with iota, of named Definitions only; the kernel checks each):
     segments   the walks state YB1v.tfibsegs, WFclose.wsegs, WFflush's YB1v.tfibsegs and WMseek.msegs; each one
                is := AsanUbsan.M.loaded_segments, the top's PSEGS.
     entry pc   the front concludes at PStdioImgB.IC_ENTRY_U := YE2e.IC_ENTRY = 0x4161c; PcapAddr.pcap_sigma
                PS___interceptor_trampoline_fclose = 0x4161c (lib/B/Prog/PcapAddr.v:38).
     ra pair    the musl body concludes at WFclose.WF_FREE1 / WF_JOIN, the front takes WFcloseI.WFI_FREE1 /
                WFI_JOIN: both pairs are := 0x8e184 / 0x8e18c.
     rlo / rhi  no bridge: the three walks are general in rlo rhi.
   No Section hypothesis, no axiom, no Admitted. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YG00 YG0f YG0d YCbq YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YCbp PcapSinkHeads YG05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YB1v YF0m YCej YCejSites YCeh YD2l YF0q YD1u.
From OSSVerify.libreac.fuzz_pcap.images Require AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require PSourceMeter PFclose.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Stdio Require Import PSourceK.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Stdio Require WFcloseI WFclose WFflush WMseek.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B Require PcapBFacts.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSyms PcapAddr PcapRelro.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- The meter law at ameter_triv: RELOCATED, not re-proved. ----
   DONOR: cgif_file_fuzzer's asan-ubsan copy lib/YCke.v:26-27 (origin/ossv/recipes c8557374ad2e, blob d3aaaad6bd5b;
   its ASan copy is lib/A/ACke.v:33-34, the donor of lib/A/Stdio/PFcloseInst.v's asrc_file_meter_trivB)
     Lemma afile_meter_trivB : forall segs B, afile_meter segs B ameter_triv.
     Proof. intros segs B. constructor; intros; exact I. Qed.
   over the donor's record afile_meter, lib/YC5n.v:24-42 (blob 0eb130c73f3). Changed: the module paths, the names
   afile_meter -> PSourceMeter.asrc_file_meter (lib/A/Stdio/PSourceMeter.v:47, the image-generic copy of the donor's
   record) and afile_meter_trivB -> asrc_file_meter_trivB, and SK passed by position. The same two differences from
   the donor as in lib/A/Stdio/PFcloseInst.v, neither beyond names (a Theorem Labs lane, 12:2xZ):
     (1) the donor's record has `Context {SK}`, pcap's has `Context (SK)` (a Theorem Labs lane,
         PSourceMeter.v:37-41), so SK is a Variable here and is passed by position;
     (2) the donor's FILE_BLOCK is cgif's block size, pcap's is SRC_FILE_BLOCK (PSource.v). At ameter_triv every
         field's conclusion is True, so the block size never enters the proof.
   The proof reads no image: the lemma holds at every segs and B. *)
Section fm. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Lemma asrc_file_meter_trivB : forall segs B, @PSourceMeter.asrc_file_meter rc SK segs B YCbp.ameter_triv.
Proof. intros segs B. constructor; intros; exact I. Qed.
End fm.

(* ---- The library facts of the asan-ubsan PcapB: TAKEN FROM lib/B/PcapBFacts.v, not restated. ----
   lib/B/PcapBFacts.v (a working branch c4b2695e96b) states PcapB_lib : YCeh.TfibLib YD2l.PcapB, the same
   statement this file held as a local fcu_lib while no lib/B facts file existed. That local copy is gone; every
   position below takes PcapBFacts.PcapB_lib. *)
(* ENV: lib/A/PcapBFacts.v:51 PcapB_env, at the asan-ubsan record. *)
Definition fcu_ENV : api_env YB1v.tfibsegs YD2l.PcapB := YCeh.tl_env YD2l.PcapB PcapBFacts.PcapB_lib.
(* ML: lib/A/PcapBFacts.v:53-54 PcapB_ML, at the asan-ubsan record. *)
Lemma fcu_ML : model_laws (as_universe YD2l.PcapB).
Proof. exact (YG05.model_laws_ok (as_universe YD2l.PcapB) (YF0m.ts_universe YD2l.PcapB YD2l.TfibB_syms)). Qed.

Section inst.
Context {rc : YM05.RunCeil}.
(* The instance, by name (as #[local] Abbreviations, the form PcapEntryTop.v uses). *)
#[local] Abbreviation SK := PcapSinkHeads.asan_ubsan_sink_head.
#[local] Abbreviation B := YD2l.PcapB.
#[local] Abbreviation MT := YCbp.ameter_triv.
#[local] Abbreviation SEGS := AsanUbsan.M.loaded_segments.

(* ---- AFM ---- *)
Lemma inst_FM_U : @PSourceMeter.asrc_file_meter rc SK SEGS B MT.
Proof. exact (@asrc_file_meter_trivB rc SK SEGS B). Qed.

(* ---- The musl body's image side conditions at SK, PcapB, pcap_KS. ---- *)
(* ASIL: YD1u.tfib_ASIL with its pcap_head class at SK by computation (sk_ofl_head asan_ubsan_sink_head = 0x5f4e88,
   YD1u.v:59, PcapSinkHeads.v). Conversion: YB1v.tfibsegs = AsanUbsan.M.loaded_segments. *)
Lemma fcu_ASIL : asource_img_laws SK SEGS B pcap_KS.
Proof. exact (YD1u.tfib_ASIL (SK := PcapSinkHeads.asan_ubsan_sink_head) (PH := eq_refl) B YD2l.TfibB_syms). Qed.
(* HSK: AOFL_HEAD = sk_ofl_head asan_ubsan_sink_head = WFclose.WF_OFL_HEAD (YCbq.v:84). *)
Lemma fcu_HSK : @YCbq.AOFL_HEAD SK = WFclose.WF_OFL_HEAD.
Proof. reflexivity. Qed.
(* HWRAPF / HRA0: PcapB's code table is YF0l.Tfib_code (YD2l.v:14), whose pc_wrap_free / pc_free_ra0 are the
   musl body's measured WF_FREETR / WF_FREE_RA0 (lib/Reusable/YF0l.v:11). *)
Lemma fcu_HWRAPF : pc_wrap_free (as_code B) = WFclose.WF_FREETR.
Proof. reflexivity. Qed.
Lemma fcu_HRA0 : pc_free_ra0 (as_code B) = WFclose.WF_FREE_RA0.
Proof. reflexivity. Qed.

(* ---- AFCLOSE ---- *)
Lemma inst_AFCLOSE_U : forall fx : YK11.FPState,
  @PFclose.afclose_source_spec fx rc SK SEGS B pcap_KS
    (pcap_sigma PS___interceptor_trampoline_fclose) WFcloseI.WFI_FREE1 WFcloseI.WFI_JOIN PCAP_RLO PCAP_RHI.
Proof.
  intros fx.
  (* conversion: YB1v.tfibsegs = AsanUbsan.M.loaded_segments, and PStdioImgB.IC_ENTRY_U = YE2e.IC_ENTRY =
     pcap_sigma PS___interceptor_trampoline_fclose (PcapAddr.v:38), in the conclusion. Inside: WFclose.wsegs /
     WMseek.msegs / YB1v.tfibsegs = AsanUbsan.M.loaded_segments at the ENV, AFREE and ASIL arguments, and
     WFclose.WF_FREE1 / WF_JOIN = WFcloseI.WFI_FREE1 / WFI_JOIN at the musl body. *)
  exact (@WFcloseI.pcapu_afclose_source_spec_icpt fx rc SK B PCAP_RLO PCAP_RHI YD2l.TfibB_syms
    (@WFclose.pcapu_afclose_source_spec_musl fx rc SK B fcu_ENV fcu_ML
       (@YF0q.afree_realizes_closed fx rc B YD2l.TfibB_syms (fun _ => eq_refl))
       pcap_KS fcu_ASIL eq_refl fcu_HSK fcu_HWRAPF fcu_HRA0 PCAP_RLO PCAP_RHI
       (@WFflush.pcapu_afflush_source_spec_icpt fx rc SK B YD2l.TfibB_syms fcu_ASIL
          (@WMseek.pcapu_amseek_rewind fx rc SK B fcu_ASIL) PCAP_RLO PCAP_RHI))).
Qed.

(* ---- HUfc1 / HUfc2: the trace universe's two fclose rows (YCejSites.fclose_free_in, YCej.v:91-92), by
   conversion: as_universe PcapB = YCej.Tfib_universe, pc_free_ra0 (as_code PcapB) = WF_FREE_RA0. ---- *)
Lemma inst_HUfc1_U : In [pc_free_ra0 (as_code B); WFcloseI.WFI_FREE1] (as_universe B).
Proof. exact (proj1 YCejSites.fclose_free_in). Qed.
Lemma inst_HUfc2_U : In [pc_free_ra0 (as_code B); WFcloseI.WFI_JOIN] (as_universe B).
Proof. exact (proj2 YCejSites.fclose_free_in). Qed.

End inst.

(* The closed statements, as a caller passes them to PcapEntryTop.v's Section top. *)
About asrc_file_meter_trivB.
About PcapBFacts.PcapB_lib.
About fcu_ENV.
About fcu_ML.
About inst_FM_U.
About inst_AFCLOSE_U.
About inst_HUfc1_U.
About inst_HUfc2_U.
Check (@inst_FM_U : forall {rc : YM05.RunCeil},
  @PSourceMeter.asrc_file_meter rc PcapSinkHeads.asan_ubsan_sink_head AsanUbsan.M.loaded_segments
    YD2l.PcapB YCbp.ameter_triv).
Check (@inst_AFCLOSE_U : forall {rc : YM05.RunCeil} (fx : YK11.FPState),
  @PFclose.afclose_source_spec fx rc PcapSinkHeads.asan_ubsan_sink_head AsanUbsan.M.loaded_segments
    YD2l.PcapB pcap_KS (pcap_sigma PS___interceptor_trampoline_fclose)
    WFcloseI.WFI_FREE1 WFcloseI.WFI_JOIN PCAP_RLO PCAP_RHI).
Check (inst_HUfc1_U : In [pc_free_ra0 (as_code YD2l.PcapB); WFcloseI.WFI_FREE1] (as_universe YD2l.PcapB)).
Check (inst_HUfc2_U : In [pc_free_ra0 (as_code YD2l.PcapB); WFcloseI.WFI_JOIN] (as_universe YD2l.PcapB)).

Print Assumptions asrc_file_meter_trivB.
Print Assumptions PcapBFacts.PcapB_lib.
Print Assumptions fcu_ENV.
Print Assumptions fcu_ML.
Print Assumptions fcu_ASIL.
Print Assumptions fcu_HSK.
Print Assumptions fcu_HWRAPF.
Print Assumptions fcu_HRA0.
Print Assumptions inst_FM_U.
Print Assumptions inst_AFCLOSE_U.
Print Assumptions inst_HUfc1_U.
Print Assumptions inst_HUfc2_U.
