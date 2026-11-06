From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file for libreac/fuzz_pcap v1.9.0's asan-ubsan build (pin
   fuzz_pcap.asan-ubsan sha256 9e66f771f22a...): the instance of pcap_source_open's closed walk
   lib/B/Prog/PcapSourceOpen.v pb_pcap_source_openX at lib/B/PcapCloseB.v's parts, so that PcapCloseB.v's former
   Section hypothesis HOPEN is a proved lemma. rule 24: no function walk here; this file is assembly and image facts.
   The A side's twin is lib/A/Prog/PcapEntryFinal.v (fin_HGX_open, fin_FOPEN, fin_OPEN), whose shape it follows.

   The instance (PcapCloseB.v's values, written here by their definitions because PcapCloseB.v Requires this file):
     PI := PcapEntryTop.PI_pcap rc, B := YD2l.PcapB, K := lib/B/Stdio/PSourceK.pcap_KS, MT := YCbp.ameter_triv,
     FM_RA := 0x8e7d8, CTX := YCej.CTX_pcap_source_open, roimg := YE3i.ro_img,
     SK := PcapSinkHeads.asan_ubsan_sink_head (sk_ofl_head 0x5f4e88), ra_fc1 / ra_fc2 := 0x8e184 / 0x8e18c.
   The parts of pb_pcap_source_openX:
     LAWS / TL / TLF / ML / ASM1 / ASF / FFL / FM / AFREAD / AFCLOSE / HUfc1 / HUfc2 / ASIL / HPATH: the lemmas that
       PcapCloseB.v's lemmas of the same names apply (lib/B/PcapBFacts.v, YG0q, YG05, YF0s, YG0t, PFreadC, PFcloseInstB,
       YCejSites, YD1u); MLAW / MLAWF: YCbp.ameter_triv_laws / ameter_triv_fs_laws.
     RO     inst_RO: lib/B/Prog/PcapEntryTop.v pcap_ro_below at the sink head (inst_HSK).
     HMODE  inst_HMODE: object 12 = "rb" = as_mode pcap_KS, by computation on the instance.
     HGX    inst_HGX: objects 4 / 2 are G_HARNESS_U's two globals (PcapEntryTop.pi_pcap_obj4 / pi_pcap_obj2), so
            PcapEntryTop.pcap_G_img and PcapBFacts.PcapB_HGOS / PcapB_HGERR.
     FOPEN  inst_FOPEN: lib/B/Prog/PcapFuzzFopen.v pb_libreac_fuzz_fopenX with ROIMG_LOW := PcapRoBridges.pcap_roimg_low,
            mc_lo / mc_hi := 0x10350 / 0x10370, FI := inst_FI (PcapFuzzFopen.fopen_img_tables_B).
     ROK    lib/B/PcapRokB.v pcap_rok_B; MCONSTS lib/B/PcapMconstsB.v pcap_mconsts_B; STRCMP lib/B/PcapStrcmpPathB.v
            pcap_strcmp_path_B; AFMEMOPEN lib/B/PcapAfmemopenB.v pcap_afmemopen_B (lib/B/Stdio/PFmemopenI.v
            pcap_afmemopen_spec over lib/B/Stdio/PFmemopenMW.v pcapu_rfmemopen_contract at ra := 0x8e7d8). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0s YI16 YG0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 PcapImgEnd YE00 YG0p YC5d YCbp.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSyms PcapList PcapAddr PcapPa PcapPaLib.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapBase.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import
PSource PSourceMeta PSourceMeter PFmemopenISpec PFreadISpec PFclose.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapFuzzFopenDefs PcapSourceOpenDefs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require PcapSourceOpen PcapFuzzFopen PcapEntryTop PcapEntry.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B Require
  PcapBFacts PcapRoBridges PcapStrcmpPathB PcapMconstsB PcapRokB PcapAfmemopenB.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Stdio Require PSourceK PFreadC PFcloseInstB.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require W_journalG.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require
  YD2l YE3i PcapSinkHeads YCej YCejSites YG0q YG05 YG0t YF0s YD1u.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Open Scope Z_scope.

(* lib/B's modules by their full paths (lib/A loads modules of the same short names). *)
Module PSO := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapSourceOpen.
Module PFF := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapFuzzFopen.
Module PET := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapEntryTop.
Module PEB := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapEntry.
Module BBF := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.PcapBFacts.
Module RRB := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.PcapRoBridges.
Module STB := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.PcapStrcmpPathB.
Module MCB := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.PcapMconstsB.
Module ROKB := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.PcapRokB.
Module AFB := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.PcapAfmemopenB.
Module KSU := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Stdio.PSourceK.
Module BFRC := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Stdio.PFreadC.
Module BFCI := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Stdio.PFcloseInstB.
Module WJG := OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.W_journalG.
Module AOD := OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog.PcapSourceOpenDefs.
Module AFD := OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog.PcapFuzzFopenDefs.
Module RI16 := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YI16.
Module RD2l := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YD2l.
Module RE3i := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YE3i.
Module RPSH := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.PcapSinkHeads.
Module RCej := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YCej.
Module RCejS := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YCejSites.
Module RG0q := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YG0q.
Module RG05 := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YG05.
Module RG0t := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YG0t.
Module RF0s := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YF0s.
Module RD1u := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YD1u.

(* PcapCloseB.v's abbreviations for PcapEntryTop.v's listing image at a given rc. *)
#[local] Abbreviation PIp rc := (@PET.PI_pcap rc).
#[local] Abbreviation PSEGS rc := (@pa_segs rc pcap_listing (PIp rc)).
#[local] Abbreviation VALp rc a := (@pa_val rc pcap_listing (PIp rc) a).
#[local] Abbreviation SIGp rc s := (@pa_sigma rc pcap_listing (PIp rc) s).
#[local] Abbreviation RLOp rc := (@pa_relro_lo rc pcap_listing (PIp rc)).
#[local] Abbreviation RHIp rc := (@pa_relro_hi rc pcap_listing (PIp rc)).
(* The instance's values (PcapCloseB.v SK_U, B_U, KS_U, CTX_U, ROI_U, by their definitions). *)
#[local] Abbreviation SKB := RPSH.asan_ubsan_sink_head.
#[local] Abbreviation BB := RD2l.PcapB.
#[local] Abbreviation KSB := KSU.pcap_KS.
#[local] Abbreviation CTXB := RCej.CTX_pcap_source_open.
#[local] Abbreviation ROIB := RE3i.ro_img.
(* The segments every lemma of the core states its facts at (= pa_segs (PIp rc), by delta). *)
#[local] Abbreviation ASEGS := OSSVerify.libreac.fuzz_pcap.images.AsanUbsan.M.loaded_segments.

(* The sink head's open-file-list head is pcap_KS's (PSourceK.pcap_KS_head, 0x5f4e88). *)
Lemma inst_HSK : @RI16.sk_ofl_head SKB = (symaddr Symbols.AsanUbsan.s_ofl_head).
Proof. reflexivity. Qed.

(* RO: PcapEntryTop.v:285 pcap_ro_below at SKB; pa_segs / pa_relro_lo / pa_relro_hi of PI_pcap are
   AsanUbsan.M.loaded_segments / PCAP_RLO / PCAP_RHI by delta (PcapEntryTop.v:144-161). *)
Lemma inst_RO : forall rc : YM05.RunCeil, @ro_below_ofl (PSEGS rc) (RLOp rc) (RHIp rc) SKB.
Proof. intros rc. exact (PET.pcap_ro_below SKB inst_HSK). Qed.

(* HMODE: the listing's object 12 is pcap_KS's mode literal "rb" (0x20d40), by computation on the instance (lib/A
   twin: PcapEntryFinal.v pi_pcap_obj12_mode). *)
Lemma inst_HMODE : forall rc : YM05.RunCeil, VALp rc (A_OBJ 12) = as_mode KSB.
Proof. intros rc. vm_compute. reflexivity. Qed.

(* HGX: objects 4 / 2 are G_HARNESS_U's two globals g_file_len 0x5d3e40 / g_file 0x5d3e60 (PcapEntryTop.pi_pcap_obj4 /
   pi_pcap_obj2), image bytes (PcapEntryTop.pcap_G_img) outside PcapB's owned statics (PcapBFacts.PcapB_HGOS) and
   errno (PcapBFacts.PcapB_HGERR) (lib/A twin: PcapEntryFinal.v fin_HGX_open). *)
Lemma inst_HGX : forall (rc : YM05.RunCeil) a,
  (VALp rc (A_OBJ 4) <= a < VALp rc (A_OBJ 4) + 8) \/ (VALp rc (A_OBJ 2) <= a < VALp rc (A_OBJ 2) + 8) ->
  in_img (PSEGS rc) a /\ ~ Exists (in_zr a) (as_owned_static BB) /\ ~ (as_errno BB <= a < as_errno BB + 4).
Proof.
  intros rc a Ha. rewrite (@PET.pi_pcap_obj4 rc), (@PET.pi_pcap_obj2 rc) in Ha.
  assert (HG : WJG.inG PEB.G_HARNESS_U a).
  { unfold WJG.inG, PEB.G_HARNESS_U. destruct Ha as [Ha | Ha];
      [apply Exists_cons_hd | apply Exists_cons_tl, Exists_cons_hd]; hnf; cbn [fst snd]; lia. }
  split; [exact (PET.pcap_G_img a HG)|].
  split; [exact (BBF.PcapB_HGOS a HG) | exact (BBF.PcapB_HGERR a HG)].
Qed.

(* FI: PcapFuzzFopen.v:586 fopen_img_tables_B (g_file_len + 8 <= g_file, pcap_KS's stdio cells in the image,
   as_ofl_head pcap_KS = 0x5f4e88), and fi_head: AOFL_HEAD at SKB is sk_ofl_head SKB = 0x5f4e88. *)
Lemma inst_FI : forall rc : YM05.RunCeil,
  PFF.FopenImg SKB (VALp rc (A_OBJ PFF.FO_LEN)) (VALp rc (A_OBJ PFF.FO_FILE)) KSB.
Proof.
  intros rc. destruct PFF.fopen_img_tables_B as (_ & _ & _ & _ & _ & _ & HK & HH).
  constructor.
  - unfold PFF.FO_LEN, PFF.FO_FILE. rewrite (@PET.pi_pcap_obj4 rc), (@PET.pi_pcap_obj2 rc). left. lia.
  - rewrite HH. reflexivity.
  - exact HK.
Qed.

(* ASIL at SKB: lib/Reusable/YD1u.v tfib_ASIL (as PcapCloseB.v's ASIL). *)
Lemma inst_ASIL : forall rc : YM05.RunCeil, asource_img_laws SKB (PSEGS rc) BB KSB.
Proof. intros rc. exact (@RD1u.tfib_ASIL SKB inst_HSK BB RD2l.TfibB_syms). Qed.

(* The arguments of the two walks, printed for the record. *)
About PSO.pb_pcap_source_openX.
About PFF.pb_libreac_fuzz_fopenX.
Check @PSO.pb_pcap_source_openX.

(* FOPEN, the statement pb_pcap_source_openX takes (PcapSourceOpen.v:453), from lib/B/Prog/PcapFuzzFopen.v
   pb_libreac_fuzz_fopenX (its Check at :568-575 lists the arguments): ROIMG_LOW lib/B/PcapRoBridges.v pcap_roimg_low,
   MCONSTS lib/B/PcapMconstsB.v pcap_mconsts_B, STRCMP lib/B/PcapStrcmpPathB.v pcap_strcmp_path_B, AFMEMOPEN
   lib/B/PcapAfmemopenB.v pcap_afmemopen_B. *)
Lemma inst_FOPEN : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @AFD.tlibreac_fuzz_fopen_specX fx rc SKB (PSEGS rc) (VALp rc A_TEXT + AF_libreac_fuzz_fopen)
    (VALp rc (A_OBJ 3)) (VALp rc (A_OBJ 4)) (VALp rc (A_OBJ 2)) ROIB BB KSB ameter_triv (symaddr (Symbols.AsanUbsan.s_fmemopen + 0x9c)%Z) CTXB.
Proof.
  intros rc fx.
  exact (@PFF.pb_libreac_fuzz_fopenX fx rc SKB (PIp rc) BB KSB (symaddr (Symbols.AsanUbsan.s_fmemopen + 0x9c)%Z) CTXB ameter_triv ROIB
    (@RRB.pcap_roimg_low rc) (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x70)%Z) (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x90)%Z) (MCB.pcap_mconsts_B rc) (@RG0q.AR_laws_ok rc (PSEGS rc) BB)
    ameter_triv_laws (inst_FI rc) (STB.pcap_strcmp_path_B rc fx) (AFB.pcap_afmemopen_B rc fx)).
Qed.

(* HOPEN (PcapCloseB.v's type): pb_pcap_source_openX at the instance; ROK lib/B/PcapRokB.v pcap_rok_B. *)
Lemma inst_HOPEN : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @AOD.tpcap_source_open_specX fx rc SKB (PSEGS rc) (RLOp rc) (RHIp rc) (VALp rc (A_OBJ 3))
    (VALp rc (A_OBJ 4)) (VALp rc (A_OBJ 2)) ROIB BB KSB ameter_triv (symaddr (Symbols.AsanUbsan.s_fmemopen + 0x9c)%Z) CTXB
    (VALp rc A_TEXT + AF_pcap_source_open).
Proof.
  intros rc fx.
  exact (@PSO.pb_pcap_source_openX fx rc SKB (PIp rc) BB KSB ameter_triv (symaddr (Symbols.AsanUbsan.s_fmemopen + 0x9c)%Z) CTXB ROIB
    (@RG0q.AR_laws_ok rc (PSEGS rc) BB) (BBF.PcapB_TL rc) (BBF.PcapB_TLF rc)
    (RG05.model_laws_ok (as_universe BB) RCej.Tfib_universe_ok)
    (@RF0s.stack_malloc1_contract fx rc BB (@RG0q.AR_laws_ok rc ASEGS BB) RD2l.TfibB_syms)
    (@RG0t.astack_free_law_ok rc (PSEGS rc) BB) (BBF.PcapB_FFL rc) ameter_triv_laws ameter_triv_fs_laws
    (BBF.PcapB_AFM rc) (inst_FOPEN rc fx)
    (@BFRC.pcapu_afread_closed fx rc BB SKB (@RG0q.AR_laws_ok rc ASEGS BB) RD2l.TfibB_syms (inst_ASIL rc))
    (symaddr (Symbols.AsanUbsan.s_fclose + 0xa4)%Z) (symaddr (Symbols.AsanUbsan.s_fclose + 0xac)%Z) (@BFCI.inst_AFCLOSE_U rc fx) (proj1 RCejS.fclose_free_in) (proj2 RCejS.fclose_free_in)
    (inst_ASIL rc) (inst_HMODE rc) (@ROKB.pcap_rok_B rc) (BBF.PcapB_HPATH rc) (inst_HGX rc) (inst_RO rc)).
Qed.

About inst_FOPEN.
About inst_HOPEN.
Print Assumptions inst_HOPEN.
