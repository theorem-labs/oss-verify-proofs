From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file for libreac/fuzz_pcap v1.9.0's asan-ubsan build (pin
   fuzz_pcap.asan-ubsan sha256 9e66f771f22a...). rule 24: no function proved here; this file is a
   segment lemma. It proves the STRCMP argument of lib/B/Prog/PcapFuzzFopen.v pb_libreac_fuzz_fopenX (its
   hypothesis STRCMP, PcapFuzzFopen.v:166; the definition astrcmp_path_at, PcapFuzzFopen.v:96) at the B instance of
   lib/B/PcapCloseB.v, for every rc and fx:
     segs  := pa_segs (PcapEntryTop.PI_pcap rc) (= AsanUbsan.M.loaded_segments = YB1v.tfibsegs, by delta),
     B     := YD2l.PcapB,  roimg := YE3i.ro_img,
     pc    := pa_sigma (PI_pcap rc) PS___interceptor_trampoline_strcmp (= 0x415b4, by computation: strcmp_pc_B),
     x     := pa_val (PI_pcap rc) (A_OBJ FO_PATH)                       (= 0x20d00, by computation: fuzz_path_obj_B).
   The source is lib/B/Rt/StrcmpIcpt.v:470 strcmp_lit_contract (astrcmp_lit_realizes B, lib/B/Rt/StrcmpDef.v:61),
   with its two premises at PcapB: AR_laws tfibsegs PcapB (lib/Reusable/YG0q.v:805 AR_laws_ok) and PcapSyms PcapB
   (lib/Reusable/YD2l.v:72 TfibB_syms). The contract's one literal instance (SM_INST, StrcmpDef.v:48) is
   (0x20d00, 0x20d00, 0), its entry SM_ENTRY = 0x415b4 and its post astrcmp_post (StrcmpDef.v:50) is the post of
   astrcmp_path_at at res = 0, token for token. Its x and y premises are the same two facts, because x = y.
   The literal [0x20d00, 0x20d0d) ("<fuzz-input>" and NUL) is inside YE3i's chunk 0x20a84 .. 0x20d0d
   (lib/Reusable/YE3i.v:48, fuzz_path_in_ro_chunk), and its 13 image bytes are those bytes (fuzz_path_bytes_img). So
   ro_img holds them; the strcmp walk reads them from ro_img there (StrcmpIcpt.v:352). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require
  YK11 YM05 YP09 YB1v YE3i YG0q YD2l YCbp YCej PcapSinkHeads.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require PaTable.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require PcapSyms PcapList PcapPa PcapEntryTop PcapFuzzFopen.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Rt Require StrcmpDef StrcmpIcpt.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Stdio Require PSourceK.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* The modules by their full paths (lib/A and lib/U load modules of the same short names). The names start with Sp
   so that they do not collide with the aliases of a file that Requires this one. *)
Module SpK11 := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YK11.
Module SpM05 := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YM05.
Module SpP09 := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YP09.
Module SpB1v := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YB1v.
Module SpE3i := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YE3i.
Module SpG0q := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YG0q.
Module SpD2l := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YD2l.
Module SpCbp := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YCbp.
Module SpCej := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YCej.
Module SpSH := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.PcapSinkHeads.
Module SpAT := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.PaTable.
Module SpSY := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapSyms.
Module SpLS := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapList.
Module SpPA := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapPa.
Module SpET := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapEntryTop.
Module SpFF := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapFuzzFopen.
Module SpSD := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Rt.StrcmpDef.
Module SpSI := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Rt.StrcmpIcpt.
Module SpKS := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Stdio.PSourceK.

(* The contract's two numerals, as StrcmpDef.v:43-44 defines them. *)
Lemma strcmp_lit_values : SpSD.SM_ENTRY = (symaddr Symbols.AsanUbsan.s___wrap_strcmp) /\ SpSD.A_FUZZ_PATH = (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68128)%Z).
Proof. split; reflexivity. Qed.

(* The listing's strcmp trampoline is the contract's entry (0x415b4), by computation on the instance. *)
Lemma strcmp_pc_B (rc : SpM05.RunCeil) :
  @SpPA.pa_sigma rc SpLS.pcap_listing (@SpET.PI_pcap rc) SpSY.PS___interceptor_trampoline_strcmp = SpSD.SM_ENTRY.
Proof. vm_compute. reflexivity. Qed.

(* The listing's object FO_PATH is the contract's literal (0x20d00), by computation on the instance. *)
Lemma fuzz_path_obj_B (rc : SpM05.RunCeil) :
  @SpPA.pa_val rc SpLS.pcap_listing (@SpET.PI_pcap rc) (SpAT.A_OBJ SpFF.FO_PATH) = SpSD.A_FUZZ_PATH.
Proof. vm_compute. reflexivity. Qed.

(* The literal and its NUL, [0x20d00, 0x20d0d), lie in the ro_img chunk 0x20a84 .. 0x20d0d (YE3i.v:48). *)
Lemma fuzz_path_in_ro_chunk :
  In (SpP09.mkChunk (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 67492)%Z) (SpP09.CImg ((symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68141)%Z) - (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 67492)%Z)))) SpE3i.img_ro_chunks /\
  (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 67492)%Z) <= SpSD.A_FUZZ_PATH /\ SpSD.A_FUZZ_PATH + 13 <= (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68141)%Z).
Proof. split; [unfold SpE3i.img_ro_chunks; cbn; tauto|]. unfold SpSD.A_FUZZ_PATH. lia. Qed.

(* The image bytes there are "<fuzz-input>" (StrcmpDef.v:46 FUZZ_PATH_BYTES) and the NUL, by computation. *)
Lemma fuzz_path_bytes_img :
  map (fun i => option_map (fun b : byte => bv_unsigned b)
                  (SpK11.seg_rom SpB1v.tfibsegs (Z_to_bv 64 (SpSD.A_FUZZ_PATH + Z.of_nat i))))
    (seq 0 13) = map Some (SpSD.FUZZ_PATH_BYTES ++ [0]).
Proof. vm_compute. reflexivity. Qed.

(* STRCMP of pb_libreac_fuzz_fopenX at the B instance, for every rc and fx. *)
Lemma pcap_strcmp_path_B : forall (rc : SpM05.RunCeil) (fx : SpK11.FPState),
  @SpFF.astrcmp_path_at fx rc (@SpPA.pa_segs rc SpLS.pcap_listing (@SpET.PI_pcap rc)) SpD2l.PcapB SpE3i.ro_img
    (@SpPA.pa_sigma rc SpLS.pcap_listing (@SpET.PI_pcap rc) SpSY.PS___interceptor_trampoline_strcmp)
    (@SpPA.pa_val rc SpLS.pcap_listing (@SpET.PI_pcap rc) (SpAT.A_OBJ SpFF.FO_PATH)).
Proof.
  intros rc fx. rewrite (strcmp_pc_B rc), (fuzz_path_obj_B rc).
  intros ly S W regs mem md HPRE G10 G11 HRO HRA HHV.
  pose proof (@SpSI.strcmp_lit_contract fx rc SpD2l.PcapB (@SpG0q.AR_laws_ok rc SpB1v.tfibsegs SpD2l.PcapB)
    SpD2l.TfibB_syms) as HC.
  unfold SpSD.astrcmp_lit_realizes in HC.
  assert (HIN : In (SpSD.A_FUZZ_PATH, SpSD.A_FUZZ_PATH, 0) SpSD.SM_INST) by (left; reflexivity).
  change 13 with (Z.of_nat (length SpSD.FUZZ_PATH_BYTES) + 1) in HRA, HHV.
  exact (HC SpSD.A_FUZZ_PATH SpSD.A_FUZZ_PATH 0 HIN ly S W regs mem md HPRE G10 G11 HRO HRA HHV HRA HHV).
Qed.

(* The lemma fits the STRCMP slot of pb_libreac_fuzz_fopenX at the instance (PcapCloseB.v's values by their
   definitions: SK := asan_ubsan_sink_head, PI := PI_pcap rc, B := PcapB, K := pcap_KS, FM_RA := 0x8e7d8,
   CTX := CTX_pcap_source_open, MT := ameter_triv, roimg := ro_img, mc_lo / mc_hi := 0x10350 / 0x10370); the other
   arguments are binders whose types the application fixes. *)
Check (fun (rc : SpM05.RunCeil) (fx : SpK11.FPState) ROIMG_LOW MCONSTS LAWS MLAWS FI AFMEMOPEN =>
  @SpFF.pb_libreac_fuzz_fopenX fx rc SpSH.asan_ubsan_sink_head (@SpET.PI_pcap rc) SpD2l.PcapB SpKS.pcap_KS (symaddr (Symbols.AsanUbsan.s_fmemopen + 0x9c)%Z)
    SpCej.CTX_pcap_source_open SpCbp.ameter_triv SpE3i.ro_img ROIMG_LOW (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x70)%Z) (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x90)%Z) MCONSTS LAWS MLAWS FI
    (pcap_strcmp_path_B rc fx) AFMEMOPEN).
Check pcap_strcmp_path_B.

Print Assumptions pcap_strcmp_path_B.
