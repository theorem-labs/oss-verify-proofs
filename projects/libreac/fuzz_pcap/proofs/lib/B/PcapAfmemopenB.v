From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Written by Theorem Labs, 2026-10 (a Theorem Labs lane, CloseB round 3): the AFMEMOPEN argument of
   lib/B/Prog/PcapFuzzFopen.v pb_libreac_fuzz_fopenX (its Section hypothesis at :167-168) at the asan-ubsan instance
   of lib/B/PcapCloseB.v. rule 24: no function proved; this file is assembly of proved lemmas.

   The statement is lib/A/Prog/PcapEntryFinal.v:401-403's AFMEMOPEN at this image: SK := asan_ubsan_sink_head,
   SEGS := pa_segs at PI_pcap, B := PcapB, K := pcap_KS (lib/B/Stdio/PSourceK.v), MT := ameter_triv,
   CTX := CTX_pcap_source_open, pc := pa_sigma PS___interceptor_trampoline_fmemopen (= 0x41614), FM_RA := 0x8e7d8,
   [mc_lo, mc_hi) := [0x10350, 0x10370).

   The proof:
   - lib/B/Stdio/PFmemopenI.v:328 pcap_afmemopen_spec (the fmemopen interceptor at FM_ENTRY = 0x41614), with
     LAWS := YG0q.AR_laws_ok, TB := YD2l.TfibB_syms, ASIL := YD1u.tfib_ASIL (as lib/B/PcapCloseB.v:294-295),
     AMR := lib/B/PcapBFacts.v:135 PcapB_AMALLOC4, and RFM := below;
   - RFM: lib/B/Stdio/PFmemopenMW.v:1551 pcapu_rfmemopen_contract (musl fmemopen at 0x8e73c, ra 0x8e7d8), with
     ASIL, TL := TfibB_syms and its strchr hypothesis SCHR (PFmemopenMW.v:468) := lib/Reusable/YE2j.v:265
     tfib_strchr_lit (the asan-ubsan strchr interceptor contract at 0x415b8; SCU_ENTRY / SCU_WIN / INSTU /
     stu_cells / rwau_img / KEPTSU / strchru_post of PFmemopenMW.v are YE2j.v's SC_ENTRY / SC_WIN / INST /
     st_cells / rwa_img / KEPTS / strchr_post by unfolding).

   FM_RA = 0x8e7d8 is the return of musl fmemopen's `jal` to the malloc trampoline at fmemopen+0x98 (0x8e7d4), the
   buf != NULL call. The buf == NULL call (fmemopen+0xa8 = 0x8e7e4, return 0x8e7e8) is not assumed away: it is
   refuted at its branches inside the walk. afmemopen_spec carries In (b, n) (ablocks B ly S)
   (lib/A/Stdio/PFmemopenISpec.v:92; pb_libreac_fuzz_fopenX supplies it at PcapFuzzFopen.v:477 from its premise
   lib/A/Prog/PcapFuzzFopenDefs.v:147), pcap_afmemopen_spec passes it to rfmemopen_pre (PFmemopenI.v:390,
   lib/A/Stdio/PFmemopenM.v:220), and pcapu_rfmemopen_contract turns it into 4096 <= b (AR's block law, al_blocks,
   PFmemopenMW.v:1563) and gives s1 = b in [4096, 2^47] to phase C (fm_C, PFmemopenMW.v:890, called at :1610-1612).
   Phase C's symbolic run r_C (PFmemopenMW.v:246-249, its fact on register 9) decides `bnez s1` at 0x8e788 taken and
   `beqz s1` at 0x8e7cc not taken, so the run reaches the malloc trampoline with ra = FM_MALLOC_RA_U = 0x8e7d8
   (fm_C's conclusion, :896, read off the computed state at :923); phase E's run (ssE, :264-266, the same fact)
   decides `bnez s1` at 0x8e820. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YK11 YM05 YI16 YB1v YD2l YD1u YE2j YG0q YCbp YCej YE3i
  PcapSinkHeads.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require PFmemopenISpec PFmemopenM.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Stdio Require PSourceK PStdioImgB PFmemopenI PFmemopenMW.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require PcapEntryTop PcapPa PcapList PcapSyms PcapAddr
  PcapFuzzFopen.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B Require PcapBFacts.
Local Open Scope Z_scope.

(* Every module by its full path: lib/A loads modules of the same short names in this closure. *)
Module RK11 := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YK11.
Module RM05 := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YM05.
Module RI16 := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YI16.
Module RB1v := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YB1v.
Module RD2l := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YD2l.
Module RD1u := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YD1u.
Module RE2j := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YE2j.
Module RG0q := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YG0q.
Module RCbp := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YCbp.
Module RCej := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YCej.
Module RE3i := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YE3i.
Module RPSH := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.PcapSinkHeads.
Module PFMS := OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio.PFmemopenISpec.
Module PFMM := OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio.PFmemopenM.
Module KSB := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Stdio.PSourceK.
Module BSIB := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Stdio.PStdioImgB.
Module BFMI := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Stdio.PFmemopenI.
Module BFMW := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Stdio.PFmemopenMW.
Module PET := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapEntryTop.
Module PPA := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapPa.
Module PLS := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapList.
Module PSY := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapSyms.
Module PADR := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapAddr.
Module PFFB := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapFuzzFopen.
Module BBF := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.PcapBFacts.

(* The sink head's ofl_head is pcap_KS's (YD1u.v's pcap_head class; PcapCloseB.v:234 HSK_U). *)
Lemma pcap_afmemopen_B_head : @RI16.sk_ofl_head RPSH.asan_ubsan_sink_head = (symaddr Symbols.AsanUbsan.s_ofl_head).
Proof. reflexivity. Qed.

(* The listing's fmemopen trampoline (PcapAddr.v:18) is the interceptor entry pcap_afmemopen_spec proves. *)
Lemma pcap_afmemopen_B_pc : PADR.pcap_sigma PSY.PS___interceptor_trampoline_fmemopen = BFMI.FM_ENTRY.
Proof. vm_compute. reflexivity. Qed.

Lemma pcap_afmemopen_B : forall (rc : RM05.RunCeil) (fx : RK11.FPState),
  @PFMS.afmemopen_spec fx rc RPSH.asan_ubsan_sink_head (@PPA.pa_segs rc PLS.pcap_listing (@PET.PI_pcap rc))
    RD2l.PcapB KSB.pcap_KS RCbp.ameter_triv RCej.CTX_pcap_source_open
    (@PPA.pa_sigma rc PLS.pcap_listing (@PET.PI_pcap rc) PSY.PS___interceptor_trampoline_fmemopen) (symaddr (Symbols.AsanUbsan.s_fmemopen + 0x9c)%Z)
    (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x70)%Z) (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x90)%Z).
Proof.
intros rc fx.
pose proof (@RG0q.AR_laws_ok rc RB1v.tfibsegs RD2l.PcapB) as LAWS_B.
pose proof (@RD1u.tfib_ASIL RPSH.asan_ubsan_sink_head pcap_afmemopen_B_head RD2l.PcapB RD2l.TfibB_syms) as ASIL_B.
pose proof (@BBF.PcapB_AMALLOC4 fx rc RPSH.asan_ubsan_sink_head) as AMR_B.
(* musl fmemopen's contract at 0x8e73c, its strchr hypothesis discharged by YE2j.v's proved interceptor contract *)
assert (RFM_B : @PFMM.rfmemopen_contract fx rc RPSH.asan_ubsan_sink_head RB1v.tfibsegs RD2l.PcapB KSB.pcap_KS
  RCbp.ameter_triv RCej.CTX_pcap_source_open BSIB.PFMEMOPEN_U (symaddr (Symbols.AsanUbsan.s_fmemopen + 0x9c)%Z) (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x70)%Z) (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x90)%Z)).
{ exact (@BFMW.pcapu_rfmemopen_contract fx rc RPSH.asan_ubsan_sink_head RD2l.PcapB RCbp.ameter_triv
    RCej.CTX_pcap_source_open ASIL_B RD2l.TfibB_syms
    (@RE2j.tfib_strchr_lit fx rc RD2l.PcapB LAWS_B RD2l.TfibB_syms)). }
change (@PPA.pa_sigma rc PLS.pcap_listing (@PET.PI_pcap rc) PSY.PS___interceptor_trampoline_fmemopen)
  with (PADR.pcap_sigma PSY.PS___interceptor_trampoline_fmemopen).
rewrite pcap_afmemopen_B_pc.
change (@PPA.pa_segs rc PLS.pcap_listing (@PET.PI_pcap rc)) with RB1v.tfibsegs.
exact (@BFMI.pcap_afmemopen_spec fx rc RD2l.PcapB LAWS_B RD2l.TfibB_syms RPSH.asan_ubsan_sink_head KSB.pcap_KS
  RCbp.ameter_triv RCej.CTX_pcap_source_open (symaddr (Symbols.AsanUbsan.s_fmemopen + 0x9c)%Z) ASIL_B AMR_B RFM_B).
Qed.

(* The lemma fits pb_libreac_fuzz_fopenX's AFMEMOPEN slot (the form of lib/A/Prog/PcapEntryFinal.v:640-641) at the
   instance: SK, PI_pcap, PcapB, pcap_KS, FM_RA 0x8e7d8, CTX_pcap_source_open, ameter_triv, ro_img, [0x10350, 0x10370),
   LAWS and MLAWS proved; ROIMG_LOW, MCONSTS, FI and STRCMP are the other lanes' arguments, bound here. *)
Check (fun (rc : RM05.RunCeil) (fx : RK11.FPState) ROIMG_LOW MCONSTS FI STRCMP =>
  @PFFB.pb_libreac_fuzz_fopenX fx rc RPSH.asan_ubsan_sink_head (@PET.PI_pcap rc) RD2l.PcapB KSB.pcap_KS (symaddr (Symbols.AsanUbsan.s_fmemopen + 0x9c)%Z)
    RCej.CTX_pcap_source_open RCbp.ameter_triv RE3i.ro_img ROIMG_LOW (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x70)%Z) (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x90)%Z) MCONSTS
    (@RG0q.AR_laws_ok rc (@PPA.pa_segs rc PLS.pcap_listing (@PET.PI_pcap rc)) RD2l.PcapB) RCbp.ameter_triv_laws
    FI STRCMP (pcap_afmemopen_B rc fx)).

Print Assumptions pcap_afmemopen_B.
