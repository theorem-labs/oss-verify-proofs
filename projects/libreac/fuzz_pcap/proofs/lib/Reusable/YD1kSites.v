From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: proof half of cgif c8557374ad2e lib/YD1k.v (the asan-ubsan twin of lib/A/AD1k.v:272-346: tfib_fwrite_site, msg_refused_eq, tfib_refused_site); the data half is a Theorem Labs lane's generated Reusable/YD1k.v (a working branch). It is the asan-ubsan twin of a Theorem Labs lane's lib/A/AD1kSites.v (a working branch 9700d736a50; commit 78fd6b35204), every hunk mirrored, ported for libreac/fuzz_pcap's asan-ubsan build (pinned image fuzz_pcap.asan-ubsan sha256 9e66f771f22a, symbols from its unstripped twin fuzz_pcap.asan-ubsan sha256 c969d83cdd59): module paths changed, TfibSyms -> PcapSyms; F_STDERR = 0x9dcd0 (__stderr_FILE+0, .symtab st_size 232 = FILE_SZ; a Theorem Labs lane's asan value 0x9de08) at both sites; the stderr FILE image range 646280 .. 647120 = [oft_arg0, __start_asan_globals) = [0x9dc88, 0x9dfd0) at both sites, which is Reusable/YD2j.v's R_A3 and the third conjunct IR3 of Reusable/YD1k.v img_facts (a Theorem Labs lane's asan range 646592 .. 647424). Unchanged from the donor (sizes): 6224, 9216, 16384, 232, message length 38, 67108864, SOff 41 0. FMT_refused 0x1965e = .rodata+0x937e, 'cli: input >= %u bytes, refused\n' in the asan-ubsan pin too (Reusable/YE3l.v). Adaptation as a Theorem Labs lane's (4 call sites): YD1k's Section d closes before this file, so icpt_pre_facts B, icpt_pre_room B, rodata_shadow_facts B HB LAWS and rodata_hull_zero B HB LAWS take B explicitly; and the two `unfold YF0x.TFIB_IMG_LO, YF0x.TFIB_IMG_END` steps also open pcap_img_end, YImgTop.IMG_TOP before their lia. TAKEN FROM (relocated core twins): Reusable/YE2p.v musl fwrite walk on __stderr_FILE; YE2x.v tfib_fwrite_icpt; YE2v.v tfib_fprintf_icpt_refused; YE3l.v refused-message constants; YE3h.v vf_file. rule 24: no function proved anew. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK15 YK18 YP0n YM02 YP0m YP09 YP0l YP06 YP08 YP03 YN3q YN3v YI04 YK04 YA0i YA0n YA0e YG00 YG01 YG0f YG0v YG0n YG0s YG0d YCe5 YL02.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YB1v YF0m YD2j YD2i YD1t YD20 YD1v YD2h YD2f YD1w YD1x.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YE2p YE3i YE39 YE3h YE3m YE3l YE23 YE2x YE2v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
(* YF0x.TFIB_IMG_END is pcap_img_end here (donor: the literal 0x5fb000), so the two numeric lia steps that cross it
   (tfib_low_not_owned's range premise, :51 and :85) unfold pcap_img_end and YImgTop.IMG_TOP as well. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PcapImgEnd YImgTop.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YD1u.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YD1k.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Section d.
Variable B : asyms.
Hypothesis HB : PcapSyms B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TL : PcapSyms B.
Theorem tfib_fwrite_site : fwrite_site_tfa B est.
Proof.
intros ly S W regs mem md E p len msg T HPRE G10 G11 G12 G13 Hlen Hlen1 Hp1 Hp2 Hhole Himg HIMG Hfd HAI HPOST.
pose proof (icpt_pre_facts B ly S W regs mem md HPRE) as (HEPRE & Hslo & Hwin & Hpres). pose proof (proj1 HEPRE) as HAR.
pose proof (img_facts E _ HIMG) as ([IR1a IR1b] & IR2 & IR3 & Vcan).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HFWI : FWI_STK = 6224) by reflexivity. assert (HDS : DIAG_STK = 16384) by reflexivity.
assert (HFE : F_STDERR = (symaddr Symbols.AsanUbsan.s___stderr_FILE)) by reflexivity. assert (HFS : FILE_SZ = 232) by reflexivity.
unfold wr. change (cfg_at tfibsegs A_icpt_fwrite regs mem md) with (cfg_at tfibsegs FW_ENTRY regs mem md).
apply (tfib_fwrite_icpt B LAWS HB ly S W regs mem md ch_stderr p len (bv_unsigned (sv_denot E (SOff 41 0))) msg T HEPRE).
- pose proof (icpt_pre_room B ly S W regs mem md HPRE); unfold FWI_STK, FPI_STK in *; lia.
- intros a Ha. apply Hpres. lia.
- exact G10. - exact G11. - exact G12. - exact G13.
- lia. - lia. - lia. - unfold kHighMemEnd. lia.
- left. unfold sp_window_lo in Hwin. lia.
- left. rewrite HFE. lia.
-
apply (proj2 (rdn_mbytes tfibsegs (mrestrict (w_H W) mem) (Z.to_nat len) p msg)). split; [lia|].
intros i Hi. destruct Hhole as [Hh|Hh]; [rewrite (IR1a (p + Z.of_nat i)) by lia | rewrite (IR1b (p + Z.of_nat i)) by lia];
unfold img_byte; rewrite (Himg i) by lia; symmetry; apply nth_error_nth'; lia.
- apply (file_is_img _ (symaddr Symbols.AsanUbsan.s_oft_arg0) (symaddr Symbols.AsanUbsan.Sec.s_asan_globals)); [exact IR3 | exact stderr_img_chk |].
unfold stderr_fields. rewrite HFE. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
- intros a Ha. apply (tfib_low_not_owned B ly S W mem md a HAR); [unfold YF0x.TFIB_IMG_LO, YF0x.TFIB_IMG_END, pcap_img_end, YImgTop.IMG_TOP; lia|].
apply (tfib_not_owned_static B F_STDERR (F_STDERR + FILE_SZ) a HB); [vm_compute; reflexivity | exact Ha].
- eapply val_mem_img; [exact IR2 | unfold A_GOT_canary; lia | unfold A_GOT_canary; cbn; lia | exact got_canary_chk].
- exact Vcan.
- exact (u64_range (sv_denot E (SOff 41 0))).
- left. unfold kLowMemEnd. lia.
- exact (proj1 (rodata_shadow_facts B HB LAWS ly S W mem md p len HAR Hp1 ltac:(lia) ltac:(lia))).
- exact (proj2 (rodata_shadow_facts B HB LAWS ly S W mem md p len HAR Hp1 ltac:(lia) ltac:(lia))).
- split; [exact Hfd | reflexivity].
- exact HAI.
- intros regs' mem' md' HAR' HP' Hsbm' Ha0' HFW' Hfr' Hpr' HAI'.
apply (HPOST regs' mem' md' HAR' HP' Hsbm' Ha0').
+ apply est_written. exact HFW'.
+ intros a Ha Hb Hf. apply (Hfr' a Ha); [lia|]. unfold STDERR_MUT, F_STDERR_LO, F_STDERR_HI in Hf. rewrite HFE, HFS. exact Hf.
+ intros a Ha Hf Hp. apply (Hpr' a Ha); [|exact Hp]. unfold STDERR_MUT, F_STDERR_LO, F_STDERR_HI in Hf. rewrite HFE, HFS. exact Hf.
+ exact HAI'.
Qed.
Lemma msg_refused_eq : map (Z_to_bv 8) YE3l.msg_refused = YO05.msg_refused /\ Z.of_nat (length YO05.msg_refused) = 38.
Proof. vm_compute. split; reflexivity. Qed.
Theorem tfib_refused_site : refused_site_tfa B est.
Proof.
intros ly S W regs mem md E T HPRE G10 G11 G12 HIMG Hfd HAI HPOST.
pose proof (icpt_pre_facts B ly S W regs mem md HPRE) as (HEPRE & Hslo & Hwin & Hpres). pose proof (proj1 HEPRE) as HAR.
pose proof (img_facts E _ HIMG) as (IR1 & IR2 & IR3 & Vcan).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof msg_refused_eq as [ME ML].
assert (HFPI : FPI_STK = 9216) by reflexivity. assert (HDS : DIAG_STK = 16384) by reflexivity.
assert (HFE : F_STDERR = (symaddr Symbols.AsanUbsan.s___stderr_FILE)) by reflexivity. assert (HFS : FILE_SZ = 232) by reflexivity.
unfold wr. rewrite <- ME. change (cfg_at tfibsegs A_icpt_fprintf regs mem md) with (cfg_at tfibsegs YE2v.FP_ENTRY regs mem md).
apply (tfib_fprintf_icpt_refused B LAWS HB TL ly S W regs mem md ch_stderr (bv_unsigned (sv_denot E (SOff 41 0))) T HEPRE).
- pose proof (icpt_pre_room B ly S W regs mem md HPRE); unfold FWI_STK, FPI_STK in *; lia.
- intros a Ha. apply Hpres. lia.
- exact G10. - exact G11. - exact G12.
- apply (file_is_img _ (symaddr Symbols.AsanUbsan.s_oft_arg0) (symaddr Symbols.AsanUbsan.Sec.s_asan_globals)); [exact IR3 | exact stderr_img_chk |].
unfold stderr_fields. rewrite HFE. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
- intros a Ha. unfold vf_file in Ha. apply (tfib_low_not_owned B ly S W mem md a HAR); [unfold YF0x.TFIB_IMG_LO, YF0x.TFIB_IMG_END, pcap_img_end, YImgTop.IMG_TOP; lia|].
apply (tfib_not_owned_static B F_STDERR (F_STDERR + FILE_SZ) a HB); [vm_compute; reflexivity | exact Ha].
- eapply val_mem_img; [exact IR2 | unfold A_GOT_canary; lia | unfold A_GOT_canary; cbn; lia | exact got_canary_chk].
- exact Vcan.
- exact (u64_range (sv_denot E (SOff 41 0))).
- exact (ro_img_of_IMG E _ HIMG).
- apply (rodata_hull_zero B HB LAWS ly S W mem md); [exact HAR | unfold FMT_refused; lia | unfold FMT_refused; lia | lia].
- split; [exact Hfd | reflexivity].
- exact HAI.
- intros regs' mem' md' HAR' HP' Hsbm' Ha0' HFW' Hfr' Hpr' HAI'.
apply (HPOST regs' mem' md' HAR' HP' Hsbm').
+ rewrite ML. exact Ha0'.
+ apply est_after_vf. exact HFW'.
+ intros a Ha Hb Hf. apply (Hfr' a Ha); [lia|]. unfold vf_file. unfold STDERR_MUT, F_STDERR_LO, F_STDERR_HI in Hf. rewrite HFE, HFS. exact Hf.
+ intros a Ha Hf Hp. apply (Hpr' a Ha); [|exact Hp]. unfold vf_file. unfold STDERR_MUT, F_STDERR_LO, F_STDERR_HI in Hf. rewrite HFE, HFS. exact Hf.
+ exact HAI'.
Qed.
End d.
End c.
