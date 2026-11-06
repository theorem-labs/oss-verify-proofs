From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: proof half of cgif c8557374ad2e lib/A/AD1k.v:272-346 (tfib_fwrite_site, msg_refused_eq, tfib_refused_site); the data half is a Theorem Labs lane's generated A/AD1k.v. Ported for libreac/fuzz_pcap's ASan build: module paths changed, TfibSyms -> PcapSyms; F_STDERR 0xa2578 -> 0x9de08 (__stderr_FILE+0, the unstripped twin's symtab, st_size 232 = FILE_SZ) at AD1k.v:279 / :320; the stderr FILE image range 664880 665712 -> 646592 647424 at AD1k.v:292 / :326 (A/AD2j.v R_A3, the range of A/AD1k.v img_facts' third conjunct: [__stderr_FILE-72, .data end) in both images; pcap: oft_arg0+0 to __start_asan_globals+0). The data half's Section d closes before this file, so its lemmas take the Section variables explicitly: icpt_pre_facts B (AD1k.v:275 / :316), icpt_pre_room B (AD1k.v:282 / :323), rodata_shadow_facts B HB LAWS (AD1k.v:300-301), rodata_hull_zero B HB LAWS (AD1k.v:334). The stack bounds FWI_STK 6224 (A/AE2x.v), FPI_STK 9216 (A/AE2v.v), DIAG_STK 16384 (A/AD1x.v), the message length 38 (Reusable/YO05.v msg_refused, V_refused 67108864) and the canary's start-up atom SOff 41 0 (A/AD1k.v img_facts) equal the donor's. rule 24: no function proved anew. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK15 YK18 YP0n YM02 YP0m YP09 YP0l YP06 YP08 YP03 YN3q YN3v YI04 YK04 YA0i YA0n YA0e YG00 YG01 YG0f YG0v YG0n YG0s YG0d YCe5 YL02.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AB1v AF0m AD2j AD2i AD1t AD20 AD1v AD2h AD2f AD1w AD1x.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AE2p AE3i AE39 AE3h AE3m AE3l AE23 AE2x AE2v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
(* AF0x.TFIB_IMG_END is pcap_img_end here (donor: the literal 0x5fb000), so the two numeric lia steps that cross it
   (tfib_low_not_owned's range premise, :51 and :85) unfold pcap_img_end and YImgTop.IMG_TOP as well. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PcapImgEnd YImgTop.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AD1u.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AD1k.
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
assert (HFE : F_STDERR = (symaddr Symbols.Asan.s___stderr_FILE)) by reflexivity. assert (HFS : FILE_SZ = 232) by reflexivity.
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
- apply (file_is_img _ (symaddr Symbols.Asan.s_oft_arg0) (symaddr Symbols.Asan.Sec.s_asan_globals)); [exact IR3 | exact stderr_img_chk |].
unfold stderr_fields. rewrite HFE. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
- intros a Ha. apply (tfib_low_not_owned B ly S W mem md a HAR); [unfold AF0x.TFIB_IMG_LO, AF0x.TFIB_IMG_END, pcap_img_end, YImgTop.IMG_TOP; lia|].
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
Lemma msg_refused_eq : map (Z_to_bv 8) AE3l.msg_refused = YO05.msg_refused /\ Z.of_nat (length YO05.msg_refused) = 38.
Proof. vm_compute. split; reflexivity. Qed.
Theorem tfib_refused_site : refused_site_tfa B est.
Proof.
intros ly S W regs mem md E T HPRE G10 G11 G12 HIMG Hfd HAI HPOST.
pose proof (icpt_pre_facts B ly S W regs mem md HPRE) as (HEPRE & Hslo & Hwin & Hpres). pose proof (proj1 HEPRE) as HAR.
pose proof (img_facts E _ HIMG) as (IR1 & IR2 & IR3 & Vcan).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof msg_refused_eq as [ME ML].
assert (HFPI : FPI_STK = 9216) by reflexivity. assert (HDS : DIAG_STK = 16384) by reflexivity.
assert (HFE : F_STDERR = (symaddr Symbols.Asan.s___stderr_FILE)) by reflexivity. assert (HFS : FILE_SZ = 232) by reflexivity.
unfold wr. rewrite <- ME. change (cfg_at tfibsegs A_icpt_fprintf regs mem md) with (cfg_at tfibsegs AE2v.FP_ENTRY regs mem md).
apply (tfib_fprintf_icpt_refused B LAWS HB TL ly S W regs mem md ch_stderr (bv_unsigned (sv_denot E (SOff 41 0))) T HEPRE).
- pose proof (icpt_pre_room B ly S W regs mem md HPRE); unfold FWI_STK, FPI_STK in *; lia.
- intros a Ha. apply Hpres. lia.
- exact G10. - exact G11. - exact G12.
- apply (file_is_img _ (symaddr Symbols.Asan.s_oft_arg0) (symaddr Symbols.Asan.Sec.s_asan_globals)); [exact IR3 | exact stderr_img_chk |].
unfold stderr_fields. rewrite HFE. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
- intros a Ha. unfold vf_file in Ha. apply (tfib_low_not_owned B ly S W mem md a HAR); [unfold AF0x.TFIB_IMG_LO, AF0x.TFIB_IMG_END, pcap_img_end, YImgTop.IMG_TOP; lia|].
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
