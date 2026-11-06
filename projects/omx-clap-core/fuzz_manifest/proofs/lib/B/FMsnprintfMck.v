(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AE30.v, with its module paths changed; 29 of its 61 lines of code are new or changed and 1526 lines of the source are left out. *)
(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMsnprintfMck.v at a working branch 5d8d8a15571, relocated A->B by Theorem Labs tools over the unstripped twins; every image numeral re-derived by symbol / section (a Theorem Labs lane reloc report). *)
(* ARU entry facts for the ports of the donor's memcpy and memset interceptor proofs (FMsnprintfMc*.v, FMsnprintfMs*.v): the
   fields of ecall_preU (Poison's FMupoison.v) on the real memory, and the interceptors' constant regions
   (A/YE2y.v icpt_rodata_ok) on the real memory. The stack window and the image cells are not user-poisoned shadow
   bytes, so `unpoison U mem` reads them as `mem`. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YE34 YF0l YF0m YF0x YB1w YE20 YE2y.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
(* ecall_pre's fields (YG0d.v) from ecall_preU, with ARU for AR and the stack window present in the real memory. *)
Lemma ecall_preU_split : forall ly S U (W : world tfibsegs) regs mem md,
ecall_preU tfibsegs B ly S U W regs mem md ->
ARU tfibsegs B ly S U W mem md /\ YK0s.ret_ok (getr regs 1) /\
spZ regs mod 16 = 0 /\ ly_stk_lo ly + ESTACK <= spZ regs /\ spZ regs <= ly_stk_hi ly /\
(forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem a) /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B).
Proof.
intros ly S U W regs mem md ((HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp) & OK & PO).
assert (HARU : ARU tfibsegs B ly S U W mem md) by exact (conj HAR (conj OK PO)).
pose proof (stk_kHighMemBeg B ly S _ (proj1 HAR)) as [SK1 SK2].
split; [exact HARU|]. split; [exact Hra|]. split; [exact Hal16|]. split; [exact Hslo|]. split; [exact Htop|].
split; [|exact (conj Hgp Htp)].
intros a Ha. destruct (HpresE a Ha) as [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite <- Hb. symmetry.
apply unpoison_out. destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:E; [|reflexivity]. exfalso.
pose proof (ush_facts tfibsegs B ly S U W mem md _ HARU E) as (_ & _ & L).
assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold ESTACK, kHighMemBeg, kHighMemEnd in *; lia).
rewrite (wz a Ha64) in L. lia.
Qed.
(* A/YE2y.v icpt_rodata_ok on the real memory: the constant cells are image bytes, below the shadow. *)
Lemma icpt_rodata_okU : TfibSyms B -> forall ly S U (W : world tfibsegs) mem md E,
ARU tfibsegs B ly S U W mem md -> Forall (region_ok tfibsegs E (mrestrict (w_H W) mem)) (map ro_region icpt_rodata).
Proof.
intros TB ly S U W mem md E HARU.
pose proof (icpt_rodata_ok B TB ly S (w_H W) (unpoison U mem) E (ARU_ARm tfibsegs B ly S U W mem md HARU)) as F0.
assert (WF : regions_wf (map ro_region icpt_rodata) = true) by (vm_compute; reflexivity).
apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) F0 r Hr) as Hr0.
pose proof (regions_wf_In _ r WF Hr) as Hwf. apply region_wf_facts in Hwf as (_ & _ & Hci).
assert (Hlit : exists e, In e icpt_rodata /\ r = ro_region e) by (apply in_map_iff in Hr as (e & <- & He); exists e; auto).
destruct Hlit as (e & He & ->).
assert (Hrange : 0 <= fst (fst e) /\ fst (fst e) + snd (fst e) <= 0x200000).
{ cbn in He. repeat (destruct He as [<-|He]; [cbn; lia|]). destruct He. }
eapply (region_ok_transport tfibsegs E E); [exact Hr0 | reflexivity | | | | exact Hci].
- intros c Hc. unfold ro_region in Hc. cbn [YP09.r_chunks] in Hc. apply in_map_iff in Hc as (cc & <- & _). cbn. reflexivity.
- intros a Ha. unfold ro_region in Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha.
apply YF0x.mbyte_mrestrict_same. symmetry. apply (ARU_mem_low tfibsegs B ly S U W mem md _ HARU).
rewrite unsigned_lit_small by lia. unfold SHADOW_OFF. lia.
- intros a Ha. unfold ro_region in Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia.
Qed.
End k.
