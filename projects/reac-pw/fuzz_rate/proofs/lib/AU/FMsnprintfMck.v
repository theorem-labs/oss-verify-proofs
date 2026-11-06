(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AE30.v, with its module paths changed; 32 of its 58 lines of code are new or changed and 1532 lines of the source are left out. *)
(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/FMsnprintfMck.v (cold/port-fm-rtprintf-param 3e35620c52e); relocated to libreac/fuzz_disco.asan by g9/tool (reloc.py target disco-A): module paths changed; 1 address numerals moved (port_addr_check 0767e70e074a predict, fm.asan -> fuzz_disco.asan, symbol + offset; table g9/tool/tables/disco-A/FMsnprintfMck.table). *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_disco/lib/A/FMsnprintfMck.v at 2d2ff01bb6f2 relocated to reac-pw/fuzz_rate's ASan image A: module paths changed; numerals by port_core 1e42da8952ec (ledger provenance/reloc/A-Snp.tsv). *)
(* ARU entry facts for the ports of the donor's memcpy and memset interceptor proofs (FMsnprintfMc*.v, FMsnprintfMs*.v): the
   fields of ecall_preU (Poison's FMupoison.v) on the real memory, and the interceptors' constant regions
   (A/YE2y.v icpt_rodata_ok) on the real memory. The stack window and the image cells are not user-poisoned shadow
   bytes, so `unpoison U mem` reads them as `mem`. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/FMsnprintfMck.v at 71994ff034c7, derived by derive_y.py: addresses moved from reac-pw/fuzz_rate's asan image (image A) to its asan-ubsan image (image B), the image module Asan -> AsanUbsan; the Modified-by lines above describe how lib/A/FMsnprintfMck.v was made and quote that file's image-A values; the code below carries image B's values; a numeral in a comment that quotes the donor's text (lib/A/FMsnprintfMck.v keeps its donor's comment text) is kept as lib/A/FMsnprintfMck.v writes it. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Rt Require Import SnUpoison.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.

From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.

From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.

From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import YB1v YE34 YF0l YF0m YF0x YB1w YE20 YE2y.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YM05.
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
