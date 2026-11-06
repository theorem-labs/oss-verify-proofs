(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACfh.v (srz_enter, the journal over a token list), ACk2.v (the file system a closed journal keeps), ACfj.v (tfib_lib_x) and ACfi.v (tfib_lib_x_all) for libreac/fuzz_grant: module paths, GrantB, the library shape grant_shape, and the entry function's phase machine of lib/A/Prog/GrantEntryDefs.v in place of cgif's. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/GrantLibX.v's grant_HTR (a working branch af735a950e2 :184-208): the proof of GrantBContracts.v's IMG_LLVMF_TRACES for the abstract B, with image B's addresses, image B's trace universe lib/B/YCej.v, and each fact about B that image A reads off its concrete record GrantB as a named premise. *)
(* GrantBContracts.v's IMG_LLVMF_TRACES (the image fact of hyps_LLVMFuzzerTestOneInput): the call traces of the six
   malloc / free wrapper calls of LLVMFuzzerTestOneInput are in the trace universe of B.

   Image A proves the same fact at its concrete record GrantB (lib/A/AD2l.v:15, as_code := Tfib_code of
   lib/A/AF0l.v:9, as_universe := Tfib_universe of lib/A/ACej.v:42). Image B has no such record yet (no definition
   of as_universe / Tfib_code / ASyms in lib/B), so img_llvmf_traces_of takes each fact the reduction reads off the
   record as a premise, named after its image-A twin:
     GrantB_as_universe      as_universe B = Tfib_universe       A: AD2l.v:38 as_universe := Tfib_universe
     Tfib_code_pc_malloc_ra0 pc_malloc_ra0 (as_code B) = 0x53178 A: AF0l.v:10 pc_malloc_ra0 := 0x52dec
     Tfib_code_pc_free_ra0   pc_free_ra0 (as_code B) = 0x53018   A: AF0l.v:11 pc_free_ra0 := 0x52c8c
   and, because the contract's BASE is the image instance's pa_val A_TEXT (a fact of PI, not of B):
     grant_val_text          pa_val A_TEXT = grant_text           A: the contract states grant_text itself
                                                                  (lib/A/Prog/GrantAddr.v grant_text)
   img_llvmf_traces_grant discharges the last one at image B's instance PI_grant (GrantImg.v:152, pa_val := grant_val,
   grant_val A_TEXT = grant_text by GrantImg.v:34).

   Image B's numbers, from bin/libreac/asan-ubsan/fuzz_grant.{objdump,nm}.txt:
     LLVMFuzzerTestOneInput = 0x80a3c = grant_text (GrantAddr.v:12; nm :2160, objdump :83911), AF_ = 0 (GrantList.v:11)
     RA_LLVMF_B = 0x80938: target_run's `jal 80a3c <LLVMFuzzerTestOneInput>` at 0x80934 (objdump :83840-83841)
     pc_malloc_ra0 = 0x53178: ___interceptor_malloc's `jal 733e0 <GetCurrentPc>` at 0x53174 (objdump :35896-35897)
     pc_free_ra0 = 0x53018: ___interceptor_free's `jal 733e0 <GetCurrentPc>` at 0x53014 (objdump :35806-35807)
     the malloc wrapper calls (`jal 52edc <__interceptor_trampoline_malloc>`, objdump :35726):
       0x80db4 ra 0x80db8 (:84134), 0x813d0 ra 0x813d4 (:84525), 0x818b4 ra 0x818b8 (:84838)
       = grant_text + TB_LLVMF_MSITES [0x37c; 0x998; 0xe7c]
     the free wrapper calls (`jal 52ed8 <__interceptor_trampoline_free>`, objdump :35723):
       0x81808 ra 0x8180c (:84795), 0x81940 ra 0x81944 (:84873), 0x81da8 ra 0x81dac (:85155)
       = grant_text + TB_LLVMF_FSITES [0xdd0; 0xf08; 0x1370]
   Each of the twelve traces (pc0 :: ra, with or without the caller's ra 0x80938) is in YCej.v's
   TRACES_LLVMFuzzerTestOneInput (:48): the proof decides each membership with memZL on a closed list. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YM05 YG00 YG0f YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantList GrantAddr GrantPa GrantImg GrantBContracts.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCej.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Section b.
Context {PI : PAImg grant_listing}.
Variable B : asyms.

(* The generic step: GrantLibX.v's grant_HTR, with each fact of A's concrete GrantB a premise. *)
Lemma img_llvmf_traces_of
  (GrantB_as_universe : as_universe B = YCej.Tfib_universe)
  (Tfib_code_pc_malloc_ra0 : pc_malloc_ra0 (as_code B) = 0x53178)
  (Tfib_code_pc_free_ra0 : pc_free_ra0 (as_code B) = 0x53018)
  (grant_val_text : @pa_val _ grant_listing PI A_TEXT = grant_text) :
  IMG_LLVMF_TRACES (PI := PI) B.
Proof.
  unfold IMG_LLVMF_TRACES. intros ly regs regsT pcf Hra Hs.
  rewrite grant_val_text, Tfib_code_pc_malloc_ra0, Tfib_code_pc_free_ra0 in Hs.
  rewrite GrantB_as_universe.
  assert (Hc : (pcf = 0x53178 /\ (raZ regsT = 0x80db8 \/ raZ regsT = 0x813d4 \/ raZ regsT = 0x818b8)) \/
               (pcf = 0x53018 /\ (raZ regsT = 0x8180c \/ raZ regsT = 0x81944 \/ raZ regsT = 0x81dac))).
  { unfold TB_LLVMF_MSITES, TB_LLVMF_FSITES, AF_LLVMFuzzerTestOneInput, grant_text in Hs.
    cbn [In] in Hs.
    destruct Hs as [[-> Hm] | [-> Hf]]; [left | right]; (split; [reflexivity|]); lia. }
  remember (raZ regsT) as ra eqn:Era.
  unfold RA_LLVMF_B in Hra.
  destruct (spZ regs + 16 <? ly_top ly).
  - rewrite call_trace_cons, <- Era, Hra. apply YCej.TRACES_LLVMFuzzerTestOneInput_U.
    destruct Hc as [[-> [-> | [-> | ->]]] | [-> [-> | [-> | ->]]]];
      apply YCej.memZL_In; vm_compute; reflexivity.
  - rewrite call_trace_nil, <- Era. apply YCej.TRACES_LLVMFuzzerTestOneInput_U.
    destruct Hc as [[-> [-> | [-> | ->]]] | [-> [-> | [-> | ->]]]];
      apply YCej.memZL_In; vm_compute; reflexivity.
Qed.
End b.

(* At image B's instance PI_grant: the text base is grant_text, so only the three premises about B stay. *)
Lemma grant_val_text_grant : @pa_val _ grant_listing PI_grant A_TEXT = grant_text.
Proof. reflexivity. Qed.

Lemma img_llvmf_traces_grant (B : asyms)
  (GrantB_as_universe : as_universe B = YCej.Tfib_universe)
  (Tfib_code_pc_malloc_ra0 : pc_malloc_ra0 (as_code B) = 0x53178)
  (Tfib_code_pc_free_ra0 : pc_free_ra0 (as_code B) = 0x53018) :
  IMG_LLVMF_TRACES (PI := PI_grant) B.
Proof.
  exact (img_llvmf_traces_of (PI := PI_grant) B GrantB_as_universe Tfib_code_pc_malloc_ra0 Tfib_code_pc_free_ra0
           grant_val_text_grant).
Qed.
End a.
