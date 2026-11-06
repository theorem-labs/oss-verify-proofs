(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v aj_intrin_at at 28fdc66416e (the call of
   __asan_memcpy in the journal) restated as hd_memcpy with the wrapper's same_but_materialized kept in the post as
   same_io, and proofs/reac-pw/fuzz_role/lib/A/RPgM02Base.v at 9e73ed57244 (m2_img_zone, m2_cstr_kept, the .rodata
   zone of m2_szone) restated as hd_img_zone / hd_cstr_kept / hd_szone for the .rodata range only; the rest of the
   file is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgScanHead.v, with its module paths, module names and addresses changed; 1418 of its 1528 lines of code are new or changed and 904 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgW3a.v, with its module names changed; 149 of its 182 lines of code are new or changed and 1495 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgE01Ha.v at ba6d82f81177 for image B
   (fuzz_rate.asan-ubsan): image B's pcs (HD 0x809bc, the malloc trampoline 0x52c0c), registers (cursor s2 = x18,
   shadow offset s4 = x20), the leaf's registers 1 10 18 21 22 23 26 and slots R+0x30 .. R+0x148, and the write
   window R+0x30 .. R+0x150. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/AU/RtPgE01HaB.v, with its module names changed; 39 of its 61 lines of code are new or changed and 160 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgE01H.v at ba6d82f81177 for image B
   (fuzz_rate.asan-ubsan): image B's part statement lib/AU/RtPgE01DB.v e01b_hdr_stmt, pcs and stack bound, and the
   kit and arms of lib/AU/RtPgE01HkB.v and lib/AU/RtPgE01HaB.v. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, same loaded bytes): part HDR of segment S_E01
   of the walk of LLVMFuzzerTestOneInput, lib/AU/RtPgE01DB.v e01b_hdr_stmt: from HD 0x809bc (the frame's header and
   shadow written) to CALL 0x52c0c (the `jal` of malloc(19744) at 0x80ae0, ra = 0x80ae4): the seven header reads in
   their input-length arms, each after its UBSan pointer-overflow test and behind its instrumented 1-byte check, the
   spills of the six header slots, s10 = buflen, s6 = 0x5000, s5 = a0 = 19744. Proves no function (kind: segment
   lemma).

   The input length n splits the walk at the Coq level into n = 0, 1, .., 7 and n >= 8 (lib/AU/RtPgE01HaB.v
   e01hb_arm0 .. e01hb_arm8, one engine run each; n = 7 and n >= 8 differ only in the input's first metadata byte);
   each run ends in RtPgE01HkB.e01hb_leaf, which RtPgE01HkB.e01hb_call_of turns into the call state e01b_call_facts
   at the run's quantities e01hb_env (the header bytes, 0 past the input's end; src = p + min 7 n, left =
   n - min 7 n), from which the continuation e01b_from_call runs. Templates: lib/A/RtPgE01H.v (image A's part) and
   the two files above. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgSegB RtPgE01DB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgE01HkB RtPgE01HaB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variables RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
Hypothesis HSTK : 0x230 + ASTACK <= LLVMF_STK.
Hypothesis HEMPTY : 0 < A_EMPTY < kLowMemEnd.
Hypothesis HSTATIC : rhb_static_law rsegs B RLO RHI.
Hypothesis HRELRO : forall a, RLO <= a < RHI -> in_img rsegs a.
Theorem e01b_hdr_ok : e01b_hdr_stmt B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof.
intros hx POST Hb HK pos lyc Sc W regs mem md Hhd.
assert (Hn0 : 0 <= h_n rsegs hx) by (pose proof Hb as (_ & _ & _ & _ & _ & Hlen & _); rewrite Hlen; lia).
(* each arm's leaf is the call state, from which the continuation runs *)
assert (KC : forall regs' mem' md', e01hb_leaf B LLVMF_STK hx pos lyc Sc W regs mem regs' mem' md' ->
  SRr rsegs W (cfg_at rsegs E01B_MALLOC regs' mem' md') POST).
{ intros regs' mem' md' HL. apply (HK pos (e01hb_env hx pos) (skipn 7 (h_pl rsegs hx)) lyc Sc W regs' mem' md').
  exact (e01hb_call_of B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK HSTK HEMPTY
           hx pos lyc Sc W regs mem md regs' mem' md' Hb Hhd HL). }
(* the input-length arms (n = 7 and n >= 8 apart: the input's first metadata byte is 7, resp. 0) *)
assert (Hc : h_n rsegs hx = 0 \/ h_n rsegs hx = 1 \/ h_n rsegs hx = 2 \/ h_n rsegs hx = 3 \/ h_n rsegs hx = 4 \/
             h_n rsegs hx = 5 \/ h_n rsegs hx = 6 \/ h_n rsegs hx = 7 \/ 8 <= h_n rsegs hx) by lia.
destruct Hc as [H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]].
- exact (e01hb_arm0 B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK HSTK HEMPTY HSTATIC HRELRO
           hx pos lyc Sc W regs mem md POST Hb Hhd H KC).
- exact (e01hb_arm1 B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK HSTK HEMPTY HSTATIC HRELRO
           hx pos lyc Sc W regs mem md POST Hb Hhd H KC).
- exact (e01hb_arm2 B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK HSTK HEMPTY HSTATIC HRELRO
           hx pos lyc Sc W regs mem md POST Hb Hhd H KC).
- exact (e01hb_arm3 B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK HSTK HEMPTY HSTATIC HRELRO
           hx pos lyc Sc W regs mem md POST Hb Hhd H KC).
- exact (e01hb_arm4 B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK HSTK HEMPTY HSTATIC HRELRO
           hx pos lyc Sc W regs mem md POST Hb Hhd H KC).
- exact (e01hb_arm5 B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK HSTK HEMPTY HSTATIC HRELRO
           hx pos lyc Sc W regs mem md POST Hb Hhd H KC).
- exact (e01hb_arm6 B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK HSTK HEMPTY HSTATIC HRELRO
           hx pos lyc Sc W regs mem md POST Hb Hhd H KC).
- exact (e01hb_arm7 B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK HSTK HEMPTY HSTATIC HRELRO
           hx pos lyc Sc W regs mem md POST Hb Hhd H KC).
- exact (e01hb_arm8 B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK HSTK HEMPTY HSTATIC HRELRO
           hx pos lyc Sc W regs mem md POST Hb Hhd H KC).
Qed.
End b.

Print Assumptions e01b_hdr_ok.
