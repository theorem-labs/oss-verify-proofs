(* reac-pw/fuzz_link image A (fuzz_link.asan, pin 059dae63e07c): the contract of the calloc wrapper
   (wrapper_calloc = __interceptor_trampoline_calloc 0x540d0, the 4-byte jump to the runtime's ___interceptor_calloc
   0x544cc), and the call rule a walk of link's own code applies at its two calloc sites, LLVMFuzzerTestOneInput 0x82c74
   (calloc(1, 8856)) and 0x82c84 (calloc(1, 516)), for every certificate B of link's image: PcapSyms B (lib/A/AF0m.v),
   TfibLib B (lib/A/ACeh.v: errno below kLowMemEnd and in the image, the trace universe is ACejUniv.Tfib_univ) and the
   depot hash of the image (the premise lib/A/AF0w.v tfib_amalloc_realizes takes for malloc).  Link's own certificate is
   lib/A/AD2l.v PcapB (PcapB_syms, PcapBFacts.PcapB_lib, and its depot hash by definition).

   The rows are libreac/fuzz_decode's lib/A/DecodeClose.v rows H_CALLOC_ALLOCATE .. H_CALLOC_IMG_CONST,
   H_CALLOC_ERRNO_LOW, HB_CALLOC_UNIV0, CALLOC_REALIZES and H_LINK_CALLOC04 (origin/ossv/recipes a34e09bd40c1), each
   discharged by the ported row file it names there (lib/A/DecodeARows.v, DecodeARowsRt.v, DecodeARowsFill.v,
   DecodeACallocTp.v, DecodeACallocAllocate.v), with link's certificate facts in place of decode's GrantB ones.

   - [link_calloc_realizes]: the realizes form, DecodeCalloc.v decode_acalloc_A at B, i.e.
     YGCalloc.acalloc_realizes_cgif tfibsegs B 0x540d0 0x545a0 DEC_CALLOC_MAX DEC_CALLOC_DEPTH
     (DEC_CALLOC_MAX = 8856, DEC_CALLOC_DEPTH = 2192, lib/Lib/DecodeCallocKit.v): from the call precondition
     acall_pre at the trampoline, with nm in a0, sz in a1, 0 <= nm, 0 <= sz, nm * sz < MALLOC_MAX, nm * sz <= 8856,
     blocks_bytes S + nm * sz <= LIVE_MAX, ly_bot ly + 2192 < sp and the trace (call_trace ly 0x545a0 regs ch) in the
     fixed trace universe, the run realizes the allocator model's malloc tree at n = nm * sz and lands in malloc's
     leaf at n plus the zero bytes [res, res + nm * sz).
   - [link_calloc_univ0]: the one-element trace [0x545a0] is in B's fixed trace universe (lib/A/ACej.v lists it, with
     the two-element traces of both sites).
   - [link_acalloc04]: YGCalloc.acalloc04_rule at link's journal (YCbq.ajournal at the sink head SK), YCbq.acall_kept
     and the trivial meter, pc 0x540d0, trace pc0 0x545a0, cmax 8856, cdepth 2192; from YCbpCalloc.acalloc04_rule_triv
     as DecodeClose.v:562 H_LINK_CALLOC04 has it.  Its post gives one allocation event, 4096 <= res (so neither
     `bnez` at 0x82c88 / 0x82c90 reaches the abort path), the block appended to ablocks, and nm * sz zero bytes. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG05 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YCbq YI16 YC5d YCbp YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YGCalloc YCbpCalloc YF0p.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import DecodeCallocKit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m AFl0 ACeh DecodeCalloc DecodeCallocRt.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require ACej DecodeCallocTop DecodeACallocAllocate.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require DecodeARows DecodeARowsRt DecodeARowsFill DecodeACallocTp.
Import ListNotations.
Open Scope Z_scope.

Section c.
Variable B : asyms.
(* The image's symbol record (lib/A/AF0m.v). *)
Hypothesis TS : PcapSyms B.
(* The library facts of the record (lib/A/ACeh.v): errno, the trace universe. *)
Hypothesis TL : TfibLib B.
(* The record's depot hash is the image's (lib/A/AFem.v tfib_depot_ok takes it, as for malloc). *)
Hypothesis HD : forall t, as_dhash B t = tfib_dhash t.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* DecodeClose.v:650 CALLOC_REALIZES, row for row. *)
Theorem link_calloc_realizes : decode_acalloc_A B.
Proof.
apply (@DecodeCallocTop.decode_acalloc_of_allocate_A_holds fx rc B).
- exact (DecodeARows.dec_a_img_cover B fx rc).
- exact (DecodeACallocTp.H_CALLOC_TP_holds B TS).
- exact (DecodeARows.dec_a_inst B TS).
- exact (DecodeARowsRt.dec_a_rt_try fx rc).
- exact (DecodeARowsRt.dec_a_rt_mcs fx rc).
- exact (DecodeARowsRt.dec_a_rt_getpc fx rc).
- exact (DecodeARows.dec_a_rt_unw fx rc).
- exact (DecodeARowsFill.dec_a_fill fx rc B).
- exact (DecodeARows.dec_a_cells B TS fx rc).
- apply AR_laws_ok.
- exact (DecodeARows.dec_a_img_const B TS).
- exact (tl_errno B TL).
- exact DEC_CALLOC_MAX_prim.
- exact (@DecodeACallocAllocate.decode_aalloc_A_of_record fx rc B TS HD).
Qed.
End a.

(* DecodeClose.v:521 HB_CALLOC_UNIV0: B's universe is ACejUniv.Tfib_univ (tl_universe), decided against lib/A/ACej.v. *)
Lemma link_calloc_univ0 : In [DEC_A_calloc_ra0] (as_universe B).
Proof. rewrite (tl_universe B TL). apply ACej.memZL_In. vm_compute. reflexivity. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}
  {SK : OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable.YI16.sink_head}.
(* DecodeClose.v:562 H_LINK_CALLOC04 at the trivial meter, for every sink head SK (passed by name, as
   lib/A/PcapBFacts.v passes it to the malloc and free rules; written by its full path: lib/A/DecodeCalloc.v loads
   lib/U/Reusable/YI16.v too, and the short name YI16 resolves to that one here). *)
Definition link_acalloc04 :
  acalloc04_rule tfibsegs B (as_universe B) (@ajournal rc SK tfibsegs B) (@acall_kept rc tfibsegs B)
    (mo_ok ameter_triv) (mo_le ameter_triv) (mo_malloc ameter_triv)
    DEC_A_wrap_calloc DEC_A_calloc_ra0 DEC_CALLOC_MAX DEC_CALLOC_DEPTH :=
  acalloc04_rule_triv (SK := SK) tfibsegs B tfib_segs_low (tl_env B TL) (AR_laws_ok tfibsegs B)
    (model_laws_ok (as_universe B) (ts_universe B TS))
    DEC_A_wrap_calloc DEC_A_calloc_ra0 DEC_CALLOC_MAX DEC_CALLOC_DEPTH link_calloc_univ0 link_calloc_realizes.
End b.
End c.
