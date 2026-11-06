(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN0j.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/Reusable/YN0j.v, with its module paths and module names changed; 546 of its 584 lines of code are new or changed and 260 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_segC.v, with its module names changed; 1538 of its 1613 lines of code are new or changed and 509 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_segC2.v, with its module paths changed; 237 of its 289 lines of code are new or changed and 1561 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/FSW_check_no_overread_ret.v, with its module paths and module names changed; 148 of its 183 lines of code are new or changed and 254 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/ACfi.v at origin/ossv/recipes (lines 25-41
   TfibB_libS's errno facts, 72-101 link_ML / link_SMP / link_FFL / link_AMEMSET / link_AMEMCPY, 128-141 the _all form)
   for reac-pw/fuzz_rate image A: the contract is lib/A/RtPgLib.v's rate_lib_x_all_stmt, proved from lib/A/RtPgTopA.v's
   rate_lib_x_A_close at the relocated frame's symbols (AD2l.TfibB), segments (AB1v.tfibsegs), sink (AE2k.tfib_K,
   tfib_sink_head) and constants (ACfn); the frame-flag law reads the image cover of lib/A/AF0x.v; the stack frames of
   classes 1 and 3, the strlen / strcmp / snprintf wrappers and __asan_set_shadow_f5 are the frame's and the runtime
   lanes' walks; the allocation traces and the code entries are checked on TfibB by computation. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; addresses from the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3): THE ENTRY FUNCTION'S PROGRAM CONTRACT,
   RtPgLib.rate_lib_x_all_stmt, the statement the closing (lib/A/AD2o.v) takes as its Section variable rate_lib_x_all.

     rate_lib_x_all : rate_lib_x_all_stmt
       (forall rc LS, LEAF -> free at every fx -> malloc at every fx ->
          forall fx, rt_lib_contract_x tfibsegs TfibB ameter_triv tfib_K XL0 XL0 0x9b6e0 0x9cb68 A_LLVMF ...)

   It instantiates RtPgTopA.rate_lib_x_A_close at TfibB and discharges each of its premises:
   - the harness constants, the sink's overflow head and the empty input's address: by computation on ACfn / AE2k;
   - the sink's laws: AD1u.tfib_AIL; the image's read-only facts and pinned bytes: RtPgRoClose.rate_A_img_facts_tfib /
     rate_A_rom_pinned_tfib (both at any B with TfibSyms B; TfibB_syms holds here);
   - the allocator's model laws (YG05.model_laws_ok), the side stack's progress (YG05.stack_malloc_progress), the
     frame-flag law (AR's al_flag / al_client_img and AF0x's image cover), the allocator environment (errno and the
     two empty traces), the code entries and cells (pc_wrap_malloc 0x52bb4, pc_wrap_free 0x52bb0, pc_asan_memcpy
     0x51860, pc_stack_malloc 1 / 3 = 0x3cf9c / 0x3d2c8, the GOT and runtime cells) and the allocation traces of the
     three mallocs and three frees (all in ACej.Tfib_universe): on TfibB;
   - __asan_memset 0x51cfc (AE2r.asan_memset_realizes), __asan_memcpy 0x51860 (AE2q.asan_memcpy_realizes),
     __asan_stack_malloc_1 (AF0s) and _3 (Rt/StackMalloc3), the strlen wrapper 0x42194 (Rt/Strlen), the strcmp
     wrapper 0x4219c (Rt/Strcmp), the snprintf wrapper 0x421d4 (Rt/SnprintfRate) and __asan_set_shadow_f5 0x54828
     (Rt/SetShadow): the frame's and the runtime lanes' walks, at every float state;
   - the lib shape's leaf law and the allocator's malloc and free: the statement's own premises.
   The one Section hypothesis left is check_csv's contract (CCSV, 0x838e0), proved by lib/A/RtPgCcsvTop.v.
   Proves no function of its own (kind: merge). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d YG05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YCbp.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import SetShadowDef.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require AStrcmpDef.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import Img0 RtPgBase RtPgCSpec RtPgImgA RtPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require RtPgSiteA RtPgE01D RtPgPostMal RtPgW14Mal RtPgX01.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require RtPgTopA RtPgLib RtPgRoClose.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.Rt Require Import StrlenDef SnprintfRateDef.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require AB1v AD2l AE2k ACfn AD1u AF0m AF0x ACej AE2q AE2r AF0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.Rt Require StackMalloc3 Strlen Strcmp SnprintfRate SetShadow.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Local Notation TB := AD2l.TfibB.
Local Notation TBS := AD2l.TfibB_syms.

(* ======================================== facts of TfibB, by computation ======================================== *)
Lemma lk_errno_in_seg : existsb (fun s => (Z.of_N (seg_base s) <=? AF0m.TFIB_ERRNO) &&
  (AF0m.TFIB_ERRNO + 4 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lk_api_env : api_env rsegs TB.
Proof.
split; [rewrite (AF0m.ts_errno TB TBS); unfold AF0m.TFIB_ERRNO, kLowMemEnd; lia|].
split.
- intros a Ha. rewrite (AF0m.ts_errno TB TBS) in Ha.
  pose proof lk_errno_in_seg as C. apply existsb_exists in C as (s & Hs & Hb).
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1, H2.
  exists s. split; [exact Hs | lia].
- split; apply ACej.memZL_In; vm_compute; reflexivity.
Qed.

Lemma lk_HPCM : pc_wrap_malloc (as_code TB) = 0x52bb4. Proof. vm_compute. reflexivity. Qed.
Lemma lk_HFREE : pc_wrap_free (as_code TB) = RtPgX01.RTX_FREE. Proof. vm_compute. reflexivity. Qed.
Lemma lk_HPCMC : pc_asan_memcpy (as_code TB) = 0x51860. Proof. vm_compute. reflexivity. Qed.
Lemma lk_HPCS1 : pc_stack_malloc (as_code TB) 1 = 0x3cf9c. Proof. vm_compute. reflexivity. Qed.
Lemma lk_HPCS3 : pc_stack_malloc (as_code TB) 3 = 0x3d2c8. Proof. vm_compute. reflexivity. Qed.
Lemma lk_HGOT : as_got_shadow TB = 0x9be70. Proof. vm_compute. reflexivity. Qed.
Lemma lk_HSC : as_shadow_cell TB = 0xa4c38. Proof. vm_compute. reflexivity. Qed.
Lemma lk_HGOTU : as_got_uar TB = 0x9bec8. Proof. vm_compute. reflexivity. Qed.
Lemma lk_HUAR : as_uar_cell TB = 0xa4c40. Proof. vm_compute. reflexivity. Qed.

(* The malloc traces: the return to r from the malloc wrapper, then optionally the harness's return RA_LLVMF. *)
Lemma lk_malloc_trace : forall (regsT : bvmap 5 word) (ch : list (Z * Z * Z)) r,
  raZ regsT = r -> (ch = [] \/ exists fp ra v, ch = [(fp, ra, v)] /\ ra = ACfn.RA_LLVMF) ->
  ACej.memZL [pc_malloc_ra0 (as_code TB); r] ACej.Tfib_universe = true ->
  ACej.memZL [pc_malloc_ra0 (as_code TB); r; ACfn.RA_LLVMF] ACej.Tfib_universe = true ->
  r <> pc_malloc_ra0 (as_code TB) ->
  In (call_trace0 (pc_malloc_ra0 (as_code TB)) regsT ch) (as_universe TB).
Proof.
intros regsT ch r Hr Hch M1 M2 Hne.
assert (EU : as_universe TB = ACej.Tfib_universe) by reflexivity. rewrite EU.
assert (Ers : pc_malloc_ra0 (as_code TB) = 0x52e50) by (vm_compute; reflexivity).
unfold call_trace0, unwind_of_chain. rewrite Hr.
destruct Hch as [->|(fp & ra & v & -> & ->)]; cbn [flat_map app].
- destruct (Z.eqb_spec r (pc_malloc_ra0 (as_code TB))) as [E|_]; [exfalso; exact (Hne E)|].
  apply ACej.memZL_In. rewrite Ers in *. vm_compute. vm_compute in M1. exact M1.
- destruct (Z.eqb_spec r (pc_malloc_ra0 (as_code TB))) as [E|_]; [exfalso; exact (Hne E)|].
  apply ACej.memZL_In. rewrite Ers in *. vm_compute. vm_compute in M2. exact M2.
Qed.

Lemma lk_HTRACE_E01 : RtPgE01D.e01_trace_stmt TB ACfn.RA_LLVMF.
Proof.
intros regsT ch Hra Hch. apply (lk_malloc_trace regsT ch _ Hra);
  [| vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; discriminate].
destruct Hch as [->|(fp & v & ->)]; [left; reflexivity | right; exists fp, ACfn.RA_LLVMF, v; split; reflexivity].
Qed.

Lemma lk_HTRACE_C23 : forall (regsT : bvmap 5 word) (hx : rh_hcx rsegs),
  raZ (h_regs _ hx) = ACfn.RA_LLVMF -> raZ regsT = RS_C3 ->
  In (call_trace0 (pc_malloc_ra0 (as_code TB)) regsT (RtPgPostMal.rt_c23_ch hx)) (as_universe TB).
Proof.
intros regsT hx Hhx Hra. apply (lk_malloc_trace regsT _ _ Hra);
  [| vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; discriminate].
unfold RtPgPostMal.rt_c23_ch. destruct (_ <? _); [right; do 3 eexists; split; [reflexivity | exact Hhx] | left; reflexivity].
Qed.

Lemma lk_HTRACE_C46 : forall (regsT : bvmap 5 word) (hx : rh_hcx rsegs),
  raZ (h_regs _ hx) = ACfn.RA_LLVMF -> raZ regsT = RS_C6 ->
  In (call_trace0 (pc_malloc_ra0 (as_code TB)) regsT (RtPgW14Mal.w14m_ch hx)) (as_universe TB).
Proof.
intros regsT hx Hhx Hra. apply (lk_malloc_trace regsT _ _ Hra);
  [| vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; discriminate].
unfold RtPgW14Mal.w14m_ch. destruct (_ <? _); [right; do 3 eexists; split; [reflexivity | exact Hhx] | left; reflexivity].
Qed.

Lemma lk_HTRACE : forall c,
  In c [[RtPgX01.RTX_RA1]; [RtPgX01.RTX_RA1; ACfn.RA_LLVMF]; [RtPgX01.RTX_RA2]; [RtPgX01.RTX_RA2; ACfn.RA_LLVMF];
        [RtPgX01.RTX_RA3]; [RtPgX01.RTX_RA3; ACfn.RA_LLVMF]] ->
  In (firstn kUnwindMax (pc_free_ra0 (as_code TB) :: flat_map (fun r => if r =? pc_free_ra0 (as_code TB) then [] else [r]) c))
  (as_universe TB).
Proof.
intros c Hc. cbn [In] in Hc.
repeat (destruct Hc as [<-|Hc]; [apply ACej.memZL_In; vm_compute; reflexivity|]). contradiction.
Qed.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Let LAWS : AR_laws rsegs TB := AR_laws_ok rsegs TB.

Lemma lk_ML : model_laws (as_universe TB).
Proof. exact (model_laws_ok (as_universe TB) (AF0m.ts_universe TB TBS)). Qed.

Lemma lk_SMP : stack_malloc_progressP TB.
Proof. intros s cid W Hc Hn. exact (stack_malloc_progress (as_universe TB) s cid W Hc Hn). Qed.

(* [cgif ACfi.v:76-87, link_FFL] *)
Lemma lk_FFL : frame_flag_lawP rsegs TB.
Proof.
intros ly S W mem md cid pos HAR Hin.
destruct (al_flag _ _ LAWS ly S W mem md cid pos HAR Hin) as (Hp & Ho & Happ & Hceil).
destruct (al_client_img _ _ LAWS ly S W mem md (flag_addr ly cid pos) HAR) as [Hhull Himg].
{ right. right. exists cid, pos. split; [exact Hin | reflexivity]. }
pose proof HAR as (M & L & _). pose proof (AF0x.img_cover_of_ledger ly S md L) as [C1 C2].
unfold AF0x.TFIB_IMG_LO, AF0x.TFIB_IMG_END in C1, C2.
destruct Happ as [H4096 Hz]. unfold in_zr in Hhull.
split; [exact Hp|]. split; [exact Ho|]. split.
- split; [|exact Himg]. unfold app_addr, in_app, ASAN_CEIL in *. lia.
- split; [exact H4096|]. split; [|exact Hceil]. unfold zone2, off_img, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

Lemma lk_ASM1 : astack_malloc_realizes rsegs TB 1.
Proof.
intros ly S W regs mem md pos S' HPRE Hc Hp. rewrite lk_HPCS1.
exact (AF0s.tfib_stack_malloc_at TB LAWS TBS ly S W regs mem md pos S' HPRE Hc Hp).
Qed.

Lemma lk_ASM3 : astack_malloc_realizes rsegs TB 3.
Proof.
intros ly S W regs mem md pos S' HPRE Hc Hp. rewrite lk_HPCS3.
exact (StackMalloc3.tfib_stack_malloc_at TB LAWS TBS ly S W regs mem md pos S' HPRE Hc Hp).
Qed.

(* [cgif ACfi.v:92-101, link_AMEMSET / link_AMEMCPY] *)
Lemma lk_AMEMSET : aintrin_realizes rsegs TB OSet 0x51cfc.
Proof.
intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull _.
exact (AE2r.asan_memset_realizes TB LAWS TBS ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Hra Hhull Ham).
Qed.

Lemma lk_AMEMCPY : aintrin_realizes rsegs TB OCpy 0x51860.
Proof.
intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull Hsrc.
exact (AE2q.asan_memcpy_realizes TB LAWS TBS ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull Hsrc).
Qed.

Lemma lk_ASTRLEN : astrlen_realizes rsegs TB 0x42194.
Proof. exact (Strlen.strlen_icpt_contract TB LAWS TBS). Qed.

Lemma lk_ASTRCMP : AStrcmpDef.astrcmp_realizes rsegs TB 0x4219c.
Proof. exact (Strcmp.strcmp_icpt_contract TB LAWS TBS). Qed.

Lemma lk_ASNP : rate_snprintf_sd_realizes rsegs TB 0x421d4.
Proof. exact SnprintfRate.rate_snprintf_sd. Qed.

Lemma lk_ASHF5 : aset_shadow_realizes rsegs TB 0x54828 0xf5.
Proof. exact (SetShadow.disco_set_shadow_f5 TB LAWS TBS). Qed.

Lemma lk_AIL : asink_img_laws (SK := AE2k.tfib_sink_head) rsegs TB AE2k.tfib_K.
Proof. exact (AD1u.tfib_AIL TB TBS). Qed.

Lemma lk_IMGF : RtPgSiteA.rate_A_img_facts rsegs TB.
Proof. exact (RtPgRoClose.rate_A_img_facts_tfib TB TBS). Qed.

Lemma lk_PIN : rt_rom_pinned rsegs TB.
Proof. exact (RtPgRoClose.rate_A_rom_pinned_tfib TB TBS). Qed.
End k.

(* ======================================== the statement ======================================== *)
Section l.
(* check_csv (0x838e0, class-2 frame, closed_list 0x21520) at every float state: proved by lib/A/RtPgCcsvTop.v *)
Hypothesis CCSV : forall (rc : YM05.RunCeil) (fy : YK11.FPState),
  rt_check_csv_specX (fx := fy) (rc := rc) (SK := AE2k.tfib_sink_head) rsegs TB ameter_triv 0x838e0 2
    RtPgSiteA.T_csv_STK 0x21520.

Theorem rate_lib_x_all : RtPgLib.rate_lib_x_all_stmt.
Proof.
intros rc LS LEAF AFREE AMALLOC fx.
unfold RtPgLib.rate_lib_contract_x, RtPgLib.XL0, RtPgLib.RO_LO, RtPgLib.RO_HI.
eapply (@RtPgTopA.rate_lib_x_A_close fx rc AE2k.tfib_sink_head LS).
all: first
  [ exact LEAF | exact AFREE | exact AMALLOC | exact (CCSV rc)
  | exact lk_IMGF | exact lk_PIN | exact lk_AIL | exact lk_ML | exact lk_api_env | exact lk_FFL | exact lk_SMP
  | exact lk_ASM3 | exact lk_HPCS3 | exact lk_HGOT | exact lk_HSC | exact lk_HGOTU | exact lk_HUAR
  | (intros fy; exact (@lk_ASM1 fy rc)) | exact lk_HPCS1 | exact lk_HPCMC
  | (intros fy; exact (@lk_ASNP fy rc)) | exact lk_HPCM | exact lk_HFREE
  | (intros fy; exact (@lk_AMEMSET fy rc)) | (intros fy; exact (@lk_AMEMCPY fy rc)) | exact lk_ASTRLEN
  | (intros fy; exact (@lk_ASTRCMP fy rc)) | (intros fy; exact (@lk_ASHF5 fy rc))
  | exact lk_HTRACE_E01 | exact lk_HTRACE_C23 | exact lk_HTRACE_C46 | exact lk_HTRACE
  | (cbn [YI16.sk_ofl_head AE2k.tfib_sink_head]; unfold AE2k.A_ofl_head; lia)
  | reflexivity
  | (apply Z.leb_le; vm_compute; reflexivity)
  | (split; apply Z.ltb_lt; vm_compute; reflexivity) ].
Qed.
End l.

Print Assumptions rate_lib_x_all.
