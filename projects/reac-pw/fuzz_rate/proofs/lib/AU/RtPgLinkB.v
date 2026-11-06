(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN0j.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/Reusable/YN0j.v, with its module paths and module names changed; 546 of its 584 lines of code are new or changed and 260 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_segC.v, with its module names changed; 1538 of its 1613 lines of code are new or changed and 509 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_segC2.v, with its module paths changed; 237 of its 289 lines of code are new or changed and 1561 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/FSW_check_no_overread_ret.v, with its module paths and module names changed; 144 of its 179 lines of code are new or changed and 254 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/ACfi.v at origin/ossv/recipes (lines 25-41
   TfibB_libS's errno facts, 72-101 link_ML / link_SMP / link_FFL / link_AMEMSET / link_AMEMCPY, 128-141 the _all form)
   for reac-pw/fuzz_rate image A: the contract is lib/A/RtPgLib.v's rate_lib_x_all_stmt, proved from lib/A/RtPgTopA.v's
   rate_lib_x_A_close at the relocated frame's symbols (AD2l.TfibB), segments (AB1v.tfibsegs), sink (AE2k.tfib_K,
   tfib_sink_head) and constants (ACfn); the frame-flag law reads the image cover of lib/A/AF0x.v; the stack frames of
   classes 1 and 3, the strlen / strcmp / snprintf wrappers and __asan_set_shadow_f5 are the frame's and the runtime
   lanes' walks; the allocation traces and the code entries are checked on TfibB by computation. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgLink.v at af0538adbf24 for image B
   (fuzz_rate.asan-ubsan): the contract is lib/AU/RtPgLibB.v's rate_lib_x_all_stmt_B, proved from lib/AU/RtPgTopAB.v's
   rate_lib_x_B at image B's core (lib/AU YB1v / YD2l / YE2k / YCfn / YD1u / YF0m / YF0x / YCej / YE2q / YE2r); the
   frames are classes 1, 2 and 4 (YF0s, YF0u, Rt/StackMalloc4), the bcmp wrapper is YE2s's, check_csv and
   reac_rate_drivable_csv are their walks, the image's read-only facts are lib/AU/RtPgRoCloseB.v's, and the strlen /
   strcmp / set_shadow_f5 / snprintf wrappers are image B's runtime walks (lib/AU/Rt/Strlen.v, Strcmp.v, SetShadow.v,
   SnprintfRate.v). *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; addresses from the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1): THE ENTRY FUNCTION'S PROGRAM CONTRACT,
   RtPgLibB.rate_lib_x_all_stmt_B, the statement image B's closing (lib/AU/YD2o.v) takes as its Section variable.

     rate_lib_x_all_B : rate_lib_x_all_stmt_B
       (forall rc LS, LEAF -> free at every fx -> malloc at every fx ->
          forall fx, rt_lib_contract_x tfibsegs TfibB ameter_triv tfib_K XL0_B XL0_B 0x9b9e0 0x9ce68 A_LLVMF ...)

   It instantiates RtPgTopAB.rate_lib_x_B at TfibB and discharges each of its premises:
   - the harness constants, the sink's overflow head and the empty input's address: by computation on YCfn / YE2k;
   - the sink's laws: YD1u.tfib_AIL; the image's read-only facts and pinned bytes: RtPgRoCloseB.rate_B_img_facts_tfib /
     rate_B_rom_pinned_tfib (both at any B with TfibSyms B; YD2l.TfibB_syms holds here);
   - the allocator's model laws (YG05.model_laws_ok), the side stack's progress (YG05.stack_malloc_progress), the
     frame-flag law (AR's al_flag / al_client_img and YF0x's image cover), the allocator environment (errno and the
     two empty traces), the code entries and cells (pc_wrap_malloc 0x52c0c, pc_wrap_free 0x52c08, pc_asan_memcpy
     0x518b8, pc_stack_malloc 1 / 2 / 4 = 0x3cfd4 / 0x3d164 / 0x3d300, the GOT and runtime cells) and the allocation
     traces of the three mallocs and three frees (all in YCej.Tfib_universe): on TfibB;
   - __asan_memset 0x51d54 (YE2r.asan_memset_realizes), __asan_memcpy 0x518b8 (YE2q.asan_memcpy_realizes),
     __asan_stack_malloc_1 / _2 / _4 (YF0s, YF0u, Rt/StackMalloc4) and the bcmp wrapper 0x42200
     (YE2s.bcmp_icpt_contract): the core's walks, at every float state;
   - the lib shape's leaf law and the allocator's malloc and free: the statement's own premises.
   - the strlen wrapper 0x421ec (lib/AU/Rt/Strlen.v strlen_icpt_contract, in lib/A/Rt/StrlenDef.v's parametric form),
     the strcmp wrapper 0x421f4 (lib/AU/Rt/Strcmp.v strcmp_icpt_contract), __asan_set_shadow_f5 0x54880
     (lib/AU/Rt/SetShadow.v disco_set_shadow_f5) and the snprintf wrapper 0x4222c (lib/AU/Rt/SnprintfRate.v
     rate_snprintf_sd, in lib/AU/Rt/SnprintfRateDef.v's text, which RtPgDcsvDefsB.v repeats word for word): the
     runtime lane's walks, at every float state.
   No Section hypothesis is left: rate_lib_x_all_B is closed. Proves no function of its own (kind: merge). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.Rt Require Import StrlenDef.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import Img0 RtPgImgB RtPgSegB RtPgSiteB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require RtPgE01DB RtPgPostMalB RtPgW14MalB RtPgX01B RtPgDcsvDefsB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require RtPgTopAB RtPgLibB RtPgRoCloseB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require YB1v YD2l YE2k YCfn YD1u YF0m YF0x YCej YE2q YE2r YE2s YF0s YF0u.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU.Rt Require StackMalloc4 Strlen Strcmp SetShadow SnprintfRate.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Local Notation TB := YD2l.TfibB.
Local Notation TBS := YD2l.TfibB_syms.

(* ======================================== facts of TfibB, by computation ======================================== *)
Lemma lk_errno_in_seg : existsb (fun s => (Z.of_N (seg_base s) <=? YF0m.TFIB_ERRNO) &&
  (YF0m.TFIB_ERRNO + 4 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lk_api_env : api_env rsegs TB.
Proof.
split; [rewrite (YF0m.ts_errno TB TBS); unfold YF0m.TFIB_ERRNO, kLowMemEnd; lia|].
split.
- intros a Ha. rewrite (YF0m.ts_errno TB TBS) in Ha.
  pose proof lk_errno_in_seg as C. apply existsb_exists in C as (s & Hs & Hb).
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1, H2.
  exists s. split; [exact Hs | lia].
- split; apply YCej.memZL_In; vm_compute; reflexivity.
Qed.

Lemma lk_HPCM : pc_wrap_malloc (as_code TB) = 0x52c0c. Proof. vm_compute. reflexivity. Qed.
Lemma lk_HFREE : pc_wrap_free (as_code TB) = 0x52c08. Proof. vm_compute. reflexivity. Qed.
Lemma lk_HPCMC : pc_asan_memcpy (as_code TB) = 0x518b8. Proof. vm_compute. reflexivity. Qed.
Lemma lk_HPCS1 : pc_stack_malloc (as_code TB) 1 = 0x3cfd4. Proof. vm_compute. reflexivity. Qed.
Lemma lk_HPCS2 : pc_stack_malloc (as_code TB) 2 = 0x3d164. Proof. vm_compute. reflexivity. Qed.
Lemma lk_HPCS4 : pc_stack_malloc (as_code TB) 4 = 0x3d300. Proof. vm_compute. reflexivity. Qed.
Lemma lk_HGOT : as_got_shadow TB = 0x9c170. Proof. vm_compute. reflexivity. Qed.
Lemma lk_HSC : as_shadow_cell TB = 0xa4f38. Proof. vm_compute. reflexivity. Qed.
Lemma lk_HGOTU : as_got_uar TB = 0x9c1c8. Proof. vm_compute. reflexivity. Qed.
Lemma lk_HUAR : as_uar_cell TB = 0xa4f40. Proof. vm_compute. reflexivity. Qed.

(* The malloc traces: the return to r from the malloc wrapper, then optionally the harness's return RA_LLVMF. *)
Lemma lk_malloc_trace : forall (regsT : bvmap 5 word) (ch : list (Z * Z * Z)) r,
  raZ regsT = r -> (ch = [] \/ exists fp ra v, ch = [(fp, ra, v)] /\ ra = YCfn.RA_LLVMF) ->
  YCej.memZL [pc_malloc_ra0 (as_code TB); r] YCej.Tfib_universe = true ->
  YCej.memZL [pc_malloc_ra0 (as_code TB); r; YCfn.RA_LLVMF] YCej.Tfib_universe = true ->
  r <> pc_malloc_ra0 (as_code TB) ->
  In (call_trace0 (pc_malloc_ra0 (as_code TB)) regsT ch) (as_universe TB).
Proof.
intros regsT ch r Hr Hch M1 M2 Hne.
assert (EU : as_universe TB = YCej.Tfib_universe) by reflexivity. rewrite EU.
assert (Ers : pc_malloc_ra0 (as_code TB) = 0x52ea8) by (vm_compute; reflexivity).
unfold call_trace0, unwind_of_chain. rewrite Hr.
destruct Hch as [->|(fp & ra & v & -> & ->)]; cbn [flat_map app].
- destruct (Z.eqb_spec r (pc_malloc_ra0 (as_code TB))) as [E|_]; [exfalso; exact (Hne E)|].
  apply YCej.memZL_In. rewrite Ers in *. vm_compute. vm_compute in M1. exact M1.
- destruct (Z.eqb_spec r (pc_malloc_ra0 (as_code TB))) as [E|_]; [exfalso; exact (Hne E)|].
  apply YCej.memZL_In. rewrite Ers in *. vm_compute. vm_compute in M2. exact M2.
Qed.

Lemma lk_HTRACE_E01 : RtPgE01DB.e01b_trace_stmt TB YCfn.RA_LLVMF.
Proof.
intros regsT ch Hra Hch. apply (lk_malloc_trace regsT ch _ Hra);
  [| vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; discriminate].
destruct Hch as [->|(fp & v & ->)]; [left; reflexivity | right; exists fp, YCfn.RA_LLVMF, v; split; reflexivity].
Qed.

Lemma lk_HTRACE_C23 : forall (regsT : bvmap 5 word) (hx : rhb_hcx rsegs),
  raZ (h_regs _ hx) = YCfn.RA_LLVMF -> raZ regsT = RSB_C3 ->
  In (call_trace0 (pc_malloc_ra0 (as_code TB)) regsT (RtPgPostMalB.rtb_c23_ch hx)) (as_universe TB).
Proof.
intros regsT hx Hhx Hra. apply (lk_malloc_trace regsT _ _ Hra);
  [| vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; discriminate].
unfold RtPgPostMalB.rtb_c23_ch. destruct (_ <? _); [right; do 3 eexists; split; [reflexivity | exact Hhx] | left; reflexivity].
Qed.

Lemma lk_HTRACE_C46 : forall (regsT : bvmap 5 word) (hx : rhb_hcx rsegs),
  raZ (h_regs _ hx) = YCfn.RA_LLVMF -> raZ regsT = RSB_C6 ->
  In (call_trace0 (pc_malloc_ra0 (as_code TB)) regsT (RtPgW14MalB.w14m_ch hx)) (as_universe TB).
Proof.
intros regsT hx Hhx Hra. apply (lk_malloc_trace regsT _ _ Hra);
  [| vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; discriminate].
unfold RtPgW14MalB.w14m_ch. destruct (_ <? _); [right; do 3 eexists; split; [reflexivity | exact Hhx] | left; reflexivity].
Qed.

Lemma lk_HTRACE : forall c,
  In c [[RtPgX01B.RTXB_RA1]; [RtPgX01B.RTXB_RA1; YCfn.RA_LLVMF]; [RtPgX01B.RTXB_RA2]; [RtPgX01B.RTXB_RA2; YCfn.RA_LLVMF];
        [RtPgX01B.RTXB_RA3]; [RtPgX01B.RTXB_RA3; YCfn.RA_LLVMF]] ->
  In (firstn kUnwindMax (pc_free_ra0 (as_code TB) :: flat_map (fun r => if r =? pc_free_ra0 (as_code TB) then [] else [r]) c))
  (as_universe TB).
Proof.
intros c Hc. cbn [In] in Hc.
repeat (destruct Hc as [<-|Hc]; [apply YCej.memZL_In; vm_compute; reflexivity|]). contradiction.
Qed.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Let LAWS : AR_laws rsegs TB := AR_laws_ok rsegs TB.

Lemma lk_ML : model_laws (as_universe TB).
Proof. exact (model_laws_ok (as_universe TB) (YF0m.ts_universe TB TBS)). Qed.

Lemma lk_SMP : stack_malloc_progressP TB.
Proof. intros s cid W Hc Hn. exact (stack_malloc_progress (as_universe TB) s cid W Hc Hn). Qed.

(* [cgif ACfi.v:76-87, link_FFL] *)
Lemma lk_FFL : frame_flag_lawP rsegs TB.
Proof.
intros ly S W mem md cid pos HAR Hin.
destruct (al_flag _ _ LAWS ly S W mem md cid pos HAR Hin) as (Hp & Ho & Happ & Hceil).
destruct (al_client_img _ _ LAWS ly S W mem md (flag_addr ly cid pos) HAR) as [Hhull Himg].
{ right. right. exists cid, pos. split; [exact Hin | reflexivity]. }
pose proof HAR as (M & L & _). pose proof (YF0x.img_cover_of_ledger ly S md L) as [C1 C2].
unfold YF0x.TFIB_IMG_LO, YF0x.TFIB_IMG_END in C1, C2.
destruct Happ as [H4096 Hz]. unfold in_zr in Hhull.
split; [exact Hp|]. split; [exact Ho|]. split.
- split; [|exact Himg]. unfold app_addr, in_app, ASAN_CEIL in *. lia.
- split; [exact H4096|]. split; [|exact Hceil]. unfold zone2, off_img, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

Lemma lk_ASM1 : astack_malloc_realizes rsegs TB 1.
Proof. exact (YF0s.stack_malloc1_contract TB LAWS TBS). Qed.

Lemma lk_ASM2 : astack_malloc_realizes rsegs TB 2.
Proof. exact (YF0u.stack_malloc2_contract TB LAWS TBS). Qed.

Lemma lk_ASM4 : astack_malloc_realizes rsegs TB 4.
Proof. exact (StackMalloc4.stack_malloc4_contract TB LAWS TBS). Qed.

Lemma lk_ABCMP : abcmp_realizes rsegs TB 0x42200.
Proof. exact (YE2s.bcmp_icpt_contract TB LAWS TBS). Qed.

(* [cgif ACfi.v:92-101, link_AMEMSET / link_AMEMCPY] *)
Lemma lk_AMEMSET : aintrin_realizes rsegs TB OSet 0x51d54.
Proof.
intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull _.
exact (YE2r.asan_memset_realizes TB LAWS TBS ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Hra Hhull Ham).
Qed.

Lemma lk_AMEMCPY : aintrin_realizes rsegs TB OCpy 0x518b8.
Proof.
intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull Hsrc.
exact (YE2q.asan_memcpy_realizes TB LAWS TBS ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull Hsrc).
Qed.

Lemma lk_AIL : asink_img_laws (SK := YE2k.tfib_sink_head) rsegs TB YE2k.tfib_K.
Proof. apply YD1u.tfib_AIL; first [exact TBS | exact LAWS]. Qed.

Lemma lk_IMGF : rate_B_img_facts rsegs TB.
Proof. exact (RtPgRoCloseB.rate_B_img_facts_tfib TB TBS). Qed.

Lemma lk_PIN : rt_rom_pinned rsegs TB.
Proof. exact (RtPgRoCloseB.rate_B_rom_pinned_tfib TB TBS). Qed.

Lemma lk_ASTRLEN : astrlen_realizes rsegs TB 0x421ec.
Proof. exact (OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU.Rt.Strlen.strlen_icpt_contract TB LAWS TBS). Qed.

Lemma lk_ASTRCMP : AStrcmpDef.astrcmp_realizes rsegs TB 0x421f4.
Proof. exact (OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU.Rt.Strcmp.strcmp_icpt_contract TB LAWS TBS). Qed.

Lemma lk_ASHF5 : aset_shadow_realizes rsegs TB 0x54880 0xf5.
Proof. exact (OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU.Rt.SetShadow.disco_set_shadow_f5 TB LAWS TBS). Qed.

(* lib/AU/Rt/SnprintfRateDef.v's rate_snprintf_sd_realizes and lib/AU/RtPgDcsvDefsB.v's copy have the same text *)
Lemma lk_ASNP : RtPgDcsvDefsB.rate_snprintf_sd_realizes rsegs TB 0x4222c.
Proof. exact OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU.Rt.SnprintfRate.rate_snprintf_sd. Qed.
End k.

(* ======================================== the statement ======================================== *)
Theorem rate_lib_x_all_B : RtPgLibB.rate_lib_x_all_stmt_B.
Proof.
intros rc LS LEAF AFREE AMALLOC fx.
unfold RtPgLibB.rate_lib_contract_x_B, RtPgLibB.XL0_B, RtPgLibB.RO_LO_B, RtPgLibB.RO_HI_B.
eapply (@RtPgTopAB.rate_lib_x_B fx rc YE2k.tfib_sink_head LS).
all: first
  [ exact LEAF | exact AFREE | exact AMALLOC
  | (intros fy; exact (@lk_ASTRCMP fy rc)) | (intros fy; exact (@lk_ASHF5 fy rc)) | (intros fy; exact (@lk_ASNP fy rc))
  | exact lk_ASTRLEN
  | exact lk_IMGF | exact lk_PIN | exact lk_AIL | exact lk_ML | exact lk_api_env | exact lk_FFL | exact lk_SMP
  | exact lk_ASM4 | exact lk_HPCS4 | exact lk_HGOT | exact lk_HSC | exact lk_HGOTU | exact lk_HUAR
  | (intros fy; exact (@lk_ASM1 fy rc)) | (intros fy; exact (@lk_ASM2 fy rc)) | exact lk_HPCS1 | exact lk_HPCS2
  | exact lk_HPCMC | (intros fy; exact (@lk_ABCMP fy rc)) | exact lk_HPCM | exact lk_HFREE
  | (intros fy; exact (@lk_AMEMSET fy rc)) | (intros fy; exact (@lk_AMEMCPY fy rc))
  | exact lk_HTRACE_E01 | exact lk_HTRACE_C23 | exact lk_HTRACE_C46 | exact lk_HTRACE
  | (cbn [YI16.sk_ofl_head YE2k.tfib_sink_head]; unfold YE2k.A_ofl_head; lia)
  | reflexivity
  | (apply Z.leb_le; vm_compute; reflexivity)
  | (split; apply Z.ltb_lt; vm_compute; reflexivity) ].
Qed.
Print Assumptions rate_lib_x_all_B.
