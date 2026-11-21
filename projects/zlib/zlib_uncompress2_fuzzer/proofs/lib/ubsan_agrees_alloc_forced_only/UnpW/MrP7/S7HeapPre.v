(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx. (* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require PropExec StdModel ShapeAlg. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW Require S7TargetPre S7World.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import MState Mem Cells Step.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KInv. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KLink. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KEv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.ProgDeps. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM13. Import MM13. Import MM13.MallocBlocks.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainS7 Require Import PImg RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Mr Require Import MrFeasNull MrFeasNull44 MrFeasSome1 MrFeasLift2 MrRoom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section S0.
Context {RCa1 : RunCtx}.  (* a worker (A1) tool *)
Context {rc : runConstT}.

(* [comment removed for export] *)
Definition drv_state (s : PState) : Prop :=
  (allnone (ps_m s) \/ (none44 (ps_m s) /\ full44 (ps_m s))) /\ metaok_ps s.

(* [comment removed for export] *)
Definition G_std (fs : Fs.Fs) : PState -> Model -> Prop :=
  fun _ mo => m_fds mo = StdModel.fds_std /\ m_fs mo = fs.

(* [comment removed for export] *)
Definition pristine_ivs : list (Z * Z) :=
  [(0x21000, 0x21c48); (0x21c50, 0x22e70); (0x22e71, 0x22eb9); (0x32eb9, 0x32ef0); (0x72f24, 0x72f70); (0x72f78, 0x72f90);
   (0x72f98, 0x72fb0); (0x72fc0, 0x72fd0); (0x72fd8, 0x92fe8); (0x93000, 0x93228); (0x93230, 0x93238); (0x93668, 0x94000)].

Record target_pre_h (sp0 buf cap : Z) (content : list byte)
       (R : bvmap 5 word) (M : word -> option byte) (mo : Model) : Prop := TARGET_PRE_H {
  (* [comment removed for export] *)
  th_ra : PropExec.getr R 1 = Z_to_bv 64 0x14a40;
  th_sp : PropExec.getr R 2 = Z_to_bv 64 (sp0 - 128);
  th_gp : PropExec.getr R 3 = Z_to_bv 64 0x10800;
  th_tp : PropExec.getr R 4 = Z_to_bv 64 0x72fc0;
  th_a0 : PropExec.getr R 10 = Z_to_bv 64 (buf + 2);
  th_a1 : PropExec.getr R 11 = Z_to_bv 64 (S7TargetPre.hdr_cfglen content);
  th_a2 : PropExec.getr R 12 = Z_to_bv 64 (buf + 6 + S7TargetPre.hdr_cfglen content);
  th_a3 : PropExec.getr R 13 = Z_to_bv 64 (S7TargetPre.hdr_paylen content);
  th_s1 : PropExec.getr R 9 = Z_to_bv 64 buf;
  th_s5 : PropExec.getr R 21 = Z_to_bv 64 (if S7TargetPre.hdr_b1 content <? 128 then S7TargetPre.hdr_b1 content
                                            else S7TargetPre.hdr_b1 content - 256 + 2 ^ 64);
  (* [comment removed for export] *)
  th_sp0 : 0x7fff80000000 <= sp0 <= 0x800000000000 /\ sp0 mod 16 = 0;
  th_atop : ATOP = sp0 - 8388608;                  (* [comment removed for export] *)
  th_len : 6 + S7TargetPre.hdr_cfglen content <= Z.of_nat (length content) < 2 ^ 26 /\ Z.of_nat (length content) <= cap;
  (* [comment removed for export] *)
  th_stack : S7TargetPre.stack_writableZ M sp0;
  th_frame : S7World.main_frame sp0 M;
  th_content : PropExec.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 buf) (length content) = Some content;
  (* [comment removed for export] *)
  th_img : forall lo hi a, In (lo, hi) pristine_ivs -> lo <= a < hi -> M (Z_to_bv 64 a) = None;
  th_tid : exists tid : Z, 1 <= tid <= 4194303 /\
           PropExec.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 0x72f18) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid));
  (* [comment removed for export] *)
  th_heap : exists (s : PState) (pb : bptr),
      RHEAP s [(pb, buf, cap)] M /\ OWN [pb] (G_std (m_fs mo)) s mo /\ drv_state s /\ room (2 ^ 27) mo;
  (* [comment removed for export] *)
  th_aux : rauxv_ok M sp0;
  th_minv : mem_inv (run_segments psegs rc_inp rc_sp rc_mb) M;
  th_errno : exists e : word, rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M RERRNO [C4 e];
  (* [comment removed for export] *)
  th_model : StdModel.std_model (m_vmmaps mo) mo
}.

(* [comment removed for export] *)
Definition target_phase_h_stmt : Prop :=
  forall (sp0 buf cap : Z) (content : list byte) (R : bvmap 5 word) (M : word -> option byte) (mo : Model),
    target_pre_h sp0 buf cap content R M mo ->
    ShapeAlg.realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (PropExec.mkst (fx := PropExec.fx0) R (Z_to_bv 64 0x14b9c) M (PropExec.seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo)
                      (S7TargetPre.t_target content (m_fs mo)).

End S0.
