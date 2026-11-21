(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.  (* a worker (A1) tool *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
Require OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StdModel OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.ShapeAlg OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.S8TargetPre OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.S8World.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import MState Mem Cells Step.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KInv. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KLink. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KEv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.ProgDeps. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM13. Import MM13. Import MM13.MallocBlocks.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainS8 Require Import PImg RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Mr Require Import MrFeasNull MrFeasNull44 MrFeasSome1 MrFeasLift2 MrRoom.
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
  [(0x21000, 0x21cb0); (0x21cb8, 0x22ee0); (0x22ee1, 0x22f29); (0x32f29, 0x32f60); (0x72f94, 0x72fe0); (0x72fe8, 0x73000);
   (0x73008, 0x73020); (0x73030, 0x73040); (0x73048, 0x93058); (0x93070, 0x93298); (0x932a0, 0x932a8); (0x936d8, 0x94000)].

Record target_pre_h (sp0 buf cap : Z) (content : list byte)
       (R : bvmap 5 word) (M : word -> option byte) (mo : Model) : Prop := TARGET_PRE_H {
  (* [comment removed for export] *)
  th_ra : PropExec.getr R 1 = Z_to_bv 64 0x14a48;
  th_sp : PropExec.getr R 2 = Z_to_bv 64 (sp0 - 128);
  th_gp : PropExec.getr R 3 = Z_to_bv 64 0x10800;
  th_tp : PropExec.getr R 4 = Z_to_bv 64 0x73030;
  th_a0 : PropExec.getr R 10 = Z_to_bv 64 (buf + 2);
  th_a1 : PropExec.getr R 11 = Z_to_bv 64 (S8TargetPre.hdr_cfglen content);
  th_a2 : PropExec.getr R 12 = Z_to_bv 64 (buf + 6 + S8TargetPre.hdr_cfglen content);
  th_a3 : PropExec.getr R 13 = Z_to_bv 64 (S8TargetPre.hdr_paylen content);
  th_s1 : PropExec.getr R 9 = Z_to_bv 64 buf;
  th_s5 : PropExec.getr R 21 = Z_to_bv 64 (if S8TargetPre.hdr_b1 content <? 128 then S8TargetPre.hdr_b1 content
                                            else S8TargetPre.hdr_b1 content - 256 + 2 ^ 64);
  (* [comment removed for export] *)
  th_sp0 : 0x7fff80000000 <= sp0 <= 0x800000000000 /\ sp0 mod 16 = 0;
  th_atop : ATOP = sp0 - 8388608;                  (* [comment removed for export] *)
  th_len : 6 + S8TargetPre.hdr_cfglen content <= Z.of_nat (length content) < 2 ^ 26 /\ Z.of_nat (length content) <= cap;
  (* [comment removed for export] *)
  th_stack : S8TargetPre.stack_writableZ M sp0;
  th_frame : S8World.main_frame sp0 M;
  th_content : PropExec.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 buf) (length content) = Some content;
  (* [comment removed for export] *)
  th_img : forall lo hi a, In (lo, hi) pristine_ivs -> lo <= a < hi -> M (Z_to_bv 64 a) = None;
  th_tid : exists tid : Z, 1 <= tid <= 4194303 /\
           PropExec.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 0x72f88) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid));
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
    ShapeAlg.realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (PropExec.mkst (fx := PropExec.fx0) R (Z_to_bv 64 0x14ba4) M (PropExec.seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo)
                      (S8TargetPre.t_target content (m_fs mo)).

End S0.
