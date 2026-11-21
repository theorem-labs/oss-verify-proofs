(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx. (* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require PropExec StdModel ShapeAlg. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW Require U7TargetPre U7World.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import MState Mem Cells Step.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KInv. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KLink. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KEv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.ProgDeps. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM13. Import MM13. Import MM13.MallocBlocks.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainU7 Require Import PImg RMallocRep RMallocTree RMalloc_iface.
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
  [(0x22000, 0x22ef8); (0x22f00, 0x24120); (0x24121, 0x24169); (0x34169, 0x341a0); (0x741d4, 0x74220); (0x74228, 0x74240);
   (0x74248, 0x74260); (0x74270, 0x74280); (0x74288, 0x94298); (0x942b0, 0x944d8); (0x944e0, 0x944e8); (0x94918, 0x95000)].

Record target_pre_h (sp0 buf cap : Z) (content : list byte)
       (R : bvmap 5 word) (M : word -> option byte) (mo : Model) : Prop := TARGET_PRE_H {
  (* [comment removed for export] *)
  th_ra : PropExec.getr R 1 = Z_to_bv 64 0x14a70;
  th_sp : PropExec.getr R 2 = Z_to_bv 64 (sp0 - 128);
  th_gp : PropExec.getr R 3 = Z_to_bv 64 0x10800;
  th_tp : PropExec.getr R 4 = Z_to_bv 64 0x74270;
  th_a0 : PropExec.getr R 10 = Z_to_bv 64 (buf + 2);
  th_a1 : PropExec.getr R 11 = Z_to_bv 64 (U7TargetPre.hdr_cfglen content);
  th_a2 : PropExec.getr R 12 = Z_to_bv 64 (buf + 6 + U7TargetPre.hdr_cfglen content);
  th_a3 : PropExec.getr R 13 = Z_to_bv 64 (U7TargetPre.hdr_paylen content);
  th_s1 : PropExec.getr R 9 = Z_to_bv 64 buf;
  th_s5 : PropExec.getr R 21 = Z_to_bv 64 (if U7TargetPre.hdr_b1 content <? 128 then U7TargetPre.hdr_b1 content
                                            else U7TargetPre.hdr_b1 content - 256 + 2 ^ 64);
  (* [comment removed for export] *)
  th_sp0 : 0x7fff80000000 <= sp0 <= 0x800000000000 /\ sp0 mod 16 = 0;
  th_atop : ATOP = sp0 - 8388608;                  (* [comment removed for export] *)
  th_len : 6 + U7TargetPre.hdr_cfglen content <= Z.of_nat (length content) < 2 ^ 26 /\ Z.of_nat (length content) <= cap;
  (* [comment removed for export] *)
  th_stack : U7TargetPre.stack_writableZ M sp0;
  th_frame : U7World.main_frame sp0 M;
  th_content : PropExec.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 buf) (length content) = Some content;
  (* [comment removed for export] *)
  th_img : forall lo hi a, In (lo, hi) pristine_ivs -> lo <= a < hi -> M (Z_to_bv 64 a) = None;
  th_tid : exists tid : Z, 1 <= tid <= 4194303 /\
           PropExec.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 0x741c8) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid));
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
    ShapeAlg.realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (PropExec.mkst (fx := PropExec.fx0) R (Z_to_bv 64 0x14bcc) M (PropExec.seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo)
                      (U7TargetPre.t_target content (m_fs mo)).

End S0.
