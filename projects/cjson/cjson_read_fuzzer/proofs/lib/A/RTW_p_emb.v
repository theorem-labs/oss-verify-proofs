(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From LinuxProcessSemantics.Riscv Require Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Cells.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Step.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Exec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Spin.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require SRealizes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_rep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_front.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_p_pop1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
Module RTW_p_oom_iface.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_front OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_pop1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


Definition A_OOM_ARM : Z := 0x373b4.      (* [comment removed for export] *)
Definition OOM_STACK : Z := 1536.        (* [comment removed for export] *)

(* [comment removed for export] *)
Definition emb_cells (m : word -> option byte) (d sz : Z) : Prop :=
  (exists j0 j1, rw_cells asegs m A_EMB [W8 (if d =? 0 then 0 else A_EMB + 32); CB 8 j0; W8 0; CB 8 j1; W8 d; W8 (if d =? 0 then 0 else EMB_CAP); W8 sz])
  /\ (d <> 0 -> vis m d (d + EMB_CAP)).

Lemma emb_cells_of_R_emb : forall st m, R_emb st m -> emb_cells m (emb_d st) (emb_sz st).
Proof. intros st m H. exact H. Qed.

(* [comment removed for export] *)
Definition oom_arm_stmt : Prop :=
  forall (sp gp tp x5 x6 x7 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (G : list (Z * Z)) (R : Z)
         (st : rtstate) (Rc c lo : Z) (fs6 fs5 fs4 fs3 fs2 fs1 fs0 fra : word)
         (al z1 mp z2 : word) (jr je js : list byte)
         (P : machine_state -> Model -> lghost -> Prop),
  R_link m -> R_consts st m -> RTWF st ->
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + OOM_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 64 <= 2^47 ->
  rw_cells asegs m (bv_unsigned sp) (pop_frame fs6 fs5 fs4 fs3 fs2 fs1 fs0 fra) ->
  rw_cells asegs m (Rc + 32) [C8 al; C8 z1; C8 mp; C8 z2; CB 4 jr; C1 (Z_to_bv 8 0); CB 3 je; CB 56 js] ->
  KHIGHMEM_BEG <= Rc -> Rc + 128 <= alloc_ceiling ->
  1 <= c <= 30 ->
  (* [comment removed for export] *)
  0 <= emb_sz st -> emb_sz st + EMB_MSG <= EMB_MSG * 33 ->
  (* [comment removed for export] *)
  (emb_d st = 0 -> EMB_CAP <= R /\ mmap_placeable mo EMB_CAP) ->
  (forall (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (m' : word -> option byte) (mo' : Model) (R' : Z) (d' sz' : Z),
     mem_inv asegs m' ->
     munch ([(lo, bv_unsigned sp + 64); (Rc + 68, Rc + 69); (A_EMB, A_EMB + 56)] ++ (if d' =? 0 then [] else [(d', d' + EMB_CAP)])) m m' ->
     wmono asegs m m' ->
     stk asegs m' lo (bv_unsigned sp + 64) ->
     rw_cells asegs m' (Rc + 32) [C8 al; C8 z1; C8 mp; C8 z2; CB 4 jr; C1 (Z_to_bv 8 1); CB 3 je; CB 56 js] ->
     emb_cells m' d' sz' ->
     emb_sz st <= sz' <= emb_sz st + EMB_MSG ->
     ((emb_d st <> 0 /\ d' = emb_d st /\ mo' = mo /\ R' = R)
      \/ (emb_d st = 0 /\ d' <> 0 /\ mmap_grant mo (wz d') EMB_CAP
          /\ mo' = mm_add_map (wz d') (wz EMB_CAP) mo /\ R' = R - EMB_CAP)) ->
     R_link m' ->
     LSCPS asegs P (MS (mkR fra (wz (bv_unsigned sp + 64)) gp tp y5 y6 y7 fs0 fs1 (wz 0) y11 y12 y13 y14 y15 y16 y17
                          fs2 fs3 fs4 fs5 fs6 x23 x24 x25 x26 x27 y28 y29 y30 y31)
                     F (ret_pc fra) fc None m' (seg_rom asegs)) mo' (mkG G R')) ->
  LSCPS asegs P (MS (mkR (wz 0x370a0) sp gp tp x5 x6 x7 (wz Rc) x9 x10 x11 (wz c) x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                   F (wz A_OOM_ARM) fc None m (seg_rom asegs)) mo (mkG G R).

(* [comment removed for export] *)


End CeilWrap.
End RTW_p_oom_iface.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_secz.
Module RTW_p_oom_stmts.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_front OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_secz.RT_emb0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_pop1 RTW_p_oom_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


Definition EMB_APPEND_STACK : Z := 512.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition msg_at (m : word -> option byte) (msg : Z) (bs : list byte) : Prop :=
  bytes_at asegs m msg (bs ++ [Z_to_bv 8 0]) /\ Forall (fun b : byte => bv_unsigned b <> 0) bs.

(* [comment removed for export] *)
Definition emb_append_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (G : list (Z * Z)) (R : Z)
         (st : rtstate) (msg : Z) (bs : list byte) (d sz lo : Z)
         (P : machine_state -> Model -> lghost -> Prop),
  let L := Z.of_nat (length bs) in
  mem_inv asegs m -> R_link m -> R_consts_rest st m ->
  a0 = wz msg -> 4096 <= bv_unsigned ra -> bv_unsigned ra mod 2 = 0 ->
  msg_at m msg bs -> 0 < L <= EMB_MSG -> bv_unsigned sp <= msg -> msg + L + 1 <= 2^47 ->
  emb_cells m d sz -> 0 <= sz -> (d = 0 -> sz = 0) -> sz + L <= EMB_CAP ->
  (d <> 0 -> AIMG_HI <= d /\ d + EMB_CAP <= alloc_ceiling /\ d mod 4096 = 0) ->
  (d = 0 -> EMB_CAP <= R /\ mmap_placeable mo EMB_CAP) ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + EMB_APPEND_STACK <= bv_unsigned sp -> bv_unsigned sp + 8 <= 2^47 ->
  (forall (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m' : word -> option byte) (mo' : Model) (R' : Z) (d' : Z),
     mem_inv asegs m' ->
     munch [(lo, bv_unsigned sp); (A_EMB, A_EMB + 56); (d', d' + EMB_CAP)] m m' ->
     wmono asegs m m' ->
     stk asegs m' lo (bv_unsigned sp) ->
     emb_cells m' d' (sz + L) ->
     ((d <> 0 /\ d' = d /\ mo' = mo /\ R' = R)
      \/ (d = 0 /\ d' <> 0 /\ mmap_grant mo (wz d') EMB_CAP
          /\ mo' = mm_add_map (wz d') (wz EMB_CAP) mo /\ R' = R - EMB_CAP)) ->
     R_link m' -> R_consts_rest st m' -> msg_at m' msg bs ->
     LSCPS asegs P (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                     F (ret_pc ra) fc None m' (seg_rom asegs)) mo' (mkG G R')) ->
  LSCPS asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (wz A_EMB_CB) fc None m (seg_rom asegs)) mo (mkG G R).


End CeilWrap.
End RTW_p_oom_stmts.

(* [comment removed for export] *)
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_leaves_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_lib2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
Module RTW_oom_lib.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_secz.RT_emb0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_lib2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_pop1 RTW_p_oom_iface RTW_p_oom_stmts.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.

(* [comment removed for export] *)
Definition msg_ok (bs : list byte) : Prop := Forall (fun b : byte => bv_unsigned b <> 0 /\ bv_unsigned b <> 27) bs.

Lemma msg_ok_nonul : forall bs, msg_ok bs -> Forall (fun b : byte => bv_unsigned b <> 0) bs.
Proof. intros bs H. eapply Forall_impl; [| exact H]. intros b [H1 _]. exact H1. Qed.
Lemma msg_ok_app : forall xs ys, msg_ok xs -> msg_ok ys -> msg_ok (xs ++ ys).
Proof. intros. apply Forall_app. split; assumption. Qed.

Lemma nth_error_lt_some' : forall {X} (l : list X) i, (i < length l)%nat -> exists x, nth_error l i = Some x.
Proof. intros X l i Hi. destruct (nth_error l i) as [x|] eqn:E; [exists x; reflexivity|]. apply nth_error_None in E. lia. Qed.

Lemma msg_at_nth : forall m a bs i, msg_at m a bs -> 0 <= i < Z.of_nat (length bs) ->
  exists b : byte, nth_error (bs ++ [Z_to_bv 8 0]) (Z.to_nat i) = Some b /\ bv_unsigned b <> 0 /\ bv_unsigned b < 256.
Proof.
  intros m a bs i [BY NZ] Hi. destruct (nth_error_lt_some' bs (Z.to_nat i) ltac:(lia)) as [b Hb].
  exists b. split; [rewrite nth_error_app1 by lia; exact Hb|].
  rewrite Forall_forall in NZ. split; [apply NZ; eapply nth_error_In; exact Hb|].
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia.
Qed.
Lemma msg_at_nul : forall m a bs, msg_at m a bs -> nth_error (bs ++ [Z_to_bv 8 0]) (Z.to_nat (Z.of_nat (length bs))) = Some (Z_to_bv 8 0).
Proof. intros m a bs _. rewrite Nat2Z.id. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac cases_17_30 c :=
  let HH := fresh in
  assert (HH : c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/ c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30) by lia;
  destruct HH as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]].

Lemma oom_size17 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : Z) (Q : machine_state -> Prop),
  17 <= c <= 30 ->
  (forall a0' a1' : word,
     evt asegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 a0' a1' (wz c) (wz (csize c)) x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (wz 0x3743c) fc None m (seg_rom asegs))) ->
  evt asegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (wz c) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (wz 0x37418) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros Hc K. cbv beta delta [wz] in *.
  cases_17_30 c; do 9 (lstep; try fl); apply K.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma istrlen_loop : forall (cnt : nat) (i : Z) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (s : Z) (bs : list byte) (Q : machine_state -> Prop),
  msg_at m s bs -> 0 <= s -> s + Z.of_nat (length bs) + 1 <= 2^64 ->
  0 <= i <= Z.of_nat (length bs) -> Z.of_nat cnt = Z.of_nat (length bs) - i ->
  4096 <= bv_unsigned x1 -> bv_unsigned x1 mod 2 = 0 ->
  evt asegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (wz (Z.of_nat (length bs))) (wz (Z.of_nat (length bs) + 1)) (wz 0) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (ret_pc x1) fc None m (seg_rom asegs)) ->
  evt asegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (wz s) (wz i) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (wz 0x6596c) fc None m (seg_rom asegs)).
Proof.
  intros cnt. induction cnt as [cnt IH] using lt_wf_ind.
  intros until Q. intros MA Hs1 Hs2 Hi Hcnt RA1 RA2 K. cbv beta delta [wz] in *.
  set (L := Z.of_nat (length bs)) in *.
  lstep. (* [comment removed for export] *)
  destruct (Z_lt_le_dec i L) as [LT|GE].
  - (nelim (msg_at_nth m s bs i MA ltac:(lia)) 4%nat; intros b Hb NZ Rb).
    pose proof (u8ro_read asegs _ s _ i b (Z_to_bv 64 (s + i)) (proj1 MA) Hb ltac:(lia) eq_refl) as RD.
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *) try if_lia.
    eapply (IH (cnt - 1)%nat ltac:(lia) (i + 1)); [exact MA| lia| lia| lia| lia| exact RA1| exact RA2| exact K].
  - assert (Ei : i = L) by lia.
    pose proof (u8ro_read asegs _ s _ i (Z_to_bv 8 0) (Z_to_bv 64 (s + i)) (proj1 MA) ltac:(rewrite Ei; apply (msg_at_nul m s bs MA)) ltac:(lia) eq_refl) as RD.
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *) try if_lia.
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    subst i. replace (L + 1 + -1) with L by lia. exact K.
Qed.

Lemma istrlen_spec : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (s : Z) (bs : list byte) (Q : machine_state -> Prop),
  msg_at m s bs -> 0 <= s -> s + Z.of_nat (length bs) + 1 <= 2^64 ->
  4096 <= bv_unsigned x1 -> bv_unsigned x1 mod 2 = 0 ->
  evt asegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (wz (Z.of_nat (length bs))) (wz (Z.of_nat (length bs) + 1)) (wz 0) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (ret_pc x1) fc None m (seg_rom asegs)) ->
  evt asegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (wz s) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (wz 0x65968) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros MA Hs1 Hs2 RA1 RA2 K. cbv beta delta [wz] in *.
  lstep. (* [comment removed for export] *)
  eapply (istrlen_loop (Z.to_nat (Z.of_nat (length bs))) 0); [exact MA| lia| lia| lia| lia| exact RA1| exact RA2| exact K].
Qed.

(* [comment removed for export] *)
Lemma wok_link_high : forall W, Forall (fun iv : Z * Z => AIMG_HI <= fst iv) W -> WOK_link W.
Proof.
  intros W HW.
  assert (D : forall a n, a + n <= AIMG_HI -> disjoint_from W a n).
  { intros a n Ha. induction W as [|[lo hi] W IH]; [exact I|]. inversion HW; subst. cbn in *. split; [lia| apply IH; assumption]. }
  split.
  - intros a v Hin. apply D. destruct (alink_range a v Hin); unfold AIMG_HI; lia.
  - apply D. unfold A_GLOBREC_LO, A_GLOBREC_HI, AIMG_HI. lia.
Qed.
Lemma rlink_keep : forall W m m', R_link m -> munch W m m' -> wmono asegs m m' -> Forall (fun iv : Z * Z => AIMG_HI <= fst iv) W -> R_link m'.
Proof. intros W m m' HL MU WM HW. exact (T_link W m m' MU HL (wok_link_high W HW)). Qed.

(* [comment removed for export] *)
Definition GOT_TOOLNAME : Z := 0xa1fb8.   (* [comment removed for export] *)
Definition GOT_CFLAGS : Z := 0xa1f70.     (* [comment removed for export] *)
Definition A_REPORT_FILE : Z := 0xa3e58.
Lemma got_silent : forall m, R_link m -> ro_cells asegs m GOT_SILENT [C8 (wz 1)].
Proof. intros m HL. apply (R_link_at m GOT_SILENT 1 HL). vm_compute. reflexivity. Qed.
Lemma got_toolname : forall m, R_link m -> ro_cells asegs m GOT_TOOLNAME [C8 (wz A_TOOLNAME)].
Proof. intros m HL. apply (R_link_at m GOT_TOOLNAME A_TOOLNAME HL). vm_compute. reflexivity. Qed.
Lemma got_cflags : forall m, R_link m -> ro_cells asegs m GOT_CFLAGS [C8 (wz A_CFLAGS)].
Proof. intros m HL. apply (R_link_at m GOT_CFLAGS A_CFLAGS HL). vm_compute. reflexivity. Qed.
Lemma cflags64 : forall st m, R_consts_rest st m -> ro_cells asegs m (A_CFLAGS + 64) [C1 (zb 0)].
Proof.
  intros st m HC. (nelim HC 5%nat; intros _ _ _ CF _).
  pose proof (cflags_byte m 64 CF ltac:(lia)) as H. exact H.
Qed.
Lemma toolname_cell : forall st m, R_consts_rest st m -> ro_cells asegs m A_TOOLNAME [W8 A_ASAN_STR].
Proof. intros st m HC. unfold R_consts_rest in HC. destruct HC as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_& TN & _). exact TN. Qed. (* [comment removed for export] *)
Lemma printfcb_cell : forall st m, R_consts_rest st m -> ro_cells asegs m A_PRINTF_CB [W8 A_EMB_CB].
Proof. intros st m HC. unfold R_consts_rest in HC. destruct HC as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_& CB). exact CB. Qed. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rfwrite_spec : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop),
  R_link m -> 4096 <= bv_unsigned x1 -> bv_unsigned x1 mod 2 = 0 ->
  evt asegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 (wz 1) x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (ret_pc x1) fc None m (seg_rom asegs)) ->
  evt asegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (wz 0x682b4) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros HL RA1 RA2 K. pose proof (got_silent m HL) as GS. unfold GOT_SILENT in GS. cbv beta delta [wz] in *.
  lstep. lstep. fl. (* [comment removed for export] *)
  lstep; try if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  exact K.
Qed.

(* [comment removed for export] *)
Lemma rawwrite_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (s lo : Z) (bs : list byte) (Q : machine_state -> Prop),
  mem_inv asegs m -> R_link m -> msg_at m s bs -> bv_unsigned sp <= s -> s + Z.of_nat (length bs) + 1 <= 2^47 ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 16 <= bv_unsigned sp -> bv_unsigned sp + 8 <= 2^47 ->
  4096 <= bv_unsigned ra -> bv_unsigned ra mod 2 = 0 ->
  (forall (m' : word -> option byte), mem_inv asegs m' -> munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' -> wmono asegs m m' ->
     stk asegs m' lo (bv_unsigned sp) ->
     evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A_REPORT_FILE) (wz s) (wz (Z.of_nat (length bs))) (wz 1) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz s) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (wz 0x626c8) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros MI HL MA Hs1 Hs2 ST CEIL LO SPH RA1 RA2 K.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold A_REPORT_FILE in *. leaf_prep.
  carve_frame 16%nat ST.
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  eapply istrlen_spec with (s := s) (bs := bs); [| lia| lia| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; reflexivity|].
  { destruct MA as [BY NZ]. split; [| exact NZ]. eapply bytes_at_transport; [exact BY| exact MU| cbn; rewrite length_app; cbn; lia]. }
  replace (ret_pc (Z_to_bv 64 0x626dc)) with (Z_to_bv 64 0x626dc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  try rewrite unsigned_lit in * by lia. try rewrite Z_to_bv_bv_unsigned.
  release_frame FR ST (bv_unsigned sp).
  eapply rfwrite_spec; [eapply rlink_keep; [exact HL| exact MU| exact WM| constructor; [cbn; unfold AIMG_HI; lia| constructor]]| exact RA1| exact RA2|].
  eapply K; [eassumption| exact MU| exact WM| exact ST].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma onprint_spec : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop),
  4096 <= bv_unsigned x1 -> bv_unsigned x1 mod 2 = 0 ->
  evt asegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (ret_pc x1) fc None m (seg_rom asegs)) ->
  evt asegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (wz 0x68bac) fc None m (seg_rom asegs)).
Proof. intros until Q. intros RA1 RA2 K. cbv beta delta [wz] in *. lstep. exact K. Qed.

(* [comment removed for export] *)
Lemma logmsg_spec : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate) (Q : machine_state -> Prop),
  R_link m -> R_consts_rest st m -> 4096 <= bv_unsigned x1 -> bv_unsigned x1 mod 2 = 0 ->
  evt asegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (wz 0) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (ret_pc x1) fc None m (seg_rom asegs)) ->
  evt asegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (wz 0x6ecf0) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros HL HC RA1 RA2 K. pose proof (got_cflags m HL) as G1. pose proof (cflags64 st m HC) as G2.
  unfold GOT_CFLAGS, A_CFLAGS in *. cbv beta delta [wz zb] in *. replace (1293736 + 64) with 1293800 in G2 by reflexivity.
  lstep. lstep. fl. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *) fl.
  lstep; try if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  exact K.
Qed.

(* [comment removed for export] *)
Lemma unmap00_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Q : machine_state -> Prop),
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 48 <= bv_unsigned sp -> bv_unsigned sp + 8 <= 2^47 ->
  4096 <= bv_unsigned ra -> bv_unsigned ra mod 2 = 0 ->
  (forall (m' : word -> option byte), mem_inv asegs m' -> munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' -> wmono asegs m m' ->
     stk asegs m' lo (bv_unsigned sp) ->
     evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (wz 0x67880) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros MI ST CEIL LO SPH RA1 RA2 K.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  leaf_prep.
  carve_frame 48%nat ST.
  do 5 lstep. (* [comment removed for export] *)
  lstep; try if_lia. (* [comment removed for export] *)
  do 4 lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  try rewrite unsigned_lit in * by lia. try rewrite Z_to_bv_bv_unsigned.
  release_frame FR ST (bv_unsigned sp).
  eapply K; [eassumption| exact MU| exact WM| exact ST].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma upd_nth_error_same : forall {X} (l : list X) i x, nth_error l i = Some x -> upd l i x = l.
Proof. induction l as [|y l IH]; intros [|i] x H; cbn in H |- *; try discriminate; [inversion H; reflexivity| f_equal; apply IH; exact H]. Qed.

Lemma ansi_loop : forall (cnt : nat) (i : Z) (x1 sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (buf : Z) (bs rest : list byte) (bi : byte) (Q : machine_state -> Prop),
  mem_inv asegs m -> u8arr asegs m buf (bs ++ Z_to_bv 8 0 :: rest) -> msg_ok bs -> 0 <= buf -> buf + Z.of_nat (length bs) + 1 + Z.of_nat (length rest) <= 2^47 ->
  0 <= i < Z.of_nat (length bs) -> Z.of_nat cnt = Z.of_nat (length bs) - i -> nth_error bs (Z.to_nat i) = Some bi ->
  (forall (m' : word -> option byte) (y11 y13 : word), mem_inv asegs m' -> munch [(buf + Z.of_nat (length bs), buf + Z.of_nat (length bs) + 1)] m m' ->
     wmono asegs m m' -> u8arr asegs m' buf (bs ++ Z_to_bv 8 0 :: rest) ->
     evt asegs Q (MS (mkR x1 sp gp tp t0 t1 t2 (wz (buf + Z.of_nat (length bs))) (wz 27) (wz (buf + Z.of_nat (length bs))) y11 a2 y13 a4 a5 a6 a7
                      (wz 91) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (wz 0x61c24) fc None m' (seg_rom asegs))) ->
  evt asegs Q (MS (mkR x1 sp gp tp t0 t1 t2 (wz (buf + i)) (wz 27) (wz (buf + i)) (wz (bv_unsigned bi)) a2 a3 a4 a5 a6 a7
                   (wz 91) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (wz 0x61bc8) fc None m (seg_rom asegs)).
Proof.
  intros cnt. induction cnt as [cnt IH] using lt_wf_ind.
  intros until Q. intros MI UA OK Hb1 Hb2 Hi Hcnt Hbi K. cbv beta delta [wz] in *.
  set (L := Z.of_nat (length bs)) in *.
  pose proof (munch_refl [(buf + L, buf + L + 1)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof OK as OK'. unfold msg_ok in OK'. rewrite Forall_forall in OK'. pose proof (OK' bi ltac:(eapply nth_error_In; exact Hbi)) as [NZ NE].
  pose proof (bv_unsigned_in_range 8 bi) as Rbi. unfold bv_modulus in Rbi. cbn in Rbi.
  assert (LU : length (bs ++ Z_to_bv 8 0 :: rest) = (length bs + 1 + length rest)%nat) by (rewrite length_app; cbn; lia).
  lstep. (* [comment removed for export] *)
  lstep; try if_lia. (* [comment removed for export] *)
  lstep; try if_lia. (* [comment removed for export] *)
  lstep; try if_lia. (* [comment removed for export] *)
  destruct (Z_lt_le_dec (i + 1) L) as [LT|GE].
  - destruct (nth_error_lt_some' bs (Z.to_nat (i + 1)) ltac:(lia)) as [b' Hb'].
    pose proof (OK' b' ltac:(eapply nth_error_In; exact Hb')) as [NZ' NE']. pose proof (bv_unsigned_in_range 8 b') as Rb'. unfold bv_modulus in Rb'. cbn in Rb'.
    pose proof (u8arr_read asegs _ buf _ (i + 1) b' (Z_to_bv 64 (buf + i + 1)) UA ltac:(rewrite nth_error_app1 by lia; exact Hb') ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    lstep. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    lstep; try if_lia. (* [comment removed for export] *)
    replace (buf + i + 1) with (buf + (i + 1)) by lia.
    eapply (IH (cnt - 1)%nat ltac:(lia) (i + 1)); [exact MI| exact UA| exact OK| lia| lia| lia| lia| exact Hb'| exact K].
  - assert (Ei : i + 1 = L) by lia.
    assert (NL : nth_error (bs ++ Z_to_bv 8 0 :: rest) (Z.to_nat L) = Some (Z_to_bv 8 0)) by (subst L; rewrite Nat2Z.id, nth_error_app2, Nat.sub_diag by lia; reflexivity).
    pose proof (u8arr_read asegs _ buf _ (i + 1) (Z_to_bv 8 0) (Z_to_bv 64 (buf + i + 1)) UA ltac:(rewrite Ei; exact NL) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    lstep. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    lstep; try if_lia. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    pose proof (u8arr_store_ok asegs _ _ _ L (Z_to_bv 64 (buf + i + 1)) UA ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK.
    lstep. (* [comment removed for export] *) rewrite le1_lit.
    pose proof (u8arr_write asegs _ _ _ L (Z_to_bv 8 0) UA ltac:(lia)) as UA'. clear UA.
    rewrite (upd_nth_error_same _ _ _ NL) in UA'.
    replace (buf + i + 1) with (buf + L) by lia. store_done.
    eapply K; [eassumption| exact MU| exact WM| exact UA'].
Qed.

Lemma ansi_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (buf lo : Z) (bs rest : list byte) (Q : machine_state -> Prop),
  mem_inv asegs m -> u8arr asegs m buf (bs ++ Z_to_bv 8 0 :: rest) -> msg_ok bs -> 0 < Z.of_nat (length bs) ->
  bv_unsigned sp <= buf -> buf + Z.of_nat (length bs) + 1 + Z.of_nat (length rest) <= 2^47 ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 32 <= bv_unsigned sp -> bv_unsigned sp + 8 <= 2^47 ->
  4096 <= bv_unsigned ra -> bv_unsigned ra mod 2 = 0 ->
  (forall (m' : word -> option byte) (y10 y11 y13 : word), mem_inv asegs m' ->
     munch [(bv_unsigned sp - 32, bv_unsigned sp); (buf + Z.of_nat (length bs), buf + Z.of_nat (length bs) + 1)] m m' ->
     wmono asegs m m' -> stk asegs m' lo (bv_unsigned sp) -> u8arr asegs m' buf (bs ++ Z_to_bv 8 0 :: rest) ->
     evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 y10 y11 a2 y13 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz buf) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (wz 0x61b9c) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros MI UA OK LPOS Hb1 Hb2 ST CEIL LO SPH RA1 RA2 K.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (buf + Z.of_nat (length bs), buf + Z.of_nat (length bs) + 1)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  leaf_prep.
  assert (LU : length (bs ++ Z_to_bv 8 0 :: rest) = (length bs + 1 + length rest)%nat) by (rewrite length_app; cbn; lia).
  destruct (nth_error_lt_some' bs 0%nat ltac:(lia)) as [b0 Hb0].
  pose proof OK as OK'. unfold msg_ok in OK'. rewrite Forall_forall in OK'. pose proof (OK' b0 ltac:(eapply nth_error_In; exact Hb0)) as [NZ0 _].
  pose proof (bv_unsigned_in_range 8 b0) as Rb0. unfold bv_modulus in Rb0. cbn in Rb0.
  carve_frame 32%nat ST.
  do 5 lstep. (* [comment removed for export] *)
  lstep; try if_lia. (* [comment removed for export] *)
  pose proof (u8arr_read asegs _ buf _ 0 b0 (Z_to_bv 64 buf) UA ltac:(rewrite nth_error_app1 by lia; exact Hb0) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  lstep. (* [comment removed for export] *)
  lstep; try if_lia. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  replace (Z_to_bv 64 buf) with (Z_to_bv 64 (buf + 0)) by (f_equal; lia).
  eapply (ansi_loop (Z.to_nat (Z.of_nat (length bs))) 0) with (bs := bs) (rest := rest) (bi := b0);
    [eassumption| exact UA| exact OK| lia| lia| lia| lia| exact Hb0|].
  intros m' y11 y13 MI' MU' WM' UA'. cbv beta delta [wz] in *.
  eapply rw_cells_transport in FR; [| exact MU'| exact WM'| cbn; lia]. eapply stk_transport_disjoint in ST; [| exact MU'| exact WM'| cbn; lia].
  do 4 lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  try rewrite unsigned_lit in * by lia. try rewrite Z_to_bv_bv_unsigned.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -32) _ |- _ => release_frame H ST (bv_unsigned sp) end.
  eapply K; [exact MI'| | | exact ST| exact UA'].
  - eapply munch_trans; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn in Hx |- *; lia| eapply munch_weaken; [| exact MU']; intros x Hx; cbn in Hx |- *; lia].
  - eapply wmono_trans; [exact WM| exact WM'].

Qed.



End CeilWrap.
(* [comment removed for export] *)
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.
Ltac cases_17_30 c :=
  let HH := fresh in
  assert (HH : c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/ c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30) by lia;
  destruct HH as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]].
End RTW_oom_lib.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Arr Bytes ITree Nodes SysStep Image.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import Spin SRealizes LMeasure LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LRz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_wf RT_rep CJ_iface RT_art RT_kit RT_fp RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_secz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_secz.RT_emb0.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_depot_lock.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_depot_mmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_depot_memcpy.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_leaves_memset.
Import RTW_p_oom_iface.
Import RTW_p_oom_stmts.
Import RTW_oom_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.

(* [comment removed for export] *)
Definition emb_frame (j : list byte) (s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
(* [comment removed for export] *)
Definition embc (ptr : Z) (j0 : list byte) (mtx : Z) (j1 : list byte) (d cap sz : Z) : list cell :=
  [W8 ptr; CB 8 j0; W8 mtx; CB 8 j1; W8 d; W8 cap; W8 sz].
Definition S9VAL : Z := 16140901064495857663.      (* [comment removed for export] *)
Definition MTX_LOCKED : Z := 1152921504606846976.  (* [comment removed for export] *)
Definition MTX_BIT61 : Z := 2305843009213693952.   (* [comment removed for export] *)
Definition LOCK_MASK : Z := 1152921504607895551.   (* [comment removed for export] *)
Ltac split_outside H := lazymatch type of H with _ /\ _ => let H1 := fresh "Ho" in destruct H as [H1 H]; split_outside H | _ => idtac end.
Ltac subfp :=
  unfold sub_fp; cbn; intros xq Hxq; split_outside Hxq;
  repeat match goal with |- _ /\ _ => split end;
  first [ exact I
        | intros Cq; match goal with H : ~ _ |- False => apply H; first [exact Cq| lia] end ].
Ltac if_lit := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  let v := eval vm_compute in c in replace c with v by (vm_compute; reflexivity); cbv iota end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition emb_lock_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (e lo ptr d cap sz : Z) (j0 j1 : list byte) : machine_state -> Prop :=
  fun ms1 => exists (j : list byte) (m1 : word -> option byte),
    ms1 = MS (mkR ra (wz (bv_unsigned sp + -96)) gp tp t0 t1 t2 (wz (e + 24)) a0 (wz 0) (wz (-1)) (wz 0) (wz 0)
                  (wz MTX_LOCKED) (wz 0) a6 a7
                  (wz 1500) (wz 1099511627776) (wz e) (wz MTX_BIT61) (wz (e + 16)) (wz MTX_LOCKED) (wz LOCK_MASK) (wz S9VAL) s10 s11 t3 t4 t5 t6)
             F (wz 0x56b74) fc None m1 (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp); (e + 16, e + 24)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (bv_unsigned sp + -96)
    /\ rw_cells asegs m1 (bv_unsigned sp + -96) (emb_frame j s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
    /\ rw_cells asegs m1 e (embc ptr j0 MTX_LOCKED j1 d cap sz).

Lemma emb_lock : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (e lo ptr d cap sz : Z) (j0 j1 : list byte),
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 96 <= bv_unsigned sp -> bv_unsigned sp + 8 <= 2^47 ->
  e = A_EMB -> 0 <= ptr < 2^64 -> 0 <= d < 2^64 -> 0 <= cap < 2^64 -> 0 <= sz < 2^64 ->
  rw_cells asegs m e (embc ptr j0 0 j1 d cap sz) ->
  evt asegs (emb_lock_post ra sp gp tp t0 t1 t2 s0 s1 a0 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m e lo ptr d cap sz j0 j1)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz A_EMB_CB) fc None m (seg_rom asegs)).
Proof.
  intros until j1. intros MI ST CEIL LO SPH He Hp Hd Hc Hs EC.
  pose proof (munch_refl [(lo, bv_unsigned sp); (e + 16, e + 24)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold A_EMB_CB, A_EMB, embc, MTX_LOCKED, MTX_BIT61, LOCK_MASK, S9VAL in *. leaf_prep.
  assert (ER : 0 <= e /\ e + 56 <= alloc_ceiling /\ e mod 8 = 0) by (subst e; idtac; lia).
  (nelim ER 3%nat; intros E1 E2 E8). idtac.
  destruct (ex_intro (fun q => q = e) _ eq_refl) as [q Hq]. rewrite <- Hq in EC, MU |- *.
  carve_frame 96%nat ST.
  do 12 lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. fl. (* [comment removed for export] *)
  lstep. fl. (* [comment removed for export] *)
  setreg 20 (Z_to_bv 64 q) ltac:(f_equal; lia).
  lstep. fl. lstep. fl. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. fl. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. fl. lstep. fl. (* [comment removed for export] *)
  lstep. fl. lstep. fl. (* [comment removed for export] *)
  lstep. fl. (* [comment removed for export] *)
  lstep. if_lit. (* [comment removed for export] *)
  lstep. fl. lstep. fl. (* [comment removed for export] *)
  amo_zstep. (* [comment removed for export] *)
  lstep. if_lit. (* [comment removed for export] *)
  amo_zstep2. fix_lit_store. (* [comment removed for export] *)
  lstep. if_lit. (* [comment removed for export] *)
  lstep. if_lit. (* [comment removed for export] *)
  apply evt_done. unfold emb_lock_post, emb_frame, embc. subst q.
  eexists _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR| exact EC].
Qed.


(* [comment removed for export] *)
Lemma msg_at_transport : forall W m m' msg bs, msg_at m msg bs -> munch W m m' ->
  disjoint_from W msg (Z.of_nat (length bs) + 1) -> msg_at m' msg bs.
Proof.
  intros W m m' msg bs [B NZ] MU D. split; [| exact NZ].
  eapply bytes_at_transport; [exact B| exact MU|]. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. exact D.
Qed.
(* [comment removed for export] *)
Lemma vis_chunk : forall m lo hi a n, vis m lo hi -> lo <= a -> 0 <= n -> a + n <= hi ->
  exists j, rw_cells asegs m a [CB (Z.to_nat n) j].
Proof.
  intros m lo hi a n V H1 H2 H3.
  destruct (stk_split asegs m lo (a + n) hi V ltac:(lia)) as [V1 _]. destruct (stk_split asegs m lo a (a + n) V1 ltac:(lia)) as [_ V2].
  (nelim (stk_carve asegs m a (a + n) (Z.to_nat n) V2 ltac:(lia)) 3%nat; intros _ j C). exists j.
  replace (a + n - Z.of_nat (Z.to_nat n)) with a in C by lia. exact C.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition emb_tail_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (e lo D sz L msg : Z) (bs j0 j1 : list byte) : machine_state -> Prop :=
  fun ms2 => exists (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (m2 : word -> option byte),
    ms2 = MS (mkR ra sp gp tp y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
             F (ret_pc ra) fc None m2 (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp); (e, e + 56); (D, D + EMB_CAP)] m m2 /\ wmono asegs m m2 /\ mem_inv asegs m2
    /\ stk asegs m2 lo (bv_unsigned sp)
    /\ rw_cells asegs m2 e (embc (e + 32) j0 0 j1 D EMB_CAP (sz + L))
    /\ vis m2 D (D + EMB_CAP) /\ msg_at m2 msg bs.

Lemma emb_tail : forall (ra sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (cx1 cs3 cs7 cs8 cs9 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (e lo D sz msg : Z) (bs j j0 j1 : list byte),
  let L := Z.of_nat (length bs) in
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo + 416 <= bv_unsigned sp + -96 -> bv_unsigned sp + 8 <= 2^47 ->
  e = A_EMB -> 4096 <= bv_unsigned ra -> bv_unsigned ra mod 2 = 0 ->
  rw_cells asegs m (bv_unsigned sp + -96) (emb_frame j s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) ->
  rw_cells asegs m e (embc (e + 32) j0 MTX_LOCKED j1 D EMB_CAP sz) ->
  vis m D (D + EMB_CAP) -> AIMG_HI <= D -> D + EMB_CAP <= alloc_ceiling ->
  0 <= sz -> 0 < L -> sz + L <= EMB_CAP ->
  msg_at m msg bs -> bv_unsigned sp <= msg -> msg + L + 1 <= 2^47 ->
  evt asegs (emb_tail_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m e lo D sz L msg bs j0 j1)
     (MS (mkR cx1 (wz (bv_unsigned sp + -96)) gp tp x5 x6 x7 (wz (e + 24)) (wz msg) x10 x11 x12 x13 x14 x15 x16 x17
              (wz (e + 32)) cs3 (wz e) (wz MTX_BIT61) (wz (e + 16)) cs7 cs8 cs9 s10 s11 x28 x29 x30 x31)
         F (wz 0x56b9c) fc None m (seg_rom asegs)).
Proof.
  intros until j1. cbn zeta. intros MI ST CEIL LO SPH He RA1 RA2 FR EC VIS DLO DHI SZ0 LPOS SZL MA SPM MHI.
  set (L := Z.of_nat (length bs)) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP0. unfold bv_modulus in RSP0. cbn in RSP0.
  pose proof VIS as VIS0. hide VIS0. pose proof MA as MA0. destruct MA as [MB MNZ]. pose proof MB as MB0. hide MB0.
  pose proof (munch_refl [(lo, bv_unsigned sp); (e, e + 56); (D, D + EMB_CAP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold A_EMB, embc, emb_frame, MTX_LOCKED, MTX_BIT61, EMB_CAP, AIMG_HI in *. leaf_prep. idtac.
  assert (ER : 0 <= e /\ e + 56 <= 2^47 /\ e mod 8 = 0) by (subst e; lia). (nelim ER 3%nat; intros E1 E2 E8).
  destruct (ex_intro (fun q => q = e) _ eq_refl) as [q Hq]. rewrite <- Hq in EC, MU |- *.
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  eapply istrlen_spec; [exact MA0| lia| lia| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; reflexivity|].
  replace (ret_pc (Z_to_bv 64 0x56ba8)) with (Z_to_bv 64 0x56ba8 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  fold L.
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  setreg 12 (Z_to_bv 64 L) ltac:(f_equal; lia).
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with V : stk _ mm D _ |- _ => destruct (vis_chunk mm D (D + 65536) (D + sz) L V ltac:(lia) ltac:(lia) ltac:(lia)) as [jd CH] end end.
  lstep. (* [comment removed for export] *)
  call internal_memset_Z; [exact MI| lia| lia| lia| exact CH| rewrite unsigned_lit by lia; exact ST| idtac; lia|].
  after_call. try rewrite unsigned_lit in ST by lia.
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  pose proof (proj1 (proj1 (bytes_at_app _ _ _ _ _) MB)) as SRC.
  pose proof (u8arr_of_rw_cells asegs _ _ _ _ POST) as DARR.
  eapply (imemcpy_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (D + sz) msg L bs);
    [lia| lia| lia| lia| exact SRC| subst L; lia| exact DARR| rewrite repeat_length; reflexivity| exact MI|].
  intros m3 dbs x14' DARR3 DLEN3 MI3 MU3 WM3. clear POST DARR SRC.
  replace (ret_pc (Z_to_bv 64 0x56c04)) with (Z_to_bv 64 0x56c04 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  eapply rw_cells_transport in FR; [| exact MU3| exact WM3| cbn; lia].
  eapply rw_cells_transport in EC; [| exact MU3| exact WM3| cbn; lia].
  eapply bytes_at_transport in MB; [| exact MU3| rewrite length_app; cbn; lia].
  eapply stk_transport_disjoint in ST; [| exact MU3| exact WM3| cbn; rewrite ?unsigned_lit by lia; lia].
  apply (munch_weaken _ [(lo, bv_unsigned sp); (q, q + 56); (D, D + 65536)]) in MU3. 2:{ subfp. }
  pose proof (munch_trans _ _ _ _ MU MU3) as MU4. pose proof (wmono_trans asegs _ _ _ WM WM3) as WM4.
  clear MU MU3 WM WM3 MI. rename MU4 into MU. rename WM4 into WM. rename MI3 into MI.
  (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  do 3 lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  do 3 lstep. fl. (* [comment removed for export] *)
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (RO98 : ro_cells asegs mm 0x103c8 [CB 8 [Z_to_bv 8 0xff; Z_to_bv 8 0xff; Z_to_bv 8 0x0f; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0xff; Z_to_bv 8 0xff; Z_to_bv 8 0xaf]])
      by (apply ro_cells_image; [exact MI| vm_compute; reflexivity| lia| cbn; lia]) end.
  lstep. fl. clear RO98. (* [comment removed for export] *)
  do 6 lstep. fl. (* [comment removed for export] *)
  lstep. fl. lstep. fl. (* [comment removed for export] *)
  lstep. if_lit. (* [comment removed for export] *)
  lstep. fl. lstep. if_lit. (* [comment removed for export] *)
  do 7 lstep. fl. (* [comment removed for export] *)
  lstep. if_lit. (* [comment removed for export] *)
  amo_zstep. (* [comment removed for export] *)
  lstep. if_lit. (* [comment removed for export] *)
  amo_zstep2. fix_lit_store. (* [comment removed for export] *)
  lstep. if_lit. (* [comment removed for export] *)
  lstep. if_lit. (* [comment removed for export] *)
  lstep. if_lit. (* [comment removed for export] *)
  do 11 lstep. lstep. lstep. (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. unfold emb_tail_post, embc. subst q.
  nexists 16%nat. split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  split; [replace (sz + L) with (L + sz) by lia; exact EC|].
  split; [unhide VIS0; eapply stk_wmono_noseg; [exact VIS0| exact WM| unfold AIMG_HI; lia]|].
  split; [exact MB| exact MNZ].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition realloc_frame (e msg : Z) : list cell := [W8 (e + 32); W8 msg; W8 (e + 24); W8 0x56b9c].
Definition emb_init_post (sp gp tp t0 t1 t2 a6 a7 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (e lo msg : Z) (j0 j1 : list byte) (fr : list cell) : machine_state -> Prop :=
  fun ms1 => exists (x13 : word) (m1 : word -> option byte),
    ms1 = MS (mkR (wz 0x5a4fc) (wz (bv_unsigned sp + -128)) gp tp t0 t1 t2 (wz (e + 32)) (wz 65536) (wz 65536) (wz 0x1e939) (wz 1) x13
                  (wz MTX_LOCKED) (wz 0) a6 a7
                  (wz 0x139d20) (wz 1099511627776) (wz e) (wz MTX_BIT61) (wz (e + 16)) (wz MTX_LOCKED) (wz LOCK_MASK) (wz S9VAL) s10 s11 t3 t4 t5 t6)
             F (wz 0x67700) fc None m1 (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp); (e, e + 56)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (bv_unsigned sp + -128)
    /\ rw_cells asegs m1 (bv_unsigned sp + -96) fr
    /\ rw_cells asegs m1 (bv_unsigned sp + -128) (realloc_frame e msg)
    /\ rw_cells asegs m1 e (embc (e + 32) j0 MTX_LOCKED j1 0 0 0).

Lemma emb_init : forall (ra sp gp tp t0 t1 t2 a0 a6 a7 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (e lo msg cap sz : Z) (j0 j1 : list byte) (fr : list cell),
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo + 32 <= bv_unsigned sp + -96 -> bv_unsigned sp + 8 <= 2^47 ->
  e = A_EMB -> 0 <= cap < 2^64 -> 0 <= sz < 2^64 -> a0 = wz msg -> 0 <= msg < 2^64 ->
  rw_cells asegs m (bv_unsigned sp + -96) fr -> Z.of_nat (cells_size fr) = 96 ->
  rw_cells asegs m e (embc 0 j0 MTX_LOCKED j1 0 cap sz) ->
  ro_cells asegs m 0xa1f60 [C8 (wz 0x139d20)] -> ro_cells asegs m 0x139d20 [W8 4096] ->
  evt asegs (emb_init_post sp gp tp t0 t1 t2 a6 a7 s10 s11 t3 t4 t5 t6 F fc m e lo msg j0 j1 fr)
    (MS (mkR ra (wz (bv_unsigned sp + -96)) gp tp t0 t1 t2 (wz (e + 24)) a0 (wz 0) (wz (-1)) (wz 0) (wz 0)
             (wz MTX_LOCKED) (wz 0) a6 a7
             (wz 1500) (wz 1099511627776) (wz e) (wz MTX_BIT61) (wz (e + 16)) (wz MTX_LOCKED) (wz LOCK_MASK) (wz S9VAL) s10 s11 t3 t4 t5 t6)
        F (wz 0x56b74) fc None m (seg_rom asegs)).
Proof.
  intros until fr. intros MI ST CEIL LO SPH He Hc Hs -> Hm FR FRSZ EC GOTP PSC.
  pose proof (bv_unsigned_in_range 64 sp) as RSP0. unfold bv_modulus in RSP0. cbn in RSP0.
  pose proof (munch_refl [(lo, bv_unsigned sp); (e, e + 56)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold A_EMB, embc, MTX_LOCKED, MTX_BIT61, LOCK_MASK, S9VAL in *. cbv beta delta [wz] in *. pose proof aceil as CEILlo.
  assert (ER : 0 <= e /\ e + 56 <= 2^47 /\ e mod 8 = 0) by (subst e; lia). (nelim ER 3%nat; intros E1 E2 E8).
  destruct (ex_intro (fun q => q = e) _ eq_refl) as [q Hq]. rewrite <- Hq in EC, MU |- *.
  hide GOTP. hide PSC.
  lstep. (* [comment removed for export] *)
  lstep. if_lit. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. fl. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  (* [comment removed for export] *)
  carve_frame 32%nat ST.
  do 5 lstep. (* [comment removed for export] *)
  lstep. if_lit. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. if_lit. (* [comment removed for export] *)
  unhide GOTP. recell GOTP MU. lstep. lstep. fl. clear GOTP. (* [comment removed for export] *)
  unhide PSC. recell PSC MU. lstep. fl. clear PSC. (* [comment removed for export] *)
  lstep. if_lit. (* [comment removed for export] *)
  lstep. fl. lstep. fl. lstep. if_lit. (* [comment removed for export] *)
  lstep. fl. lstep. fl. lstep. fl. lstep. fl. (* [comment removed for export] *)
  lstep. lstep. fl. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  apply evt_done. unfold emb_init_post, realloc_frame, embc, MTX_LOCKED, MTX_BIT61, LOCK_MASK, S9VAL. subst q. cbv beta delta [wz].
  do 2 eexists. split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  split; [exact FR|]. split; [exact FR0| exact EC].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition emb_rret_post (sp gp tp s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (e lo msg a : Z) (j0 j1 : list byte) (fr : list cell) : machine_state -> Prop :=
  fun ms1 => exists (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m1 : word -> option byte),
    ms1 = MS (mkR (wz 0x56b9c) (wz (bv_unsigned sp + -96)) gp tp x5 x6 x7 (wz (e + 24)) (wz msg) x10 x11 x12 x13 x14 x15 x16 x17
                  (wz (e + 32)) (wz 1099511627776) (wz e) (wz MTX_BIT61) (wz (e + 16)) (wz MTX_LOCKED) (wz LOCK_MASK) (wz S9VAL) s10 s11 x28 x29 x30 x31)
             F (wz 0x56b9c) fc None m1 (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp); (e, e + 56)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (bv_unsigned sp + -96)
    /\ rw_cells asegs m1 (bv_unsigned sp + -96) fr
    /\ rw_cells asegs m1 e (embc (e + 32) j0 MTX_LOCKED j1 a EMB_CAP 0)
    /\ vis m1 a (a + EMB_CAP).

Lemma emb_rret : forall (sp gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 s10 s11 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (e lo msg a : Z) (j0 j1 : list byte) (fr : list cell),
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -128) -> alloc_ceiling <= lo -> lo + 48 <= bv_unsigned sp + -128 -> bv_unsigned sp + 8 <= 2^47 ->
  e = A_EMB -> 0 <= msg < 2^64 -> AIMG_HI <= a -> a + EMB_CAP <= alloc_ceiling ->
  rw_cells asegs m (bv_unsigned sp + -96) fr -> Z.of_nat (cells_size fr) = 96 ->
  rw_cells asegs m (bv_unsigned sp + -128) (realloc_frame e msg) ->
  rw_cells asegs m e (embc (e + 32) j0 MTX_LOCKED j1 0 0 0) ->
  rw_cells asegs m a [CB (Z.to_nat EMB_CAP) (repeat (Z_to_bv 8 0) (Z.to_nat EMB_CAP))] ->
  evt asegs (emb_rret_post sp gp tp s10 s11 F fc m e lo msg a j0 j1 fr)
    (MS (mkR (wz 0x5a4fc) (wz (bv_unsigned sp + -128)) gp tp x5 x6 x7 (wz (e + 32)) (wz 65536) (wz a) x11 x12 x13 x14 x15 x16 x17
             (wz 0x139d20) (wz 1099511627776) (wz e) (wz MTX_BIT61) (wz (e + 16)) (wz MTX_LOCKED) (wz LOCK_MASK) (wz S9VAL) s10 s11 x28 x29 x30 x31)
        F (ret_pc (wz 0x5a4fc)) fc None m (seg_rom asegs)).
Proof.
  intros until fr. intros MI ST CEIL LO SPH He Hm ALO AHI FR FRSZ FR0 EC BLK.
  pose proof (bv_unsigned_in_range 64 sp) as RSP0. unfold bv_modulus in RSP0. cbn in RSP0.
  pose proof (munch_refl [(lo, bv_unsigned sp); (e, e + 56)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold A_EMB, embc, realloc_frame, MTX_LOCKED, MTX_BIT61, LOCK_MASK, S9VAL, EMB_CAP, AIMG_HI in *. cbv beta delta [wz] in *.
  idtac.
  assert (ER : 0 <= e /\ e + 56 <= 2^47 /\ e mod 8 = 0) by (subst e; lia). (nelim ER 3%nat; intros E1 E2 E8).
  destruct (ex_intro (fun q => q = e) _ eq_refl) as [q Hq]. rewrite <- Hq in EC, FR0, MU |- *.
  pose proof (stk_of_rw_cells asegs m a _ BLK) as VIS. cbn [cells_size csize Nat.add] in VIS.
  match type of VIS with stk _ _ _ ?hi => replace hi with (a + 65536) in VIS by (cbn; lia) end.
  clear BLK. hide VIS.
  replace (ret_pc (Z_to_bv 64 0x5a4fc)) with (Z_to_bv 64 0x5a4fc : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. if_lit. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  replace (ret_pc (Z_to_bv 64 0x5a50c)) with (Z_to_bv 64 0x5a50c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  eapply unmap00_spec; [exact MI| rewrite unsigned_lit by lia; exact ST| idtac; lia| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia
    | rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; reflexivity|].
  intros m2 MI2 MU2 WM2 ST2. rewrite unsigned_lit in MU2, ST2 by lia.
  eapply rw_cells_transport in FR; [| exact MU2| exact WM2| cbn; lia].
  eapply rw_cells_transport in FR0; [| exact MU2| exact WM2| cbn; lia].
  eapply rw_cells_transport in EC; [| exact MU2| exact WM2| cbn; lia].
  apply (munch_weaken _ [(lo, bv_unsigned sp); (q, q + 56)]) in MU2. 2:{ subfp. }
  pose proof (munch_trans _ _ _ _ MU MU2) as MU3. pose proof (wmono_trans asegs _ _ _ WM WM2) as WM3.
  clear MU MU2 WM WM2 MI ST. rename MU3 into MU. rename WM3 into WM. rename MI2 into MI. rename ST2 into ST.
  replace (ret_pc (Z_to_bv 64 0x5a51c)) with (Z_to_bv 64 0x5a51c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  lstep. lstep. (* [comment removed for export] *)
  do 4 lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  release_frame FR0 ST (bv_unsigned sp + -96).
  apply evt_done. unfold emb_rret_post, embc, MTX_LOCKED, MTX_BIT61, LOCK_MASK, S9VAL, EMB_CAP. subst q. cbv beta delta [wz].
  nexists 16%nat. split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  split; [exact FR|]. split; [exact EC|]. unhide VIS. eapply stk_wmono_noseg; [exact VIS| exact WM| unfold AIMG_HI; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition emb_fp_ok (iv : Z * Z) : Prop := (A_EMB <= fst iv /\ snd iv <= A_EMB + 56) \/ AIMG_HI <= fst iv.

Lemma emb_fp_disj : forall W a n, Forall emb_fp_ok W -> (a + n <= A_EMB \/ (A_EMB + 56 <= a /\ a + n <= AIMG_HI)) -> disjoint_from W a n.
Proof.
  intros W a n HW H. induction W as [|[lo hi] W IH]; [exact I|]. inversion HW as [|x l H1 H2]; subst. cbn. split; [| apply IH; exact H2].
  unfold emb_fp_ok in H1. cbn [fst snd] in H1. unfold A_EMB, AIMG_HI in *. lia.
Qed.

Lemma link_keep : forall W m m', R_link m -> munch W m m' -> wmono asegs m m' -> Forall emb_fp_ok W -> R_link m'.
Proof.
  intros W m m' HL MU WM HW. apply (T_link W m m' MU HL). split.
  - intros a v Hin. apply (emb_fp_disj W a 8 HW). destruct (alink_range a v Hin); unfold A_EMB; lia.
  - apply (emb_fp_disj W _ _ HW). unfold A_GLOBREC_LO, A_GLOBREC_HI, A_EMB. lia.
Qed.

Lemma consts_rest_keep : forall st W m m', R_consts_rest st m -> munch W m m' -> wmono asegs m m' -> Forall emb_fp_ok W -> R_consts_rest st m'.
Proof.
  intros st W m m' H MU WM HW. unfold R_consts_rest in *.
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & [oom H15] & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27). (* [comment removed for export] *)
  unfold A_SHADOW_OFF_CELL, A_UAR_OPTION, A_AFLAGS, A_CFLAGS, A_PAGESIZE_CACHED, A_KHIGHMEMEND, A_KMIDMEMBEG, A_KMIDMEMEND,
    A_ASAN_INITED, A_MCS, A_CAN_POISON, A_TSD_KEY_INITED, A_TSD_KEY, A_MAY_RETURN_NULL, A_ALLOC_OOM, A_DYING, A_VERBOSITY,
    A_MFHOOKS, A_LSAN_DISABLE, A_IA_INITED, AHOOKS, A_LIBC_PAGESIZE, A_MU_GLOBALS, A_GLOBALS_REGD, A_TPCG_INITED, A_TOOLNAME, A_PRINTF_CB, ATP in *.
  Local Ltac trk MU WM HW H := first [ eapply (roT _ _ _ MU _ _ H) | eapply (rwT _ _ _ MU WM _ _ H) ]; cbn -[Z.add Z.mul Z.le Z.lt Z.sub disjoint_from];
    apply (emb_fp_disj _ _ _ HW); unfold A_EMB, AIMG_HI; lia.
  split; [trk MU WM HW H1|]. split; [trk MU WM HW H2|]. split; [trk MU WM HW H3|]. split; [trk MU WM HW H4|]. split; [trk MU WM HW H5|]. split; [trk MU WM HW H6|].
  split; [trk MU WM HW H7|]. split; [trk MU WM HW H8|]. split; [trk MU WM HW H9|]. split; [trk MU WM HW H10|]. split; [trk MU WM HW H11|]. split; [trk MU WM HW H12|].
  split; [trk MU WM HW H13|]. split; [trk MU WM HW H14|]. split; [exists oom; trk MU WM HW H15|]. split; [trk MU WM HW H16|]. split; [trk MU WM HW H17|].
  split; [trk MU WM HW H18|]. split; [trk MU WM HW H19|]. split; [trk MU WM HW H20|]. split; [trk MU WM HW H21|]. split; [trk MU WM HW H22|]. split; [trk MU WM HW H23|]. split; [trk MU WM HW H24|].
  split; [trk MU WM HW H25|]. split; [trk MU WM HW H26|]. trk MU WM HW H27.
Qed.

(* [comment removed for export] *)
Lemma mmap_consts_of_rest : forall st m, R_link m -> R_consts_rest st m -> mmap_consts m.
Proof.
  intros st m HL HC. unfold mmap_consts. unfold R_consts_rest in HC.
  (nelim HC 17%nat; intros _ _ _ CF K5 _ _ _ _ _ _ _ _ _ _ K16 _).
  split; [apply (R_link_at m 0xa1f60 0x139d20 HL); vm_compute; reflexivity|].
  split; [exact K5|].
  split; [apply (R_link_at m 0xa1f70 0x13bda8 HL); vm_compute; reflexivity|].
  split; [exact (cflags_byte m 260 CF ltac:(lia))|].
  split; [exact (cflags_word m 144 0 CF ltac:(lia) ltac:(lia) ltac:(intros i Hi; do 8 (destruct i as [|i]; [reflexivity|]); lia))|].
  split; [apply (R_link_at m 0xa1fc0 1 HL); vm_compute; reflexivity|].
  exact K16.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem emb_append_proof : emb_append_stmt.
Proof.
  unfold emb_append_stmt. intros until P. cbn zeta.
  intros MI HL HCR -> RA1 RA2 MA LB SPM MHI [[j0 [j1 EC]] VISD] SZ0 SZD SZL DNZ DZ ST CEIL LO SPH K.
  set (L := Z.of_nat (length bs)) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP0. unfold bv_modulus in RSP0. cbn in RSP0.
  unfold EMB_APPEND_STACK, EMB_MSG in *. pose proof CEIL as CEILn. idtac.
  assert (MR : 0 <= msg) by lia.
  apply lscps_assume. intros NWX HOK HBINV.
  apply lscps_step_evt.
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply (emb_lock ra sp gp tp t0 t1 t2 s0 s1 (wz msg) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A_EMB lo
              (if d =? 0 then 0 else A_EMB + 32) d (if d =? 0 then 0 else EMB_CAP) sz j0 j1);
      [exact MI| exact ST| exact CEIL| lia| lia| reflexivity| | | | | exact EC].
    - unfold A_EMB. destruct (d =? 0); lia.
    - destruct (Z.eq_dec d 0) as [->|NZ]; [lia|]. destruct (DNZ NZ). idtac. unfold AIMG_HI, EMB_CAP in *. lia.
    - unfold EMB_CAP. destruct (d =? 0); lia.
    - unfold EMB_CAP in *. lia. }
  intros ms1 nelH_; (nelim nelH_ 9%nat; intros j m1 -> MU1 WM1 MI1 ST1 FR1 EC1).
  destruct (Z.eq_dec d 0) as [Dz|Dnz].
  - (* [comment removed for export] *)
    subst d. specialize (SZD eq_refl). subst sz. cbn [Z.eqb] in EC1. destruct (DZ eq_refl) as [HRR HPL].
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply (emb_init ra sp gp tp t0 t1 t2 (wz msg) a6 a7 s10 s11 t3 t4 t5 t6 F fc m1 A_EMB lo msg 0 0 j0 j1);
        [exact MI1| exact ST1| exact CEIL| lia| lia| reflexivity| lia| lia| reflexivity| lia| exact FR1| reflexivity| exact EC1| |].
      - eapply (ro_cells_transport asegs _ m m1); [apply (R_link_at m 0xa1f60 0x139d20 HL); vm_compute; reflexivity| exact MU1| unfold A_EMB; cbn; lia].
      - unfold R_consts_rest in HCR. (nelim HCR 6%nat; intros _ _ _ _ K5 _).
        eapply (ro_cells_transport asegs _ m m1); [exact K5| exact MU1| unfold A_EMB, A_PAGESIZE_CACHED; cbn; lia]. }
    intros ms2 nelH_; (nelim nelH_ 10%nat; intros x13 m2 -> MU2 WM2 MI2 ST2 FR2 FRR2 EC2).
    apply (munch_weaken _ [(lo, bv_unsigned sp); (A_EMB, A_EMB + 56)]) in MU1. 2:{ subfp. }
    pose proof (munch_trans _ _ _ _ MU1 MU2) as MU02.
    pose proof (wmono_trans asegs _ _ _ WM1 WM2) as WM02.
    (* [comment removed for export] *)
    apply evt_done. cbv beta delta [wz].
    eapply mmapordie_spec with (lo := lo).
    + apply (mmap_consts_munch _ m m2 (mmap_consts_of_rest st m HL HCR) MU02); unfold A_EMB; cbn; lia.
    + exact MI2.
    + rewrite unsigned_lit by lia. exact ST2.
    + rewrite unsigned_lit by lia. lia.
    + unfold EMB_CAP in *. lia.
    + lia.
    + unfold EMB_CAP in *. lia.
    + exact HPL.
    + intros a x5 x6 x7 x11 x12 y13 x14 x15 x16 x17 x28 x29 x30 x31 m3 GR MI3 MU3 WM3 ST3 BLK.
      rewrite unsigned_lit in MU3, ST3 by lia.
      pose proof (grant_above_image mo a 65536 HOK GR ltac:(lia)) as ALO.
      (nelimp GR 4%nat; intros GA GP GC GF). idtac.
      pose proof (bv_unsigned_in_range 64 a) as RA. unfold bv_modulus in RA. cbn in RA.
      eapply rw_cells_transport in FR2; [| exact MU3| exact WM3| cbn; lia].
      eapply rw_cells_transport in FRR2; [| exact MU3| exact WM3| cbn; lia].
      eapply rw_cells_transport in EC2; [| exact MU3| exact WM3| unfold A_EMB, AIMG_HI in *; cbn; lia].
      apply lscps_step_evt. rewrite <- (Z_to_bv_bv_unsigned a). set (D := bv_unsigned a) in *.
      (* [comment removed for export] *)
      eapply evt_cut.
      { eapply (emb_rret sp gp tp x5 x6 x7 x11 x12 y13 x14 x15 x16 x17 s10 s11 x28 x29 x30 x31 F fc m3 A_EMB lo msg D j0 j1);
          [exact MI3| exact ST3| exact CEIL| lia| lia| reflexivity| lia| exact ALO| unfold EMB_CAP; idtac; lia| exact FR2| reflexivity| exact FRR2| exact EC2|].
        unfold EMB_CAP. exact BLK. }
      intros ms4 nelH_; (nelim nelH_ 24%nat; intros y5 y6 y7 y10 y11 y12 z13 y14 y15 y16 y17 y28 y29 y30 y31 m4 -> MU4 WM4 MI4 ST4 FR4 EC4 VIS4).
      (* [comment removed for export] *)
      assert (MU04 : munch [(lo, bv_unsigned sp); (A_EMB, A_EMB + 56); (D, D + EMB_CAP)] m m4).
      { eapply munch_trans; [eapply munch_weaken; [| exact MU02]; subfp|].
        eapply munch_trans; [eapply munch_weaken; [| exact MU3]; unfold EMB_CAP; subfp|].
        eapply munch_weaken; [| exact MU4]; subfp. }
      pose proof (wmono_trans asegs _ _ _ WM02 (wmono_trans asegs _ _ _ WM3 WM4)) as WM04.
      (* [comment removed for export] *)
      eapply evt_cut.
      { eapply (emb_tail ra sp gp tp y5 y6 y7 s0 s1 y10 y11 y12 z13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31
                  (wz 0x56b9c) (wz 1099511627776) (wz MTX_LOCKED) (wz LOCK_MASK) (wz S9VAL) F fc m4 A_EMB lo D 0 msg bs j j0 j1);
          [exact MI4| exact ST4| exact CEIL| lia| lia| reflexivity| exact RA1| exact RA2| exact FR4| exact EC4| exact VIS4| exact ALO| unfold EMB_CAP; idtac; lia
          | lia| subst L; lia| unfold EMB_CAP in *; subst L; lia| | exact SPM| subst L; lia].
        (* [comment removed for export] *)
        eapply (msg_at_transport _ m m4); [exact MA| exact MU04|]. subst L. unfold A_EMB, AIMG_HI, EMB_CAP in *. cbn. lia. }
      intros ms5 nelH_; (nelim nelH_ 24%nat; intros z5 z6 z7 z10 z11 z12 w13 z14 z15 z16 z17 z28 z29 z30 z31 m5 -> MU5 WM5 MI5 ST5 EC5 VIS5 MA5).
      apply evt_done.
      assert (MU05 : munch [(lo, bv_unsigned sp); (A_EMB, A_EMB + 56); (D, D + EMB_CAP)] m m5).
      { eapply munch_trans; [exact MU04|]. eapply munch_weaken; [| exact MU5]. unfold EMB_CAP; subfp. }
      pose proof (wmono_trans asegs _ _ _ WM04 WM5) as WM05.
      assert (FPOK : Forall emb_fp_ok [(lo, bv_unsigned sp); (A_EMB, A_EMB + 56); (D, D + EMB_CAP)]).
      { unfold emb_fp_ok. repeat constructor; cbn [fst snd]; unfold A_EMB, AIMG_HI in *; lia. }
      eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 (mm_add_map (Z_to_bv 64 D) (Z_to_bv 64 65536) mo) (R - 65536) D).
      * exact MI5.
      * exact MU05.
      * exact WM05.
      * exact ST5.
      * split; [| intros _; exact VIS5]. exists j0, j1. replace (D =? 0) with false by (symmetry; apply Z.eqb_neq; unfold AIMG_HI in ALO; lia).
        unfold embc in EC5. rewrite Z.add_0_l in EC5. exact EC5.
      * right. split; [reflexivity|]. split; [unfold AIMG_HI in ALO; lia|]. unfold wz, EMB_CAP.
        split; [subst D; rewrite Z_to_bv_bv_unsigned; exact GR|]. split; reflexivity.
      * exact (link_keep _ m m5 HL MU05 WM05 FPOK).
      * exact (consts_rest_keep st _ m m5 HCR MU05 WM05 FPOK).
      * exact MA5.
  - (* [comment removed for export] *)
    (nelim (DNZ Dnz) 3%nat; intros DLO DHI DAL). replace (d =? 0) with false in EC1 by (symmetry; apply Z.eqb_neq; exact Dnz).
    cbv beta delta [wz].
    pose proof EC1 as EC1u. unfold embc in EC1u. unfold A_EMB in EC1u |- *.
    lstep. cbv beta delta [wz]. (* [comment removed for export] *)
    lstep. if_lia. (* [comment removed for export] *)
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply (emb_tail ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 MTX_LOCKED) (Z_to_bv 64 0) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                ra (wz 1099511627776) (wz MTX_LOCKED) (wz LOCK_MASK) (wz S9VAL) F fc m1 A_EMB lo d sz msg bs j j0 j1);
        [exact MI1| exact ST1| exact CEIL| lia| lia| reflexivity| exact RA1| exact RA2| exact FR1| exact EC1| | exact DLO| exact DHI
        | lia| subst L; lia| unfold EMB_CAP in *; subst L; lia| | exact SPM| subst L; lia].
      - eapply stk_wmono_noseg; [exact (VISD Dnz)| exact WM1| unfold AIMG_HI in *; lia].
      - eapply (msg_at_transport _ m m1); [exact MA| exact MU1|]. subst L. unfold A_EMB in *. cbn. lia. }
    intros ms5 nelH_; (nelim nelH_ 24%nat; intros z5 z6 z7 z10 z11 z12 w13 z14 z15 z16 z17 z28 z29 z30 z31 m5 -> MU5 WM5 MI5 ST5 EC5 VIS5 MA5).
    apply evt_done.
    assert (MU05 : munch [(lo, bv_unsigned sp); (A_EMB, A_EMB + 56); (d, d + EMB_CAP)] m m5).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU1]; subfp|].
      eapply munch_weaken; [| exact MU5]. subfp. }
    pose proof (wmono_trans asegs _ _ _ WM1 WM5) as WM05.
    assert (FPOK : Forall emb_fp_ok [(lo, bv_unsigned sp); (A_EMB, A_EMB + 56); (d, d + EMB_CAP)]).
    { unfold emb_fp_ok. repeat constructor; cbn [fst snd]; unfold A_EMB, AIMG_HI in *; lia. }
    eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 mo R d).
    + exact MI5.
    + exact MU05.
    + exact WM05.
    + exact ST5.
    + split; [| intros _; exact VIS5]. exists j0, j1. replace (d =? 0) with false by (symmetry; apply Z.eqb_neq; exact Dnz). exact EC5.
    + left. repeat split; try reflexivity. exact Dnz.
    + exact (link_keep _ m m5 HL MU05 WM05 FPOK).
    + exact (consts_rest_keep st _ m m5 HCR MU05 WM05 FPOK).
    + exact MA5.
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.
Ltac split_outside H := lazymatch type of H with _ /\ _ => let H1 := fresh "Ho" in destruct H as [H1 H]; split_outside H | _ => idtac end.
Ltac subfp :=
  unfold sub_fp; cbn; intros xq Hxq; split_outside Hxq;
  repeat match goal with |- _ /\ _ => split end;
  first [ exact I
        | intros Cq; match goal with H : ~ _ |- False => apply H; first [exact Cq| lia] end ].
Ltac if_lit := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  let v := eval vm_compute in c in replace c with v by (vm_compute; reflexivity); cbv iota end.
