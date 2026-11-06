(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SFModel.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ITree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Decode.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prelim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Monad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Stdio.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_memcpy.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_fwritex.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_pad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_fmt_fp_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_printf_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require UImg.
Module Stdio_iface.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_printf_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation mem := (word -> option byte).

Definition stderr_wfile0 (m : mem) : Prop :=
  exists (flags mode : word) (e wend : Z) (tail : list byte),
    rw_cells usegs m RSTDERR (file_cells flags wend e e F_STDIO_WRITE 0x55098 0 2 mode 0xffffffff tail)
    /\ Z.land (bv_unsigned flags) 40 = 0
    /\ (wend = 0 \/ (wend = 0x55098 /\ e = 0x55098))
    /\ 0 <= e < 2^63.

Lemma stderr_wfile0_wfile : forall m, stderr_wfile0 m -> stderr_wfile m.
Proof. intros m (flags & mode & e & wend & tail & H & FL & _ & _). exists flags, mode, e, wend, tail. split; [exact H| exact FL]. Qed.
Lemma stderr_wfile0_file : forall m, stderr_wfile0 m -> stderr_file m.
Proof. intros m H. apply stderr_wfile_file, stderr_wfile0_wfile, H. Qed.

(* [comment removed for export] *)
Definition FWRITE_DEPTH : Z := 240.

Section Fwrite.
  Context {St : Type}.

  Definition fwrite_diag_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (canary : word) (m : mem) (st : St) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m'
      /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ stderr_wfile0 m'
      /\ ssp_cells m' canary
      /\ st' = st.

  (* [comment removed for export] *)
  Definition fwrite_diag_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word) (s : list Z),
      towrite_stmt ->
      stderr_wfile0 m ->
      bytes_at usegs m (bv_unsigned a0) (zb s) -> Forall (fun c => 0 <= c < 256) s -> 0 < zlength s < 2^31 ->
      a1 = Z_to_bv 64 (zlength s) -> a2 = Z_to_bv 64 1 -> a3 = Z_to_bv 64 RSTDERR ->
      stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FWRITE_DEPTH) -> (GLOBALS_TOP <= lo) ->
      (bv_unsigned a0 + zlength s <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
      (bv_unsigned a0 + zlength s <= RSTDERR \/ RSTDERR + 232 <= bv_unsigned a0) ->
      ssp_cells m canary -> mem_inv usegs m ->
      implM usegs (stderr_fwrite s : M St unit) st
            (fwrite_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo canary m st)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x187d0) fc None m (seg_rom usegs)).
End Fwrite.
End Stdio_iface.

(* [comment removed for export] *)
From Stdlib Require NArith.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Driver.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Printf_model.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require InitMem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeSpec.
From Stdlib Require Zify.
Module SO_iface.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Driver.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_printf_iface Stdio_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.InitMem.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeSpec.

(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
(* [comment removed for export] *)

Import ListNotations.
Open Scope Z_scope.

Notation mem := (word -> option byte).
Notation RTD := 0x34908%Z (only parsing).
Notation RTP := 0x349d0%Z (only parsing).

(* [comment removed for export] *)
Definition chan_ok (mo : Model) (fd : Z) : Prop :=
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fdiag_pieces (d : diag_msg) : list (list Z) :=
  match d with
  | DUsage s => pieces_usage s | DCannotOpen s => pieces_cannot_open s | DReadError s => pieces_read_error s
  | DTooBig => pieces_too_big | DOom => pieces_oom | DShortHdr => pieces_short_hdr | DCfgOverrun => pieces_cfg_overrun
  end.
Definition fdiag_bytes (d : diag_msg) : list byte := to_bytes (concat (fdiag_pieces d)).

(* [comment removed for export] *)
Definition diag_small (d : diag_msg) : Prop :=
  match d with DUsage s | DCannotOpen s | DReadError s => zlength s <= 2^25 | _ => True end.

Definition so_fprintf_diag_stmt : Prop :=
  forall (d : diag_msg)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (lo : Z) (canary : word) (K : TSet),
    MOK mo -> chan_ok mo 2 ->
    stderr_wfile m ->
    a0 = Z_to_bv 64 RSTDERR -> diag_args d m a1 a2 lo (bv_unsigned sp) -> diag_small d ->
    stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) ->
    (bv_unsigned sp < 2^63) ->
    ssp_cells m canary -> mem_inv usegs m -> frm0 fc ->
    K [] ->
    (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
        munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m' -> wmono usegs m m' -> mem_inv usegs m' ->
        frm0 fc' -> (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k) ->
        stk usegs m' lo (bv_unsigned sp) -> stderr_wfile m' -> ssp_cells m' canary ->
        realizes usegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  Ft (ret_pc ra) fc' None m' (seg_rom usegs)) mo) K) ->
    realizes usegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 0x18634) fc None m (seg_rom usegs)) mo)
             (t_emit (W 2 (fdiag_bytes d)) K).

(* [comment removed for export] *)
Definition so_fwrite_diag_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (lo : Z) (canary : word) (s : list Z) (K : TSet),
    MOK mo -> chan_ok mo 2 ->
    stderr_wfile0 m ->
    bytes_at usegs m (bv_unsigned a0) (zb s) -> Forall (fun c => 0 <= c < 256) s -> 0 < zlength s < 2^25 ->
    a1 = Z_to_bv 64 (zlength s) -> a2 = Z_to_bv 64 1 -> a3 = Z_to_bv 64 RSTDERR ->
    stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FWRITE_DEPTH) -> (GLOBALS_TOP <= lo) ->
    (bv_unsigned a0 + zlength s <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
    (bv_unsigned a0 + zlength s <= RSTDERR \/ RSTDERR + 232 <= bv_unsigned a0) ->
    ssp_cells m canary -> mem_inv usegs m ->
    K [] ->
    (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
        munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m' -> wmono usegs m m' -> mem_inv usegs m' ->
        stk usegs m' lo (bv_unsigned sp) -> stderr_wfile0 m' -> ssp_cells m' canary ->
        realizes usegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  F (ret_pc ra) fc None m' (seg_rom usegs)) mo) K) ->
    realizes usegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 0x187d0) fc None m (seg_rom usegs)) mo)
             (t_emit (W 2 (zb s)) K).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition EMITD_DEPTH : Z := 5632.
Definition emit_line : list byte := [Z_to_bv 8 48; Z_to_bv 8 10].   (* [comment removed for export] *)

Definition emit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (lo : Z) (canary : word) (m : mem) (so' : stdout_st) (mo : Model) (K : TSet) : Prop :=
  forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
    munch [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)] m m' ->
    wmono usegs m m' -> mem_inv usegs m' -> frm0 fc' ->
    (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k) ->
    stk usegs m' lo (bv_unsigned sp) -> stdout_file m' so' -> ssp_cells m' canary ->
    realizes usegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                              Ft (ret_pc ra) fc' None m' (seg_rom usegs)) mo) K.

(* [comment removed for export] *)
Definition emit_after_first : stdout_st := mkStdout true [] false false.

Definition so_emit_first_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (lo : Z) (canary : word) (K : TSet),
    MOK mo -> chan_ok mo 1 ->
    stdout_file m stdout_init ->
    bv_unsigned a1 mod 2^32 = 0 ->
    stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - EMITD_DEPTH) -> (GLOBALS_TOP <= lo) -> (bv_unsigned sp < 2^63) ->
    ssp_cells m canary -> mem_inv usegs m -> frm0 fc ->
    K [] ->
    emit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m emit_after_first mo K ->
    realizes usegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 0x135c4) fc None m (seg_rom usegs)) mo)
             (t_emit (W 1 emit_line) K).

(* [comment removed for export] *)
Definition so_emit_again_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (lo : Z) (canary : word) (buf : list Z) (K : TSet),
    MOK mo -> chan_ok mo 1 ->
    stdout_file m (mkStdout true buf false false) -> zlength buf + 2 <= STDOUT_BUFSIZ -> Forall (fun c => 0 <= c < 256) buf ->
    bv_unsigned a1 mod 2^32 = 0 ->
    stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - EMITD_DEPTH) -> (GLOBALS_TOP <= lo) -> (bv_unsigned sp < 2^63) ->
    ssp_cells m canary -> mem_inv usegs m -> frm0 fc ->
    K [] ->
    emit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (mkStdout true (buf ++ [48; 10]) false false) mo K ->
    realizes usegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 0x135c4) fc None m (seg_rom usegs)) mo)
             (t_emit (W 1 []) K).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition EXIT_DEPTH : Z := 176.

Definition so_exit_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (lo : Z) (so : stdout_st)
         (code t : Z) (td0 td1 td2 td3 guard : word) (cdt thr sec : byte) (tm1 : word) (ph : bool),
    MOK mo -> chan_ok mo 1 ->
    stk usegs m lo (bv_unsigned sp) ->
    rw_cells usegs m RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)] ->      (* [comment removed for export] *)
    rw_cells usegs m 0x54c30 [C4 (Z_to_bv 64 0)] ->                                  (* [comment removed for export] *)
    rw_cells usegs m 0x23638 [C8 (Z_to_bv 64 0x23540); C8 (Z_to_bv 64 0x23538)] ->    (* [comment removed for export] *)
    rw_cells usegs m 0x23538 [C8 (Z_to_bv 64 0x130dc)] ->                            (* [comment removed for export] *)
    rw_cells usegs m 0x248b8 [C1 (Z_to_bv 8 0)] ->                                    (* [comment removed for export] *)
    rw_cells usegs m 0x235e0 [C8 (Z_to_bv 64 0x15fdc); C8 (Z_to_bv 64 0)] ->          (* [comment removed for export] *)
    rw_cells usegs m 0x24648 [C8 (Z_to_bv 64 0x24648)] ->                            (* [comment removed for export] *)
    rw_cells usegs m 0x348c4 [C1 (Z_to_bv 8 0)] ->                                    (* [comment removed for export] *)
    ATEX ph m ->                                                                      (* [comment removed for export] *)
    rw_cells usegs m 0x54c58 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->   (* [comment removed for export] *)
    rw_cells usegs m 0x55088 [C8 (Z_to_bv 64 0)] ->                                  (* [comment removed for export] *)
    rw_cells usegs m 0x55078 [C8 (Z_to_bv 64 0)] ->                                  (* [comment removed for export] *)
    rw_cells usegs m 0x24860 [C8 (Z_to_bv 64 RSTDOUT)] ->                            (* [comment removed for export] *)
    rw_cells usegs m 0x24770 [C8 (Z_to_bv 64 RSTDERR)] ->                            (* [comment removed for export] *)
    stdout_file m so -> zlength (so_buf so) <= 2^25 -> stderr_file m ->
    rw_cells usegs m 0x23630 [C8 (Z_to_bv 64 0x54c38)] -> rw_cells usegs m 0x54c38 [C8 guard] ->   (* [comment removed for export] *)
    mem_inv usegs m ->
    tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code -> 0 <= code < 256 ->
    (0 < t < 4194304) -> (lo <= bv_unsigned sp - EXIT_DEPTH) -> (GLOBALS_TOP <= lo) ->
    realizes usegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 0x160f8) fc None m (seg_rom usegs)) mo)
             (t_emit (W 1 (to_bytes (so_buf so))) (t_exit (Z_to_bv 64 code) (m_fs mo))).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition so_diag_str_stmt (fmt : Z) (msg : list byte -> list byte) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (lo : Z) (canary : word) (s slack : list byte) (K : TSet),
    MOK mo -> chan_ok mo 2 ->
    stderr_wfile m ->
    a0 = Z_to_bv 64 RSTDERR -> a1 = Z_to_bv 64 fmt ->
    bytes_at usegs m (bv_unsigned a2) (s ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) s ->
    ((- (bv_unsigned a2 + zlength s + 1)) mod 8 <= zlength slack) -> (zlength s <= 2^20) ->
    (bv_unsigned a2 + zlength s + 1 + zlength slack <= lo \/ bv_unsigned sp <= bv_unsigned a2) ->
    (GLOBALS_TOP <= bv_unsigned a2) ->
    stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) ->
    (bv_unsigned sp < 2^63) ->
    ssp_cells m canary -> mem_inv usegs m -> frm0 fc ->
    K [] ->
    (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
        munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m' -> wmono usegs m m' -> mem_inv usegs m' ->
        frm0 fc' -> (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k) ->
        stk usegs m' lo (bv_unsigned sp) -> stderr_wfile m' -> ssp_cells m' canary ->
        realizes usegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  Ft (ret_pc ra) fc' None m' (seg_rom usegs)) mo) K) ->
    realizes usegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 0x18634) fc None m (seg_rom usegs)) mo)
             (t_emit (W 2 (msg s)) K).

Definition so_diag_usage_stmt : Prop := so_diag_str_stmt A_FMT_usage msg_usage.              (* [comment removed for export] *)
Definition so_diag_cannot_open_stmt : Prop := so_diag_str_stmt A_FMT_cannot_open msg_cannot_open.   (* [comment removed for export] *)
Definition so_diag_read_error_stmt : Prop := so_diag_str_stmt A_FMT_read_error msg_read_error.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition so_diag_refused_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (lo : Z) (canary : word) (K : TSet),
    MOK mo -> chan_ok mo 2 ->
    stderr_wfile m ->
    a0 = Z_to_bv 64 RSTDERR -> a1 = Z_to_bv 64 A_FMT_too_big -> bv_unsigned a2 mod 2^32 = 67108864 ->
    stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) ->
    (bv_unsigned sp < 2^63) ->
    ssp_cells m canary -> mem_inv usegs m -> frm0 fc ->
    K [] ->
    (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
        munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m' -> wmono usegs m m' -> mem_inv usegs m' ->
        frm0 fc' -> (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k) ->
        stk usegs m' lo (bv_unsigned sp) -> stderr_wfile m' -> ssp_cells m' canary ->
        realizes usegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  Ft (ret_pc ra) fc' None m' (seg_rom usegs)) mo) K) ->
    realizes usegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 0x18634) fc None m (seg_rom usegs)) mo)
             (t_emit (W 2 msg_refused) K).

(* [comment removed for export] *)
Definition A_MSG_oom : Z := 0x102c5.      (* [comment removed for export] *)
Definition A_MSG_short : Z := 0x10389.    (* [comment removed for export] *)
Definition A_MSG_overrun : Z := 0x102f6.  (* [comment removed for export] *)

Definition so_diag_lit_stmt (A n : Z) (msg : list byte) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (lo : Z) (canary : word) (K : TSet),
    MOK mo -> chan_ok mo 2 ->
    stderr_wfile0 m ->
    a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 1 -> a3 = Z_to_bv 64 RSTDERR ->
    stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FWRITE_DEPTH) -> (GLOBALS_TOP <= lo) ->
    ssp_cells m canary -> mem_inv usegs m ->
    K [] ->
    (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
        munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m' -> wmono usegs m m' -> mem_inv usegs m' ->
        stk usegs m' lo (bv_unsigned sp) -> stderr_wfile0 m' -> ssp_cells m' canary ->
        realizes usegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  F (ret_pc ra) fc None m' (seg_rom usegs)) mo) K) ->
    realizes usegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 0x187d0) fc None m (seg_rom usegs)) mo)
             (t_emit (W 2 msg) K).

Definition so_diag_oom_stmt : Prop := so_diag_lit_stmt A_MSG_oom 19 msg_oom.
Definition so_diag_short_stmt : Prop := so_diag_lit_stmt A_MSG_short 31 msg_short.
Definition so_diag_overrun_stmt : Prop := so_diag_lit_stmt A_MSG_overrun 31 msg_overrun.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac so_img_chunk NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  assert (H : rw_cells usegs m A cs);
  [ apply (rw_cells_recast usegs m A [CB (length bs) bs] cs);
    [ apply (rw_cells_image0 usegs m A bs);
      [ intros a' Ha'; apply NONE; cbn [length] in Ha'; lia | vm_compute; reflexivity | lia | cbn [length]; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].

(* [comment removed for export] *)
Lemma stdout_file_init : forall m : mem,
  (forall a : word, 0x24778 <= bv_unsigned a < 0x24860 -> m a = None) ->
  (forall a : word, 0x550a0 <= bv_unsigned a < 0x554a0 -> m a = None) ->
  stdout_file m stdout_init.
Proof.
  intros m N1 N2. unfold stdout_file, stdout_init. cbn [so_active so_buf so_first so_lbf_nl zlength length Z.of_nat].
  so_img_chunk N1 m 0x24778 (file_cells (Z_to_bv 64 5) 0 0 0 0x18d4c 0x550a0 1024 1 (Z_to_bv 64 0) 10 (repeat (Z_to_bv 8 0) 80)) FC.
  so_img_chunk N2 m 0x550a0 [CB 1024 (repeat (Z_to_bv 8 0) 1024)] BC.
  exists (Z_to_bv 64 5), (Z_to_bv 64 0), (repeat (Z_to_bv 8 0) 80), (repeat (Z_to_bv 8 0) 1024).
  split; [exact FC|]. split; [reflexivity|]. split; [exact BC|]. split; [reflexivity|]. split; [apply Z.leb_le; reflexivity|]. intros _; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma stderr_wfile0_init : forall m : mem,
  (forall a : word, 0x24688 <= bv_unsigned a < 0x24770 -> m a = None) ->
  stderr_wfile0 m.
Proof.
  intros m N1. unfold stderr_wfile0.
  so_img_chunk N1 m 0x24688 (file_cells (Z_to_bv 64 5) 0 0 0 0x18bb4 0x55098 0 2 (Z_to_bv 64 0) 0xffffffff (repeat (Z_to_bv 8 0) 80)) FC.
  exists (Z_to_bv 64 5), (Z_to_bv 64 0), 0, 0, (repeat (Z_to_bv 8 0) 80).
  split; [exact FC|]. split; [reflexivity|]. split; [left; reflexivity| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma to_bytes_of_bytes : forall l : list byte, to_bytes (map bv_unsigned l) = l.
Proof.
  induction l as [|b l IH]; [reflexivity|]. cbn. f_equal; [| exact IH].
  apply bv_eq. rewrite Z_to_bv_unsigned. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_wrap, bv_modulus in *. apply Z.mod_small. lia.
Qed.

Lemma to_bytes_app : forall a b, to_bytes (a ++ b) = to_bytes a ++ to_bytes b.
Proof. intros; unfold to_bytes; apply map_app. Qed.

Lemma msg_usage_eq : forall argv0 : list byte, fdiag_bytes (DUsage (map bv_unsigned argv0)) = msg_usage argv0.
Proof.
  intros argv0. unfold fdiag_bytes, fdiag_pieces, pieces_usage, msg_usage. cbn [concat].
  rewrite !to_bytes_app, to_bytes_of_bytes. reflexivity.
Qed.

Lemma msg_cannot_open_eq : forall p : list byte, fdiag_bytes (DCannotOpen (map bv_unsigned p)) = msg_cannot_open p.
Proof.
  intros p. unfold fdiag_bytes, fdiag_pieces, pieces_cannot_open, msg_cannot_open. cbn [concat].
  rewrite !to_bytes_app, to_bytes_of_bytes. reflexivity.
Qed.

Lemma msg_read_error_eq : forall p : list byte, fdiag_bytes (DReadError (map bv_unsigned p)) = msg_read_error p.
Proof.
  intros p. unfold fdiag_bytes, fdiag_pieces, pieces_read_error, msg_read_error. cbn [concat].
  rewrite !to_bytes_app, to_bytes_of_bytes. reflexivity.
Qed.

Lemma msg_refused_eq : fdiag_bytes DTooBig = msg_refused.
Proof. vm_compute. reflexivity. Qed.
Lemma msg_oom_eq : zb (concat pieces_oom) = msg_oom.
Proof. vm_compute. reflexivity. Qed.
Lemma msg_short_eq : zb (concat pieces_short_hdr) = msg_short.
Proof. vm_compute. reflexivity. Qed.
Lemma msg_overrun_eq : zb (concat pieces_cfg_overrun) = msg_overrun.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma zero_lines_eq : forall n, to_bytes (concat (repeat [48; 10] n)) = zero_lines n.
Proof. induction n as [|n IH]; [reflexivity|]. cbn. rewrite <- IH. reflexivity. Qed.
End SO_iface.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import SFModel Arr ITree Nodes Decode.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim Monad SoftFloat FmtFp Stdio Driver.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import F_memcpy F_fwritex F_pad F_fmt_fp_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require NumFacts_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import F_pop_arg Exit F_printf_iface.
Import Stdio_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import Printf_model.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import UImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SO_model.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
Section StderrSink.
  Context {St : Type}.
  Variable B : Z.
  Definition OUT_stderr (s : list Z) : M (list Z * St) unit :=
    fun bs => let '(buf, st) := bs in
      if INTERNAL_BUFSIZ - zlength buf <? zlength s
      then ebind (stdio_writev 2 buf s st) (fun r => ITree.Ret (Ok (tt, ([], snd r))))
      else ITree.Ret (Ok (tt, (buf ++ s, st))).
End StderrSink.

Definition fwritex_stderr_stmt : Prop :=
  forall (St : Type) (B : Z),
    @out_stmt (list Z * St) RSTDERR B 80 (SINK_stderr B) TOPOK_none OUT_stderr.

(* [comment removed for export] *)
Definition fwritex_stdout_stmt : Prop :=
  forall (St : Type) (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St),
    (forall s so, get_so (set_so so s) = so) -> (forall s so so', set_so so' (set_so so s) = set_so so' s) ->
    @out_stmt St RSTDOUT RSTDOUT_BUF 1024 (SINK_stdout get_so) TOPOK_none (stdout_fwritex get_so set_so).


Definition stdio_write_flush_stmt : Prop :=
  forall (St : Type) (B : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (buf : list Z) (st : St) (lo : Z) (canary : word),
    SINK_stderr B m (buf, st) ->
    a0 = Z_to_bv 64 RSTDERR -> a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 0 ->   (* [comment removed for export] *)
    stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - OUT_DEPTH) -> (GLOBALS_TOP <= lo) ->
    (bv_unsigned sp < 2^63) -> (B + 80 <= lo \/ bv_unsigned sp <= B) ->
    ssp_cells m canary -> mem_inv usegs m ->
    implM usegs (stdio_writev 2 buf [] : M St unit) st
          (stdio_write_flush_post B ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo canary m)
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x18bb4) fc None m (seg_rom usegs)).


Section Emit.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

  Definition fprintf_diag_stmt : Prop :=
    forall (d : diag_msg)
           (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word),
      fwritex_stderr_stmt -> stdio_write_flush_stmt ->
      stderr_wfile m ->
      a0 = Z_to_bv 64 RSTDERR -> diag_args d m a1 a2 lo (bv_unsigned sp) ->
      stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) ->
      (bv_unsigned sp < 2^63) ->
      ssp_cells m canary -> mem_inv usegs m -> frm0 fc ->
      implM usegs (s_diag (St:=St) d) st
            (fprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x18634) fc None m (seg_rom usegs)).
End Emit.

(* [comment removed for export] *)
Section Fwrite.
  Context {St : Type}.

  (* [comment removed for export] *)
  Definition fwrite_diag_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word) (s : list Z),
      towrite_stmt ->
      stderr_wfile0 m ->
      bytes_at usegs m (bv_unsigned a0) (zb s) -> Forall (fun c => 0 <= c < 256) s -> 0 < zlength s < 2^31 ->
      a1 = Z_to_bv 64 (zlength s) -> a2 = Z_to_bv 64 1 -> a3 = Z_to_bv 64 RSTDERR ->
      stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FWRITE_DEPTH) -> (GLOBALS_TOP <= lo) ->
      (bv_unsigned a0 + zlength s <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
      (bv_unsigned a0 + zlength s <= RSTDERR \/ RSTDERR + 232 <= bv_unsigned a0) ->
      ssp_cells m canary -> mem_inv usegs m ->
      implM usegs (stderr_fwrite s : M St unit) st
            (fwrite_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo canary m st)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x187d0) fc None m (seg_rom usegs)).
End Fwrite.

(* [comment removed for export] *)
Section StdioExitStatement.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Local Open Scope bv_scope.
  Local Notation z64 := (Z_to_bv 64 0).
  Local Notation RTP := 0x349d0%Z (only parsing).
  Definition stdio_exit_spec_stmt : Prop :=
    forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (s : St) (guard : word)
           (cdt thr sec : byte) (tm1 : word),
      stk usegs m lo (bv_unsigned sp) ->
      rw_cells usegs m 0x54c58 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->   (* [comment removed for export] *)
      rw_cells usegs m 0x55088 [C8 z64] ->                                            (* [comment removed for export] *)
      rw_cells usegs m 0x55078 [C8 z64] ->                                            (* [comment removed for export] *)
      rw_cells usegs m 0x24860 [C8 (Z_to_bv 64 RSTDOUT)] ->                          (* [comment removed for export] *)
      rw_cells usegs m 0x24770 [C8 (Z_to_bv 64 RSTDERR)] ->                          (* [comment removed for export] *)
      stdout_file m (get_so s) -> stderr_file m ->
      rw_cells usegs m 0x23630 [C8 (Z_to_bv 64 0x54c38)] -> rw_cells usegs m 0x54c38 [C8 guard] ->   (* [comment removed for export] *)
      mem_inv usegs m ->
      tp = Z_to_bv 64 RTP ->
      (lo <= bv_unsigned sp - 160)%Z -> (0x56000 <= lo)%Z ->
      implM usegs (stdout_exit_flush get_so set_so) s
            (stdio_exit_post set_so ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m s)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x188dc) fc None m (seg_rom usegs)).
End StdioExitStatement.
