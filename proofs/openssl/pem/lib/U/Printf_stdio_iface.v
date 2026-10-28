(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import SFModel Arr ITree Nodes Decode.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim Monad PrintfModel PrintfFormats Stdio Driver.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Printf_lib F_memset F_memcpy F_fwritex F_pop_arg F_printf_iface.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Export Stdio_iface Printf_wfile.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import PrintfModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
Section ImplSo.
  Variable segs : list Segment.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Lemma implM_rdso : forall {A} (f : stdout_st -> @M St A) (s : St) Q ms,
    implM segs (f (get_so s)) s Q ms -> implM segs (Monad.mbind (rd_so get_so) f) s Q ms.
  Proof. intros A f s Q ms H. exact H. Qed.
  Lemma implM_updso : forall {A} (g : stdout_st -> stdout_st) (f : unit -> @M St A) (s : St) Q ms,
    implM segs (f tt) (set_so (g (get_so s)) s) Q ms -> implM segs (Monad.mbind (upd_so get_so set_so g) f) s Q ms.
  Proof. intros A g f s Q ms H. exact H. Qed.
  Lemma implM_updso_last : forall (g : stdout_st -> stdout_st) (s : St) (Q : unit -> St -> machine_state -> Prop) ms,
    Q tt (set_so (g (get_so s)) s) ms -> implM segs (upd_so get_so set_so g) s Q ms.
  Proof. intros g s Q ms H. apply implM_upd. apply evt_done. exact H. Qed.
End ImplSo.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition OUT_MAX : Z := 2^25.

(* [comment removed for export] *)
Section StderrSink.
  Context {St : Type}.
  Variable B : Z.

  Definition SINK_stderr (m : mem) (bs : list Z * St) : Prop :=
    let buf := fst bs in
    exists (flags mode : word) (tail : list byte) (rest : list byte),
      rw_cells usegs m RSTDERR (file_cells flags (B + 80) (B + zlength buf) B F_STDIO_WRITE B 80 2 mode 0xffffffff tail)
      /\ Z.land (bv_unsigned flags) 32 = 0 /\ Z.land (bv_unsigned flags) 8 = 0      (* [comment removed for export] *)
      /\ rw_cells usegs m B [CB 80 (zb buf ++ rest)]
      /\ zlength buf + zlength rest = 80
      /\ B + 80 < 2^63 /\ GLOBALS_TOP <= B.  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition OUT_stderr (s : list Z) : M (list Z * St) unit :=
    fun bs => let '(buf, st) := bs in
      if OUT_MAX <? zlength s then ITree.Ret Unr else
      if INTERNAL_BUFSIZ - zlength buf <? zlength s
      then ebind (stdio_writev 2 buf s st) (fun r => ITree.Ret (Ok (tt, ([], snd r))))
      else ITree.Ret (Ok (tt, (buf ++ s, st))).
  Definition OUTFP_stderr (y w p fl t : Z) : M (list Z * St) Z := fun _ => ITree.Ret Unr.
End StderrSink.

(* [comment removed for export] *)
Section StdoutSink.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

  Definition SINK_stdout (m : mem) (st : St) : Prop :=
    let so := get_so st in
    so_active so = true /\
    exists (flags mode : word) (tail bufbytes : list byte),
      rw_cells usegs m RSTDOUT
        (file_cells flags (RSTDOUT_BUF + 1024) (RSTDOUT_BUF + zlength (so_buf so)) RSTDOUT_BUF
           (if so_first so then F_STDOUT_WRITE else F_STDIO_WRITE)
           RSTDOUT_BUF 1024 1 mode
           (if so_lbf_nl so then 10 else 0xffffffff) tail)
      /\ Z.land (bv_unsigned flags) 104 = 0                       (* [comment removed for export] *)
      /\ rw_cells usegs m RSTDOUT_BUF [CB 1024 bufbytes]
      /\ firstn (length (so_buf so)) bufbytes = to_bytes (so_buf so)
      /\ zlength (so_buf so) <= 1024.
  Definition OUTFP_stdout (y w p fl t : Z) : M St Z := fun _ => ITree.Ret Unr.
  (* [comment removed for export] *)
  Definition OUT_stdout (s : list Z) : M St unit :=
    if OUT_MAX <? zlength s then munr else stdout_fwritex get_so set_so s.
End StdoutSink.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fwritex_stderr_stmt : Prop :=
  forall (St : Type) (B : Z),
    @out_stmt (list Z * St) RSTDERR B 80 (SINK_stderr B) TOPOK_none OUT_stderr.

(* [comment removed for export] *)
Definition fwritex_stdout_stmt : Prop :=
  forall (St : Type) (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St),
    (forall s so, get_so (set_so so s) = so) -> (forall s so so', set_so so' (set_so so s) = set_so so' s) ->
    @out_stmt St RSTDOUT RSTDOUT_BUF 1024 (SINK_stdout get_so) TOPOK_none (OUT_stdout get_so set_so).

(* [comment removed for export] *)
Definition stdio_write_flush_post {St : Type} (B : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
  fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232); (B, B + 80)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ SINK_stderr B m' ([], st')
    /\ ssp_cells m' canary.
Definition stdio_write_flush_stmt : Prop :=
  forall (St : Type) (B : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (buf : list Z) (st : St) (lo : Z) (canary : word),
    SINK_stderr B m (buf, st) ->
    a0 = Z_to_bv 64 RSTDERR -> a1 = Z_to_bv 64 0 (* [comment removed for export] *) -> a2 = Z_to_bv 64 0 ->
    stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - OUT_DEPTH) -> (GLOBALS_TOP <= lo) ->
    (bv_unsigned sp < 2^63) -> (B + 80 <= lo \/ bv_unsigned sp <= B) ->
    ssp_cells m canary -> mem_inv usegs m ->
    implM usegs (stdio_writev 2 buf [] : M St unit) st
          (stdio_write_flush_post B ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo canary m)
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x2b44b8) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition EMIT_DEPTH : Z := 5632.
Section Emit.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

  Definition emit_printf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom usegs)
      /\ munch [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)] m m'
      /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ frm0 fc'
      /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ stdout_file m' (get_so st')
      /\ ssp_cells m' canary.

  Definition emit_printf_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word),
      (forall x so, get_so (set_so so x) = so) -> (forall x so so', set_so so' (set_so so x) = set_so so' x) ->
      fwritex_stdout_stmt ->
      stdout_file m (get_so st) ->
      bv_unsigned a1 mod 2^32 = 0 ->
      stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - EMIT_DEPTH) -> (GLOBALS_TOP <= lo) ->
      (bv_unsigned sp < 2^63) ->
      ssp_cells m canary -> mem_inv usegs m -> frm0 fc ->
      implM usegs (stdout_vprintf get_so set_so pieces_emit_0) st
            (emit_printf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0xe1a64) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition FPRINTF_DEPTH : Z := 5632.

  Definition diag_args (d : diag_msg) (m : mem) (fmtp argw : word) (lo sp : Z) : Prop :=
    match d with
    | DUsage s | DCannotOpen s | DReadError s =>
        fmtp = Z_to_bv 64 (match d with DUsage _ => A_FMT_usage | DCannotOpen _ => A_FMT_cannot_open | _ => A_FMT_read_error end)
        /\ exists slack : list byte,
             bytes_at usegs m (bv_unsigned argw) (zb s ++ Z_to_bv 8 0 :: slack)
             /\ Forall (fun c => 0 < c < 256) s
             /\ ((- (bv_unsigned argw + zlength s + 1)) mod 8 <= zlength slack)
             /\ (zlength s < 2^24)                    (* [comment removed for export] *)
             /\ (bv_unsigned argw + zlength s + 1 + zlength slack <= lo \/ sp <= bv_unsigned argw)
             /\ (GLOBALS_TOP <= bv_unsigned argw)
    | DTooBig => fmtp = Z_to_bv 64 A_FMT_too_big /\ bv_unsigned argw mod 2^32 = 67108864
    | _ => False
    end.

  Definition fprintf_diag_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (lo : Z) (canary : word) (m : mem) (st : St) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom usegs)
      /\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m'
      /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ frm0 fc'
      /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ stderr_wfile m'
      /\ ssp_cells m' canary
      /\ st' = st.

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
                F (Z_to_bv 64 0x2b4648) fc None m (seg_rom usegs)).
End Emit.

