(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec ImageA Nodes RzCPS NodesA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import Prelim Canon Stdio.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition e_open : Z := 0x557c1c.
Definition e_close : Z := 0x56a278.
Definition e_exit : Z := 0x5579a8.
(* [comment removed for export] *)
Definition SSP_GUARD : Z := 0xbfae90.
Definition GOT_SSP : Z := 0x5e2c40.

Section DIface.
Variable RT : rt_sig.
(* [comment removed for export] *)
Variable XENV : mem -> Prop.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
(* [comment removed for export] *)
Variable LIBX : mem -> Prop.

(* [comment removed for export] *)
Definition ssp_cells (m : mem) : Prop :=
  exists g : word, ro_cells bsegs m GOT_SSP [C8 (Z_to_bv 64 SSP_GUARD)] /\ ro_cells bsegs m SSP_GUARD [C8 g].

(* [comment removed for export] *)
Definition cancel_cells (m : mem) : Prop := rw_cells bsegs m (0xbdae50 + -156) [C4 (Z_to_bv 64 0); C1 (Z_to_bv 8 0)].

(* [comment removed for export] *)
Definition musl_after (Σ : rts RT) (sp lo : Z) (W : list (Z * Z)) (m m' : mem) : Prop :=
  ART RT Σ m' /\ mem_inv bsegs m' /\ wmono bsegs m m' /\ stk bsegs m' lo sp /\ munch ((sp - 128, sp) :: W) m m'.

(* [comment removed for export] *)
Definition open_contract : Prop :=
  forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (path : Z) (s : list byte) (lo : Z) ent,
  a0 = Z_to_bv 64 path -> a1 = Z_to_bv 64 0 ->
  bytes_at bsegs m path (s ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) s ->
  path_has_slash s = false -> path_eqb s dotdot_path = false ->
  open_ent s fs0 = Some ent -> fd_lookup F0 (alloc_fd F0) = None ->
  stk bsegs m lo (bv_unsigned sp) -> lo + 128 <= bv_unsigned sp -> rt_sp0 RT Σ - STACK_WIN <= lo ->
  rw_cells bsegs m (errno_cell tp) [C4 (Z_to_bv 64 0)] \/ (exists v, rw_cells bsegs m (errno_cell tp) [C4 v]) ->
  ssp_cells m -> cancel_cells m -> ART RT Σ m -> mem_inv bsegs m ->
  tp = Z_to_bv 64 0xbdae50 -> (path + Z.of_nat (length s) + 1 <= lo \/ bv_unsigned sp <= path) ->
  cps2 bsegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
                                                     s10 s11 t3 t4 t5 t6 F fc e_open m)))
    (fun c => exists (e : Z) m', In e openat_errnos /\
        ASTA RT Σ (PMfd F0 fs0) (fun ms => ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (-1)) m' ms
           /\ musl_after Σ (bv_unsigned sp) lo [(errno_cell tp, errno_cell tp + 4)] m m'
           /\ rw_cells bsegs m' (errno_cell tp) [C4 (Z_to_bv 64 e)]) c)
    (fun c => exists m',
        ASTA RT Σ (PMfd (fd_insert F0 (alloc_fd F0) ent) fs0)
           (fun ms => ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (alloc_fd F0) m' ms
              /\ musl_after Σ (bv_unsigned sp) lo [] m m') c).

(* [comment removed for export] *)
Definition open_refused_contract : Prop :=
  forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (path : Z) (s : list byte) (lo : Z),
  a0 = Z_to_bv 64 path -> a1 = Z_to_bv 64 0 ->
  bytes_at bsegs m path (s ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) s ->
  path_has_slash s = false -> path_eqb s dotdot_path = false -> open_ent s fs0 = None ->
  stk bsegs m lo (bv_unsigned sp) -> lo + 128 <= bv_unsigned sp -> rt_sp0 RT Σ - STACK_WIN <= lo ->
  (exists v, rw_cells bsegs m (errno_cell tp) [C4 v]) ->
  ssp_cells m -> cancel_cells m -> ART RT Σ m -> mem_inv bsegs m ->
  tp = Z_to_bv 64 0xbdae50 -> (path + Z.of_nat (length s) + 1 <= lo \/ bv_unsigned sp <= path) ->
  cps bsegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
                                                    s10 s11 t3 t4 t5 t6 F fc e_open m)))
    (fun c => exists (e : Z) m', 1 <= e <= 4095 /\
        ASTA RT Σ (PMfd F0 fs0) (fun ms => ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (-1)) m' ms
           /\ musl_after Σ (bv_unsigned sp) lo [(errno_cell tp, errno_cell tp + 4)] m m'
           /\ rw_cells bsegs m' (errno_cell tp) [C4 (Z_to_bv 64 e)]) c).

(* [comment removed for export] *)
Definition close_contract : Prop :=
  forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (fd lo : Z),
  a0 = Z_to_bv 64 fd -> 3 <= fd < 2^31 -> fd_lookup F0 (Z_to_bv 64 fd) <> None ->
  stk bsegs m lo (bv_unsigned sp) -> lo + 128 <= bv_unsigned sp -> rt_sp0 RT Σ - STACK_WIN <= lo ->
  tp = Z_to_bv 64 0xbdae50 -> cancel_cells m ->
  ART RT Σ m -> mem_inv bsegs m ->
  cps bsegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
                                                    s10 s11 t3 t4 t5 t6 F fc e_close m)))
    (fun c => exists m', ASTA RT Σ (PMfd (fd_remove F0 (Z_to_bv 64 fd)) fs0)
        (fun ms => ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
           /\ musl_after Σ (bv_unsigned sp) lo [] m m') c).

(* [comment removed for export] *)
Definition EXITc (fs0 : Fs) (code : Z) (c : config) : Prop :=
  exists A Pm PM, AST SEGTOP_A A Pm PM c
    /\ (forall ms, Pm ms -> (ms_svc_pending ms = Some (Z_to_bv 64 93) \/ ms_svc_pending ms = Some (Z_to_bv 64 94))
                            /\ areg ms 10 = Z_to_bv 64 code)
    /\ (forall mo, PM mo -> m_fs mo = fs0).

(* [comment removed for export] *)
Definition exit_contract : Prop :=
  forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (so : stdout_st) (code lo : Z),
  a0 = Z_to_bv 64 code -> 0 <= code < 256 -> tp = Z_to_bv 64 0xbdae50 ->
  (so = stdout_init \/ exists k, (k < 500)%nat /\ so = so_lines k) ->
  fd_lookup F0 (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  OUT_rep so m -> ERR_rep m -> XENV m -> LIBX m ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo -> io_ssp m ->
  (* [comment removed for export] *)
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> lo + RT_STACK + 0x1000 <= bv_unsigned sp ->
  cpsE bsegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
                                                     s10 s11 t3 t4 t5 t6 F fc e_exit m)))
    (evw 1 (so_buf so)) (EXITc fs0 code).

End DIface.
