(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Spec ShapeAlg PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AIcpm9j AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpya4 AIcp3q7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpwpz.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpwpz AIcpw0i.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpq85.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpq85.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpq85.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpya4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp3q7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpwpz.AIcpdm8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpwpz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpw0i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpq85.AIcpa3z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpq85.AIcpesd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpq85.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Se7o.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Ey6n DA_Eg3i DA_Cells.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition MEMCPY_ICPT_ENTRY : Z := 0x574f8.     (* [comment removed for export] *)
Definition MEMSET_ICPT_ENTRY : Z := 0x574f4.     (* [comment removed for export] *)
Definition STRNLEN_ICPT_ENTRY : Z := 0x478e0.    (* [comment removed for export] *)
Definition READ_ICPT_ENTRY : Z := 0x478fc.       Definition READ_ICPT_STACK : Z := 2400.      (* [comment removed for export] *)
Definition FWRITE_ICPT_ENTRY : Z := 0x47900.     Definition FWRITE_ICPT_STACK : Z := 2600.    (* [comment removed for export] *)
Definition FPRINTF_ICPT_ENTRY : Z := 0x47918.    Definition FPRINTF_ICPT_STACK : Z := 8192.   (* [comment removed for export] *)
Definition VPRINTF_ICPT_ENTRY : Z := 0x4790c.    Definition VPRINTF_ICPT_STACK : Z := 8192.
Definition OPEN_ENTRY : Z := 0x985e8.            Definition OPEN_STACK : Z := 112.          (* [comment removed for export] *)
Definition CLOSE_ENTRY : Z := 0xa7298.           Definition CLOSE_STACK : Z := 32.           (* [comment removed for export] *)
Definition TOWRITE_ENTRY : Z := 0x9e1f8.         (* [comment removed for export] *)
Definition FWRITEX_ENTRY : Z := 0x9e008.         Definition FWRITEX_STACK : Z := 2400.         (* [comment removed for export] *)
Definition STDIO_WRITE_ENTRY : Z := 0x9d884.     Definition STDIO_WRITE_STACK : Z := 112.
Definition STDOUT_WRITE_ENTRY : Z := 0x9e288.    Definition STDOUT_WRITE_STACK : Z := 144.     (* [comment removed for export] *)
Definition LIB_ENTRY : Z := 0x86cdc.             Definition LIB_STACK_A : Z := 32768.          (* [comment removed for export] *)

(* [comment removed for export] *)
Definition REAL_READ_CELL : Z := 0xaa8e0.     Definition MUSL_READ : Z := 0xa7378.
Definition REAL_FWRITE_CELL : Z := 0xaa8e8.   Definition MUSL_FWRITE : Z := 0x9e140.
Definition REAL_VPRINTF_CELL : Z := 0xaa900.  Definition MUSL_VPRINTF : Z := 0xa14d8.
Definition REAL_VFPRINTF_CELL : Z := 0xaa908. Definition MUSL_VFPRINTF : Z := 0x9e3c8.
Definition REAL_STRNLEN_CELL : Z := 0xaa9c0.  Definition MUSL_STRNLEN : Z := 0xa2500.
Definition REAL_MEMCHR_CELL : Z := 0xaa8d0.   Definition MUSL_MEMCHR : Z := 0xa1a90.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  #[local] Notation rom := (seg_rom rsegs).

  (* [comment removed for export] *)
  Definition md_io (md md' : Model) (fds' : list (word * FdEntry)) : Prop :=
    m_fs md' = m_fs md /\ m_fds md' = fds' /\ m_halted md' = None.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition memcpy_icpt_cells : (word -> option byte) -> Prop := asan_memcpy_cells.

  Definition memcpy_icpt_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (src junk : list byte) (lo : Z),
      let A := bv_unsigned a0 in let S := bv_unsigned a1 in let N := bv_unsigned a2 in
      bytes_at rsegs m S src -> length src = Z.to_nat N ->
      rw_cells rsegs m A [CB (Z.to_nat N) junk] ->
      (S + N <= A \/ A + N <= S)%Z ->
      mem_inv rsegs m ->
      asan_memcpy_cells m ->
      stk rsegs m lo (bv_unsigned sp) ->
      (lo + MEMCPY_ICPT_STACK <= bv_unsigned sp)%Z -> (alloc_ceiling <= lo)%Z ->
      (A + N <= lo \/ bv_unsigned sp <= A)%Z -> (S + N <= lo \/ bv_unsigned sp <= S)%Z ->
      (N < 2^32)%Z ->
      (N = 0%Z \/ (range_ok m S N /\ range_ok m A N)) ->
      evt rsegs (memcpy_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x574f8) fc None m rom).
  Lemma memcpy_icpt_ok : memcpy_icpt_stmt.
  Proof. exact memcpy_icpt_spec. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition memset_icpt_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk : list byte) (lo : Z),
      let A := bv_unsigned a0 in let N := bv_unsigned a2 in
      rw_cells rsegs m A [CB (Z.to_nat N) junk] ->
      mem_inv rsegs m ->
      asan_memset_cells m ->
      stk rsegs m lo (bv_unsigned sp) ->
      (lo + MEMSET_ICPT_STACK <= bv_unsigned sp)%Z -> (alloc_ceiling <= lo)%Z ->
      (A + N <= lo \/ bv_unsigned sp <= A)%Z ->
      (N < 2^32)%Z ->
      (N = 0%Z \/ range_ok m A N) ->
      evt rsegs (memset_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x574f4) fc None m rom).
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition strnlen_icpt_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (buf : list byte) (lo : Z),
      let A := bv_unsigned a0 in let n := bv_unsigned a1 in
      bytes_at rsegs m A buf ->
      memchr_ok A 0 n buf ->
      mem_inv rsegs m -> strnlen_icpt_cells m ->
      stk rsegs m lo (bv_unsigned sp) -> (lo + STRNLEN_ICPT_STACK <= bv_unsigned sp)%Z -> (alloc_ceiling <= lo)%Z ->
      (A + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= A)%Z ->
      (0 < A)%Z -> (n < 2^32)%Z ->
      (memchr_len 0 n buf = 0%Z \/ range_ok m A (memchr_len 0 n buf)) ->
      evt rsegs (strnlen_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 n buf lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x478e0) fc None m rom).
  (* [comment removed for export] *)


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition open_cells (v : word -> option byte) : Prop :=
       ro_cells rsegs v SSP_GOT [C8 (wz SSP_GUARD)]               (* [comment removed for export] *)
    /\ exists g, ro_cells rsegs v SSP_GUARD [C8 g].              (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition open_pre (v : word -> option byte) (sp a0 a1 tp : word) (p1 : Z) (path : list byte) (lo : Z) : Prop :=
       a0 = wz p1 /\ a1 = wz 0 /\ tp = cl_tp LPA
    /\ bytes_at rsegs v p1 (path ++ [Z_to_bv 8 0]) /\ ~ In (Z_to_bv 8 0) path /\ bv_unsigned sp <= p1
    /\ mem_inv rsegs v /\ open_cells v
    /\ stk rsegs v lo (bv_unsigned sp) /\ lo + OPEN_STACK <= bv_unsigned sp /\ alloc_ceiling <= lo
    /\ (exists e, rw_cells rsegs v ERRNO_CELL [C4 e]).

  (* [comment removed for export] *)
  Definition open_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (r : Z) (errno_written : bool) (lo : Z) (v : word -> option byte) (m' : word -> option byte) (A : AS) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' rom
      /\ munch ((bv_unsigned sp - OPEN_STACK, bv_unsigned sp) :: (if errno_written then [(ERRNO_CELL, ERRNO_CELL + 4)] else [])) v (aview A m')
      /\ wmono rsegs v (aview A m') /\ mem_inv rsegs (aview A m') /\ stk rsegs (aview A m') lo (bv_unsigned sp)
      /\ (exists e, rw_cells rsegs (aview A m') ERRNO_CELL [C4 e]).

  (* [comment removed for export] *)
  Definition open_fail_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (A : AS) (p1 : Z) (path : list byte) (lo : Z) (K : TSet),
      let v := aview A m in
      ainv A m md -> open_pre v sp a0 a1 tp p1 path lo ->
      (   (4096 <= length path)%nat
       \/ path = []
       \/ (path <> [] /\ path <> dot_path /\ path_eqb path dotdot_path = false /\ path_has_slash path = false /\
           (length path <= 4095)%nat /\ fs_lookup (m_fs md) path = None)) ->
      (forall m' md', ainv A m' md' -> md_io md md' (m_fds md) ->
          forall ms', open_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (-1) true lo v m' A ms' ->
          srealizes rsegs (mkCfg ms' md') K) ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (wz OPEN_ENTRY) fc None m rom) md) K.

  (* [comment removed for export] *)
  Definition open_ok_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (A : AS) (p1 : Z) (path : list byte) (lo : Z)
           (e : FdEntry) (KA KB : TSet),
      let v := aview A m in
      ainv A m md -> open_pre v sp a0 a1 tp p1 path lo -> m_fds md = fds_std -> (length path <= 4095)%nat ->
      (   (path = dot_path /\ e = FdDir)
       \/ (path <> [] /\ path <> dot_path /\ path_eqb path dotdot_path = false /\ path_has_slash path = false /\
           (exists d, fs_lookup (m_fs md) path = Some d) /\ e = FdFile path (wz 0))) ->
      (forall m' md', ainv A m' md' -> md_io md md' fds_std ->
          forall ms', open_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (-1) true lo v m' A ms' ->
          srealizes rsegs (mkCfg ms' md') KA) ->
      (forall m' md', ainv A m' md' -> md_io md md' (fds3 e) ->
          forall ms', open_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 3 false lo v m' A ms' ->
          srealizes rsegs (mkCfg ms' md') KB) ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (wz OPEN_ENTRY) fc None m rom) md) (t_alt2 KA KB).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition close_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (A : AS) (e : FdEntry) (lo : Z) (K : TSet),
      let v := aview A m in
      ainv A m md -> mem_inv rsegs v -> a0 = wz 3 -> m_fds md = fds3 e ->
      stk rsegs v lo (bv_unsigned sp) -> lo + CLOSE_STACK <= bv_unsigned sp -> alloc_ceiling <= lo ->
      (exists e0, rw_cells rsegs v ERRNO_CELL [C4 e0]) ->
      (forall m' md', ainv A m' md' -> md_io md md' fds_std ->
          forall ms', open_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 0 false lo v m' A ms' ->
          srealizes rsegs (mkCfg ms' md') K) ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (wz CLOSE_ENTRY) fc None m rom) md) K.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition read_icpt_cells (v : word -> option byte) : Prop :=
       asan_inited_cell v                                           (* [comment removed for export] *)
    /\ ro_cells rsegs v REAL_READ_CELL [C8 (wz MUSL_READ)]
    /\ map_cells v.                                                 (* [comment removed for export] *)

  Definition read_icpt_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (res : word) (W : list (Z * Z)) (lo : Z) (v : word -> option byte) (m' : word -> option byte) (A : AS) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 res a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' rom
      /\ munch ((bv_unsigned sp - READ_ICPT_STACK, bv_unsigned sp) :: W) v (aview A m')
      /\ wmono rsegs v (aview A m') /\ mem_inv rsegs (aview A m') /\ stk rsegs (aview A m') lo (bv_unsigned sp)
      /\ (exists e, rw_cells rsegs (aview A m') ERRNO_CELL [C4 e]).

  (* [comment removed for export] *)
  Definition read_icpt_file_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (A : AS)
           (b n dst cnt : Z) (path : list byte) (off : Z) (data junk : list byte) (lo : Z) (K : TSet),
      let v := aview A m in
      let bs := firstn (Z.to_nat cnt) (skipn (Z.to_nat off) data) in
      ainv A m md -> mem_inv rsegs v -> read_icpt_cells v -> tp = cl_tp LPA ->
      a0 = wz 3 -> a1 = wz dst -> a2 = wz cnt -> 1 <= cnt <= 65536 ->
      a_live A b = Some n -> b <= dst -> dst + cnt <= b + n ->
      rw_cells rsegs v dst [CB (Z.to_nat cnt) junk] ->
      m_fds md = fds3 (FdFile path (wz off)) -> fs_lookup (m_fs md) path = Some data -> 0 <= off < 2^63 ->
      stk rsegs v lo (bv_unsigned sp) -> lo + READ_ICPT_STACK <= bv_unsigned sp -> alloc_ceiling <= lo ->
      (exists e, rw_cells rsegs v ERRNO_CELL [C4 e]) ->
      (forall m' md', ainv A m' md' -> md_io md md' (fds3 (FdFile path (wz (off + Z.of_nat (length bs))))) ->
          rw_cells rsegs (aview A m') dst [CB (length bs) bs; CB (Z.to_nat cnt - length bs) (skipn (length bs) junk)] ->
          forall ms', read_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (wz (Z.of_nat (length bs)))
                                    [(dst, dst + cnt)] lo v m' A ms' ->
          srealizes rsegs (mkCfg ms' md') K) ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (wz READ_ICPT_ENTRY) fc None m rom) md) K.

  (* [comment removed for export] *)
  Definition read_icpt_dir_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (A : AS)
           (b n dst cnt : Z) (junk : list byte) (lo : Z) (K : TSet),
      let v := aview A m in
      ainv A m md -> mem_inv rsegs v -> read_icpt_cells v -> tp = cl_tp LPA ->
      a0 = wz 3 -> a1 = wz dst -> a2 = wz cnt -> 1 <= cnt <= 65536 ->
      a_live A b = Some n -> b <= dst -> dst + cnt <= b + n ->
      rw_cells rsegs v dst [CB (Z.to_nat cnt) junk] ->
      m_fds md = fds3 FdDir ->
      stk rsegs v lo (bv_unsigned sp) -> lo + READ_ICPT_STACK <= bv_unsigned sp -> alloc_ceiling <= lo ->
      (exists e, rw_cells rsegs v ERRNO_CELL [C4 e]) ->
      (forall m' md', ainv A m' md' -> md_io md md' (fds3 FdDir) ->
          rw_cells rsegs (aview A m') dst [CB (Z.to_nat cnt) junk] ->
          rw_cells rsegs (aview A m') ERRNO_CELL [C4 (wz EISDIR)] ->
          forall ms', read_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (wz (-1)) [(ERRNO_CELL, ERRNO_CELL + 4)] lo v m' A ms' ->
          srealizes rsegs (mkCfg ms' md') K) ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (wz READ_ICPT_ENTRY) fc None m rom) md) K.

  (* [comment removed for export] *)
  Definition read_icpt_stage_file_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (A : AS)
           (cnt : Z) (path : list byte) (off : Z) (data junk : list byte) (lo : Z) (K : TSet),
      let v := aview A m in
      let bs := firstn (Z.to_nat cnt) (skipn (Z.to_nat off) data) in
      ainv A m md -> mem_inv rsegs v -> read_icpt_cells v -> tp = cl_tp LPA ->
      a0 = wz 3 -> a1 = wz READ_STAGE -> a2 = wz cnt -> 1 <= cnt <= 65536 ->
      rw_cells rsegs v READ_STAGE [CB (Z.to_nat cnt) junk] ->
      m_fds md = fds3 (FdFile path (wz off)) -> fs_lookup (m_fs md) path = Some data -> 0 <= off < 2^63 ->
      stk rsegs v lo (bv_unsigned sp) -> lo + READ_ICPT_STACK <= bv_unsigned sp -> alloc_ceiling <= lo ->
      (exists e, rw_cells rsegs v ERRNO_CELL [C4 e]) ->
      (forall m' md', ainv A m' md' -> md_io md md' (fds3 (FdFile path (wz (off + Z.of_nat (length bs))))) ->
          rw_cells rsegs (aview A m') READ_STAGE [CB (length bs) bs; CB (Z.to_nat cnt - length bs) (skipn (length bs) junk)] ->
          forall ms', read_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (wz (Z.of_nat (length bs)))
                                    [(READ_STAGE, READ_STAGE + cnt)] lo v m' A ms' ->
          srealizes rsegs (mkCfg ms' md') K) ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (wz READ_ICPT_ENTRY) fc None m rom) md) K.

  Definition read_icpt_stage_dir_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (A : AS)
           (cnt : Z) (junk : list byte) (lo : Z) (K : TSet),
      let v := aview A m in
      ainv A m md -> mem_inv rsegs v -> read_icpt_cells v -> tp = cl_tp LPA ->
      a0 = wz 3 -> a1 = wz READ_STAGE -> a2 = wz cnt -> 1 <= cnt <= 65536 ->
      rw_cells rsegs v READ_STAGE [CB (Z.to_nat cnt) junk] ->
      m_fds md = fds3 FdDir ->
      stk rsegs v lo (bv_unsigned sp) -> lo + READ_ICPT_STACK <= bv_unsigned sp -> alloc_ceiling <= lo ->
      (exists e, rw_cells rsegs v ERRNO_CELL [C4 e]) ->
      (forall m' md', ainv A m' md' -> md_io md md' (fds3 FdDir) ->
          rw_cells rsegs (aview A m') READ_STAGE [CB (Z.to_nat cnt) junk] ->
          rw_cells rsegs (aview A m') ERRNO_CELL [C4 (wz EISDIR)] ->
          forall ms', read_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (wz (-1)) [(ERRNO_CELL, ERRNO_CELL + 4)] lo v m' A ms' ->
          srealizes rsegs (mkCfg ms' md') K) ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (wz READ_ICPT_ENTRY) fc None m rom) md) K.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition towrite_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (Fa : Z) (f : mfile) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 mo' m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' rom
      /\ munch [(Fa, Fa + 152)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ file_at m' Fa (mf_set_mode (mf_set_rp (mf_set_w f (wz (mf_buf f)) (wz (mf_buf f)) (wz (mf_buf f + mf_bufsize f))) w0 w0) mo').
  Definition towrite_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fa : Z) (f : mfile),
      a0 = wz Fa -> file_at m Fa f -> Z.land (mf_flags f) 8 = 0 -> 0 <= mf_flags f < 2^32 -> 0 <= mf_mode f < 2^32 -> mem_inv rsegs m ->
      0xaa000 <= Fa -> Fa + 152 <= 0x60a000 ->
      0 <= mf_buf f -> mf_buf f + mf_bufsize f < 2^47 -> 0 <= mf_bufsize f ->
      evt rsegs (towrite_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fa f m)
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz TOWRITE_ENTRY) fc None m rom).

  (* [comment removed for export] *)
  Definition stdio_write_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (A : AS)
           (Fa : Z) (f : mfile) (pend s : list byte) (sa wp : Z) (lo : Z) (K : TSet),
      let v := aview A m in
      ainv A m md -> mem_inv rsegs v ->
      a0 = wz Fa -> a1 = wz sa -> a2 = wz (Z.of_nat (length s)) ->
      file_at v Fa f -> (mf_fd f = 1 \/ mf_fd f = 2) ->
      0xaa000 <= Fa -> Fa + 152 <= SSP_GUARD -> img_client (L:=LPA) Fa (Fa + 152) ->
      fd_lookup (m_fds md) (wz (mf_fd f)) = Some (FdChannel (wz (mf_fd f))) ->
      mf_wbase f = wz (mf_buf f) -> mf_wpos f = wz wp -> wp = mf_buf f + Z.of_nat (length pend) ->
      bytes_at rsegs v (mf_buf f) pend -> bytes_at rsegs v sa s ->
      Z.of_nat (length pend) + Z.of_nat (length s) <= 2^26 -> (1 <= length pend + length s)%nat ->
      0 <= mf_buf f -> mf_buf f + mf_bufsize f < 2^47 -> 0 <= mf_bufsize f -> Z.of_nat (length pend) <= mf_bufsize f ->
      0 <= sa -> sa + Z.of_nat (length s) < 2^47 ->
      (mf_buf f + Z.of_nat (length pend) <= bv_unsigned sp - STDIO_WRITE_STACK \/ bv_unsigned sp <= mf_buf f) ->
      (sa + Z.of_nat (length s) <= bv_unsigned sp - STDIO_WRITE_STACK \/ bv_unsigned sp <= sa) ->
      (exists g, ro_cells rsegs v SSP_GUARD [C8 g]) -> ro_cells rsegs v SSP_GOT [C8 (wz SSP_GUARD)] ->
      stk rsegs v lo (bv_unsigned sp) -> lo + STDIO_WRITE_STACK <= bv_unsigned sp -> alloc_ceiling <= lo -> bv_unsigned sp <= 2^47 ->
      K [] ->
      (forall m' md', ainv A m' md' -> md_io md md' (m_fds md) ->
          file_at (aview A m') Fa (mf_set_w f (wz (mf_buf f)) (wz (mf_buf f)) (wz (mf_buf f + mf_bufsize f))) ->
          forall ms', (exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
              ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz (Z.of_nat (length s))) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                       F (ret_pc ra) fc None m' rom
              /\ munch [(bv_unsigned sp - STDIO_WRITE_STACK, bv_unsigned sp); (Fa, Fa + 152)] v (aview A m')
              /\ wmono rsegs v (aview A m') /\ mem_inv rsegs (aview A m') /\ stk rsegs (aview A m') lo (bv_unsigned sp)) ->
          srealizes rsegs (mkCfg ms' md') K) ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (wz STDIO_WRITE_ENTRY) fc None m rom) md)
                (t_emit (W (mf_fd f) (pend ++ s)) K).


  (* [comment removed for export] *)
  Definition stdio_write_zero_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (A : AS)
           (Fa : Z) (f : mfile) (lo : Z) (K : TSet),
      let v := aview A m in
      ainv A m md -> mem_inv rsegs v ->
      a0 = wz Fa -> a1 = wz 0 -> a2 = wz 0 ->
      file_at v Fa f -> (mf_fd f = 1 \/ mf_fd f = 2) ->
      0xaa000 <= Fa -> Fa + 152 <= SSP_GUARD -> img_client (L:=LPA) Fa (Fa + 152) ->
      fd_lookup (m_fds md) (wz (mf_fd f)) = Some (FdChannel (wz (mf_fd f))) ->
      mf_wbase f = wz (mf_buf f) -> mf_wpos f = wz (mf_buf f) ->
      0 <= mf_buf f -> mf_buf f + mf_bufsize f < 2^47 -> 0 <= mf_bufsize f ->
      (exists g, ro_cells rsegs v SSP_GUARD [C8 g]) -> ro_cells rsegs v SSP_GOT [C8 (wz SSP_GUARD)] ->
      stk rsegs v lo (bv_unsigned sp) -> lo + STDIO_WRITE_STACK <= bv_unsigned sp -> alloc_ceiling <= lo -> bv_unsigned sp <= 2^47 ->
      (forall m' md', ainv A m' md' -> md_io md md' (m_fds md) ->
          file_at (aview A m') Fa (mf_set_w f (wz (mf_buf f)) (wz (mf_buf f)) (wz (mf_buf f + mf_bufsize f))) ->
          forall ms', (exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
              ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                       F (ret_pc ra) fc None m' rom
              /\ munch [(bv_unsigned sp - STDIO_WRITE_STACK, bv_unsigned sp); (Fa, Fa + 152)] v (aview A m')
              /\ wmono rsegs v (aview A m') /\ mem_inv rsegs (aview A m') /\ stk rsegs (aview A m') lo (bv_unsigned sp)) ->
          srealizes rsegs (mkCfg ms' md') K) ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (wz STDIO_WRITE_ENTRY) fc None m rom) md) K.

  (* [comment removed for export] *)
  Definition fwritex_fit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (Fa : Z) (f : mfile) (pend s rest : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz (Z.of_nat (length s))) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' rom
      /\ munch [(bv_unsigned sp - FWRITEX_STACK, bv_unsigned sp); (Fa, Fa + 152);
                (mf_buf f + Z.of_nat (length pend), mf_buf f + Z.of_nat (length pend) + Z.of_nat (length s))] m m'
      /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
      /\ file_at m' Fa (mf_set_w f (wz (mf_buf f + Z.of_nat (length pend) + Z.of_nat (length s))) (wz (mf_buf f)) (wz (mf_buf f + mf_bufsize f)))
      /\ bytes_at rsegs m' (mf_buf f) (pend ++ s)
      /\ rw_cells rsegs m' (mf_buf f + Z.of_nat (length pend) + Z.of_nat (length s)) [CB (length rest - length s)%nat (skipn (length s) rest)].
  Definition fwritex_fit_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fa : Z) (f : mfile) (pend s rest : list byte) (sa lo : Z),
      let wp := mf_buf f + Z.of_nat (length pend) in let l := Z.of_nat (length s) in
      a0 = wz sa -> a1 = wz l -> a2 = wz Fa ->
      file_at m Fa f -> mf_wbase f = wz (mf_buf f) -> mf_wpos f = wz wp -> mf_wend f = wz (mf_buf f + mf_bufsize f) ->
      0 < mf_buf f -> mf_buf f + mf_bufsize f < 2^47 -> 0 <= mf_bufsize f < 2^31 -> -2^31 <= mf_lbf f < 2^31 ->
      (mf_lbf f < 0 \/ ~ In (Z_to_bv 8 10) s) ->
      Z.of_nat (length pend) + l <= mf_bufsize f -> Z.of_nat (length pend) + Z.of_nat (length rest) = mf_bufsize f ->
      bytes_at rsegs m (mf_buf f) pend -> rw_cells rsegs m wp [CB (length rest) rest] -> bytes_at rsegs m sa s ->
      0 <= sa -> sa + l < 2^47 ->
      mem_inv rsegs m -> memcpy_icpt_cells m ->
      stk rsegs m lo (bv_unsigned sp) -> lo + FWRITEX_STACK <= bv_unsigned sp -> alloc_ceiling <= lo ->
      0xaa000 <= Fa -> Fa + 152 <= 0x60a000 ->
      (Fa + 152 <= mf_buf f \/ mf_buf f + mf_bufsize f <= Fa) ->            (* [comment removed for export] *)
      (mf_buf f + mf_bufsize f <= lo \/ bv_unsigned sp <= mf_buf f) ->     (* [comment removed for export] *)
      (sa + l <= lo \/ bv_unsigned sp <= sa) ->                            (* [comment removed for export] *)
      (sa + l <= wp \/ wp + l <= sa) ->                                    (* [comment removed for export] *)
      (l = 0 \/ (range_ok m sa l /\ range_ok m wp l)) ->
      evt rsegs (fwritex_fit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fa f pend s rest lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz FWRITEX_ENTRY) fc None m rom).


  (* [comment removed for export] *)
  Definition fwritex_flush_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (A : AS)
           (Fa : Z) (f : mfile) (pend s : list byte) (sa : Z) (lo : Z) (K : TSet),
      let v := aview A m in let wp := mf_buf f + Z.of_nat (length pend) in let l := Z.of_nat (length s) in
      ainv A m md -> mem_inv rsegs v ->
      a0 = wz sa -> a1 = wz l -> a2 = wz Fa ->
      file_at v Fa f -> (mf_fd f = 1 \/ mf_fd f = 2) -> mf_write f = STDIO_WRITE ->
      mf_wbase f = wz (mf_buf f) -> mf_wpos f = wz wp -> mf_wend f = wz (mf_buf f + mf_bufsize f) ->
      0 < mf_buf f -> mf_buf f + mf_bufsize f < 2^47 -> 0 <= mf_bufsize f ->
      mf_bufsize f - Z.of_nat (length pend) < l -> Z.of_nat (length pend) <= mf_bufsize f -> Z.of_nat (length pend) + l <= 2^26 ->
      0xaa000 <= Fa -> Fa + 152 <= SSP_GUARD -> img_client (L:=LPA) Fa (Fa + 152) ->
      fd_lookup (m_fds md) (wz (mf_fd f)) = Some (FdChannel (wz (mf_fd f))) ->
      bytes_at rsegs v (mf_buf f) pend -> bytes_at rsegs v sa s ->
      0 <= sa -> sa + l < 2^47 ->
      (mf_buf f + Z.of_nat (length pend) <= bv_unsigned sp - FWRITEX_STACK \/ bv_unsigned sp <= mf_buf f) ->
      (sa + l <= bv_unsigned sp - FWRITEX_STACK \/ bv_unsigned sp <= sa) ->
      (exists g, ro_cells rsegs v SSP_GUARD [C8 g]) -> ro_cells rsegs v SSP_GOT [C8 (wz SSP_GUARD)] ->
      stk rsegs v lo (bv_unsigned sp) -> lo + FWRITEX_STACK <= bv_unsigned sp -> alloc_ceiling <= lo -> bv_unsigned sp <= 2^47 ->
      K [] ->
      (forall m' md', ainv A m' md' -> md_io md md' (m_fds md) ->
          file_at (aview A m') Fa (mf_set_w f (wz (mf_buf f)) (wz (mf_buf f)) (wz (mf_buf f + mf_bufsize f))) ->
          forall ms', (exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
              ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz l) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                       F (ret_pc ra) fc None m' rom
              /\ munch [(bv_unsigned sp - FWRITEX_STACK, bv_unsigned sp); (Fa, Fa + 152)] v (aview A m')
              /\ wmono rsegs v (aview A m') /\ mem_inv rsegs (aview A m') /\ stk rsegs (aview A m') lo (bv_unsigned sp)) ->
          srealizes rsegs (mkCfg ms' md') K) ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (wz FWRITEX_ENTRY) fc None m rom) md)
                (t_emit (W (mf_fd f) (pend ++ s)) K).

  (* [comment removed for export] *)
  Definition fwritex_nl_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (A : AS)
           (f : mfile) (pend bj : list byte) (sa : Z) (lo : Z) (K : TSet),
      let v := aview A m in
      ainv A m md -> mem_inv rsegs v ->
      a0 = wz sa -> a1 = wz 1 -> a2 = wz STDOUT_F ->
      file_at v STDOUT_F f -> mf_fd f = 1 -> mf_flags f = 5 -> mf_buf f = STDOUT_BUF -> mf_bufsize f = 1024 ->
      mf_write f = STDOUT_WRITE -> 0 <= mf_lbf f < 2^31 ->
      mf_wbase f = wz STDOUT_BUF -> mf_wpos f = wz (STDOUT_BUF + Z.of_nat (length pend)) -> mf_wend f = wz (STDOUT_BUF + 1024) ->
      (length pend + 1 <= 1024)%nat ->
      fd_lookup (m_fds md) (wz 1) = Some (FdChannel (wz 1)) ->
      rw_cells rsegs v STDOUT_BUF [CB 1024 bj] -> firstn (length pend) bj = pend ->
      bytes_at rsegs v sa [Z_to_bv 8 10] -> 0 <= sa -> sa + 1 < 2^47 ->
      (sa + 1 <= lo \/ bv_unsigned sp <= sa) -> (sa + 1 <= STDOUT_F \/ STDOUT_F + 152 <= sa) ->
      memcpy_icpt_cells v ->
      (exists g, ro_cells rsegs v SSP_GUARD [C8 g]) -> ro_cells rsegs v SSP_GOT [C8 (wz SSP_GUARD)] ->
      stk rsegs v lo (bv_unsigned sp) -> lo + FWRITEX_STACK <= bv_unsigned sp -> alloc_ceiling <= lo -> bv_unsigned sp <= 2^47 ->
      K [] ->
      (forall m' md', ainv A m' md' -> md_io md md' (m_fds md) ->
          file_at (aview A m') STDOUT_F (mf_set_write_lbf (mf_set_w f (wz STDOUT_BUF) (wz STDOUT_BUF) (wz (STDOUT_BUF + 1024))) STDIO_WRITE (-1)) ->
          (exists bj', rw_cells rsegs (aview A m') STDOUT_BUF [CB 1024 bj']) ->
          forall ms', (exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
              ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                       F (ret_pc ra) fc None m' rom
              /\ munch [(bv_unsigned sp - FWRITEX_STACK, bv_unsigned sp); (STDOUT_F, STDOUT_F + 152); (STDOUT_BUF, STDOUT_BUF + 0)] v (aview A m')
              /\ wmono rsegs v (aview A m') /\ mem_inv rsegs (aview A m') /\ stk rsegs (aview A m') lo (bv_unsigned sp)) ->
          srealizes rsegs (mkCfg ms' md') K) ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (wz FWRITEX_ENTRY) fc None m rom) md)
                (t_emit (W 1 (pend ++ [Z_to_bv 8 10])) K).

  (* [comment removed for export] *)
  Definition stdout_write_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (A : AS)
           (f : mfile) (pend s : list byte) (sa : Z) (lo : Z) (K : TSet),
      let v := aview A m in
      ainv A m md -> mem_inv rsegs v ->
      a0 = wz STDOUT_F -> a1 = wz sa -> a2 = wz (Z.of_nat (length s)) ->
      file_at v STDOUT_F f -> mf_fd f = 1 -> mf_flags f = 5 -> mf_buf f = STDOUT_BUF -> mf_bufsize f = 1024 ->
      fd_lookup (m_fds md) (wz 1) = Some (FdChannel (wz 1)) ->
      mf_wbase f = wz STDOUT_BUF -> mf_wpos f = wz (STDOUT_BUF + Z.of_nat (length pend)) ->
      bytes_at rsegs v STDOUT_BUF pend -> bytes_at rsegs v sa s ->
      (1 <= length pend + length s)%nat -> (length pend <= 1024)%nat -> Z.of_nat (length s) <= 2^25 ->
      0 <= sa -> sa + Z.of_nat (length s) < 2^47 ->
      (sa + Z.of_nat (length s) <= bv_unsigned sp - STDOUT_WRITE_STACK \/ bv_unsigned sp <= sa) ->
      (sa + Z.of_nat (length s) <= STDOUT_F \/ STDOUT_F + 152 <= sa) ->
      (exists g, ro_cells rsegs v SSP_GUARD [C8 g]) -> ro_cells rsegs v SSP_GOT [C8 (wz SSP_GUARD)] ->
      stk rsegs v lo (bv_unsigned sp) -> lo + STDOUT_WRITE_STACK <= bv_unsigned sp -> alloc_ceiling <= lo -> bv_unsigned sp <= 2^47 ->
      K [] ->
      (forall m' md', ainv A m' md' -> md_io md md' (m_fds md) ->
          file_at (aview A m') STDOUT_F (mf_set_write_lbf (mf_set_w f (wz STDOUT_BUF) (wz STDOUT_BUF) (wz (STDOUT_BUF + 1024))) STDIO_WRITE (-1)) ->
          forall ms', (exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
              ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz (Z.of_nat (length s))) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                       F (ret_pc ra) fc None m' rom
              /\ munch [(bv_unsigned sp - STDOUT_WRITE_STACK, bv_unsigned sp); (STDOUT_F, STDOUT_F + 152)] v (aview A m')
              /\ wmono rsegs v (aview A m') /\ mem_inv rsegs (aview A m') /\ stk rsegs (aview A m') lo (bv_unsigned sp)) ->
          srealizes rsegs (mkCfg ms' md') K) ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (wz STDOUT_WRITE_ENTRY) fc None m rom) md)
                (t_emit (W 1 (pend ++ s)) K).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition fwrite_icpt_cells (v : word -> option byte) : Prop :=
       asan_inited_cell v /\ ro_cells rsegs v REAL_FWRITE_CELL [C8 (wz MUSL_FWRITE)] /\ map_cells v
    /\ (exists g, ro_cells rsegs v SSP_GUARD [C8 g]) /\ ro_cells rsegs v SSP_GOT [C8 (wz SSP_GUARD)].

  (* [comment removed for export] *)
  Definition stderr_ok (f : mfile) : Prop :=
    exists w mo, f = mf_set_mode (mf_set_w stderr0 w w w) mo /\ (w = w0 \/ w = wz STDERR_BUFP).

  (* [comment removed for export] *)
  Definition fwrite_diag_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (A : AS)
           (msg : list byte) (pa : Z) (fe : mfile) (lo : Z) (K : TSet),
      let v := aview A m in
      ainv A m md -> mem_inv rsegs v -> fwrite_icpt_cells v ->
      a0 = wz pa -> a1 = wz (Z.of_nat (length msg)) -> a2 = wz 1 -> a3 = wz STDERR_F ->
      (1 <= length msg <= 64)%nat -> 0x10000 <= pa -> pa + Z.of_nat (length msg) <= 0x35000 (* [comment removed for export] *) ->
      bytes_at rsegs v pa msg -> (forall v', consts_hold LPA v' -> range_ok v' pa (Z.of_nat (length msg))) ->
      file_at v STDERR_F fe -> stderr_ok fe ->
      fd_lookup (m_fds md) (wz 2) = Some (FdChannel (wz 2)) ->
      stk rsegs v lo (bv_unsigned sp) -> lo + FWRITE_ICPT_STACK <= bv_unsigned sp -> alloc_ceiling <= lo -> bv_unsigned sp <= 2^47 -> K [] ->
      (forall m' md' fe', ainv A m' md' -> md_io md md' (m_fds md) -> stderr_ok fe' -> file_at (aview A m') STDERR_F fe' ->
          forall ms', (exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
              ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                       F (ret_pc ra) fc None m' rom
              /\ munch [(bv_unsigned sp - FWRITE_ICPT_STACK, bv_unsigned sp); (STDERR_F, STDERR_F + 152)] v (aview A m')
              /\ wmono rsegs v (aview A m') /\ mem_inv rsegs (aview A m') /\ stk rsegs (aview A m') lo (bv_unsigned sp)) ->
          srealizes rsegs (mkCfg ms' md') K) ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (wz FWRITE_ICPT_ENTRY) fc None m rom) md)
                (t_emit (W 2 msg) K).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Inductive diag_fmt := DF_usage | DF_cannot_open | DF_read_error | DF_refused.
  Definition diag_fmt_addr (d : diag_fmt) : Z :=
    match d with DF_usage => 0x15abe | DF_cannot_open => 0x1de96 | DF_read_error => 0x1deab | DF_refused => 0x19c98 end.
  Definition diag_msg (d : diag_fmt) (arg : list byte) : list byte :=
    match d with DF_usage => msg_usage arg | DF_cannot_open => msg_cannot_open arg | DF_read_error => msg_read_error arg
               | DF_refused => msg_refused end.

  Definition fprintf_diag_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (A : AS)
           (d : diag_fmt) (arg slack : list byte) (pa : Z) (fe : mfile) (lo : Z) (K : TSet),
      let v := aview A m in
      ainv A m md -> mem_inv rsegs v -> tp = cl_tp LPA ->   (* [comment removed for export] *)
      a0 = wz STDERR_F -> a1 = wz (diag_fmt_addr d) ->
      match d with DF_refused => a2 = wz 67108864 /\ arg = []
                 | _ => a2 = wz pa /\ bytes_at rsegs v pa (arg ++ Z_to_bv 8 0 :: slack) /\ ~ In (Z_to_bv 8 0) arg
                        /\ alloc_ceiling <= pa /\ pa + Z.of_nat (length arg) + 1 + Z.of_nat (length slack) <= 2^47 /\ 16 <= Z.of_nat (length slack) (* [comment removed for export] *)
                        /\ bv_unsigned sp <= pa (* [comment removed for export] *)
                        /\ (- (pa + Z.of_nat (length arg) + 1)) mod 8 <= Z.of_nat (length slack) (* [comment removed for export] *) end ->
      (Z.of_nat (length arg) <= 131072) ->
      bytes_at rsegs v (sh alloc_ceiling) (zeros (Z.to_nat ((2^47 - alloc_ceiling) / 8))) ->
      file_at v STDERR_F fe -> stderr_ok fe -> (exists j8, rw_cells rsegs v STDERR_BUFP [CB 8 j8]) ->
      fd_lookup (m_fds md) (wz 2) = Some (FdChannel (wz 2)) ->
      (exists g, ro_cells rsegs v SSP_GUARD [C8 g]) -> ro_cells rsegs v SSP_GOT [C8 (wz SSP_GUARD)] ->   (* [comment removed for export] *)
      stk rsegs v lo (bv_unsigned sp) -> lo + FPRINTF_ICPT_STACK <= bv_unsigned sp -> alloc_ceiling <= lo ->
      bv_unsigned sp mod 16 = 0 ->
      bv_unsigned sp <= 2^47 ->   (* [comment removed for export] *)
      K [] ->
      (forall m' md' fe' (r : word), ainv A m' md' -> md_io md md' (m_fds md) -> stderr_ok fe' -> file_at (aview A m') STDERR_F fe' ->
          forall ms', (exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
              ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                       F (ret_pc ra) fc None m' rom
              /\ munch [(bv_unsigned sp - FPRINTF_ICPT_STACK, bv_unsigned sp); (STDERR_F, STDERR_F + 152); (STDERR_BUFP, STDERR_BUFP + 8)] v (aview A m')
              /\ wmono rsegs v (aview A m') /\ mem_inv rsegs (aview A m') /\ stk rsegs (aview A m') lo (bv_unsigned sp)) ->
          srealizes rsegs (mkCfg ms' md') K) ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (wz FPRINTF_ICPT_ENTRY) fc None m rom) md)
                (t_emit (W 2 (diag_msg d arg)) K).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition FMT_D : Z := 0x149ba.  (* [comment removed for export] *)
  Definition vprintf_first_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (A : AS) (va : Z) (lo : Z) (K : TSet),
      let v := aview A m in
      ainv A m md -> mem_inv rsegs v -> tp = cl_tp LPA ->
      a0 = wz FMT_D -> a1 = wz va -> bytes_at rsegs v va (le8 (wz 0)) -> alloc_ceiling <= va -> va + 8 < 2^47 ->
      bv_unsigned sp <= va ->                                                   (* [comment removed for export] *)
      (forall v', consts_hold LPA v' -> range_ok v' FMT_D 4 /\ range_ok v' STDOUT_BUF 1024) ->   (* [comment removed for export] *)
      bytes_at rsegs v (sh alloc_ceiling) (zeros (Z.to_nat ((2^47 - alloc_ceiling) / 8))) ->
      stdout_at v SO_pristine -> fd_lookup (m_fds md) (wz 1) = Some (FdChannel (wz 1)) ->
      (exists g, ro_cells rsegs v SSP_GUARD [C8 g]) -> ro_cells rsegs v SSP_GOT [C8 (wz SSP_GUARD)] ->
      stk rsegs v lo (bv_unsigned sp) -> lo + VPRINTF_ICPT_STACK <= bv_unsigned sp -> alloc_ceiling <= lo -> bv_unsigned sp mod 16 = 0 ->
      K [] ->
      (forall m' md' (r : word), ainv A m' md' -> md_io md md' (m_fds md) -> stdout_at (aview A m') (SO_buffered []) ->
          forall ms', (exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
              ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                       F (ret_pc ra) fc None m' rom
              /\ munch [(bv_unsigned sp - VPRINTF_ICPT_STACK, bv_unsigned sp); (STDOUT_F, STDOUT_F + 152); (STDOUT_BUF, STDOUT_BUF + 1024)] v (aview A m')
              /\ wmono rsegs v (aview A m') /\ mem_inv rsegs (aview A m') /\ stk rsegs (aview A m') lo (bv_unsigned sp)) ->
          srealizes rsegs (mkCfg ms' md') K) ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (wz VPRINTF_ICPT_ENTRY) fc None m rom) md)
                (t_emit (W 1 [Z_to_bv 8 48; Z_to_bv 8 10]) K).

  Definition vprintf_next_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (A : AS) (va : Z) (p : list byte) (lo : Z) (K : TSet),
      let v := aview A m in
      ainv A m md -> mem_inv rsegs v -> tp = cl_tp LPA ->
      a0 = wz FMT_D -> a1 = wz va -> bytes_at rsegs v va (le8 (wz 0)) -> alloc_ceiling <= va -> va + 8 < 2^47 ->
      bv_unsigned sp <= va ->                                                   (* [comment removed for export] *)
      (forall v', consts_hold LPA v' -> range_ok v' FMT_D 4 /\ range_ok v' STDOUT_BUF 1024) ->   (* [comment removed for export] *)
      bytes_at rsegs v (sh alloc_ceiling) (zeros (Z.to_nat ((2^47 - alloc_ceiling) / 8))) ->
      stdout_at v (SO_buffered p) -> (length p <= 6)%nat ->
      (exists g, ro_cells rsegs v SSP_GUARD [C8 g]) -> ro_cells rsegs v SSP_GOT [C8 (wz SSP_GUARD)] ->
      stk rsegs v lo (bv_unsigned sp) -> lo + VPRINTF_ICPT_STACK <= bv_unsigned sp -> alloc_ceiling <= lo -> bv_unsigned sp mod 16 = 0 ->
      (forall m' md' (r : word), ainv A m' md' -> md_io md md' (m_fds md) ->
          stdout_at (aview A m') (SO_buffered (p ++ [Z_to_bv 8 48; Z_to_bv 8 10])) ->
          forall ms', (exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
              ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                       F (ret_pc ra) fc None m' rom
              /\ munch [(bv_unsigned sp - VPRINTF_ICPT_STACK, bv_unsigned sp); (STDOUT_F, STDOUT_F + 152); (STDOUT_BUF, STDOUT_BUF + 1024)] v (aview A m')
              /\ wmono rsegs v (aview A m') /\ mem_inv rsegs (aview A m') /\ stk rsegs (aview A m') lo (bv_unsigned sp)) ->
          srealizes rsegs (mkCfg ms' md') K) ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (wz VPRINTF_ICPT_ENTRY) fc None m rom) md) K.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
End S.
