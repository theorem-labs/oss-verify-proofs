(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1d7 X1cx X1cy X1cp X1cj X1dd X1cg X1cm X1cs X1d0 X1da X1d1.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require Import X1rw X1rn X1s9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X00a.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r9.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r9.
Import ListNotations.
Open Scope Z_scope.

Section FRM.
Variable RT : rt_sig.

Definition malloc_contract_okF : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (n lo : Z),
fdfs_only PMc -> mat_stable PMc ->
1 <= n <= 0x4000000 -> a0 = Z_to_bv 64 n -> tp = Z_to_bv 64 0x638c98 ->
Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost n <= rt_credit RT Σ ->
ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo -> unwind_ok ra s0 sp ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_malloc m)))
(malloc_postF RT Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 n lo m).
Lemma malloc_contract_okF_of : malloc_contract RT -> malloc_contract_okF.
Proof. intros H. unfold malloc_contract_okF. intros. eapply H; try eassumption. apply unwind_ok_ch; assumption. Qed.

Definition free_contract_okF : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (p n lo : Z),
fdfs_only PMc -> mat_stable PMc ->
In (p, n) (rt_live RT Σ) -> a0 = Z_to_bv 64 p -> tp = Z_to_bv 64 0x638c98 ->
ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo -> unwind_ok ra s0 sp ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_free m)))
(free_postF RT Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p lo m).
Lemma free_contract_okF_of : free_contract RT -> free_contract_okF.
Proof. intros H. unfold free_contract_okF. intros. eapply H; try eassumption. apply unwind_ok_ch; assumption. Qed.

Lemma malloc_contract_ok_of_okF : malloc_contract_okF -> malloc_contract_ok RT.
Proof.
intros H. unfold malloc_contract_ok. intros. eapply cps_post; [eapply H; eassumption |].
intros c0 Hc0. eapply malloc_postF_w. exact Hc0.
Qed.
Lemma free_contract_ok_of_okF : free_contract_okF -> free_contract_ok RT.
Proof.
intros H. unfold free_contract_ok. intros. eapply cps_post; [eapply H; eassumption |].
intros c0 Hc0. eapply free_postF_w. exact Hc0.
Qed.

Definition read_icontract_fileF : Prop :=
forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (fd buf count : Z) p off data (lo : Z),
a0 = Z_to_bv 64 fd -> a1 = Z_to_bv 64 buf -> a2 = Z_to_bv 64 count ->
buf = g_read_stage ->
3 <= fd < 2^32 -> 0 < count <= 65536 -> 0 < buf -> buf + count <= SEGTOP_A -> checked_dst RT Σ m sp buf count ->
fd_lookup F0 (Z_to_bv 64 fd) = Some (FdFile p off) -> fs_lookup fs0 p = Some data ->
ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
let bs := file_read data off (Z_to_bv 64 count) in
cps bsegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
s10 s11 t3 t4 t5 t6 F fc e_read m)))
(ASTA RT Σ (PMfd (fd_insert F0 (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) fs0)
(fun ms => exists m', ret_stF F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (len_word bs) m' ms
/\ rt_after RT Σ (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(buf, buf + Z.of_nat (length bs))] m m'
/\ bytes_at bsegs m' buf bs)).

Definition open_contractF : Prop :=
forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (path : Z) (s : list byte) (lo : Z) ent,
a0 = Z_to_bv 64 path -> a1 = Z_to_bv 64 0 ->
bytes_at bsegs m path (s ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) s ->
path_has_slash s = false -> path_eqb s dotdot_path = false ->
open_ent s fs0 = Some ent -> fd_lookup F0 (alloc_fd F0) = None ->
stk bsegs m lo (bv_unsigned sp) -> lo + 128 <= bv_unsigned sp -> rt_sp0 RT Σ - STACK_WIN <= lo ->
rw_cells bsegs m (errno_cell tp) [C4 (Z_to_bv 64 0)] \/ (exists v, rw_cells bsegs m (errno_cell tp) [C4 v]) ->
ssp_cells m -> ART RT Σ m -> mem_inv bsegs m ->
tp = Z_to_bv 64 0x638c98 -> (path + Z.of_nat (length s) + 1 <= lo \/ bv_unsigned sp <= path) ->
cps2 bsegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
s10 s11 t3 t4 t5 t6 F fc e_open m)))
(fun c => exists (e : Z) m', In e openat_errnos /\
ASTA RT Σ (PMfd F0 fs0) (fun ms => ret_stF F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (-1)) m' ms
/\ musl_after RT Σ (bv_unsigned sp) lo [(errno_cell tp, errno_cell tp + 4)] m m'
/\ rw_cells bsegs m' (errno_cell tp) [C4 (Z_to_bv 64 e)]) c)
(fun c => exists m',
ASTA RT Σ (PMfd (fd_insert F0 (alloc_fd F0) ent) fs0)
(fun ms => ret_stF F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (alloc_fd F0) m' ms
/\ musl_after RT Σ (bv_unsigned sp) lo [] m m') c).

Definition close_contractF : Prop :=
forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (fd lo : Z),
a0 = Z_to_bv 64 fd -> 3 <= fd < 2^31 -> fd_lookup F0 (Z_to_bv 64 fd) <> None ->
stk bsegs m lo (bv_unsigned sp) -> lo + 128 <= bv_unsigned sp -> rt_sp0 RT Σ - STACK_WIN <= lo ->
ART RT Σ m -> mem_inv bsegs m ->
cps bsegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
s10 s11 t3 t4 t5 t6 F fc e_close m)))
(fun c => exists m', ASTA RT Σ (PMfd (fd_remove F0 (Z_to_bv 64 fd)) fs0)
(fun ms => ret_stF F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
/\ musl_after RT Σ (bv_unsigned sp) lo [] m m') c).

Section IO.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).

Definition vprintf_emit0_icontractR : Prop :=
forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (so : stdout_st) (ap : Z) (lo : Z),
a0 = Z_to_bv 64 FMT_emit -> a1 = Z_to_bv 64 ap ->
rw_cells bsegs m ap [C8 (Z_to_bv 64 0)] ->
ap = bv_unsigned sp + 24 ->
(so = stdout_init \/ exists k, (k < 500)%nat /\ so = so_lines k) ->
fd_lookup F0 (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
OUT_rep so m -> io_ssp m ->
ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo -> pois_above (rt_pois RT Σ) (bv_unsigned sp) ->
cpsE bsegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
s10 s11 t3 t4 t5 t6 F fc e_vprintf m)))
(evw 1 (emit0_out so))
(ASTA RT Σ (PMfd F0 fs0)
(fun ms => exists v m', ret_stR fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after RT Σ (bv_unsigned sp) lo m m' /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) IO_FP m m'
/\ OUT_rep (emit0_next so) m' /\ (ERR_rep m -> ERR_rep m'))).
End IO.
End FRM.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.

Section FRM.
Variable RT : rt_sig.

Definition malloc_contract_okF : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (n lo : Z),
fdfs_only PMc -> mat_stable PMc ->
1 <= n <= 0x4000000 -> a0 = Z_to_bv 64 n -> tp = Z_to_bv 64 0x630458 ->
Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost n <= rt_credit RT Σ ->
ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> unwind_ok ra s0 sp ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_malloc m)))
(malloc_postF RT Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 n lo m).
Lemma malloc_contract_okF_of : malloc_contract RT -> malloc_contract_okF.
Proof. intros H. unfold malloc_contract_okF. intros. eapply H; try eassumption. apply unwind_ok_ch; assumption. Qed.

Definition free_contract_okF : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (p n lo : Z),
fdfs_only PMc -> mat_stable PMc ->
In (p, n) (rt_live RT Σ) -> a0 = Z_to_bv 64 p -> tp = Z_to_bv 64 0x630458 ->
ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> unwind_ok ra s0 sp ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_free m)))
(free_postF RT Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p lo m).
Lemma free_contract_okF_of : free_contract RT -> free_contract_okF.
Proof. intros H. unfold free_contract_okF. intros. eapply H; try eassumption. apply unwind_ok_ch; assumption. Qed.

Lemma malloc_contract_ok_of_okF : malloc_contract_okF -> malloc_contract_ok RT.
Proof.
intros H. unfold malloc_contract_ok. intros. eapply cps_post; [eapply H; eassumption |].
intros c0 Hc0. eapply malloc_postF_w. exact Hc0.
Qed.
Lemma free_contract_ok_of_okF : free_contract_okF -> free_contract_ok RT.
Proof.
intros H. unfold free_contract_ok. intros. eapply cps_post; [eapply H; eassumption |].
intros c0 Hc0. eapply free_postF_w. exact Hc0.
Qed.

Definition read_icontract_fileF : Prop :=
forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (fd buf count : Z) p off data (lo : Z),
a0 = Z_to_bv 64 fd -> a1 = Z_to_bv 64 buf -> a2 = Z_to_bv 64 count ->
buf = g_read_stage ->
3 <= fd < 2^32 -> 0 < count <= 65536 -> 0 < buf -> buf + count <= SEGTOP_A -> checked_dst RT Σ m sp buf count ->
fd_lookup F0 (Z_to_bv 64 fd) = Some (FdFile p off) -> fs_lookup fs0 p = Some data ->
ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
let bs := file_read data off (Z_to_bv 64 count) in
cps asegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
s10 s11 t3 t4 t5 t6 F fc e_read m)))
(ASTA RT Σ (PMfd (fd_insert F0 (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) fs0)
(fun ms => exists m', ret_stF F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (len_word bs) m' ms
/\ rt_after RT Σ (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(buf, buf + Z.of_nat (length bs))] m m'
/\ bytes_at asegs m' buf bs)).

Definition open_contractF : Prop :=
forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (path : Z) (s : list byte) (lo : Z) ent,
a0 = Z_to_bv 64 path -> a1 = Z_to_bv 64 0 ->
bytes_at asegs m path (s ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) s ->
path_has_slash s = false -> path_eqb s dotdot_path = false ->
open_ent s fs0 = Some ent -> fd_lookup F0 (alloc_fd F0) = None ->
stk asegs m lo (bv_unsigned sp) -> lo + 128 <= bv_unsigned sp -> rt_sp0 RT Σ - STACK_WIN <= lo ->
rw_cells asegs m (errno_cell tp) [C4 (Z_to_bv 64 0)] \/ (exists v, rw_cells asegs m (errno_cell tp) [C4 v]) ->
ssp_cells m -> ART RT Σ m -> mem_inv asegs m ->
tp = Z_to_bv 64 0x630458 -> (path + Z.of_nat (length s) + 1 <= lo \/ bv_unsigned sp <= path) ->
cps2 asegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
s10 s11 t3 t4 t5 t6 F fc e_open m)))
(fun c => exists (e : Z) m', In e openat_errnos /\
ASTA RT Σ (PMfd F0 fs0) (fun ms => ret_stF F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (-1)) m' ms
/\ musl_after RT Σ (bv_unsigned sp) lo [(errno_cell tp, errno_cell tp + 4)] m m'
/\ rw_cells asegs m' (errno_cell tp) [C4 (Z_to_bv 64 e)]) c)
(fun c => exists m',
ASTA RT Σ (PMfd (fd_insert F0 (alloc_fd F0) ent) fs0)
(fun ms => ret_stF F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (alloc_fd F0) m' ms
/\ musl_after RT Σ (bv_unsigned sp) lo [] m m') c).

Definition close_contractF : Prop :=
forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (fd lo : Z),
a0 = Z_to_bv 64 fd -> 3 <= fd < 2^31 -> fd_lookup F0 (Z_to_bv 64 fd) <> None ->
stk asegs m lo (bv_unsigned sp) -> lo + 128 <= bv_unsigned sp -> rt_sp0 RT Σ - STACK_WIN <= lo ->
ART RT Σ m -> mem_inv asegs m ->
cps asegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
s10 s11 t3 t4 t5 t6 F fc e_close m)))
(fun c => exists m', ASTA RT Σ (PMfd (fd_remove F0 (Z_to_bv 64 fd)) fs0)
(fun ms => ret_stF F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
/\ musl_after RT Σ (bv_unsigned sp) lo [] m m') c).

Section IO.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).

Definition vprintf_emit0_icontractR : Prop :=
forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (so : stdout_st) (ap : Z) (lo : Z),
a0 = Z_to_bv 64 FMT_emit -> a1 = Z_to_bv 64 ap ->
rw_cells asegs m ap [C8 (Z_to_bv 64 0)] ->
ap = bv_unsigned sp + 24 ->
(so = stdout_init \/ exists k, (k < 500)%nat /\ so = so_lines k) ->
fd_lookup F0 (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
OUT_rep so m -> io_ssp m ->
ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> pois_above (rt_pois RT Σ) (bv_unsigned sp) ->
cpsE asegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
s10 s11 t3 t4 t5 t6 F fc e_vprintf m)))
(evw 1 (emit0_out so))
(ASTA RT Σ (PMfd F0 fs0)
(fun ms => exists v m', ret_stR fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after RT Σ (bv_unsigned sp) lo m m' /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) IO_FP m m'
/\ OUT_rep (emit0_next so) m' /\ (ERR_rep m -> ERR_rep m'))).
End IO.
End FRM.
