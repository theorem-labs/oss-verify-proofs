(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1bk X1bs X1c2 X1bn X1cc X1c6.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1ri.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qv X0qx X0on.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ff X1nm X1nn.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope bv_scope.
Import X1bs.Exc.

Notation rsegs := X1ff.rsegs.

Definition file_cells (flags : word) (wend wpos wbase writefn buf bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
[C4 flags; C4 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 0x34f38);
C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 z64; C8 (Z_to_bv 64 wbase); C8 z64;
C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 0x350f4); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
C8 z64; C8 z64; C4 (Z_to_bv 64 fd); C4 z64; C8 z64; C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 z64;
CB 80 tail].

Notation RSTDOUT := 0x3d200%Z (only parsing).
Notation RSTDOUT_BUF := 0x6db20%Z (only parsing).
Notation RSTDERR := 0x3d110%Z (only parsing).
Notation F_STDOUT_WRITE := 0x350fc%Z (only parsing).
Notation F_STDIO_WRITE := 0x34f64%Z (only parsing).

Definition stdout_file (m : word -> option byte) (so : stdout_st) : Prop :=
exists (flags mode : word) (tail bufbytes : list byte),
rw_cells rsegs m RSTDOUT
(file_cells flags
(if so_active so then RSTDOUT_BUF + 1024 else 0)%Z
(if so_active so then RSTDOUT_BUF + zlength (so_buf so) else 0)%Z
(if so_active so then RSTDOUT_BUF else 0)%Z
(if so_first so then F_STDOUT_WRITE else F_STDIO_WRITE)
RSTDOUT_BUF 1024 1 mode
(if so_lbf_nl so then 10 else 0xffffffff)%Z tail)
/\ Z.land (bv_unsigned flags) 72 = 0%Z
/\ rw_cells rsegs m RSTDOUT_BUF [CB 1024 bufbytes]
/\ firstn (length (so_buf so)) bufbytes = to_bytes (so_buf so)
/\ (zlength (so_buf so) <= 1024)%Z
/\ (so_active so = false -> so_buf so = []).

Definition stderr_file (m : word -> option byte) : Prop :=
exists (flags mode : word) (e wend : Z) (tail : list byte),
rw_cells rsegs m RSTDERR (file_cells flags wend e e F_STDIO_WRITE 0x6db18 0 2 mode 0xffffffff tail).

Definition RATEXIT : Z := 0x6d490.
Definition RATEXIT_A0 : Z := 0x6d5b0.
Definition RATEXIT_CALL : Z := 0x31514.
Definition RAEF_INCB : Z := 0x4d354.
Definition RAEF_GUARD : Z := 0x1c0b0.
Definition RATEXIT_FN : Z := 0x31450.
Definition RFUNCS_ON_EXIT : Z := 0x31384.
Definition RCXA_FINALIZE : Z := 0x3144c.
Definition RDSO : Z := 0x3d0e8.

Definition ax_cells (fin slot head next f0 : Z) : list cell :=
[C1 (Z_to_bv 8 fin); CB 3 (repeat (Z_to_bv 8 0) 3); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 slot); CB 4 (repeat (Z_to_bv 8 0) 4);
C8 (Z_to_bv 64 head); C8 (Z_to_bv 64 next); C8 (Z_to_bv 64 f0)].

Definition AXSTAT (k : bool) (m : word -> option byte) : Prop :=
rw_cells rsegs m RAEF_INCB [C1 (Z_to_bv 8 0)]
/\ (if k then rw_cells rsegs m RATEXIT (ax_cells 0 1 (RATEXIT + 24) 0 RATEXIT_CALL) /\ rw_cells rsegs m RATEXIT_A0 [C8 (Z_to_bv 64 RAEF_GUARD)]
else rw_cells rsegs m RATEXIT (ax_cells 0 0 0 0 0) /\ rw_cells rsegs m RATEXIT_A0 [C8 (Z_to_bv 64 0)]).

Definition axstat_addr (a : Z) : Prop :=
(RAEF_INCB <= a < RAEF_INCB + 1)%Z \/ (RATEXIT <= a < RATEXIT + 40)%Z \/ (RATEXIT_A0 <= a < RATEXIT_A0 + 8)%Z.

Lemma AXSTAT_cells : forall k m,
AXSTAT k m <->
(rw_cells rsegs m RAEF_INCB [C1 (Z_to_bv 8 0)]
/\ rw_cells rsegs m RATEXIT (ax_cells 0 (if k then 1 else 0) (if k then RATEXIT + 24 else 0) 0 (if k then RATEXIT_CALL else 0))
/\ rw_cells rsegs m RATEXIT_A0 [C8 (Z_to_bv 64 (if k then RAEF_GUARD else 0))]).
Proof. intros [|] m; unfold AXSTAT; cbv beta iota; tauto. Qed.

Definition atexit_guard_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (RATEXIT, RATEXIT + 40); (RATEXIT_A0, RATEXIT_A0 + 8)]%Z m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ AXSTAT true m'.

Lemma atexit_guard_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (cdt thr sec : byte) (tm1 : word),
stk rsegs m lo (bv_unsigned sp) ->
rw_cells rsegs m 0x6d6d8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
AXSTAT false m ->
mem_inv rsegs m ->
a0 = Z_to_bv 64 RAEF_GUARD ->
(lo <= bv_unsigned sp - 48)%Z -> (0x6e000 <= lo)%Z ->
evt rsegs (atexit_guard_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RATEXIT_FN) fc None m (seg_rom rsegs)).
Proof.
intros until tm1. intros ST LCH [INCB [AX AX0]] MI -> LO LOLO.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
unfold RATEXIT, RATEXIT_A0, RAEF_INCB, RAEF_GUARD, RATEXIT_FN, ax_cells in *. cbn [Z.add] in *.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x6d490, 0x6d490 + 40); (0x6d5b0, 0x6d5b0 + 8)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
carve_frame 48%nat ST.
steps_to 0x314a0%Z.
replace (sx32 z64) with z64 by (vm_compute; reflexivity).
steps_to 0x31510%Z.
release_frame FR ST (bv_unsigned sp). astep.
apply evt_done. unfold atexit_guard_post. repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
unfold AXSTAT, RATEXIT, RATEXIT_A0, RAEF_INCB, RAEF_GUARD, RATEXIT_CALL, ax_cells. cbn [Z.add].
split; [hyp_by_addr|]. split; hyp_by_addr.
Qed.

Definition funcs_on_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (RATEXIT, RATEXIT + 40)]%Z m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp).

Lemma funcs_on_exit_spec : forall (k : bool) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (cdt thr sec : byte) (tm1 : word),
stk rsegs m lo (bv_unsigned sp) ->
rw_cells rsegs m 0x6d6d8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
AXSTAT k m ->
mem_inv rsegs m ->
(lo <= bv_unsigned sp - 48)%Z -> (0x6e000 <= lo)%Z ->
evt rsegs (funcs_on_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RFUNCS_ON_EXIT) fc None m (seg_rom rsegs)).
Proof.
intros until tm1. intros ST LCH [INCB AX2] MI LO LOLO.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
unfold RATEXIT, RATEXIT_A0, RAEF_INCB, RAEF_GUARD, RFUNCS_ON_EXIT, RATEXIT_CALL, ax_cells in *. cbn [Z.add] in *.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x6d490, 0x6d490 + 40)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
carve_frame 48%nat ST.
destruct k; destruct AX2 as [AX AX0].
-
steps_to 0x313bc%Z.
replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (vm_compute; reflexivity).
steps_to 0x31410%Z.
replace (sx32 z64) with z64 by (vm_compute; reflexivity).
steps_to 0x31448%Z.
release_frame FR ST (bv_unsigned sp). astep. astep. astep. astep.
apply evt_done. unfold funcs_on_exit_post. repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
-
steps_to 0x31448%Z.
release_frame FR ST (bv_unsigned sp). astep. astep. astep. astep.
apply evt_done. unfold funcs_on_exit_post. repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
Qed.

Section StdioExitStatement.
Context {RCEIL : RunCeiling}.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

Definition stdio_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (guard : word) (m : word -> option byte) (s : St) : unit -> St -> machine_state -> Prop :=
fun _ s' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 so' m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 160, bv_unsigned sp); (RSTDOUT, 0x3d2e8); (RSTDOUT_BUF, 0x6df20)]%Z m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ s' = set_so so' s
/\ stdout_file m' so' /\ so_buf so' = []
/\ stderr_file m'
/\ rw_cells rsegs m' 0x3c0d0 [C8 (Z_to_bv 64 0x6d6b8)] /\ rw_cells rsegs m' 0x6d6b8 [C8 guard].

Definition stdio_exit_spec_stmt : Prop :=
forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (s : St) (guard : word)
(cdt thr sec : byte) (tm1 : word),
stk rsegs m lo (bv_unsigned sp) ->
rw_cells rsegs m 0x6d6d8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
rw_cells rsegs m 0x6db08 [C8 z64] ->
rw_cells rsegs m 0x6daf8 [C8 z64] ->
rw_cells rsegs m 0x3d2e8 [C8 (Z_to_bv 64 RSTDOUT)] ->
rw_cells rsegs m 0x3d1f8 [C8 (Z_to_bv 64 RSTDERR)] ->
stdout_file m (get_so s) -> stderr_file m ->
rw_cells rsegs m 0x3c0d0 [C8 (Z_to_bv 64 0x6d6b8)] -> rw_cells rsegs m 0x6d6b8 [C8 guard] ->
mem_inv rsegs m ->
tp = Z_to_bv 64 RTP ->
(lo <= bv_unsigned sp - 160)%Z -> (0x6e000 <= lo)%Z ->
implM rsegs (stdout_exit_flush get_so set_so) s
(stdio_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m s)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x34b64) fc None m (seg_rom rsegs)).
End StdioExitStatement.

Definition rexit_prefix_post (sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo code t : Z) (td0 td1 td2 td3 ra : word) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR (Z_to_bv 64 0x315d4) (Z_to_bv 64 (bv_unsigned sp + -16)) gp (Z_to_bv 64 RTP) t0 t1 t2 (Z_to_bv 64 code) s1
a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x34b64) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (0x6d6b0, 0x6d6b4); (0x3d348, 0x3d349); (0x6d490, 0x6d4b8)]%Z m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp + -16)
/\ rw_cells rsegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra]
/\ rw_cells rsegs m' RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)]
/\ rw_cells rsegs m' 0x6d6b0 [C4 (Z_to_bv 64 t)]
/\ rw_cells rsegs m' 0x3d348 [C1 (Z_to_bv 8 1)].

Lemma rexit_prefix_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (code t : Z) (td0 td1 td2 td3 : word)
(cdt thr sec : byte) (tm1 : word) (k : bool),
stk rsegs m lo (bv_unsigned sp) ->
rw_cells rsegs m RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)] ->
rw_cells rsegs m 0x6d6b0 [C4 z64] ->
rw_cells rsegs m 0x3c0d8 [C8 (Z_to_bv 64 0x3b6f8); C8 (Z_to_bv 64 0x3b6f0)] ->
rw_cells rsegs m 0x3b6f0 [C8 (Z_to_bv 64 0x1bbf8)] ->
rw_cells rsegs m 0x3d348 [C1 (Z_to_bv 8 0)] ->
rw_cells rsegs m 0x3c010 [C8 (Z_to_bv 64 RCXA_FINALIZE); C8 z64] ->
mem_inv rsegs m ->
tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code ->
(0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - 64)%Z -> (0x6e000 <= lo)%Z ->
rw_cells rsegs m 0x6d6d8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
AXSTAT k m ->
rw_cells rsegs m RDSO [C8 (Z_to_bv 64 RDSO)] ->
evt rsegs (rexit_prefix_post sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code t td0 td1 td2 td3 ra m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x31568) fc None m (seg_rom rsegs)).
Proof.
intros until k. intros ST TDa EXL GF FA FIN GCX MI -> -> Ht LO LOLO LCH AX DSO.
apply AXSTAT_cells in AX. destruct AX as (INCB & AX & AX0).
unfold RCXA_FINALIZE, RDSO, RAEF_INCB, RATEXIT, RATEXIT_A0, ax_cells in *. cbn [Z.add] in *.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (0x6d6b0, 0x6d6b4); (0x3d348, 0x3d349); (0x6d490, 0x6d4b8)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
carve_frame 16%nat ST.
do 6 lstep.
replace (sx32 (Z_to_bv 64 t)) with (Z_to_bv 64 t)
by (unfold sx32; f_equal; rewrite unsigned_lit by lia; symmetry; apply swrap32_small; lia).
lstep. lstep.

amo_step. replace (sx32 z64) with z64 by (vm_compute; reflexivity).
lstep. if_false. amo_step. lstep. if_false.
lstep. change (bv_swrap 32 (0 + 0)) with 0%Z.
lstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K. lstep. if_true.
lstep. lstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
assert (AX1 : AXSTAT k m1) by (apply AXSTAT_cells; unfold RAEF_INCB, RATEXIT, RATEXIT_A0, ax_cells; cbn [Z.add];
split; [exact INCB | split; [exact AX | exact AX0]]) end.
clear INCB AX AX0.
name_sp sp (-16)%Z.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
eapply evt_cut;
[ eapply (funcs_on_exit_spec k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo cdt thr sec tm1)
| cbv beta delta [funcs_on_exit_post RATEXIT]; cbn [Z.add]; post_call rsegs m1 ]
end.
all: unname_sp.
all: lazymatch goal with
| |- evt _ _ _ => idtac
| |- AXSTAT _ _ => exact AX1
| |- ?g => first [ hyp_by_addr | reflexivity | lia ]
end.
try clear AX1.
match goal with H : stk _ _ _ _ |- _ => rename H into ST end.
steps_to 0x3151c%Z.

carve_frame 32%nat ST. steps_to 0x1bbf8%Z.
carve_frame 16%nat ST. steps_to 0x1bc84%Z. release_frame FR1 ST (bv_unsigned sp + -48)%Z. astep.
steps_to 0x31564%Z. release_frame FR0 ST (bv_unsigned sp + -16)%Z. astep. astep.
astep.
unfold rexit_prefix_post. sys_finish.
Time Qed.

Section ExitProof.
Context {RCEIL : RunCeiling}.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

Hypothesis stdio_exit_spec : stdio_exit_spec_stmt get_so set_so.

#[using="stdio_exit_spec"] Lemma exit_spec : forall (s : St) (Q : Empty_set -> St -> machine_state -> Prop)
ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (code t : Z) (td0 td1 td2 td3 guard : word)
(cdt thr sec : byte) (tm1 : word) (k : bool),
stk rsegs m lo (bv_unsigned sp) ->
rw_cells rsegs m RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)] ->
rw_cells rsegs m 0x6d6b0 [C4 z64] ->
rw_cells rsegs m 0x3c0d8 [C8 (Z_to_bv 64 0x3b6f8); C8 (Z_to_bv 64 0x3b6f0)] ->
rw_cells rsegs m 0x3b6f0 [C8 (Z_to_bv 64 0x1bbf8)] ->
rw_cells rsegs m 0x3d348 [C1 (Z_to_bv 8 0)] ->
rw_cells rsegs m 0x3c010 [C8 (Z_to_bv 64 RCXA_FINALIZE); C8 z64] ->
rw_cells rsegs m 0x6d6d8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
rw_cells rsegs m 0x6db08 [C8 z64] -> rw_cells rsegs m 0x6daf8 [C8 z64] ->
rw_cells rsegs m 0x3d2e8 [C8 (Z_to_bv 64 RSTDOUT)] -> rw_cells rsegs m 0x3d1f8 [C8 (Z_to_bv 64 RSTDERR)] ->
stdout_file m (get_so s) -> stderr_file m ->
rw_cells rsegs m 0x3c0d0 [C8 (Z_to_bv 64 0x6d6b8)] -> rw_cells rsegs m 0x6d6b8 [C8 guard] ->
mem_inv rsegs m ->
tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code ->
(0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - 176)%Z -> (0x6e000 <= lo)%Z ->
AXSTAT k m -> rw_cells rsegs m RDSO [C8 (Z_to_bv 64 RDSO)] ->
implM rsegs (stdio_exit_model get_so set_so code) s Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x31568) fc None m (seg_rom rsegs)).
Proof.
intros until k. intros ST TDa EXL GF FA FIN GCX LCH OFL SIN SOU SEU SOF SEF GG GU MI -> -> Ht LO LOLO AX DSO.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.

first [ sf_destruct 10%nat SOF as flg mode tail bufb SOF1 SOF2 SOF3 SOF4 SOF5 SOF6 | sf_fb; destruct SOF as (flg & mode & tail & bufb & SOF1 & SOF2 & SOF3 & SOF4 & SOF5 & SOF6) ].
first [ sf_destruct 6%nat SEF as flg' mode' ee wend' tail' SEF1 | sf_fb; destruct SEF as (flg' & mode' & ee & wend' & tail' & SEF1) ].
unfold file_cells in SOF1, SEF1.
unfold stdio_exit_model.
eapply (implM_bind rsegs _ _ s
(fun _ _ ms' => exists sp' gp' tp' x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m',
ms' = MS (mkR (Z_to_bv 64 0x315d4) sp' gp' tp' x5 x6 x7 (Z_to_bv 64 code) x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0x315d4) fc None m' (seg_rom rsegs))).
-
unfold implM. iprefix.
call rexit_prefix_spec; [exact ST | exact TDa | exact EXL | exact GF | exact FA | exact FIN | exact GCX | exact MI
| reflexivity | reflexivity | lia | lia | lia | exact LCH | exact AX | exact DSO | ].
name_sp sp (-16)%Z.
pose proof stdio_exit_spec as SE. unfold stdio_exit_spec_stmt, implM in SE.
apply evt_done. eapply impl_epost_mono; [eapply SE|].
all: lazymatch goal with
| |- forall _, _ =>
intros [[] s'] ms' PO; cbn [fst snd] in PO; unfold stdio_exit_post in PO;
destruct_exs PO; destruct PO as (E & PO); subst ms'; cbn [fst snd];
replace (ret_pc (Z_to_bv 64 0x315d4)) with (Z_to_bv 64 0x315d4) by (symmetry; apply ret_pc_even; [lia|reflexivity]);
repeat eexists; cbv delta [mkR]; reflexivity
| |- stdout_file _ _ => exists flg, mode, tail, bufb; exact (conj SOF1 (conj SOF2 (conj SOF3 (conj SOF4 (conj SOF5 SOF6)))))
| |- stderr_file _ => exists flg', mode', ee, wend', tail'; exact SEF1
| |- _ => unname_sp; first [ hyp_by_addr | reflexivity | lia ]
end.
-
clear SOF1 SOF2 SOF3 SOF4 SOF5 SOF6 SEF1.
intros [] s' ms' PO. destruct_exs PO. subst ms'.
apply implM_sys. do 4 lstep. step_ecall.
split; [ at_node_red; split; [right; reflexivity | reflexivity] | intros rsp a H; cbn in H; discriminate H].
Time Qed.
End ExitProof.
