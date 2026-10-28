(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei.   (* [comment removed for export] *)
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import ITree Nodes Decode SysStep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import SysStepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
Open Scope bv_scope.

Section CANSEC1. Context {rc : runConstT}.
Definition sysret_entry := 0xb717c%Z.
Definition read_entry := 0xc5d3c%Z.
Definition close_entry := 0xc5c5c%Z.
Definition open_entry := 0xb7098%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sysret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r errv : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (sysret_val r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (errno_addr tp) [C4 (sysret_errno r errv)].

Lemma sysret_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (errv : word) (lo : Z),
  stk bsegs m lo (bv_unsigned sp) ->
  rw_cells bsegs m (errno_addr tp) [C4 errv] ->
  mem_inv bsegs m ->
  (lo <= bv_unsigned sp - 16)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  (* [comment removed for export] *)
  rng RNG lo (bv_unsigned sp - lo) ->
  rng RNG (errno_addr tp) 4 ->
  evtF bsegs RNG (sysret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 errv F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xb717c) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST ERR MI LO SEP TP RSTK RERR.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  do 3 step. if_cases Hc; zify_cond Hc.
  - (* [comment removed for export] *)
    step. unfold sysret_post, sysret_val, sysret_errno. rewrite (errno_of_small a0) by lia. finish.
  - carve_frame 16%nat ST.
    do 14 step.
    pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0.
    rewrite negw_errno in ERR by lia.
    unfold sysret_post, sysret_val, sysret_errno. rewrite (errno_of_big a0) by lia.
    release_frame FR ST (bv_unsigned sp).
    finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition read_ret (a : read_ans) : word :=
  match a with RdErr _ => Z_to_bv 64 (-1) | RdData bs => Z_to_bv 64 (Z.of_nat (length bs)) end.

Definition read_post (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (B : Z) (n : nat) (junk : list byte) (errv : word) (lo : Z) (m : word -> option byte)
    (a : read_ans) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => RNG' = RNG /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (read_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (B, B + Z.of_nat n); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ match a with
       | RdErr e => rw_cells bsegs m' B [CB n junk]
                    /\ rw_cells bsegs m' (errno_addr tp) [C4 (Z_to_bv 64 e)] /\ (1 <= e <= 4095)%Z
       | RdData bs => rw_cells bsegs m' B [CB (length bs) bs; CB (n - length bs) (skipn (length bs) junk)]
                      /\ rw_cells bsegs m' (errno_addr tp) [C4 errv] /\ (length bs <= n)%nat
       end.

Lemma read_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (fd count : Z) (junk : list byte) (errv : word) (lo : Z),
  stk bsegs m lo (bv_unsigned sp) ->
  rw_cells bsegs m (bv_unsigned a1) [CB (Z.to_nat count) junk] ->
  rw_cells bsegs m (errno_addr tp) [C4 errv] ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 fd -> a2 = Z_to_bv 64 count ->
  (3 <= fd < 2^32)%Z -> (1 <= count <= 16777216)%Z ->
  (bv_unsigned a1 + count <= 2^47)%Z ->                 (* [comment removed for export] *)
  (lo <= bv_unsigned sp - 16)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (bv_unsigned a1 + count <= bv_unsigned sp - 16 \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
  (bv_unsigned a1 + count <= errno_addr tp \/ errno_addr tp + 4 <= bv_unsigned a1)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  (* [comment removed for export] *)
  rng RNG lo (bv_unsigned sp - lo) ->
  rng RNG (errno_addr tp) 4 ->
  rng RNG (bv_unsigned a1) count ->
  implA bsegs RNG (enode (NRead fd (bv_unsigned a1) count) (dec_read (bv_unsigned a1) count))
       (epostF (read_post RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a1) (Z.to_nat count) junk errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0xc5d3c) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST DST ERR MI -> -> FD CNT CNT2 LO SEP1 SEP2 SEP3 TP RSTK RERR RDST.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + Z.of_nat (Z.to_nat count));
                          (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  apply implF_enode.
  carve_frame 16%nat ST.
  do 18 step.
  step_ecall.
  split. { at_nodeA_solve. }
  fstep_intro rsp RNG' ans HF Hdec. apply dec_read_Some in Hdec as [ci Hdec]; [|lia].
  destruct ans as [e|bs].
  - destruct Hdec as [-> He]. sys_nret.
    do 3 step. release_frame FR ST (bv_unsigned sp).
    step. call sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ].
    unfold read_post, sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
    finish; lia.
  - destruct Hdec as [-> Hlen]. sys_nret.
    do 3 step. release_frame FR ST (bv_unsigned sp).
    step. call sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ].
    unfold read_post, sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    finish; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma eintr_mask_errno : forall e, (1 <= e <= 4095)%Z ->
  Z_to_bv 64 (Z.land ((Z.b2z ((bv_unsigned (errno_ret e) + 4) mod 18446744073709551616 <? 1) + -1) mod 18446744073709551616)
                     (bv_unsigned (errno_ret e)))
  = if (e =? 4)%Z then Z_to_bv 64 0 else errno_ret e.
Proof.
  intros e He. rewrite unsigned_errno_ret by lia.
  destruct (Z.eqb_spec e 4) as [->|Hne].
  - replace ((2 ^ 64 - 4 + 4) mod 18446744073709551616)%Z with 0%Z by reflexivity.
    cbn. reflexivity.
  - assert (Hnz : ((2 ^ 64 - e + 4) mod 18446744073709551616 <? 1)%Z = false).
    { apply Z.ltb_ge. destruct (Z.ltb_spec0 e 4).
      - replace (2 ^ 64 - e + 4)%Z with ((4 - e) + 1 * 18446744073709551616)%Z by lia.
        rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
      - rewrite Z.mod_small by lia. lia. }
    rewrite Hnz. cbn [Z.b2z]. change ((0 + -1) mod 18446744073709551616)%Z with (Z.ones 64).
    rewrite Z.land_comm, Z.land_ones by lia. change (2^64)%Z with 18446744073709551616%Z.
    rewrite Z.mod_small by lia. unfold errno_ret. rewrite <- (Z_to_bv_minus_mod (18446744073709551616 - e)). f_equal. lia.
Qed.

Definition close_ret (a : sret) : word :=
  match a with
  | SVal _ => Z_to_bv 64 0
  | SErr e => if (e =? EINTR)%Z then Z_to_bv 64 0 else Z_to_bv 64 (-1)
  end.
Definition close_errno (a : sret) (errv : word) : word :=
  match a with
  | SVal _ => errv
  | SErr e => if (e =? EINTR)%Z then errv else Z_to_bv 64 e
  end.

Definition close_post (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (errv : word) (lo : Z) (m : word -> option byte) (a : sret) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => RNG' = RNG /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (close_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (errno_addr tp) [C4 (close_errno a errv)].

Lemma close_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (fd : Z) (errv : word) (lo : Z),
  stk bsegs m lo (bv_unsigned sp) ->
  rw_cells bsegs m (errno_addr tp) [C4 errv] ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 fd -> (3 <= fd < 2^32)%Z ->
  (lo <= bv_unsigned sp - 32)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  rng RNG lo (bv_unsigned sp - lo) ->
  rng RNG (errno_addr tp) 4 ->
  implA bsegs RNG (enode (NClose fd) dec_close)
       (epostF (close_post RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0xc5c5c) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST ERR MI -> FD LO SEP1 TP RSTK RERR.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  apply implF_enode.
  carve_frame 16%nat ST.
  do 20 step.
  step_ecall.
  split. { at_nodeA_solve. }
  fstep_intro rsp RNG' ans HF Hdec. apply dec_plain_Some in Hdec as [ci Hdec].
  destruct ans as [e|v].
  - destruct Hdec as [-> He]. sys_nret.
    do 2 step. rewrite sextw_errno by lia.
    do 4 zstep. rewrite eintr_mask_errno by lia. step.
    call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | solve_rng | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *.
    destruct (Z.eqb_spec e 4) as [->|Hne].
    + rewrite errno_of_lit in * by lia.
      do 4 step. release_frame FR ST (bv_unsigned sp).
      unfold close_post, close_ret, close_errno, EINTR. rewrite Z.eqb_refl. finish.
    + rewrite errno_of_errno_ret in * by lia.
      do 4 step. release_frame FR ST (bv_unsigned sp).
      unfold close_post, close_ret, close_errno, EINTR. replace (e =? 4)%Z with false by (symmetry; apply Z.eqb_neq; lia). finish.
  - destruct Hdec as (-> & Hv & _). apply Z.eqb_eq in Hv. subst v. sys_nret.
    do 6 zstep. rewrite Z.land_0_r. step.
    call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | solve_rng | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    do 4 step. release_frame FR ST (bv_unsigned sp).
    unfold close_post, close_ret, close_errno. finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition got_ssp := 0xc7fe0%Z.
Definition ssp_guard := 0x622cf0%Z.

Definition open_ret (a : sret) : word :=
  match a with SVal fd => Z_to_bv 64 fd | SErr _ => Z_to_bv 64 (-1) end.
Definition open_errno (a : sret) (errv : word) : word :=
  match a with SVal _ => errv | SErr e => Z_to_bv 64 e end.

Definition open_post (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P : Z) (path : list byte) (errv canary : word) (lo : Z) (m : word -> option byte) (a : sret) (RNG' : footprint)
    : machine_state -> Prop :=
  fun ms' => RNG' = RNG /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (open_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (errno_addr tp) [C4 (open_errno a errv)]
    /\ bytes_at bsegs m' P (path ++ [Z_to_bv 8 0])
    /\ rw_cells bsegs m' got_ssp [C8 (Z_to_bv 64 ssp_guard)]
    /\ rw_cells bsegs m' ssp_guard [C8 canary]
    /\ match a with SVal fd => (3 <= fd <= 4096)%Z | SErr e => (1 <= e <= 4095)%Z end.

Lemma open_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (path : list byte) (errv canary : word) (lo : Z),
  stk bsegs m lo (bv_unsigned sp) ->
  bytes_at bsegs m (bv_unsigned a0) (path ++ [Z_to_bv 8 0]) ->
  rw_cells bsegs m (errno_addr tp) [C4 errv] ->
  rw_cells bsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] ->
  rw_cells bsegs m ssp_guard [C8 canary] ->
  mem_inv bsegs m ->
  a1 = Z_to_bv 64 0 (* [comment removed for export] *) ->
  ~ In (Z_to_bv 8 0) path ->
  path_has_slash path = false ->                        (* [comment removed for export] *)
  (lo <= bv_unsigned sp - 112)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (bv_unsigned a0 + Z.of_nat (length path) + 1 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a0 + Z.of_nat (length path) + 1 <= errno_addr tp \/ errno_addr tp + 4 <= bv_unsigned a0)%Z ->
  (ssp_guard + 8 <= bv_unsigned sp - 112)%Z ->
  (errno_addr tp + 4 <= ssp_guard \/ ssp_guard + 8 <= errno_addr tp)%Z ->
  (got_ssp + 8 <= errno_addr tp \/ errno_addr tp + 4 <= got_ssp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  (* [comment removed for export] *)
  rng RNG lo (bv_unsigned sp - lo) ->
  rng RNG (errno_addr tp) 4 ->
  rng RNG (bv_unsigned a0) (Z.of_nat (length path) + 1) ->
  rng_aimg RNG ->
  implA bsegs RNG (enode (NOpen path) dec_open)
       (epostF (open_post RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) path errv canary lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0xb7098) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST SRC ERR GOT SSP MI -> NUL NSL LO SEP1 SEP2 SEP3 SEP4 SEP5 SEP6 TP RSTK RERR RSRC RIMG.
  unfold got_ssp, ssp_guard in *.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BP. rewrite length_app in BP. cbn [length] in BP.
  apply implF_enode.
  carve_frame 96%nat ST.
  do 18 step. if_false. do 3 step. if_false. do 2 step.
  do 8 step. (* [comment removed for export] *) do 8 step. (* [comment removed for export] *)
  step_ecall.
  split. { at_nodeA_solve. }
  fstep_intro rsp RNG' ans HF Hdec. apply dec_plain_Some in Hdec as [ci Hdec].
  destruct ans as [e|fd].
  - destruct Hdec as [-> He]. sys_nret.
    do 4 step. if_true. step. rewrite sextw_errno by lia. step.
    call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | solve_rng | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
    do 3 step. if_false. do 6 step. release_frame FR ST (bv_unsigned sp).
    unfold open_post, open_ret, open_errno, got_ssp, ssp_guard. sys_finish; lia.
  - destruct Hdec as (-> & Hfd & Hrange). apply andb_prop in Hfd as [Hfd3 Hfd]. apply Z.leb_le in Hfd3. apply Z.leb_le in Hfd. sys_nret.
    do 4 step. if_true. step. rewrite sextw_small by lia. step.
    call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | solve_rng | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    do 3 step. if_false. step. rewrite sextw_small by lia. do 5 step. release_frame FR ST (bv_unsigned sp).
    unfold open_post, open_ret, open_errno, got_ssp, ssp_guard. sys_finish; lia.
Qed.
End CANSEC1.
