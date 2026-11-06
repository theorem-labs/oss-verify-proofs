(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Namei.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require MM_syscalls.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_syscalls.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei.   (* [comment removed for export] *)
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT}.
Definition sysret_entry := 0x94b1c%Z.
Definition read_entry := 0xa3ea8%Z.
Definition close_entry := 0xa3dc8%Z.
Definition open_entry := 0x94a38%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sysret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r errv : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (sysret_val r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (errno_addr tp) [C4 (sysret_errno r errv)].

#[using="Type"] Lemma sysret_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (errv : word) (lo : Z),
  stk asegs m lo (bv_unsigned sp) ->
  rw_cells asegs m (errno_addr tp) [C4 errv] ->
  mem_inv asegs m ->
  (lo <= bv_unsigned sp - 16)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  (* [comment removed for export] *)
  rng RNG lo (bv_unsigned sp - lo) ->
  rng RNG (errno_addr tp) 4 ->
  evtF asegs RNG (sysret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 errv F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x94b1c) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST ERR MI LO SEP TP RSTK RERR.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
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
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (B, B + Z.of_nat n); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ match a with
       | RdErr e => rw_cells asegs m' B [CB n junk]
                    /\ rw_cells asegs m' (errno_addr tp) [C4 (Z_to_bv 64 e)] /\ (1 <= e <= 4095)%Z
       | RdData bs => rw_cells asegs m' B [CB (length bs) bs; CB (n - length bs) (skipn (length bs) junk)]
                      /\ rw_cells asegs m' (errno_addr tp) [C4 errv] /\ (length bs <= n)%nat
       end.

Definition read_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (fd count : Z) (junk : list byte) (errv : word) (lo : Z),
  stk asegs m lo (bv_unsigned sp) ->
  rw_cells asegs m (bv_unsigned a1) [CB (Z.to_nat count) junk] ->
  rw_cells asegs m (errno_addr tp) [C4 errv] ->
  mem_inv asegs m ->
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
  implA asegs ASHM RNG (enode (NRead fd (bv_unsigned a1) count) (dec_read (bv_unsigned a1) count))
       (epostF (read_post RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a1) (Z.to_nat count) junk errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0xa3ea8) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 0).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 7).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 8).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 9).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 10).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 11).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 12).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 13).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 14).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 15).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 16).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 17).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 18).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 19).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 20).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 21).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 22).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 23).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 24).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 25).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 26).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 27).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 28).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 29).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 30).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 31).
Variable F : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 32).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 33).
Variable m : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 34).
Variable fd : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 35).
Variable count : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 36).
Variable junk : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 37).
Variable errv : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 38).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 39).
#[using="Type"] Lemma read_spec__body : ltac:(let T := type of (fun (h : read_spec__stmt) => h RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m fd count junk errv lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (fd, (count, (junk, (errv, lo)))))))))))))))))))))))))))))))))))))))) as _.
 intros ST DST ERR MI -> -> FD CNT CNT2 LO SEP1 SEP2 SEP3 TP RSTK RERR RDST.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + Z.of_nat (Z.to_nat count));
                          (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  apply implF_enode.
  carve_frame 16%nat ST.
  do 18 step.
  step_ecall.
  split. { at_nodeA_solve. }
  fstep_intro rsp RNG' ans HF Hdec. apply dec_read_Some in Hdec; [|lia].
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
End Zd1.
#[using="Type"] Lemma read_spec : ltac:(let t := eval cbv delta [read_spec__stmt] in read_spec__stmt in exact t).
Proof. exact read_spec__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma eintr_mask_errno : forall e, (1 <= e <= 4095)%Z ->
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
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (errno_addr tp) [C4 (close_errno a errv)].

Definition close_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (fd : Z) (errv : word) (lo : Z),
  stk asegs m lo (bv_unsigned sp) ->
  rw_cells asegs m (errno_addr tp) [C4 errv] ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 fd -> (3 <= fd < 2^32)%Z ->
  (lo <= bv_unsigned sp - 32)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  rng RNG lo (bv_unsigned sp - lo) ->
  rng RNG (errno_addr tp) 4 ->
  implA asegs ASHM RNG (enode (NClose fd) dec_close)
       (epostF (close_post RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0xa3dc8) fc None m (seg_rom asegs)).
Section Zd2.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 0).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 7).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 8).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 9).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 10).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 11).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 12).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 13).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 14).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 15).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 16).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 17).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 18).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 19).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 20).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 21).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 22).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 23).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 24).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 25).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 26).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 27).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 28).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 29).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 30).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 31).
Variable F : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 32).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 33).
Variable m : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 34).
Variable fd : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 35).
Variable errv : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 36).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 37).
#[using="Type"] Lemma close_spec__body : ltac:(let T := type of (fun (h : close_spec__stmt) => h RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m fd errv lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (fd, (errv, lo)))))))))))))))))))))))))))))))))))))) as _.
 intros ST ERR MI -> FD LO SEP1 TP RSTK RERR.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  apply implF_enode.
  carve_frame 16%nat ST.
  do 20 step.
  step_ecall.
  split. { at_nodeA_solve. }
  fstep_intro rsp RNG' ans HF Hdec. apply dec_plain_Some in Hdec.
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
  - (destruct Hdec as (-> & ndR1__); nd_pre ndR1__ 2%nat; intros Hv _; nd_post). apply Z.eqb_eq in Hv. subst v. sys_nret.
    do 6 zstep. rewrite Z.land_0_r. step.
    call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | solve_rng | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    do 4 step. release_frame FR ST (bv_unsigned sp).
    unfold close_post, close_ret, close_errno. finish.
Qed.
End Zd2.
#[using="Type"] Lemma close_spec : ltac:(let t := eval cbv delta [close_spec__stmt] in close_spec__stmt in exact t).
Proof. exact close_spec__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition got_ssp := 0xa6160%Z.
Definition ssp_guard := 0x6015f8%Z.

Definition open_ret (a : sret) : word :=
  match a with SVal fd => Z_to_bv 64 fd | SErr _ => Z_to_bv 64 (-1) end.
Definition open_errno (a : sret) (errv : word) : word :=
  match a with SVal _ => errv | SErr e => Z_to_bv 64 e end.

Definition open_post (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P : Z) (path : list byte) (errv canary : word) (lo : Z) (m : word -> option byte) (a : sret) (RNG' : footprint)
    : machine_state -> Prop :=
  fun ms' => RNG' = RNG /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (open_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (errno_addr tp) [C4 (open_errno a errv)]
    /\ bytes_at asegs m' P (path ++ [Z_to_bv 8 0])
    /\ rw_cells asegs m' got_ssp [C8 (Z_to_bv 64 ssp_guard)]
    /\ rw_cells asegs m' ssp_guard [C8 canary]
    /\ match a with SVal fd => (3 <= fd <= 4096)%Z | SErr e => (1 <= e <= 4095)%Z end.

Definition open_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (path : list byte) (errv canary : word) (lo : Z),
  stk asegs m lo (bv_unsigned sp) ->
  bytes_at asegs m (bv_unsigned a0) (path ++ [Z_to_bv 8 0]) ->
  rw_cells asegs m (errno_addr tp) [C4 errv] ->
  rw_cells asegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] ->
  rw_cells asegs m ssp_guard [C8 canary] ->
  mem_inv asegs m ->
  a1 = Z_to_bv 64 0 (* [comment removed for export] *) ->
  ~ In (Z_to_bv 8 0) path ->
  path_has_slash path = false ->                        (* [comment removed for export] *)
  Fs.path_eqb path Namei.dotdot_path = false ->         (* [comment removed for export] *)
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
  implA asegs ASHM RNG (enode (NOpen path) dec_open)
       (epostF (open_post RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) path errv canary lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x94a38) fc None m (seg_rom asegs)).
Section Zd3.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 0).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 7).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 8).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 9).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 10).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 11).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 12).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 13).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 14).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 15).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 16).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 17).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 18).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 19).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 20).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 21).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 22).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 23).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 24).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 25).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 26).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 27).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 28).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 29).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 30).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 31).
Variable F : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 32).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 33).
Variable m : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 34).
Variable path : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 35).
Variable errv : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 36).
Variable canary : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 37).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 38).
#[using="Type"] Lemma open_spec__body : ltac:(let T := type of (fun (h : open_spec__stmt) => h RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m path errv canary lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (path, (errv, (canary, lo))))))))))))))))))))))))))))))))))))))) as _.
 intros ST SRC ERR GOT SSP MI -> NUL NSL NDD LO SEP1 SEP2 SEP3 SEP4 SEP5 SEP6 TP RSTK RERR RSRC RIMG.
  unfold got_ssp, ssp_guard in *.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BP. rewrite length_app in BP. cbn [length] in BP.
  apply implF_enode.
  carve_frame 96%nat ST.
  do 18 step. if_false. do 3 step. if_false. do 2 step.
  do 8 step. (* [comment removed for export] *) do 8 step. (* [comment removed for export] *)
  step_ecall.
  split. { at_nodeA_solve. }
  fstep_intro rsp RNG' ans HF Hdec. apply dec_plain_Some in Hdec.
  destruct ans as [e|fd].
  - destruct Hdec as [-> He]. sys_nret.
    do 4 step. if_true. step. rewrite sextw_errno by lia. step.
    call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | solve_rng | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
    do 3 step. if_false. do 6 step. release_frame FR ST (bv_unsigned sp).
    unfold open_post, open_ret, open_errno, got_ssp, ssp_guard. sys_finish; lia.
  - (destruct Hdec as (-> & ndR1__); nd_pre ndR1__ 2%nat; intros Hfd Hrange; nd_post). apply andb_prop in Hfd as [Hfd3 Hfd]. apply Z.leb_le in Hfd3. apply Z.leb_le in Hfd. sys_nret.
    do 4 step. if_true. step. rewrite sextw_small by lia. step.
    call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | solve_rng | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    do 3 step. if_false. step. rewrite sextw_small by lia. do 5 step. release_frame FR ST (bv_unsigned sp).
    unfold open_post, open_ret, open_errno, got_ssp, ssp_guard. sys_finish; lia.
Qed.
End Zd3.
#[using="Type"] Lemma open_spec : ltac:(let t := eval cbv delta [open_spec__stmt] in open_spec__stmt in exact t).
Proof. exact open_spec__body. Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Namei.   (* [comment removed for export] *)
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT}.
Definition sysret_entry := 0x94f00%Z.
Definition read_entry := 0xa428c%Z.
Definition close_entry := 0xa41ac%Z.
Definition open_entry := 0x94e1c%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sysret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r errv : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (sysret_val r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (errno_addr tp) [C4 (sysret_errno r errv)].

#[using="Type"] Lemma sysret_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (errv : word) (lo : Z),
  stk asegs m lo (bv_unsigned sp) ->
  rw_cells asegs m (errno_addr tp) [C4 errv] ->
  mem_inv asegs m ->
  (lo <= bv_unsigned sp - 16)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  (* [comment removed for export] *)
  rng RNG lo (bv_unsigned sp - lo) ->
  rng RNG (errno_addr tp) 4 ->
  evtF asegs RNG (sysret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 errv F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x94f00) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST ERR MI LO SEP TP RSTK RERR.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
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
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (B, B + Z.of_nat n); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ match a with
       | RdErr e => rw_cells asegs m' B [CB n junk]
                    /\ rw_cells asegs m' (errno_addr tp) [C4 (Z_to_bv 64 e)] /\ (1 <= e <= 4095)%Z
       | RdData bs => rw_cells asegs m' B [CB (length bs) bs; CB (n - length bs) (skipn (length bs) junk)]
                      /\ rw_cells asegs m' (errno_addr tp) [C4 errv] /\ (length bs <= n)%nat
       end.

Definition read_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (fd count : Z) (junk : list byte) (errv : word) (lo : Z),
  stk asegs m lo (bv_unsigned sp) ->
  rw_cells asegs m (bv_unsigned a1) [CB (Z.to_nat count) junk] ->
  rw_cells asegs m (errno_addr tp) [C4 errv] ->
  mem_inv asegs m ->
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
  implA asegs ASHM RNG (enode (NRead fd (bv_unsigned a1) count) (dec_read (bv_unsigned a1) count))
       (epostF (read_post RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a1) (Z.to_nat count) junk errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0xa428c) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 0).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 7).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 8).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 9).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 10).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 11).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 12).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 13).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 14).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 15).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 16).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 17).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 18).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 19).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 20).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 21).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 22).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 23).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 24).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 25).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 26).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 27).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 28).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 29).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 30).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 31).
Variable F : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 32).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 33).
Variable m : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 34).
Variable fd : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 35).
Variable count : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 36).
Variable junk : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 37).
Variable errv : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 38).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'read_spec__stmt 39).
#[using="Type"] Lemma read_spec__body : ltac:(let T := type of (fun (h : read_spec__stmt) => h RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m fd count junk errv lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (fd, (count, (junk, (errv, lo)))))))))))))))))))))))))))))))))))))))) as _.
 intros ST DST ERR MI -> -> FD CNT CNT2 LO SEP1 SEP2 SEP3 TP RSTK RERR RDST.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + Z.of_nat (Z.to_nat count));
                          (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  apply implF_enode.
  carve_frame 16%nat ST.
  do 18 step.
  step_ecall.
  split. { at_nodeA_solve. }
  fstep_intro rsp RNG' ans HF Hdec. apply dec_read_Some in Hdec; [|lia].
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
End Zd1.
#[using="Type"] Lemma read_spec : ltac:(let t := eval cbv delta [read_spec__stmt] in read_spec__stmt in exact t).
Proof. exact read_spec__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma eintr_mask_errno : forall e, (1 <= e <= 4095)%Z ->
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
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (errno_addr tp) [C4 (close_errno a errv)].

Definition close_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (fd : Z) (errv : word) (lo : Z),
  stk asegs m lo (bv_unsigned sp) ->
  rw_cells asegs m (errno_addr tp) [C4 errv] ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 fd -> (3 <= fd < 2^32)%Z ->
  (lo <= bv_unsigned sp - 32)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  rng RNG lo (bv_unsigned sp - lo) ->
  rng RNG (errno_addr tp) 4 ->
  implA asegs ASHM RNG (enode (NClose fd) dec_close)
       (epostF (close_post RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0xa41ac) fc None m (seg_rom asegs)).
Section Zd2.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 0).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 7).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 8).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 9).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 10).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 11).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 12).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 13).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 14).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 15).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 16).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 17).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 18).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 19).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 20).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 21).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 22).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 23).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 24).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 25).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 26).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 27).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 28).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 29).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 30).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 31).
Variable F : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 32).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 33).
Variable m : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 34).
Variable fd : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 35).
Variable errv : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 36).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'close_spec__stmt 37).
#[using="Type"] Lemma close_spec__body : ltac:(let T := type of (fun (h : close_spec__stmt) => h RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m fd errv lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (fd, (errv, lo)))))))))))))))))))))))))))))))))))))) as _.
 intros ST ERR MI -> FD LO SEP1 TP RSTK RERR.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  apply implF_enode.
  carve_frame 16%nat ST.
  do 20 step.
  step_ecall.
  split. { at_nodeA_solve. }
  fstep_intro rsp RNG' ans HF Hdec. apply dec_plain_Some in Hdec.
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
  - (destruct Hdec as (-> & ndR1__); nd_pre ndR1__ 2%nat; intros Hv _; nd_post). apply Z.eqb_eq in Hv. subst v. sys_nret.
    do 6 zstep. rewrite Z.land_0_r. step.
    call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | solve_rng | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    do 4 step. release_frame FR ST (bv_unsigned sp).
    unfold close_post, close_ret, close_errno. finish.
Qed.
End Zd2.
#[using="Type"] Lemma close_spec : ltac:(let t := eval cbv delta [close_spec__stmt] in close_spec__stmt in exact t).
Proof. exact close_spec__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition got_ssp := 0xa6540%Z.
Definition ssp_guard := 0x6019f8%Z.

Definition open_ret (a : sret) : word :=
  match a with SVal fd => Z_to_bv 64 fd | SErr _ => Z_to_bv 64 (-1) end.
Definition open_errno (a : sret) (errv : word) : word :=
  match a with SVal _ => errv | SErr e => Z_to_bv 64 e end.

Definition open_post (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P : Z) (path : list byte) (errv canary : word) (lo : Z) (m : word -> option byte) (a : sret) (RNG' : footprint)
    : machine_state -> Prop :=
  fun ms' => RNG' = RNG /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (open_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (errno_addr tp) [C4 (open_errno a errv)]
    /\ bytes_at asegs m' P (path ++ [Z_to_bv 8 0])
    /\ rw_cells asegs m' got_ssp [C8 (Z_to_bv 64 ssp_guard)]
    /\ rw_cells asegs m' ssp_guard [C8 canary]
    /\ match a with SVal fd => (3 <= fd <= 4096)%Z | SErr e => (1 <= e <= 4095)%Z end.

Definition open_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (path : list byte) (errv canary : word) (lo : Z),
  stk asegs m lo (bv_unsigned sp) ->
  bytes_at asegs m (bv_unsigned a0) (path ++ [Z_to_bv 8 0]) ->
  rw_cells asegs m (errno_addr tp) [C4 errv] ->
  rw_cells asegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] ->
  rw_cells asegs m ssp_guard [C8 canary] ->
  mem_inv asegs m ->
  a1 = Z_to_bv 64 0 (* [comment removed for export] *) ->
  ~ In (Z_to_bv 8 0) path ->
  path_has_slash path = false ->                        (* [comment removed for export] *)
  Fs.path_eqb path Namei.dotdot_path = false ->         (* [comment removed for export] *)
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
  implA asegs ASHM RNG (enode (NOpen path) dec_open)
       (epostF (open_post RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) path errv canary lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x94e1c) fc None m (seg_rom asegs)).
Section Zd3.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 0).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 7).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 8).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 9).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 10).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 11).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 12).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 13).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 14).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 15).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 16).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 17).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 18).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 19).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 20).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 21).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 22).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 23).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 24).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 25).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 26).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 27).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 28).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 29).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 30).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 31).
Variable F : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 32).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 33).
Variable m : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 34).
Variable path : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 35).
Variable errv : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 36).
Variable canary : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 37).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'open_spec__stmt 38).
#[using="Type"] Lemma open_spec__body : ltac:(let T := type of (fun (h : open_spec__stmt) => h RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m path errv canary lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (path, (errv, (canary, lo))))))))))))))))))))))))))))))))))))))) as _.
 intros ST SRC ERR GOT SSP MI -> NUL NSL NDD LO SEP1 SEP2 SEP3 SEP4 SEP5 SEP6 TP RSTK RERR RSRC RIMG.
  unfold got_ssp, ssp_guard in *.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BP. rewrite length_app in BP. cbn [length] in BP.
  apply implF_enode.
  carve_frame 96%nat ST.
  do 18 step. if_false. do 3 step. if_false. do 2 step.
  do 8 step. (* [comment removed for export] *) do 8 step. (* [comment removed for export] *)
  step_ecall.
  split. { at_nodeA_solve. }
  fstep_intro rsp RNG' ans HF Hdec. apply dec_plain_Some in Hdec.
  destruct ans as [e|fd].
  - destruct Hdec as [-> He]. sys_nret.
    do 4 step. if_true. step. rewrite sextw_errno by lia. step.
    call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | solve_rng | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
    do 3 step. if_false. do 6 step. release_frame FR ST (bv_unsigned sp).
    unfold open_post, open_ret, open_errno, got_ssp, ssp_guard. sys_finish; lia.
  - (destruct Hdec as (-> & ndR1__); nd_pre ndR1__ 2%nat; intros Hfd Hrange; nd_post). apply andb_prop in Hfd as [Hfd3 Hfd]. apply Z.leb_le in Hfd3. apply Z.leb_le in Hfd. sys_nret.
    do 4 step. if_true. step. rewrite sextw_small by lia. step.
    call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | solve_rng | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    do 3 step. if_false. step. rewrite sextw_small by lia. do 5 step. release_frame FR ST (bv_unsigned sp).
    unfold open_post, open_ret, open_errno, got_ssp, ssp_guard. sys_finish; lia.
Qed.
End Zd3.
#[using="Type"] Lemma open_spec : ltac:(let t := eval cbv delta [open_spec__stmt] in open_spec__stmt in exact t).
Proof. exact open_spec__body. Qed.
End CANSEC1.
End TwB.
End F_syscalls.

(* [comment removed for export] *)
Module RT_stubs.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MM_syscalls.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition rt_mmap_entry := 0x68298%Z.
Definition rt_munmap_entry := 0x682a4%Z.
Definition rt_mprotect_entry := 0x682b0%Z.
Definition rt_close_entry := 0x682ec%Z.

(* [comment removed for export] *)
Definition eff_mem (m : word -> option byte) (e : resp) : word -> option byte :=
  apply_writes (apply_copies m (apply_zeros (apply_unmaps m (eff_unmaps e)) (eff_zeros e)) (eff_copies e)) (eff_writes e).

#[using="Type"] Lemma nret_MSsvc_gen : forall R F pc x8 fc rv m ro e,
  nret (MSsvc R F pc x8 fc rv m ro) e = MS (bvmap_set 10 (eff_ret e) R) F (pc + Z_to_bv 64 4) fc rv (eff_mem m e) ro.
Proof. intros. destruct e. reflexivity. Qed.

#[using="Type"] Lemma eff_mem_efferr : forall m e, eff_mem m (efferr e) = m.      (* [comment removed for export] *)
Proof. reflexivity. Qed.
#[using="Type"] Lemma eff_mem_eff0 : forall m r, eff_mem m (eff0 r) = m.
Proof. reflexivity. Qed.
#[using="Type"] Lemma eff_mem_zeros : forall m r z ci, eff_mem m (mkEffectU r [] [z] [] [] ci) = apply_zeros m [z].
Proof. reflexivity. Qed.
#[using="Type"] Lemma eff_mem_unmaps : forall m r u ci, eff_mem m (mkEffectU r [] [] [u] [] ci) = apply_unmaps m [u].
Proof. reflexivity. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma rt_mmap_grant : forall addr len flags avoid rsp a R R',
  fstepA (NMmap addr len (PROT_READ + PROT_WRITE) flags) rsp R R' ->
  dec_mmap len avoid rsp = Some (MmOk a) -> (0 <= len)%Z ->     (* [comment removed for export] *)
  rng R' a (mmap_len len).
Proof.
  intros addr len flags avoid rsp a R R' HF Hdec LEN.
  destruct (dec_mmap_Some _ _ _ _ Hdec) as [-> Hok].
  pose proof (mmap_addr_ok_true _ _ _ Hok) as ((HA & H0 & HC) & _). change (@alloc_ceiling _) with ATOP in HC.
  pose proof (mmap_len_ge len) as ML. pose proof atop_range as AR.
  assert (E : bv_unsigned (eff_ret (mkEffect (Z_to_bv 64 a) [] [(wa a, Z_to_bv 64 (mmap_len len))])) = a).
  { cbn [eff_ret]. apply unsigned_lit. clear -H0 HC ML LEN. lia. }
  pose proof (fstepA_mmap_grant addr len flags _ R R' HF) as G. rewrite E in G.
  rewrite (unsigned_lit len) in G by (clear -H0 HC ML LEN; lia). apply G. exact HA.
Qed.

Section STUBS.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).

Definition rt_regs (a0 a1 a2 a3 a4 a5 a7 : word) : bvmap 5 word :=
  mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

Local Ltac stub_tail HF Hdec rsp :=
  rewrite nret_MSsvc_gen; rewrite ?mkR_set_a0; simp_regs;
  (lazymatch goal with
   | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4) _ _ _ _) =>
       let p' := eval vm_compute in (p + 4)%Z in
       replace (Z_to_bv 64 p + Z_to_bv 64 4 : word) with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity)
   end).

(* [comment removed for export] *)
#[using="Type"] Lemma rt_mmap_stub : forall RNG {X} (dec : resp -> option X) (addr len prot flags : Z) (x17 : word),
  Z.testbit flags 14 = false ->      (* [comment removed for export] *)
  implA asegs ASHM RNG (enode (NMmap addr len prot flags) dec)
    (epostF (fun a RNG' ms' => exists rsp,
        fstepA (NMmap addr len prot flags) rsp RNG RNG' /\ dec rsp = Some a /\
        ms' = MS (rt_regs (eff_ret rsp) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) (Z_to_bv 64 222))
                 F (ret_pc ra) fc None (eff_mem m rsp) (seg_rom asegs)))
    (MS (rt_regs (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) x17)
        F (Z_to_bv 64 0x68298) fc None m (seg_rom asegs)).
Proof.
  intros RNG X dec addr len prot flags x17 NR. unfold rt_regs. apply implF_enode.
  step. step_ecall. split. { at_nodeA_solve. }
  intros rsp RNG' a HF Hdec. stub_tail HF Hdec rsp.
  step.
  apply evtF_done. exists rsp. split; [exact HF|]. split; [exact Hdec|]. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rt_mmap_stubP : forall (fst : node -> resp -> footprint -> footprint -> Prop) RNG {X} (dec : resp -> option X)
    (addr len prot flags : Z) (x17 : word),
  Z.testbit flags 14 = false ->
  @implF node asegs (at_nodeA asegs) (silA ASHM) (npeekA asegs) fst _ RNG (enode (NMmap addr len prot flags) dec)
    (epostF (fun a RNG' ms' => exists rsp,
        fst (NMmap addr len prot flags) rsp RNG RNG' /\ dec rsp = Some a /\
        ms' = MS (rt_regs (eff_ret rsp) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) (Z_to_bv 64 222))
                 F (ret_pc ra) fc None (eff_mem m rsp) (seg_rom asegs)))
    (MS (rt_regs (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) x17)
        F (Z_to_bv 64 0x68298) fc None m (seg_rom asegs)).
Proof.
  intros fst RNG X dec addr len prot flags x17 NR. unfold rt_regs. apply implF_enode.
  step. step_ecall. split. { at_nodeA_solve. }
  intros rsp RNG' a HF Hdec. stub_tail HF Hdec rsp.
  step.
  apply evtF_done. exists rsp. split; [exact HF|]. split; [exact Hdec|]. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rt_munmap_stub : forall RNG {X} (dec : resp -> option X) (addr len : Z) (x12 x13 x14 x15 x17 : word),
  implA asegs ASHM RNG (enode (NMunmap addr len) dec)
    (epostF (fun a RNG' ms' => exists rsp,
        fstepA (NMunmap addr len) rsp RNG RNG' /\ dec rsp = Some a /\
        ms' = MS (rt_regs (eff_ret rsp) (Z_to_bv 64 len) x12 x13 x14 x15 (Z_to_bv 64 215))
                 F (ret_pc ra) fc None (eff_mem m rsp) (seg_rom asegs)))
    (MS (rt_regs (Z_to_bv 64 addr) (Z_to_bv 64 len) x12 x13 x14 x15 x17)
        F (Z_to_bv 64 0x682a4) fc None m (seg_rom asegs)).
Proof.
  intros RNG X dec addr len x12 x13 x14 x15 x17. unfold rt_regs. apply implF_enode.
  step. step_ecall. split. { at_nodeA_solve. }
  intros rsp RNG' a HF Hdec. stub_tail HF Hdec rsp.
  step.
  apply evtF_done. exists rsp. split; [exact HF|]. split; [exact Hdec|]. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma rt_close_stub : forall RNG {X} (dec : resp -> option X) (fd : Z) (x11 x12 x13 x14 x15 x17 : word),
  (3 <= fd < 2^32)%Z ->
  implA asegs ASHM RNG (enode (NClose fd) dec)
    (epostF (fun a RNG' ms' => exists rsp,
        RNG' = RNG /\ dec rsp = Some a /\
        ms' = MS (rt_regs (eff_ret rsp) x11 x12 x13 x14 x15 (Z_to_bv 64 57))
                 F (ret_pc ra) fc None (eff_mem m rsp) (seg_rom asegs)))
    (MS (rt_regs (Z_to_bv 64 fd) x11 x12 x13 x14 x15 x17)
        F (Z_to_bv 64 0x682ec) fc None m (seg_rom asegs)).
Proof.
  intros RNG X dec fd x11 x12 x13 x14 x15 x17 FD. unfold rt_regs. apply implF_enode.
  step. step_ecall. split. { at_nodeA_solve. }
  intros rsp RNG' a HF Hdec. stub_tail HF Hdec rsp.
  step.
  apply evtF_done. exists rsp. split; [exact HF|]. split; [exact Hdec|]. reflexivity.
Qed.

End STUBS.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MM_syscalls.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition rt_mmap_entry := 0x68300%Z.
Definition rt_munmap_entry := 0x6830c%Z.
Definition rt_mprotect_entry := 0x68318%Z.
Definition rt_close_entry := 0x68354%Z.

(* [comment removed for export] *)
Definition eff_mem (m : word -> option byte) (e : resp) : word -> option byte :=
  apply_writes (apply_copies m (apply_zeros (apply_unmaps m (eff_unmaps e)) (eff_zeros e)) (eff_copies e)) (eff_writes e).

#[using="Type"] Lemma nret_MSsvc_gen : forall R F pc x8 fc rv m ro e,
  nret (MSsvc R F pc x8 fc rv m ro) e = MS (bvmap_set 10 (eff_ret e) R) F (pc + Z_to_bv 64 4) fc rv (eff_mem m e) ro.
Proof. intros. destruct e. reflexivity. Qed.

#[using="Type"] Lemma eff_mem_efferr : forall m e, eff_mem m (efferr e) = m.      (* [comment removed for export] *)
Proof. reflexivity. Qed.
#[using="Type"] Lemma eff_mem_eff0 : forall m r, eff_mem m (eff0 r) = m.
Proof. reflexivity. Qed.
#[using="Type"] Lemma eff_mem_zeros : forall m r z ci, eff_mem m (mkEffectU r [] [z] [] [] ci) = apply_zeros m [z].
Proof. reflexivity. Qed.
#[using="Type"] Lemma eff_mem_unmaps : forall m r u ci, eff_mem m (mkEffectU r [] [] [u] [] ci) = apply_unmaps m [u].
Proof. reflexivity. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma rt_mmap_grant : forall addr len flags avoid rsp a R R',
  fstepA (NMmap addr len (PROT_READ + PROT_WRITE) flags) rsp R R' ->
  dec_mmap len avoid rsp = Some (MmOk a) -> (0 <= len)%Z ->     (* [comment removed for export] *)
  rng R' a (mmap_len len).
Proof.
  intros addr len flags avoid rsp a R R' HF Hdec LEN.
  destruct (dec_mmap_Some _ _ _ _ Hdec) as [-> Hok].
  pose proof (mmap_addr_ok_true _ _ _ Hok) as ((HA & H0 & HC) & _). change (@alloc_ceiling _) with ATOP in HC.
  pose proof (mmap_len_ge len) as ML. pose proof atop_range as AR.
  assert (E : bv_unsigned (eff_ret (mkEffect (Z_to_bv 64 a) [] [(wa a, Z_to_bv 64 (mmap_len len))])) = a).
  { cbn [eff_ret]. apply unsigned_lit. clear -H0 HC ML LEN. lia. }
  pose proof (fstepA_mmap_grant addr len flags _ R R' HF) as G. rewrite E in G.
  rewrite (unsigned_lit len) in G by (clear -H0 HC ML LEN; lia). apply G. exact HA.
Qed.

Section STUBS.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).

Definition rt_regs (a0 a1 a2 a3 a4 a5 a7 : word) : bvmap 5 word :=
  mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

Local Ltac stub_tail HF Hdec rsp :=
  rewrite nret_MSsvc_gen; rewrite ?mkR_set_a0; simp_regs;
  (lazymatch goal with
   | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4) _ _ _ _) =>
       let p' := eval vm_compute in (p + 4)%Z in
       replace (Z_to_bv 64 p + Z_to_bv 64 4 : word) with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity)
   end).

(* [comment removed for export] *)
#[using="Type"] Lemma rt_mmap_stub : forall RNG {X} (dec : resp -> option X) (addr len prot flags : Z) (x17 : word),
  Z.testbit flags 14 = false ->      (* [comment removed for export] *)
  implA asegs ASHM RNG (enode (NMmap addr len prot flags) dec)
    (epostF (fun a RNG' ms' => exists rsp,
        fstepA (NMmap addr len prot flags) rsp RNG RNG' /\ dec rsp = Some a /\
        ms' = MS (rt_regs (eff_ret rsp) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) (Z_to_bv 64 222))
                 F (ret_pc ra) fc None (eff_mem m rsp) (seg_rom asegs)))
    (MS (rt_regs (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) x17)
        F (Z_to_bv 64 0x68300) fc None m (seg_rom asegs)).
Proof.
  intros RNG X dec addr len prot flags x17 NR. unfold rt_regs. apply implF_enode.
  step. step_ecall. split. { at_nodeA_solve. }
  intros rsp RNG' a HF Hdec. stub_tail HF Hdec rsp.
  step.
  apply evtF_done. exists rsp. split; [exact HF|]. split; [exact Hdec|]. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rt_mmap_stubP : forall (fst : node -> resp -> footprint -> footprint -> Prop) RNG {X} (dec : resp -> option X)
    (addr len prot flags : Z) (x17 : word),
  Z.testbit flags 14 = false ->
  @implF node asegs (at_nodeA asegs) (silA ASHM) (npeekA asegs) fst _ RNG (enode (NMmap addr len prot flags) dec)
    (epostF (fun a RNG' ms' => exists rsp,
        fst (NMmap addr len prot flags) rsp RNG RNG' /\ dec rsp = Some a /\
        ms' = MS (rt_regs (eff_ret rsp) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) (Z_to_bv 64 222))
                 F (ret_pc ra) fc None (eff_mem m rsp) (seg_rom asegs)))
    (MS (rt_regs (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) x17)
        F (Z_to_bv 64 0x68300) fc None m (seg_rom asegs)).
Proof.
  intros fst RNG X dec addr len prot flags x17 NR. unfold rt_regs. apply implF_enode.
  step. step_ecall. split. { at_nodeA_solve. }
  intros rsp RNG' a HF Hdec. stub_tail HF Hdec rsp.
  step.
  apply evtF_done. exists rsp. split; [exact HF|]. split; [exact Hdec|]. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rt_munmap_stub : forall RNG {X} (dec : resp -> option X) (addr len : Z) (x12 x13 x14 x15 x17 : word),
  implA asegs ASHM RNG (enode (NMunmap addr len) dec)
    (epostF (fun a RNG' ms' => exists rsp,
        fstepA (NMunmap addr len) rsp RNG RNG' /\ dec rsp = Some a /\
        ms' = MS (rt_regs (eff_ret rsp) (Z_to_bv 64 len) x12 x13 x14 x15 (Z_to_bv 64 215))
                 F (ret_pc ra) fc None (eff_mem m rsp) (seg_rom asegs)))
    (MS (rt_regs (Z_to_bv 64 addr) (Z_to_bv 64 len) x12 x13 x14 x15 x17)
        F (Z_to_bv 64 0x6830c) fc None m (seg_rom asegs)).
Proof.
  intros RNG X dec addr len x12 x13 x14 x15 x17. unfold rt_regs. apply implF_enode.
  step. step_ecall. split. { at_nodeA_solve. }
  intros rsp RNG' a HF Hdec. stub_tail HF Hdec rsp.
  step.
  apply evtF_done. exists rsp. split; [exact HF|]. split; [exact Hdec|]. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma rt_close_stub : forall RNG {X} (dec : resp -> option X) (fd : Z) (x11 x12 x13 x14 x15 x17 : word),
  (3 <= fd < 2^32)%Z ->
  implA asegs ASHM RNG (enode (NClose fd) dec)
    (epostF (fun a RNG' ms' => exists rsp,
        RNG' = RNG /\ dec rsp = Some a /\
        ms' = MS (rt_regs (eff_ret rsp) x11 x12 x13 x14 x15 (Z_to_bv 64 57))
                 F (ret_pc ra) fc None (eff_mem m rsp) (seg_rom asegs)))
    (MS (rt_regs (Z_to_bv 64 fd) x11 x12 x13 x14 x15 x17)
        F (Z_to_bv 64 0x68354) fc None m (seg_rom asegs)).
Proof.
  intros RNG X dec fd x11 x12 x13 x14 x15 x17 FD. unfold rt_regs. apply implF_enode.
  step. step_ecall. split. { at_nodeA_solve. }
  intros rsp RNG' a HF Hdec. stub_tail HF Hdec rsp.
  step.
  apply evtF_done. exists rsp. split; [exact HF|]. split; [exact Hdec|]. reflexivity.
Qed.

End STUBS.
End CANSEC1.
End TwB.
End RT_stubs.
