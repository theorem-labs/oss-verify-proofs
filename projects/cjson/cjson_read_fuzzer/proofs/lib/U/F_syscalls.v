(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac ITree Nodes SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import UImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_syscalls.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.


Definition sysret_entry := 0x162d4%Z.
Definition read_entry := 0x224f8%Z.
Definition close_entry := 0x22498%Z.
Definition open_entry := 0x16188%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sysret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r errv : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (sysret_val r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 (sysret_errno r errv)].

Lemma sysret_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (errv : word) (lo : Z),
  stk usegs m lo (bv_unsigned sp) ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  (lo <= bv_unsigned sp - 16)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  evt usegs (sysret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 errv F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x162d4) fc None m (seg_rom usegs)).
Proof. first [ exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_syscalls.sysret_spec | (pose proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_syscalls.sysret_spec as T_; exact T_) | exact @OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_syscalls.sysret_spec | apply OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_syscalls.sysret_spec | (apply (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_syscalls.sysret_spec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img); typeclasses eauto) ]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition read_ret (a : read_ans) : word :=
  match a with RdErr _ => Z_to_bv 64 (-1) | RdData bs => Z_to_bv 64 (Z.of_nat (length bs)) end.

Definition read_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (B : Z) (n : nat) (junk : list byte) (errv : word) (lo : Z) (m : word -> option byte)
    (a : read_ans) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (read_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (B, B + Z.of_nat n); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ match a with
       | RdErr e => rw_cells usegs m' B [CB n junk]
                    /\ rw_cells usegs m' (errno_addr tp) [C4 (Z_to_bv 64 e)] /\ (1 <= e <= 4095)%Z
       | RdData bs => rw_cells usegs m' B [CB (length bs) bs; CB (n - length bs) (skipn (length bs) junk)]
                      /\ rw_cells usegs m' (errno_addr tp) [C4 errv] /\ (length bs <= n)%nat
       end.

Lemma read_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (fd count : Z) (junk : list byte) (errv : word) (lo : Z),
  stk usegs m lo (bv_unsigned sp) ->
  rw_cells usegs m (bv_unsigned a1) [CB (Z.to_nat count) junk] ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 fd -> a2 = Z_to_bv 64 count ->
  (3 <= fd < 2^32)%Z -> (0 <= count < 2^63)%Z ->
  (lo <= bv_unsigned sp - 16)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (bv_unsigned a1 + count <= bv_unsigned sp - 16 \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
  (bv_unsigned a1 + count <= errno_addr tp \/ errno_addr tp + 4 <= bv_unsigned a1)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl usegs (at_node usegs) (enode (NRead fd (bv_unsigned a1) count) (dec_read (bv_unsigned a1) count))
       (epost (read_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a1) (Z.to_nat count) junk errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x224f8) fc None m (seg_rom usegs)).
Proof. first [ exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_syscalls.read_spec | (pose proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_syscalls.read_spec as T_; exact T_) | exact @OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_syscalls.read_spec | apply OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_syscalls.read_spec | (apply (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_syscalls.read_spec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img); typeclasses eauto) ]. Qed.

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

Definition close_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (errv : word) (lo : Z) (m : word -> option byte) (a : sret) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (close_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 (close_errno a errv)].

Lemma close_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (fd : Z) (errv : word) (lo : Z),
  stk usegs m lo (bv_unsigned sp) ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 fd -> (3 <= fd < 2^32)%Z ->
  (lo <= bv_unsigned sp - 32)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl usegs (at_node usegs) (enode (NClose fd) dec_close)
       (epost (close_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x22498) fc None m (seg_rom usegs)).
Proof. first [ exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_syscalls.close_spec | (pose proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_syscalls.close_spec as T_; exact T_) | exact @OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_syscalls.close_spec | apply OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_syscalls.close_spec | (apply (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_syscalls.close_spec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img); typeclasses eauto) ]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition got_ssp := 0x23630%Z.
Definition ssp_guard := 0x54c38%Z.

Definition open_ret (a : sret) : word :=
  match a with SVal fd => Z_to_bv 64 fd | SErr _ => Z_to_bv 64 (-1) end.
Definition open_errno (a : sret) (errv : word) : word :=
  match a with SVal _ => errv | SErr e => Z_to_bv 64 e end.

Definition open_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P : Z) (path : list byte) (errv canary : word) (lo : Z) (m : word -> option byte) (a : sret) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (open_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 (open_errno a errv)]
    /\ bytes_at usegs m' P (path ++ [Z_to_bv 8 0])
    /\ rw_cells usegs m' got_ssp [C8 (Z_to_bv 64 ssp_guard)]
    /\ rw_cells usegs m' ssp_guard [C8 canary]
    /\ match a with SVal fd => (3 <= fd <= 4096)%Z | SErr e => (1 <= e <= 4095)%Z end.

Lemma open_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (path : list byte) (errv canary : word) (lo : Z),
  stk usegs m lo (bv_unsigned sp) ->
  bytes_at usegs m (bv_unsigned a0) (path ++ [Z_to_bv 8 0]) ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  rw_cells usegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] ->
  rw_cells usegs m ssp_guard [C8 canary] ->
  mem_inv usegs m ->
  a1 = Z_to_bv 64 0 (* [comment removed for export] *) ->
  ~ In (Z_to_bv 8 0) path ->
  (lo <= bv_unsigned sp - 112)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (bv_unsigned a0 + Z.of_nat (length path) + 1 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a0 + Z.of_nat (length path) + 1 <= errno_addr tp \/ errno_addr tp + 4 <= bv_unsigned a0)%Z ->
  (ssp_guard + 8 <= bv_unsigned sp - 112)%Z ->
  (errno_addr tp + 4 <= ssp_guard \/ ssp_guard + 8 <= errno_addr tp)%Z ->
  (got_ssp + 8 <= errno_addr tp \/ errno_addr tp + 4 <= got_ssp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl usegs (at_node usegs) (enode (NOpen path) dec_open)
       (epost (open_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) path errv canary lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x16188) fc None m (seg_rom usegs)).
Proof. first [ exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_syscalls.open_spec | (pose proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_syscalls.open_spec as T_; exact T_) | exact @OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_syscalls.open_spec | apply OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_syscalls.open_spec | (apply (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_syscalls.open_spec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img); typeclasses eauto) ]. Qed.
#[export] Instance U_sysret_spec_c : OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_syscalls.sysret_spec_c := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_syscalls.sysret_spec_c_ok.
#[export] Instance U_read_spec_c : OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_syscalls.read_spec_c := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_syscalls.read_spec_c_ok.
#[export] Instance U_close_spec_c : OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_syscalls.close_spec_c := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_syscalls.close_spec_c_ok.
#[export] Instance U_open_spec_c : OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_syscalls.open_spec_c := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_syscalls.open_spec_c_ok.
