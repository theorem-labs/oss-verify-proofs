(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Agree Ceiling.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import InitStack.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Stdio_base Printf_lib Startup RefImpl Stdio_iface RDriver_kit RDriver_ctx.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import H_fuzz_stmt.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim STree Malloc Monad Stdio Driver Prog.
Import ListNotations.
Open Scope Z_scope.

Section IFACE.
  Context {HGW : HasGuard} {HCEIL : HasCeiling}.
  Variables (sp0 : word) (argv : list (list byte)) (TID : Z) (S4 S5 S6 S7 S8 S9 S10 S11 : word).
  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATP).

  Definition CJ1 (mm : mem) : Prop :=
    rw_cells rsegs mm 0x3b6d0 [C1 (Z_to_bv 8 1)]
    /\ rw_cells rsegs mm 0x3b6e0 [CB 16 (repeat (Z_to_bv 8 0) 16)]
    /\ rw_cells rsegs mm 0x2a108 [C8 (Z_to_bv 64 0)]
    /\ GD mm.

  Definition TRFRAME (mm : mem) (pad : list byte) (sc PL A L : Z) : Prop :=
    rw_cells rsegs mm (usp0 + -208)
      [CB 8 pad; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 RSV); C8 (Z_to_bv 64 sc); C8 (Z_to_bv 64 PL); C8 (Z_to_bv 64 (A + 6 + L)); C8 (Z_to_bv 64 L);
       C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 2)); C8 (Z_to_bv 64 0x13c90)].

  Definition rat_parser (ap : at_parser (ptr:=bptr)) (s : PState) (ms : machine_state) : Prop :=
    exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem)
           (A cap L sc AL OW : Z) (DATA junk mpad pad : list byte) (errv : word) (LB : list block),
      ms = MS (mkR x1 (Z_to_bv 64 (usp0 + -208)) gpv tpv t0 t1 t2
                   (Z_to_bv 64 (ap_payload_len ap)) (Z_to_bv 64 AL) a0 a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 OW) (Z_to_bv 64 (A + 2)) (Z_to_bv 64 0x3b6d0) (Z_to_bv 64 (ap_calls ap)) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) S8 S9 S10 S11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x13ea4) fc None mm (seg_rom rsegs)
      /\ frm0 fc

      /\ ap_content ap = map bv_unsigned DATA /\ ap_config_len ap = L /\ ap_count ap = (sc <? 0)
      /\ 1 <= ap_calls ap <= 4
      /\ 6 + L <= Z.of_nat (length DATA) <= cap /\ cap <= MAX_INPUT /\ 0 <= L < 32768 /\ -128 <= sc < 128
      /\ rblock_range A cap
      /\ match ap_owned ap with
         | None => ap_payload_len ap = 0 /\ AL = 0x3b6e0 /\ OW = 0 /\ LB = [(ap_buf ap, A, cap)]
         | Some p => 0 < ap_payload_len ap /\ OW = AL /\ LB = [(p, AL, ap_payload_len ap); (ap_buf ap, A, cap)]
                     /\ rblock_range AL (ap_payload_len ap)
                     /\ rw_cells rsegs mm AL [CB (Z.to_nat (ap_payload_len ap)) (skipn (Z.to_nat (6 + L)) DATA)]
         end

      /\ RHEAP s LB mm /\ ps_so s = stdout_init /\ ps_fa s = (0, 0)
      /\ rw_cells rsegs mm A [CB (length DATA) DATA; CB (Z.to_nat (cap - Z.of_nat (length DATA))) junk]
      /\ TRFRAME mm pad sc (ap_payload_len ap) A L /\ MFRAME sp0 argv mm mpad S7 S6 S5 S4
      /\ stk rsegs mm (usp0 - 8388608) (usp0 + -208)
      /\ mem_inv rsegs mm /\ RSTAT TID mm /\ rauxv_ok mm usp0
      /\ stderr_wfile0 mm /\ stdout_file mm stdout_init
      /\ rw_cells rsegs mm RERRNO [C4 errv]
      /\ CJ1 mm.
End IFACE.
