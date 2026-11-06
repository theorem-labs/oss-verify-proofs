(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg StdioFiles.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Malloc Monad Stdio Harness Prog.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Harness_iface () := "C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00c59OSSVerify5KrLib5Plain=Harness_iface<stderr_file0C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib5Plain:StdioFiles:file_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib6Malloc9MallocRep2wzC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6repeatK47Corelib4Init5Logic2ex01K47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib5Plain4PImg5psegsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes3nat01".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition PFUZZ_ENTRY : Z := 0x131d0.    (* [comment removed for export] *)
Definition PEMPTY : Z := 0x37740.         (* [comment removed for export] *)
Definition PGOT_STDERR : Z := 0x26470.    (* [comment removed for export] *)
Definition PSTDERR_PTR : Z := 0x26420.    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition HARNESS_STACK : Z := 16384.

(* [comment removed for export] *)
Definition harness_cells (m : mem) : Prop :=
  rw_cells psegs m PGOT_STDERR [C8 (wz PSTDERR_PTR)]
  /\ rw_cells psegs m PSTDERR_PTR [C8 (wz RSTDERR)].

(* [comment removed for export] *)
Definition stderr_file0 (m : mem) : Prop :=
  rw_cells psegs m RSTDERR (file_cells (Z_to_bv 64 5) 0 0 0 F_STDIO_WRITE RSTDERR_BUF 0 2 (wz 0) 0xffffffff (repeat (Z_to_bv 8 0) 80)).

Lemma stderr_file0_file : forall m, stderr_file0 m -> stderr_file m.
Proof.
ltac2:(KReplay.run1 (kr_t_Harness_iface ()) ["CANSEC1"] "h04tailh14wendh21eh34modeh41Hh55flagsh61mp;1p;;p;4p;2p;3p10000p4p70p1000ep4p710R0p8p1001Vp4p70P0p8g002Kj15Tg0030j1=Tg003Nj1<Tg0041j1CTg004Sj1ATg005Xj1?Tg0068j11Tg006]j16Tg007;l;7Tg008;j49Tg0091j24Tg009Kj2>Tg00:1j1BTg00:ij3@Tg00;Hj4;Tg00;bj10Tf0R0#5#5p=2%10#1p=8%10#1#1#1p=3%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=:g00<AR1#5R2#2R3#5#2#=R4#<R5%=3R3#<R6#C[%A0P5g00<fR7%?6R8g00=DR9f6%21#1#8#5#1#2#3#2#2#6R:f4R;f1R<f2R=P=%11#8#3#5#2#1#8#5#2#6R>%51#1#5#1#8#3#2#2#2#2#6R?g00>9R@%62RAf3RB%11#8#3#3#3#3#3#3#3#6R1P0M;7C9X08'4X17,47X27'4X35,45X55%12#6,>4R4P5P9f5P:P4P<P=P=P>P?P@PAPBP1P0M;7C9X08,48X17,47X27,47X35%B@R5P7P9P;P:P4P<P=P=P>P?P@PAP5P1P0M;7C9X08,48X17,47X27P@P7P9PBP:P4P<P@P@P>P?P@PAP5P1P0M;7C9X08,48X17P@P8P9P=P:P4P@P@P@P>P?P@PAP5P1P0M;7C9X081>3@g00>W#:#:#:#:#:5@6P0C;C;C;C;C;W4W6o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FuzzOne.
  (* [comment removed for export] *)

  Definition fuzz_one_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (s : PState) (LB : list block) (AB lo : Z) (m : mem)
      (r : Z) (s' : PState) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (errv' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None m' (seg_rom psegs)
      /\ -2^31 <= r < 2^31
      /\ mem_inv psegs m' /\ frm0 fc'
      /\ stk psegs m' lo (bv_unsigned sp)
      /\ rw_cells psegs m' (errno_addr tp) [C4 errv']
      /\ rauxv_ok m' AB
      /\ rheap_pres LB (bv_unsigned sp) m m'
      /\ RHEAP s' LB m'
      /\ ps_so s' = ps_so s.

  Definition fuzz_one_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem)
           (s : PState) (LB : list block) (D : Z) (payload : list Z) (AB lo : Z) (errv : word),
      RHEAP s LB m ->
      (* [comment removed for export] *)
      bytes_at psegs m D (map (Z_to_bv 8) payload) -> Forall (fun c => 0 <= c < 256) payload ->
      rclient_range LB (bv_unsigned sp) D (zlength payload) ->
      D mod 16 = 0 -> 0 < D -> D + zlength payload <= ATOP -> zlength payload < 2^26 ->
      (* [comment removed for export] *)
      harness_cells m -> stderr_file0 m ->
      (* [comment removed for export] *)
      rauxv_ok m AB -> bv_unsigned sp <= AB -> AB <= 2^47 ->      (* [comment removed for export] *)
      stk psegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - HARNESS_STACK ->
      rw_cells psegs m (errno_addr tp) [C4 errv] ->
      mem_inv psegs m -> frm0 fc ->
      tp = wz RATP -> bv_unsigned sp mod 16 = 0 ->
      a0 = wz D -> a1 = wz (zlength payload) ->
      implM psegs (Prog.fuzz_one payload) s
            (fuzz_one_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB AB lo m)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (wz PFUZZ_ENTRY) fc None m (seg_rom psegs)).
End FuzzOne.
End CANSEC1.
