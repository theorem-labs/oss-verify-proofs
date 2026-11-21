(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (14 recorded proofs replaced by written proofs (RHEAP_ext, RHEAP_perm, rheap_pres_refl and 11 more)). *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocHINV Malloc_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RMallocRep RMallocTree.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RMalloc_iface () := "C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib6Malloc<MallocBlocks5blockC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdI46Stdlib7Sorting;Permutation;Permutation00C59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps4bptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5implMC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes4list00c59OSSVerify5KrLib5Ubsan=RMalloc_iface5RHEAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5stripC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState6ps_brkC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib4Spec6PState4ps_mC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep5rmrepC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01I47Corelib4Init5Logic2eq00C59OSSVerify5KrLib6Malloc:MallocHINV9HINV_fromC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep<ref_reservedC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib4Spec6PState6PState00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree3memC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;PermutationAPermutation_transC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltc59OSSVerify5KrLib5Ubsan=RMalloc_iface<rclient_addrC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewK47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic3notK47Corelib4Init5Logic2eq01c59OSSVerify5KrLib5Ubsan=RMalloc_iface:rheap_presC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib5Ubsan4UImg5usegsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transK47Corelib7Numbers7BinNums8positive01c59OSSVerify5KrLib5Ubsan=RMalloc_iface=ralloc_staticC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<Malloc_iface8in_blockC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C59OSSVerify5KrLib6Malloc<MallocBlocks8blk_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks8blk_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC46Stdlib5Lists4List2InK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c59OSSVerify5KrLib5Ubsan=RMalloc_iface=rclient_rangeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init5Logic5False00C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib5Lists4List9nth_errorC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega7EnvRing5PExpr07c59OSSVerify5KrLib5Ubsan=RMalloc_ifaceBrclient_range_addrC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib3Lib3Mem3mrdC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5CellsBcells_bytes_lengthC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan=RMalloc_ifaceCrheap_pres_bytes_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan=RMalloc_iface@rheap_pres_wr_atC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr5u8arrC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3ArrArw_cells_of_u8arrC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib5Arith8PeanoNat3Nat7add_0_rc59OSSVerify5KrLib5Ubsan=RMalloc_ifaceCrheap_pres_rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3ArrAu8arr_of_rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Image9reservedZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState7ps_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>MMAP_THRESHOLDC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec3evtC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr03K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC59OSSVerify5KrLib3Lib6MState;lift_resultC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_signedC59OSSVerify5KrLib3Lib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib3Lib4StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC45stdpp9bitvector;definitions6bv_addC59OSSVerify5KrLib3Lib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC59OSSVerify5KrLib3Lib6MState8step_genC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbK4ELinuxProcessSemantics5Riscv5Instr5instr05C59OSSVerify5KrLib3Lib6MState;lit_add_litC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv7Prelude4tree00C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init5Logic6eq_symK4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC59OSSVerify5KrLib3Lib6MState;ret_pc_foldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step@Z_to_bv_lit_selfC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC59OSSVerify5KrLib3Lib4Exec8evt_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec8evt_stepC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K47Corelib4Init9Datatypes4prod01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00c59OSSVerify5KrLib5Ubsan=RMalloc_iface9RFREE_SYMC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C4ELinuxProcessSemantics5Riscv3Sem2w0C59OSSVerify5KrLib3Lib6MState6w0_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem2w1C59OSSVerify5KrLib3Lib6MState6w1_litC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan=RMalloc_iface?rfree_null_stmtC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Definition RMALLOC_SYM : Z := 0x21c70.   (* [comment removed for export] *)
Definition RFREE_SYM : Z := 0x21b30.     (* [comment removed for export] *)
Definition RMALLOC_STACK : Z := 8192.
Definition RFREE_STACK : Z := 8192.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ralloc_static (a : Z) : Prop :=
  (RLIBC <= a < RCTX + 928) \/ (RERRNO <= a < RERRNO + 4)
  \/ (RSSP_GUARD <= a < RSSP_GUARD + 8) \/ (RGOT_SSP <= a < RGOT_SSP + 8).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition RHEAP (s : PState) (LB : list block) (m : mem) : Prop :=
  exists st LB0, Permutation.Permutation LB0 LB /\ strip st = ps_m s /\ rmrep st m
                 /\ HINV_from ref_reserved st (ps_brk s) LB0.

Lemma RHEAP_ext : forall s s' LB m, RHEAP s LB m -> ps_m s' = ps_m s -> ps_brk s' = ps_brk s -> RHEAP s' LB m.
Proof. intros s s' LB m (st & LB0 & HP & H1 & H2 & H3) E1 E2. exists st, LB0. rewrite E1, E2. auto 6. Qed.

Lemma RHEAP_perm : forall s LB LB' m, RHEAP s LB m -> Permutation.Permutation LB LB' -> RHEAP s LB' m.
Proof.
  intros s LB LB' m (st & LB0 & HP & H1 & H2 & H3) P. exists st, LB0. split; [|auto].
  eapply Permutation.Permutation_trans; [exact HP| exact P].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rclient_addr (LB : list block) (SP : Z) (a : Z) : Prop :=
  SP <= a \/ (0x2a000 <= a < 0x5d000 /\ ~ ralloc_static a) \/ in_block LB a.

Definition rheap_pres (LB : list block) (SP : Z) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> rclient_addr LB SP a ->
    m' (wa a) = m (wa a) /\ (wview usegs m (wa a) <> None -> wview usegs m' (wa a) <> None).

Lemma rheap_pres_refl : forall LB SP m, rheap_pres LB SP m m.
Proof. intros LB SP m a _ _. auto. Qed.

Lemma rheap_pres_trans : forall LB SP m1 m2 m3,
  rheap_pres LB SP m1 m2 -> rheap_pres LB SP m2 m3 -> rheap_pres LB SP m1 m3.
Proof.
  intros LB SP m1 m2 m3 H1 H2 a Ha Hc. destruct (H1 a Ha Hc) as [E1 W1]. destruct (H2 a Ha Hc) as [E2 W2].
  split; [congruence| auto].
Qed.

Lemma rheap_pres_weaken : forall LB LB' SP SP' m m',
  rheap_pres LB SP m m' -> SP <= SP' -> (forall b, In b LB' -> In b LB) -> rheap_pres LB' SP' m m'.
Proof.
  intros LB LB' SP SP' m m' H HS HL a Ha Hc. apply H; [exact Ha|].
  destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; lia| right; left; exact Hc| right; right].
  exists b. split; [apply HL; exact Hb| exact Hr].
Qed.

(* [comment removed for export] *)
Definition rclient_range (LB : list block) (SP : Z) (A n : Z) : Prop :=
  SP <= A
  \/ (0x2a000 <= A /\ A + n <= 0x5d000 /\ (A + n <= RLIBC \/ RCTX + 928 <= A) /\ (A + n <= RERRNO \/ RERRNO + 4 <= A)
      /\ (A + n <= RSSP_GUARD \/ RSSP_GUARD + 8 <= A) /\ (A + n <= RGOT_SSP \/ RGOT_SSP + 8 <= A))
  \/ (exists b, In b LB /\ blk_addr b <= A /\ A + n <= blk_addr b + blk_size b).

Lemma rclient_range_addr : forall LB SP A n a,
  rclient_range LB SP A n -> A <= a < A + n -> rclient_addr LB SP a.
Proof.
  intros LB SP A n a HR Ha. unfold rclient_range, rclient_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *.
  destruct HR as [H|[H|(b & Hb & H1 & H2)]]; [left; lia| right; left; lia| right; right; exists b; split; [exact Hb|lia]].
Qed.

Lemma rheap_pres_bytes_at : forall LB SP m m' A bs,
  rheap_pres LB SP m m' -> bytes_at usegs m A bs -> rclient_range LB SP A (Z.of_nat (length bs)) ->
  bytes_at usegs m' A bs.
Proof.
  intros LB SP m m' A bs HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(eapply rclient_range_addr; [exact HR|lia])) as [E _].
  rewrite E. reflexivity.
Qed.

Lemma rheap_pres_wr_at : forall LB SP m m' A n,
  rheap_pres LB SP m m' -> wr_at usegs m A n -> rclient_range LB SP A n -> wr_at usegs m' A n.
Proof.
  intros LB SP m m' A n HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(eapply rclient_range_addr; [exact HR|lia])) as [_ W].
  apply W. apply HW. exact Hi.
Qed.

Lemma rheap_pres_rw_cells : forall LB SP m m' A cs,
  rheap_pres LB SP m m' -> rw_cells usegs m A cs -> rclient_range LB SP A (Z.of_nat (cells_size cs)) ->
  rw_cells usegs m' A cs.
Proof.
  intros LB SP m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply rheap_pres_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply rheap_pres_wr_at; eauto.
Qed.

Lemma rheap_pres_u8arr : forall LB SP m m' A xs,
  rheap_pres LB SP m m' -> u8arr usegs m A xs -> rclient_range LB SP A (Z.of_nat (length xs)) ->
  u8arr usegs m' A xs.
Proof.
  intros LB SP m m' A xs HP H HR. apply (u8arr_of_rw_cells usegs m' A (length xs)).
  eapply rheap_pres_rw_cells; [exact HP| apply rw_cells_of_u8arr; exact H|].
  cbn [cells_size csize]. rewrite Nat.add_0_r. exact HR.
Qed.

Lemma rheap_pres_stk : forall LB SP m m' lo hi,
  rheap_pres LB SP m m' -> stk usegs m lo hi -> SP <= lo -> stk usegs m' lo hi.
Proof.
  intros LB SP m m' lo hi HP ST HS. destruct ST as (H0 & H1 & HW). split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP i ltac:(lia) ltac:(left; lia)) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
  split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rblock_range (A n : Z) : Prop :=
  0 < A /\ A mod 16 = 0 /\ 0 <= n /\ A + n <= ATOP /\ (A + n <= 0x10000 \/ 0x5d000 <= A).

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition rclient_write_ok (LB : list block) (iv : Z * Z) : Prop :=
  ATOP <= fst iv
  \/ (0x2a000 <= fst iv /\ snd iv <= 0x5d000 /\ (snd iv <= RLIBC \/ RCTX + 928 <= fst iv)
      /\ (snd iv <= RSSP_GUARD \/ RSSP_GUARD + 8 <= fst iv) /\ (snd iv <= RGOT_SSP \/ RGOT_SSP + 8 <= fst iv))
  \/ (exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b).


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition raddr_exposed (s : PState) (n : Z) : Prop :=
  MMAP_THRESHOLD <= n \/ ps_m s = ps_m (ps_init (reservedZ usegs) ATOP).

Lemma raddr_exposed_big : forall s n, MMAP_THRESHOLD <= n -> raddr_exposed s n.
Proof. intros; left; assumption. Qed.
Lemma raddr_exposed_init : forall s n, ps_m s = ps_m (ps_init (reservedZ usegs) ATOP) -> raddr_exposed s n.
Proof. intros; right; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rmalloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (n lo B : Z) (m : mem)
    (r : option bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 errv']
    /\ rauxv_ok m' B
    /\ rheap_pres LB (bv_unsigned sp) m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ match r with
       | None => a0 = Z_to_bv 64 0 /\ RHEAP s' LB m'
       | Some p => exists A junk,
           a0 = Z_to_bv 64 A /\ rblock_range A n
           /\ RHEAP s' ((p, A, n) :: LB) m'
           /\ rw_cells usegs m' A [CB (Z.to_nat n) junk]
           /\ (raddr_exposed s n -> A = ptr_addr s' p)
       end.

Definition rmalloc_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (n lo B : Z) (errv : word),
  RHEAP s LB m ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk usegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RMALLOC_STACK ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  implM usegs (raw_malloc n) s
        (rmalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RMALLOC_SYM) fc None m (seg_rom usegs)).

Definition rfree_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (p : bptr) (lo B : Z) (errv : word) (m : mem)
    (r : unit) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 errv]          (* [comment removed for export] *)
    /\ rauxv_ok m' B
    /\ rheap_pres (lb_remove p LB) (bv_unsigned sp) m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ RHEAP s' (lb_remove p LB) m'.

Definition rfree_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (p : bptr) (A n lo B : Z) (errv : word),
  RHEAP s LB m -> In (p, A, n) LB ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk usegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RFREE_STACK ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 A ->
  implM usegs (raw_free p) s
        (rfree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p lo B errv m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RFREE_SYM) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
Definition rfree_null_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  a0 = Z_to_bv 64 0 ->
  evt usegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m (seg_rom usegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RFREE_SYM) fc None m (seg_rom usegs)).

Lemma rfree_null_spec : rfree_null_stmt.
Proof.
  intros until m. intros ->. unfold RFREE_SYM.
  step. step. if_true. step. apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End CANSEC1.
