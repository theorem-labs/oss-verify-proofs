(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import MallocHINV Malloc_iface.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RMallocRep RMallocTree.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import ProgDeps.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Section CANSEC1. Context {rc : runConstT}.
Definition RMALLOC_SYM : Z := 0x152f4.
Definition RFREE_SYM : Z := 0x151b4.
Definition RMALLOC_STACK : Z := 8192.
Definition RFREE_STACK : Z := 8192.
Definition ralloc_static (a : Z) : Prop :=
(RLIBC <= a < RCTX + 928) \/ (RERRNO <= a < RERRNO + 4)
\/ (RSSP_GUARD <= a < RSSP_GUARD + 8) \/ (RGOT_SSP <= a < RGOT_SSP + 8).
Definition RHEAP (s : PState) (LB : list block) (m : mem) : Prop :=
exists st LB0, Permutation.Permutation LB0 LB /\ strip st = ps_m s /\ rmrep st m
/\ HINV_from ref_reserved st (ps_brk s) LB0.
#[using="Type"] Lemma RHEAP_ext : forall s s' LB m, RHEAP s LB m -> ps_m s' = ps_m s -> ps_brk s' = ps_brk s -> RHEAP s' LB m.
Proof. intros s s' LB m (st & LB0 & HP & H1 & H2 & H3) E1 E2. exists st, LB0. rewrite E1, E2. auto 6. Qed.
Definition rclient_addr (LB : list block) (SP : Z) (a : Z) : Prop :=
SP <= a \/ (0x1d000 <= a < 0x50000 /\ ~ ralloc_static a) \/ in_block LB a.
Definition rheap_pres (LB : list block) (SP : Z) (m m' : mem) : Prop :=
forall a, 0 <= a < 2^64 -> rclient_addr LB SP a ->
m' (wa a) = m (wa a) /\ (wview usegs m (wa a) <> None -> wview usegs m' (wa a) <> None).
#[using="Type"] Lemma rheap_pres_trans : forall LB SP m1 m2 m3,
rheap_pres LB SP m1 m2 -> rheap_pres LB SP m2 m3 -> rheap_pres LB SP m1 m3.
Proof.
intros LB SP m1 m2 m3 H1 H2 a Ha Hc. destruct (H1 a Ha Hc) as [E1 W1]. destruct (H2 a Ha Hc) as [E2 W2].
split; [congruence| auto].
Qed.
#[using="Type"] Lemma rheap_pres_weaken : forall LB LB' SP SP' m m',
rheap_pres LB SP m m' -> SP <= SP' -> (forall b, In b LB' -> In b LB) -> rheap_pres LB' SP' m m'.
Proof.
intros LB LB' SP SP' m m' H HS HL a Ha Hc. apply H; [exact Ha|].
Local Ltac2 Set LiaHints.tbl := fun () => "0010>37275289936.13000007S2HS2Hc".
destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; lia| right; left; exact Hc| right; right].
exists b. split; [apply HL; exact Hb| exact Hr].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition rclient_range (LB : list block) (SP : Z) (A n : Z) : Prop :=
SP <= A
\/ (0x1d000 <= A /\ A + n <= 0x50000 /\ (A + n <= RLIBC \/ RCTX + 928 <= A) /\ (A + n <= RERRNO \/ RERRNO + 4 <= A)
/\ (A + n <= RSSP_GUARD \/ RSSP_GUARD + 8 <= A) /\ (A + n <= RGOT_SSP \/ RGOT_SSP + 8 <= A))
\/ (exists b, In b LB /\ blk_addr b <= A /\ A + n <= blk_addr b + blk_size b).
#[using="Type"] Lemma rclient_range_addr : forall LB SP A n a,
rclient_range LB SP A n -> A <= a < A + n -> rclient_addr LB SP a.
Proof.
intros LB SP A n a HR Ha. unfold rclient_range, rclient_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *.
Local Ltac2 Set LiaHints.tbl := fun () => "0030>32162264840.8 37275290198.8 68189514523.1100000600<00FS1H2HaS1H2HaS2H12H22Ha".
destruct HR as [H|[H|(b & Hb & H1 & H2)]]; [left; lia| right; left; lia| right; right; exists b; split; [exact Hb|lia]].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rheap_pres_bytes_at : forall LB SP m m' A bs,
rheap_pres LB SP m m' -> bytes_at usegs m A bs -> rclient_range LB SP A (Z.of_nat (length bs)) ->
bytes_at usegs m' A bs.
Proof.
intros LB SP m m' A bs HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
intros i Hi. rewrite <- (HB i Hi). unfold mrd.
destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(eapply rclient_range_addr; [exact HR|lia])) as [E _].
rewrite E. reflexivity.
Qed.
#[using="Type"] Lemma rheap_pres_wr_at : forall LB SP m m' A n,
rheap_pres LB SP m m' -> wr_at usegs m A n -> rclient_range LB SP A n -> wr_at usegs m' A n.
Proof.
intros LB SP m m' A n HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(eapply rclient_range_addr; [exact HR|lia])) as [_ W].
apply W. apply HW. exact Hi.
Qed.
#[using="Type"] Lemma rheap_pres_rw_cells : forall LB SP m m' A cs,
rheap_pres LB SP m m' -> rw_cells usegs m A cs -> rclient_range LB SP A (Z.of_nat (cells_size cs)) ->
rw_cells usegs m' A cs.
Proof.
intros LB SP m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
- eapply rheap_pres_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
- eapply rheap_pres_wr_at; eauto.
Qed.
#[using="Type"] Lemma rheap_pres_u8arr : forall LB SP m m' A xs,
rheap_pres LB SP m m' -> u8arr usegs m A xs -> rclient_range LB SP A (Z.of_nat (length xs)) ->
u8arr usegs m' A xs.
Proof.
intros LB SP m m' A xs HP H HR. apply (u8arr_of_rw_cells usegs m' A (length xs)).
eapply rheap_pres_rw_cells; [exact HP| apply rw_cells_of_u8arr; exact H|].
cbn [cells_size csize]. rewrite Nat.add_0_r. exact HR.
Qed.
#[using="Type"] Lemma rheap_pres_stk : forall LB SP m m' lo hi,
rheap_pres LB SP m m' -> stk usegs m lo hi -> SP <= lo -> stk usegs m' lo hi.
Proof.
intros LB SP m m' lo hi HP ST HS. destruct ST as (H0 & H1 & HW). split; [exact H0|]. split; [exact H1|].
intros i Hi. destruct (HP i ltac:(lia) ltac:(left; lia)) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.
Definition rblock_range (A n : Z) : Prop :=
0 < A /\ A mod 16 = 0 /\ 0 <= n /\ A + n <= ATOP /\ (A + n <= 0x10000 \/ 0x50000 <= A).
Definition rclient_write_ok (LB : list block) (iv : Z * Z) : Prop :=
ATOP <= fst iv
\/ (0x1d000 <= fst iv /\ snd iv <= 0x50000 /\ (snd iv <= RLIBC \/ RCTX + 928 <= fst iv)
/\ (snd iv <= RSSP_GUARD \/ RSSP_GUARD + 8 <= fst iv) /\ (snd iv <= RGOT_SSP \/ RGOT_SSP + 8 <= fst iv))
\/ (exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b).
Definition raddr_exposed (s : PState) (n : Z) : Prop :=
MMAP_THRESHOLD <= n \/ ps_m s = ps_m (ps_init (reservedZ usegs) ATOP).
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
/\ rw_cells usegs m' (errno_addr tp) [C4 errv]
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
Definition rfree_null_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
a0 = Z_to_bv 64 0 ->
evt usegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom usegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RFREE_SYM) fc None m (seg_rom usegs)).
#[using="Type"] Lemma rfree_null_spec : rfree_null_stmt.
Proof.
intros until m. intros ->. unfold RFREE_SYM.
step. step. if_true. step. apply evt_done. reflexivity.
Qed.
End CANSEC1.
