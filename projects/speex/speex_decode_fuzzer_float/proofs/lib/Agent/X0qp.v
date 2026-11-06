(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8 X1bs X1c2 X1bn X1bj.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0ok.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pu X0qm X0qc X0qn.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv X1qx X1r3.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.

Definition AGP : Z := 0x1a800.
Definition ATP : Z := 0x1a620.
Definition ERRNO : Z := ATP - 164.
Definition MALLOC_SYM : Z := 0x1596c.
Definition FREE_SYM : Z := 0x156e0.
Definition MALLOC_STACK : Z := 8192.
Definition FREE_STACK : Z := 8192.

Definition MEDTAB : Z := 0x1a060.
Definition alloc_static (a : Z) : Prop :=
(MLOCK <= a < MLOCK + 4) \/ (LIBC <= a < CTX + 928) \/ (ERRNO <= a < ERRNO + 4) \/ (MEDTAB <= a < MEDTAB + 4).

Definition medtab_cells : list cell := [C1 (Z_to_bv 8 28); C1 (Z_to_bv 8 24); C1 (Z_to_bv 8 20); C1 (Z_to_bv 8 32)].

Definition HEAP {RCEIL : RunCeiling} (s : PState) (LB : list block) (m : mem) : Prop :=
exists st LB0, Permutation.Permutation LB0 LB /\ strip st = ps_m s /\ mrep st m /\ HINV st (ps_brk s) LB0
/\ rw_cells asegs m MEDTAB medtab_cells.

Lemma HEAP_ext {RCEIL : RunCeiling} : forall s s' LB m, HEAP s LB m -> ps_m s' = ps_m s -> ps_brk s' = ps_brk s -> HEAP s' LB m.
Proof. intros s s' LB m sfH_; first [ sf_destruct 7%nat sfH_ as st LB0 HP H1 H2 H3 H4 | sf_fb; destruct sfH_ as (st & LB0 & HP & H1 & H2 & H3 & H4) ]; intros E1 E2. exists st, LB0. rewrite E1, E2. auto 6. Qed.

Definition in_block (LB : list block) (a : Z) : Prop :=
exists b, In b LB /\ blk_addr b <= a < blk_addr b + blk_size b.

Definition client_addr (LB : list block) (SP : Z) (a : Z) : Prop :=
SP <= a \/ (0x19000 <= a < 0x1b000 /\ ~ alloc_static a) \/ in_block LB a.

Definition heap_pres (LB : list block) (SP : Z) (m m' : mem) : Prop :=
forall a, 0 <= a < 2^64 -> client_addr LB SP a ->
m' (wa a) = m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None).

Lemma heap_pres_refl : forall LB SP m, heap_pres LB SP m m.
Proof. intros LB SP m a _ _. auto. Qed.

Lemma heap_pres_trans : forall LB SP m1 m2 m3,
heap_pres LB SP m1 m2 -> heap_pres LB SP m2 m3 -> heap_pres LB SP m1 m3.
Proof.
intros LB SP m1 m2 m3 H1 H2 a Ha Hc. destruct (H1 a Ha Hc) as [E1 W1]. destruct (H2 a Ha Hc) as [E2 W2].
split; [congruence| auto].
Qed.

Lemma heap_pres_weaken : forall LB LB' SP SP' m m',
heap_pres LB SP m m' -> SP <= SP' -> (forall b, In b LB' -> In b LB) -> heap_pres LB' SP' m m'.
Proof.
intros LB LB' SP SP' m m' H HS HL a Ha Hc. apply H; [exact Ha|].
destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; lia| right; left; exact Hc| right; right].
exists b. split; [apply HL; exact Hb| exact Hr].
Qed.

Definition client_range (LB : list block) (SP : Z) (A n : Z) : Prop :=
SP <= A
\/ (0x19000 <= A /\ A + n <= 0x1b000 /\ (A + n <= MLOCK \/ MLOCK + 4 <= A) /\ (A + n <= LIBC \/ CTX + 928 <= A)
/\ (A + n <= ERRNO \/ ERRNO + 4 <= A) /\ (A + n <= MEDTAB \/ MEDTAB + 4 <= A))
\/ (exists b, In b LB /\ blk_addr b <= A /\ A + n <= blk_addr b + blk_size b).

Lemma client_range_addr : forall LB SP A n a,
client_range LB SP A n -> A <= a < A + n -> client_addr LB SP a.
Proof.
intros LB SP A n a HR Ha. unfold client_range, client_addr, alloc_static, MLOCK, LIBC, CTX, ERRNO, ATP, MEDTAB in *.
destruct HR as [H|[H|(b & Hb & H1 & H2)]]; [left; lia| right; left; lia| right; right; exists b; split; [exact Hb|lia]].
Qed.

Lemma heap_pres_bytes_at : forall LB SP m m' A bs,
heap_pres LB SP m m' -> bytes_at asegs m A bs -> client_range LB SP A (Z.of_nat (length bs)) ->
bytes_at asegs m' A bs.
Proof.
intros LB SP m m' A bs HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
intros i Hi. rewrite <- (HB i Hi). unfold mrd.
destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(eapply client_range_addr; [exact HR|lia])) as [E _].
rewrite E. reflexivity.
Qed.

Lemma heap_pres_wr_at : forall LB SP m m' A n,
heap_pres LB SP m m' -> wr_at asegs m A n -> client_range LB SP A n -> wr_at asegs m' A n.
Proof.
intros LB SP m m' A n HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(eapply client_range_addr; [exact HR|lia])) as [_ W].
apply W. apply HW. exact Hi.
Qed.

Lemma heap_pres_rw_cells : forall LB SP m m' A cs,
heap_pres LB SP m m' -> rw_cells asegs m A cs -> client_range LB SP A (Z.of_nat (cells_size cs)) ->
rw_cells asegs m' A cs.
Proof.
intros LB SP m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
- eapply heap_pres_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
- eapply heap_pres_wr_at; eauto.
Qed.

Lemma heap_pres_u8arr : forall LB SP m m' A xs,
heap_pres LB SP m m' -> u8arr asegs m A xs -> client_range LB SP A (Z.of_nat (length xs)) ->
u8arr asegs m' A xs.
Proof.
intros LB SP m m' A xs HP H HR. apply (u8arr_of_rw_cells asegs m' A (length xs)).
eapply heap_pres_rw_cells; [exact HP| apply rw_cells_of_u8arr; exact H|].
cbn [cells_size csize]. rewrite Nat.add_0_r. exact HR.
Qed.

Lemma heap_pres_stk : forall LB SP m m' lo hi,
heap_pres LB SP m m' -> stk asegs m lo hi -> SP <= lo -> stk asegs m' lo hi.
Proof.
intros LB SP m m' lo hi HP ST HS. destruct ST as (H0 & H1 & HW). split; [exact H0|]. split; [exact H1|].
intros i Hi. destruct (HP i ltac:(lia) ltac:(left; lia)) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

Definition block_range {RCEIL : RunCeiling} (A n : Z) : Prop :=
0 < A /\ A mod 16 = 0 /\ 0 <= n /\ A + n <= alloc_ceiling /\ (A + n <= 0x10000 \/ 0x1b000 <= A).

Definition client_write_ok {RCEIL : RunCeiling} (LB : list block) (iv : Z * Z) : Prop :=
alloc_ceiling <= fst iv
\/ (0x19000 <= fst iv /\ snd iv <= 0x1b000 /\ (snd iv <= MLOCK \/ MLOCK + 4 <= fst iv) /\ (snd iv <= LIBC \/ CTX + 928 <= fst iv)
/\ (snd iv <= ERRNO \/ ERRNO + 4 <= fst iv) /\ (snd iv <= MEDTAB \/ MEDTAB + 4 <= fst iv))
\/ (exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b).

Lemma HEAP_perm {RCEIL : RunCeiling} : forall s LB LB' m, HEAP s LB m -> Permutation.Permutation LB LB' -> HEAP s LB' m.
Proof.
intros s LB LB' m sfH_; first [ sf_destruct 7%nat sfH_ as st LB0 HP H1 H2 H3 H4 | sf_fb; destruct sfH_ as (st & LB0 & HP & H1 & H2 & H3 & H4) ]; intros P. exists st, LB0. split; [|auto].
eapply Permutation.Permutation_trans; [exact HP| exact P].
Qed.

Definition addr_exposed {RCEIL : RunCeiling} (s : PState) (n : Z) : Prop :=
MMAP_THRESHOLD <= n \/ ps_m s = ps_m (ps_init alloc_ceiling (reservedZ asegs)).

Lemma addr_exposed_big {RCEIL : RunCeiling} : forall s n, MMAP_THRESHOLD <= n -> addr_exposed s n.
Proof. intros; left; assumption. Qed.
Lemma addr_exposed_init {RCEIL : RunCeiling} : forall s n, ps_m s = ps_m (ps_init alloc_ceiling (reservedZ asegs)) -> addr_exposed s n.
Proof. intros; right; assumption. Qed.

Definition bptr_eqb (p q : bptr) : bool :=
aptr_eqb (fst p) (fst q) && Z.eqb (snd p) (snd q).

Definition lb_remove (p : bptr) (LB : list block) : list block :=
filter (fun b => negb (bptr_eqb (blk_id b) p)) LB.

Definition malloc_post {RCEIL : RunCeiling} (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PState) (LB : list block) (n lo B : Z) (m : mem)
(r : option bptr) (s' : PState) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' (errno_addr tp) [C4 errv']
/\ auxv_ok m' B
/\ heap_pres LB (bv_unsigned sp) m m'
/\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
/\ match r with
| None => a0 = Z_to_bv 64 0 /\ HEAP s' LB m'
| Some p => exists A junk,
a0 = Z_to_bv 64 A /\ block_range A n
/\ HEAP s' ((p, A, n) :: LB) m'
/\ rw_cells asegs m' A [CB (Z.to_nat n) junk]
/\ (addr_exposed s n -> A = ptr_addr s' p)
end.

Definition malloc_stmt {RCEIL : RunCeiling} : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (n lo B : Z) (errv : word),
HEAP s LB m ->
auxv_ok m B -> bv_unsigned sp <= B ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - MALLOC_STACK ->
rw_cells asegs m (errno_addr tp) [C4 errv] ->
mem_inv asegs m ->
gp = Z_to_bv 64 AGP -> tp = Z_to_bv 64 ATP ->
a0 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
implM asegs (raw_malloc n) s
(malloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 MALLOC_SYM) fc None m (seg_rom asegs)).

Definition free_post {RCEIL : RunCeiling} (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PState) (LB : list block) (p : bptr) (lo B : Z) (errv : word) (m : mem)
(r : unit) (s' : PState) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' (errno_addr tp) [C4 errv]
/\ auxv_ok m' B
/\ heap_pres (lb_remove p LB) (bv_unsigned sp) m m'
/\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
/\ HEAP s' (lb_remove p LB) m'.

Definition free_stmt {RCEIL : RunCeiling} : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (p : bptr) (A n lo B : Z) (errv : word),
HEAP s LB m -> In (p, A, n) LB ->
auxv_ok m B -> bv_unsigned sp <= B ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - FREE_STACK ->
rw_cells asegs m (errno_addr tp) [C4 errv] ->
mem_inv asegs m ->
gp = Z_to_bv 64 AGP -> tp = Z_to_bv 64 ATP ->
a0 = Z_to_bv 64 A ->
implM asegs (raw_free p) s
(free_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p lo B errv m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 FREE_SYM) fc None m (seg_rom asegs)).

Definition free_null_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
a0 = Z_to_bv 64 0 ->
evt asegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom asegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 FREE_SYM) fc None m (seg_rom asegs)).

