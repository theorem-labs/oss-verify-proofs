(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocHINV Malloc_iface.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt Require Import RMallocRep RMallocTree.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Tgt_RMalloc_iface () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocBlocks."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Arr."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Prog."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMalloc_iface.CEIL_WRAP_1."; "Stdlib.Lists.List."; "Stdlib.Sorting.Permutation."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1length"; "1list"; "2and"; "2eq"; "3Z"; "0LB"; "0LB'"; "0RUNp"; "4block"; "5mem"; "6u8arr"; "7cell"; "7cells_size"; "8stk"; "9bytes_at"]; ["9wr_at"; ":rw_cells"; ";MMAP_THRESHOLD"; ";mstate"; "<PState"; "<ps_brk"; "<ps_init"; "<ps_m"; "<reservedZ"; "=rsegs"; ">RHEAP"; ">raddr_exposed"; ">rclient_addr"; ">rclient_range"; ">rfree_null_stmt"; ">rheap_pres"]; ["0SP"; "0SP'"; "?In"; "@Permutation"; "Aadd"; "Ale"; "Alt"; "Aof_nat"; "0a"; "0b"; "0bs"; "0cs"; "0hi"; "0lo"; "0m"; "0m'"]; ["0m1"; "0m2"; "0m3"; "0n"; "0s"; "0s'"; "Bbv"; "0xs"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition RMALLOC_SYM : Z := 0x9bb08.
Definition RFREE_SYM : Z := 0x9b9c8.
Definition RMALLOC_STACK : Z := 8192.
Definition RFREE_STACK : Z := 8192.
Definition ralloc_static (a : Z) : Prop :=
(RLIBC <= a < RCTX + 928) \/ (RERRNO <= a < RERRNO + 4)
\/ (RSSP_GUARD <= a < RSSP_GUARD + 8) \/ (RGOT_SSP <= a < RGOT_SSP + 8)
\/ (RVMLOCKC <= a < RVMLOCKC + 4).
Definition RHEAP (s : PState) (LB : list block) (m : mem) : Prop :=
exists st LB0, Permutation.Permutation LB0 LB /\ strip st = ps_m s /\ rmrep st m
/\ HINV_from ref_reserved st (ps_brk s) LB0.
Lemma RHEAP_ext : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMalloc_iface "O'D'2&9%211&:&Jr4r2r1%43321'4'C&G%117r5%311%63531'5&E%115r6%311%<3531%B339Ap021p091p0A1pRNG1p>I1pS<M1pS:N1").
Proof. intros s s' LB m (st & LB0 & HP & H1 & H2 & H3) E1 E2. exists st, LB0. rewrite E1, E2. auto 6. Qed.
Lemma RHEAP_perm : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMalloc_iface "D'D'2&9%211&:&Jr4r3r1%43321'Q3%13954r6%83176p031p061pRN<1p@>1p>?1pS:C1").
Proof.
intros s LB LB' m (st & LB0 & HP & H1 & H2 & H3) P. exists st, LB0. split; [|auto].
eapply Permutation.Permutation_trans; [exact HP| exact P].
Qed.
Definition rclient_addr (LB : list block) (SP : Z) (a : Z) : Prop :=
SP <= a \/ (0xb0000 <= a < 0xea000 /\ ~ ralloc_static a) \/ in_block LB a.
Definition rheap_pres (LB : list block) (SP : Z) (m m' : mem) : Prop :=
forall a, 0 <= a < 2^64 -> rclient_addr LB SP a ->
m' (wa a) = m (wa a) /\ (wview rsegs m (wa a) <> None -> wview rsegs m' (wa a) <> None).
Lemma rheap_pres_refl : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMalloc_iface "='2&9%211'5&:&Or3r2r1%443211pRN61pR281p>:1").
Proof. intros LB SP m a _ _. auto. Qed.
Lemma rheap_pres_trans : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMalloc_iface "F'2&9%211'5&:&Or5r4r3r2%544321r6%741643r7%941386p031p061pS6=1pS4>1pS2?1pR2A1p>C1").
Proof.
intros LB SP m1 m2 m3 H1 H2 a Ha Hc. destruct (H1 a Ha Hc) as [E1 W1]. destruct (H2 a Ha Hc) as [E2 W2].
split; [congruence| auto].
Qed.
Lemma rheap_pres_weaken : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMalloc_iface "O'2&9%211'5&:&Or6r4r2r1%544321&Q5r5%2216&Q2r8%23?71r:%43A:1p031pRDC1%@46?9>p021p0:1p0>1pS0E1pRNF1pR4H1pR2I1p@K1p>L1").
Proof.
intros LB LB' SP SP' m m' H HS HL a Ha Hc. apply H; [exact Ha|].
destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; lia| right; left; exact Hc| right; right].
exists b. split; [apply HL; exact Hb| exact Hr].
Qed.
Definition rclient_range (LB : list block) (SP : Z) (A n : Z) : Prop :=
SP <= A
\/ (0xb0000 <= A /\ A + n <= 0xea000 /\ (A + n <= RLIBC \/ RCTX + 928 <= A) /\ (A + n <= RERRNO \/ RERRNO + 4 <= A)
/\ (A + n <= RSSP_GUARD \/ RSSP_GUARD + 8 <= A) /\ (A + n <= RGOT_SSP \/ RGOT_SSP + 8 <= A)
/\ (A + n <= RVMLOCKC \/ RVMLOCKC + 4 <= A))
\/ (exists b, In b LB /\ blk_addr b <= A /\ A + n <= blk_addr b + blk_size b).
Section SE.
Local Abbreviation SEC_T_rclient_range_addr := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMalloc_iface "M'2&9%211'5&Mr5r4r3r2%544321'3&Q5%1264&Q6&Q4%1298%3281%7251&Lr7r6%3321>p051p0>1pRBE1pS8F1p2G1pR2H1p>J1")) (only parsing).
Variable LB : ltac:(sec_ty2 constr:(SEC_T_rclient_range_addr) 0%nat 0%nat).
Variable SP : ltac:(sec_ty2 constr:(SEC_T_rclient_range_addr) 1%nat 0%nat).
Variable A : ltac:(sec_ty2 constr:(SEC_T_rclient_range_addr) 2%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_rclient_range_addr) 3%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SEC_T_rclient_range_addr) 4%nat 0%nat).
Lemma rclient_range_addr : ltac:(sec_stmt2 constr:(SEC_T_rclient_range_addr) 5%nat 0%nat).
Proof.
intros HR Ha.
unfold rclient_range, rclient_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *.
destruct HR as [H|[H|(b & Hb & H1 & H2)]]; [left; lia| right; left; lia| right; right; exists b; split; [exact Hb|lia]].
Qed.
End SE.
Lemma rheap_pres_bytes_at : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMalloc_iface "Q5'2&9%211'5&:'QFy8%211%811&Or6r5r4r3%544321&?&Ir2%342751&Mr8r7&Q7&1%12A;%311%7465>1%<4;A@?p021p0;1p0@1pRFG1p2M1pS0M1pRNN1pR2Q01p>Q21").
Proof.
intros LB SP m m' A bs HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
intros i Hi. rewrite <- (HB i Hi). unfold mrd.
destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(eapply rclient_range_addr; [exact HR|lia])) as [E _].
rewrite E. reflexivity.
Qed.
Lemma rheap_pres_wr_at : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMalloc_iface "M'2&9%211'5&:&Or6r5r4r3%544321&@&Ir2%342751&Mr8r7%3421:9%847=<;p021p071p0<1pS8D1p2E1pS0E1pRNF1pR2H1p>J1").
Proof.
intros LB SP m m' A n HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(eapply rclient_range_addr; [exact HR|lia])) as [_ W].
apply W. apply HW. exact Hi.
Qed.
Lemma rheap_pres_rw_cells : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMalloc_iface "Q3'2&9%211'5&:'<%611&Or6r5r4r3%544321&A&Ir2%342751&Mr8r7&Q7&=%11;%311%7465>1%<4;A@?p021p0;1p0@1pRHG1p2K1pS0K1pRNL1pR2N1p>Q01").
Proof.
intros LB SP m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
- eapply rheap_pres_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
- eapply rheap_pres_wr_at; eauto.
Qed.
Lemma rheap_pres_u8arr : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMalloc_iface "Q5'2&9%211'5&:'QFy8%211%811&Or6r5r4r3%544321&;&Ir2%342751&Mr8r7&Q7&1%12A;%311%7465>1%<4;A@?p021p0;1p0@1pS@G1p2M1pS0M1pRNN1pR2Q01p>Q21").
Proof.
intros LB SP m m' A xs HP H HR. apply (u8arr_of_rw_cells rsegs m' A (length xs)).
eapply rheap_pres_rw_cells; [exact HP| apply rw_cells_of_u8arr; exact H|].
cbn [cells_size csize]. rewrite Nat.add_0_r. exact HR.
Qed.
Lemma rheap_pres_stk : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMalloc_iface "L'2&9%211'5&:&Or6r5r4r3%544321&>&Ir2%342751&Q5r7%2219%746<;:p021p061p0;1pRJC1pRLD1pS0D1pRNE1pR2G1p>I1").
Proof.
intros LB SP m m' lo hi HP ST HS. destruct ST as (H0 & H1 & HW). split; [exact H0|]. split; [exact H1|].
intros i Hi. destruct (HP i ltac:(lia) ltac:(left; lia)) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.
Definition rblock_range (A n : Z) : Prop :=
0 < A /\ A mod 16 = 0 /\ 0 <= n /\ A + n <= alloc_ceiling /\ (A + n <= 0x10000 \/ 0xea000 <= A).
Definition rclient_write_ok (LB : list block) (iv : Z * Z) : Prop :=
alloc_ceiling <= fst iv
\/ (0xb0000 <= fst iv /\ snd iv <= 0xea000 /\ (snd iv <= RLIBC \/ RCTX + 928 <= fst iv)
/\ (snd iv <= RSSP_GUARD \/ RSSP_GUARD + 8 <= fst iv) /\ (snd iv <= RGOT_SSP \/ RGOT_SSP + 8 <= fst iv)
/\ (snd iv <= RVMLOCKC \/ RVMLOCKC + 4 <= fst iv))
\/ (exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b).
Definition raddr_exposed (s : PState) (n : Z) : Prop :=
MMAP_THRESHOLD <= n \/ ps_m s = ps_m (ps_init (reservedZ rsegs)).
Lemma raddr_exposed_big : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMalloc_iface "='D'5&Q5&Br1%3221&Kr3r2%3221p051pS8:1pS:<1").
Proof. intros; left; assumption. Qed.
Lemma raddr_exposed_init : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMalloc_iface "E'D'5'4'C&Gr2%211&Fv8&H&I%211%5241%911%<3;81&Kr3%221<p041pS8B1pS:D1").
Proof. intros; right; assumption. Qed.
Definition rdeep_pres (lo : Z) (m m' : mem) : Prop :=
forall a, alloc_ceiling <= a < lo -> m' (wa a) = m (wa a).
Definition rimg_pres (m m' : mem) : Prop :=
forall a, 0x10000 <= a < 0xea000 -> ~ (RCTX <= a < RCTX + 928) -> ~ (RERRNO <= a < RERRNO + 4) -> m' (wa a) = m (wa a).
Definition rmalloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PState) (LB : list block) (n lo B : Z) (m : mem)
(r : option bptr) (s' : PState) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 errv']
/\ rauxv_ok m' B
/\ rheap_pres LB (bv_unsigned sp) m m' /\ rdeep_pres lo m m' /\ rimg_pres m m'
/\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
/\ match r with
| None => a0 = Z_to_bv 64 0 /\ RHEAP s' LB m'
| Some p => exists A junk,
a0 = Z_to_bv 64 A /\ rblock_range A n
/\ RHEAP s' ((p, A, n) :: LB) m'
/\ rw_cells rsegs m' A [CB (Z.to_nat n) junk]
/\ (raddr_exposed s n -> A = ptr_addr s' p)
end.
Definition rmalloc_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (n lo B : Z) (errv : word),
RHEAP s LB m ->
rauxv_ok m B -> bv_unsigned sp <= B ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RMALLOC_STACK ->
rw_cells rsegs m (errno_addr tp) [C4 errv] ->
mem_inv rsegs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
implM rsegs (raw_malloc n) s
(rmalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RMALLOC_SYM) fc None m (seg_rom rsegs)).
Definition rfree_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PState) (LB : list block) (p : bptr) (lo B : Z) (errv : word) (m : mem)
(r : unit) (s' : PState) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 errv]
/\ rauxv_ok m' B
/\ rheap_pres (lb_remove p LB) (bv_unsigned sp) m m' /\ rdeep_pres lo m m' /\ rimg_pres m m'
/\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
/\ RHEAP s' (lb_remove p LB) m'.
Definition rfree_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (p : bptr) (A n lo B : Z) (errv : word),
RHEAP s LB m -> In (p, A, n) LB ->
rauxv_ok m B -> bv_unsigned sp <= B ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RFREE_STACK ->
rw_cells rsegs m (errno_addr tp) [C4 errv] ->
mem_inv rsegs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 A ->
implM rsegs (raw_free p) s
(rfree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p lo B errv m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RFREE_SYM) fc None m (seg_rom rsegs)).
Definition rfree_null_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
a0 = Z_to_bv 64 0 ->
evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom rsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RFREE_SYM) fc None m (seg_rom rsegs)).
Lemma rfree_null_spec : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RMalloc_iface "1&N").
Proof.
intros until m. intros ->. unfold RFREE_SYM.
step. step. if_true. step. apply evt_done. reflexivity.
Qed.
End CEIL_WRAP_1.
