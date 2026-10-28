(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QmZZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmZZ. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QKQo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKQo.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uu4M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uu4M.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UPZI.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Ub4w.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ub4w. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UPZI.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U2Sr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U2Sr.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Ujk3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ujk3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uuoa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uuoa.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UY9Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UY9Y.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qvbw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvbw. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QYIF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYIF.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QyuL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyuL.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBGG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBGG.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uh14.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uh14. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UGEL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UGEL. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UmtA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UmtA. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Udgq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Udgq. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UIjw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UIjw.Mq1.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo.exec_pre i ::= QlEo.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition get_string_stmt_P (HIx : heap_iface S4L) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB BS : list blk) (s : jshape) (p rc lo : Z) (errv : word),
HEAP S4L HIx A (BS ++ LB) m md ->
jval rsegs S4F s m BS p rc ->
sdepth s <= 1000 ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 16 - ser_budget s ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells rsegs m ERRNO [C4 errv] ->
tp = Z_to_bv 64 TP -> bv_unsigned ra mod 2 = 0 -> frm0 fc ->
a0 = Z_to_bv 64 p ->
(forall ms' md', tojs_post HIx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo s p rc ms' md' ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 SER_GETSTR) fc None m (seg_rom rsegs)) md) T.
Definition get_string_null_P (HIx : heap_iface S4L) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet) (A : AS S4L HIx) (LB : list blk) (lo : Z),
HEAP S4L HIx A LB m md ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
(forall (m1 : word -> option byte) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m1 -> wmono rsegs m m1 -> HEAP S4L HIx A LB m1 md -> stk rsegs m1 lo (bv_unsigned sp) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m1 (seg_rom rsegs)) md) T) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 SER_GETSTR) fc None m (seg_rom rsegs)) md) T.

Definition GD_LCONV_P : Z := 0x65798.
Definition GD_DP_P : Z := 0x10eaf.

Section HarnJoP1.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).

Hypothesis GETB : jo_get_pure_stmt S4L HIx S4F 0x25680.
Hypothesis GETD : hi_top S4L HIx < 2^62 -> jo_get_double_stmt S4L HIx S4F 0x26220 (64 + 8928) GD_LCONV_P GD_DP_P.
Hypothesis GETI : hi_top S4L HIx < 2^62 -> jo_get_num_stmt S4L HIx S4F 0x257ec 448.
Hypothesis GETI64 : hi_top S4L HIx < 2^62 -> jo_get_num_stmt S4L HIx S4F 0x25a5c 448.
Hypothesis GETU64 : hi_top S4L HIx < 2^62 -> jo_get_num_stmt S4L HIx S4F 0x25bc4 448.
Hypothesis GETS : hi_top S4L HIx < 2^62 -> get_string_stmt_P HIx.
Hypothesis GETS0 : get_string_null_P HIx.
Hypothesis GETSL : jo_get_pure_stmt S4L HIx S4F 0x26658.
Hypothesis GETO : jo_get_pure_stmt S4L HIx S4F 0x254cc.
Hypothesis GETA : jo_get_pure_stmt S4L HIx S4F 0x268c4.
Hypothesis GETT : jo_get_pure_stmt S4L HIx S4F 0x2496c.
Hypothesis VISIT : jo_visit_stmt S4L HIx S4F JCVISIT_P EMIT_P 112 96.

Section Ctx.

Variables (sp0 lo : Z) (LB : list blk) (m0 : word -> option byte) (md0 : Model) (F0 : bvmap 5 word) (fc0 : bv 32).
Variables (ra0 s0v s1v s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (T : TSet).
Variables (data0 size : Z) (payload : list byte).
Let spf : Z := sp0 - 64.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= sp0 - TGT_STACK.
Hypothesis SPA : sp0 mod 16 = 0.
Hypothesis HT : sp0 <= hi_top S4L HIx.
Hypothesis HT62 : hi_top S4L HIx < 2^62.
Hypothesis RA0 : bv_unsigned ra0 mod 2 = 0.
Hypothesis FRM0 : frm0 fc0.
Hypothesis PLEN : Z.of_nat (length payload) = size.
Hypothesis SZ : 0 <= size < 2^26.
Hypothesis D0 : 0 < data0.
Hypothesis DSZ : data0 + size < 2^63.
Hypothesis INB : size = 0 \/ In (data0, size) LB.
Hypothesis DLO : data0 + size <= alloc_ceiling.

Definition hsave (m : word -> option byte) : Prop :=
rw_cells rsegs m (spf + 48) [C8 s0v; C8 ra0].

Definition HINV (m : word -> option byte) (md : Model) (F : bvmap 5 word) (fc : bv 32) (errv : word)
(ptr rem : Z) (data : list byte) : Prop :=
heap_presx S4L (xtgt S4L) LB sp0 m0 m /\ model_vm_only md0 md /\ fsaved F0 F /\ frm0 fc /\
rw_cells rsegs m LOCCELL [C8 (Z_to_bv 64 GLOBLOC)] /\ rw_cells rsegs m LOCALE_LOCK [C4 (Z_to_bv 64 0)] /\ hglob_P m /\
stk rsegs m lo spf /\ hsave m /\ rw_cells rsegs m (0x77c00 - 164) [C4 errv] /\
(exists j8, rw_cells rsegs m spf [CB 8 j8]) /\
(exists sj, rw_cells rsegs m (spf + 8) [CB 24 sj]) /\
fdp_at spf m ptr rem data /\ 0 < ptr /\ data0 <= ptr /\ ptr + rem <= data0 + size /\ 0 <= rem.

#[using="RC__ sp0 ra0 payload spf SZ D0 INB DLO"] Lemma window_bytes : forall m m' ptr rem data,
bytes_at rsegs m ptr data -> Z.of_nat (length data) = rem -> data0 <= ptr -> ptr + rem <= data0 + size -> 0 <= rem ->
(forall a, 0 <= a < 2^64 -> in_block LB a -> m' (wa a) = m (wa a)) ->
bytes_at rsegs m' ptr data.
Proof.
intros m m' ptr rem data B L P1 P2 R0 E.
destruct INB as [Z0 | INB'].
- assert (data = []) as -> by (destruct data; [reflexivity | cbn in L; lia]).
destruct B as (B0 & B1 & _). split; [exact B0|]. split; [exact B1|]. intros i Hi. cbn in Hi. lia.
- destruct B as (B0 & B1 & BB). split; [exact B0|]. split; [exact B1|].
intros i Hi. rewrite <- (BB i Hi). unfold mrd. rewrite (E (ptr + Z.of_nat i)); [reflexivity | lia |].
exists (data0, size). split; [exact INB' | cbn; lia].
Qed.

#[using="payload SZ D0 INB DLO"] Lemma HINV_call : forall m m' md md' F F' fc fc' errv errv' ptr rem data LBx,
HINV m md F fc errv ptr rem data ->
heap_pres S4L LBx spf m m' -> incl LB LBx -> model_vm_only md md' -> fsaved F F' -> frm0 fc' ->
stk rsegs m' lo spf -> rw_cells rsegs m' (0x77c00 - 164) [C4 errv'] ->
HINV m' md' F' fc' errv' ptr rem data.
Proof.
intros m m' md md' F F' fc fc' errv errv' ptr rem data LBx
(PX & VM & FS & FRM & LOC & LCK & G & ST & SAV & ERR & [j16 SCR] & [sj STR] & (FD & B & L & P0 & P1) & PP & D1 & D2 & R0)
HPR Hi VM' FS' FRM' ST' ERR'.
unfold HINV, hsave, fdp_at in *.
assert (INBm : forall a, 0 <= a < 2^64 -> in_block LB a -> m' (wa a) = m (wa a)).
{ intros a Ha (b & Hb & Hr). apply (HPR a Ha). right; right. exists b. split; [apply Hi; exact Hb | exact Hr]. }
split. { eapply heap_presx_trans; [exact PX|]. apply heap_pres_presx. eapply heap_pres_weaken; [exact HPR | unfold spf; lia | exact Hi]. }
split. { eapply model_vm_only_trans; [exact VM | exact VM']. }
split. { eapply fsaved_trans; [exact FS | exact FS']. }
split. { exact FRM'. }
split. { eapply (heap_pres_rw_cells S4L); [exact HPR | exact LOC |]. right; left. unfold LOCCELL. cbn. unfold s4_client_static. intros; lia. }
split. { eapply (heap_pres_rw_cells S4L); [exact HPR | exact LCK |]. right; left. unfold LOCALE_LOCK. cbn. unfold s4_client_static. intros; lia. }
split. { eapply hglob_P_pres; [exact HPR | exact G]. }
split. { exact ST'. }
split. { eapply (heap_pres_rw_cells S4L); [exact HPR | exact SAV |]. left. cbn. lia. }
split. { exact ERR'. }
split. { exists j16. eapply (heap_pres_rw_cells S4L); [exact HPR | exact SCR |]. left. cbn. lia. }
split. { exists sj. eapply (heap_pres_rw_cells S4L); [exact HPR | exact STR |]. left. cbn. lia. }
split. { split. { eapply (heap_pres_rw_cells S4L); [exact HPR | exact FD |]. left. cbn. lia. }
split. { eapply window_bytes; [exact B | exact L | exact D1 | exact D2 | exact R0 | exact INBm]. }
split; [exact L | split; [exact P0 | exact P1]]. }
lia.
Qed.

#[using="Type"] Lemma HINV_regs : forall m md F F' fc fc' errv ptr rem data,
HINV m md F fc errv ptr rem data -> fsaved F F' -> frm0 fc' -> HINV m md F' fc' errv ptr rem data.
Proof.
intros m md F F' fc fc' errv ptr rem data (PX & VM & FS & FRM & REST) FS' FRM'.
split; [exact PX|]. split; [exact VM|]. split; [eapply fsaved_trans; [exact FS | exact FS']|]. split; [exact FRM'|]. exact REST.
Qed.

#[using="payload LO LOS HT SZ D0 INB DLO"] Lemma HINV_below : forall m m1 md F fc errv ptr rem data (A : AS S4L HIx) LBx,
HINV m md F fc errv ptr rem data -> HEAPx A LBx m md -> incl LB LBx ->
munch [(spf - 16, spf)] m m1 -> wmono rsegs m m1 -> stk rsegs m1 lo spf ->
HINV m1 md F fc errv ptr rem data.
Proof.
intros m m1 md F fc errv ptr rem data A LBx
(PX & VM & FS & FRM & LOC & LCK & G & ST & SAV & ERR & [j8 SCR] & [sj STR] & (FD & B & L & P0 & P1) & PP & D1 & D2 & R0)
HP Hi MU WM ST1.
unfold hsave in SAV. unfold TGT_STACK in LOS. unfold_consts.
unfold HINV, hsave, fdp_at.
split. { eapply heap_presx_trans; [exact PX|]. eapply heap_presx_of_munchx; [exact MU | exact WM |].
eapply (client_outsidex HIx); [exact HP | exact Hi | clia | apply Forall_cons; [left; cbn; unfold spf; clia | apply Forall_nil]]. }
split; [exact VM|]. split; [exact FS|]. split; [exact FRM|].
split. { eapply rw_cells_transport; [exact LOC | exact MU | exact WM | unfold LOCCELL; cbn; unfold spf; clia]. }
split. { eapply rw_cells_transport; [exact LCK | exact MU | exact WM | unfold LOCALE_LOCK; cbn; unfold spf; clia]. }
split. { eapply hglob_P_outside; [exact G | exact MU | exact WM | apply Forall_cons; [cbn; right; unfold spf; clia | apply Forall_nil]]. }
split; [exact ST1|].
split. { eapply rw_cells_transport; [exact SAV | exact MU | exact WM | cbn; unfold spf; lia]. }
split. { eapply rw_cells_transport; [exact ERR | exact MU | exact WM | cbn; unfold spf; clia]. }
split. { exists j8. eapply rw_cells_transport; [exact SCR | exact MU | exact WM | cbn; unfold spf; lia]. }
split. { exists sj. eapply rw_cells_transport; [exact STR | exact MU | exact WM | cbn; unfold spf; lia]. }
split. { split. { eapply rw_cells_transport; [exact FD | exact MU | exact WM | cbn; unfold spf; lia]. }
split. { eapply bytes_at_transport; [exact B | exact MU | cbn; unfold spf; clia]. }
split; [exact L | split; [exact P0 | exact P1]]. }
split; [exact PP|]. split; [exact D1|]. split; [exact D2 | exact R0].
Qed.

#[using="RC__ sp0 ra0 size payload spf SZ"] Lemma lconv_facts : forall m, hglob_P m -> mem_inv rsegs m ->
bytes_at rsegs m GD_LCONV_P (le8 (Z_to_bv 64 GD_DP_P)) /\ bytes_at rsegs m GD_DP_P [Z_to_bv 8 46].
Proof.
intros m [_ (J1 & J2 & J3 & J4)] MI. split; [exact J2|].
pose proof (ro_cells_image rsegs m GD_DP_P [Z_to_bv 8 46] MI ltac:(vm_compute; reflexivity) ltac:(unfold GD_DP_P; lia) ltac:(unfold GD_DP_P; cbn; lia)) as [_ RO].
cbn [cells_bytes cbytes app] in RO. rewrite ?app_nil_r in RO. exact RO.
Qed.

Section Getters.
Variable p : Z.

Definition gstate (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (pc : Z) (fc : bv 32) (m : word -> option byte) :=
MS (mkR x1 (Z_to_bv 64 spf) gp (Z_to_bv 64 0x77c00) t0 t1 t2 (Z_to_bv 64 p) s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None m (seg_rom rsegs).

Definition GINV (m : word -> option byte) (md : Model) (A : AS S4L HIx) (F : bvmap 5 word) (fc : bv 32) (errv : word)
(ptr rem : Z) (data : list byte) (s : option jshape) (BS LK : list blk) : Prop :=
HINV m md F fc errv ptr rem data /\ HEAPx A (BS ++ LK ++ LB) m md /\ jopt rsegs S4F s m BS p /\ odepth s <= 32.

Definition KG (k : Z) (s : option jshape) : Prop :=
forall m' md' (A' : AS S4L HIx) F' fc' errv' ptr' rem' data' BS' LK' (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
GINV m' md' A' F' fc' errv' ptr' rem' data' s BS' LK' ->
realizes rsegs (mkCfg (gstate x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' k fc' m') md') T.

#[using="payload SZ"] Lemma pure_call : forall (pc f : Z) m md (A : AS S4L HIx) F fc errv ptr rem data s BS LK
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
jo_get_pure_stmt S4L HIx S4F f ->
(pc = 0x21084 /\ f = 0x25680 \/ pc = 0x210b4 /\ f = 0x26658 \/ pc = 0x210bc /\ f = 0x254cc \/ pc = 0x210c4 /\ f = 0x268c4 \/ pc = 0x210cc /\ f = 0x2496c) ->
GINV m md A F fc errv ptr rem data s BS LK ->
KG (pc + 8) s ->
realizes rsegs (mkCfg (gstate x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F pc fc m) md) T.
Proof.
intros pc f m md A F fc errv ptr rem data s BS LK x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 GP Hpc (INV & HP & JO & OD) K.
pose proof INV as (PX & VM & FS & FRM & LOC & LCK & G & ST & SAV & ERR & _).
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK. pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
unfold gstate. unfold_consts.
destruct Hpc as [[-> ->] | [[-> ->] | [[-> ->] | [[-> ->] | [-> ->]]]]];
(apply rz_evt; [exact MOK|]; step; step; fold_mkR; apply evt_RZ_done;
eapply GP with (BS := BS) (LB := LK ++ LB) (s := s);
[ exact HP | exact JO | vm_compute; reflexivity | exact FRM | reflexivity |];
intros ms' r (xt0 & xt1 & xt2 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xt3 & xt4 & xt5 & xt6 & F' & fc' & -> & FS' & FRM');
lazymatch goal with |- realizes _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) _) _ =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end;
lazymatch type of K with KG ?e _ => let v := eval vm_compute in e in change e with v in K end;
unfold KG, gstate in K; cbn [hl_segs S4L]; eapply K; split; [eapply HINV_regs; [exact INV | exact FS' | exact (FRM' FRM)] | split; [exact HP | split; [exact JO | exact OD]]]).
Qed.

#[using="RC__ ra0 size payload SPA SZ"] Lemma spf16 : spf mod 16 = 0.
Proof. unfold spf. replace (sp0 - 64) with (sp0 + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact SPA. Qed.

#[using="payload LO LOS SPA HT HT62 SZ D0 INB DLO"] Lemma num_call : forall (pc f : Z) m md (A : AS S4L HIx) F fc errv ptr rem data s BS LK
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
jo_get_num_stmt S4L HIx S4F f 448 ->
(pc = 0x21094 /\ f = 0x257ec \/ pc = 0x2109c /\ f = 0x25a5c \/ pc = 0x210a4 /\ f = 0x25bc4) ->
GINV m md A F fc errv ptr rem data s BS LK ->
KG (pc + 8) s ->
realizes rsegs (mkCfg (gstate x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F pc fc m) md) T.
Proof.
intros pc f m md A F fc errv ptr rem data s BS LK x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 GN Hpc (INV & HP & JO & OD) K.
pose proof INV as (PX & VM & FS & FRM & LOC & LCK & G & ST & SAV & ERR & _).
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK. pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof spf16 as SPF16. unfold TGT_STACK in LOS.
unfold gstate. unfold_consts.
destruct Hpc as [[-> ->] | [[-> ->] | [-> ->]]];
(apply rz_evt; [exact MOK|]; step; step; fold_mkR; apply evt_RZ_done;
eapply GN with (A := A) (BS := BS) (LB := LK ++ LB) (s := s) (lo := lo);
[ split; [exact HP|]; rewrite unsigned_lit by lia;
split; [exact ST|]; split; [exact LO|]; split; [unfold spf; lia|]; split; [exact SPF16|]; split; [unfold spf; lia|];
split; [exact ERR|]; split; [reflexivity | vm_compute; reflexivity]
| exact JO | exact FRM | reflexivity |];
intros ms' md' m' r (RS & VM' & ST' & HPR' & [errv' ERR']) JO' HP';
destruct RS as (xt0 & xt1 & xt2 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xt3 & xt4 & xt5 & xt6 & F' & fc' & -> & FS' & FRM');
cbn [hl_segs hl_tp S4L] in ST', HPR', ERR', HP'; rewrite unsigned_lit in ST', HPR' by lia;
lazymatch goal with |- realizes _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) _) _ =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end;
lazymatch type of K with KG ?e _ => let v := eval vm_compute in e in change e with v in K end;
unfold KG, gstate in K; cbn [hl_segs S4L]; eapply K; split;
[ eapply (HINV_call m m' md md' F F' fc fc' errv errv' ptr rem data (LK ++ LB) INV HPR' ltac:(intros b Hb; apply in_or_app; right; exact Hb) VM' FS' (FRM' FRM) ST' ERR')
| split; [exact HP' | split; [exact JO' | exact OD]]]).
Qed.

#[using="GETD payload LO LOS SPA HT HT62 SZ D0 INB DLO"] Lemma dbl_call : forall m md (A : AS S4L HIx) F fc errv ptr rem data s BS LK
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
GINV m md A F fc errv ptr rem data s BS LK ->
KG 0x21094 s ->
realizes rsegs (mkCfg (gstate x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F 0x2108c fc m) md) T.
Proof.
intros m md A F fc errv ptr rem data s BS LK x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (INV & HP & JO & OD) K.
pose proof INV as (PX & VM & FS & FRM & LOC & LCK & G & ST & SAV & ERR & _).
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK. pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof spf16 as SPF16. unfold TGT_STACK in LOS.
destruct (lconv_facts m G MI) as [LC DP].
unfold gstate. unfold_consts.
apply rz_evt; [exact MOK|]. step. step. fold_mkR. apply evt_RZ_done.
eapply (GETD HT62) with (A := A) (BS := BS) (LB := LK ++ LB) (s := s) (lo := lo);
[ split; [exact HP|]; rewrite unsigned_lit by lia;
split; [exact ST|]; split; [exact LO|]; split; [unfold spf; lia|]; split; [exact SPF16|]; split; [unfold spf; lia|];
split; [exact ERR|]; split; [reflexivity | vm_compute; reflexivity]
| exact JO | exact FRM | reflexivity | exact LC | exact DP |].
intros ms' md' m' r (RS & VM' & ST' & HPR' & [errv' ERR']) JO' [A' HP'].
destruct RS as (xt0 & xt1 & xt2 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xt3 & xt4 & xt5 & xt6 & F' & fc' & -> & FS' & FRM').
cbn [hl_segs hl_tp S4L] in ST', HPR', ERR', HP'. rewrite unsigned_lit in ST', HPR' by lia.
replace (ret_pc (Z_to_bv 64 0x21094)) with (Z_to_bv 64 0x21094 : word) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
unfold KG, gstate in K. cbn [hl_segs S4L]. eapply K. split;
[ eapply (HINV_call m m' md md' F F' fc fc' errv errv' ptr rem data (LK ++ LB) INV HPR' ltac:(intros b Hb; apply in_or_app; right; exact Hb) VM' FS' (FRM' FRM) ST' ERR')
| split; [exact HP' | split; [exact JO' | exact OD]]].
Qed.

#[using="GETS GETS0 payload LO LOS SPA HT HT62 SZ D0 INB DLO"] Lemma str_call : forall m md (A : AS S4L HIx) F fc errv ptr rem data s BS LK
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
GINV m md A F fc errv ptr rem data s BS LK ->
KG 0x210b4 s ->
realizes rsegs (mkCfg (gstate x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F 0x210ac fc m) md) T.
Proof.
intros m md A F fc errv ptr rem data s BS LK x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (INV & HP & JO & OD) K.
pose proof INV as (PX & VM & FS & FRM & LOC & LCK & G & ST & SAV & ERR & _).
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK. pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof spf16 as SPF16. unfold TGT_STACK in LOS.
unfold gstate. unfold_consts.
apply rz_evt; [exact MOK|]. step. step. fold_mkR. apply evt_RZ_done.
destruct s as [sh|].
- destruct JO as [Hp J]. cbn [odepth] in OD.
eapply (GETS HT62) with (A := A) (BS := BS) (LB := LK ++ LB) (s := sh) (lo := lo);
[ exact HP | exact J | lia | rewrite unsigned_lit by lia; exact ST | exact LO
| rewrite unsigned_lit by lia; unfold ser_budget, spf; lia | rewrite unsigned_lit by lia; exact SPF16
| rewrite unsigned_lit by lia; unfold spf; lia | unfold ERRNO; exact ERR | reflexivity | vm_compute; reflexivity | exact FRM | reflexivity |].
intros ms' md' (m' & A' & r & errv' & BS' & RS & VM' & ST' & HPR' & ERR' & HP' & J').
destruct RS as (xt0 & xt1 & xt2 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xt3 & xt4 & xt5 & xt6 & F' & fc' & -> & FS' & FRM').
cbn [hl_segs hl_tp S4L] in ST', HPR', HP'. rewrite unsigned_lit in ST', HPR' by lia. unfold ERRNO in ERR'.
replace (ret_pc (Z_to_bv 64 0x210b4)) with (Z_to_bv 64 0x210b4 : word) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
unfold KG, gstate in K. cbn [hl_segs S4L]. eapply K. split;
[ eapply (HINV_call m m' md md' F F' fc fc' errv errv' ptr rem data (LK ++ LB) INV HPR' ltac:(intros b Hb; apply in_or_app; right; exact Hb) VM' FS' (FRM' FRM) ST' ERR')
| split; [exact HP' | split; [split; [exact Hp | exact J'] | exact OD]]].
- destruct JO as [Hp EBS]. rewrite Hp. subst BS. cbn [app] in HP.
eapply GETS0; [exact HP | rewrite unsigned_lit by lia; exact ST | exact LO | rewrite unsigned_lit by lia; unfold spf; lia | rewrite unsigned_lit by lia; exact SPF16 | rewrite unsigned_lit by lia; unfold spf; lia |].
intros m1 xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 MU1 WM1 HP1 ST1.
rewrite unsigned_lit in MU1, ST1 by lia.
replace (ret_pc (Z_to_bv 64 0x210b4)) with (Z_to_bv 64 0x210b4 : word) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
unfold KG, gstate in K. cbn [hl_segs S4L]. rewrite <- Hp. eapply K with (BS' := []).
split; [| split; [exact HP1 | split; [split; [exact Hp | reflexivity] | exact OD]]].
eapply HINV_below; [exact INV | exact HP | intros b Hb; apply in_or_app; right; exact Hb | exact MU1 | exact WM1 | exact ST1].
Qed.

#[using="VISIT payload LO LOS SPA HT HT62 SZ D0 INB DLO"] Lemma visit_call : forall m md (A : AS S4L HIx) F fc errv ptr rem data s BS LK
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
GINV m md A F fc errv ptr rem data s BS LK ->
KG 0x210ec s ->
realizes rsegs (mkCfg (gstate x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F 0x210d4 fc m) md) T.
Proof.
intros m md A F fc errv ptr rem data s BS LK x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (INV & HP & JO & OD) K.
pose proof INV as (PX & VM & FS & FRM & LOC & LCK & G & ST & SAV & ERR & _).
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK. pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof spf16 as SPF16. unfold TGT_STACK in LOS.
unfold gstate. unfold_consts.
apply rz_evt; [exact MOK|]. step. step. step. step. step. step. fold_mkR. apply evt_RZ_done.
pose proof VISIT as VI. unfold jo_visit_stmt, JCVISIT_P, EMIT_P in VI.
eapply VI with (A := A) (BS := BS) (LB := LK ++ LB) (s := s) (lo := lo);
[ split; [exact HP|]; rewrite unsigned_lit by lia;
split; [exact ST|]; split; [exact LO|]; split; [unfold spf; lia|]; split; [exact SPF16|]; split; [unfold spf; lia|];
split; [exact ERR|]; split; [reflexivity | vm_compute; reflexivity]
| exact JO | reflexivity | reflexivity | reflexivity | reflexivity |].
intros ms' md' m' r (RS & VM' & ST' & HPR' & [errv' ERR']) -> JO' HP' ERRx.
destruct RS as (xt0 & xt1 & xt2 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xt3 & xt4 & xt5 & xt6 & F' & fc' & -> & FS' & FRM').
cbn [hl_segs hl_tp S4L] in ST', HPR', ERR', HP', ERRx. rewrite unsigned_lit in ST', HPR' by lia.
replace (ret_pc (Z_to_bv 64 0x210ec)) with (Z_to_bv 64 0x210ec : word) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
unfold KG, gstate in K. cbn [hl_segs S4L]. eapply K. split;
[ eapply (HINV_call m m' md md' F F' fc fc' errv errv ptr rem data (LK ++ LB) INV HPR' ltac:(intros b Hb; apply in_or_app; right; exact Hb) VM' FS' (FRM' FRM) ST' ERRx)
| split; [exact HP' | split; [exact JO' | exact OD]]].
Qed.

#[using="GETB GETD GETI GETI64 GETU64 GETS GETS0 GETSL GETO GETA GETT VISIT payload LO LOS SPA HT HT62 SZ D0 INB DLO"] Lemma seg_getters : forall m md (A : AS S4L HIx) F fc errv ptr rem data s BS LK
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
GINV m md A F fc errv ptr rem data s BS LK ->
KG 0x210ec s ->
realizes rsegs (mkCfg (gstate x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F 0x21084 fc m) md) T.
Proof.
intros m md A F fc errv ptr rem data s BS LK x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 GI K.
Ltac kg_next := unfold KG; intros;
lazymatch goal with |- realizes _ (mkCfg (gstate _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?pc _ _) _) _ =>
let v := eval vm_compute in pc in change pc with v end.
eapply (pure_call 0x21084 0x25680); [exact GETB | (repeat first [ left; split; reflexivity | right ]; try (split; reflexivity)) | exact GI |]. kg_next.
eapply dbl_call; [eassumption|]. kg_next.
eapply (num_call 0x21094 0x257ec); [exact (GETI HT62) | (repeat first [ left; split; reflexivity | right ]; try (split; reflexivity)) | eassumption |]. kg_next.
eapply (num_call 0x2109c 0x25a5c); [exact (GETI64 HT62) | (repeat first [ left; split; reflexivity | right ]; try (split; reflexivity)) | eassumption |]. kg_next.
eapply (num_call 0x210a4 0x25bc4); [exact (GETU64 HT62) | (repeat first [ left; split; reflexivity | right ]; try (split; reflexivity)) | eassumption |]. kg_next.
eapply str_call; [eassumption|]. kg_next.
eapply (pure_call 0x210b4 0x26658); [exact GETSL | (repeat first [ left; split; reflexivity | right ]; try (split; reflexivity)) | eassumption |]. kg_next.
eapply (pure_call 0x210bc 0x254cc); [exact GETO | (repeat first [ left; split; reflexivity | right ]; try (split; reflexivity)) | eassumption |]. kg_next.
eapply (pure_call 0x210c4 0x268c4); [exact GETA | (repeat first [ left; split; reflexivity | right ]; try (split; reflexivity)) | eassumption |]. kg_next.
eapply (pure_call 0x210cc 0x2496c); [exact GETT | (repeat first [ left; split; reflexivity | right ]; try (split; reflexivity)) | eassumption |]. kg_next.
eapply visit_call; [eassumption | exact K].
Qed.
End Getters.
End Ctx.
End HarnJoP1.

End RC__1.
