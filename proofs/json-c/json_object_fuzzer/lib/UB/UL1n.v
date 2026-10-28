(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3.Mq2.
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
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qvbw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvbw. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QYIF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYIF.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QyuL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyuL.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBGG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBGG.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uh14.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uh14. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UmtA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UmtA. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UIjw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UIjw.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEE7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEE7.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UrIB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UrIB.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UHNo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UHNo.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QmtA.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo.exec_pre i ::= QlEo.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rdepth_set_double_root : forall d r, rdepth (set_double_root d r) <= rdepth r.
Proof. intros d r. destruct r as [|s| |]; cbn; try lia. pose proof (sdepth_nonneg s). destruct s; cbn in *; lia. Qed.
#[using="Type"] Lemma rdepth_set_string_root : forall r, rdepth (set_string_root r) <= rdepth r.
Proof. intros r. destruct r as [|s| |]; cbn; try lia. pose proof (sdepth_nonneg s). destruct s; cbn in *; lia. Qed.

#[using="Type"] Lemma land_even_1 : forall n, Z.land (2 * n) 1 = 0.
Proof. intros n. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. rewrite Z.mul_comm. apply Z_mod_mult. Qed.
#[using="Type"] Lemma short_flag0 : forall n, 0 <= n <= 127 -> Z.land (bv_unsigned (zxb (Z_to_bv 8 (2 * n)))) 1 = 0.
Proof.
intros n Hn. unfold zxb. rewrite unsigned_lit.
2:{ pose proof (bv_unsigned_in_range 8 (Z_to_bv 8 (2 * n))) as R. unfold bv_modulus in R. cbn in R. lia. }
rewrite Z_to_bv_unsigned. change (bv_wrap 8 (2 * n)) with ((2 * n) mod 2^8). rewrite Z.mod_small by lia.
apply land_even_1.
Qed.
#[using="Type"] Lemma short_size : forall n, 0 <= n <= 127 -> Z.shiftr (bv_unsigned (zxb (Z_to_bv 8 (2 * n)))) 1 = n.
Proof.
intros n Hn. unfold zxb. rewrite unsigned_lit.
2:{ pose proof (bv_unsigned_in_range 8 (Z_to_bv 8 (2 * n))) as R. unfold bv_modulus in R. cbn in R. lia. }
rewrite Z_to_bv_unsigned. change (bv_wrap 8 (2 * n)) with ((2 * n) mod 2^8). rewrite Z.mod_small by lia.
rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity.
Qed.

#[using="Type"] Lemma disjoint_from_bounds : forall (W : list (Z * Z)) (P : Z * Z -> Prop) A n,
Forall P W -> (forall u v, P (u, v) -> A + n <= u \/ v <= A) -> disjoint_from W A n.
Proof.
intros W P A n FW H. induction W as [|[u v] W IH]; [exact I|].
apply Forall_cons_iff in FW as [F1 FW]. cbn. split; [exact (H u v F1) | apply IH; exact FW].
Qed.

Definition hj_fp1 := Eval vm_compute in match image_bytes rsegs 0x133c8 8 with Some bs => bs | None => [] end.
Definition hj_fp2 := Eval vm_compute in match image_bytes rsegs 0x133b0 8 with Some bs => bs | None => [] end.
#[using="Type"] Lemma hj_ro : forall m, mem_inv rsegs m -> ro_cells rsegs m 0x133c8 [CB 8 hj_fp1] /\ ro_cells rsegs m 0x133b0 [CB 8 hj_fp2].
Proof.
intros m MI. split.
- change 8%nat with (length hj_fp1). apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ]. change (Z.of_nat (length hj_fp1)) with 8%Z. lia.
- change 8%nat with (length hj_fp2). apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ]. change (Z.of_nat (length hj_fp2)) with 8%Z. lia.
Qed.

#[using="Type"] Lemma notin0_forall : forall s : list byte, ~ In (Z_to_bv 8 0) s -> Forall (fun b => bv_unsigned b <> 0) s.
Proof.
intros s H. apply Forall_forall. intros b Hb E. apply H. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E. reflexivity.
Qed.

Section HarnJoP2.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).

Hypothesis SETI : jo_set_scalar_stmt S4L HIx S4F 0x2598c.
Hypothesis SETI64 : jo_set_scalar_stmt S4L HIx S4F 0x259c0.
Hypothesis SETU64 : jo_set_scalar_stmt S4L HIx S4F 0x25d28.
Hypothesis SETB : jo_set_scalar_stmt S4L HIx S4F 0x25754.
Hypothesis SETD : jo_set_double_stmt2 HIx SD_ENTRY_P SD_TBL_P SD_STK.
Hypothesis CFP : cfp_stmt rsegs CFP_P CFP_STK_P IHI_P.
Hypothesis CRLS : crls_stmt rsegs CRLS_P CRLS_FRAME_P.
Hypothesis SETS : jo_set_string_stmt S4L HIx S4F 0x2669c (64 + 8256).
Hypothesis SETSL : jo_set_string_len_stmt S4L HIx S4F 0x26828 (64 + 8256).
Hypothesis CII_INT : cii_stmt rsegs QmtA.CII_INT_U 4 (2^64 - 2^31) (2^31 - 1).
Hypothesis CII_I64 : cii_stmt rsegs QmtA.CII_I64_U 8 (2^63) (2^63 - 1).
Hypothesis CII_U64 : cii_stmt rsegs QmtA.CII_U64_U 8 0 (2^64 - 1).

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

Notation HINVc := (HINV sp0 lo LB m0 md0 F0 ra0 s0v data0 size).

Local Ltac feed_hyps t :=
lazymatch type of t with
| forall _ : ?A, _ => first [ feed_hyps (t SETI) | feed_hyps (t SETI64) | feed_hyps (t SETU64) | feed_hyps (t SETB) | feed_hyps (t SETD) | feed_hyps (t CFP) | feed_hyps (t CRLS) | feed_hyps (t SETS) | feed_hyps (t SETSL) | feed_hyps (t CII_INT) | feed_hyps (t CII_I64) | feed_hyps (t CII_U64) | feed_hyps (t LO) | feed_hyps (t LOS) | feed_hyps (t SPA) | feed_hyps (t HT) | feed_hyps (t HT62) | feed_hyps (t RA0) | feed_hyps (t FRM0) | feed_hyps (t PLEN) | feed_hyps (t SZ) | feed_hyps (t D0) | feed_hyps (t DSZ) | feed_hyps (t INB) | feed_hyps (t DLO) | exact t ]
| _ => exact t
end.
Let HINV_callc := ltac:(feed_hyps (HINV_call sp0 lo LB m0 md0 F0 ra0 s0v data0 size payload)).

#[using="RC__ lo LB m0 md0 F0 ra0 s0v s1v data0 size payload SPA SZ D0 INB DLO"] Lemma spf16' : spf mod 16 = 0.
Proof. unfold spf. replace (sp0 - 64) with (sp0 + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact SPA. Qed.

#[using="Type"] Lemma HINV_intro : forall m md F fc errv ptr rem data j8 sj,
heap_presx S4L (xtgt S4L) LB sp0 m0 m -> model_vm_only md0 md -> fsaved F0 F -> frm0 fc ->
rw_cells rsegs m LOCCELL [C8 (Z_to_bv 64 GLOBLOC)] -> rw_cells rsegs m LOCALE_LOCK [C4 (Z_to_bv 64 0)] -> hglob_P m ->
stk rsegs m lo spf -> hsave sp0 ra0 s0v m -> rw_cells rsegs m (0x77c00 - 164) [C4 errv] ->
rw_cells rsegs m spf [CB 8 j8] -> rw_cells rsegs m (spf + 8) [CB 24 sj] ->
fdp_at spf m ptr rem data -> 0 < ptr -> data0 <= ptr -> ptr + rem <= data0 + size -> 0 <= rem ->
HINVc m md F fc errv ptr rem data.
Proof.
intros. unfold HINV. repeat (split; [first [eassumption | eexists; eassumption] |]). assumption.
Qed.

Section Setters.
Variable p : Z.

Definition sstate (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (pc : Z) (fc : bv 32) (m : word -> option byte) :=
MS (mkR x1 (Z_to_bv 64 spf) gp (Z_to_bv 64 0x77c00) t0 t1 t2 (Z_to_bv 64 p) s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None m (seg_rom rsegs).

Definition SINV (m : word -> option byte) (md : Model) (A : AS S4L HIx) (F : bvmap 5 word) (fc : bv 32) (errv : word)
(ptr rem : Z) (data : list byte) (r : jroot) (BS LK : list blk) : Prop :=
HINVc m md F fc errv ptr rem data /\ HEAPx A (BS ++ LK ++ LB) m md /\ jroot_rep S4L S4F r m BS p /\ rdepth r <= 32.

Definition KS (k : Z) (r : jroot) : Prop :=
forall m' md' (A' : AS S4L HIx) F' fc' errv' ptr' rem' data' BS' LK' (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
SINV m' md' A' F' fc' errv' ptr' rem' data' r BS' LK' ->
realizes rsegs (mkCfg (sstate x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' k fc' m') md') T.

Definition KSF (k : Z) (r : jroot) : Prop :=
forall m' md' (A' : AS S4L HIx) F' fc' errv' ptr' rem' data' BS' LK' (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
SINV m' md' A' F' fc' errv' ptr' rem' data' r BS' LK' ->
(exists (n : Z) (sj23 : list byte), 0 <= n <= 10 /\ rw_cells rsegs m' (spf + 8) [C1 (Z_to_bv 8 (2 * n)); CB 23 sj23]) ->
realizes rsegs (mkCfg (sstate x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' k fc' m') md') T.

#[using="payload LO LOS HT SZ D0 INB DLO"] Lemma SINV_munch : forall m m' md A F F' fc fc' errv ptr rem data ptr' rem' data' r BS LK W,
SINV m md A F fc errv ptr rem data r BS LK ->
munch W m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
Forall (fun iv => lo <= fst iv /\ snd iv <= spf + 48 /\ fst iv <= snd iv /\ (snd iv <= spf \/ spf + 8 <= fst iv)) W ->
fsaved F F' -> frm0 fc' ->
stk rsegs m' lo spf ->
fdp_at spf m' ptr' rem' data' -> 0 < ptr' -> data0 <= ptr' -> ptr' + rem' <= data0 + size -> 0 <= rem' ->
(forall sj, rw_cells rsegs m (spf + 8) [CB 24 sj] -> exists sj', rw_cells rsegs m' (spf + 8) [CB 24 sj']) ->
SINV m' md A F' fc' errv ptr' rem' data' r BS LK.
Proof.
intros m m' md A F F' fc fc' errv ptr rem data ptr' rem' data' r BS LK W
((PX & VM & FS & FRM & LOC & LCK & G & ST & SAV & ERR & [j16 SCR] & [sj STR] & FD & PP & D1 & D2 & R0) & HP & RR & RD)
MU WM MI' FW FS' FRM' ST' FD' PP' D1' D2' R0' STRk.
unfold hsave in SAV. unfold TGT_STACK in LOS. unfold_consts.
assert (OUT : forall x, (sp0 <= x \/ x < lo \/ (spf + 48 <= x) \/ (spf <= x < spf + 8)) -> outside W x).
{ intros x Hx. clear -FW Hx LOS. induction W as [|[u v] W IH]; [exact I|]. apply Forall_cons_iff in FW as [(F1 & F2 & F3 & F4) FW]. cbn [fst snd] in *.
split; [unfold spf in *; lia | apply IH; exact FW]. }
destruct (STRk sj STR) as [sj' STR'].
split; [| split; [| split; [| exact RD]]].
- eapply HINV_intro.
+ eapply heap_presx_trans; [exact PX|]. eapply heap_presx_of_munchx; [exact MU | exact WM |].
eapply (client_outsidex HIx); [exact HP | intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb | clia |].
clear -FW LOS LO. induction W as [|[u v] W IH]; [apply Forall_nil|]. apply Forall_cons_iff in FW as [(F1 & F2 & F3 & F4) FW]. cbn [fst snd] in F1, F2, F3, F4.
apply Forall_cons; [| apply IH; exact FW]. left. cbn [fst snd]. unfold spf in *. clia.
+ exact VM.
+ eapply fsaved_trans; [exact FS | exact FS'].
+ exact FRM'.
+ eapply rw_cells_transport; [exact LOC | exact MU | exact WM |]. eapply disjoint_from_bounds; [exact FW|]. unfold LOCCELL. cbn. intros u v (F1 & F2 & _). unfold spf in *. lia.
+ eapply rw_cells_transport; [exact LCK | exact MU | exact WM |]. eapply disjoint_from_bounds; [exact FW|]. unfold LOCALE_LOCK. cbn. intros u v (F1 & F2 & _). unfold spf in *. lia.
+ eapply hglob_P_outside; [exact G | exact MU | exact WM |].
eapply Forall_impl; [| exact FW]. intros [u v] (F1 & _). cbn [fst snd] in *. right. lia.
+ exact ST'.
+ unfold hsave. eapply rw_cells_transport; [exact SAV | exact MU | exact WM |]. eapply disjoint_from_bounds; [exact FW|]. cbn. intros u v (F1 & F2 & _). unfold spf in *. lia.
+ eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]. eapply disjoint_from_bounds; [exact FW|]. cbn. intros u v (F1 & F2 & _). unfold spf in *. lia.
+ eapply rw_cells_transport; [exact SCR | exact MU | exact WM |]. eapply disjoint_from_bounds; [exact FW|]. cbn. intros u v (F1 & F2 & F3 & F4). unfold spf in *. lia.
+ exact STR'.
+ exact FD'.
+ exact PP'. + exact D1'. + exact D2'. + exact R0'.
- eapply (heap_frame S4L HIx); [exact HP | | exact WM | exact MI'].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU).
clear -FW LOS LO HT. induction W as [|[u v] W IH]; [apply Forall_nil|]. apply Forall_cons_iff in FW as [(F1 & F2 & F3 & F4) FW]. cbn [fst snd] in F1, F2, F3, F4.
apply Forall_cons; [| apply IH; exact FW]. cbn [fst snd]. left. unfold spf in *. split; [clia | lia].
- eapply (jroot_rep_agree S4L S4F); [exact RR | | apply incl_refl].
eapply agree_of_munch; [exact MU | exact WM |]. intros a k Hin.
pose proof (heap_blk S4L HIx _ _ _ _ a k HP ltac:(apply in_or_app; left; exact Hin)) as (Hk & _ & _ & Hhi & _).
clear -FW Hk Hhi LOS LO. induction W as [|[u v] W IH]; [exact I|]. apply Forall_cons_iff in FW as [(F1 & F2 & F3 & F4) FW]. cbn [fst snd] in F1, F2, F3, F4.
cbn. split; [unfold spf in *; clia | apply IH; exact FW].
Qed.

#[using="payload SZ D0 INB DLO HINV_callc"] Lemma SINV_ret : forall m m' md md' A A' F F' fc fc' errv errv' ptr rem data r r' BS BS' LK LK',
SINV m md A F fc errv ptr rem data r BS LK ->
heap_pres S4L (LK ++ LB) spf m m' -> model_vm_only md md' -> fsaved F F' -> frm0 fc' ->
stk rsegs m' lo spf -> rw_cells rsegs m' (0x77c00 - 164) [C4 errv'] ->
HEAPx A' (BS' ++ LK' ++ LB) m' md' -> jroot_rep S4L S4F r' m' BS' p -> rdepth r' <= 32 ->
SINV m' md' A' F' fc' errv' ptr rem data r' BS' LK'.
Proof.
intros until LK'. intros (INV & HP & RR & RD) HPR VM FS FRM ST ERR HP' RR' RD'.
split; [| split; [exact HP' | split; [exact RR' | exact RD']]].
eapply HINV_callc; [exact INV | exact HPR | intros b Hb; apply in_or_app; right; exact Hb | exact VM | exact FS | exact FRM | exact ST | exact ERR].
Qed.

#[using="payload LO LOS SPA HT HT62 SZ D0 INB DLO HINV_callc"] Lemma set_call : forall (f ret : Z) m md (A : AS S4L HIx) F fc errv ptr rem data r BS LK
(gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
jo_set_scalar_stmt S4L HIx S4F f ->
0 <= ret < 2^64 -> ret mod 2 = 0 ->
SINV m md A F fc errv ptr rem data r BS LK ->
KS ret r ->
realizes rsegs (mkCfg (MS (mkR (Z_to_bv 64 ret) (Z_to_bv 64 spf) gp (Z_to_bv 64 0x77c00) t0 t1 t2 (Z_to_bv 64 p) s1v (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 f) fc None m (seg_rom rsegs)) md) T.
Proof.
intros f ret m md A F fc errv ptr rem data r BS LK gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ST_ Hret Hret2 SI K.
pose proof SI as ((PX & VM & FS & FRM & LOC & LCK & G & ST & SAV & ERR & _) & HP & RR & RD).
pose proof spf16' as SPF16. unfold TGT_STACK in LOS.
eapply ST_ with (A := A) (BS := BS) (LB := LK ++ LB) (r := r) (lo := lo);
[ split; [exact HP|]; rewrite unsigned_lit by (unfold spf; lia);
split; [exact ST|]; split; [exact LO|]; split; [unfold spf; lia|]; split; [exact SPF16|]; split; [unfold spf; lia|];
split; [exact ERR|]; split; [reflexivity | rewrite unsigned_lit by lia; exact Hret2]
| exact RR | reflexivity |].
intros ms' md' m' rv (RS & VM' & ST' & HPR' & [errv' ERR']) ERRx RR' HP'.
destruct RS as (xt0 & xt1 & xt2 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xt3 & xt4 & xt5 & xt6 & F' & fc' & -> & FS' & FRM').
cbn [hl_segs hl_tp S4L] in ST', HPR', ERR', HP', ERRx. rewrite unsigned_lit in ST', HPR' by (unfold spf; lia).
replace (ret_pc (Z_to_bv 64 ret)) with (Z_to_bv 64 ret : word) by (symmetry; apply ret_pc_even; [lia | exact Hret2]).
unfold KS, sstate in K. eapply K. eapply SINV_ret; [exact SI | exact HPR' | exact VM' | exact FS' | exact (FRM' FRM) | exact ST' | exact ERRx | exact HP' | exact RR' | exact RD].
Qed.

#[using="payload LO LOS HT HT62 SZ D0 INB DLO"] Lemma cii_call : forall (e kmax A1 A2 ret : Z) m md (A : AS S4L HIx) F fc errv ptr rem data r BS LK
(gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
cii_stmt rsegs e kmax A1 A2 -> 0 <= kmax ->
0 <= ret < 2^64 -> ret mod 2 = 0 ->
SINV m md A F fc errv ptr rem data r BS LK ->
bv_unsigned a1 = A1 -> bv_unsigned a2 = A2 ->
(forall m' (xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
SINV m' md A F fc errv ptr (Z.max (rem - kmax) 0) (firstn (Z.to_nat (Z.max (rem - kmax) 0)) data) r BS LK ->
realizes rsegs (mkCfg (MS (mkR (Z_to_bv 64 ret) (Z_to_bv 64 spf) gp (Z_to_bv 64 0x77c00) xt0 xt1 xt2 (Z_to_bv 64 p) s1v xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
F (Z_to_bv 64 ret) fc None m' (seg_rom rsegs)) md) T) ->
realizes rsegs (mkCfg (MS (mkR (Z_to_bv 64 ret) (Z_to_bv 64 spf) gp (Z_to_bv 64 0x77c00) t0 t1 t2 (Z_to_bv 64 p) s1v (Z_to_bv 64 (spf + 32)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e) fc None m (seg_rom rsegs)) md) T.
Proof.
intros e kmax A1 A2 ret m md A F fc errv ptr rem data r BS LK gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 CI Hk Hret Hret2 SI HA1 HA2 K.
pose proof SI as ((PX & VM & FS & FRM & LOC & LCK & G & ST & SAV & ERR & [j16 SCR] & [sj STR] & FD & PP & D1 & D2 & R0) & HP & RR & RD).
pose proof FD as (FDc & B & L & P0 & P1).
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK. pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
unfold TGT_STACK in LOS. unfold_consts.
unfold cii_stmt, fdp_post, fdp_W, fdp_pre in CI.
apply rz_evt; [exact MOK|].
eapply evt_cut.
{ eapply CI with (P := spf + 32) (ptr := ptr) (rem := rem) (lo := lo) (data := data);
[ split; [reflexivity|]; split; [exact FDc|]; split; [exact B|]; split; [exact L|]; split; [exact PP|];
rewrite unsigned_lit by (unfold spf; lia); split; [exact ST|]; split; [unfold spf; lia|]; split; [unfold spf; lia|]; split; [unfold spf; clia|]; exact MI
| exact HA1 | exact HA2 ]. }
intros ms' (yt0 & yt1 & yt2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & yt3 & yt4 & yt5 & yt6 & m1 & -> & MU & WM & MI1 & _ & FD1 & B1 & ST1).
rewrite unsigned_lit in ST1, MU by (unfold spf; lia).
replace (ret_pc (Z_to_bv 64 ret)) with (Z_to_bv 64 ret : word) by (symmetry; apply ret_pc_even; [lia | exact Hret2]).
replace (spf + 32 + 8) with (spf + 40) in MU by lia. replace (spf + 32 + 16) with (spf + 48) in MU by lia.
apply evt_RZ_done. eapply K.
eapply (SINV_munch m m1); [exact SI | exact MU | exact WM | exact MI1 | | apply fsaved_refl | exact FRM | exact ST1 | | lia | lia | lia | lia |].
- apply Forall_cons; [cbn; unfold spf; lia |]. apply Forall_cons; [cbn; unfold spf; lia | apply Forall_nil].
- eapply fdp_shrink; [exact FD | lia | exact FD1 | exact B1].
- intros sjx STRx. exists sjx. eapply rw_cells_transport; [exact STRx | exact MU | exact WM | cbn; unfold spf; lia].
Qed.

#[using="SETI CII_INT payload LO LOS SPA HT HT62 SZ D0 INB DLO HINV_callc"] Lemma seg_setint : forall m md (A : AS S4L HIx) F fc errv ptr rem data r BS LK
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
SINV m md A F fc errv ptr rem data r BS LK ->
KS 0x2110c r ->
realizes rsegs (mkCfg (sstate x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F 0x210ec fc m) md) T.
Proof.
intros m md A F fc errv ptr rem data r BS LK x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 SI K.
pose proof SI as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _) & HP & _ & _).
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK. pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl (@nil (Z * Z)) m) as MU. pose proof (wmono_refl rsegs m) as WM.
unfold TGT_STACK in LOS. unfold sstate. unfold_consts.
apply rz_evt; [exact MOK|]. step. step. step. step. step. fold_mkR. apply evt_RZ_done.
eapply (cii_call QmtA.CII_INT_U 4 (2^64 - 2^31) (2^31 - 1) 0x21100); [exact CII_INT | lia | lia | reflexivity | exact SI | vm_compute; reflexivity | vm_compute; reflexivity |].
clear m MU WM MI MOK HP SI.
intros m xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 SI.
pose proof SI as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _) & HP & _ & _).
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK. pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl (@nil (Z * Z)) m) as MU. pose proof (wmono_refl rsegs m) as WM.
apply rz_evt; [exact MOK|]. step. step. step. fold_mkR. apply evt_RZ_done.
eapply (set_call 0x2598c 0x2110c); [exact SETI | lia | reflexivity | exact SI | exact K].
Qed.

#[using="SETI64 CII_I64 payload LO LOS SPA HT HT62 SZ D0 INB DLO HINV_callc"] Lemma seg_setint64 : forall m md (A : AS S4L HIx) F fc errv ptr rem data r BS LK
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
SINV m md A F fc errv ptr rem data r BS LK ->
KS 0x2112c r ->
realizes rsegs (mkCfg (sstate x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F 0x2110c fc m) md) T.
Proof.
intros m md A F fc errv ptr rem data r BS LK x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 SI K.
pose proof SI as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _) & HP & _ & _).
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK. pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl (@nil (Z * Z)) m) as MU. pose proof (wmono_refl rsegs m) as WM.
unfold TGT_STACK in LOS. unfold sstate. unfold_consts.
apply rz_evt; [exact MOK|]. step. step. step. step. step. fold_mkR. apply evt_RZ_done.
eapply (cii_call QmtA.CII_I64_U 8 (2^63) (2^63 - 1) 0x21120); [exact CII_I64 | lia | lia | reflexivity | exact SI | vm_compute; reflexivity | vm_compute; reflexivity |].
clear m MU WM MI MOK HP SI.
intros m xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 SI.
pose proof SI as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _) & HP & _ & _).
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK. pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl (@nil (Z * Z)) m) as MU. pose proof (wmono_refl rsegs m) as WM.
apply rz_evt; [exact MOK|]. step. step. step. fold_mkR. apply evt_RZ_done.
eapply (set_call 0x259c0 0x2112c); [exact SETI64 | lia | reflexivity | exact SI | exact K].
Qed.

#[using="SETU64 CII_U64 payload LO LOS SPA HT HT62 SZ D0 INB DLO HINV_callc"] Lemma seg_setuint64 : forall m md (A : AS S4L HIx) F fc errv ptr rem data r BS LK
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
SINV m md A F fc errv ptr rem data r BS LK ->
KS 0x21148 r ->
realizes rsegs (mkCfg (sstate x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F 0x2112c fc m) md) T.
Proof.
intros m md A F fc errv ptr rem data r BS LK x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 SI K.
pose proof SI as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _) & HP & _ & _).
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK. pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl (@nil (Z * Z)) m) as MU. pose proof (wmono_refl rsegs m) as WM.
unfold TGT_STACK in LOS. unfold sstate. unfold_consts.
apply rz_evt; [exact MOK|]. step. step. step. step. fold_mkR. apply evt_RZ_done.
eapply (cii_call QmtA.CII_U64_U 8 0 (2^64 - 1) 0x2113c); [exact CII_U64 | lia | lia | reflexivity | exact SI | vm_compute; reflexivity | vm_compute; reflexivity |].
clear m MU WM MI MOK HP SI.
intros m xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 SI.
pose proof SI as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _) & HP & _ & _).
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK. pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl (@nil (Z * Z)) m) as MU. pose proof (wmono_refl rsegs m) as WM.
apply rz_evt; [exact MOK|]. step. step. step. fold_mkR. apply evt_RZ_done.
eapply (set_call 0x25d28 0x21148); [exact SETU64 | lia | reflexivity | exact SI | exact K].
Qed.

#[using="SETD CFP payload LO LOS SPA HT HT62 SZ D0 INB DLO HINV_callc"] Lemma seg_setdouble : forall m md (A : AS S4L HIx) F fc errv ptr rem data r BS LK
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
SINV m md A F fc errv ptr rem data r BS LK ->
KS 0x21168 (set_double_root (fn_dbl_to_json_string S4F) r) ->
realizes rsegs (mkCfg (sstate x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F 0x21148 fc m) md) T.
Proof.
intros m md A F fc errv ptr rem data r BS LK x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 SI K.
pose proof SI as ((PX & VM & FS & FRM & LOC & LCK & G & ST & SAV & ERR & [j16 SCR] & [sj STR] & FD & PP & D1 & D2 & R0) & HP & RR & RD).
pose proof FD as (FDc & B & L & P0 & P1).
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK. pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
destruct (hj_ro m MI) as [RO1 RO2].
pose proof spf16' as SPF16. unfold TGT_STACK in LOS. unfold sstate. unfold_consts.
pose proof (munch_refl (@nil (Z * Z)) m) as MU. pose proof (wmono_refl rsegs m) as WM.
apply rz_evt; [exact MOK|].
step. step. step. step. step. step. fold_mkR. clear MU WM.
pose proof CFP as CFP'. unfold cfp_stmt, CFP_P, CFP_STK_P, IHI_P, fdp_preS, fdp_postF, fdp_WS in CFP'.
clear SCR STR SAV LOC LCK ERR RO1 RO2.
eapply evt_cut.
{ eapply CFP' with (P := spf + 32) (ptr := ptr) (rem := rem) (lo := lo) (data := data).
- split; [apply bv_eq; rewrite !unsigned_lit by (unfold spf; lia); unfold spf; lia|]. split; [exact FDc|]. split; [exact B|]. split; [exact L|]. split; [exact PP|].
rewrite unsigned_lit by (unfold spf; lia). split; [exact ST|]. split; [unfold spf; lia|]. split; [unfold spf; lia|]. split; [unfold spf; clia|]. exact MI.
- clia.
- rewrite freg_get_same by reflexivity. vm_compute. reflexivity.
- rewrite freg_get_other by (vm_compute; reflexivity). rewrite freg_get_same by reflexivity. vm_compute. reflexivity.
- exact FRM. }
intros ms' (yt0 & yt1 & yt2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & yt3 & yt4 & yt5 & yt6 & F1 & fc1 & m1 & -> & FS1 & FRM1 & MU1 & WM1 & MI1 & FD1 & B1 & ST1).
rewrite unsigned_lit in ST1, MU1 by (unfold spf; lia).
replace (ret_pc (Z_to_bv 64 0x21160)) with (Z_to_bv 64 0x21160 : word) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
replace (spf + 32 + 8) with (spf + 40) in MU1 by lia. replace (spf + 32 + 16) with (spf + 48) in MU1 by lia.
rename MU1 into MU. rename WM1 into WM.
assert (SI1 : SINV m1 md A F1 fc1 errv ptr (Z.max (rem - 9) 0) (firstn (Z.to_nat (Z.max (rem - 9) 0)) data) r BS LK).
{ eapply (SINV_munch m m1); [exact SI | exact MU | exact WM | exact MI1 | | | exact FRM1 | exact ST1 | | lia | lia | lia | lia |].
- apply Forall_cons; [cbn; unfold spf; lia |]. apply Forall_cons; [cbn; unfold spf; lia | apply Forall_nil].
- eapply fsaved_trans; [| exact FS1]. intros k Hk. rewrite !freg_get_other; [reflexivity|..]; cbn [FSAVED In] in Hk;
repeat (destruct Hk as [<- | Hk]); try (vm_compute; reflexivity); destruct Hk.
- eapply fdp_shrink; [exact FD | lia | exact FD1 | exact B1].
- intros sjx STRx. exists sjx. eapply rw_cells_transport; [exact STRx | exact MU | exact WM | cbn; unfold spf; lia]. }
pose proof SI1 as ((_ & _ & _ & _ & _ & _ & G1 & _ & _ & ERR1 & _) & HP1 & RR1 & _).
clear ST FD FDc B MU WM.
step. step. fold_mkR. apply evt_RZ_done.
pose proof SETD as SD. unfold jo_set_double_stmt2, SD_ENTRY_P, SD_TBL_P, SD_STK in SD.
eapply SD with (A := A) (BS := BS) (LB := LK ++ LB) (r := r) (lo := lo);
[ split; [exact HP1|]; rewrite unsigned_lit by (unfold spf; lia);
split; [exact ST1|]; split; [exact LO|]; split; [unfold spf; lia|]; split; [exact SPF16|]; split; [unfold spf; lia|];
split; [exact ERR1|]; split; [reflexivity | vm_compute; reflexivity]
| exact RR1 | reflexivity | exact (proj1 (proj2 G1)) |].
intros ms' md' m' rv (RS & VM' & ST' & HPR' & [errv' ERR']) ERRx (A' & BS' & RR' & HP').
destruct RS as (xt0 & xt1 & xt2 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xt3 & xt4 & xt5 & xt6 & F' & fc' & -> & FS' & FRM').
cbn [hl_segs hl_tp S4L] in ST', HPR', ERR', HP', ERRx. rewrite unsigned_lit in ST', HPR' by (unfold spf; lia).
replace (ret_pc (Z_to_bv 64 0x21168)) with (Z_to_bv 64 0x21168 : word) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
unfold KS, sstate in K. eapply K.
eapply SINV_ret; [exact SI1 | exact HPR' | exact VM' | exact FS' | exact (FRM' FRM1) | exact ST' | exact ERRx | exact HP' | exact RR' |].
pose proof (rdepth_set_double_root (fn_dbl_to_json_string S4F) r). lia.
Qed.

#[using="CRLS payload LO LOS SPA HT HT62 SZ D0 INB DLO"] Lemma crls_call : forall (ret : Z) m md (A : AS S4L HIx) F fc errv ptr rem data r BS LK
(gp t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
(ret = 0x21178 \/ ret = 0x21204) ->
SINV m md A F fc errv ptr rem data r BS LK ->
(forall m' ptr' rem' data' (n : Z) (str rest : list byte) (xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
SINV m' md A F fc errv ptr' rem' data' r BS LK ->
rw_cells rsegs m' (spf + 8) [C1 (Z_to_bv 8 (2 * n)); CB 23 (str ++ Z_to_bv 8 0 :: rest)] ->
0 <= n <= 10 -> Z.of_nat (length str) <= n -> ~ In (Z_to_bv 8 0) str -> mem_inv rsegs m' ->
realizes rsegs (mkCfg (MS (mkR (Z_to_bv 64 ret) (Z_to_bv 64 spf) gp (Z_to_bv 64 0x77c00) xt0 xt1 xt2 (Z_to_bv 64 p) s1v xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
F (Z_to_bv 64 ret) fc None m' (seg_rom rsegs)) md) T) ->
realizes rsegs (mkCfg (MS (mkR (Z_to_bv 64 ret) (Z_to_bv 64 spf) gp (Z_to_bv 64 0x77c00) t0 t1 t2 (Z_to_bv 64 p) s1v (Z_to_bv 64 (spf + 8)) (Z_to_bv 64 (spf + 32)) (Z_to_bv 64 10) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 CRLS_P) fc None m (seg_rom rsegs)) md) T.
Proof.
intros ret m md A F fc errv ptr rem data r BS LK gp t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Hret SI K.
pose proof SI as ((PX & VM & FS & FRM & LOC & LCK & G & ST & SAV & ERR & [j16 SCR] & [sj STR] & FD & PP & D1 & D2 & R0) & HP & RR & RD).
pose proof FD as (FDc & B & L & P0 & P1).
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK. pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
unfold TGT_STACK in LOS. unfold_consts.
assert (Hr : 0 <= ret < 2^64 /\ ret mod 2 = 0) by (destruct Hret as [-> | ->]; split; try lia; reflexivity).
pose proof CRLS as CR. unfold crls_stmt, crls_post, crls_W, CRLS_FRAME_P in CR.
apply rz_evt; [exact MOK|].
clear SCR SAV LOC LCK ERR.
eapply evt_cut.
{ eapply (CR _ (Z_to_bv 64 spf)) with (S := spf + 8) (P := spf + 32) (ptr := ptr) (rem := rem) (lo := lo) (maxlen := 10) (data := data);
[ reflexivity | reflexivity | reflexivity | lia | exact STR | exact FDc | exact B | exact L | lia
| rewrite unsigned_lit by (unfold spf; lia); exact ST | rewrite unsigned_lit by (unfold spf; lia); unfold spf; lia
| rewrite unsigned_lit by (unfold spf; lia); lia | lia | rewrite unsigned_lit by (unfold spf; lia); unfold spf; clia | exact MI ]. }
intros ms' (yt0 & yt1 & yt2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & yt3 & yt4 & yt5 & yt6 & m1 & n & k & str & rest & -> & MU & WM & MI1 & Hn & Hstr & NONUL & STR1 & Hk & FD1 & B1 & ST1).
rewrite unsigned_lit in ST1, MU by (unfold spf; lia).
replace (ret_pc (Z_to_bv 64 ret)) with (Z_to_bv 64 ret : word) by (symmetry; apply ret_pc_even; [lia | exact (proj2 Hr)]).
pose proof B1 as B1k. rewrite <- (firstn_skipn (Z.to_nat k) data) in B1k. apply bytes_at_app in B1k as [_ B1k].
rewrite firstn_length_le in B1k by lia. rewrite Z2Nat.id in B1k by lia.
assert (FD1' : fdp_at spf m1 (ptr + k) (rem - k) (skipn (Z.to_nat k) data)).
{ split; [exact FD1|]. split; [exact B1k|]. split; [rewrite length_skipn; lia | lia]. }
apply evt_RZ_done. eapply (K m1 (ptr + k) (rem - k)); [| exact STR1 | exact Hn | exact Hstr | exact NONUL | exact MI1].
eapply (SINV_munch m m1); [exact SI | exact MU | exact WM | exact MI1 | | apply fsaved_refl | exact FRM | exact ST1 | exact FD1' | lia | lia | lia | lia |].
- apply Forall_cons; [cbn; unfold spf; lia |]. apply Forall_cons; [cbn; unfold spf; lia |]. apply Forall_cons; [cbn; unfold spf; lia | apply Forall_nil].
- intros sjx _. exists (Z_to_bv 8 (2 * n) :: str ++ Z_to_bv 8 0 :: rest).
eapply rw_cells_recast; [exact STR1 | | cbn; rewrite ?app_nil_r; reflexivity | reflexivity].
destruct STR1 as [[WF _] _]. cbn in WF |- *. rewrite length_app in *. cbn [length] in *. lia.
Qed.

#[using="CRLS SETS payload LO LOS SPA HT HT62 SZ D0 INB DLO HINV_callc"] Lemma seg_setstring : forall m md (A : AS S4L HIx) F fc errv ptr rem data r BS LK
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
SINV m md A F fc errv ptr rem data r BS LK ->
KS 0x211b4 (set_string_root r) ->
realizes rsegs (mkCfg (sstate x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F 0x21168 fc m) md) T.
Proof.
intros m md A F fc errv ptr rem data r BS LK x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 SI K.
pose proof SI as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _) & HP & _ & _).
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK. pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl (@nil (Z * Z)) m) as MU. pose proof (wmono_refl rsegs m) as WM.
unfold TGT_STACK in LOS. unfold sstate. unfold_consts.
apply rz_evt; [exact MOK|]. step. step. step. step. fold_mkR. apply evt_RZ_done.
eapply (crls_call 0x21178); [left; reflexivity | exact SI |].
clear m MU WM MI MOK HP SI.
intros m ptr1 rem1 data1 n str rest xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 SI STR Hn Hstr NONUL MI.
pose proof SI as ((PX & VM & FS & FRM & LOC & LCK & G & ST & SAV & ERR & [j16 SCR] & _ & FD & PP & D1 & D2 & R0) & HP & RR & RD).
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (munch_refl (@nil (Z * Z)) m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof spf16' as SPF16.
apply rz_evt; [exact MOK|].

step. step. rewrite short_flag0 by lia. step. try if_true. step. step. step. fold_mkR.

pose proof STR as STR2. apply rw_cells_app with (cs1 := [_]) in STR2 as [_ STRB]. cbn [cells_size csize Nat.add] in STRB.
pose proof (rw_cells_bytes_at rsegs m _ _ STRB) as SB. cbn [cells_bytes cbytes app] in SB. rewrite app_nil_r in SB.
change (spf + 8 + Z.of_nat 1) with (spf + 8 + 1) in SB.
assert (LREST : Z.of_nat (length rest) = 22 - Z.of_nat (length str)).
{ destruct STR as [[WF _] _]. cbn in WF. rewrite length_app in WF. cbn [length] in WF. lia. }
pose proof (Z.mod_pos_bound (- (spf + 8 + 1 + Z.of_nat (length str) + 1)) 8 ltac:(lia)) as MB.
apply evt_RZ_done.
pose proof SETS as SS. unfold jo_set_string_stmt, set_string_post in SS.
eapply SS with (A := A) (BS := BS) (LB := LK ++ LB) (r := r) (lo := lo) (S := spf + 8 + 1) (sb := str) (slack := rest);
[ split; [exact HP|]; rewrite unsigned_lit by (unfold spf; lia);
split; [exact ST|]; split; [exact LO|]; split; [unfold spf; lia|]; split; [exact SPF16|]; split; [unfold spf; lia|];
split; [exact ERR|]; split; [reflexivity | vm_compute; reflexivity]
| exact RR
| split; [exact SB|]; split; [apply notin0_forall; exact NONUL|]; rewrite unsigned_lit by (unfold spf; lia); unfold spf; split; [lia | split; [lia | lia]]
| lia | reflexivity | apply bv_eq; rewrite !unsigned_lit by (unfold spf; lia); unfold spf; lia |].
intros ms' md' m' rv (RS & VM' & ST' & HPR' & [errv' ERR']) (A' & BS' & RR' & HP').
destruct RS as (zt0 & zt1 & zt2 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & zt3 & zt4 & zt5 & zt6 & F' & fc' & -> & FS' & FRM').
cbn [hl_segs hl_tp S4L] in ST', HPR', ERR', HP' |- *. rewrite unsigned_lit in ST', HPR' by (unfold spf; lia).
replace (ret_pc (Z_to_bv 64 0x21198)) with (Z_to_bv 64 0x21198 : word) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
assert (SI' : SINV m' md' A' F' fc' errv' ptr1 rem1 data1 (set_string_root r) BS' LK).
{ eapply SINV_ret; [exact SI | exact HPR' | exact VM' | exact FS' | exact (FRM' FRM) | exact ST' | exact ERR' | exact HP' | exact RR' |].
pose proof (rdepth_set_string_root r). lia. }
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR') in STR; [| left; cbn; unfold spf; lia]. cbn [hl_segs S4L] in STR.
pose proof (heap_model_ok _ _ _ _ _ _ HP') as MOK'. pose proof (heap_mem_inv _ _ _ _ _ _ HP') as MI'. cbn [hl_segs S4L] in MI'.
clear MU WM. pose proof (munch_refl (@nil (Z * Z)) m') as MU. pose proof (wmono_refl rsegs m') as WM.
apply rz_evt; [exact MOK'|]. step. step. rewrite short_flag0 by lia. step. try if_true. fold_mkR.
apply evt_RZ_done. unfold KS, sstate in K. eapply K. exact SI'.
Qed.

#[using="SETB payload LO LOS SPA HT HT62 SZ D0 INB DLO HINV_callc"] Lemma seg_setbool : forall m md (A : AS S4L HIx) F fc errv ptr rem data r BS LK
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
SINV m md A F fc errv ptr rem data r BS LK ->
KS 0x211f4 r ->
realizes rsegs (mkCfg (sstate x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F 0x211b4 fc m) md) T.
Proof.
intros m md A F fc errv ptr rem data r BS LK x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 SI K.
pose proof SI as ((PX & VM & FS & FRM & LOC & LCK & G & ST & SAV & ERR & [j16 SCR] & [sj STR] & FD & PP & D1 & D2 & R0) & HP & RR & RD).
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK. pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
unfold TGT_STACK in LOS. unfold sstate. unfold_consts.
apply rz_evt; [exact MOK|].
eapply cbool_P; [exact FD | exact PP | unfold spf; clia | exact MI | unfold spf; lia | unfold spf; lia |].
intros m1 rem1 a0' a1' a2' a3' FD1 Hrem1 Ha1 MU WM MI1.
assert (ST1 : stk rsegs m1 lo spf).
{ eapply stk_transport_disjoint; [exact ST | exact MU | exact WM | cbn; lia]. }
assert (SI1 : SINV m1 md A F fc errv ptr rem1 (firstn (Z.to_nat rem1) data) r BS LK).
{ eapply (SINV_munch m m1); [exact SI | exact MU | exact WM | exact MI1 | | apply fsaved_refl | exact FRM | exact ST1 | exact FD1 | lia | lia | lia | lia |].
- apply Forall_cons; [cbn; unfold spf; lia | apply Forall_nil].
- intros sjx STRx. exists sjx. eapply rw_cells_transport; [exact STRx | exact MU | exact WM | cbn; lia]. }
clear ST SCR STR FD SAV LOC LCK ERR.
step. step. fold_mkR.
apply evt_RZ_done.
eapply (set_call 0x25754 0x211f4); [exact SETB | lia | reflexivity | exact SI1 | exact K].
Qed.

#[using="CRLS SETSL payload LO LOS SPA HT HT62 SZ D0 INB DLO HINV_callc"] Lemma seg_setstrlen : forall m md (A : AS S4L HIx) F fc errv ptr rem data r BS LK
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
SINV m md A F fc errv ptr rem data r BS LK ->
KSF 0x21230 (set_string_root r) ->
realizes rsegs (mkCfg (sstate x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F 0x211f4 fc m) md) T.
Proof.
intros m md A F fc errv ptr rem data r BS LK x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 SI K.
pose proof SI as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _) & HP & _ & _).
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK. pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl (@nil (Z * Z)) m) as MU. pose proof (wmono_refl rsegs m) as WM.
unfold TGT_STACK in LOS. unfold sstate. unfold_consts.
apply rz_evt; [exact MOK|]. step. step. step. step. fold_mkR. apply evt_RZ_done.
eapply (crls_call 0x21204); [right; reflexivity | exact SI |].
clear m MU WM MI MOK HP SI.
intros m ptr1 rem1 data1 n str rest xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 SI STR Hn Hstr NONUL MI.
pose proof SI as ((PX & VM & FS & FRM & LOC & LCK & G & ST & SAV & ERR & [j16 SCR] & _ & FD & PP & D1 & D2 & R0) & HP & RR & RD).
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (munch_refl (@nil (Z * Z)) m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof spf16' as SPF16.
apply rz_evt; [exact MOK|].

step. step. rewrite short_flag0 by lia. step. try if_true. step. step. try rewrite short_size by lia. step. try rewrite short_size by lia. step. step. fold_mkR.

pose proof STR as STR2. apply rw_cells_app with (cs1 := [_]) in STR2 as [_ STRB]. cbn [cells_size csize Nat.add] in STRB.
pose proof (rw_cells_bytes_at rsegs m _ _ STRB) as SB. cbn [cells_bytes cbytes app] in SB. rewrite app_nil_r in SB.
change (spf + 8 + Z.of_nat 1) with (spf + 8 + 1) in SB.
assert (LREST : Z.of_nat (length rest) = 22 - Z.of_nat (length str)).
{ destruct STR as [[WF _] _]. cbn in WF. rewrite length_app in WF. cbn [length] in WF. lia. }
pose proof SB as SBn. rewrite <- (firstn_skipn (Z.to_nat n) (str ++ Z_to_bv 8 0 :: rest)) in SBn. apply bytes_at_app in SBn as [SBn _].
assert (LN : Z.of_nat (length (firstn (Z.to_nat n) (str ++ Z_to_bv 8 0 :: rest))) = n).
{ rewrite firstn_length_le; [lia|]. rewrite length_app. cbn [length]. lia. }
apply evt_RZ_done.
pose proof SETSL as SS. unfold jo_set_string_len_stmt, set_string_post in SS.
eapply SS with (A := A) (BS := BS) (LB := LK ++ LB) (r := r) (lo := lo) (S := spf + 8 + 1) (sb := firstn (Z.to_nat n) (str ++ Z_to_bv 8 0 :: rest));
[ split; [exact HP|]; rewrite unsigned_lit by (unfold spf; lia);
split; [exact ST|]; split; [exact LO|]; split; [unfold spf; lia|]; split; [exact SPF16|]; split; [unfold spf; lia|];
split; [exact ERR|]; split; [reflexivity | vm_compute; reflexivity]
| exact RR
| split; [exact SBn|]; rewrite unsigned_lit by (unfold spf; lia); rewrite LN; unfold spf; lia
| rewrite LN; lia | reflexivity | apply bv_eq; rewrite !unsigned_lit by (unfold spf; lia); unfold spf; lia
| rewrite LN; rewrite unsigned_lit by lia; rewrite Z.add_0_r, swrap32_id by lia; reflexivity |].
intros ms' md' m' rv (RS & VM' & ST' & HPR' & [errv' ERR']) (A' & BS' & RR' & HP').
destruct RS as (zt0 & zt1 & zt2 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & zt3 & zt4 & zt5 & zt6 & F' & fc' & -> & FS' & FRM').
cbn [hl_segs hl_tp S4L] in ST', HPR', ERR', HP' |- *. rewrite unsigned_lit in ST', HPR' by (unfold spf; lia).
replace (ret_pc (Z_to_bv 64 0x21230)) with (Z_to_bv 64 0x21230 : word) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
unfold KSF, sstate in K. eapply K.
- eapply SINV_ret; [exact SI | exact HPR' | exact VM' | exact FS' | exact (FRM' FRM) | exact ST' | exact ERR' | exact HP' | exact RR' |].
pose proof (rdepth_set_string_root r). lia.
- exists n, (str ++ Z_to_bv 8 0 :: rest). split; [lia|].
eapply (heap_pres_rw_cells S4L); [exact HPR' | exact STR | left; cbn; unfold spf; lia].
Qed.

#[using="SETI SETI64 SETU64 SETB SETD CFP CRLS SETS SETSL CII_INT CII_I64 CII_U64 payload LO LOS SPA HT HT62 SZ D0 INB DLO HINV_callc"] Lemma seg_setters : forall m md (A : AS S4L HIx) F fc errv ptr rem data r BS LK
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
SINV m md A F fc errv ptr rem data r BS LK ->
KSF 0x21230 (set_string_root (set_string_root (set_double_root (fn_dbl_to_json_string S4F) r))) ->
realizes rsegs (mkCfg (sstate x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F 0x210ec fc m) md) T.
Proof.
intros m md A F fc errv ptr rem data r BS LK x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 SI K.
eapply seg_setint; [exact SI|]. unfold KS; intros.
eapply seg_setint64; [eassumption|]. unfold KS; intros.
eapply seg_setuint64; [eassumption|]. unfold KS; intros.
eapply seg_setdouble; [eassumption|]. unfold KS; intros.
eapply seg_setstring; [eassumption|]. unfold KS; intros.
eapply seg_setbool; [eassumption|]. unfold KS; intros.
eapply seg_setstrlen; [eassumption|]. exact K.
Qed.
End Setters.
End Ctx.
End HarnJoP2.

End RC__1.
