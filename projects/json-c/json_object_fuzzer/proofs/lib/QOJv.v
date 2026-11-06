(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs QCiC Q6sh QQwg QKTr QJBH QvG1 QyW2 Qp4j QDw3 QUxU QNwL QYnC QSsj QZbm QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QDw3 QUxU QNwL QYnC QSsj QZbm.
Import QlES.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.

Section S.
Context {BAND : Band}.
Variable C : arun_components.
Hypothesis HRT : ac_RTconst C = RTconst.
Hypothesis HRF : ac_RFake C = RFake.

Lemma ARUN_uar_on : forall s LB FS RE m, ARUN C s LB FS RE m ->
ro_cells asegs m 0x0e5e10 [C8 (Z_to_bv 64 0x0efb00)] /\ ro_cells asegs m 0x0efb00 [C4 (Z_to_bv 64 1)].
Proof.
intros s LB FS RE m AR. destruct (ARUN_open C _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
destruct AX as (GC & R1 & _). rewrite HRT in R1.
pose proof (RT_img _ _ _ R1 20%nat _ _ eq_refl) as K20. cbn [fst snd] in K20.
pose proof (RT_img _ _ _ R1 6%nat _ _ eq_refl) as K6. cbn [fst snd] in K6.
split; [| exact K6].
apply (proj1 (ro_cells_app asegs m _ [C8 (Z_to_bv 64 0x0e7df8); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0x18161c); C8 (Z_to_bv 64 0x17f598)] _)) in K20 as [_ K].
exact K.
Qed.

Lemma ARUN_fframes_nodup : forall s LB FS RE m, ARUN C s LB FS RE m -> List.NoDup (map ff_addr FS).
Proof.
intros s LB FS RE m AR. destruct (ARUN_open C _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
destruct AX as (GC & _ & _ & _ & _ & _ & _ & _ & R8). rewrite HRF in R8.
eapply Permutation_NoDup; [apply Permutation_map; apply Permutation_sym; exact PF|]. exact (RFake_nodup RE X FS0 m R8).
Qed.

End S.
End Mq0.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsGW Qu1d QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk.Mq1.
Import QlES.
Import ListNotations. Local Ltac QsGW.small_offset k ::= QsGW.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Unset Keyed Unification.

Definition MUTEX_HELD : Z := 1152921504606846976.

Lemma max_count_facts : forall c, 1 <= c <= 31 -> 2 <= max_count c <= 16 /\ max_count c mod 2 = 0.
Proof.
intros c Hc.
assert (H : forallb (fun c => (2 <=? max_count c) && (max_count c <=? 16) && (max_count c mod 2 =? 0))
(map Z.of_nat (seq 1 31)) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in H. specialize (H c).
assert (Hin : In c (map Z.of_nat (seq 1 31))) by (apply in_map_iff; exists (Z.to_nat c); split; [lia| apply in_seq; lia]).
specialize (H Hin). apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.eqb_eq in H3. lia.
Qed.

Lemma le4_sx32' (v : word) : le4 (sx32 v) = le4 v.
Proof.
transitivity (le4 (Z_to_bv 64 (bv_unsigned v))); [| rewrite Z_to_bv_bv_unsigned; reflexivity].
unfold sx32. apply le4_eqm.
unfold bv_swrap. pose proof (bv_unsigned_in_range 64 v) as R.
set (u := bv_unsigned v) in *. clearbody u. unfold bv_wrap.
change (bv_modulus 32) with (2^32)%Z. change (bv_half_modulus 32) with (2^31)%Z.
Z.div_mod_to_equations. lia.
Qed.
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QDw3 QNwL QYnC QSsj QNQk.Mq1.
Import QlES. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).
Local Notation mem := (word -> option byte) (only parsing).

Definition map_or_die_entry : Z := 0x7f80c.
Definition MAPORDIE_STACK : Z := 704.

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).

Definition map_or_die_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(A N lo : Z) (m : mem) (ans : ansA) : machine_state -> Prop :=
fun ms' =>
match ans with
| AErr => True
| AOk x => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - MAPORDIE_STACK, bv_unsigned sp); (A, A + N)] m m'
/\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ RTconst RE X m'
/\ x = A /\ a0 = wz A /\ rw_cells asegs m' A [CB (Z.to_nat N) (repeat (b8 0) (Z.to_nat N))]
end.

Definition map_or_die_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (A N lo : Z),
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - MAPORDIE_STACK ->
A mod 4096 = 0 -> N mod 4096 = 0 -> 0 < N -> 0x645000 <= A -> A + N <= band_lo ->
rt_avoid RE X (A, A + N) ->
impl asegs (at_nodeA L asegs) (enode (NMmap A N PROT_RW FL_FIXED) (dec_fixedA A N))
(epost (map_or_die_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A N lo m))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz A) (wz N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz map_or_die_entry) fc None m (seg_rom asegs)).
End S.
End Mq2.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5.
Import Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq1 QNQk.Mq4.
Import QlES.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QsGW.small_offset k ::= QsGW.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition map_with_callback_entry : Z := 0x7f6c0.
Definition mmap_fixed_impl_entry : Z := 0x77488.
Definition MMAPFIXED_IMPL_STACK : Z := 368.
Definition MMAPFIXED_STACK : Z := 400.

Definition fixed_fp (A N : Z) (ans : ansA) : list (Z * Z) :=
match ans with AErr => [] | AOk _ => [(A, A + N)] end.

Lemma mmap_len_aligned : forall len, len mod 4096 = 0 -> mmap_len len = len.
Proof. intros. unfold mmap_len, page_round_up_Z, page_size. Z.div_mod_to_equations. lia. Qed.

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Local Notation atn := (at_nodeA L asegs).

Definition map_fixed_post_k (K : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(A N lo : Z) (m : word -> option byte) (ans : ansA) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch ((bv_unsigned sp - K, bv_unsigned sp) :: fixed_fp A N ans) m m'
/\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ RTconst RE X m'
/\ match ans with
| AErr => False
| AOk x => x = A /\ a0 = wz A /\ rw_cells asegs m' A [CB (Z.to_nat N) (repeat (b8 0) (Z.to_nat N))]
end.
Definition map_fixed_post := map_fixed_post_k MMAPFIXED_STACK.

Definition get_named_mapping_fd_entry : Z := 0x77b1c.

Lemma get_named_mapping_fd_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m lo,
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 272 ->
evt asegs (leafw_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 272, bv_unsigned sp)] lo m
(fun a0' m' => a0' = wz (-1) /\ RTconst RE X m'))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz get_named_mapping_fd_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros RT RL MI ST CEIL LO. pose proof CEIL as CEIL'. idtac.
rtc RT 19%nat K19. rtc RT 33%nat K33. unfold get_named_mapping_fd_entry.
pose proof (munch_refl [(bv_unsigned sp - 272, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
carve_frame 272%nat ST.
do 8 stf.
step. step.
step.
if_cases Hnm.

2: step; step; stp; stp; stp; step; if_lit.
1-2: do 10 stf;
release_frame FR ST (bv_unsigned sp);
apply evt_done; unfold leafw_post; do 16 eexists; (split; [reflexivity|]);
(split; [exact MU|]); (split; [exact WM|]); (split; [assumption|]); (split; [exact ST|]); (split; [reflexivity|]);
(eapply RTconst_stack; [exact RT| exact RL| exact MU| exact WM|]; constructor; [cbn [fst]; lia| constructor]).
Qed.

Lemma mmap_fixed_impl_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (A N lo : Z),
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - MMAPFIXED_IMPL_STACK ->
A mod 4096 = 0 -> N mod 4096 = 0 -> 0 < N -> KHI <= A -> A + N <= band_lo ->
rt_avoid RE X (A, A + N) ->
impl asegs atn (enode (NMmap A N PROT_RW FL_FIXED) (dec_fixedA A N))
(epost (map_fixed_post_k MMAPFIXED_IMPL_STACK ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A N lo m))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A) (wz N) (wz 1) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz mmap_fixed_impl_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros RT RL MI ST CEIL LO AAL NAL N0 AK AC AV.
pose proof CEIL as CEIL'. idtac. rewrite ?KHI_eq in AK. unfold MMAPFIXED_IMPL_STACK in *.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 368, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
rtc RT 18%nat K18. rtc RT 8%nat K8. rtc RT 19%nat K19. rtc RT 33%nat K33. unfold mmap_fixed_impl_entry.
apply impl_enode.
carve_frame 96%nat ST.
do 10 step.
step. step. step. step.
clear K18 K8 K19 K33.
step. if_lit.
step. step. step. if_lit.
stp. stp. stp. stp.
rewrite (unsigned_lit (N + 4095)) by lia. rewrite land_pagemask by lia.
replace (N + 4095 - (N + 4095) mod 4096) with N by (Z.div_mod_to_equations; lia).
step. if_lit.
stp.
rewrite (unsigned_lit A) by lia. rewrite ?land_pagemask, ?land_pagemask_l by lia.
replace (A - A mod 4096) with A by lia.
step. step. step. step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (RT1 : RTconst RE X mm) end.
{ eapply RTconst_stack; [exact RT| exact RL| exact MU| exact WM|]. constructor; [cbn [fst]; lia| constructor]. }
call_sp (get_named_mapping_fd_spec _ _); try eassumption; [lia|]. subst x2. clear RT1. rename POST into RT1.
rename x14 into m1 || idtac. rename PC into ST.
stp.
step. step. step. step. step.
step. step.
step_ecall.
split. { cbn [at_nodeA]. at_node_solve. }
intros rsp ans Hdec. destruct ans as [|xg].
-
exfalso. exact (dec_fixedA_noerr _ _ _ Hdec).
-
apply dec_fixedA_ok_inv in Hdec as [-> ->].
rewrite (mmap_len_aligned N) by exact NAL.
apply (munch_weaken _ [(bv_unsigned sp - 368, bv_unsigned sp); (A, A + N)]) in MU.
2:{ unfold sub_fp; cbn [outside]; intros; tauto. }
assert (ROF : forall x : word, A <= bv_unsigned x < A + N -> ro_addr asegs x = false) by (intros xw Hxw; apply a_ro_addr_false; lia).
sys_nret. clear ROF RT1.
step.
step. step. step.
stp. stp. step.
unfold_cond. rewrite (unsigned_lit A) by lia. if_lit.
step. rewrite v_sltu_b2z. rewrite (unsigned_lit A) by lia. fold_closed_in_goal.
replace (18446744073709547520 <? A) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
step.
step. step. stf. step.
step. step.
stp. stp. step.
unfold_cond. rewrite (unsigned_lit A) by lia. if_lit.
step. rewrite v_sltu_b2z. rewrite (unsigned_lit A) by lia. fold_closed_in_goal.
replace (18446744073709547520 <? A) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
step.
step. if_lit.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (RT2 : RTconst RE X mm) end.
{ eapply RTconst_munch; [exact RT| exact MU| exact WM|].
constructor; [apply rt_avoid_stack; [exact RL| lia]| constructor; [exact AV| constructor]]. }
step. call0 (increase_total_mmap_spec RE X); [exact RT2| assumption|].
step. do 6 step. step. step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold map_fixed_post_k. cbn [fixed_fp]. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split.
+ eapply RTconst_munch; [exact RT| exact MU| exact WM|].
constructor; [apply rt_avoid_stack; [exact RL| lia]| constructor; [exact AV| constructor]].
+ split; [reflexivity|]. split; [reflexivity|]. exact ZNEW.
Qed.
End S.

Section S2.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).

Lemma impl_suffix : forall {node : Type} segs (atn : node -> machine_state -> Prop) {R} (t : itree node R) (Q1 Q : R -> machine_state -> Prop) ms,
impl segs atn t Q1 ms -> (forall r ms', Q1 r ms' -> evt segs (Q r) ms') -> impl segs atn t Q ms.
Proof.
intros node segs atn R t. induction t as [r|n k IH]; intros Q1 Q ms H HQ; cbn in *.
- eapply evt_cut; [exact H|]. intros ms' H1. exact (HQ _ _ H1).
- eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; eauto.
Qed.

Lemma map_with_callback_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (A N lo : Z),
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - MMAPFIXED_STACK ->
A mod 4096 = 0 -> N mod 4096 = 0 -> 0 < N -> KHI <= A -> A + N <= band_lo ->
rt_avoid RE X (A, A + N) ->
impl asegs (at_nodeA L asegs) (enode (NMmap A N PROT_RW FL_FIXED) (dec_fixedA A N))
(epost (map_fixed_post RE X ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A N lo m))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz A) (wz N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz map_with_callback_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros RT RL MI ST CEIL LO AAL NAL N0 AK AC AV. unfold map_with_callback_entry, MMAPFIXED_STACK in *.
pose proof CEIL as CEIL'. rewrite ?KHI_eq in AK.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 400, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
iprefix.
carve_frame 32%nat ST.
do 5 stf.
step. step. step. step. step.
step.
step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (RT1 : RTconst RE X mm) end.
{ eapply RTconst_stack; [exact RT| exact RL| exact MU| exact WM|]. constructor; [cbn [fst]; lia| constructor]. }
ihere.
eapply impl_suffix.
{ eapply (mmap_fixed_impl_spec); try eassumption.
- rewrite unsigned_lit by lia. exact ST.
- rewrite unsigned_lit by lia. unfold MMAPFIXED_IMPL_STACK. lia. }
intros [|ans] ms' POST; cbn [epost] in POST |- *; [apply evt_done; exact I|].
destruct POST as (u0 & u1 & u2 & r0 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & u3 & u4 & u5 & u6 & mc1 & -> & MU2 & WM2 & MI2 & ST2 & RT2 & ANS).
destruct ans as [|xg]; [contradiction|]. destruct ANS as (-> & -> & ZNEW). cbn [fixed_fp] in MU2.
rewrite !(unsigned_lit (bv_unsigned sp + -32)) in * by lia. unfold MMAPFIXED_IMPL_STACK in MU2.
lazymatch goal with |- context [ret_pc (wz ?n)] => replace (ret_pc (wz n)) with (wz n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
apply (munch_weaken _ [(bv_unsigned sp - 400, bv_unsigned sp); (A, A + N)]) in MU.
2:{ unfold sub_fp; cbn [outside]; intros; tauto. }
pose proof (wmono_trans _ _ _ _ WM WM2) as WM'.
hide MU. transport_after_call asegs m1 mc1 MU2 WM2. unhide MU.
assert (MU' : munch [(bv_unsigned sp - 400, bv_unsigned sp); (A, A + N)] m mc1) by (eapply munch_chain; [exact MU| exact MU2| sub_fp_solve]).
clear MU MU2 WM2 WM MI; rename MU' into MU.
step. unfold_cond. rewrite (unsigned_lit A) by lia. if_lit.
do 4 step. step. step.
release_frame FR ST2 (bv_unsigned sp).
apply evt_done. unfold map_fixed_post, map_fixed_post_k. cbn [fixed_fp]. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM'|]. split; [assumption|]. split; [exact ST2|]. split; [exact RT2|].
split; [reflexivity|]. split; [reflexivity|]. exact ZNEW.
Qed.
End S2.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QDM6 QwAs.Mq2.
Import Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq1 QTVW.Mq3.
Import QlES. Local Ltac QsGW.small_offset k ::= QsGW.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition poison_shadow_entry : Z := 0x64824.

Lemma land_7 : forall a, 0 <= a -> Z.land a 7 = a mod 8.
Proof. intros a Ha. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Section S.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Definition poison_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(addr size v lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (SH addr, SH addr + size / 8)] m m'
/\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ RTconst RE X m'
/\ rw_cells asegs m' (SH addr) [CB (Z.to_nat (size / 8)) (repeat (b8 v) (Z.to_nat (size / 8)))].

Lemma poison_shadow_spec_gen : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (addr size v lo : Z) (junk : list byte),
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 64 ->
addr mod 8 = 0 -> size mod 8 = 0 -> 0 <= size -> KHI <= addr < 2^47 -> KHI + 8 <= addr + size <= 2^47 ->
0 <= v < 256 -> (v <> 0 \/ size / 8 < 0xffffffffffffffff) ->
rw_cells asegs m (SH addr) [CB (Z.to_nat (size / 8)) junk] ->
evt asegs (poison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr size v lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz addr) (wz size) (wz v) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz poison_shadow_entry) fc None m (seg_rom asegs)).
Proof.
intros until junk; intros RT RL MI ST CEIL LO AAL SAL S0 AK AH VR VC SHD.
pose proof CEIL as CEIL'. idtac. rewrite ?KHI_eq in AK, AH. change (2^47) with 140737488355328 in AK, AH.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
assert (SHa : SH addr = addr / 8 + 0x7fff8000) by reflexivity.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (SH addr, SH addr + size / 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
rtc RT 2%nat K2. rtc RT 19%nat K19. rtc RT 1%nat K1. rtc RT 5%nat K5. rtc RT 23%nat K23. rtc RT 16%nat K16.
unfold poison_shadow_entry.
carve_frame 64%nat ST.
do 8 step.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms1 => exists a3' : word, ms1 = MS (@bvmap_set 5 word 13 a3' R) FF (wz 0x64858) fcc rv mm ro))
end.
{ step. if_cases Hv.
- apply evt_done. eexists. simp_regs. reflexivity.
- step. stp. step. step. if_lit. apply evt_done. eexists. simp_regs. reflexivity. }
intros ms1 [a3' ->]. simp_regs.
stp. rewrite ?(unsigned_lit addr) by lia. rewrite (land_7 addr) by lia. replace (addr mod 8) with 0 by lia.
step. if_lit.
step. stp. stp.
step. stp. stp. stp.
step. ifz.
step. step. step. step. step. step.
stp. step. ifz.
step. step. step. stp. stp.
step. ifz.
step. ifz.
step. stp. stp. step. ifz. step. ifz.

stp. rewrite ?(unsigned_lit size) by lia. rewrite (land_7 size) by lia. replace (size mod 8) with 0 by lia.
step. if_lit.
step. step.
step. ifz.
step. step. step. step. step. step. stp. step. ifz.
step. step. step. stp. stp.
step. ifz. step. ifz.

step. stp. stp. step. if_lit.
step. step. step. step. step.
rewrite !(unsigned_lit addr), !(unsigned_lit (addr + size + -8)) by lia.
rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite !(unsigned_lit (addr / 8)) by lia.
replace ((addr + size + -8) / 8 + 1 + - (addr / 8)) with (size / 8) by (Z.div_mod_to_equations; lia).
replace (2147450880 + addr / 8) with (SH addr) by lia.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms2 => exists a1' : word, ms2 = MS (@bvmap_set 5 word 11 a1' R) FF (wz 0x64b8c) fcc rv mm ro))
end.
{ step. if_cases Hv.
-  apply evt_done. eexists. simp_regs. reflexivity.
-
zify_cond Hv. rewrite ?(unsigned_lit v) in Hv by lia.
step. stp. stp. step. ifz. apply evt_done. eexists. simp_regs. reflexivity. }
intros ms2 [a1' ->]. simp_regs.
step. step.
step. do 7 step. step.
release_frame FR ST (bv_unsigned sp).
step.
assert (SHR : 0 <= SH addr /\ SH addr + size / 8 < 2^64) by (rewrite SHa; Z.div_mod_to_equations; lia).
eapply evt_cut.
{ eapply memset_spec; [| eassumption]. rewrite !unsigned_lit by lia. exact SHD. }
intros ms' POST. unfold memset_post in POST. rewrite !unsigned_lit in POST by lia.
destruct POST as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m' & -> & MU2 & WM2 & MI2 & SHD2).
replace (v mod 256) with v in SHD2 by (symmetry; apply Z.mod_small; lia).
apply evt_done. unfold poison_post. do 16 eexists. split; [reflexivity|].
split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; (first [ clear - H x SHR SPR VC VR AH AK v size addr sp; tauto | tauto ]). }
split. { eapply wmono_trans; [exact WM| exact WM2]. }
split. { exact MI2. }
assert (SHhi : SH addr + size / 8 <= KHI) by (rewrite SHa, ?KHI_eq; Z.div_mod_to_equations; lia).
split. { eapply stk_transport_disjoint; [exact ST| exact MU2| exact WM2|]. cbn [disjoint_from]. rewrite ?KHI_eq in SHhi. split; [lia| exact I]. }
split.
{ eapply RTconst_munch; [exact RT| | |].
- eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; (first [ clear - H x SHR SPR VC VR AH AK v size addr sp; tauto | tauto ]).
- eapply wmono_trans; [exact WM| exact WM2].
- constructor; [apply rt_avoid_stack; [exact RL| lia]|].
constructor; [| constructor]. apply rt_avoid_gap; [exact RL| rewrite SHa; unfold kLowEnd; lia| exact SHhi]. }
exact SHD2.
Qed.

Lemma poison_shadow_spec_gen_low : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (addr size v lo : Z) (junk : list byte),
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 64 ->
addr mod 8 = 0 -> size mod 8 = 0 -> 0 <= size -> 0 <= addr < 0x7fff8000 -> 8 <= addr + size <= 0x7fff8000 ->
0 <= v < 256 -> (v <> 0 \/ size / 8 < 0xffffffffffffffff) ->
rw_cells asegs m (SH addr) [CB (Z.to_nat (size / 8)) junk] ->
evt asegs (poison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr size v lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz addr) (wz size) (wz v) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz poison_shadow_entry) fc None m (seg_rom asegs)).
Proof.
intros until junk; intros RT RL MI ST CEIL LO AAL SAL S0 AK AH VR VC SHD.
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
assert (SHa : SH addr = addr / 8 + 0x7fff8000) by reflexivity.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (SH addr, SH addr + size / 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
rtc RT 2%nat K2. rtc RT 19%nat K19. rtc RT 1%nat K1. rtc RT 5%nat K5. rtc RT 23%nat K23. rtc RT 16%nat K16.
unfold poison_shadow_entry.
carve_frame 64%nat ST.
do 8 step.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms1 => exists a3' : word, ms1 = MS (@bvmap_set 5 word 13 a3' R) FF (wz 0x64858) fcc rv mm ro))
end.
{ step. if_cases Hv.
- apply evt_done. eexists. simp_regs. reflexivity.
- step. stp. step. step. if_lit. apply evt_done. eexists. simp_regs. reflexivity. }
intros ms1 [a3' ->]. simp_regs.
stp. rewrite ?(unsigned_lit addr) by lia. rewrite (land_7 addr) by lia. replace (addr mod 8) with 0 by lia.
step. if_lit.
step. stp. stp.
step. stp. stp. stp.
step. ifz.
stp. rewrite ?(unsigned_lit size) by lia. rewrite (land_7 size) by lia. replace (size mod 8) with 0 by lia.
step. if_lit.
step. step.
step. ifz.

step. stp. stp. step. if_lit.
step. step. step. step. step.
rewrite !(unsigned_lit addr), !(unsigned_lit (addr + size + -8)) by lia.
rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite !(unsigned_lit (addr / 8)) by lia.
replace ((addr + size + -8) / 8 + 1 + - (addr / 8)) with (size / 8) by (Z.div_mod_to_equations; lia).
replace (2147450880 + addr / 8) with (SH addr) by lia.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms2 => exists a1' : word, ms2 = MS (@bvmap_set 5 word 11 a1' R) FF (wz 0x64b8c) fcc rv mm ro))
end.
{ step. if_cases Hv.
-  apply evt_done. eexists. simp_regs. reflexivity.
-
zify_cond Hv. rewrite ?(unsigned_lit v) in Hv by lia.
step. stp. stp. step. ifz. apply evt_done. eexists. simp_regs. reflexivity. }
intros ms2 [a1' ->]. simp_regs.
step. step.
step. do 7 step. step.
release_frame FR ST (bv_unsigned sp).
step.
assert (SHR : 0 <= SH addr /\ SH addr + size / 8 < 2^64) by (rewrite SHa; Z.div_mod_to_equations; lia).
eapply evt_cut.
{ eapply memset_spec; [| eassumption]. rewrite !unsigned_lit by lia. exact SHD. }
intros ms' POST. unfold memset_post in POST. rewrite !unsigned_lit in POST by lia.
destruct POST as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m' & -> & MU2 & WM2 & MI2 & SHD2).
replace (v mod 256) with v in SHD2 by (symmetry; apply Z.mod_small; lia).
apply evt_done. unfold poison_post. do 16 eexists. split; [reflexivity|].
split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; (first [ clear - H x SHR SPR VC VR AH AK v size addr sp; tauto | tauto ]). }
split. { eapply wmono_trans; [exact WM| exact WM2]. }
split. { exact MI2. }
assert (SHhi : SH addr + size / 8 <= KHI) by (rewrite SHa, ?KHI_eq; Z.div_mod_to_equations; lia).
split. { eapply stk_transport_disjoint; [exact ST| exact MU2| exact WM2|]. cbn [disjoint_from]. rewrite ?KHI_eq in SHhi. split; [lia| exact I]. }
split.
{ eapply RTconst_munch; [exact RT| | |].
- eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; (first [ clear - H x SHR SPR VC VR AH AK v size addr sp; tauto | tauto ]).
- eapply wmono_trans; [exact WM| exact WM2].
- constructor; [apply rt_avoid_stack; [exact RL| lia]|].
constructor; [| constructor]. apply rt_avoid_gap; [exact RL| rewrite SHa; unfold kLowEnd; lia| exact SHhi]. }
exact SHD2.
Qed.

Lemma poison_shadow_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (addr size v lo : Z) (junk : list byte),
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 64 ->
addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> KHI <= addr -> addr + size <= 2^47 ->
0 <= v < 256 -> (v <> 0 \/ size / 8 < 0xffffffffffffffff) ->
rw_cells asegs m (SH addr) [CB (Z.to_nat (size / 8)) junk] ->
evt asegs (poison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr size v lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz addr) (wz size) (wz v) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz poison_shadow_entry) fc None m (seg_rom asegs)).
Proof.
intros until junk; intros RT RL MI ST CEIL LO AAL SAL S0 AK AH VR VC SHD.
eapply poison_shadow_spec_gen; try eassumption; [lia| lia|]. clear - SAL S0 AK AH. Z.div_mod_to_equations. lia.
Qed.

Lemma poison_shadow_spec_lh : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (addr size v lo : Z) (junk : list byte),
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 64 ->
addr mod 8 = 0 -> size mod 8 = 0 -> 0 <= size ->
((KHI <= addr < 2^47 /\ KHI + 8 <= addr + size <= 2^47) \/ (0 <= addr < 0x7fff8000 /\ 8 <= addr + size <= 0x7fff8000)) ->
0 <= v < 256 -> (v <> 0 \/ size / 8 < 0xffffffffffffffff) ->
rw_cells asegs m (SH addr) [CB (Z.to_nat (size / 8)) junk] ->
evt asegs (poison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr size v lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz addr) (wz size) (wz v) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz poison_shadow_entry) fc None m (seg_rom asegs)).
Proof.
intros until junk; intros RT RL MI ST CEIL LO AAL SAL S0 [[AK AH]|[AK AH]] VR VC SHD.
- eapply poison_shadow_spec_gen; eassumption.
- eapply poison_shadow_spec_gen_low; eassumption.
Qed.
End S.
End Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmP7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QDw3 QUxU QNwL QYnC QSsj QNQk.Mq1 QmP7.Mq0 QTVW.Mq0.
Import QlES. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.

Local Notation wz := (Z_to_bv 64).

Definition QPOP_STACK : Z := 672.

Section S.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Definition gstep (a a1 : AState) (G G1 : ghost) : Prop :=
same_tags tag_quar G G1 /\ same_tags is_live G G1
/\ (forall c i t, tag_at G c i = Some t -> exists t', tag_at G1 c i = Some t')
/\ (forall LB FS, gcons a LB FS G RE X -> gcons a1 LB FS G1 RE X).

Definition qpop_W (sp : Z) (a : AState) : list (Z * Z) :=
[ (sp - QPOP_STACK, sp); (rl_T X + 208, rl_T X + 3168); (ri_addr RE 24, ri_addr RE 24 + 128);
(fa_beg (ae_L RE) 24, fa_beg (ae_L RE) 24 + kFreeArraySize);
(SH (fa_beg (ae_L RE) 24), SH (fa_beg (ae_L RE) 24) + kFreeArraySize / 8);
(reg_beg (ae_L RE) 24 + c_alloc_user (cls a 24), reg_beg (ae_L RE) 24 + kFreeArrayOffset);
(SH (reg_beg (ae_L RE) 24 + c_alloc_user (cls a 24)), SH (reg_beg (ae_L RE) 24 + kFreeArrayOffset)) ].

Definition qpop_ghost (a a1 : AState) (G G1 : ghost) : Prop := gstep a a1 G G1.

Definition qpop_post (ra sp gp a0 a2 a3 a4 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PStateA) (a : AState) (G : ghost) (lo : Z) (m : word -> option byte)
(r : bool * AState) (s' : PStateA) (ms' : machine_state) : Prop :=
exists (ra' t0 t1 t2 s0 s1 a0' a1 a3' a4' a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 : word) m' G1,
ms' = MS (mkR ra' sp gp (wz A_TP) t0 t1 t2 s0 s1 a0' a1 a2 a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz (if fst r then 0x43744 else 0x43830)) fc None m' (seg_rom asegs)
/\ s' = s
/\ munch (qpop_W (bv_unsigned sp) a) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ RTconst RE X m' /\ RStats RE X m' /\ qpop_ghost a (snd r) G G1
/\ if fst r then
a0' = a0 /\ a3' = a3 /\ a4' = a4 /\
exists i, tag_at G1 24 i = Some TCached /\ a1 = wz (slot_beg RE 24 i)
/\ (forall t, tag_prim t = false -> RPrim (snd r) (set_tag 24 i t G1) RE X m')
/\ hjunk m' (slot_beg RE 24 i) (slot_beg RE 24 i + 8192)
/\ rw_cells asegs m' (SH (slot_beg RE 24 i)) [CB 1024%nat (fas 1024)]
else RPrim (snd r) G1 RE X m'.

Definition qpop24_stmt (L : lvp) : Prop :=
forall (ra sp gp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (s : PStateA) (a : AState) (G : ghost) (lo : Z),
RTconst RE X m -> rlay_ok RE X -> RStats RE X m -> RPrim a G RE X m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - QPOP_STACK ->
aimplT (at_nodeA L asegs) (cache_alloc (ae_L RE) a kBatchClass) s
(qpop_post ra sp gp a0 a2 a3 a4 s6 s7 s8 s9 s10 s11 F fc s a G lo m)
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 a0 (wz (rl_T X + 208)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x436f4) fc None m (seg_rom asegs)).
End S.

Lemma gstep_refl {BAND : Band} : forall RE X a G, gstep RE X a a G G.
Proof. intros. split; [apply same_tags_refl|]. split; [apply same_tags_refl|]. split; [intros c i t H; exists t; exact H| auto]. Qed.

Lemma gstep_trans {BAND : Band} : forall RE X a a1 a2 G G1 G2, gstep RE X a a1 G G1 -> gstep RE X a1 a2 G1 G2 -> gstep RE X a a2 G G2.
Proof.
intros RE X a a1 a2 G G1 G2 (Q1 & L1 & T1 & C1) (Q2 & L2 & T2 & C2).
split; [intros c i t Ht; rewrite (Q1 c i t Ht); apply Q2; exact Ht|].
split; [intros c i t Ht; rewrite (L1 c i t Ht); apply L2; exact Ht|].
split; [| intros LB FS H; apply C2, C1, H].
intros c i t Ht. destruct (T1 c i t Ht) as [t' Ht']. exact (T2 c i t' Ht').
Qed.

Lemma gstep_state {BAND : Band} : forall RE X a a1 G, (forall LB FS, gcons a LB FS G RE X -> gcons a1 LB FS G RE X) -> gstep RE X a a1 G G.
Proof. intros. split; [apply same_tags_refl|]. split; [apply same_tags_refl|]. split; [intros c i t Ht; exists t; exact Ht| assumption]. Qed.
End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig.
Import Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj QNQk.Mq2 QTVW.Mq3.
Import QlES. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).

Definition set_shadow_00_entry : Z := 0x654f0.
Definition set_shadow_f8_entry : Z := 0x65610.
Definition real_memset_entry : Z := 0xdb750.

Section Walk.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Lemma set_shadow_00_stub : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m P,
RTconst RE X m -> rlay_ok RE X ->
evt asegs P (MS (mkR ra sp gp tp t0 (wz real_memset_entry) t2 s0 s1 a0 (wz 0) a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz real_memset_entry) fc None m (seg_rom asegs)) ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz set_shadow_00_entry) fc None m (seg_rom asegs)).
Proof.
intros until P; intros RT RL K. unfold set_shadow_00_entry, real_memset_entry in *.
rt_now RT RL 19%nat K19. rt_now RT RL 23%nat K23.
istep. istep. istep. istep. istep. istep. exact K.
Qed.

Lemma set_shadow_f8_stub : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m P,
RTconst RE X m -> rlay_ok RE X ->
evt asegs P (MS (mkR ra sp gp tp t0 (wz real_memset_entry) t2 s0 s1 a0 (wz 248) a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz real_memset_entry) fc None m (seg_rom asegs)) ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz set_shadow_f8_entry) fc None m (seg_rom asegs)).
Proof.
intros until P; intros RT RL K. unfold set_shadow_f8_entry, real_memset_entry in *.
rt_now RT RL 19%nat K19. rt_now RT RL 23%nat K23.
istep. istep. istep. istep. istep. istep. exact K.
Qed.

End Walk.

Lemma stk_after_memset : forall m m' lo hi dst n bs,
stk asegs m lo hi -> munch [(dst, dst + n)] m m' -> wmono asegs m m' ->
rw_cells asegs m' dst [CB (Z.to_nat n) bs] -> 0 <= n ->
stk asegs m' lo hi.
Proof.
intros m m' lo hi dst n bs (S1 & S2 & S3) MU WM RC Hn. split; [exact S1|]. split; [exact S2|].
intros a Ha. destruct (S3 a Ha) as [Wv (b & Hb)]. split; [apply WM; exact Wv|].
destruct RC as [[[WF _] (B1 & B2 & B3)] _]. cbn [cell_wf] in WF. cbn [cells_bytes cbytes] in B2, B3.
rewrite app_nil_r in B2, B3. rewrite WF in B2, B3.
destruct (Z_lt_le_dec a dst) as [L|GE]; [| destruct (Z_lt_le_dec a (dst + n)) as [L2|GE2]].
- exists b. unfold mrd in *. rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. cbn. lia.
- specialize (B3 (Z.to_nat (a - dst)) ltac:(lia)).
replace (dst + Z.of_nat (Z.to_nat (a - dst))) with a in B3 by lia.
destruct (nth_error bs (Z.to_nat (a - dst))) as [b'|] eqn:E.
+ exists b'. exact B3.
+ exfalso. apply nth_error_None in E. lia.
- exists b. unfold mrd in *. rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. cbn. lia.
Qed.

Section Lift.
Context {BAND : Band}.
Variable C : arun_components.
Hypothesis HRT : forall RE X m, ac_RTconst C RE X m <-> RTconst RE X m.

Lemma set_shadow_A : forall entry v,
(entry = set_shadow_00_entry /\ v = 0) \/ (entry = set_shadow_f8_entry /\ v = 0xf8) ->
aset_shadowA_stmt asegs a_alayout (ARUN C) entry v.
Proof.
intros entry v EV. unfold aset_shadowA_stmt. intros until lo; intros old s LB FS RE AR ST CEIL LO MI Ha0 Ha1 HN RC.
destruct (ARUN_open C _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
pose proof (proj1 AX) as GC. pose proof (proj1 GC) as RL.
pose proof (proj1 (HRT _ _ _) (proj1 (proj2 AX))) as RT.
pose proof (rw_cells_bound _ _ _ _ RC) as B. cbn [cells_size csize Nat.add] in B.
subst a0 a1.
assert (POST : evt asegs (memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (wz dst) (wz v) (wz n) m)
(MS (mkR ra sp gp tp t0 (wz real_memset_entry) t2 s0 s1 (wz dst) (wz v) (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz real_memset_entry) fc None m (seg_rom asegs))).
{ apply (memset_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ old); [| exact MI].
rewrite !unsigned_lit by lia. exact RC. }
eapply evt_mono.
- destruct EV as [[-> ->]|[-> ->]].
+ eapply (set_shadow_00_stub RE X); [exact RT| exact RL| exact POST].
+ eapply (set_shadow_f8_stub RE X); [exact RT| exact RL| exact POST].
- cbv beta. intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & RC').
assert (Hv : 0 <= v < 256) by (destruct EV as [[_ ->]|[_ ->]]; lia).
rewrite !unsigned_lit in MU by lia. rewrite !unsigned_lit in RC' by lia. rewrite (Z.mod_small v 256) in RC' by lia.
do 15 eexists. split; [reflexivity|].
split. { eapply munch_weaken; [| exact MU]. intros y Hy. cbn [outside fst snd] in Hy |- *. tauto. }
split; [exact WM|]. split; [exact MI'|].
split; [eapply stk_after_memset; [exact ST| exact MU| exact WM| exact RC'| lia]|].
exact RC'.
Qed.

Lemma set_shadow_00_A : aset_shadowA_stmt asegs a_alayout (ARUN C) (ala_set_shadow_00 a_alayout) 0.
Proof. apply set_shadow_A. left. split; reflexivity. Qed.

Lemma set_shadow_f8_A : aset_shadowA_stmt asegs a_alayout (ARUN C) (ala_set_shadow_f8 a_alayout) 0xf8.
Proof. apply set_shadow_A. right. split; reflexivity. Qed.

End Lift.
End Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg Q61C QWRO Qu4g QFQR QKBN QsJM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW Q61C QWRO Qu4g QFQR QmP7 QKBN QsJM.
Import QlES. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.

Section S.
Context {BAND : Band}.
Variable C : arun_components.
Hypothesis HRT : ac_RTconst C = RTconst.
Hypothesis HRF : ac_RFake C = RFake.

Lemma ARUN_uar_on : forall s LB FS RE m, ARUN C s LB FS RE m ->
ro_cells asegs m 0x0e8210 [C8 (Z_to_bv 64 0x0f21c0)] /\ ro_cells asegs m 0x0f21c0 [C4 (Z_to_bv 64 1)].
Proof.
intros s LB FS RE m AR. destruct (ARUN_open C _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
destruct AX as (GC & R1 & _). rewrite HRT in R1.
pose proof (RT_img _ _ _ R1 20%nat _ _ eq_refl) as K20. cbn [fst snd] in K20.
pose proof (RT_img _ _ _ R1 6%nat _ _ eq_refl) as K6. cbn [fst snd] in K6.
split; [| exact K6].
apply (proj1 (ro_cells_app asegs m _ [C8 (Z_to_bv 64 0x0ea218); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0x183cdc); C8 (Z_to_bv 64 0x181c58)] _)) in K20 as [_ K].
exact K.
Qed.

Lemma ARUN_fframes_nodup : forall s LB FS RE m, ARUN C s LB FS RE m -> List.NoDup (map ff_addr FS).
Proof.
intros s LB FS RE m AR. destruct (ARUN_open C _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
destruct AX as (GC & _ & _ & _ & _ & _ & _ & _ & R8). rewrite HRF in R8.
eapply Permutation_NoDup; [apply Permutation_map; apply Permutation_sym; exact PF|]. exact (RFake_nodup RE X FS0 m R8).
Qed.

End S.
End Mq7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbcP_c1 QN4c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c QNQk.Mq6.
Import QlES.
Import ListNotations. Local Ltac QbcP_c1.small_offset k ::= QbcP_c1.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Unset Keyed Unification.

Definition MUTEX_HELD : Z := 1152921504606846976.

Lemma max_count_facts : forall c, 1 <= c <= 31 -> 2 <= max_count c <= 16 /\ max_count c mod 2 = 0.
Proof.
intros c Hc.
assert (H : forallb (fun c => (2 <=? max_count c) && (max_count c <=? 16) && (max_count c mod 2 =? 0))
(map Z.of_nat (seq 1 31)) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in H. specialize (H c).
assert (Hin : In c (map Z.of_nat (seq 1 31))) by (apply in_map_iff; exists (Z.to_nat c); split; [lia| apply in_seq; lia]).
specialize (H Hin). apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.eqb_eq in H3. lia.
Qed.

Lemma le4_sx32' (v : word) : le4 (sx32 v) = le4 v.
Proof.
transitivity (le4 (Z_to_bv 64 (bv_unsigned v))); [| rewrite Z_to_bv_bv_unsigned; reflexivity].
unfold sx32. apply le4_eqm.
unfold bv_swrap. pose proof (bv_unsigned_in_range 64 v) as R.
set (u := bv_unsigned v) in *. clearbody u. unfold bv_wrap.
change (bv_modulus 32) with (2^32)%Z. change (bv_half_modulus 32) with (2^31)%Z.
Z.div_mod_to_equations. lia.
Qed.
End Mq8.

Module Mq9.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QKTr.
Import QJBH.
Import QZzg QTVW Q61C QWRO QFQR QmP7 QKBN QNQk.Mq6.
Import QlES. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).
Local Notation mem := (word -> option byte) (only parsing).

Definition map_or_die_entry : Z := 0x7fbe4.
Definition MAPORDIE_STACK : Z := 704.

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).

Definition map_or_die_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(A N lo : Z) (m : mem) (ans : ansA) : machine_state -> Prop :=
fun ms' =>
match ans with
| AErr => True
| AOk x => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - MAPORDIE_STACK, bv_unsigned sp); (A, A + N)] m m'
/\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ RTconst RE X m'
/\ x = A /\ a0 = wz A /\ rw_cells asegs m' A [CB (Z.to_nat N) (repeat (b8 0) (Z.to_nat N))]
end.

Definition map_or_die_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (A N lo : Z),
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - MAPORDIE_STACK ->
A mod 4096 = 0 -> N mod 4096 = 0 -> 0 < N -> 0x647000 <= A -> A + N <= band_lo ->
rt_avoid RE X (A, A + N) ->
impl asegs (at_nodeA L asegs) (enode (NMmap A N PROT_RW FL_FIXED) (dec_fixedA A N))
(epost (map_or_die_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A N lo m))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz A) (wz N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz map_or_die_entry) fc None m (seg_rom asegs)).
End S.
End Mq9.

Module Mqa.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5.
Import Q6sh QKTr.
Import QJBH.
Import QZzg QTVW QbcP_c1 QWRO QFQR QmP7 QKBN QN4c QNQk.Mq6 QNQk.Mq8.
Import QlES.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QbcP_c1.small_offset k ::= QbcP_c1.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition map_with_callback_entry : Z := 0x7fa98.
Definition mmap_fixed_impl_entry : Z := 0x77860.
Definition MMAPFIXED_IMPL_STACK : Z := 368.
Definition MMAPFIXED_STACK : Z := 400.

Definition fixed_fp (A N : Z) (ans : ansA) : list (Z * Z) :=
match ans with AErr => [] | AOk _ => [(A, A + N)] end.

Lemma mmap_len_aligned : forall len, len mod 4096 = 0 -> mmap_len len = len.
Proof. intros. unfold mmap_len, page_round_up_Z, page_size. Z.div_mod_to_equations. lia. Qed.

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Local Notation atn := (at_nodeA L asegs).

Definition map_fixed_post_k (K : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(A N lo : Z) (m : word -> option byte) (ans : ansA) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch ((bv_unsigned sp - K, bv_unsigned sp) :: fixed_fp A N ans) m m'
/\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ RTconst RE X m'
/\ match ans with
| AErr => False
| AOk x => x = A /\ a0 = wz A /\ rw_cells asegs m' A [CB (Z.to_nat N) (repeat (b8 0) (Z.to_nat N))]
end.
Definition map_fixed_post := map_fixed_post_k MMAPFIXED_STACK.

Definition get_named_mapping_fd_entry : Z := 0x77ef4.

Lemma get_named_mapping_fd_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m lo,
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 272 ->
evt asegs (leafw_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 272, bv_unsigned sp)] lo m
(fun a0' m' => a0' = wz (-1) /\ RTconst RE X m'))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz get_named_mapping_fd_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros RT RL MI ST CEIL LO. pose proof CEIL as CEIL'. idtac.
rtc RT 19%nat K19. rtc RT 33%nat K33. unfold get_named_mapping_fd_entry.
pose proof (munch_refl [(bv_unsigned sp - 272, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
carve_frame 272%nat ST.
do 8 stf.
step. step.
step.
if_cases Hnm.

2: step; step; stp; stp; stp; step; if_lit.
1-2: do 10 stf;
release_frame FR ST (bv_unsigned sp);
apply evt_done; unfold leafw_post; do 16 eexists; (split; [reflexivity|]);
(split; [exact MU|]); (split; [exact WM|]); (split; [assumption|]); (split; [exact ST|]); (split; [reflexivity|]);
(eapply RTconst_stack; [exact RT| exact RL| exact MU| exact WM|]; constructor; [cbn [fst]; lia| constructor]).
Qed.

Lemma mmap_fixed_impl_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (A N lo : Z),
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - MMAPFIXED_IMPL_STACK ->
A mod 4096 = 0 -> N mod 4096 = 0 -> 0 < N -> KHI <= A -> A + N <= band_lo ->
rt_avoid RE X (A, A + N) ->
impl asegs atn (enode (NMmap A N PROT_RW FL_FIXED) (dec_fixedA A N))
(epost (map_fixed_post_k MMAPFIXED_IMPL_STACK ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A N lo m))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A) (wz N) (wz 1) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz mmap_fixed_impl_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros RT RL MI ST CEIL LO AAL NAL N0 AK AC AV.
pose proof CEIL as CEIL'. idtac. rewrite ?KHI_eq in AK. unfold MMAPFIXED_IMPL_STACK in *.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 368, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
rtc RT 18%nat K18. rtc RT 8%nat K8. rtc RT 19%nat K19. rtc RT 33%nat K33. unfold mmap_fixed_impl_entry.
apply impl_enode.
carve_frame 96%nat ST.
do 10 step.
step. step. step. step.
clear K18 K8 K19 K33.
step. if_lit.
step. step. step. if_lit.
stp. stp. stp. stp.
rewrite (unsigned_lit (N + 4095)) by lia. rewrite land_pagemask by lia.
replace (N + 4095 - (N + 4095) mod 4096) with N by (Z.div_mod_to_equations; lia).
step. if_lit.
stp.
rewrite (unsigned_lit A) by lia. rewrite ?land_pagemask, ?land_pagemask_l by lia.
replace (A - A mod 4096) with A by lia.
step. step. step. step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (RT1 : RTconst RE X mm) end.
{ eapply RTconst_stack; [exact RT| exact RL| exact MU| exact WM|]. constructor; [cbn [fst]; lia| constructor]. }
call_sp (get_named_mapping_fd_spec _ _); try eassumption; [lia|]. subst x2. clear RT1. rename POST into RT1.
rename x14 into m1 || idtac. rename PC into ST.
stp.
step. step. step. step. step.
step. step.
step_ecall.
split. { cbn [at_nodeA]. at_node_solve. }
intros rsp ans Hdec. destruct ans as [|xg].
-
exfalso. exact (dec_fixedA_noerr _ _ _ Hdec).
-
apply dec_fixedA_ok_inv in Hdec as [-> ->].
rewrite (mmap_len_aligned N) by exact NAL.
apply (munch_weaken _ [(bv_unsigned sp - 368, bv_unsigned sp); (A, A + N)]) in MU.
2:{ unfold sub_fp; cbn [outside]; intros; tauto. }
assert (ROF : forall x : word, A <= bv_unsigned x < A + N -> ro_addr asegs x = false) by (intros xw Hxw; apply a_ro_addr_false; lia).
sys_nret. clear ROF RT1.
step.
step. step. step.
stp. stp. step.
unfold_cond. rewrite (unsigned_lit A) by lia. if_lit.
step. rewrite v_sltu_b2z. rewrite (unsigned_lit A) by lia. fold_closed_in_goal.
replace (18446744073709547520 <? A) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
step.
step. step. stf. step.
step. step.
stp. stp. step.
unfold_cond. rewrite (unsigned_lit A) by lia. if_lit.
step. rewrite v_sltu_b2z. rewrite (unsigned_lit A) by lia. fold_closed_in_goal.
replace (18446744073709547520 <? A) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
step.
step. if_lit.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (RT2 : RTconst RE X mm) end.
{ eapply RTconst_munch; [exact RT| exact MU| exact WM|].
constructor; [apply rt_avoid_stack; [exact RL| lia]| constructor; [exact AV| constructor]]. }
step. call0 (increase_total_mmap_spec RE X); [exact RT2| assumption|].
step. do 6 step. step. step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold map_fixed_post_k. cbn [fixed_fp]. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split.
+ eapply RTconst_munch; [exact RT| exact MU| exact WM|].
constructor; [apply rt_avoid_stack; [exact RL| lia]| constructor; [exact AV| constructor]].
+ split; [reflexivity|]. split; [reflexivity|]. exact ZNEW.
Qed.
End S.

Section S2.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).

Lemma impl_suffix : forall {node : Type} segs (atn : node -> machine_state -> Prop) {R} (t : itree node R) (Q1 Q : R -> machine_state -> Prop) ms,
impl segs atn t Q1 ms -> (forall r ms', Q1 r ms' -> evt segs (Q r) ms') -> impl segs atn t Q ms.
Proof.
intros node segs atn R t. induction t as [r|n k IH]; intros Q1 Q ms H HQ; cbn in *.
- eapply evt_cut; [exact H|]. intros ms' H1. exact (HQ _ _ H1).
- eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; eauto.
Qed.

Lemma map_with_callback_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (A N lo : Z),
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - MMAPFIXED_STACK ->
A mod 4096 = 0 -> N mod 4096 = 0 -> 0 < N -> KHI <= A -> A + N <= band_lo ->
rt_avoid RE X (A, A + N) ->
impl asegs (at_nodeA L asegs) (enode (NMmap A N PROT_RW FL_FIXED) (dec_fixedA A N))
(epost (map_fixed_post RE X ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A N lo m))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz A) (wz N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz map_with_callback_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros RT RL MI ST CEIL LO AAL NAL N0 AK AC AV. unfold map_with_callback_entry, MMAPFIXED_STACK in *.
pose proof CEIL as CEIL'. rewrite ?KHI_eq in AK.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 400, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
iprefix.
carve_frame 32%nat ST.
do 5 stf.
step. step. step. step. step.
step.
step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (RT1 : RTconst RE X mm) end.
{ eapply RTconst_stack; [exact RT| exact RL| exact MU| exact WM|]. constructor; [cbn [fst]; lia| constructor]. }
ihere.
eapply impl_suffix.
{ eapply (mmap_fixed_impl_spec); try eassumption.
- rewrite unsigned_lit by lia. exact ST.
- rewrite unsigned_lit by lia. unfold MMAPFIXED_IMPL_STACK. lia. }
intros [|ans] ms' POST; cbn [epost] in POST |- *; [apply evt_done; exact I|].
destruct POST as (u0 & u1 & u2 & r0 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & u3 & u4 & u5 & u6 & mc1 & -> & MU2 & WM2 & MI2 & ST2 & RT2 & ANS).
destruct ans as [|xg]; [contradiction|]. destruct ANS as (-> & -> & ZNEW). cbn [fixed_fp] in MU2.
rewrite !(unsigned_lit (bv_unsigned sp + -32)) in * by lia. unfold MMAPFIXED_IMPL_STACK in MU2.
lazymatch goal with |- context [ret_pc (wz ?n)] => replace (ret_pc (wz n)) with (wz n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
apply (munch_weaken _ [(bv_unsigned sp - 400, bv_unsigned sp); (A, A + N)]) in MU.
2:{ unfold sub_fp; cbn [outside]; intros; tauto. }
pose proof (wmono_trans _ _ _ _ WM WM2) as WM'.
hide MU. transport_after_call asegs m1 mc1 MU2 WM2. unhide MU.
assert (MU' : munch [(bv_unsigned sp - 400, bv_unsigned sp); (A, A + N)] m mc1) by (eapply munch_chain; [exact MU| exact MU2| sub_fp_solve]).
clear MU MU2 WM2 WM MI; rename MU' into MU.
step. unfold_cond. rewrite (unsigned_lit A) by lia. if_lit.
do 4 step. step. step.
release_frame FR ST2 (bv_unsigned sp).
apply evt_done. unfold map_fixed_post, map_fixed_post_k. cbn [fixed_fp]. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM'|]. split; [assumption|]. split; [exact ST2|]. split; [exact RT2|].
split; [reflexivity|]. split; [reflexivity|]. exact ZNEW.
Qed.
End S2.
End Mqa.

Module Mqb.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QDM6 QwAs.Mq2.
Import Q6sh QKTr.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO QFQR QmP7 QKBN QN4c QNQk.Mq6 QTVW.Mqa.
Import QlES. Local Ltac QbcP_c1.small_offset k ::= QbcP_c1.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition poison_shadow_entry : Z := 0x64bfc.

Lemma land_7 : forall a, 0 <= a -> Z.land a 7 = a mod 8.
Proof. intros a Ha. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Section S.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Definition poison_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(addr size v lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (SH addr, SH addr + size / 8)] m m'
/\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ RTconst RE X m'
/\ rw_cells asegs m' (SH addr) [CB (Z.to_nat (size / 8)) (repeat (b8 v) (Z.to_nat (size / 8)))].

Lemma poison_shadow_spec_gen : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (addr size v lo : Z) (junk : list byte),
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 64 ->
addr mod 8 = 0 -> size mod 8 = 0 -> 0 <= size -> KHI <= addr < 2^47 -> KHI + 8 <= addr + size <= 2^47 ->
0 <= v < 256 -> (v <> 0 \/ size / 8 < 0xffffffffffffffff) ->
rw_cells asegs m (SH addr) [CB (Z.to_nat (size / 8)) junk] ->
evt asegs (poison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr size v lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz addr) (wz size) (wz v) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz poison_shadow_entry) fc None m (seg_rom asegs)).
Proof.
intros until junk; intros RT RL MI ST CEIL LO AAL SAL S0 AK AH VR VC SHD.
pose proof CEIL as CEIL'. idtac. rewrite ?KHI_eq in AK, AH. change (2^47) with 140737488355328 in AK, AH.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
assert (SHa : SH addr = addr / 8 + 0x7fff8000) by reflexivity.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (SH addr, SH addr + size / 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
rtc RT 2%nat K2. rtc RT 19%nat K19. rtc RT 1%nat K1. rtc RT 5%nat K5. rtc RT 23%nat K23. rtc RT 16%nat K16.
unfold poison_shadow_entry.
carve_frame 64%nat ST.
do 8 step.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms1 => exists a3' : word, ms1 = MS (@bvmap_set 5 word 13 a3' R) FF (wz 0x64c30) fcc rv mm ro))
end.
{ step. if_cases Hv.
- apply evt_done. eexists. simp_regs. reflexivity.
- step. stp. step. step. if_lit. apply evt_done. eexists. simp_regs. reflexivity. }
intros ms1 [a3' ->]. simp_regs.
stp. rewrite ?(unsigned_lit addr) by lia. rewrite (land_7 addr) by lia. replace (addr mod 8) with 0 by lia.
step. if_lit.
step. stp. stp.
step. stp. stp. stp.
step. ifz.
step. step. step. step. step. step.
stp. step. ifz.
step. step. step. stp. stp.
step. ifz.
step. ifz.
step. stp. stp. step. ifz. step. ifz.

stp. rewrite ?(unsigned_lit size) by lia. rewrite (land_7 size) by lia. replace (size mod 8) with 0 by lia.
step. if_lit.
step. step.
step. ifz.
step. step. step. step. step. step. stp. step. ifz.
step. step. step. stp. stp.
step. ifz. step. ifz.

step. stp. stp. step. if_lit.
step. step. step. step. step.
rewrite !(unsigned_lit addr), !(unsigned_lit (addr + size + -8)) by lia.
rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite !(unsigned_lit (addr / 8)) by lia.
replace ((addr + size + -8) / 8 + 1 + - (addr / 8)) with (size / 8) by (Z.div_mod_to_equations; lia).
replace (2147450880 + addr / 8) with (SH addr) by lia.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms2 => exists a1' : word, ms2 = MS (@bvmap_set 5 word 11 a1' R) FF (wz 0x64f64) fcc rv mm ro))
end.
{ step. if_cases Hv.
-  apply evt_done. eexists. simp_regs. reflexivity.
-
zify_cond Hv. rewrite ?(unsigned_lit v) in Hv by lia.
step. stp. stp. step. ifz. apply evt_done. eexists. simp_regs. reflexivity. }
intros ms2 [a1' ->]. simp_regs.
step. step.
step. do 7 step. step.
release_frame FR ST (bv_unsigned sp).
step.
assert (SHR : 0 <= SH addr /\ SH addr + size / 8 < 2^64) by (rewrite SHa; Z.div_mod_to_equations; lia).
eapply evt_cut.
{ eapply memset_spec; [| eassumption]. rewrite !unsigned_lit by lia. exact SHD. }
intros ms' POST. unfold memset_post in POST. rewrite !unsigned_lit in POST by lia.
destruct POST as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m' & -> & MU2 & WM2 & MI2 & SHD2).
replace (v mod 256) with v in SHD2 by (symmetry; apply Z.mod_small; lia).
apply evt_done. unfold poison_post. do 16 eexists. split; [reflexivity|].
split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; (first [ clear - H x SHR SPR VC VR AH AK v size addr sp; tauto | tauto ]). }
split. { eapply wmono_trans; [exact WM| exact WM2]. }
split. { exact MI2. }
assert (SHhi : SH addr + size / 8 <= KHI) by (rewrite SHa, ?KHI_eq; Z.div_mod_to_equations; lia).
split. { eapply stk_transport_disjoint; [exact ST| exact MU2| exact WM2|]. cbn [disjoint_from]. rewrite ?KHI_eq in SHhi. split; [lia| exact I]. }
split.
{ eapply RTconst_munch; [exact RT| | |].
- eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; (first [ clear - H x SHR SPR VC VR AH AK v size addr sp; tauto | tauto ]).
- eapply wmono_trans; [exact WM| exact WM2].
- constructor; [apply rt_avoid_stack; [exact RL| lia]|].
constructor; [| constructor]. apply rt_avoid_gap; [exact RL| rewrite SHa; unfold kLowEnd; lia| exact SHhi]. }
exact SHD2.
Qed.

Lemma poison_shadow_spec_gen_low : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (addr size v lo : Z) (junk : list byte),
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 64 ->
addr mod 8 = 0 -> size mod 8 = 0 -> 0 <= size -> 0 <= addr < 0x7fff8000 -> 8 <= addr + size <= 0x7fff8000 ->
0 <= v < 256 -> (v <> 0 \/ size / 8 < 0xffffffffffffffff) ->
rw_cells asegs m (SH addr) [CB (Z.to_nat (size / 8)) junk] ->
evt asegs (poison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr size v lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz addr) (wz size) (wz v) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz poison_shadow_entry) fc None m (seg_rom asegs)).
Proof.
intros until junk; intros RT RL MI ST CEIL LO AAL SAL S0 AK AH VR VC SHD.
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
assert (SHa : SH addr = addr / 8 + 0x7fff8000) by reflexivity.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (SH addr, SH addr + size / 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
rtc RT 2%nat K2. rtc RT 19%nat K19. rtc RT 1%nat K1. rtc RT 5%nat K5. rtc RT 23%nat K23. rtc RT 16%nat K16.
unfold poison_shadow_entry.
carve_frame 64%nat ST.
do 8 step.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms1 => exists a3' : word, ms1 = MS (@bvmap_set 5 word 13 a3' R) FF (wz 0x64c30) fcc rv mm ro))
end.
{ step. if_cases Hv.
- apply evt_done. eexists. simp_regs. reflexivity.
- step. stp. step. step. if_lit. apply evt_done. eexists. simp_regs. reflexivity. }
intros ms1 [a3' ->]. simp_regs.
stp. rewrite ?(unsigned_lit addr) by lia. rewrite (land_7 addr) by lia. replace (addr mod 8) with 0 by lia.
step. if_lit.
step. stp. stp.
step. stp. stp. stp.
step. ifz.
stp. rewrite ?(unsigned_lit size) by lia. rewrite (land_7 size) by lia. replace (size mod 8) with 0 by lia.
step. if_lit.
step. step.
step. ifz.

step. stp. stp. step. if_lit.
step. step. step. step. step.
rewrite !(unsigned_lit addr), !(unsigned_lit (addr + size + -8)) by lia.
rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite !(unsigned_lit (addr / 8)) by lia.
replace ((addr + size + -8) / 8 + 1 + - (addr / 8)) with (size / 8) by (Z.div_mod_to_equations; lia).
replace (2147450880 + addr / 8) with (SH addr) by lia.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms2 => exists a1' : word, ms2 = MS (@bvmap_set 5 word 11 a1' R) FF (wz 0x64f64) fcc rv mm ro))
end.
{ step. if_cases Hv.
-  apply evt_done. eexists. simp_regs. reflexivity.
-
zify_cond Hv. rewrite ?(unsigned_lit v) in Hv by lia.
step. stp. stp. step. ifz. apply evt_done. eexists. simp_regs. reflexivity. }
intros ms2 [a1' ->]. simp_regs.
step. step.
step. do 7 step. step.
release_frame FR ST (bv_unsigned sp).
step.
assert (SHR : 0 <= SH addr /\ SH addr + size / 8 < 2^64) by (rewrite SHa; Z.div_mod_to_equations; lia).
eapply evt_cut.
{ eapply memset_spec; [| eassumption]. rewrite !unsigned_lit by lia. exact SHD. }
intros ms' POST. unfold memset_post in POST. rewrite !unsigned_lit in POST by lia.
destruct POST as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m' & -> & MU2 & WM2 & MI2 & SHD2).
replace (v mod 256) with v in SHD2 by (symmetry; apply Z.mod_small; lia).
apply evt_done. unfold poison_post. do 16 eexists. split; [reflexivity|].
split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; (first [ clear - H x SHR SPR VC VR AH AK v size addr sp; tauto | tauto ]). }
split. { eapply wmono_trans; [exact WM| exact WM2]. }
split. { exact MI2. }
assert (SHhi : SH addr + size / 8 <= KHI) by (rewrite SHa, ?KHI_eq; Z.div_mod_to_equations; lia).
split. { eapply stk_transport_disjoint; [exact ST| exact MU2| exact WM2|]. cbn [disjoint_from]. rewrite ?KHI_eq in SHhi. split; [lia| exact I]. }
split.
{ eapply RTconst_munch; [exact RT| | |].
- eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; (first [ clear - H x SHR SPR VC VR AH AK v size addr sp; tauto | tauto ]).
- eapply wmono_trans; [exact WM| exact WM2].
- constructor; [apply rt_avoid_stack; [exact RL| lia]|].
constructor; [| constructor]. apply rt_avoid_gap; [exact RL| rewrite SHa; unfold kLowEnd; lia| exact SHhi]. }
exact SHD2.
Qed.

Lemma poison_shadow_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (addr size v lo : Z) (junk : list byte),
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 64 ->
addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> KHI <= addr -> addr + size <= 2^47 ->
0 <= v < 256 -> (v <> 0 \/ size / 8 < 0xffffffffffffffff) ->
rw_cells asegs m (SH addr) [CB (Z.to_nat (size / 8)) junk] ->
evt asegs (poison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr size v lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz addr) (wz size) (wz v) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz poison_shadow_entry) fc None m (seg_rom asegs)).
Proof.
intros until junk; intros RT RL MI ST CEIL LO AAL SAL S0 AK AH VR VC SHD.
eapply poison_shadow_spec_gen; try eassumption; [lia| lia|]. clear - SAL S0 AK AH. Z.div_mod_to_equations. lia.
Qed.

Lemma poison_shadow_spec_lh : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (addr size v lo : Z) (junk : list byte),
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 64 ->
addr mod 8 = 0 -> size mod 8 = 0 -> 0 <= size ->
((KHI <= addr < 2^47 /\ KHI + 8 <= addr + size <= 2^47) \/ (0 <= addr < 0x7fff8000 /\ 8 <= addr + size <= 0x7fff8000)) ->
0 <= v < 256 -> (v <> 0 \/ size / 8 < 0xffffffffffffffff) ->
rw_cells asegs m (SH addr) [CB (Z.to_nat (size / 8)) junk] ->
evt asegs (poison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr size v lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz addr) (wz size) (wz v) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz poison_shadow_entry) fc None m (seg_rom asegs)).
Proof.
intros until junk; intros RT RL MI ST CEIL LO AAL SAL S0 [[AK AH]|[AK AH]] VR VC SHD.
- eapply poison_shadow_spec_gen; eassumption.
- eapply poison_shadow_spec_gen_low; eassumption.
Qed.
End S.
End Mqb.

Module Mqc.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW Q61C QWRO Qu4g QFQR QmP7 QKBN QNQk.Mq6 QmP7.Mq1 QTVW.Mq7.
Import QlES. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.

Local Notation wz := (Z_to_bv 64).

Definition QPOP_STACK : Z := 672.

Section S.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Definition gstep (a a1 : AState) (G G1 : ghost) : Prop :=
same_tags tag_quar G G1 /\ same_tags is_live G G1
/\ (forall c i t, tag_at G c i = Some t -> exists t', tag_at G1 c i = Some t')
/\ (forall LB FS, gcons a LB FS G RE X -> gcons a1 LB FS G1 RE X).

Definition qpop_W (sp : Z) (a : AState) : list (Z * Z) :=
[ (sp - QPOP_STACK, sp); (rl_T X + 208, rl_T X + 3168); (ri_addr RE 24, ri_addr RE 24 + 128);
(fa_beg (ae_L RE) 24, fa_beg (ae_L RE) 24 + kFreeArraySize);
(SH (fa_beg (ae_L RE) 24), SH (fa_beg (ae_L RE) 24) + kFreeArraySize / 8);
(reg_beg (ae_L RE) 24 + c_alloc_user (cls a 24), reg_beg (ae_L RE) 24 + kFreeArrayOffset);
(SH (reg_beg (ae_L RE) 24 + c_alloc_user (cls a 24)), SH (reg_beg (ae_L RE) 24 + kFreeArrayOffset)) ].

Definition qpop_ghost (a a1 : AState) (G G1 : ghost) : Prop := gstep a a1 G G1.

Definition qpop_post (ra sp gp a0 a2 a3 a4 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PStateA) (a : AState) (G : ghost) (lo : Z) (m : word -> option byte)
(r : bool * AState) (s' : PStateA) (ms' : machine_state) : Prop :=
exists (ra' t0 t1 t2 s0 s1 a0' a1 a3' a4' a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 : word) m' G1,
ms' = MS (mkR ra' sp gp (wz A_TP) t0 t1 t2 s0 s1 a0' a1 a2 a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz (if fst r then 0x43970 else 0x43a5c)) fc None m' (seg_rom asegs)
/\ s' = s
/\ munch (qpop_W (bv_unsigned sp) a) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ RTconst RE X m' /\ RStats RE X m' /\ qpop_ghost a (snd r) G G1
/\ if fst r then
a0' = a0 /\ a3' = a3 /\ a4' = a4 /\
exists i, tag_at G1 24 i = Some TCached /\ a1 = wz (slot_beg RE 24 i)
/\ (forall t, tag_prim t = false -> RPrim (snd r) (set_tag 24 i t G1) RE X m')
/\ hjunk m' (slot_beg RE 24 i) (slot_beg RE 24 i + 8192)
/\ rw_cells asegs m' (SH (slot_beg RE 24 i)) [CB 1024%nat (fas 1024)]
else RPrim (snd r) G1 RE X m'.

Definition qpop24_stmt (L : lvp) : Prop :=
forall (ra sp gp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (s : PStateA) (a : AState) (G : ghost) (lo : Z),
RTconst RE X m -> rlay_ok RE X -> RStats RE X m -> RPrim a G RE X m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - QPOP_STACK ->
aimplT (at_nodeA L asegs) (cache_alloc (ae_L RE) a kBatchClass) s
(qpop_post ra sp gp a0 a2 a3 a4 s6 s7 s8 s9 s10 s11 F fc s a G lo m)
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 a0 (wz (rl_T X + 208)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x43920) fc None m (seg_rom asegs)).
End S.

Lemma gstep_refl {BAND : Band} : forall RE X a G, gstep RE X a a G G.
Proof. intros. split; [apply same_tags_refl|]. split; [apply same_tags_refl|]. split; [intros c i t H; exists t; exact H| auto]. Qed.

Lemma gstep_trans {BAND : Band} : forall RE X a a1 a2 G G1 G2, gstep RE X a a1 G G1 -> gstep RE X a1 a2 G1 G2 -> gstep RE X a a2 G G2.
Proof.
intros RE X a a1 a2 G G1 G2 (Q1 & L1 & T1 & C1) (Q2 & L2 & T2 & C2).
split; [intros c i t Ht; rewrite (Q1 c i t Ht); apply Q2; exact Ht|].
split; [intros c i t Ht; rewrite (L1 c i t Ht); apply L2; exact Ht|].
split; [| intros LB FS H; apply C2, C1, H].
intros c i t Ht. destruct (T1 c i t Ht) as [t' Ht']. exact (T2 c i t' Ht').
Qed.

Lemma gstep_state {BAND : Band} : forall RE X a a1 G, (forall LB FS, gcons a LB FS G RE X -> gcons a1 LB FS G RE X) -> gstep RE X a a1 G G.
Proof. intros. split; [apply same_tags_refl|]. split; [apply same_tags_refl|]. split; [intros c i t Ht; exists t; exact Ht| assumption]. Qed.
End Mqc.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJBH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJBH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZzg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q61C.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q61C. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbcP_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbcP_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWRO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWRO. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFQR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFQR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmP7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmP7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKBN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKBN. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mqa.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).

Definition set_shadow_00_entry : Z := 0x658c8.
Definition set_shadow_f8_entry : Z := 0x659e8.
Definition real_memset_entry : Z := 0xdde14.

Section Walk.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Lemma set_shadow_00_stub : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m P,
RTconst RE X m -> rlay_ok RE X ->
evt asegs P (MS (mkR ra sp gp tp t0 (wz real_memset_entry) t2 s0 s1 a0 (wz 0) a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz real_memset_entry) fc None m (seg_rom asegs)) ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz set_shadow_00_entry) fc None m (seg_rom asegs)).
Proof.
intros until P; intros RT RL K. unfold set_shadow_00_entry, real_memset_entry in *.
rt_now RT RL 19%nat K19. rt_now RT RL 23%nat K23.
istep. istep. istep. istep. istep. istep. exact K.
Qed.

Lemma set_shadow_f8_stub : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m P,
RTconst RE X m -> rlay_ok RE X ->
evt asegs P (MS (mkR ra sp gp tp t0 (wz real_memset_entry) t2 s0 s1 a0 (wz 248) a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz real_memset_entry) fc None m (seg_rom asegs)) ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz set_shadow_f8_entry) fc None m (seg_rom asegs)).
Proof.
intros until P; intros RT RL K. unfold set_shadow_f8_entry, real_memset_entry in *.
rt_now RT RL 19%nat K19. rt_now RT RL 23%nat K23.
istep. istep. istep. istep. istep. istep. exact K.
Qed.

End Walk.

Lemma stk_after_memset : forall m m' lo hi dst n bs,
stk asegs m lo hi -> munch [(dst, dst + n)] m m' -> wmono asegs m m' ->
rw_cells asegs m' dst [CB (Z.to_nat n) bs] -> 0 <= n ->
stk asegs m' lo hi.
Proof.
intros m m' lo hi dst n bs (S1 & S2 & S3) MU WM RC Hn. split; [exact S1|]. split; [exact S2|].
intros a Ha. destruct (S3 a Ha) as [Wv (b & Hb)]. split; [apply WM; exact Wv|].
destruct RC as [[[WF _] (B1 & B2 & B3)] _]. cbn [cell_wf] in WF. cbn [cells_bytes cbytes] in B2, B3.
rewrite app_nil_r in B2, B3. rewrite WF in B2, B3.
destruct (Z_lt_le_dec a dst) as [L|GE]; [| destruct (Z_lt_le_dec a (dst + n)) as [L2|GE2]].
- exists b. unfold mrd in *. rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. cbn. lia.
- specialize (B3 (Z.to_nat (a - dst)) ltac:(lia)).
replace (dst + Z.of_nat (Z.to_nat (a - dst))) with a in B3 by lia.
destruct (nth_error bs (Z.to_nat (a - dst))) as [b'|] eqn:E.
+ exists b'. exact B3.
+ exfalso. apply nth_error_None in E. lia.
- exists b. unfold mrd in *. rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. cbn. lia.
Qed.

Section Lift.
Context {BAND : Band}.
Variable C : arun_components.
Hypothesis HRT : forall RE X m, ac_RTconst C RE X m <-> RTconst RE X m.

Lemma set_shadow_A : forall entry v,
(entry = set_shadow_00_entry /\ v = 0) \/ (entry = set_shadow_f8_entry /\ v = 0xf8) ->
aset_shadowA_stmt asegs a_alayout (ARUN C) entry v.
Proof.
intros entry v EV. unfold aset_shadowA_stmt. intros until lo; intros old s LB FS RE AR ST CEIL LO MI Ha0 Ha1 HN RC.
destruct (ARUN_open C _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
pose proof (proj1 AX) as GC. pose proof (proj1 GC) as RL.
pose proof (proj1 (HRT _ _ _) (proj1 (proj2 AX))) as RT.
pose proof (rw_cells_bound _ _ _ _ RC) as B. cbn [cells_size csize Nat.add] in B.
subst a0 a1.
assert (POST : evt asegs (memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (wz dst) (wz v) (wz n) m)
(MS (mkR ra sp gp tp t0 (wz real_memset_entry) t2 s0 s1 (wz dst) (wz v) (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz real_memset_entry) fc None m (seg_rom asegs))).
{ apply (memset_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ old); [| exact MI].
rewrite !unsigned_lit by lia. exact RC. }
eapply evt_mono.
- destruct EV as [[-> ->]|[-> ->]].
+ eapply (set_shadow_00_stub RE X); [exact RT| exact RL| exact POST].
+ eapply (set_shadow_f8_stub RE X); [exact RT| exact RL| exact POST].
- cbv beta. intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & RC').
assert (Hv : 0 <= v < 256) by (destruct EV as [[_ ->]|[_ ->]]; lia).
rewrite !unsigned_lit in MU by lia. rewrite !unsigned_lit in RC' by lia. rewrite (Z.mod_small v 256) in RC' by lia.
do 15 eexists. split; [reflexivity|].
split. { eapply munch_weaken; [| exact MU]. intros y Hy. cbn [outside fst snd] in Hy |- *. tauto. }
split; [exact WM|]. split; [exact MI'|].
split; [eapply stk_after_memset; [exact ST| exact MU| exact WM| exact RC'| lia]|].
exact RC'.
Qed.

Lemma set_shadow_00_A : aset_shadowA_stmt asegs a_alayout (ARUN C) (ala_set_shadow_00 a_alayout) 0.
Proof. apply set_shadow_A. left. split; reflexivity. Qed.

Lemma set_shadow_f8_A : aset_shadowA_stmt asegs a_alayout (ARUN C) (ala_set_shadow_f8 a_alayout) 0xf8.
Proof. apply set_shadow_A. right. split; reflexivity. Qed.

End Lift.
