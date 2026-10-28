(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup QRjH QHnV QCcH QfLs Q0Ek Q6q3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c UPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek.
Import UC8c.Mq0 UC8c UPZI.Mq0.
Import ListNotations. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Fixpoint okmax (l : list (option jshape)) : Z :=
match l with [] => 0 | None :: l' => okmax l' | Some s :: l' => Z.max (sdepth s) (okmax l') end.
Definition odep (o : option jshape) : Z := match o with None => 0 | Some s => sdepth s end.
#[using="Type"] Lemma kmax_nonneg : forall l, 0 <= (fix kmax (l0 : list (option jshape)) : Z := match l0 with [] => 0 | None :: l' => kmax l' | Some s' :: l' => Z.max (sdepth s') (kmax l') end) l.
Proof. induction l as [|[x|] l IHl]; cbn; lia. Qed.
#[using="Type"] Lemma sdepth_nonneg : forall s, 0 <= sdepth s.
Proof. intros [| | | |kids|kids]; cbn -[Z.add Z.max]; try lia; pose proof (kmax_nonneg kids); lia. Qed.
#[using="Type"] Lemma okmax_nonneg : forall l, 0 <= okmax l.
Proof. induction l as [|[x|] l IH]; cbn; lia. Qed.
#[using="Type"] Lemma odep_nonneg : forall o, 0 <= odep o.
Proof. intros [s|]; cbn; [apply sdepth_nonneg | lia]. Qed.
#[using="Type"] Lemma sdepth_Sobj : forall kids, sdepth (Sobj kids) = 1 + okmax kids.
Proof. reflexivity. Qed.
#[using="Type"] Lemma sdepth_Sarr : forall kids, sdepth (Sarr kids) = 1 + okmax kids.
Proof. reflexivity. Qed.
#[using="Type"] Lemma okmax_app : forall l1 l2, okmax (l1 ++ l2) = Z.max (okmax l1) (okmax l2).
Proof.
intros l1; induction l1 as [|[x|] l1 IH]; intros l2; cbn -[Z.max].
- pose proof (okmax_nonneg l2). lia.
- rewrite IH. pose proof (sdepth_nonneg x). lia.
- apply IH.
Qed.
#[using="Type"] Lemma okmax_cons : forall o l, okmax (o :: l) = Z.max (odep o) (okmax l).
Proof. intros [x|] l; cbn -[Z.max]; pose proof (okmax_nonneg l); lia. Qed.
#[using="Type"] Lemma okmax_single : forall o, okmax [o] = odep o.
Proof. intros [x|]; cbn -[Z.max]; [pose proof (sdepth_nonneg x); lia | reflexivity]. Qed.

Section JoStmts.
Variable L : heap_layout.
Variable HIx : heap_iface L.
Variable fn : fnaddrs.
Variable G : (word -> option byte) -> Prop.
Notation segs := (hl_segs L).

Definition jo_pre (A : AS L HIx) (LBall : list blk) (m : word -> option byte) (md : Model)
(sp tp ra : word) (lo stkb : Z) (errv : word) : Prop :=
HEAP L HIx A LBall m md /\
stk segs m lo (bv_unsigned sp) /\ alloc_ceiling <= lo /\ lo <= bv_unsigned sp - stkb /\
bv_unsigned sp mod 16 = 0 /\ bv_unsigned sp <= hi_top L HIx /\
rw_cells segs m (hl_tp L - 164) [C4 errv] /\
tp = Z_to_bv 64 (hl_tp L) /\ bv_unsigned ra mod 2 = 0.

Definition jo_post_frame (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo : Z)
(r : Z) (m' : word -> option byte) (ms' : machine_state) (md' : Model) : Prop :=
ret_statew L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only md md' /\
stk segs m' lo (bv_unsigned sp) /\
heap_pres L LB (bv_unsigned sp) m m' /\
(exists errv', rw_cells segs m' (hl_tp L - 164) [C4 errv']).

Definition jo_post_framex (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo : Z)
(r : Z) (m' : word -> option byte) (ms' : machine_state) (md' : Model) : Prop :=
ret_statew L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only md md' /\
stk segs m' lo (bv_unsigned sp) /\
heap_presx L (hl_volatile L) LB (bv_unsigned sp) m m' /\
(exists errv', rw_cells segs m' (hl_tp L - 164) [C4 errv']).

Definition jo_new_container_stmt (entry stkb : Z) (s : jshape) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS L HIx) (LB : list blk) (lo : Z) (errv : word),
jo_pre A LB m md sp tp ra lo stkb errv -> G m ->
(forall ms' md' m' r, jo_post_frame ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo r m' ms' md' ->
((r = 0 /\ exists A', HEAP L HIx A' LB m' md') \/
(r <> 0 /\ exists A' BS, jval segs fn s m' BS r 1 /\ HEAP L HIx A' (BS ++ LB) m' md')) ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom segs)) md) T.

Definition jo_array_add_stmt (entry stkb : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS L HIx) (LB ABS VBS : list blk) (lo p v : Z) (kids : list (option jshape)) (vs : option jshape) (errv : word),
jo_pre A (ABS ++ VBS ++ LB) m md sp tp ra lo stkb errv ->
jval segs fn (Sarr kids) m ABS p 1 -> jopt segs fn vs m VBS v ->
a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 v ->
(forall ms' md' m' r, jo_post_frame ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo r m' ms' md' ->
((r = 0 /\ exists A' ABS', jval segs fn (Sarr (kids ++ [vs])) m' ABS' p 1 /\ HEAP L HIx A' (ABS' ++ LB) m' md') \/
(r = 2^64 - 1 /\ exists A', jval segs fn (Sarr kids) m' ABS p 1 /\ jopt segs fn vs m' VBS v /\ HEAP L HIx A' (ABS ++ VBS ++ LB) m' md')) ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom segs)) md) T.

Definition jo_array_shrink_stmt (entry stkb : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS L HIx) (LB ABS : list blk) (lo p : Z) (kids : list (option jshape)) (errv : word),
jo_pre A (ABS ++ LB) m md sp tp ra lo stkb errv ->
jval segs fn (Sarr kids) m ABS p 1 -> a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 0 ->
(forall ms' md' m' r, jo_post_frame ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo r m' ms' md' ->
(exists A' ABS', jval segs fn (Sarr kids) m' ABS' p 1 /\ HEAP L HIx A' (ABS' ++ LB) m' md') ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom segs)) md) T.

Definition jo_object_add_stmt (entry stkb : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS L HIx) (LB OBS VBS : list blk) (lo p v k kn : Z) (ks : list byte) (kids : list (option jshape)) (vs : option jshape) (errv : word),
jo_pre A (OBS ++ VBS ++ LB) m md sp tp ra lo stkb errv -> G m ->
jval segs fn (Sobj kids) m OBS p 1 -> jopt segs fn vs m VBS v ->
In (k, kn) LB -> cstr segs m k kn ks -> kn <= 2^31 ->
frm0 fc ->
a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 k -> a2 = Z_to_bv 64 v ->
(forall ms' md' m' r, jo_post_framex ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo r m' ms' md' -> G m' ->
((r = 0 /\ exists A' OBS' kids', jval segs fn (Sobj kids') m' OBS' p 1 /\ HEAP L HIx A' (OBS' ++ LB) m' md'
/\ Z.of_nat (length kids') <= Z.of_nat (length kids) + 1
/\ okmax kids' <= Z.max (okmax kids) (odep vs)) \/
(r = 2^64 - 1 /\ exists A' REM, jval segs fn (Sobj kids) m' OBS p 1 /\ jopt segs fn vs m' VBS v /\ HEAP L HIx A' (OBS ++ VBS ++ REM ++ LB) m' md')) ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom segs)) md) T.

Definition jo_object_add_ex_stmt (entry stkb opts : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS L HIx) (LB OBS VBS : list blk) (lo p v k kn : Z) (ks : list byte) (kids : list (option jshape)) (vs : option jshape) (errv : word),
jo_pre A (OBS ++ VBS ++ LB) m md sp tp ra lo stkb errv -> G m ->
jval segs fn (Sobj kids) m OBS p 1 -> jopt segs fn vs m VBS v ->
In (k, kn) LB -> cstr segs m k kn ks -> kn <= 2^31 ->
frm0 fc ->
a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 k -> a2 = Z_to_bv 64 v -> a3 = Z_to_bv 64 opts ->
(forall ms' md' m' r, jo_post_framex ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo r m' ms' md' -> G m' ->
((r = 0 /\ exists A' OBS' kids', jval segs fn (Sobj kids') m' OBS' p 1 /\ HEAP L HIx A' (OBS' ++ LB) m' md'
/\ Z.of_nat (length kids') <= Z.of_nat (length kids) + 1
/\ okmax kids' <= Z.max (okmax kids) (odep vs)) \/
(r = 2^64 - 1 /\ exists A' REM, jval segs fn (Sobj kids) m' OBS p 1 /\ jopt segs fn vs m' VBS v /\ HEAP L HIx A' (OBS ++ VBS ++ REM ++ LB) m' md')) ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom segs)) md) T.

End JoStmts.

Definition jo_new_object_P (HIx : heap_iface S4L) := jo_new_container_stmt S4L HIx S4F jc_glob_P 0x253bc (48 + 48 + 8256) (Sobj []).
Definition jo_new_array_P (HIx : heap_iface S4L) := jo_new_container_stmt S4L HIx S4F (fun _ => True) 0x2682c (32 + 32 + 8256) (Sarr []).
Definition jo_array_add_P (HIx : heap_iface S4L) := jo_array_add_stmt S4L HIx S4F 0x26908 (64 + 8256).
Definition jo_array_shrink_P (HIx : heap_iface S4L) := jo_array_shrink_stmt S4L HIx S4F 0x26938 (64 + 8256).
Definition jo_object_add_P (HIx : heap_iface S4L) := jo_object_add_stmt S4L HIx S4F jc_glob_P 0x25614 (96 + 64 + 64 + 8256 + 2048).
Definition jo_object_add_ex_P (HIx : heap_iface S4L) (opts : Z) := jo_object_add_ex_stmt S4L HIx S4F jc_glob_P 0x254f8 (96 + 64 + 64 + 8256 + 2048) opts.

End RC__1.
End Mq0.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UPZI.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBpc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBpc.
Import ListNotations. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Lemma rw_cells_img_gen : forall segs (m : word -> option byte) A bs cs,
(forall i, (A <= i < A + Z.of_nat (length bs))%Z -> m (Z_to_bv 64 i) = None) ->
QBpc.rw_bytes_b segs A bs = true -> (0 <= A)%Z -> (A + Z.of_nat (length bs) <= 2^64)%Z ->
cells_wf cs -> cells_bytes cs = bs -> cells_size cs = length bs ->
rw_cells segs m A cs.
Proof.
intros segs m A bs cs Hn Hb HA Hhi WF E1 E2.
apply (QBpc.rw_cells_recast segs m A [CB (length bs) bs] cs); [| exact WF| cbn; rewrite app_nil_r; exact E1| cbn; rewrite Nat.add_0_r; exact E2].
apply QBpc.rw_cells_image0; [| exact Hb| exact HA| exact Hhi].
intros a Ha. rewrite <- (Z_to_bv_bv_unsigned a). apply Hn. exact Ha.
Qed.

Lemma jc_glob_P_init : forall m : word -> option byte,
(forall a, (0x66a38 <= a < 0x66a44 \/ 0x658e0 <= a < 0x658e8 \/ 0x66f20 <= a < 0x66f28) -> m (Z_to_bv 64 a) = None) ->
jc_glob_P m.
Proof.
intros m NONE. split; [| split].
- exists (Z_to_bv 64 0xffffffff).
eapply (rw_cells_img_gen rsegs m 0x66a38 (cells_bytes [C8 (Z_to_bv 64 (fn_lh_char_hash S4F)); C4 (Z_to_bv 64 0xffffffff)]));
[intros i Hi; apply NONE; cbn in Hi; lia | vm_compute; reflexivity | lia | cbn; lia | cbn; repeat split; lia | reflexivity | reflexivity].
- eapply (rw_cells_img_gen rsegs m 0x658e0 (cells_bytes [C8 (Z_to_bv 64 (fn_lh_char_equal S4F))]));
[intros i Hi; apply NONE; cbn in Hi; lia | vm_compute; reflexivity | lia | cbn; lia | cbn; repeat split; lia | reflexivity | reflexivity].
- exists JG_CGT_P. split; [| left; reflexivity].
eapply (rw_cells_img_gen rsegs m 0x66f20 (cells_bytes [C8 (Z_to_bv 64 JG_CGT_P)]));
[intros i Hi; apply NONE; cbn in Hi; lia | vm_compute; reflexivity | lia | cbn; lia | cbn; repeat split; lia | reflexivity | reflexivity].
Qed.
