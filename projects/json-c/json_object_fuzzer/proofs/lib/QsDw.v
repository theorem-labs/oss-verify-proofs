(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs QCiC Q6sh QQwg QKTr QvDJ QJBH QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk QTVW QpY2 QOJv Q9Ho QqLk QnRU QmP7 QYyZ Qu3b QpME QkJ4 QlES QVo2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr QvDJ.Mq2.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk.Mq1 QTVW.Mq0 QNQk.Mq4 QpY2.Mq8 QTVW.Mq3 QOJv.Mq4 QNQk.Mq2 Q9Ho.Mq2 QqLk QnRU.Mqa QmP7.Mq0 QpY2.Mq1 Q9Ho.Mq1 QYyZ.Mq0 QnRU.Mq0 QOJv.Mq5 Qu3b.Mq2 QYyZ.Mq5 QYyZ.Mq3 QpME.Mq1 QkJ4.
Import QlES.
Import QVo2.

Import ListNotations.
Import Qc6I.Exc. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition calloc_icpt_entry : Z := 0x636d0.
Definition asan_calloc_entry : Z := 0x3f9f0.

Definition CALLOC_STACK : Z := 2192 + ALLOC_STACK.

Section S.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Definition calloc_W (bp : Z) (c au : Z) : list (Z * Z) :=
(bp - CALLOC_STACK, bp) :: (rl_T X + 3168, rl_T X + 3169) :: (A_ERRNO, A_ERRNO + 4) :: tl (alloc_W RE X (bp - 2192) c au).

Definition calloc_post (ra : word) (bp : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PStateA) (a : AState) (G : ghost) (n lo : Z) (m : word -> option byte)
(r : option aptr * AState) (s' : PStateA) (ms' : machine_state) : Prop :=
exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' G1,
ms' = MS (mkR ra (wz bp) gp (wz A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ s' = s
/\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo bp
/\ RTconst RE X m' /\ RStats RE X m' /\ RDepot RE X m' /\ depot_step m m'
/\ match r with
| (None, a1) => a0 = wz 0 /\ munch (calloc_W bp (class_of n) (c_alloc_user (cls a (class_of n)))) m m'
/\ qframe a a1 /\ gstep RE X a a1 G G1 /\ RPrim a1 G1 RE X m'
| (Some p, a2) => exists a1 i,
p = APrim (as_next a1) n /\ a2 = set_next (N.succ (as_next a1)) a1 /\ qframe a a1
/\ gstep RE X a a1 G G1 /\ tag_at G1 (class_of n) i = Some TCached /\ 0 <= i
/\ a0 = wz (slot_beg RE (class_of n) i + rz_size n)
/\ munch (calloc_W bp (class_of n) (c_alloc_user (cls a (class_of n))) ++ slot_W RE (class_of n) i) m m'
/\ (forall t, tag_prim t = false -> RPrim a1 (set_tag (class_of n) i t G1) RE X m')
/\ chunk_mem m' (slot_beg RE (class_of n) i) (slot_beg RE (class_of n) i + class_size (class_of n)) (slot_beg RE (class_of n) i + rz_size n) n
/\ rw_cells asegs m' (slot_beg RE (class_of n) i + rz_size n) [CB (Z.to_nat n) (repeat (b8 0) (Z.to_nat n))]
end.

Lemma user_frame : forall a1 LB FS G1 c i m m' W,
gcons a1 LB FS G1 RE X -> tag_at G1 c i = Some TCached -> 0 <= i ->
munch W m m' -> wmono asegs m m' ->
(forall lo hi x, In (lo, hi) W -> lo <= x < hi -> slot_beg RE c i <= x < slot_beg RE c i + class_size c) ->
(RTconst RE X m -> RTconst RE X m') /\ (RStats RE X m -> RStats RE X m') /\ (RDepot RE X m -> RDepot RE X m')
/\ ((forall t, tag_prim t = false -> RPrim a1 (set_tag c i t G1) RE X m) -> forall t, tag_prim t = false -> RPrim a1 (set_tag c i t G1) RE X m').
Proof.
intros a1 LB FS G1 c i m m' W GC1 TI I0 MU WM HW.
pose proof (gc_rlay _ _ _ _ _ _ GC1) as RL. pose proof kconsts as (KR & KO & KS & K32 & _).
pose proof (tag_slot _ _ _ _ _ _ GC1 c i TCached TI) as (C1 & _ & _ & SL1 & SL2 & SL3 & SL4 & _). rewrite KO in SL4.
pose proof (reg_geom RE X RL c ltac:(lia)) as (RB & _ & _ & _ & _ & PH & _).
set (Gq := set_tag c i TQOwn G1).
assert (TIq : tag_at Gq c i = Some TQOwn) by (apply (tag_at_set_tag_eq _ _ _ _ _ TI)).
assert (GCq : gcons a1 LB FS Gq RE X) by (apply (gcons_retag_nonlive _ _ _ _ _ _ _ _ _ _ GC1 TI eq_refl); [intros q0; reflexivity| reflexivity]).
assert (HW' : forall lo hi x, In (lo, hi) W -> lo <= x < hi -> tzone RE X Gq c i x).
{ intros lo hi x Hin Hx. right; left. pose proof (HW lo hi x Hin Hx). split; cbn [fst snd]; lia. }
destruct (tzone_frame RE X a1 LB FS Gq c i m m' W GCq TIq MU WM HW') as (FP & FS' & FD).
assert (QZs : forall z, slot_beg RE c i <= z < slot_beg RE c i + class_size c -> fp_RQuar a1 LB Gq RE X z).
{ intros z Hz. do 5 right; left. exists c, i, TQOwn. split; [exact TIq|]. split; [reflexivity|]. split; cbn [fst snd]; lia. }
split; [| split; [| split]].
- intros RT. eapply RTconst_munch; [exact RT| exact MU| exact WM|]. apply Forall_forall. intros [lo hi] Hin x Hx Fx. cbn [fst snd] in Hx.
pose proof (HW lo hi x Hin Hx) as XS.
exact (rt_avoid_prim RE X RL (slot_beg RE c i) (slot_beg RE c i + class_size c) ltac:(lia) ltac:(rewrite PH; lia) x ltac:(cbn [fst snd]; lia) Fx).
- intros RS. apply FS'; [| exact RS]. intros lo hi x Hin Hx Fx. exact (fpQ_RStats _ _ _ _ _ _ GCq x (QZs x (HW _ _ _ Hin Hx)) Fx).
- intros RD. apply FD; [| exact RD]. intros lo hi x Hin Hx Fx. exact (fpQ_RDepot _ _ _ _ _ _ GCq x (QZs x (HW _ _ _ Hin Hx)) Fx).
- intros RPF t Ht. pose proof (FP (RPF TQOwn eq_refl)) as RPq.
pose proof (RPrim_retag _ _ _ _ _ _ _ _ t RPq TIq eq_refl Ht) as RPt.
destruct (retag_twice G1 c i TCached TQOwn t tag_prim TI I0) as [SL SG].
eapply RPrim_ext; [exact RPt| intros; reflexivity| reflexivity| exact SL| exact SG].
Qed.

Lemma chunk_mem_agree_user : forall m m' lo hi A n,
chunk_mem m lo hi A n -> wmono asegs m m' -> agree_on asegs (fun z => ~ (A <= z < A + n)) m m' ->
chunk_mem m' lo hi A n.
Proof.
intros m m' lo hi A n CM WM AG.
destruct CM as (LEFT & (b1 & id & B1 & HDR) & WR & RIGHT & SHD & PURE).
pose proof PURE as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9).
pose proof (round_up_ge (used_size n) 8 ltac:(lia)) as (U1 & U2 & U3). pose proof (ngran_eq (used_size n) ltac:(unfold used_size; lia)) as (N1 & N2 & N3).
idtac. rewrite ?KHI_eq in M8.
split; [|split; [|split; [|split; [|split; [|exact PURE]]]]].
- intros Hrz. destruct (LEFT Hrz) as [L1 L2]. split.
+ eapply rw_cells_agree; [exact AG| exact L1|]. intros z Hz. cbn [cells_size csize Nat.add] in Hz. cbn beta. lia.
+ eapply hjunk_agree; [exact AG| exact L2|]. intros z Hz. cbn beta. lia.
- exists b1, id. split; [exact B1|]. eapply rw_cells_agree; [exact AG| exact HDR|]. intros z Hz. cbn [hdr_cells cells_size csize Nat.add] in Hz. cbn beta. lia.
- eapply wr_at_transport; [exact WR| exact WM].
- eapply hjunk_agree; [exact AG| exact RIGHT|]. intros z Hz. cbn beta. lia.
- eapply rw_cells_agree; [exact AG| exact SHD|]. intros z Hz. cbn beta.
cbn [cells_size csize] in Hz. unfold fas in Hz. rewrite !Nat.add_0_r in Hz.
rewrite !Nat2Z.inj_add, !Z2Nat.id in Hz by (unfold used_size in *; Z.div_mod_to_equations; (first [ clear - H24 q4 H14 q2 H0 H r Hz z N3 N1 q1 U1 M8 M6 M5 M4 M2 PURE r5 r4 r3 r2 q0 q n A hi lo BAND N2 H29 q5 H5 H4 r0 M1; lia | lia ])).
unfold SH, A_SHADOW_OFS in Hz. unfold used_size in *. Z.div_mod_to_equations. (first [ clear - H34 q6 H10 H9 r1 H5 H4 r0 H0 H r Hz q z N3 N1 q2 U1 M9 M8 M6 M4 M1 PURE r6 r5 r4 r3 q1 q0 n A hi lo BAND; lia | lia ]).
Qed.

End S.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg QbcP_c1 Q61C QWRO Qu4g QFQR QKBN QN4c QV3O QpF1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr QvDJ.Mq2.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c QNQk.Mq6 QTVW.Mq7 QNQk.Mq8 QpY2.Mqi QTVW.Mqa QOJv.Mqb QNQk Q9Ho.Mq4 QV3O QnRU.Mql QmP7.Mq1 QpY2.Mqb Q9Ho.Mq3 QYyZ.Mq8 QnRU.Mqc QOJv.Mqc Qu3b QYyZ.Mqc QYyZ.Mqa QpME.Mq8 QpF1.
Import QlES.
Import QVo2.Mq2.

Import ListNotations.
Import Qc6I.Exc. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition calloc_icpt_entry : Z := 0x63aa8.
Definition asan_calloc_entry : Z := 0x3fc1c.

Definition CALLOC_STACK : Z := 2192 + ALLOC_STACK.

Section S.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Definition calloc_W (bp : Z) (c au : Z) : list (Z * Z) :=
(bp - CALLOC_STACK, bp) :: (rl_T X + 3168, rl_T X + 3169) :: (A_ERRNO, A_ERRNO + 4) :: tl (alloc_W RE X (bp - 2192) c au).

Definition calloc_post (ra : word) (bp : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PStateA) (a : AState) (G : ghost) (n lo : Z) (m : word -> option byte)
(r : option aptr * AState) (s' : PStateA) (ms' : machine_state) : Prop :=
exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' G1,
ms' = MS (mkR ra (wz bp) gp (wz A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ s' = s
/\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo bp
/\ RTconst RE X m' /\ RStats RE X m' /\ RDepot RE X m' /\ depot_step m m'
/\ match r with
| (None, a1) => a0 = wz 0 /\ munch (calloc_W bp (class_of n) (c_alloc_user (cls a (class_of n)))) m m'
/\ qframe a a1 /\ gstep RE X a a1 G G1 /\ RPrim a1 G1 RE X m'
| (Some p, a2) => exists a1 i,
p = APrim (as_next a1) n /\ a2 = set_next (N.succ (as_next a1)) a1 /\ qframe a a1
/\ gstep RE X a a1 G G1 /\ tag_at G1 (class_of n) i = Some TCached /\ 0 <= i
/\ a0 = wz (slot_beg RE (class_of n) i + rz_size n)
/\ munch (calloc_W bp (class_of n) (c_alloc_user (cls a (class_of n))) ++ slot_W RE (class_of n) i) m m'
/\ (forall t, tag_prim t = false -> RPrim a1 (set_tag (class_of n) i t G1) RE X m')
/\ chunk_mem m' (slot_beg RE (class_of n) i) (slot_beg RE (class_of n) i + class_size (class_of n)) (slot_beg RE (class_of n) i + rz_size n) n
/\ rw_cells asegs m' (slot_beg RE (class_of n) i + rz_size n) [CB (Z.to_nat n) (repeat (b8 0) (Z.to_nat n))]
end.

Lemma user_frame : forall a1 LB FS G1 c i m m' W,
gcons a1 LB FS G1 RE X -> tag_at G1 c i = Some TCached -> 0 <= i ->
munch W m m' -> wmono asegs m m' ->
(forall lo hi x, In (lo, hi) W -> lo <= x < hi -> slot_beg RE c i <= x < slot_beg RE c i + class_size c) ->
(RTconst RE X m -> RTconst RE X m') /\ (RStats RE X m -> RStats RE X m') /\ (RDepot RE X m -> RDepot RE X m')
/\ ((forall t, tag_prim t = false -> RPrim a1 (set_tag c i t G1) RE X m) -> forall t, tag_prim t = false -> RPrim a1 (set_tag c i t G1) RE X m').
Proof.
intros a1 LB FS G1 c i m m' W GC1 TI I0 MU WM HW.
pose proof (gc_rlay _ _ _ _ _ _ GC1) as RL. pose proof kconsts as (KR & KO & KS & K32 & _).
pose proof (tag_slot _ _ _ _ _ _ GC1 c i TCached TI) as (C1 & _ & _ & SL1 & SL2 & SL3 & SL4 & _). rewrite KO in SL4.
pose proof (reg_geom RE X RL c ltac:(lia)) as (RB & _ & _ & _ & _ & PH & _).
set (Gq := set_tag c i TQOwn G1).
assert (TIq : tag_at Gq c i = Some TQOwn) by (apply (tag_at_set_tag_eq _ _ _ _ _ TI)).
assert (GCq : gcons a1 LB FS Gq RE X) by (apply (gcons_retag_nonlive _ _ _ _ _ _ _ _ _ _ GC1 TI eq_refl); [intros q0; reflexivity| reflexivity]).
assert (HW' : forall lo hi x, In (lo, hi) W -> lo <= x < hi -> tzone RE X Gq c i x).
{ intros lo hi x Hin Hx. right; left. pose proof (HW lo hi x Hin Hx). split; cbn [fst snd]; lia. }
destruct (tzone_frame RE X a1 LB FS Gq c i m m' W GCq TIq MU WM HW') as (FP & FS' & FD).
assert (QZs : forall z, slot_beg RE c i <= z < slot_beg RE c i + class_size c -> fp_RQuar a1 LB Gq RE X z).
{ intros z Hz. do 5 right; left. exists c, i, TQOwn. split; [exact TIq|]. split; [reflexivity|]. split; cbn [fst snd]; lia. }
split; [| split; [| split]].
- intros RT. eapply RTconst_munch; [exact RT| exact MU| exact WM|]. apply Forall_forall. intros [lo hi] Hin x Hx Fx. cbn [fst snd] in Hx.
pose proof (HW lo hi x Hin Hx) as XS.
exact (rt_avoid_prim RE X RL (slot_beg RE c i) (slot_beg RE c i + class_size c) ltac:(lia) ltac:(rewrite PH; lia) x ltac:(cbn [fst snd]; lia) Fx).
- intros RS. apply FS'; [| exact RS]. intros lo hi x Hin Hx Fx. exact (fpQ_RStats _ _ _ _ _ _ GCq x (QZs x (HW _ _ _ Hin Hx)) Fx).
- intros RD. apply FD; [| exact RD]. intros lo hi x Hin Hx Fx. exact (fpQ_RDepot _ _ _ _ _ _ GCq x (QZs x (HW _ _ _ Hin Hx)) Fx).
- intros RPF t Ht. pose proof (FP (RPF TQOwn eq_refl)) as RPq.
pose proof (RPrim_retag _ _ _ _ _ _ _ _ t RPq TIq eq_refl Ht) as RPt.
destruct (retag_twice G1 c i TCached TQOwn t tag_prim TI I0) as [SL SG].
eapply RPrim_ext; [exact RPt| intros; reflexivity| reflexivity| exact SL| exact SG].
Qed.

Lemma chunk_mem_agree_user : forall m m' lo hi A n,
chunk_mem m lo hi A n -> wmono asegs m m' -> agree_on asegs (fun z => ~ (A <= z < A + n)) m m' ->
chunk_mem m' lo hi A n.
Proof.
intros m m' lo hi A n CM WM AG.
destruct CM as (LEFT & (b1 & id & B1 & HDR) & WR & RIGHT & SHD & PURE).
pose proof PURE as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9).
pose proof (round_up_ge (used_size n) 8 ltac:(lia)) as (U1 & U2 & U3). pose proof (ngran_eq (used_size n) ltac:(unfold used_size; lia)) as (N1 & N2 & N3).
idtac. rewrite ?KHI_eq in M8.
split; [|split; [|split; [|split; [|split; [|exact PURE]]]]].
- intros Hrz. destruct (LEFT Hrz) as [L1 L2]. split.
+ eapply rw_cells_agree; [exact AG| exact L1|]. intros z Hz. cbn [cells_size csize Nat.add] in Hz. cbn beta. lia.
+ eapply hjunk_agree; [exact AG| exact L2|]. intros z Hz. cbn beta. lia.
- exists b1, id. split; [exact B1|]. eapply rw_cells_agree; [exact AG| exact HDR|]. intros z Hz. cbn [hdr_cells cells_size csize Nat.add] in Hz. cbn beta. lia.
- eapply wr_at_transport; [exact WR| exact WM].
- eapply hjunk_agree; [exact AG| exact RIGHT|]. intros z Hz. cbn beta. lia.
- eapply rw_cells_agree; [exact AG| exact SHD|]. intros z Hz. cbn beta.
cbn [cells_size csize] in Hz. unfold fas in Hz. rewrite !Nat.add_0_r in Hz.
rewrite !Nat2Z.inj_add, !Z2Nat.id in Hz by (unfold used_size in *; Z.div_mod_to_equations; (first [ clear - H24 q4 H14 q2 H0 H r Hz z N3 N1 q1 U1 M8 M6 M5 M4 M2 PURE r5 r4 r3 r2 q0 q n A hi lo BAND N2 H29 q5 H5 H4 r0 M1; lia | lia ])).
unfold SH, A_SHADOW_OFS in Hz. unfold used_size in *. Z.div_mod_to_equations. (first [ clear - H34 q6 H10 H9 r1 H5 H4 r0 H0 H r Hz q z N3 N1 q2 U1 M9 M8 M6 M4 M1 PURE r6 r5 r4 r3 q1 q0 n A hi lo BAND; lia | lia ]).
Qed.

End S.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjgW QmvA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c QNQk.Mq6 QTVW.Mq7 QjgW QYyZ.Mqc Qu3b.
Import QpY2.Mqc.
Import QmvA.Mq5 QpME.Mqc.
Import QlES.
Import QVo2.Mq2.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Local Notation atn := (at_nodeA L asegs).
Hypothesis large_alloc_spec : large_alloc_stmt RE X L.

Definition combs_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PStateA) (a : AState) (LB : list ablock) (lo n : Z) (m : mem)
(r : option Z * AState) (s' : PStateA) (ms' : machine_state) : Prop :=
exists (t0 t1 t2 a0 a1r a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 a0 a1r a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ s' = s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ wmono asegs m m' /\ RTconst RE X m' /\ RStats RE X m'
/\ match r with
| (None, a1) => a0 = wz 0 /\ a1 = a /\ munch ((bv_unsigned sp - 48, bv_unsigned sp) :: W_large (bv_unsigned sp - 48) RE X) m m' /\ RSec a LB RE X m'
| (Some mb, a1) =>
let msz := sec_map_size n in let sz := sec_size n in
a0 = wz (mb + kPage)
/\ as_reg a1 = as_reg a ++ [mkSec mb msz n]
/\ as_tq a1 = as_tq a /\ as_gq a1 = as_gq a /\ (forall c, cls a1 c = cls a c)
/\ as_cache_inited a1 = as_cache_inited a /\ as_next a1 = as_next a
/\ (as_nres a1 = as_nres a \/ as_nres a1 = as_nres a + kPtrArrBlock)
/\ as_spent a1 = as_spent a + sec_cost msz
/\ mb mod kPage = 0 /\ appr mb msz /\ mb + msz <= band_lo
/\ zavoids mb msz (avoid_of (ae_L RE) a) = true
/\ munch (((bv_unsigned sp - 48, bv_unsigned sp) :: W_large (bv_unsigned sp - 48) RE X) ++ [(mb, mb + msz); (SH mb, SH (mb + msz))]) m m'
/\ RSec a1 LB RE X m'
/\ rw_cells asegs m' (mb + kPage) [CB (Z.to_nat (msz - kPage)) (repeat (b8 0) (Z.to_nat (msz - kPage)))]
/\ hjunk m' (SH (mb + kPage)) (SH (mb + kPage + sz))
/\ rw_cells asegs m' (SH (mb + kPage + sz)) [CB (Z.to_nat ((msz - kPage - sz) / 8)) (fas ((msz - kPage - sz) / 8))]
end.

Lemma combined_sec_spec : forall ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (s : PStateA) (a : AState) (LB : list ablock) (FS : list fframe) (G : ghost) (n lo : Z),
gcons a LB FS G RE X -> avoid_covers RE X ->
RTconst RE X m -> RStats RE X m -> RSec a LB RE X m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - COMB_STACK ->
0 <= n <= 2^26 -> from_primary n = false ->
aimplT atn (large_alloc (ae_L RE) a n) s
(combs_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s a LB lo n m)
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz A_INSTANCE) (wz (rl_T X + 208)) (wz (sec_size n)) (wz 8) a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz combined_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros GC AC RT RS RSE MI ST CEIL LO Hn HP.
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof CEIL as CEIL'. idtac. unfold COMB_STACK in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
assert (HPN : ~ needed n <= kMaxSize) by (intros HH; apply (proj2 (from_primary_iff n)) in HH; rewrite HH in HP; discriminate). unfold kMaxSize in HPN.
pose proof (needed_facts n ltac:(lia)) as NF. pose proof (rz_size_range n) as [RZ1 RZ2].
assert (SS : 65537 <= sec_size n <= 2^26 + 4104) by (unfold sec_size; pose proof (round_up_ge (Z.max n 8) 8 ltac:(lia)); lia).
pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m) as MUs. pose proof (wmono_refl asegs m) as WM.
unfold combined_entry. apply aimplT_from_evt.
carve_frame 48%nat ST.
do 7 step.
step.
replace (v_sltiu (wz (sec_size n)) 1) with (wz 0) by (unfold v_sltiu; rewrite unsigned_lit by lia; change (bv_wrap 64 1) with 1; replace (sec_size n <? 1) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
step.
replace (sec_size n + 0) with (sec_size n) by lia.
step.
rewrite (unsigned_lit (sec_size n)), zb_lxor_ones by lia.
step. ifz.
stp. step. step. ifz.
stp. step. if_lit.
step. ifz.
step. step. step. step.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (RT0 : RTconst RE X mm) end.
{ eapply RTconst_munch; [exact RT| exact MUs| exact WM|]. constructor; [apply rt_avoid_stack; [exact RL| lia]| constructor]. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (RS0 : RStats RE X mm) end.
{ eapply RStats_munch; [exact RS| exact MUs| exact WM|]. constructor; [st_avoid_solve| constructor]. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (RSE0 : RSec a LB RE X mm) end.
{ eapply RSec_frame; [exact RSE| exact WM|]. eapply agree_on_of_munch; [exact MUs| exact WM|]. intros z Fz _. cbn [outside].
pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 4 right; left; exact Fz)). idtac. lia. }
apply evt_done.
eapply aimplT_then.
{ eapply large_alloc_spec; [exact GC| exact AC| exact RT0| exact RS0| exact RSE0| assumption| rewrite unsigned_lit by lia; exact ST| exact CEIL'| rewrite unsigned_lit by lia; unfold LARGE_STACK; lia| exact Hn| exact HP]. }
intros [r a1] s' ms' PO. unfold large_post in PO. rewrite !(unsigned_lit (bv_unsigned sp + -48)) in PO by lia.
destruct PO as (u0 & u1 & u2 & ra0 & ra1 & ra2 & ra3 & ra4 & ra5 & ra6 & ra7 & u3 & u4 & u5 & u6 & m2 & -> & -> & MI2 & ST2 & WM2 & RT2 & RS2 & REST).
replace (ret_pc (wz 277364)) with (wz 277364) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

assert (TAIL : forall mm (Q : machine_state -> Prop),
mem_inv asegs mm -> stk asegs mm lo (bv_unsigned sp + -48) ->
rw_cells asegs mm (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
(stk asegs mm lo (bv_unsigned sp) -> evt asegs Q (MS (mkR ra sp gp (wz A_TP) u0 u1 u2 s0 s1 ra0 (wz 9) ra2 (wz 8) ra4 ra5 ra6 ra7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
F (ret_pc ra) fc None mm (seg_rom asegs))) ->
evt asegs Q (MS (mkR (wz 277364) (wz (bv_unsigned sp + -48)) gp (wz A_TP) u0 u1 u2 (wz 8) s1 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
F (wz 277364) fc None mm (seg_rom asegs))).
{ intros mm Q MIm STm FRm K. step. stp. step. if_lit.
step.
do 6 step. step.
release_frame FRm STm (bv_unsigned sp).
step. apply K. exact STm. }
pose proof (rlay_prim_facts RE X RL) as (_ & _ & _ & _ & QK & QC & _). unfold ptrarr_hi in QC. idtac.
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (TA & TK & TB & TD & _). cbn [fst snd] in TA, TK, TB, TD. idtac.
destruct r as [mb|].
- destruct REST as (-> & REG & TQ & GQ & CLS & CI & NX & NR & SPN & MBP & MBK & MBC & ZA & MU2 & RSE2 & BODY & HJ & FAS).
pose proof MBC as MBC'. idtac.
assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
{ eapply rw_cells_transport; [exact FR| exact MU2| exact WM2|].
unfold W_large, LARGE_STACK. cbn [disjoint_from app]. simpl_sizes. unfold SH, A_SHADOW_OFS, A_INSTANCE in *.
unfold ptrarr_lo, ptrarr_hi in *. Z.div_mod_to_equations. (first [ clear - H39 q7 H34 q6 H33 H32 H31 H30 H29 q5 H5 H4 r0 MBC' TB TK QC QK q0 q MBK MBP r5 NX a1 mb RZ2 r6 RZ1 NF r7 HPN CEIL' LO lo n a sp X RE BAND; lia | lia ]). }
apply TAIL; [exact MI2| exact ST2| exact FR2|]. clear ST2; intros ST2.
apply evt_done. unfold combs_post. do 16 eexists.
split; [reflexivity|]. split; [reflexivity|]. split; [exact MI2|]. split; [exact ST2|].
split; [eapply wmono_trans; [exact WM| exact WM2]|]. split; [exact RT2|]. split; [exact RS2|].
split; [reflexivity|]. split; [exact REG|]. split; [exact TQ|]. split; [exact GQ|]. split; [exact CLS|]. split; [exact CI|]. split; [exact NX|].
split; [exact NR|]. split; [exact SPN|]. split; [exact MBP|]. split; [exact MBK|]. split; [exact MBC|]. split; [exact ZA|].
split.
{ unfold W_large. cbn [app]. eapply munch_chain; [eapply munch_weaken; [| exact MUs]; sub_fp_solve| exact MU2| unfold W_large; cbn [app]; sub_fp_solve]. }
split; [exact RSE2|]. split; [exact BODY|]. split; [exact HJ| exact FAS].
- destruct REST as (-> & -> & MU2 & RSE2).
assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
{ eapply rw_cells_transport; [exact FR| exact MU2| exact WM2|].
unfold W_large, LARGE_STACK. cbn [disjoint_from app]. simpl_sizes. unfold A_INSTANCE, ptrarr_lo, ptrarr_hi in *. lia. }
apply TAIL; [exact MI2| exact ST2| exact FR2|]. clear ST2; intros ST2.
apply evt_done. unfold combs_post. do 16 eexists.
split; [reflexivity|]. split; [reflexivity|]. split; [exact MI2|]. split; [exact ST2|].
split; [eapply wmono_trans; [exact WM| exact WM2]|]. split; [exact RT2|]. split; [exact RS2|].
split; [reflexivity|]. split; [reflexivity|]. split; [| exact RSE2].
unfold W_large. eapply munch_chain; [eapply munch_weaken; [| exact MUs]; sub_fp_solve| exact MU2| unfold W_large; sub_fp_solve].
Qed.
End S.
End Mq2.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBrp. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDM6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDM6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVsB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVsB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQwg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQwg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJBH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJBH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvG1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvG1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QyW2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyW2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsGW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsGW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qp4j.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qp4j. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDw3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUxU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUxU. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNwL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNwL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYnC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYnC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSsj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSsj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu1d.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu1d. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkfD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkfD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYyZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYyZ.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu3b.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmvA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmvA.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpME.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpME.Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVo2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVo2.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Local Notation atn := (at_nodeA L asegs).
Hypothesis large_alloc_spec : large_alloc_stmt RE X L.

Definition combs_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PStateA) (a : AState) (LB : list ablock) (lo n : Z) (m : mem)
(r : option Z * AState) (s' : PStateA) (ms' : machine_state) : Prop :=
exists (t0 t1 t2 a0 a1r a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 a0 a1r a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ s' = s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ wmono asegs m m' /\ RTconst RE X m' /\ RStats RE X m'
/\ match r with
| (None, a1) => a0 = wz 0 /\ a1 = a /\ munch ((bv_unsigned sp - 48, bv_unsigned sp) :: W_large (bv_unsigned sp - 48) RE X) m m' /\ RSec a LB RE X m'
| (Some mb, a1) =>
let msz := sec_map_size n in let sz := sec_size n in
a0 = wz (mb + kPage)
/\ as_reg a1 = as_reg a ++ [mkSec mb msz n]
/\ as_tq a1 = as_tq a /\ as_gq a1 = as_gq a /\ (forall c, cls a1 c = cls a c)
/\ as_cache_inited a1 = as_cache_inited a /\ as_next a1 = as_next a
/\ (as_nres a1 = as_nres a \/ as_nres a1 = as_nres a + kPtrArrBlock)
/\ as_spent a1 = as_spent a + sec_cost msz
/\ mb mod kPage = 0 /\ appr mb msz /\ mb + msz <= band_lo
/\ zavoids mb msz (avoid_of (ae_L RE) a) = true
/\ munch (((bv_unsigned sp - 48, bv_unsigned sp) :: W_large (bv_unsigned sp - 48) RE X) ++ [(mb, mb + msz); (SH mb, SH (mb + msz))]) m m'
/\ RSec a1 LB RE X m'
/\ rw_cells asegs m' (mb + kPage) [CB (Z.to_nat (msz - kPage)) (repeat (b8 0) (Z.to_nat (msz - kPage)))]
/\ hjunk m' (SH (mb + kPage)) (SH (mb + kPage + sz))
/\ rw_cells asegs m' (SH (mb + kPage + sz)) [CB (Z.to_nat ((msz - kPage - sz) / 8)) (fas ((msz - kPage - sz) / 8))]
end.

Lemma combined_sec_spec : forall ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (s : PStateA) (a : AState) (LB : list ablock) (FS : list fframe) (G : ghost) (n lo : Z),
gcons a LB FS G RE X -> avoid_covers RE X ->
RTconst RE X m -> RStats RE X m -> RSec a LB RE X m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - COMB_STACK ->
0 <= n <= 2^26 -> from_primary n = false ->
aimplT atn (large_alloc (ae_L RE) a n) s
(combs_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s a LB lo n m)
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz A_INSTANCE) (wz (rl_T X + 208)) (wz (sec_size n)) (wz 8) a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz combined_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros GC AC RT RS RSE MI ST CEIL LO Hn HP.
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof CEIL as CEIL'. idtac. unfold COMB_STACK in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
assert (HPN : ~ needed n <= kMaxSize) by (intros HH; apply (proj2 (from_primary_iff n)) in HH; rewrite HH in HP; discriminate). unfold kMaxSize in HPN.
pose proof (needed_facts n ltac:(lia)) as NF. pose proof (rz_size_range n) as [RZ1 RZ2].
assert (SS : 65537 <= sec_size n <= 2^26 + 4104) by (unfold sec_size; pose proof (round_up_ge (Z.max n 8) 8 ltac:(lia)); lia).
pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m) as MUs. pose proof (wmono_refl asegs m) as WM.
unfold combined_entry. apply aimplT_from_evt.
carve_frame 48%nat ST.
do 7 step.
step.
replace (v_sltiu (wz (sec_size n)) 1) with (wz 0) by (unfold v_sltiu; rewrite unsigned_lit by lia; change (bv_wrap 64 1) with 1; replace (sec_size n <? 1) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
step.
replace (sec_size n + 0) with (sec_size n) by lia.
step.
rewrite (unsigned_lit (sec_size n)), zb_lxor_ones by lia.
step. ifz.
stp. step. step. ifz.
stp. step. if_lit.
step. ifz.
step. step. step. step.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (RT0 : RTconst RE X mm) end.
{ eapply RTconst_munch; [exact RT| exact MUs| exact WM|]. constructor; [apply rt_avoid_stack; [exact RL| lia]| constructor]. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (RS0 : RStats RE X mm) end.
{ eapply RStats_munch; [exact RS| exact MUs| exact WM|]. constructor; [st_avoid_solve| constructor]. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (RSE0 : RSec a LB RE X mm) end.
{ eapply RSec_frame; [exact RSE| exact WM|]. eapply agree_on_of_munch; [exact MUs| exact WM|]. intros z Fz _. cbn [outside].
pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 4 right; left; exact Fz)). idtac. lia. }
apply evt_done.
eapply aimplT_then.
{ eapply large_alloc_spec; [exact GC| exact AC| exact RT0| exact RS0| exact RSE0| assumption| rewrite unsigned_lit by lia; exact ST| exact CEIL'| rewrite unsigned_lit by lia; unfold LARGE_STACK; lia| exact Hn| exact HP]. }
intros [r a1] s' ms' PO. unfold large_post in PO. rewrite !(unsigned_lit (bv_unsigned sp + -48)) in PO by lia.
destruct PO as (u0 & u1 & u2 & ra0 & ra1 & ra2 & ra3 & ra4 & ra5 & ra6 & ra7 & u3 & u4 & u5 & u6 & m2 & -> & -> & MI2 & ST2 & WM2 & RT2 & RS2 & REST).
replace (ret_pc (wz 276808)) with (wz 276808) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

assert (TAIL : forall mm (Q : machine_state -> Prop),
mem_inv asegs mm -> stk asegs mm lo (bv_unsigned sp + -48) ->
rw_cells asegs mm (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
(stk asegs mm lo (bv_unsigned sp) -> evt asegs Q (MS (mkR ra sp gp (wz A_TP) u0 u1 u2 s0 s1 ra0 (wz 9) ra2 (wz 8) ra4 ra5 ra6 ra7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
F (ret_pc ra) fc None mm (seg_rom asegs))) ->
evt asegs Q (MS (mkR (wz 276808) (wz (bv_unsigned sp + -48)) gp (wz A_TP) u0 u1 u2 (wz 8) s1 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
F (wz 276808) fc None mm (seg_rom asegs))).
{ intros mm Q MIm STm FRm K. step. stp. step. if_lit.
step.
do 6 step. step.
release_frame FRm STm (bv_unsigned sp).
step. apply K. exact STm. }
pose proof (rlay_prim_facts RE X RL) as (_ & _ & _ & _ & QK & QC & _). unfold ptrarr_hi in QC. idtac.
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (TA & TK & TB & TD & _). cbn [fst snd] in TA, TK, TB, TD. idtac.
destruct r as [mb|].
- destruct REST as (-> & REG & TQ & GQ & CLS & CI & NX & NR & SPN & MBP & MBK & MBC & ZA & MU2 & RSE2 & BODY & HJ & FAS).
pose proof MBC as MBC'. idtac.
assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
{ eapply rw_cells_transport; [exact FR| exact MU2| exact WM2|].
unfold W_large, LARGE_STACK. cbn [disjoint_from app]. simpl_sizes. unfold SH, A_SHADOW_OFS, A_INSTANCE in *.
unfold ptrarr_lo, ptrarr_hi in *. Z.div_mod_to_equations. (first [ clear - H39 q7 H34 q6 H33 H32 H31 H30 H29 q5 H5 H4 r0 MBC' TB TK QC QK q0 q MBK MBP r5 NX a1 mb RZ2 r6 RZ1 NF r7 HPN CEIL' LO lo n a sp X RE BAND; lia | lia ]). }
apply TAIL; [exact MI2| exact ST2| exact FR2|]. clear ST2; intros ST2.
apply evt_done. unfold combs_post. do 16 eexists.
split; [reflexivity|]. split; [reflexivity|]. split; [exact MI2|]. split; [exact ST2|].
split; [eapply wmono_trans; [exact WM| exact WM2]|]. split; [exact RT2|]. split; [exact RS2|].
split; [reflexivity|]. split; [exact REG|]. split; [exact TQ|]. split; [exact GQ|]. split; [exact CLS|]. split; [exact CI|]. split; [exact NX|].
split; [exact NR|]. split; [exact SPN|]. split; [exact MBP|]. split; [exact MBK|]. split; [exact MBC|]. split; [exact ZA|].
split.
{ unfold W_large. cbn [app]. eapply munch_chain; [eapply munch_weaken; [| exact MUs]; sub_fp_solve| exact MU2| unfold W_large; cbn [app]; sub_fp_solve]. }
split; [exact RSE2|]. split; [exact BODY|]. split; [exact HJ| exact FAS].
- destruct REST as (-> & -> & MU2 & RSE2).
assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
{ eapply rw_cells_transport; [exact FR| exact MU2| exact WM2|].
unfold W_large, LARGE_STACK. cbn [disjoint_from app]. simpl_sizes. unfold A_INSTANCE, ptrarr_lo, ptrarr_hi in *. lia. }
apply TAIL; [exact MI2| exact ST2| exact FR2|]. clear ST2; intros ST2.
apply evt_done. unfold combs_post. do 16 eexists.
split; [reflexivity|]. split; [reflexivity|]. split; [exact MI2|]. split; [exact ST2|].
split; [eapply wmono_trans; [exact WM| exact WM2]|]. split; [exact RT2|]. split; [exact RS2|].
split; [reflexivity|]. split; [reflexivity|]. split; [| exact RSE2].
unfold W_large. eapply munch_chain; [eapply munch_weaken; [| exact MUs]; sub_fp_solve| exact MU2| unfold W_large; sub_fp_solve].
Qed.
End S.
