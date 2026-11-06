(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27 Q13u QHig QvG1 QyW2 Qp4j QDw3 QNwL QYnC QSsj Qu1d QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qc27 Q13u QHig.
Import QvG1 QyW2 Qp4j QDw3 QNwL QYnC QSsj Qu1d.
Import QlES.
Import ListNotations. Local Ltac QoSL.solve_load ::= QsGW.mkr__solve_load_1.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Section S.
Context {BAND : Band}.

Lemma rt_replace_str : forall RE X m, RTconst RE X m -> ro_cells asegs m (0x0ed2f8 + 29) [C1 (b8 1)].
Proof. intros RE X m RT. rtc RT 71%nat K. exact K. Qed.

Lemma rt_got_memcpy : forall RE X m, RTconst RE X m -> ro_cells asegs m 0x0e5de0 [C8 (wz 0x0e7da8)].
Proof. intros RE X m RT. rtc RT 72%nat K. exact K. Qed.
End S.
End Mq0.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh QKTr QJBH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import Qc27 Q13u QHig.
Import Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 QDw3 QNwL QYnC QSsj.
Import QlES. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.

Definition rt_avoid (RE : aentry) (X : rlay) (iv : Z * Z) : Prop :=
forall x, fst iv <= x < snd iv -> ~ fp_RTconst RE X x.

Lemma RTconst_munch {BAND : Band} : forall RE X m m' W,
RTconst RE X m -> munch W m m' -> wmono asegs m m' -> Forall (rt_avoid RE X) W -> RTconst RE X m'.
Proof.
intros RE X m m' W RT MU WM FW. eapply RTconst_frame; [exact RT| exact WM|].
eapply agree_on_of_munch; [exact MU| exact WM|]. intros x Fx Hx. apply outside_intro.
intros lo hi Hin [H1 H2]. exact (proj1 (List.Forall_forall _ _) FW _ Hin x (conj H1 H2) Fx).
Qed.

Lemma rlay_prim_facts {BAND : Band} : forall RE X, rlay_ok RE X ->
prim_lo RE mod 0x10000 = 0 /\ KHI <= prim_lo RE /\ prim_hi RE <= band_lo
/\ ptrarr_lo RE mod 4096 = 0 /\ (lowhigh (ptrarr_lo RE) 0x800000 /\ off_hull (ptrarr_lo RE) 0x800000) /\ ptrarr_hi RE <= band_lo
/\ iv_disjoint (prim_lo RE, 2^37 + 0x1000) (ptrarr_lo RE, 0x800000).
Proof. intros RE X RL. destruct RL as (_ & _ & _ & _ & _ & P0 & P1 & P2 & Q0 & Q1 & Q2 & [D _] & _). exact (conj P0 (conj P1 (conj P2 (conj Q0 (conj Q1 (conj Q2 D)))))). Qed.

Lemma rlay_avoid {BAND : Band} : forall RE X, rlay_ok RE X -> avoid_covers RE X.
Proof. intros RE X RL. destruct RL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [_ AC] & _). exact AC. Qed.

Section Avoid.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).
Hypothesis RL : rlay_ok RE X.

Lemma rt_avoid_stack : forall lo hi, band_lo <= lo -> rt_avoid RE X (lo, hi).
Proof. intros lo hi H x [Hx _] Fx. cbn [fst] in Hx. pose proof (fp_RTconst_lt_ceil RE X x RL Fx). lia. Qed.

Lemma fp_RTconst_where : forall x, fp_RTconst RE X x ->
(0x10000 <= x < 0x645000) \/ exists o, In o (rlay_objs RE X) /\ in_iv o x.
Proof.
intros x [H|[H|[H|H]]].
- left. exact (proj1 (rtconst_img_ok x H)).
- right. exists (rl_T X, 0x1000). split; [apply T_obj|]. destruct H; split; cbn [fst snd] in *; lia.
- right. exists (rl_ctx X, 0x10000). split; [apply ctx_obj|]. destruct H; split; cbn [fst snd] in *; lia.
- right. exists (rl_dtls X, 0x1000). split; [apply dtls_obj|]. exact H.
Qed.

Lemma rt_avoid_gap : forall lo hi, 0x7fff7000 <= lo -> hi <= 0x10007fff8000 -> rt_avoid RE X (lo, hi).
Proof.
intros lo hi H1 H2 x [Hx1 Hx2] Fx. cbn [fst snd] in *.
destruct (fp_RTconst_where x Fx) as [L|(o & Ho & [O1 O2])]; [unfold kLowEnd in *; lia|].
pose proof (rlay_obj_facts RE X o RL Ho) as (_ & [K _] & _). unfold kLowEnd, KHI in *. lia.
Qed.

Lemma rt_avoid_prim : forall lo hi, prim_lo RE <= lo -> hi <= prim_hi RE -> rt_avoid RE X (lo, hi).
Proof.
intros lo hi H1 H2 x [Hx1 Hx2] Fx. cbn [fst snd] in *.
pose proof (rlay_prim_facts RE X RL) as (_ & PK & _). rewrite ?KHI_eq in PK.
destruct (fp_RTconst_where x Fx) as [L|(o & Ho & [O1 O2])]; [unfold prim_lo in *; lia|].
pose proof (rlay_obj_facts RE X o RL Ho) as (_ & _ & _ & D & _).
unfold iv_disjoint, prim_lo, prim_hi in *. cbn [fst snd] in D. lia.
Qed.

Lemma rt_avoid_ptrarr : forall lo hi, ptrarr_lo RE <= lo -> hi <= ptrarr_hi RE -> rt_avoid RE X (lo, hi).
Proof.
intros lo hi H1 H2 x [Hx1 Hx2] Fx. cbn [fst snd] in *.
pose proof (rlay_prim_facts RE X RL) as (_ & _ & _ & _ & PK & _). rewrite ?KHI_eq in PK.
destruct (fp_RTconst_where x Fx) as [L|(o & Ho & [O1 O2])]; [unfold ptrarr_lo, ptrarr_hi, iv_disjoint, a_ro_lo, a_data_hi, kLowEnd, KHI in *; cbn [fst snd] in *; lia|].
pose proof (rlay_obj_facts RE X o RL Ho) as (_ & _ & _ & _ & D).
unfold iv_disjoint, ptrarr_lo, ptrarr_hi in *. cbn [fst snd] in D. lia.
Qed.
End Avoid.

Definition st_avoid (iv : Z * Z) : Prop :=
forall x, fst iv <= x < snd iv -> ~ (A_ERRNO <= x < A_ERRNO + 4 \/ x = 0x171d60).

Lemma RStats_munch : forall RE X m m' W,
RStats RE X m -> munch W m m' -> wmono asegs m m' -> Forall st_avoid W -> RStats RE X m'.
Proof.
intros RE X m m' W (HJ & [e ERR] & [b OOM]) MU WM FW.
assert (AG : agree_on asegs (fun x => A_ERRNO <= x < A_ERRNO + 4 \/ x = 0x171d60) m m').
{ eapply agree_on_of_munch; [exact MU| exact WM|]. intros x Fx Hx. apply outside_intro.
intros lo hi Hin [H1 H2]. exact (proj1 (List.Forall_forall _ _) FW _ Hin x (conj H1 H2) Fx). }
split; [eapply hjunk_wmono; [exact HJ| exact WM]|]. split.
- exists e. eapply rw_cells_agree; [exact AG| exact ERR|]. intros z Hz. left. cbn [cells_size csize Nat.add] in Hz. lia.
- exists b. eapply rw_cells_agree; [exact AG| exact OOM|]. intros z Hz. right. cbn [cells_size csize Nat.add] in Hz. lia.
Qed.

Lemma st_avoid_high : forall lo hi, 0x171d61 <= lo -> hi <= A_ERRNO -> st_avoid (lo, hi).
Proof. intros lo hi H1 H2 x [Hx1 Hx2] [[K1 K2]|K]; cbn [fst snd] in *; unfold A_ERRNO in *; lia. Qed.
Lemma st_avoid_above : forall lo hi, A_ERRNO + 4 <= lo -> st_avoid (lo, hi).
Proof. intros lo hi H1 x [Hx1 Hx2] [[K1 K2]|K]; cbn [fst snd] in *; unfold A_ERRNO in *; lia. Qed.

Lemma hjunk_C8x2 : forall m a, hjunk m a (a + 16) -> exists w1 w2 : word, rw_cells asegs m a [C8 w1; C8 w2].
Proof.
intros m a HJ. destruct (hjunk_cells m a 16 HJ) as [junk RC].
assert (LEN : length junk = 16%nat) by (destruct RC as [[[WF _] _] _]; cbn in WF; lia).
exists (Z_to_bv 64 (bytes_le_to_Z (firstn 8 junk))), (Z_to_bv 64 (bytes_le_to_Z (skipn 8 junk))).
eapply rw_cells_recast'; [exact RC| cbn; tauto|].
cbn [cells_bytes cbytes app]. rewrite !le8_of_bytes by (rewrite ?length_take, ?length_drop; lia).
rewrite !app_nil_r. apply firstn_skipn.
Qed.

Lemma hjunk_C8 : forall m a, hjunk m a (a + 8) -> exists w : word, rw_cells asegs m a [C8 w].
Proof.
intros m a HJ. destruct (hjunk_cells m a 8 HJ) as [junk RC].
assert (LEN : length junk = 8%nat) by (destruct RC as [[[WF _] _] _]; cbn in WF; lia).
exists (Z_to_bv 64 (bytes_le_to_Z junk)).
eapply rw_cells_recast'; [exact RC| cbn; tauto|].
cbn [cells_bytes cbytes app]. rewrite le8_of_bytes by lia. reflexivity.
Qed.

Lemma RStats_mmap_words : forall RE X m, RStats RE X m ->
exists w1 w2 : word, rw_cells asegs m (rl_T X + 2872) [C8 w1; C8 w2].
Proof.
intros RE X m (HJ & _). apply hjunk_C8x2.
destruct (hjunk_split m _ (rl_T X + 2872) _ HJ ltac:(lia)) as [_ H2].
destruct (hjunk_split m _ (rl_T X + 2872 + 16) _ H2 ltac:(lia)) as [H3 _]. exact H3.
Qed.

Lemma rt_avoid_Thigh {BAND : Band} : forall RE X lo hi, rlay_ok RE X -> rl_T X + 80 <= lo -> hi <= rl_T X + 0x1000 -> rt_avoid RE X (lo, hi).
Proof.
intros RE X lo hi RL H1 H2 x [Hx1 Hx2] Fx. cbn [fst snd] in *.
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & _). cbn [fst snd] in TK. rewrite ?KHI_eq in TK.
destruct Fx as [H|[H|[H|H]]].
- pose proof (proj1 (rtconst_img_ok x H)). lia.
- destruct H as [A B]; cbn [fst snd] in A, B. lia.
- destruct H as [A B]; cbn [fst snd] in A, B.
assert (NE : (rl_T X, 0x1000) <> (rl_ctx X, 0x10000)) by (intros E; inversion E; lia).
destruct RL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PD).
pose proof (pairwise_disjoint_In _ _ _ PD (T_obj RE X) (ctx_obj RE X) NE) as D. unfold iv_disjoint in D; cbn [fst snd] in D. lia.
- destruct H as [A B]; cbn [fst snd] in A, B.
assert (NE : (rl_T X, 0x1000) <> (rl_dtls X, 0x1000)).
{ intros E. inversion E.
destruct RL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PD). cbn [rlay_objs pairwise_disjoint] in PD.
destruct PD as (F1 & _). pose proof (proj1 (List.Forall_forall _ _) F1 (rl_dtls X, 0x1000) ltac:(cbn; tauto)) as D.
unfold iv_disjoint in D; cbn [fst snd] in D. lia. }
destruct RL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PD).
pose proof (pairwise_disjoint_In _ _ _ PD (T_obj RE X) (dtls_obj RE X) NE) as D. unfold iv_disjoint in D; cbn [fst snd] in D. lia.
Qed.
End Mq1.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsGW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig.
Import Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj.
Import QlES.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition rpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(W : list (Z * Z)) (lo : Z) (m : word -> option byte) (K : word -> (word -> option byte) -> Prop) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch W m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ K a0 m'.

Lemma rlay_obj_facts {BAND : Band} : forall RE X o, rlay_ok RE X -> In o (rlay_objs RE X) ->
fst o mod 4096 = 0 /\ (lowhigh (fst o) (snd o) /\ off_hull (fst o) (snd o)) /\ fst o + snd o <= band_lo.
Proof.
intros RE X o RL Ho. destruct RL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F & _).
pose proof (proj1 (List.Forall_forall _ _) F o Ho) as (H1 & H2 & H3 & _). auto.
Qed.

Ltac obj_facts RL :=
let T := fresh "OT" in let C := fresh "OC" in let D := fresh "OD" in let N := fresh "ON" in
let S := fresh "OS" in let Fq := fresh "OF" in

pose proof (rlay_obj_facts_lia _ _ _ RL (T_obj _ _)) as T; pose proof (rlay_obj_facts_lia _ _ _ RL (ctx_obj _ _)) as C;
pose proof (rlay_obj_facts_lia _ _ _ RL (dtls_obj _ _)) as D; pose proof (rlay_obj_facts_lia _ _ _ RL (dn_obj _ _)) as N;
pose proof (rlay_obj_facts_lia _ _ _ RL (ssb_obj _ _)) as S; pose proof (rlay_obj_facts_lia _ _ _ RL (fs_obj _ _)) as Fq;
cbn [fst snd] in T, C, D, N, S, Fq; rewrite ?KHI_eq in T, C, D, N, S, Fq; unfold A_FS_MAP_SIZE in Fq.

Ltac lnorm :=
repeat match goal with
| |- context [sx32 (Z_to_bv 64 ?e)] => is_Zlit e; rewrite (sx32_small e) by lia
| |- context [zx32 (Z_to_bv 64 ?e)] => is_Zlit e; rewrite (zx32_small e) by lia
| |- context [zxb (Z_to_bv 8 ?e)] => is_Zlit e; rewrite (zxb_b8 e); let v := eval vm_compute in (e mod 256)%Z in change (e mod 256)%Z with v
| |- context [sxb (Z_to_bv 8 ?e)] => is_Zlit e; rewrite (sxb_b8 e) by lia
| |- context [Z.modulo ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.modulo a b) in change (Z.modulo a b) with v
| |- evt _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) => is_Zlit p; progress fold_closed_in_goal
| |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => progress fold_closed_in_goal
end.

Ltac istep := step; fix_lit_store; lnorm.

Ltac unsigned_lits :=
repeat match goal with
| |- context [bv_unsigned (Z_to_bv 64 ?e)] => first [ is_Zlit e; fail | rewrite (unsigned_lit e) by lia ]
end.
Ltac cond_u := unfold bv_eqb, bv_ltu, bv_leu; fold_lit_ux; unsigned_lits;
first [ reflexivity | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia | apply Z.leb_le; lia | apply Z.leb_gt; lia
| apply Z.eqb_eq; lia | apply Z.eqb_neq; lia
| apply (proj2 (Bool.negb_true_iff _)); first [apply Z.eqb_neq; lia | apply Z.ltb_ge; lia | apply Z.leb_gt; lia]
| apply (proj2 (Bool.negb_false_iff _)); first [apply Z.eqb_eq; lia | apply Z.ltb_lt; lia | apply Z.leb_le; lia] ].

Ltac unsigned_lits_in H :=
repeat match type of H with
| context [bv_unsigned (Z_to_bv 64 ?e)] => first [ is_Zlit e; fail | rewrite (unsigned_lit e) in H by lia ]
end.
Ltac post_call_u segs m :=
let ms' := fresh "ms'" in let PO := fresh "POST" in
intros ms' PO; cbv beta delta [rpost] in PO; hnf in PO; unsigned_lits_in PO;
destruct_exs PO;
let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
destruct PO as [E [MUc [WMc PO]]];
first [ destruct PO as [MIc PO] | rename PO into MIc ];
subst ms';
lazymatch type of MUc with
| munch _ m ?m' =>
transport_after_call segs m m' MUc WMc;
clear MUc WMc;
try match goal with H : mem_inv segs m |- _ => clear H end;
try clear m
end;
try destruct_ands PO;
repeat match goal with H : @eq (bv 64) ?v _ |- _ => is_var v; subst v end;
try (lazymatch goal with
| |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
end).
Tactic Notation "call_u" uconstr(SPEC) :=
lazymatch goal with
| |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | post_call_u segs m ]
end.

Ltac subst_words := repeat match goal with H : @eq (bv 64) ?v _ |- _ => is_var v; subst v end.

Ltac if_true_u :=
lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with true; [cbv iota| symmetry; cond_u] end.
Ltac if_false_u :=
lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false; [cbv iota| symmetry; cond_u] end.

Ltac step_until p :=
lazymatch goal with
| |- evt _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => first [ constr_eq q p | istep; step_until p ]
| _ => idtac
end.

Ltac small_offset k ::=
let b := eval vm_compute in (andb (Z.leb (-4096) k) (Z.ltb k 4096))%Z in
lazymatch b with true => idtac end. Ltac mkr__small_offset_1 k := let b := eval vm_compute in (andb (Z.leb (-4096) k) (Z.ltb k 4096))%Z in
lazymatch b with true => idtac end.

Definition rt_safe_iv {BAND : Band} (RE : aentry) (X : rlay) (iv : Z * Z) : Prop :=
band_lo <= fst iv
\/ (ae_fs_base RE <= fst iv /\ snd iv <= ae_fs_base RE + A_FS_MAP_SIZE)
\/ (SH (ae_fs_base RE) <= fst iv /\ snd iv <= SH (ae_fs_base RE + A_FS_MAP_SIZE))
\/ (0x1c19c8 <= fst iv /\ snd iv <= 0x6119f0)
\/ (rl_dn X <= fst iv /\ snd iv <= rl_dn X + 0x100000)
\/ (rl_ssb X <= fst iv /\ snd iv <= rl_ssb X + 0x800000)
\/ (rl_T X + 80 <= fst iv /\ snd iv <= rl_T X + 0x1000).

Lemma rtconst_img_bounds : forall x, in_ivs rtconst_img x -> x < 0x1c19c8 \/ (0x622e08 <= x < 0x645000).
Proof.
intros x (iv & Hin & [H1 H2]). unfold rtconst_img in Hin. cbn in Hin.
repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in H1, H2; unfold A_INSTANCE, A_TLS_TSD, A_TSD_MAIN, A_TP in *; lia|]). destruct Hin.
Qed.

Lemma rlay_pd {BAND : Band} : forall RE X, rlay_ok RE X -> pairwise_disjoint (rlay_objs RE X).
Proof. intros RE X RL. destruct RL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & P). exact P. Qed.

Tactic Notation "pd_pair" hyp(PD) integer(i) integer(k) ident(D) :=
pose proof PD as D; cbn [rlay_objs pairwise_disjoint] in D;
do i (apply proj2 in D); apply proj1 in D;
do k (apply Forall_inv_tail in D); apply Forall_inv in D;
unfold iv_disjoint in D; cbn [fst snd] in D; unfold A_FS_MAP_SIZE in D.

Lemma RTconst_safe {BAND : Band} : forall RE X m m' W,
RTconst RE X m -> rlay_ok RE X -> munch W m m' -> wmono asegs m m' ->
Forall (rt_safe_iv RE X) W -> RTconst RE X m'.
Proof.
intros RE X m m' W RT RL MU WM FW. eapply RTconst_frame; [exact RT| exact WM|].
eapply agree_on_of_munch; [exact MU| exact WM|]. intros x Fx Hx. apply outside_intro.
intros lo hi Hin [H1 H2]. pose proof (proj1 (List.Forall_forall _ _) FW _ Hin) as C. unfold rt_safe_iv in C. cbn [fst snd] in C.
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & T1 & T2). pose proof (rlay_obj_facts RE X _ RL (ctx_obj RE X)) as (_ & X1 & X2).
pose proof (rlay_obj_facts RE X _ RL (dtls_obj RE X)) as (_ & D1 & D2). pose proof (rlay_obj_facts RE X _ RL (fs_obj RE X)) as (_ & F1 & F2).
pose proof (rlay_obj_facts RE X _ RL (dn_obj RE X)) as (_ & N1 & N2). pose proof (rlay_obj_facts RE X _ RL (ssb_obj RE X)) as (_ & S1 & S2).
cbn [fst snd] in T1, T2, X1, X2, D1, D2, F1, F2, N1, N2, S1, S2.
idtac. rewrite ?KHI_eq in *. unfold A_FS_MAP_SIZE in *.
pose proof (rlay_pd RE X RL) as PD.

assert (SHlo : 0x7fff8000 <= SH (ae_fs_base RE)) by (rewrite SH_eq; Z.div_mod_to_equations; lia).
assert (SHhi : SH (ae_fs_base RE + 11571200) <= 0x10007fff8000) by (rewrite SH_eq; Z.div_mod_to_equations; lia).

rewrite !SH_eq in C.
destruct Fx as [Fimg|[FT|[FC|FD]]].
- pose proof (rtconst_img_bounds x Fimg) as IB. pose proof (proj1 (rtconst_img_ok x Fimg)) as IB2.
destruct C as [C|[C|[C|[C|[C|[C|C]]]]]].
+ clear -IB IB2 C H1. lia.
+ clear -IB IB2 C H1 H2 F1. lia.
+ clear -IB IB2 C H1 SHlo. rewrite SH_eq in SHlo. lia.
+ clear -IB IB2 C H1 H2. lia.
+ clear -IB IB2 C H1 H2 N1. lia.
+ clear -IB IB2 C H1 H2 S1. lia.
+ clear -IB IB2 C H1 H2 T1. lia.
- destruct FT as [FT1 FT2]. cbn [fst snd] in FT1, FT2.
pd_pair PD 0 4 DTF. pd_pair PD 0 1 DTN. pd_pair PD 0 2 DTS.
destruct C as [C|[C|[C|[C|[C|[C|C]]]]]].
+ clear -C FT1 FT2 H1 H2 T2. lia.
+ clear -C FT1 FT2 H1 H2 DTF. lia.
+ clear -C FT1 FT2 H1 H2 T1 SHlo SHhi. rewrite SH_eq in SHlo, SHhi. lia.
+ clear -C FT1 FT2 H1 H2 T1. lia.
+ clear -C FT1 FT2 H1 H2 DTN. lia.
+ clear -C FT1 FT2 H1 H2 DTS. lia.
+ clear -C FT1 FT2 H1 H2. lia.
- destruct FC as [FC1 FC2]. cbn [fst snd] in FC1, FC2.
pd_pair PD 1 3 DCF. pd_pair PD 1 0 DCN. pd_pair PD 1 1 DCS. pd_pair PD 0 0 DTC.
destruct C as [C|[C|[C|[C|[C|[C|C]]]]]].
+ clear -C FC1 FC2 H1 H2 X2. lia.
+ clear -C FC1 FC2 H1 H2 DCF. lia.
+ clear -C FC1 FC2 H1 H2 X1 SHlo SHhi. rewrite SH_eq in SHlo, SHhi. lia.
+ clear -C FC1 FC2 H1 H2 X1. lia.
+ clear -C FC1 FC2 H1 H2 DCN. lia.
+ clear -C FC1 FC2 H1 H2 DCS. lia.
+ clear -C FC1 FC2 H1 H2 DTC. lia.
- destruct FD as [FD1 FD2]. cbn [fst snd] in FD1, FD2.
pd_pair PD 4 0 DDF. pd_pair PD 2 1 DND. pd_pair PD 3 0 DSD. pd_pair PD 0 3 DTD.
destruct C as [C|[C|[C|[C|[C|[C|C]]]]]].
+ clear -C FD1 FD2 H1 H2 D2. lia.
+ clear -C FD1 FD2 H1 H2 DDF. lia.
+ clear -C FD1 FD2 H1 H2 D1 SHlo SHhi. rewrite SH_eq in SHlo, SHhi. lia.
+ clear -C FD1 FD2 H1 H2 D1. lia.
+ clear -C FD1 FD2 H1 H2 DND. lia.
+ clear -C FD1 FD2 H1 H2 DSD. lia.
+ clear -C FD1 FD2 H1 H2 DTD. lia.
Qed.

Ltac rt_safe_tac :=
repeat (apply Forall_cons || apply Forall_nil);
try (unfold rt_safe_iv; cbn [fst snd]; idtac; unfold A_FS_MAP_SIZE; lia).

Ltac rt_at RT RL mc H :=
lazymatch type of RT with RTconst ?RE ?X ?m0 =>
first [ constr_eq m0 mc; pose proof RT as H
| match goal with MU : munch ?W m0 mc, WM : wmono _ m0 mc |- _ =>
assert (H : RTconst RE X mc)
by (eapply (RTconst_safe RE X m0 mc W RT RL MU WM); unfold rt_safe_iv; rt_safe_tac) end ]
end.
Ltac rt_cur RT RL H :=
lazymatch goal with
| |- evt _ _ (MS _ _ _ _ _ ?mc _) => rt_at RT RL mc H
| |- RTconst _ _ ?mc => rt_at RT RL mc H
end.

Ltac rt_solve RT RL := let H := fresh "RTn" in rt_cur RT RL H; exact H.
Ltac rt_now RT RL k K := let H := fresh "RTn" in rt_cur RT RL H; rtc H k K; clear H.
Ltac rt_T_now RT RL K := let H := fresh "RTn" in rt_cur RT RL H; pose proof (RT_T _ _ _ H) as K; unfold rt_T_cells in K; clear H.
Ltac rt_ctx_now RT RL K := let H := fresh "RTn" in rt_cur RT RL H; pose proof (RT_ctx_thread _ _ _ H) as K; clear H.
Ltac rt_dtls_now RT RL K := let H := fresh "RTn" in rt_cur RT RL H; pose proof (RT_dtls _ _ _ H) as K; clear H.

End Mq2.
From Stdlib Require Permutation.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs QCiC QQwg QUxU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QDw3 QUxU QNwL QYnC QSsj.
Import QlES.
Import ListNotations. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section S.
Context {BAND : Band}.
Variable C : arun_components.
Hypothesis HRC : ac_RChunks C = RChunks.

Lemma ARUN_blk_slack : forall s LB FS RE m p A n, ARUN C s LB FS RE m -> In (p, A, n) LB ->
exists junk : list byte, bytes_at asegs m (A + n) junk /\ Z.of_nat (length junk) = (16 - n mod 16) mod 16.
Proof.
intros s LB FS RE m p A n AR Hin. destruct (ARUN_open C _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
destruct AX as (GC & R1 & R2 & R3 & R4 & _). rewrite HRC in R4. destruct R4 as [CR _].
assert (Hin0 : In (p, A, n) LB0) by (eapply Permutation_in; [exact PB| exact Hin]).
specialize (CR p A n Hin0).

assert (GEO : exists hi, hjunk m (A + n) hi /\ A mod 16 = 0 /\ hi mod 16 = 0 /\ A + n <= hi /\ 0 <= n).
{ destruct (gc_blocks _ _ _ _ _ _ GC p A n Hin0) as [(id & i & -> & Hn & HP & Ht & Hi & HA)|(mb & -> & Hn & HP & He & HA)]; cbn [chunk_rep] in CR.
- destruct CR as (_ & i' & Ht' & HA' & CM). destruct CM as (_ & _ & _ & HJ & _ & L16 & A16 & _ & _ & _ & _ & N0 & _).
pose proof (class_of_facts n Hn HP) as (Q1 & Q2 & Q3 & Q4 & _). cbv zeta in Q1, Q2, Q3, Q4.
exists (slot_beg RE (class_of n) i' + class_size (class_of n)). split; [exact HJ|]. split; [exact A16|].
split; [Z.div_mod_to_equations; lia|]. split; [| exact N0]. pose proof (rz_size_range n) as [Z1 Z2]. lia.
- destruct CR as (_ & He' & HA' & CM). destruct CM as (_ & _ & _ & HJ & _ & L16 & A16 & _ & _ & _ & _ & N0 & _).
pose proof (sec_map_size_ge n Hn HP) as [M1 M2].
pose proof (sec_entry_facts _ _ _ _ _ _ GC _ He') as SOK.
destruct SOK as (S1 & _). cbn [se_beg] in S1. pose proof kconsts as (_ & _ & _ & _ & KP & KU & _).
exists (mb + sec_map_size n). split; [exact HJ|]. split; [exact A16|].
split; [Z.div_mod_to_equations; lia|]. split; [| exact N0]. unfold kSecUserOff in *. lia. }
destruct GEO as (hi & HJ & A16 & H16 & LE & N0).
set (k := (16 - n mod 16) mod 16).
assert (K : 0 <= k < 16 /\ A + n + k <= hi) by (subst k; Z.div_mod_to_equations; lia).
destruct (hjunk_split m (A + n) (A + n + k) hi HJ ltac:(lia)) as [HJ1 _].
replace (A + n + k) with (A + n + Z.of_nat (Z.to_nat k)) in HJ1 by lia.
destruct (hjunk_cells m (A + n) (Z.to_nat k) HJ1) as [junk RC].
exists junk. destruct RC as [[WF BA] _]. cbn [cells_bytes cbytes app] in BA. rewrite app_nil_r in BA.
split; [exact BA|]. cbn [cells_wf cell_wf] in WF. destruct WF as [WF _]. rewrite WF. fold k. lia.
Qed.
End S.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig.
Import Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 QsGW QDw3 QUxU QNwL QYnC QSsj.
Import QlES. Local Ltac QsGW.small_offset k ::= QsGW.mkr__small_offset_0 k.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).

Definition asan_inited_entry : Z := 0x69bd0.
Definition try_asan_init_entry : Z := 0x6aae0.
Definition rss_limit_entry : Z := 0x6f9ac.
Definition may_return_null_entry : Z := 0x6f984.
Definition set_oom_entry : Z := 0x6f974.
Definition malloc_ctx_size_entry : Z := 0x6b868.
Definition get_current_pc_entry : Z := 0x8443c.
Definition can_poison_entry : Z := 0x64810.
Definition lsan_disabled_entry : Z := 0x90fb8.
Definition set_errno_entry : Z := 0x7d850.
Definition increase_total_mmap_entry : Z := 0x71654.
Definition run_malloc_hooks_entry : Z := 0x71bc8.

Section Leaves.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Local Notation REGS ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 :=
(mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).

Definition leaf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (K : word -> Prop) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom asegs)
/\ K a0.

Ltac leaf_finish := apply evt_done; unfold leaf_post; do 15 eexists; split; [reflexivity|].

Lemma asan_inited_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m,
RTconst RE X m -> mem_inv asegs m ->
evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m (fun a0' => a0' = wz 1))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz asan_inited_entry) fc None m (seg_rom asegs)).
Proof.
intros until m; intros RT MI. rtc RT 0%nat C0. unfold asan_inited_entry.
do 6 step. leaf_finish. reflexivity.
Qed.

Lemma rss_limit_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m,
RTconst RE X m -> mem_inv asegs m ->
evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m (fun a0' => a0' = wz 0))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz rss_limit_entry) fc None m (seg_rom asegs)).
Proof.
intros until m; intros RT MI. rtc RT 7%nat C7. unfold rss_limit_entry.
do 4 step. leaf_finish. reflexivity.
Qed.

Lemma may_return_null_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m,
RTconst RE X m -> mem_inv asegs m ->
evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m (fun a0' => a0' = wz 1))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz may_return_null_entry) fc None m (seg_rom asegs)).
Proof.
intros until m; intros RT MI. rtc RT 7%nat C7. unfold may_return_null_entry.
do 4 step. leaf_finish. reflexivity.
Qed.

Lemma malloc_ctx_size_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m,
RTconst RE X m -> mem_inv asegs m ->
evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m (fun a0' => a0' = wz 30))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz malloc_ctx_size_entry) fc None m (seg_rom asegs)).
Proof.
intros until m; intros RT MI. rtc RT 1%nat CC1. unfold malloc_ctx_size_entry.
do 4 step. leaf_finish. reflexivity.
Qed.

Lemma get_current_pc_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m,
evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m (fun a0' => a0' = ra))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz get_current_pc_entry) fc None m (seg_rom asegs)).
Proof.
intros. unfold get_current_pc_entry. do 2 step. leaf_finish. reflexivity.
Qed.

Lemma can_poison_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m,
RTconst RE X m -> mem_inv asegs m ->
evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m (fun a0' => a0' = wz 1))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz can_poison_entry) fc None m (seg_rom asegs)).
Proof.
intros until m; intros RT MI. rtc RT 2%nat CC2. unfold can_poison_entry.
do 5 step. leaf_finish. reflexivity.
Qed.

Lemma lsan_disabled_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m,
RTconst RE X m -> mem_inv asegs m ->
evt asegs (leaf_post ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m (fun a0' => a0' = wz 0))
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz lsan_disabled_entry) fc None m (seg_rom asegs)).
Proof.
intros until m; intros RT MI. rtc RT 21%nat C21. rtc RT 32%nat C32. unfold lsan_disabled_entry, A_TP in *.
do 6 step. leaf_finish. reflexivity.
Qed.

Lemma increase_total_mmap_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m,
RTconst RE X m -> mem_inv asegs m ->
evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m (fun _ => True))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz increase_total_mmap_entry) fc None m (seg_rom asegs)).
Proof.
intros until m; intros RT MI. rtc RT 19%nat C19. rtc RT 17%nat C17. unfold increase_total_mmap_entry in *.
do 4 step. if_true. step. leaf_finish. exact I.
Qed.

Definition leafw_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(W : list (Z * Z)) (lo : Z) (m : word -> option byte) (K : word -> (word -> option byte) -> Prop) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch W m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ K a0 m'.

Lemma try_asan_init_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m lo,
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 16 ->
evt asegs (leafw_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 16, bv_unsigned sp)] lo m
(fun a0' m' => a0' = wz 1 /\ RTconst RE X m'))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz try_asan_init_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros RT RL MI ST CEIL LO. pose proof CEIL as CEIL'. idtac. rtc RT 0%nat C0. unfold try_asan_init_entry.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
carve_frame 16%nat ST.
do 9 step. try if_false. do 4 step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold leafw_post. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [reflexivity|].
eapply RTconst_stack; [exact RT| exact RL| exact MU| exact WM|]. constructor; [cbn [fst]; lia| constructor].
Qed.

Lemma set_oom_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m lo,
RStats RE X m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> band_lo <= lo ->
evt asegs (leafw_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(0x171d60, 0x171d61)] lo m
(fun _ m' => RStats RE X m'))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz set_oom_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros RS MI ST CEIL. idtac. pose proof RS as (HJ & [e ERR] & [b OOM]). unfold set_oom_entry.
pose proof (munch_refl [(0x171d60, 0x171d61)] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold A_ERRNO in ERR.
step. step. step. step.
apply evt_done. unfold leafw_post. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
split; [eapply hjunk_wmono; [exact HJ| exact WM]|]. split; [exists e; exact ERR| eexists; exact OOM].
Qed.

Lemma set_errno_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m lo,
RStats RE X m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 16 ->
evt asegs (leafw_post ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
[(bv_unsigned sp - 16, bv_unsigned sp); (A_ERRNO, A_ERRNO + 4)] lo m
(fun _ m' => RStats RE X m'))
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz set_errno_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros RS MI ST CEIL LO. idtac. pose proof RS as (HJ & [e ERR] & [b OOM]).
unfold set_errno_entry, A_TP, A_ERRNO in *.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (6434236, 6434236 + 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
carve_frame 16%nat ST.
step. step. step.
step. step. step.
step. step.
step. step. step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold leafw_post. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
split; [eapply hjunk_wmono; [exact HJ| exact WM]|]. split; [eexists; exact ERR| eexists; exact OOM].
Qed.

Lemma run_malloc_hooks_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m lo,
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 32 ->
evt asegs (leafw_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 32, bv_unsigned sp)] lo m
(fun _ m' => RTconst RE X m'))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz run_malloc_hooks_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros RT RL MI ST CEIL LO. idtac. rtc RT 10%nat C10. unfold run_malloc_hooks_entry.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
carve_frame 32%nat ST.
do 7 step.
step. step.
step. step. step.
step. try if_true.
do 6 step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold leafw_post. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
eapply RTconst_stack; [exact RT| exact RL| exact MU| exact WM|]. constructor; [cbn [fst]; idtac; lia| constructor].
Qed.

End Leaves.
End Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg QTVW Q61C QWRO QFQR QmP7 QKBN QN4c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qc27 Q13u QHig.
Import QZzg QTVW Q61C QWRO QFQR QmP7 QKBN QN4c.
Import QlES.
Import ListNotations. Local Ltac QoSL.solve_load ::= QbcP_c1.mkr__solve_load_1. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Section S.
Context {BAND : Band}.

Lemma rt_replace_str : forall RE X m, RTconst RE X m -> ro_cells asegs m (0x0ef9b8 + 29) [C1 (b8 1)].
Proof. intros RE X m RT. rtc RT 71%nat K. exact K. Qed.

Lemma rt_got_memcpy : forall RE X m, RTconst RE X m -> ro_cells asegs m 0x0e81e0 [C8 (wz 0x0ea1c8)].
Proof. intros RE X m RT. rtc RT 72%nat K. exact K. Qed.
End S.
End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import Qc27 Q13u QHig.
Import Q6sh QKTr.
Import QJBH.
Import QZzg QTVW QWRO QFQR QmP7 QKBN.
Import QlES. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.

Definition rt_avoid (RE : aentry) (X : rlay) (iv : Z * Z) : Prop :=
forall x, fst iv <= x < snd iv -> ~ fp_RTconst RE X x.

Lemma RTconst_munch {BAND : Band} : forall RE X m m' W,
RTconst RE X m -> munch W m m' -> wmono asegs m m' -> Forall (rt_avoid RE X) W -> RTconst RE X m'.
Proof.
intros RE X m m' W RT MU WM FW. eapply RTconst_frame; [exact RT| exact WM|].
eapply agree_on_of_munch; [exact MU| exact WM|]. intros x Fx Hx. apply outside_intro.
intros lo hi Hin [H1 H2]. exact (proj1 (List.Forall_forall _ _) FW _ Hin x (conj H1 H2) Fx).
Qed.

Lemma rlay_prim_facts {BAND : Band} : forall RE X, rlay_ok RE X ->
prim_lo RE mod 0x10000 = 0 /\ KHI <= prim_lo RE /\ prim_hi RE <= band_lo
/\ ptrarr_lo RE mod 4096 = 0 /\ (lowhigh (ptrarr_lo RE) 0x800000 /\ off_hull (ptrarr_lo RE) 0x800000) /\ ptrarr_hi RE <= band_lo
/\ iv_disjoint (prim_lo RE, 2^37 + 0x1000) (ptrarr_lo RE, 0x800000).
Proof. intros RE X RL. destruct RL as (_ & _ & _ & _ & _ & P0 & P1 & P2 & Q0 & Q1 & Q2 & [D _] & _). exact (conj P0 (conj P1 (conj P2 (conj Q0 (conj Q1 (conj Q2 D)))))). Qed.

Lemma rlay_avoid {BAND : Band} : forall RE X, rlay_ok RE X -> avoid_covers RE X.
Proof. intros RE X RL. destruct RL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [_ AC] & _). exact AC. Qed.

Section Avoid.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).
Hypothesis RL : rlay_ok RE X.

Lemma rt_avoid_stack : forall lo hi, band_lo <= lo -> rt_avoid RE X (lo, hi).
Proof. intros lo hi H x [Hx _] Fx. cbn [fst] in Hx. pose proof (fp_RTconst_lt_ceil RE X x RL Fx). lia. Qed.

Lemma fp_RTconst_where : forall x, fp_RTconst RE X x ->
(0x10000 <= x < 0x647000) \/ exists o, In o (rlay_objs RE X) /\ in_iv o x.
Proof.
intros x [H|[H|[H|H]]].
- left. exact (proj1 (rtconst_img_ok x H)).
- right. exists (rl_T X, 0x1000). split; [apply T_obj|]. destruct H; split; cbn [fst snd] in *; lia.
- right. exists (rl_ctx X, 0x10000). split; [apply ctx_obj|]. destruct H; split; cbn [fst snd] in *; lia.
- right. exists (rl_dtls X, 0x1000). split; [apply dtls_obj|]. exact H.
Qed.

Lemma rt_avoid_gap : forall lo hi, 0x7fff7000 <= lo -> hi <= 0x10007fff8000 -> rt_avoid RE X (lo, hi).
Proof.
intros lo hi H1 H2 x [Hx1 Hx2] Fx. cbn [fst snd] in *.
destruct (fp_RTconst_where x Fx) as [L|(o & Ho & [O1 O2])]; [unfold kLowEnd in *; lia|].
pose proof (rlay_obj_facts RE X o RL Ho) as (_ & [K _] & _). unfold kLowEnd, KHI in *. lia.
Qed.

Lemma rt_avoid_prim : forall lo hi, prim_lo RE <= lo -> hi <= prim_hi RE -> rt_avoid RE X (lo, hi).
Proof.
intros lo hi H1 H2 x [Hx1 Hx2] Fx. cbn [fst snd] in *.
pose proof (rlay_prim_facts RE X RL) as (_ & PK & _). rewrite ?KHI_eq in PK.
destruct (fp_RTconst_where x Fx) as [L|(o & Ho & [O1 O2])]; [unfold prim_lo in *; lia|].
pose proof (rlay_obj_facts RE X o RL Ho) as (_ & _ & _ & D & _).
unfold iv_disjoint, prim_lo, prim_hi in *. cbn [fst snd] in D. lia.
Qed.

Lemma rt_avoid_ptrarr : forall lo hi, ptrarr_lo RE <= lo -> hi <= ptrarr_hi RE -> rt_avoid RE X (lo, hi).
Proof.
intros lo hi H1 H2 x [Hx1 Hx2] Fx. cbn [fst snd] in *.
pose proof (rlay_prim_facts RE X RL) as (_ & _ & _ & _ & PK & _). rewrite ?KHI_eq in PK.
destruct (fp_RTconst_where x Fx) as [L|(o & Ho & [O1 O2])]; [unfold ptrarr_lo, ptrarr_hi, iv_disjoint, a_ro_lo, a_data_hi, kLowEnd, KHI in *; cbn [fst snd] in *; lia|].
pose proof (rlay_obj_facts RE X o RL Ho) as (_ & _ & _ & _ & D).
unfold iv_disjoint, ptrarr_lo, ptrarr_hi in *. cbn [fst snd] in D. lia.
Qed.
End Avoid.

Definition st_avoid (iv : Z * Z) : Prop :=
forall x, fst iv <= x < snd iv -> ~ (A_ERRNO <= x < A_ERRNO + 4 \/ x = 0x174420).

Lemma RStats_munch : forall RE X m m' W,
RStats RE X m -> munch W m m' -> wmono asegs m m' -> Forall st_avoid W -> RStats RE X m'.
Proof.
intros RE X m m' W (HJ & [e ERR] & [b OOM]) MU WM FW.
assert (AG : agree_on asegs (fun x => A_ERRNO <= x < A_ERRNO + 4 \/ x = 0x174420) m m').
{ eapply agree_on_of_munch; [exact MU| exact WM|]. intros x Fx Hx. apply outside_intro.
intros lo hi Hin [H1 H2]. exact (proj1 (List.Forall_forall _ _) FW _ Hin x (conj H1 H2) Fx). }
split; [eapply hjunk_wmono; [exact HJ| exact WM]|]. split.
- exists e. eapply rw_cells_agree; [exact AG| exact ERR|]. intros z Hz. left. cbn [cells_size csize Nat.add] in Hz. lia.
- exists b. eapply rw_cells_agree; [exact AG| exact OOM|]. intros z Hz. right. cbn [cells_size csize Nat.add] in Hz. lia.
Qed.

Lemma st_avoid_high : forall lo hi, 0x174421 <= lo -> hi <= A_ERRNO -> st_avoid (lo, hi).
Proof. intros lo hi H1 H2 x [Hx1 Hx2] [[K1 K2]|K]; cbn [fst snd] in *; unfold A_ERRNO in *; lia. Qed.
Lemma st_avoid_above : forall lo hi, A_ERRNO + 4 <= lo -> st_avoid (lo, hi).
Proof. intros lo hi H1 x [Hx1 Hx2] [[K1 K2]|K]; cbn [fst snd] in *; unfold A_ERRNO in *; lia. Qed.

Lemma hjunk_C8x2 : forall m a, hjunk m a (a + 16) -> exists w1 w2 : word, rw_cells asegs m a [C8 w1; C8 w2].
Proof.
intros m a HJ. destruct (hjunk_cells m a 16 HJ) as [junk RC].
assert (LEN : length junk = 16%nat) by (destruct RC as [[[WF _] _] _]; cbn in WF; lia).
exists (Z_to_bv 64 (bytes_le_to_Z (firstn 8 junk))), (Z_to_bv 64 (bytes_le_to_Z (skipn 8 junk))).
eapply rw_cells_recast'; [exact RC| cbn; tauto|].
cbn [cells_bytes cbytes app]. rewrite !le8_of_bytes by (rewrite ?length_take, ?length_drop; lia).
rewrite !app_nil_r. apply firstn_skipn.
Qed.

Lemma hjunk_C8 : forall m a, hjunk m a (a + 8) -> exists w : word, rw_cells asegs m a [C8 w].
Proof.
intros m a HJ. destruct (hjunk_cells m a 8 HJ) as [junk RC].
assert (LEN : length junk = 8%nat) by (destruct RC as [[[WF _] _] _]; cbn in WF; lia).
exists (Z_to_bv 64 (bytes_le_to_Z junk)).
eapply rw_cells_recast'; [exact RC| cbn; tauto|].
cbn [cells_bytes cbytes app]. rewrite le8_of_bytes by lia. reflexivity.
Qed.

Lemma RStats_mmap_words : forall RE X m, RStats RE X m ->
exists w1 w2 : word, rw_cells asegs m (rl_T X + 2872) [C8 w1; C8 w2].
Proof.
intros RE X m (HJ & _). apply hjunk_C8x2.
destruct (hjunk_split m _ (rl_T X + 2872) _ HJ ltac:(lia)) as [_ H2].
destruct (hjunk_split m _ (rl_T X + 2872 + 16) _ H2 ltac:(lia)) as [H3 _]. exact H3.
Qed.

Lemma rt_avoid_Thigh {BAND : Band} : forall RE X lo hi, rlay_ok RE X -> rl_T X + 80 <= lo -> hi <= rl_T X + 0x1000 -> rt_avoid RE X (lo, hi).
Proof.
intros RE X lo hi RL H1 H2 x [Hx1 Hx2] Fx. cbn [fst snd] in *.
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & _). cbn [fst snd] in TK. rewrite ?KHI_eq in TK.
destruct Fx as [H|[H|[H|H]]].
- pose proof (proj1 (rtconst_img_ok x H)). lia.
- destruct H as [A B]; cbn [fst snd] in A, B. lia.
- destruct H as [A B]; cbn [fst snd] in A, B.
assert (NE : (rl_T X, 0x1000) <> (rl_ctx X, 0x10000)) by (intros E; inversion E; lia).
destruct RL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PD).
pose proof (pairwise_disjoint_In _ _ _ PD (T_obj RE X) (ctx_obj RE X) NE) as D. unfold iv_disjoint in D; cbn [fst snd] in D. lia.
- destruct H as [A B]; cbn [fst snd] in A, B.
assert (NE : (rl_T X, 0x1000) <> (rl_dtls X, 0x1000)).
{ intros E. inversion E.
destruct RL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PD). cbn [rlay_objs pairwise_disjoint] in PD.
destruct PD as (F1 & _). pose proof (proj1 (List.Forall_forall _ _) F1 (rl_dtls X, 0x1000) ltac:(cbn; tauto)) as D.
unfold iv_disjoint in D; cbn [fst snd] in D. lia. }
destruct RL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PD).
pose proof (pairwise_disjoint_In _ _ _ PD (T_obj RE X) (dtls_obj RE X) NE) as D. unfold iv_disjoint in D; cbn [fst snd] in D. lia.
Qed.
End Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu4g.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW Q61C QWRO Qu4g QFQR QmP7 QKBN.
Import QlES.
Import ListNotations. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section S.
Context {BAND : Band}.
Variable C : arun_components.
Hypothesis HRC : ac_RChunks C = RChunks.

Lemma ARUN_blk_slack : forall s LB FS RE m p A n, ARUN C s LB FS RE m -> In (p, A, n) LB ->
exists junk : list byte, bytes_at asegs m (A + n) junk /\ Z.of_nat (length junk) = (16 - n mod 16) mod 16.
Proof.
intros s LB FS RE m p A n AR Hin. destruct (ARUN_open C _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
destruct AX as (GC & R1 & R2 & R3 & R4 & _). rewrite HRC in R4. destruct R4 as [CR _].
assert (Hin0 : In (p, A, n) LB0) by (eapply Permutation_in; [exact PB| exact Hin]).
specialize (CR p A n Hin0).

assert (GEO : exists hi, hjunk m (A + n) hi /\ A mod 16 = 0 /\ hi mod 16 = 0 /\ A + n <= hi /\ 0 <= n).
{ destruct (gc_blocks _ _ _ _ _ _ GC p A n Hin0) as [(id & i & -> & Hn & HP & Ht & Hi & HA)|(mb & -> & Hn & HP & He & HA)]; cbn [chunk_rep] in CR.
- destruct CR as (_ & i' & Ht' & HA' & CM). destruct CM as (_ & _ & _ & HJ & _ & L16 & A16 & _ & _ & _ & _ & N0 & _).
pose proof (class_of_facts n Hn HP) as (Q1 & Q2 & Q3 & Q4 & _). cbv zeta in Q1, Q2, Q3, Q4.
exists (slot_beg RE (class_of n) i' + class_size (class_of n)). split; [exact HJ|]. split; [exact A16|].
split; [Z.div_mod_to_equations; lia|]. split; [| exact N0]. pose proof (rz_size_range n) as [Z1 Z2]. lia.
- destruct CR as (_ & He' & HA' & CM). destruct CM as (_ & _ & _ & HJ & _ & L16 & A16 & _ & _ & _ & _ & N0 & _).
pose proof (sec_map_size_ge n Hn HP) as [M1 M2].
pose proof (sec_entry_facts _ _ _ _ _ _ GC _ He') as SOK.
destruct SOK as (S1 & _). cbn [se_beg] in S1. pose proof kconsts as (_ & _ & _ & _ & KP & KU & _).
exists (mb + sec_map_size n). split; [exact HJ|]. split; [exact A16|].
split; [Z.div_mod_to_equations; lia|]. split; [| exact N0]. unfold kSecUserOff in *. lia. }
destruct GEO as (hi & HJ & A16 & H16 & LE & N0).
set (k := (16 - n mod 16) mod 16).
assert (K : 0 <= k < 16 /\ A + n + k <= hi) by (subst k; Z.div_mod_to_equations; lia).
destruct (hjunk_split m (A + n) (A + n + k) hi HJ ltac:(lia)) as [HJ1 _].
replace (A + n + k) with (A + n + Z.of_nat (Z.to_nat k)) in HJ1 by lia.
destruct (hjunk_cells m (A + n) (Z.to_nat k) HJ1) as [junk RC].
exists junk. destruct RC as [[WF BA] _]. cbn [cells_bytes cbytes app] in BA. rewrite app_nil_r in BA.
split; [exact BA|]. cbn [cells_wf cell_wf] in WF. destruct WF as [WF _]. rewrite WF. fold k. lia.
Qed.
End S.
End Mq7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbcP_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig.
Import Q6sh QKTr.
Import QJBH.
Import QZzg QTVW QbcP_c1 QWRO Qu4g QFQR QmP7 QKBN.
Import QlES. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).

Definition asan_inited_entry : Z := 0x69fa8.
Definition try_asan_init_entry : Z := 0x6aeb8.
Definition rss_limit_entry : Z := 0x6fd84.
Definition may_return_null_entry : Z := 0x6fd5c.
Definition set_oom_entry : Z := 0x6fd4c.
Definition malloc_ctx_size_entry : Z := 0x6bc40.
Definition get_current_pc_entry : Z := 0x84814.
Definition can_poison_entry : Z := 0x64be8.
Definition lsan_disabled_entry : Z := 0x91390.
Definition set_errno_entry : Z := 0x7dc28.
Definition increase_total_mmap_entry : Z := 0x71a2c.
Definition run_malloc_hooks_entry : Z := 0x71fa0.

Section Leaves.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Local Notation REGS ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 :=
(mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).

Definition leaf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (K : word -> Prop) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom asegs)
/\ K a0.

Ltac leaf_finish := apply evt_done; unfold leaf_post; do 15 eexists; split; [reflexivity|].

Lemma asan_inited_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m,
RTconst RE X m -> mem_inv asegs m ->
evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m (fun a0' => a0' = wz 1))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz asan_inited_entry) fc None m (seg_rom asegs)).
Proof.
intros until m; intros RT MI. rtc RT 0%nat C0. unfold asan_inited_entry.
do 6 step. leaf_finish. reflexivity.
Qed.

Lemma rss_limit_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m,
RTconst RE X m -> mem_inv asegs m ->
evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m (fun a0' => a0' = wz 0))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz rss_limit_entry) fc None m (seg_rom asegs)).
Proof.
intros until m; intros RT MI. rtc RT 7%nat C7. unfold rss_limit_entry.
do 4 step. leaf_finish. reflexivity.
Qed.

Lemma may_return_null_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m,
RTconst RE X m -> mem_inv asegs m ->
evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m (fun a0' => a0' = wz 1))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz may_return_null_entry) fc None m (seg_rom asegs)).
Proof.
intros until m; intros RT MI. rtc RT 7%nat C7. unfold may_return_null_entry.
do 4 step. leaf_finish. reflexivity.
Qed.

Lemma malloc_ctx_size_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m,
RTconst RE X m -> mem_inv asegs m ->
evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m (fun a0' => a0' = wz 30))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz malloc_ctx_size_entry) fc None m (seg_rom asegs)).
Proof.
intros until m; intros RT MI. rtc RT 1%nat CC1. unfold malloc_ctx_size_entry.
do 4 step. leaf_finish. reflexivity.
Qed.

Lemma get_current_pc_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m,
evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m (fun a0' => a0' = ra))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz get_current_pc_entry) fc None m (seg_rom asegs)).
Proof.
intros. unfold get_current_pc_entry. do 2 step. leaf_finish. reflexivity.
Qed.

Lemma can_poison_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m,
RTconst RE X m -> mem_inv asegs m ->
evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m (fun a0' => a0' = wz 1))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz can_poison_entry) fc None m (seg_rom asegs)).
Proof.
intros until m; intros RT MI. rtc RT 2%nat CC2. unfold can_poison_entry.
do 5 step. leaf_finish. reflexivity.
Qed.

Lemma lsan_disabled_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m,
RTconst RE X m -> mem_inv asegs m ->
evt asegs (leaf_post ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m (fun a0' => a0' = wz 0))
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz lsan_disabled_entry) fc None m (seg_rom asegs)).
Proof.
intros until m; intros RT MI. rtc RT 21%nat C21. rtc RT 32%nat C32. unfold lsan_disabled_entry, A_TP in *.
do 6 step. leaf_finish. reflexivity.
Qed.

Lemma increase_total_mmap_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m,
RTconst RE X m -> mem_inv asegs m ->
evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m (fun _ => True))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz increase_total_mmap_entry) fc None m (seg_rom asegs)).
Proof.
intros until m; intros RT MI. rtc RT 19%nat C19. rtc RT 17%nat C17. unfold increase_total_mmap_entry in *.
do 4 step. if_true. step. leaf_finish. exact I.
Qed.

Definition leafw_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(W : list (Z * Z)) (lo : Z) (m : word -> option byte) (K : word -> (word -> option byte) -> Prop) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch W m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ K a0 m'.

Lemma try_asan_init_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m lo,
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 16 ->
evt asegs (leafw_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 16, bv_unsigned sp)] lo m
(fun a0' m' => a0' = wz 1 /\ RTconst RE X m'))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz try_asan_init_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros RT RL MI ST CEIL LO. pose proof CEIL as CEIL'. idtac. rtc RT 0%nat C0. unfold try_asan_init_entry.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
carve_frame 16%nat ST.
do 9 step. try if_false. do 4 step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold leafw_post. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [reflexivity|].
eapply RTconst_stack; [exact RT| exact RL| exact MU| exact WM|]. constructor; [cbn [fst]; lia| constructor].
Qed.

Lemma set_oom_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m lo,
RStats RE X m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> band_lo <= lo ->
evt asegs (leafw_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(0x174420, 0x174421)] lo m
(fun _ m' => RStats RE X m'))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz set_oom_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros RS MI ST CEIL. idtac. pose proof RS as (HJ & [e ERR] & [b OOM]). unfold set_oom_entry.
pose proof (munch_refl [(0x174420, 0x174421)] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold A_ERRNO in ERR.
step. step. step. step.
apply evt_done. unfold leafw_post. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
split; [eapply hjunk_wmono; [exact HJ| exact WM]|]. split; [exists e; exact ERR| eexists; exact OOM].
Qed.

Lemma set_errno_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m lo,
RStats RE X m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 16 ->
evt asegs (leafw_post ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
[(bv_unsigned sp - 16, bv_unsigned sp); (A_ERRNO, A_ERRNO + 4)] lo m
(fun _ m' => RStats RE X m'))
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz set_errno_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros RS MI ST CEIL LO. idtac. pose proof RS as (HJ & [e ERR] & [b OOM]).
unfold set_errno_entry, A_TP, A_ERRNO in *.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (6444156, 6444156 + 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
carve_frame 16%nat ST.
step. step. step.
step. step. step.
step. step.
step. step. step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold leafw_post. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
split; [eapply hjunk_wmono; [exact HJ| exact WM]|]. split; [eexists; exact ERR| eexists; exact OOM].
Qed.

Lemma run_malloc_hooks_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m lo,
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 32 ->
evt asegs (leafw_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 32, bv_unsigned sp)] lo m
(fun _ m' => RTconst RE X m'))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz run_malloc_hooks_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros RT RL MI ST CEIL LO. idtac. rtc RT 10%nat C10. unfold run_malloc_hooks_entry.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
carve_frame 32%nat ST.
do 7 step.
step. step.
step. step. step.
step. try if_true.
do 6 step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold leafw_post. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
eapply RTconst_stack; [exact RT| exact RL| exact MU| exact WM|]. constructor; [cbn [fst]; idtac; lia| constructor].
Qed.

End Leaves.
End Mq8.

From Stdlib Require Import ZArith NArith List Lia Bool.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKBN.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition rpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(W : list (Z * Z)) (lo : Z) (m : word -> option byte) (K : word -> (word -> option byte) -> Prop) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch W m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ K a0 m'.

Lemma rlay_obj_facts {BAND : Band} : forall RE X o, rlay_ok RE X -> In o (rlay_objs RE X) ->
fst o mod 4096 = 0 /\ (lowhigh (fst o) (snd o) /\ off_hull (fst o) (snd o)) /\ fst o + snd o <= band_lo.
Proof.
intros RE X o RL Ho. destruct RL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F & _).
pose proof (proj1 (List.Forall_forall _ _) F o Ho) as (H1 & H2 & H3 & _). auto.
Qed.

Ltac obj_facts RL :=
let T := fresh "OT" in let C := fresh "OC" in let D := fresh "OD" in let N := fresh "ON" in
let S := fresh "OS" in let Fq := fresh "OF" in

pose proof (rlay_obj_facts_lia _ _ _ RL (T_obj _ _)) as T; pose proof (rlay_obj_facts_lia _ _ _ RL (ctx_obj _ _)) as C;
pose proof (rlay_obj_facts_lia _ _ _ RL (dtls_obj _ _)) as D; pose proof (rlay_obj_facts_lia _ _ _ RL (dn_obj _ _)) as N;
pose proof (rlay_obj_facts_lia _ _ _ RL (ssb_obj _ _)) as S; pose proof (rlay_obj_facts_lia _ _ _ RL (fs_obj _ _)) as Fq;
cbn [fst snd] in T, C, D, N, S, Fq; rewrite ?KHI_eq in T, C, D, N, S, Fq; unfold A_FS_MAP_SIZE in Fq.

Ltac lnorm :=
repeat match goal with
| |- context [sx32 (Z_to_bv 64 ?e)] => is_Zlit e; rewrite (sx32_small e) by lia
| |- context [zx32 (Z_to_bv 64 ?e)] => is_Zlit e; rewrite (zx32_small e) by lia
| |- context [zxb (Z_to_bv 8 ?e)] => is_Zlit e; rewrite (zxb_b8 e); let v := eval vm_compute in (e mod 256)%Z in change (e mod 256)%Z with v
| |- context [sxb (Z_to_bv 8 ?e)] => is_Zlit e; rewrite (sxb_b8 e) by lia
| |- context [Z.modulo ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.modulo a b) in change (Z.modulo a b) with v
| |- evt _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) => is_Zlit p; progress fold_closed_in_goal
| |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => progress fold_closed_in_goal
end.

Ltac istep := step; fix_lit_store; lnorm.

Ltac unsigned_lits :=
repeat match goal with
| |- context [bv_unsigned (Z_to_bv 64 ?e)] => first [ is_Zlit e; fail | rewrite (unsigned_lit e) by lia ]
end.
Ltac cond_u := unfold bv_eqb, bv_ltu, bv_leu; fold_lit_ux; unsigned_lits;
first [ reflexivity | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia | apply Z.leb_le; lia | apply Z.leb_gt; lia
| apply Z.eqb_eq; lia | apply Z.eqb_neq; lia
| apply (proj2 (Bool.negb_true_iff _)); first [apply Z.eqb_neq; lia | apply Z.ltb_ge; lia | apply Z.leb_gt; lia]
| apply (proj2 (Bool.negb_false_iff _)); first [apply Z.eqb_eq; lia | apply Z.ltb_lt; lia | apply Z.leb_le; lia] ].

Ltac unsigned_lits_in H :=
repeat match type of H with
| context [bv_unsigned (Z_to_bv 64 ?e)] => first [ is_Zlit e; fail | rewrite (unsigned_lit e) in H by lia ]
end.
Ltac post_call_u segs m :=
let ms' := fresh "ms'" in let PO := fresh "POST" in
intros ms' PO; cbv beta delta [rpost] in PO; hnf in PO; unsigned_lits_in PO;
destruct_exs PO;
let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
destruct PO as [E [MUc [WMc PO]]];
first [ destruct PO as [MIc PO] | rename PO into MIc ];
subst ms';
lazymatch type of MUc with
| munch _ m ?m' =>
transport_after_call segs m m' MUc WMc;
clear MUc WMc;
try match goal with H : mem_inv segs m |- _ => clear H end;
try clear m
end;
try destruct_ands PO;
repeat match goal with H : @eq (bv 64) ?v _ |- _ => is_var v; subst v end;
try (lazymatch goal with
| |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
end).
Tactic Notation "call_u" uconstr(SPEC) :=
lazymatch goal with
| |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | post_call_u segs m ]
end.

Ltac subst_words := repeat match goal with H : @eq (bv 64) ?v _ |- _ => is_var v; subst v end.

Ltac if_true_u :=
lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with true; [cbv iota| symmetry; cond_u] end.
Ltac if_false_u :=
lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false; [cbv iota| symmetry; cond_u] end.

Ltac step_until p :=
lazymatch goal with
| |- evt _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => first [ constr_eq q p | istep; step_until p ]
| _ => idtac
end.

Ltac small_offset k ::=
let b := eval vm_compute in (andb (Z.leb (-4096) k) (Z.ltb k 4096))%Z in
lazymatch b with true => idtac end. Ltac mkr__small_offset_1 k := let b := eval vm_compute in (andb (Z.leb (-4096) k) (Z.ltb k 4096))%Z in
lazymatch b with true => idtac end.

Definition rt_safe_iv {BAND : Band} (RE : aentry) (X : rlay) (iv : Z * Z) : Prop :=
band_lo <= fst iv
\/ (ae_fs_base RE <= fst iv /\ snd iv <= ae_fs_base RE + A_FS_MAP_SIZE)
\/ (SH (ae_fs_base RE) <= fst iv /\ snd iv <= SH (ae_fs_base RE + A_FS_MAP_SIZE))
\/ (0x1c4088 <= fst iv /\ snd iv <= 0x6140b0)
\/ (rl_dn X <= fst iv /\ snd iv <= rl_dn X + 0x100000)
\/ (rl_ssb X <= fst iv /\ snd iv <= rl_ssb X + 0x800000)
\/ (rl_T X + 80 <= fst iv /\ snd iv <= rl_T X + 0x1000).

Lemma rtconst_img_bounds : forall x, in_ivs rtconst_img x -> x < 0x1c4088 \/ (0x6254c8 <= x < 0x647000).
Proof.
intros x (iv & Hin & [H1 H2]). unfold rtconst_img in Hin. cbn in Hin.
repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in H1, H2; unfold A_INSTANCE, A_TLS_TSD, A_TSD_MAIN, A_TP in *; lia|]). destruct Hin.
Qed.

Lemma rlay_pd {BAND : Band} : forall RE X, rlay_ok RE X -> pairwise_disjoint (rlay_objs RE X).
Proof. intros RE X RL. destruct RL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & P). exact P. Qed.

Tactic Notation "pd_pair" hyp(PD) integer(i) integer(k) ident(D) :=
pose proof PD as D; cbn [rlay_objs pairwise_disjoint] in D;
do i (apply proj2 in D); apply proj1 in D;
do k (apply Forall_inv_tail in D); apply Forall_inv in D;
unfold iv_disjoint in D; cbn [fst snd] in D; unfold A_FS_MAP_SIZE in D.

Lemma RTconst_safe {BAND : Band} : forall RE X m m' W,
RTconst RE X m -> rlay_ok RE X -> munch W m m' -> wmono asegs m m' ->
Forall (rt_safe_iv RE X) W -> RTconst RE X m'.
Proof.
intros RE X m m' W RT RL MU WM FW. eapply RTconst_frame; [exact RT| exact WM|].
eapply agree_on_of_munch; [exact MU| exact WM|]. intros x Fx Hx. apply outside_intro.
intros lo hi Hin [H1 H2]. pose proof (proj1 (List.Forall_forall _ _) FW _ Hin) as C. unfold rt_safe_iv in C. cbn [fst snd] in C.
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & T1 & T2). pose proof (rlay_obj_facts RE X _ RL (ctx_obj RE X)) as (_ & X1 & X2).
pose proof (rlay_obj_facts RE X _ RL (dtls_obj RE X)) as (_ & D1 & D2). pose proof (rlay_obj_facts RE X _ RL (fs_obj RE X)) as (_ & F1 & F2).
pose proof (rlay_obj_facts RE X _ RL (dn_obj RE X)) as (_ & N1 & N2). pose proof (rlay_obj_facts RE X _ RL (ssb_obj RE X)) as (_ & S1 & S2).
cbn [fst snd] in T1, T2, X1, X2, D1, D2, F1, F2, N1, N2, S1, S2.
idtac. rewrite ?KHI_eq in *. unfold A_FS_MAP_SIZE in *.
pose proof (rlay_pd RE X RL) as PD.

assert (SHlo : 0x7fff8000 <= SH (ae_fs_base RE)) by (rewrite SH_eq; Z.div_mod_to_equations; lia).
assert (SHhi : SH (ae_fs_base RE + 11571200) <= 0x10007fff8000) by (rewrite SH_eq; Z.div_mod_to_equations; lia).

rewrite !SH_eq in C.
destruct Fx as [Fimg|[FT|[FC|FD]]].
- pose proof (rtconst_img_bounds x Fimg) as IB. pose proof (proj1 (rtconst_img_ok x Fimg)) as IB2.
destruct C as [C|[C|[C|[C|[C|[C|C]]]]]].
+ clear -IB IB2 C H1. lia.
+ clear -IB IB2 C H1 H2 F1. lia.
+ clear -IB IB2 C H1 SHlo. rewrite SH_eq in SHlo. lia.
+ clear -IB IB2 C H1 H2. lia.
+ clear -IB IB2 C H1 H2 N1. lia.
+ clear -IB IB2 C H1 H2 S1. lia.
+ clear -IB IB2 C H1 H2 T1. lia.
- destruct FT as [FT1 FT2]. cbn [fst snd] in FT1, FT2.
pd_pair PD 0 4 DTF. pd_pair PD 0 1 DTN. pd_pair PD 0 2 DTS.
destruct C as [C|[C|[C|[C|[C|[C|C]]]]]].
+ clear -C FT1 FT2 H1 H2 T2. lia.
+ clear -C FT1 FT2 H1 H2 DTF. lia.
+ clear -C FT1 FT2 H1 H2 T1 SHlo SHhi. rewrite SH_eq in SHlo, SHhi. lia.
+ clear -C FT1 FT2 H1 H2 T1. lia.
+ clear -C FT1 FT2 H1 H2 DTN. lia.
+ clear -C FT1 FT2 H1 H2 DTS. lia.
+ clear -C FT1 FT2 H1 H2. lia.
- destruct FC as [FC1 FC2]. cbn [fst snd] in FC1, FC2.
pd_pair PD 1 3 DCF. pd_pair PD 1 0 DCN. pd_pair PD 1 1 DCS. pd_pair PD 0 0 DTC.
destruct C as [C|[C|[C|[C|[C|[C|C]]]]]].
+ clear -C FC1 FC2 H1 H2 X2. lia.
+ clear -C FC1 FC2 H1 H2 DCF. lia.
+ clear -C FC1 FC2 H1 H2 X1 SHlo SHhi. rewrite SH_eq in SHlo, SHhi. lia.
+ clear -C FC1 FC2 H1 H2 X1. lia.
+ clear -C FC1 FC2 H1 H2 DCN. lia.
+ clear -C FC1 FC2 H1 H2 DCS. lia.
+ clear -C FC1 FC2 H1 H2 DTC. lia.
- destruct FD as [FD1 FD2]. cbn [fst snd] in FD1, FD2.
pd_pair PD 4 0 DDF. pd_pair PD 2 1 DND. pd_pair PD 3 0 DSD. pd_pair PD 0 3 DTD.
destruct C as [C|[C|[C|[C|[C|[C|C]]]]]].
+ clear -C FD1 FD2 H1 H2 D2. lia.
+ clear -C FD1 FD2 H1 H2 DDF. lia.
+ clear -C FD1 FD2 H1 H2 D1 SHlo SHhi. rewrite SH_eq in SHlo, SHhi. lia.
+ clear -C FD1 FD2 H1 H2 D1. lia.
+ clear -C FD1 FD2 H1 H2 DND. lia.
+ clear -C FD1 FD2 H1 H2 DSD. lia.
+ clear -C FD1 FD2 H1 H2 DTD. lia.
Qed.

Ltac rt_safe_tac :=
repeat (apply Forall_cons || apply Forall_nil);
try (unfold rt_safe_iv; cbn [fst snd]; idtac; unfold A_FS_MAP_SIZE; lia).

Ltac rt_at RT RL mc H :=
lazymatch type of RT with RTconst ?RE ?X ?m0 =>
first [ constr_eq m0 mc; pose proof RT as H
| match goal with MU : munch ?W m0 mc, WM : wmono _ m0 mc |- _ =>
assert (H : RTconst RE X mc)
by (eapply (RTconst_safe RE X m0 mc W RT RL MU WM); unfold rt_safe_iv; rt_safe_tac) end ]
end.
Ltac rt_cur RT RL H :=
lazymatch goal with
| |- evt _ _ (MS _ _ _ _ _ ?mc _) => rt_at RT RL mc H
| |- RTconst _ _ ?mc => rt_at RT RL mc H
end.

Ltac rt_solve RT RL := let H := fresh "RTn" in rt_cur RT RL H; exact H.
Ltac rt_now RT RL k K := let H := fresh "RTn" in rt_cur RT RL H; rtc H k K; clear H.
Ltac rt_T_now RT RL K := let H := fresh "RTn" in rt_cur RT RL H; pose proof (RT_T _ _ _ H) as K; unfold rt_T_cells in K; clear H.
Ltac rt_ctx_now RT RL K := let H := fresh "RTn" in rt_cur RT RL H; pose proof (RT_ctx_thread _ _ _ H) as K; clear H.
Ltac rt_dtls_now RT RL K := let H := fresh "RTn" in rt_cur RT RL H; pose proof (RT_dtls _ _ _ H) as K; clear H.

