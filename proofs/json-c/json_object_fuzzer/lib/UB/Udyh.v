(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsjA QEpW QZDE QbVh QlEo QWxq QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH QHnV QCcH QfLs Q0Ek Qtgi QjDH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7 QkMG. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UG8z UPZI. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QsjA QEpW QZDE QbVh QlEo QWxq QXup.
Import UEQM.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0.
Import UC8c.Mq0.
Import Qsw7 QkMG.
Import UG8z UPZI.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section Inv.
Variable HIx : heap_iface S4L.

Definition PE_BASE (pf : pe_fix) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (LBall : list blk) (errv : word) : Prop :=
HEAP S4L HIx A LBall m md /\
stk rsegs m lo (pf_spf pf) /\
rw_cells rsegs m (0x77c00 - 164) [C4 errv] /\
bytes_at rsegs m (pf_sb pf) payload /\ Z.of_nat (length payload) = pf_len pf /\
(pf_len pf = 0 \/ payload_loc pf LB0) /\
heap_presx S4L s4_volatile LB0 (pf_spf pf + PE_FRAME) me m /\
model_vm_only (pf_md pf) md /\
jc_glob_P m.

#[using="Type"] Lemma PE_REST_base : forall pf q LB0 payload me lo m md A ts errv,
PE_REST HIx pf q LB0 payload me lo m md A ts errv ->
PE_BASE pf LB0 payload me lo m md A (pe_blocks pf q LB0 ts) errv /\
(forall i l, nth_error (t_levels ts) i = Some l -> lvl_cur rsegs S4F m (t_depth ts) i l) /\
(if zin (cur_st ts) [ST_array_add; ST_ovadd] then jopt rsegs S4F (t_objs ts) m (t_objbs ts) (t_obj ts) else t_objbs ts = []).
Proof.
intros until errv. intros (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & JCG).
split; [| split; [exact LV | exact OBJ]].
split; [exact HP|]. split; [exact ST|]. split; [exact ERR|]. split; [exact STR|]. split; [exact PLEN|]. split; [exact SBin | split; [exact HPR | split; [exact MDV | exact JCG]]].
Qed.

#[using="Type"] Lemma PE_REST_of_base : forall pf q LB0 payload me lo m md A ts errv,
PE_BASE pf LB0 payload me lo m md A (pe_blocks pf q LB0 ts) errv ->
(forall i l, nth_error (t_levels ts) i = Some l -> lvl_cur rsegs S4F m (t_depth ts) i l) ->
(if zin (cur_st ts) [ST_array_add; ST_ovadd] then jopt rsegs S4F (t_objs ts) m (t_objbs ts) (t_obj ts) else t_objbs ts = []) ->
PE_REST HIx pf q LB0 payload me lo m md A ts errv.
Proof.
intros until errv. intros (HP & ST & ERR & STR & PLEN & SBin & HPR & MDV & JCG) LV OBJ.
split; [exact HP|]. split; [exact LV|]. split; [exact OBJ|].
split; [exact ST|]. split; [exact ERR|]. split; [exact STR|]. split; [exact PLEN|]. split; [exact SBin | split; [exact HPR | split; [exact MDV | exact JCG]]].
Qed.

#[using="Type"] Lemma PE_BASE_perm : forall pf LB0 payload me lo m md A LBall LBall' errv,
PE_BASE pf LB0 payload me lo m md A LBall errv -> Permutation LBall LBall' ->
PE_BASE pf LB0 payload me lo m md A LBall' errv.
Proof.
intros until errv. intros (HP & REST) HPm. split; [| exact REST]. eapply heap_perm; [exact HP | exact HPm].
Qed.

Definition base_w (pf : pe_fix) (LB0 LBall : list blk) (iv : Z * Z) : Prop :=
(exists a n, In (a, n) LBall /\ (forall k, ~ In (a, k) LB0) /\ a <= fst iv /\ snd iv <= a + n) \/
(pf_spf pf <= fst iv /\ snd iv <= pf_spf pf + PE_FRAME).

#[using="Type"] Lemma PE_BASE_write : forall pf LB0 payload me lo m m' md A LBall errv W,
PE_STATIC HIx pf lo ->
PE_BASE pf LB0 payload me lo m md A LBall errv ->
incl LB0 LBall ->
munch W m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
Forall (base_w pf LB0 LBall) W ->
PE_BASE pf LB0 payload me lo m' md A LBall errv.
Proof.
intros until W. intros STC (HP & ST & ERR & STR & PLEN & SBin & HPR & MDV & JCG) Hincl MU WM MI HW.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL). unfold alloc_ceiling, sp_window_lo, stack_max_size in LO.
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND.
split; [| split; [| split; [| split; [| split; [exact PLEN | split; [exact SBin | split; [| split; [exact MDV |]]]]]]]].
- eapply (heap_frame S4L HIx); [exact HP | | exact WM | exact MI].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU).
eapply Forall_impl; [| exact HW]. intros [lo' hi'] Hiv. unfold base_w in Hiv. cbn [fst snd] in *.
destruct Hiv as [(b & k & Hb & _ & H1) | H1].
+ right; left. exists b, k. split; [exact Hb | lia].
+ left. unfold PE_FRAME, alloc_ceiling, sp_window_lo, stack_max_size in *. lia.
- eapply (stk_transport_disjoint rsegs); [exact ST | exact MU | exact WM |].
destruct ST as (ST0 & ST1 & _).
clear - HW LOS LO ST0 ST1 HP. induction W as [|[lo' hi'] W IH]; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. unfold base_w in H1. cbn [disjoint_from fst snd] in *. split; [| apply IH; exact HW].
destruct H1 as [(b & k & Hb & _ & H1) | H1]; [| lia].
pose proof (heap_blk S4L HIx _ _ _ _ _ _ HP Hb) as (_ & _ & _ & Hbhi & _). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hbhi. lia.
- eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]. cbn [cells_size csize Z.of_nat].
clear - HW LOS LO HP SP0. induction W as [|[lo' hi'] W IH]; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. unfold base_w in H1. cbn [disjoint_from fst snd] in *. split; [| apply IH; exact HW].
destruct H1 as [(b & k & Hb & _ & H1) | H1]; [| lia].
pose proof (heap_blk_img S4L HIx _ _ _ _ _ _ HP Hb) as Hbi. cbn [hl_img_lo hl_img_hi S4L] in Hbi.
pose proof (heap_blk S4L HIx _ _ _ _ _ _ HP Hb) as (Hk0 & _). lia.
- eapply payload_transport; [exact STC | exact HP | exact Hincl | exact STR | exact PLEN | exact SBin | exact MU |].
eapply Forall_impl; [| exact HW]. intros [lo' hi'] Hiv. unfold base_w in Hiv. unfold payload_safe. cbn [fst snd] in *.
destruct Hiv as [(b & k & Hb & Hnot & H1) | H1].
+ right; left. exists b, k. split; [exact Hb|]. split; [exact Hnot | lia].
+ left. unfold alloc_ceiling, sp_window_lo, stack_max_size in *. lia.
- eapply heap_presx_trans; [exact HPR|].
eapply (heap_presx_of_munch S4L s4_volatile LB0); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | exact Hincl | unfold PE_FRAME, alloc_ceiling, sp_window_lo, stack_max_size; lia |].
eapply Forall_impl; [| exact HW]. intros [lo' hi'] Hiv. unfold base_w in Hiv. cbn [fst snd] in *.
destruct Hiv as [(b & k & Hb & Hnot & H1) | H1].
+ right; left. exists b, k. split; [exact Hb|]. split; [exact (Hnot k) | lia].
+ left. unfold PE_FRAME, alloc_ceiling, sp_window_lo, stack_max_size in *. lia.
-
eapply jc_glob_P_outside; [exact JCG | exact MU | exact WM |].
eapply Forall_impl; [| exact HW]. intros [lo' hi'] Hiv. unfold base_w in Hiv. cbn [fst snd] in *.
destruct Hiv as [(b & k & Hb & Hnot & H1) | H1].
+ pose proof (heap_blk_img S4L HIx _ _ _ _ b k HP Hb) as Hbi. cbn [hl_img_lo hl_img_hi S4L] in Hbi. lia.
+ unfold PE_FRAME, alloc_ceiling, sp_window_lo, stack_max_size in *. lia.
Qed.

#[using="Type"] Lemma PE_BASE_callx : forall pf LB0 payload me lo m1 m2 md md2 A A2 LBall LBall2 LBc errv errv2,
PE_BASE pf LB0 payload me lo m1 md A LBall errv ->
heap_presx S4L s4_volatile LBc (pf_spf pf) m1 m2 -> incl LB0 LBc ->
model_vm_only md md2 -> jc_glob_P m2 ->
HEAP S4L HIx A2 LBall2 m2 md2 ->
stk rsegs m2 lo (pf_spf pf) ->
rw_cells rsegs m2 (0x77c00 - 164) [C4 errv2] ->
PE_BASE pf LB0 payload me lo m2 md2 A2 LBall2 errv2.
Proof.
intros until errv2. intros (HP & ST & ERR & STR & PLEN & SBin & HPR & MDV & JCG) HPRc Hincl VM12 JCG2 HP2 ST2 ERR2.
split; [exact HP2|]. split; [exact ST2|]. split; [exact ERR2|]. split; [| split; [exact PLEN | split; [exact SBin | split; [| split; [eapply model_vm_only_trans; [exact MDV | exact VM12] | exact JCG2]]]]].
- eapply payload_presx; [exact HPRc | exact Hincl | unfold PE_FRAME; lia | exact STR | exact PLEN | exact SBin].
- eapply heap_presx_trans; [exact HPR|]. eapply heap_presx_weaken; [exact HPRc | unfold PE_FRAME; lia | exact Hincl | intros a Xa; exact Xa].
Qed.

#[using="Type"] Lemma PE_BASE_call : forall pf LB0 payload me lo m1 m2 md md2 A A2 LBall LBall2 LBc errv errv2,
PE_BASE pf LB0 payload me lo m1 md A LBall errv ->
heap_pres S4L LBc (pf_spf pf) m1 m2 -> incl LB0 LBc ->
model_vm_only md md2 ->
HEAP S4L HIx A2 LBall2 m2 md2 ->
stk rsegs m2 lo (pf_spf pf) ->
rw_cells rsegs m2 (0x77c00 - 164) [C4 errv2] ->
PE_BASE pf LB0 payload me lo m2 md2 A2 LBall2 errv2.
Proof.
intros until errv2. intros B HPRc Hincl VM12 HP2 ST2 ERR2. eapply PE_BASE_callx; try eassumption.
- apply heap_pres_presx. exact HPRc.
- eapply jc_glob_P_pres; [exact HPRc | exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 B))))))))].
Qed.

Definition PE_INVK (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (LK : list blk)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) : Prop :=
PE_CORE pf q m ts cb j1 j2 utf sv /\
PE_BASE pf LB0 payload me lo m md A (pe_blocks pf q LB0 ts ++ LK) errv /\
(forall i l, nth_error (t_levels ts) i = Some l -> lvl_cur rsegs S4F m (t_depth ts) i l) /\
(if zin (cur_st ts) [ST_array_add; ST_ovadd] then jopt rsegs S4F (t_objs ts) m (t_objbs ts) (t_obj ts) else t_objbs ts = []).

#[using="Type"] Lemma PE_INV_K : forall pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv,
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
PE_INVK pf q LB0 payload me lo m md A ts [] cb j1 j2 utf sv errv.
Proof.
intros until errv. intros [CORE REST]. apply PE_REST_base in REST as (BASE & LV & OBJ).
split; [exact CORE|]. split; [rewrite app_nil_r; exact BASE|]. split; [exact LV | exact OBJ].
Qed.

Definition lvl_weak (m : word -> option byte) (depth i : nat) (l : tlevel) : Prop :=
(0 <= tl_st l <= 26 /\ 0 <= tl_ss l <= 26) /\
jopt rsegs S4F (tl_cs l) m (tl_cbs l) (tl_cur l) /\
(name_ok rsegs m false l \/ name_ok rsegs m true l) /\
((depth < i)%nat -> lvl_clean l).

Definition PE_INVW (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (LK : list blk)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) : Prop :=
PE_CORE pf q m ts cb j1 j2 utf sv /\
PE_BASE pf LB0 payload me lo m md A (pe_blocks pf q LB0 ts ++ LK) errv /\
(forall i l, nth_error (t_levels ts) i = Some l -> lvl_weak m (t_depth ts) i l).

#[using="Type"] Lemma lvl_cur_weak : forall m depth i l, lvl_cur rsegs S4F m depth i l -> lvl_weak m depth i l.
Proof.
intros m depth i l (R1 & R2 & J & M). split; [split; [exact R1 | exact R2]|]. split; [exact J|].
destruct (Nat.ltb_spec i depth) as [Hlt|Hge].
- destruct M as [(_ & _ & N)|(_ & _ & N)]; (split; [| intros; exfalso; lia]); [left | right]; exact N.
- destruct (Nat.eqb_spec i depth) as [->|Hne].
+ destruct M as (c & hn & _ & _ & N). split; [| intros; exfalso; lia]. destruct hn; [right | left]; exact N.
+ pose proof M as (C1 & C2 & C3 & C4 & C5). split; [| intros _; exact M]. left. cbn. split; [exact C4 | exact C5].
Qed.

#[using="Type"] Lemma PE_INVK_W : forall pf q LB0 payload me lo m md A ts LK cb j1 j2 utf sv errv,
PE_INVK pf q LB0 payload me lo m md A ts LK cb j1 j2 utf sv errv ->
PE_INVW pf q LB0 payload me lo m md A ts LK cb j1 j2 utf sv errv.
Proof.
intros until errv. intros (CORE & BASE & LV & _). split; [exact CORE|]. split; [exact BASE|].
intros i l Hl. apply lvl_cur_weak. exact (LV i l Hl).
Qed.

#[using="Type"] Lemma PE_INV_W : forall pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv,
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
PE_INVW pf q LB0 payload me lo m md A ts [] cb j1 j2 utf sv errv.
Proof. intros. apply PE_INVK_W. apply PE_INV_K. assumption. Qed.

#[using="Type"] Lemma lvl_mode_aadd : forall ss, lvl_mode ST_array_add ss = Some (CArr, false).
Proof.
intros ss. destruct (Z.eq_dec ss ST_array_add) as [->|NE]; [vm_compute; reflexivity|].
unfold lvl_mode. replace (Z.eqb ST_array_add ss) with false by (symmetry; apply Z.eqb_neq; congruence).
cbn -[zin andb orb]. cbn [zin existsb Z.eqb ws_states val_states esc_states app orb ST_array_add ST_eatws ST_comment_start ST_comment ST_comment_eol ST_comment_end
ST_start ST_null ST_boolean ST_number ST_inf ST_string ST_finish ST_string_escape ST_escape_unicode ST_esc_need_escape ST_esc_need_u].
rewrite ?Bool.andb_false_r. reflexivity.
Qed.
#[using="Type"] Lemma lvl_mode_ovadd : forall ss, lvl_mode ST_ovadd ss = Some (CObj, true).
Proof.
intros ss. destruct (Z.eq_dec ss ST_ovadd) as [->|NE]; [vm_compute; reflexivity|].
unfold lvl_mode. replace (Z.eqb ST_ovadd ss) with false by (symmetry; apply Z.eqb_neq; congruence).
cbn -[zin andb orb]. cbn [zin existsb Z.eqb ws_states val_states esc_states app orb ST_ovadd ST_array_add ST_eatws ST_comment_start ST_comment ST_comment_eol ST_comment_end
ST_start ST_null ST_boolean ST_number ST_inf ST_string ST_finish ST_string_escape ST_escape_unicode ST_esc_need_escape ST_esc_need_u ST_ofield].
rewrite ?Bool.andb_false_r. reflexivity.
Qed.

#[using="Type"] Lemma concat_split : forall (levels : list tlevel) i l,
nth_error levels i = Some l ->
concat (map lvl_blocks levels) =
concat (map lvl_blocks (firstn i levels)) ++ lvl_blocks l ++ concat (map lvl_blocks (skipn (S i) levels)).
Proof.
induction levels as [|h t IH]; intros [|i] l H; cbn in H; try discriminate.
- injection H as ->. cbn. reflexivity.
- cbn [firstn skipn map concat]. rewrite (IH i l H). rewrite !app_assoc. reflexivity.
Qed.

#[using="Type"] Lemma lupd_split : forall (levels : list tlevel) i l x,
nth_error levels i = Some l ->
concat (map lvl_blocks (lupd levels i x)) =
concat (map lvl_blocks (firstn i levels)) ++ lvl_blocks x ++ concat (map lvl_blocks (skipn (S i) levels)).
Proof.
induction levels as [|h t IH]; intros [|i] l x H; cbn in H; try discriminate.
- injection H as ->. cbn. reflexivity.
- cbn [lupd firstn skipn map concat]. rewrite (IH i l x H). rewrite !app_assoc. reflexivity.
Qed.

#[using="Type"] Lemma concat_lupd_empty : forall (levels : list tlevel) i l x,
nth_error levels i = Some l -> lvl_blocks x = [] ->
Permutation (concat (map lvl_blocks levels)) (lvl_blocks l ++ concat (map lvl_blocks (lupd levels i x))).
Proof.
intros levels i l x H Hx. rewrite (concat_split _ _ _ H), (lupd_split _ _ _ x H), Hx. rewrite app_nil_l.
apply Permutation_app_swap_app.
Qed.

#[using="Type"] Lemma concat_lupd_fill : forall (levels : list tlevel) i l x,
nth_error levels i = Some l -> lvl_blocks l = [] ->
Permutation (lvl_blocks x ++ concat (map lvl_blocks levels)) (concat (map lvl_blocks (lupd levels i x))).
Proof.
intros levels i l x H Hl. rewrite (concat_split _ _ _ H), (lupd_split _ _ _ x H), Hl. rewrite app_nil_l.
apply Permutation_app_swap_app.
Qed.
End Inv.

End RC__1.
End Mq0.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply QJjn.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require TopUbTac.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Tk1 Require Tk1Tac Tk1Disp.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Tk3 Require Tk3Tac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import UEQM.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0.
Import UC8c.Mq0.
Import Qsw7 QJjn QkMG.
Import UG8z.
Import TopUbTac Tk1Tac Tk1Disp.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeBreak.
Variable HIx : heap_iface S4L.

#[using="Type"] Lemma seg_break :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
t_co ts < pf_len pf ->
(forall m' a0' a1',
bv_unsigned cb = 0 ->
PE_INV HIx pf q LB0 payload me lo m' md A (ts_set_co ts (t_co ts + 1)) cb j1 j2 utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_OUT (t_co ts + 1) x1 gp t0 t1 t2 a0' a1' a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m') md) T) ->
(forall m' a1',
bv_unsigned cb <> 0 ->
PE_INV HIx pf q LB0 payload me lo m' md A (ts_set_co ts (t_co ts + 1)) cb j1 j2 utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_LOOP (t_co ts + 1) x1 gp t0 t1 t2 (Z_to_bv 64 (t_co ts + 1)) a1' a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m') md) T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK (t_co ts) x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hco Kout Kloop.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & _ & _ & _ & _ & _ & _ & PLOC & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR. unfold pe_ms. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold_consts.
assert (SB1 : 1 <= sb).
{ unfold payload_loc in PLOC. cbn [pf_spf pf_sb pf_len blk_addr blk_size fst snd] in PLOC.
destruct PLOC as [L0 | [PL | ([ba bn] & Hb & Hb1 & _)]]; [lia | unfold PE_FRAME in PL; lia |].
assert (INb : In (ba, bn) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs)))
by (unfold pe_blocks; apply in_or_app; right; right; right; exact Hb).
pose proof (heap_blk S4L HIx _ _ _ _ ba bn HP INb) as (_ & _ & Hb0 & _). unfold blk_addr in Hb1. cbn [fst] in Hb1. lia. }
clear PLOC.
assert (INtk : In (tk, 72) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs)))
by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ tk 72 HP INtk) as Himg_t. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Himg_t.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
pose proof (wmono_refl rsegs m) as WM.
pose proof (munch_refl [(tk, tk + 72)] m) as MU.
stash PB. stash REST. clear HP.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
apply rz_evt; [exact MOK|]. unfold PE_BREAK.
step. step. step. tk1_chk.
step. norm_sx32. step. norm_w32. step. tk1_chk.
step. stepz.
replace (sb + co + 1) with (sb + (co + 1)) by lia.
unstash PB. unstash REST.
assert (HW : Forall (pe_wtf (PEF tk oldl newl len lenr sb spf pmd mxd fl)) [(tk, tk + 72)]) by (apply Forall_cons; [left; cbn; lia | apply Forall_nil]).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (INV' : PE_INV HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A
(ts_set_co (TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) (co + 1))
cb j1 j2 utf sv errv)
end.
{ split.
- unfold PE_CORE, ts_set_co; cbn. split; [exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [exact TOK|]. split; [| split; [exact Hpb | split; [| exact FR]]].
+ eapply (pbuf_wtf HIx) with (ts := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs);
[exact STC | exact (proj1 REST) | exact PB | exact MU | exact WM | exact HW].
+ eapply (tstack_wtf HIx) with (ts := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs);
[exact STC | exact (proj1 REST) | exact TSK | exact LEN32 | exact MU | exact WM | exact HW].
- unfold ts_set_co; cbn. eapply (PE_REST_private_write HIx) with (ts := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in REST;
[exact REST | exact STC | exact MU | exact WM | exact MI | apply pe_wtf_private; exact HW]. }
clear TOK FR PB TSK REST MU WM.
try (change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb))).
destruct (Z.eq_dec (bv_unsigned cb) 0) as [Hc0 | Hc1].
- step. if_truex. apply evt_RZ_done. eapply Kout; [exact Hc0 | exact INV'].
- step. if_falsex. step. apply evt_RZ_done. eapply Kloop; [exact Hc1 | exact INV'].
Qed.

#[using="Type"] Lemma seg_break2 :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (av : Z),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
t_co ts < pf_len pf ->
0 <= av < 2^64 -> (av = 0 <-> bv_unsigned cb = 0) ->
(forall m' a0' a1',
bv_unsigned cb = 0 ->
PE_INV HIx pf q LB0 payload me lo m' md A (ts_set_co ts (t_co ts + 1)) cb j1 j2 utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_OUT (t_co ts + 1) x1 gp t0 t1 t2 a0' a1' a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m') md) T) ->
(forall m' a1',
bv_unsigned cb <> 0 ->
PE_INV HIx pf q LB0 payload me lo m' md A (ts_set_co ts (t_co ts + 1)) cb j1 j2 utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_LOOP (t_co ts + 1) x1 gp t0 t1 t2 (Z_to_bv 64 (t_co ts + 1)) a1' a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m') md) T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK2 (t_co ts) x1 gp t0 t1 t2 (Z_to_bv 64 av) a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until av. intros STC INV Hco _ _ Kout Kloop.
exact (seg_break pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv T x1 gp t0 t1 t2 (Z_to_bv 64 av) a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc STC INV Hco Kout Kloop).
Qed.

End PeBreak.

End RC__1.
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import UEQM.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0.
Import UC8c.Mq0.
Import Qsw7 QJjn QkMG.
Import UG8z.
Import QJjn.Mq0.
Import TopUbTac Tk1Tac Tk3Tac.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeLoop.
Variable HIx : heap_iface S4L.

Definition ts_set_err (ts : tstate) (e : word) : tstate :=
TST (t_depth ts) (t_levels ts) (t_co ts) (t_pb ts) (t_pbs ts)
(TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (ts_choff (t_x ts)) e (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts).

Local Ltac wstop S := lazymatch goal with
| |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
let b := eval vm_compute in (existsb (Z.eqb pc) S) in
lazymatch b with true => fail | false => idtac end
| |- _ => idtac end.
Local Ltac pbr E := try E; ub_resolve; lazymatch goal with
| |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => first [if_truex | align_true]
| |- _ => idtac end.
Local Ltac pwalk S E := repeat (wstop S; lazymatch goal with
| |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => pbr E
| |- _ => try shl_norm; try E; first [stepz | step]
end).
Local Ltac pexp S E K := pwalk S E; lazymatch goal with
| |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd; cbv iota; pexp S E K
| |- _ => K
end.

#[using="Type"] Lemma lbody_wider : forall V T c, lbody rsegs V T c ->
forall V' : config -> Prop, (forall x, V x -> V' x) -> lbody rsegs V' T c.
Proof.
intros V T c H. induction H as [V T c Hr | V T c I nx k Hn Hk IH Hv]; intros V' HV.
- apply lb_exit. exact Hr.
- eapply lb_node; [exact Hn | intros i Ei; exact (IH i Ei V' HV) | intros i Ei; exact (HV _ (Hv i Ei))].
Qed.

#[using="Type"] Lemma star_det1 : forall c c' tr ce,
node_ok rsegs c unit (fun _ => []) (fun _ => c') -> star_cfg rsegs (alloc_only_cfg false) c tr ce -> tr = [] ->
ce = c \/ star_cfg rsegs (alloc_only_cfg false) c' [] ce.
Proof.
intros c c' tr ce Hn Hw. revert Hn. destruct Hw as [c0 | c1 evs c2 tr c3 Hss Hs']; intros Hn Etr.
- left. reflexivity.
- right. apply app_eq_nil in Etr as [-> ->]. destruct Hn as [_ Hc].
destruct (Hc _ _ Hss) as (u & _ & Hx). cbv beta in Hx. injection Hx as ->. exact Hs'.
Qed.

#[using="Type"] Lemma rz_fwd1 : forall c c' T,
node_ok rsegs c unit (fun _ => []) (fun _ => c') -> realizes rsegs c T -> realizes rsegs c' T.
Proof.
assert (K : (forall c T, realizes rsegs c T -> forall c', node_ok rsegs c unit (fun _ => []) (fun _ => c') -> realizes rsegs c' T)
/\ (forall V T c, lbody rsegs V T c -> forall c', node_ok rsegs c unit (fun _ => []) (fun _ => c') -> lbody rsegs V T c' \/ V c')).
{ apply (realizes_lbody_mutind rsegs
(fun c T _ => forall c', node_ok rsegs c unit (fun _ => []) (fun _ => c') -> realizes rsegs c' T)
(fun V T c _ => forall c', node_ok rsegs c unit (fun _ => []) (fun _ => c') -> lbody rsegs V T c' \/ V c')).
- intros c I evs nx Tf i0 Hnode Hcont IH c' Hn.
destruct Hnode as [Hs _]. destruct Hn as [_ Hc].
assert (E : forall i, evs i = [] /\ nx i = c').
{ intros i. destruct (Hc _ _ (Hs i)) as (u & He & Hx). cbv beta in He, Hx. split; [exact He | injection Hx as Hx; exact Hx]. }
assert (R : forall i, realizes rsegs c' (Tf i)) by (intros i; destruct (E i) as [_ Ex]; rewrite <- Ex; apply Hcont).
apply (rz_conseq rsegs c' (Tf i0)); [apply R |].
intros tr. unfold t_alt, t_emit. split.
+ intros Ht. exists i0. right. exists tr. destruct (E i0) as [Ee _]. rewrite Ee. split; [reflexivity | exact Ht].
+ intros (i & [Hp | (tr' & Htr & Ht)]); destruct (E i) as [Ee _]; rewrite Ee in *.
* apply is_prefix_nil_r in Hp. subst tr. exact (realizes_nonempty rsegs _ _ (R i0)).
* cbn [app] in Htr. subst tr'. apply (proj1 (realizes_obs_iff rsegs _ _ (R i0) tr)). apply (proj2 (realizes_obs_iff rsegs _ _ (R i) tr)). exact Ht.
- intros c Hh c' Hn. destruct Hn as [Hs _]. exfalso. apply Hh. exact (sstep_halted_none rsegs _ _ _ (Hs tt)).
- intros c T T' H IH Heq c' Hn. exact (rz_conseq rsegs c' T T' (IH c' Hn) Heq).
- intros V T c ce HV Hbody IHb Hw He IHe c' Hn.
destruct (star_det1 c c' [] ce Hn Hw eq_refl) as [Ec | Hw'].
+ subst ce. exact (IHe c' Hn).
+ destruct (IHb c HV c' Hn) as [Lb | Vc].
* apply (rz_loop rsegs (fun x => V x \/ x = c') T c' ce); [right; reflexivity | | exact Hw' | exact He].
intros x [Vx | ->]; [apply (lbody_wider V T x (Hbody x Vx)) | apply (lbody_wider V T c' Lb)]; intros y Vy; left; exact Vy.
* exact (rz_loop rsegs V T c' ce Vc Hbody Hw' He).
- intros V T c H IH c' Hn. left. apply lb_exit. exact (IH c' Hn).
- intros V T c I nx k Hnode Hk IHk Hv c' Hn. destruct Hn as [Hs _]. destruct Hnode as [_ Hc].
destruct (Hc _ _ (Hs tt)) as (i & _ & Hx). cbv beta in Hx. injection Hx as Hx. rewrite Hx.
destruct (k i) eqn:Ek; [left; exact (Hk i Ek) | right; exact (Hv i Ek)]. }
intros c c' T Hn H. exact (proj1 K c T H c' Hn).
Qed.

#[using="Type"] Lemma rz_fwd : forall ms ms' md T, model_ok md -> msteps rsegs ms ms' ->
realizes rsegs (mkCfg ms md) T -> realizes rsegs (mkCfg ms' md) T.
Proof.
intros ms ms' md T [Hh Hl] Hms. induction Hms as [ms | ms ms1 ms2 [Hsvc Hst] Hms IH]; intros Hr; [exact Hr |].
apply IH. eapply rz_fwd1; [eapply node_instr; eassumption | exact Hr].
Qed.

#[using="Type"] Lemma seg_loop :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
(pf_lenr pf <> pf_len pf -> t_co ts < pf_len pf) ->

(forall m' (c : byte) (a0' : word) (j2' : list byte) x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some c ->
PE_INV HIx pf q LB0 payload me lo m' md A ts c j1 j2' utf sv errv ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_REDO (t_co ts) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md) T) ->

(forall m' (e : word) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc',
t_co ts = pf_len pf ->
PE_INV HIx pf q LB0 payload me lo m' md A (ts_set_err ts e) cb j1 j2 utf sv errv ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_OUT (t_co ts) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F' fc' m') md) T) ->

(forall x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6',
t_co ts < pf_len pf ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR (t_co ts) x1' gp' t0' t1' t2' (Z_to_bv 64 14) a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F fc m) md) T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_LOOP (t_co ts) x1 gp t0 t1 t2 (Z_to_bv 64 (t_co ts)) a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV CLT Kredo Kout Kerr.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & (SBL & RR & LENR)).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & JCG).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR. unfold pe_ms. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl].
unfold_consts.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, (32 * mxd)) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ tk 72 HP INtk) as Himg_t. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Himg_t.
pose proof (heap_blk S4L HIx _ _ _ _ q (32 * mxd) HP INq) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ q (32 * mxd) HP INq) as Himg_q. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Himg_q.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hqhi.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
pose proof (wmono_refl rsegs m) as WM.
pose proof (bytes_at_bound _ _ _ _ STR) as SBB.
stash PB. stash REST. clear OBJ HPR.
apply rz_evt; [exact MOK|]. unfold PE_LOOP.
destruct (loop_cases (PEF tk oldl newl len lenr sb spf pmd mxd fl) co LENR (proj1 RR) ltac:(cbn [pf_len pf_mxd]; lia) ltac:(cbn [pf_len pf_mxd]; lia) CLT) as [[Elenr Heof] | [Hne Hmore]]; cbn [pf_len pf_lenr pf_mxd] in *.
-
subst lenr. pose (lenr := len). subst co.
pose proof (munch_refl [(tk, tk + 72)] m) as MU.
assert (TAIL : forall (e : word) mc x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6',
rw_cells rsegs mc tk
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 (Z.of_nat depth)); C4 isd; C4 stpos;
C4 (Z_to_bv 64 len); C4 e; C4 ucs; C4 high; C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)] ->
rw_cells rsegs mc spf [C8 (Z_to_bv 64 obj); CB 16 j1; C4 (nbw j2); CB 3 (skipn 4 j2); C1 cb; CB 8 utf;
C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv); C8 (pe_s7 sv); C8 (pe_s6 sv);
C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)] ->
munch [(tk, tk + 72)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
evt rsegs (RZ rsegs md T)
(MS (mkR x1' (Z_to_bv 64 spf) gp (Z_to_bv 64 490496) t0' t1' t2' (Z_to_bv 64 tk) (Z_to_bv 64 oldl) a0' a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4' (Z_to_bv 64 (sb + len)) s6' s7' s8' s9' s10' (Z_to_bv 64 0x134c0) t3' t4' t5' t6')
F (Z_to_bv 64 PE_OUT) fc None mc (seg_rom rsegs))).
{ intros e mc x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' TOK' FR' MU' WM' MI'.
unstash PB. unstash REST.
assert (HW : Forall (pe_wtf (PEF tk oldl newl len lenr sb spf pmd mxd fl)) [(tk, tk + 72)]) by (apply Forall_cons; [left; cbn; lia | apply Forall_nil]).
apply evt_RZ_done. eapply (Kout mc e); [reflexivity | | apply fsaved_refl | intros Hf; exact Hf].
split.
- unfold PE_CORE, ts_set_err; cbn. split; [exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [exact TOK'|]. split; [| split; [exact Hpb | split; [| exact FR']]].
+ eapply (pbuf_wtf HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact PB | exact MU' | exact WM' | exact HW].
+ eapply (tstack_wtf HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact TSK | exact LEN32 | exact MU' | exact WM' | exact HW].
- unfold ts_set_err; cbn. eapply (PE_REST_private_write HIx) with (ts := ts0) in REST;
[exact REST | exact STC | exact MU' | exact WM' | exact MI' | apply pe_wtf_private; exact HW]. }
pwalk [0x23ea8] ltac:(try norm_sx32).
destruct (PeanoNat.Nat.eq_dec depth 0) as [D0 | Dn].
+ subst depth. cbn [Z.of_nat pf_mxd] in TOK |- *. pbr idtac.
destruct (nth_error levels 0) as [l0|] eqn:Hl0; [| apply nth_error_None in Hl0; lia].
pose proof (TSK 0%nat l0 Hl0) as L0. rewrite Z.mul_0_r, Z.add_0_r in L0. unfold srec_cells in L0.
pose proof (stash_i _ TSK) as TSK'. clear TSK. rename TSK' into TSK.
pose proof (LV 0%nat l0 Hl0) as (ST26 & SS26 & _).
pwalk [0x23ea8] ltac:(try norm_sx32).
destruct (Z.eq_dec (tl_st l0) 0) as [S0 | Sn].
* rewrite S0. pbr idtac. pwalk [0x23ea8] ltac:(try norm_sx32).
destruct (Z.eq_dec (tl_ss l0) 2) as [F2 | Fn].
-- rewrite F2. pbr idtac. pwalk [0x23ea8] ltac:(try norm_sx32). unstash TSK. eapply TAIL; [exact TOK | exact FR | exact MU | exact WM | exact MI].
-- pbr idtac. pwalk [0x23ea8] ltac:(try norm_sx32). unstash TSK. eapply TAIL; [exact TOK | exact FR | exact MU | exact WM | exact MI].
* pbr idtac. pwalk [0x23ea8] ltac:(try norm_sx32). unstash TSK. eapply TAIL; [exact TOK | exact FR | exact MU | exact WM | exact MI].
+ pbr idtac. pwalk [0x23ea8] ltac:(try norm_sx32). eapply TAIL; [exact TOK | exact FR | exact MU | exact WM | exact MI].
-
assert (Hco : co < len) by lia.
assert (SB1 : 1 <= sb).
{ unfold payload_loc in SBin; cbn [pf_spf pf_sb pf_len pf_mxd] in SBin.
destruct SBin as [L0 | [Hs | (b & Hb & Hb1 & Hb2)]]; [lia | unfold PE_FRAME in Hs; lia |].
destruct b as [ba bn]. cbn [blk_addr blk_size fst snd] in Hb1, Hb2. unfold blk_addr in Hb1 || idtac. cbn [fst] in Hb1.
assert (INb : In (ba, bn) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; right; right; exact Hb).
pose proof (heap_blk S4L HIx _ _ _ _ ba bn HP INb) as (_ & _ & Hba & _). lia. }
destruct (nth_error payload (Z.to_nat co)) as [c|] eqn:Hc; [| apply nth_error_None in Hc; lia].
pose proof (tok_flags_byte_g mxd fl m tk pb (Z.of_nat depth) q (TS isd stpos (Z_to_bv 64 co) err ucs high quote) TOK) as RDF.
pose proof (payload_byte _ _ _ _ _ STR Hc ltac:(lia)) as RDC.
pose proof (bv_unsigned_in_range 8 c) as CBR; unfold bv_modulus in CBR; cbn in CBR.
assert (JOINR : forall mc nv x1' t0' t1' t2' a0v a1v a2v a3v a4v a5v a6v a7v s4' s6' s7' s8' s9' s10' t3' t4' t5' t6',
rw_cells rsegs mc spf [C8 (Z_to_bv 64 obj); CB 16 j1; C4 nv; CB 3 (skipn 4 j2); C1 cb; CB 8 utf;
C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv); C8 (pe_s7 sv); C8 (pe_s6 sv);
C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)] ->
munch [(spf, spf + 144)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc -> bytes_at rsegs mc sb payload ->
evt rsegs (RZ rsegs md T)
(MS (mkR x1' (Z_to_bv 64 spf) gp (Z_to_bv 64 490496) t0' t1' t2' (Z_to_bv 64 tk) (Z_to_bv 64 oldl) a0v a1v a2v a3v a4v a5v a6v a7v
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4' (Z_to_bv 64 (sb + co)) s6' s7' s8' s9' s10' (Z_to_bv 64 0x134c0) t3' t4' t5' t6')
F (Z_to_bv 64 0x21dcc) fc None mc (seg_rom rsegs))).
{ intros mc nv x1' t0' t1' t2' a0v a1v a2v a3v a4v a5v a6v a7v s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' FRj MUj WMj MIj STRj.
assert (TOKj : rw_cells rsegs mc tk (tok_cells_g mxd fl pb (Z.of_nat depth) q (TS isd stpos (Z_to_bv 64 co) err ucs high quote))).
{ eapply rw_cells_transport; [exact TOK | exact MUj | exact WMj | unfold tok_cells_g; cbn; lia]. }
unfold tok_cells_g in TOKj. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOKj.
pose proof (payload_byte _ _ _ _ _ STRj Hc ltac:(lia)) as RDCj.
clear RDF RDC.
pwalk [0x21e34] ltac:(try norm_sx32; try (rewrite le1_zxb; mem_after_store)).
unstash PB. unstash REST.
assert (HW : Forall (pe_wtf (PEF tk oldl newl len lenr sb spf pmd mxd fl)) [(spf, spf + 144)]) by (apply Forall_cons; [right; unfold PE_FRAME; cbn [pf_spf pf_tk fst snd pf_md pf_mxd pf_fl]; split; [apply Z.le_refl | apply Z.le_refl] | apply Forall_nil]).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?x _) => rename x into mf end.
lazymatch goal with H : munch _ m ?mf |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
rename H into MUf;
lazymatch goal with W : wmono rsegs m mf |- _ => rename W into WMf end;
lazymatch goal with I : mem_inv rsegs mf |- _ => rename I into MIf end;
lazymatch goal with Fj : rw_cells rsegs mf spf _ |- _ => rename Fj into FRf end
end.
assert (TOKf : rw_cells rsegs mf tk (tok_cells_g mxd fl pb (Z.of_nat depth) q (TS isd stpos (Z_to_bv 64 co) err ucs high quote))).
{ eapply rw_cells_transport; [exact TOK | exact MUf | exact WMf | unfold tok_cells_g; cbn; lia]. }
apply evt_RZ_done.
lazymatch goal with |- realizes _ (mkCfg (MS ?R ?Fx _ ?fx ?rv ?mf ?ro) _) _ =>
apply (rz_fwd (MS R Fx (Z_to_bv 64 0x21e14) fx rv mf ro)); [exact MOK | | ] end.
{ lazymatch goal with |- msteps _ ?a ?b => cut (evt rsegs (fun s => s = b) a); [intros (s & Hm & Hq); cbv beta in Hq; subst s; exact Hm |] end.
pose proof TOKf as TOKg. unfold tok_cells_g in TOKg. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOKg.
pwalk [0x21e34] ltac:(try norm_sx32).
apply evt_done; reflexivity. }
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
eapply (Kredo mf c _ (le4 nv ++ skipn 4 j2)); [exact Hco | first [reflexivity | exact Hc] | | apply fsaved_refl | intros Hf; exact Hf] end.
split.
- unfold PE_CORE; cbn. split; [exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [exact TOKf|].
split; [| split; [exact Hpb | split; [| apply pe_frame_nb_set; exact FRf]]].
+ eapply (pbuf_wtf HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact PB | exact MUf | exact WMf | exact HW].
+ eapply (tstack_wtf HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact TSK | exact LEN32 | exact MUf | exact WMf | exact HW].
- eapply (PE_REST_private_write HIx) with (ts := ts0) in REST;
[exact REST | exact STC | exact MUf | exact WMf | exact MIf | apply pe_wtf_private; exact HW]. }
assert (JOINS : forall (a0v : word) x1' t0' t1' t2' a1v a2v a3v a4v a5v a6v a7v s4' s6' s7' s8' s9' s10' t3' t4' t5' t6',
evt rsegs (RZ rsegs md T)
(MS (mkR x1' (Z_to_bv 64 spf) gp (Z_to_bv 64 490496) t0' t1' t2' (Z_to_bv 64 tk) (Z_to_bv 64 oldl) a0v a1v a2v a3v a4v a5v a6v a7v
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4' (Z_to_bv 64 (sb + co)) s6' s7' s8' s9' s10' (Z_to_bv 64 0x134c0) t3' t4' t5' t6')
F (Z_to_bv 64 0x21dbc) fc None m (seg_rom rsegs))).
{ intros a0v x1' t0' t1' t2' a1v a2v a3v a4v a5v a6v a7v s4' s6' s7' s8' s9' s10' t3' t4' t5' t6'.
clear RDF RDC. stash STR.
pose proof (munch_refl [(spf, spf + 144)] m) as MUs. pose proof (wmono_refl rsegs m) as WMs.
step. try mem_after_store.
lazymatch goal with H : munch _ m ?mf |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
rename H into MU1;
lazymatch goal with W : wmono rsegs m mf |- _ => rename W into WM1 end;
lazymatch goal with I : mem_inv rsegs mf |- _ => rename I into MI1 end;
lazymatch goal with Fj : rw_cells rsegs mf spf _ |- _ => rename Fj into FR1 end
end.
unstash REST. unstash STR.
assert (HWs : Forall (pe_private (PEF tk oldl newl len lenr sb spf pmd mxd fl) q pbs) [(spf, spf + 144)]).
{ apply Forall_cons; [| apply Forall_nil]. right; right; right. unfold PE_FRAME; cbn [fst snd pf_spf pf_mxd]. lia. }
pose proof (payload_private HIx _ _ _ ts0 _ _ _ _ _ _ _ STC (proj1 REST) STR PLEN SBin MU1 HWs) as STR1. cbn [pf_sb pf_mxd] in STR1.
stash REST.
pwalk [0x21dcc] ltac:(try norm_sx32).
eapply JOINR; [exact FR1 | exact MU1 | exact WM1 | exact MI1 | exact STR1]. }
pose proof (munch_refl [(spf, spf + 144)] m) as MU.
pwalk [0x21dcc; 0x21dbc; 0x23ea4] ltac:(try norm_sx32).
rewrite (zxb_byte fl), (unsigned_lit (fl mod 256)) by (pose proof (Z.mod_pos_bound fl 256 ltac:(lia)); lia).
rewrite (land_mod256 fl 16) by lia.
destruct (land16_cases fl) as [F16 | F16]; rewrite F16.
+ pbr idtac. eapply JOINR; [exact FR | exact MU | exact WM | exact MI | exact STR].
+ pbr idtac. pexp [0x21dcc; 0x21dbc; 0x23ea4] ltac:(try norm_sx32) ltac:(first
[ eapply JOINR; [exact FR | exact MU | exact WM | exact MI | exact STR]
| apply JOINS
| apply evt_RZ_done; eapply Kerr; exact Hco ]).
Qed.

End PeLoop.

End RC__1.
End Mq2.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import UEQM.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0.
Import UC8c.Mq0.
Import Qsw7 QJjn QkMG.
Import UG8z.
Import TopUbTac Tk1Tac Tk3Tac.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Ltac enum_z H v :=

let rec go k := lazymatch k with
| 27%nat => exfalso; lia
| _ => let kz := eval vm_compute in (Z.of_nat k) in
let E := fresh "E" in
destruct (Z.eq_dec v kz) as [E | ?]; [ rewrite ?E in * | go (S k) ]
end in go 0%nat.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeOfend.
Variable HIx : heap_iface S4L.

Definition ts_set_level (ts : tstate) (l : tlevel) : tstate :=
TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) l) (t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (t_obj ts) (t_objs ts) (t_objbs ts).

#[using="Type"] Lemma seg_ofend :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a3 a4 a5 a6 a7 s6 s7 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_ofend ->
t_co ts < pf_len pf ->

(forall m' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6',
bv_unsigned cb = 58 ->
PE_INV HIx pf q LB0 payload me lo m' md A (ts_set_level ts (TL ST_eatws ST_ovalue (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb j1 j2 utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK (t_co ts) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F fc m') md) T) ->

(forall x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6',
bv_unsigned cb <> 58 ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR (t_co ts) x1' gp' t0' t1' t2' (Z_to_bv 64 10) a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F fc m) md) T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf (pe_jt ST_ofend) (t_co ts) x1 gp t0 t1 t2
(Z_to_bv 64 0) (Z_to_bv 64 (tl_st l)) (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a3 a4 a5 a6 a7
(Z_to_bv 64 q) s6 s7 s8 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hst Hco Kbreak Kerr.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR. unfold pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold_consts.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, (32 * mxd)) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk S4L HIx _ _ _ _ q (32 * mxd) HP INq) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ q (32 * mxd) HP INq) as Himg_q. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Himg_q.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hqhi.
assert (Htq : tk <> q).
{ pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND. unfold pe_blocks in ND. rewrite map_app in ND. apply NoDup_app_remove_l in ND.
cbn [map blk_addr fst pf_mxd] in ND. apply List.NoDup_cons_iff in ND as [Hni _]. intros E. apply Hni. left. symmetry. exact E. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tk 72 q (32 * mxd) HP INtk INq Htq) as Hdtq.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
pose proof (wmono_refl rsegs m) as WM.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).

pose proof (srec_join8 _ _ _ (TSK depth l Hl)) as Ld. cbn [le4 Z_to_le_bytes app pf_mxd] in Ld.
remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (munch_refl [(bse, bse + 32)] m) as MU.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
stash PB. stash REST. stash TSK. clear HP LV.
apply rz_evt; [exact MOK|]. rewrite Hst. unfold ST_ofend. cbn [pe_jt pf_mxd].
replace (q + 32 * Z.of_nat depth) with bse by lia.

assert (TAIL : forall mc x1' t0' t1' t2' a0v a1v a2v a3v a4v a5v a6v a7v s4' s6' s7' s8' s9' s10' t3' t4' t5' t6',
bv_unsigned cb = 58 ->
rw_cells rsegs mc bse [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 ST_ovalue); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (tl_cur l)); C8 (Z_to_bv 64 (tl_name l))] ->
munch [(bse, bse + 32)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
(forall H : rw_cells rsegs mc tk [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 (Z.of_nat depth)); C4 isd; C4 stpos;
C4 (Z_to_bv 64 co); C4 err; C4 ucs; C4 high; C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)], True) ->
rw_cells rsegs mc tk [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 (Z.of_nat depth)); C4 isd; C4 stpos;
C4 (Z_to_bv 64 co); C4 err; C4 ucs; C4 high; C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)] ->
rw_cells rsegs mc spf [C8 (Z_to_bv 64 obj); CB 16 j1; C4 (nbw j2); CB 3 (skipn 4 j2); C1 cb; CB 8 utf;
C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv); C8 (pe_s7 sv); C8 (pe_s6 sv);
C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)] ->
realizes rsegs (mkCfg (MS (mkR x1' (Z_to_bv 64 spf) gp (Z_to_bv 64 490496) t0' t1' t2' (Z_to_bv 64 tk) (Z_to_bv 64 oldl)
a0v a1v a2v a3v a4v a5v a6v a7v
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4' (Z_to_bv 64 (sb + co)) s6' s7' s8' s9' s10' (Z_to_bv 64 0x134c0) t3' t4' t5' t6')
F (Z_to_bv 64 PE_BREAK) fc None mc (seg_rom rsegs)) md) T).
{ intros mc x1' t0' t1' t2' a0v a1v a2v a3v a4v a5v a6v a7v s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' Hss L8 MU' WM' MI' _ TOK' FR'.
unstash PB. unstash REST. unstash TSK.
set (ss' := ST_ovalue).
assert (L5 : rw_cells rsegs mc bse [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 ss'); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (tl_cur l)); C8 (Z_to_bv 64 (tl_name l))]) by exact L8. clear L8.
set (l' := TL ST_eatws ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
assert (HW : Forall (pe_wtq (PEF tk oldl newl len lenr sb spf pmd mxd fl) q) [(bse, bse + 32)]).
{ apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia | apply Forall_nil]. }
subst bse. apply (Kbreak mc x1' gp t0' t1' t2' a0v a1v a2v a3v a4v a5v a6v a7v s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' Hss). split.
- unfold PE_CORE, ts_set_level; cbn. split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [exact TOK'|]. split; [| split; [exact Hpb | split; [| exact FR']]].
+ eapply (pbuf_wtq HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact PB | exact MU' | exact WM' | exact HW].
+ eapply (tstack_put rsegs m _ q levels depth l' []); [exact TSK | lia | exact MU' | exact WM' | intros; exact I | exact L5].
- assert (REST' : PE_REST HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A ts0 errv).
{ eapply (PE_REST_private_write HIx) with (ts := ts0) in REST; [exact REST | exact STC | exact MU' | exact WM' | exact MI' | apply pe_wtq_private; exact HW]. }
destruct REST' as (HP' & LV' & OBJ' & ST' & ERR' & STR' & PLEN' & SBin' & HPR' & MDV' & JCG').
unfold ts_set_level; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd].
split.
{ match goal with |- HEAP _ _ _ ?L _ _ => replace L with (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0); [exact HP' |] end.
unfold pe_blocks, tstate_blocks, ts0; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd].
match goal with |- context [map lvl_blocks (lupd ?lv ?d ?x)] => rewrite (map_lupd_same lvl_blocks lv d x l Hl eq_refl) end. reflexivity. } split; [| split; [| split; [exact ST' | split; [exact ERR' | split; [exact STR' | split; [exact PLEN' | split; [exact SBin' | split; [exact HPR' | split; [exact MDV' | exact JCG']]]]]]]]].
+ assert (MODE0 : c0 = CObj /\ hn0 = true).
{ rewrite Hst in Hmode. unfold ST_ofend in Hmode. clear - Hmode SS26.
assert (R : 0 <= tl_ss l <= 26) by lia. enum_z R (tl_ss l); vm_compute in Hmode; split; congruence. }
destruct MODE0 as [-> ->].
intros i li Hli. unfold ts0 in Hli. cbn [t_levels t_depth pf_mxd] in Hli. destruct (PeanoNat.Nat.eq_dec i depth) as [-> | NE].
* rewrite nth_error_lupd_eq in Hli by lia. injection Hli as <-.
eapply lvl_cur_restate with (c' := CObj); [exact (LV' depth l Hl) | exact Hmode | vm_compute; reflexivity | unfold ST_eatws; lia | unfold ss', ST_ovalue; lia | left; reflexivity].
* rewrite nth_error_lupd_neq in Hli by congruence. exact (LV' i li Hli).
+ unfold cur_st in *; cbn in *. rewrite nth_error_lupd_eq by lia. cbn [tl_st pf_mxd]. unfold ST_eatws. cbn.
revert OBJ'. rewrite Hl, Hst. cbn. intros OBJ'. exact OBJ'. }
destruct (Z.eq_dec (bv_unsigned cb) 58) as [C58 | N58].
- tk3_walk 0x23d14 ltac:(try norm_sx32; try unfold zxb; try rewrite (unsigned_lit (bv_unsigned cb)) by lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
apply evt_RZ_done; eapply (TAIL mc _ _); [exact C58 | exact Ld | exact MU | exact WM | exact MI | intros; exact I | exact TOK | exact FR] end.
- tk3_walk 0x23ea4 ltac:(try norm_sx32; try unfold zxb; try rewrite (unsigned_lit (bv_unsigned cb)) by lia).
subst bse. apply evt_RZ_done. eapply Kerr; exact N58.
Qed.
End PeOfend.

End RC__1.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import UEQM.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0.
Import UC8c.Mq0.
Import Qsw7 QJjn QkMG.
Import UG8z.
Import TopUbTac Tk1Tac Tk3Tac.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Ltac enum_z H v :=

let rec go k := lazymatch k with
| 27%nat => exfalso; lia
| _ => let kz := eval vm_compute in (Z.of_nat k) in
let E := fresh "E" in
destruct (Z.eq_dec v kz) as [E | ?]; [ rewrite ?E in * | go (S k) ]
end in go 0%nat.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeOsep.
Variable HIx : heap_iface S4L.

Definition ts_set_level (ts : tstate) (l : tlevel) : tstate :=
TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) l) (t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (t_obj ts) (t_objs ts) (t_objbs ts).

#[using="Type"] Lemma seg_osep :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a3 a4 a5 a6 a7 s6 s7 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_osep ->
t_co ts < pf_len pf ->

(forall m' ss' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6',
(bv_unsigned cb = 44 /\ ss' = ST_ofs_after_sep) \/ (bv_unsigned cb = 125 /\ ss' = ST_finish) ->
PE_INV HIx pf q LB0 payload me lo m' md A (ts_set_level ts (TL ST_eatws ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb j1 j2 utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK2 (t_co ts) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F fc m') md) T) ->

(forall x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6',
bv_unsigned cb <> 44 -> bv_unsigned cb <> 125 ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR (t_co ts) x1' gp' t0' t1' t2' (Z_to_bv 64 11) a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F fc m) md) T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf (pe_jt ST_osep) (t_co ts) x1 gp t0 t1 t2
(Z_to_bv 64 0) (Z_to_bv 64 (tl_st l)) (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a3 a4 a5 a6 a7
(Z_to_bv 64 q) s6 s7 s8 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hst Hco Kbreak Kerr.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR. unfold pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold_consts.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, (32 * mxd)) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk S4L HIx _ _ _ _ q (32 * mxd) HP INq) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ q (32 * mxd) HP INq) as Himg_q. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Himg_q.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hqhi.
assert (Htq : tk <> q).
{ pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND. unfold pe_blocks in ND. rewrite map_app in ND. apply NoDup_app_remove_l in ND.
cbn [map blk_addr fst pf_mxd] in ND. apply List.NoDup_cons_iff in ND as [Hni _]. intros E. apply Hni. left. symmetry. exact E. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tk 72 q (32 * mxd) HP INtk INq Htq) as Hdtq.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
pose proof (wmono_refl rsegs m) as WM.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).

pose proof (srec_join8 _ _ _ (TSK depth l Hl)) as Ld. cbn [le4 Z_to_le_bytes app pf_mxd] in Ld.
remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (munch_refl [(bse, bse + 32)] m) as MU.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
stash PB. stash REST. stash TSK. clear HP LV.
apply rz_evt; [exact MOK|]. rewrite Hst. unfold ST_osep. cbn [pe_jt pf_mxd].
replace (q + 32 * Z.of_nat depth) with bse by lia.

assert (TAIL : forall ss' mc x1' t0' t1' t2' a0v a1v a2v a3v a4v a5v a6v a7v s4' s6' s7' s8' s9' s10' t3' t4' t5' t6',
(bv_unsigned cb = 44 /\ ss' = ST_ofs_after_sep) \/ (bv_unsigned cb = 125 /\ ss' = ST_finish) ->
rw_cells rsegs mc bse [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 ss'); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (tl_cur l)); C8 (Z_to_bv 64 (tl_name l))] ->
munch [(bse, bse + 32)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
(forall H : rw_cells rsegs mc tk [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 (Z.of_nat depth)); C4 isd; C4 stpos;
C4 (Z_to_bv 64 co); C4 err; C4 ucs; C4 high; C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)], True) ->
rw_cells rsegs mc tk [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 (Z.of_nat depth)); C4 isd; C4 stpos;
C4 (Z_to_bv 64 co); C4 err; C4 ucs; C4 high; C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)] ->
rw_cells rsegs mc spf [C8 (Z_to_bv 64 obj); CB 16 j1; C4 (nbw j2); CB 3 (skipn 4 j2); C1 cb; CB 8 utf;
C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv); C8 (pe_s7 sv); C8 (pe_s6 sv);
C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)] ->
realizes rsegs (mkCfg (MS (mkR x1' (Z_to_bv 64 spf) gp (Z_to_bv 64 490496) t0' t1' t2' (Z_to_bv 64 tk) (Z_to_bv 64 oldl)
a0v a1v a2v a3v a4v a5v a6v a7v
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4' (Z_to_bv 64 (sb + co)) s6' s7' s8' s9' s10' (Z_to_bv 64 0x134c0) t3' t4' t5' t6')
F (Z_to_bv 64 PE_BREAK2) fc None mc (seg_rom rsegs)) md) T).
{ intros ss' mc x1' t0' t1' t2' a0v a1v a2v a3v a4v a5v a6v a7v s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' Hss L8 MU' WM' MI' _ TOK' FR'.
unstash PB. unstash REST. unstash TSK.
assert (SS' : 0 <= ss' <= 26) by (unfold ST_ofs_after_sep, ST_finish in Hss; lia).
pose proof L8 as L5. clear L8.
set (l' := TL ST_eatws ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
assert (HW : Forall (pe_wtq (PEF tk oldl newl len lenr sb spf pmd mxd fl) q) [(bse, bse + 32)]).
{ apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia | apply Forall_nil]. }
subst bse. apply (Kbreak mc ss' x1' gp t0' t1' t2' a0v a1v a2v a3v a4v a5v a6v a7v s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' Hss). split.
- unfold PE_CORE, ts_set_level; cbn. split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [exact TOK'|]. split; [| split; [exact Hpb | split; [| exact FR']]].
+ eapply (pbuf_wtq HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact PB | exact MU' | exact WM' | exact HW].
+ eapply (tstack_put rsegs m _ q levels depth l' []); [exact TSK | lia | exact MU' | exact WM' | intros; exact I | exact L5].
- assert (REST' : PE_REST HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A ts0 errv).
{ eapply (PE_REST_private_write HIx) with (ts := ts0) in REST; [exact REST | exact STC | exact MU' | exact WM' | exact MI' | apply pe_wtq_private; exact HW]. }
destruct REST' as (HP' & LV' & OBJ' & ST' & ERR' & STR' & PLEN' & SBin' & HPR' & MDV' & JCG').
unfold ts_set_level; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd].
split.
{ match goal with |- HEAP _ _ _ ?L _ _ => replace L with (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0); [exact HP' |] end.
unfold pe_blocks, tstate_blocks, ts0; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd].
match goal with |- context [map lvl_blocks (lupd ?lv ?d ?x)] => rewrite (map_lupd_same lvl_blocks lv d x l Hl eq_refl) end. reflexivity. } split; [| split; [| split; [exact ST' | split; [exact ERR' | split; [exact STR' | split; [exact PLEN' | split; [exact SBin' | split; [exact HPR' | split; [exact MDV' | exact JCG']]]]]]]]].
+ assert (MODE0 : c0 = CObj /\ hn0 = false).
{ rewrite Hst in Hmode. unfold ST_osep in Hmode. clear - Hmode SS26.
assert (R : 0 <= tl_ss l <= 26) by lia. enum_z R (tl_ss l); vm_compute in Hmode; split; congruence. }
destruct MODE0 as [-> ->].
intros i li Hli. unfold ts0 in Hli. cbn [t_levels t_depth pf_mxd] in Hli. destruct (PeanoNat.Nat.eq_dec i depth) as [-> | NE].
* rewrite nth_error_lupd_eq in Hli by lia. injection Hli as <-.
destruct Hss as [[_ Ess] | [_ Ess]]; rewrite Ess in *.
-- eapply lvl_cur_restate with (c' := CObj); [exact (LV' depth l Hl) | exact Hmode | vm_compute; reflexivity | unfold ST_eatws; lia | unfold ST_ofs_after_sep; lia | left; reflexivity].
-- eapply lvl_cur_restate with (c' := CAny); [exact (LV' depth l Hl) | exact Hmode | vm_compute; reflexivity | unfold ST_eatws; lia | unfold ST_finish; lia | right; reflexivity].
* rewrite nth_error_lupd_neq in Hli by congruence. exact (LV' i li Hli).
+ unfold cur_st in *; cbn in *. rewrite nth_error_lupd_eq by lia. cbn [tl_st pf_mxd]. unfold ST_eatws. cbn.
revert OBJ'. rewrite Hl, Hst. cbn. intros OBJ'. exact OBJ'. }
destruct (Z.eq_dec (bv_unsigned cb) 44) as [C44 | N44].
- tk3_walk 0x23d14 ltac:(try norm_sx32; try unfold zxb; try rewrite (unsigned_lit (bv_unsigned cb)) by lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
apply evt_RZ_done; eapply (TAIL ST_ofs_after_sep mc _); [left; split; [exact C44 | reflexivity] | exact Ld | exact MU | exact WM | exact MI | intros; exact I | exact TOK | exact FR] end.
- destruct (Z.eq_dec (bv_unsigned cb) 125) as [C125 | N125].
+ tk3_walk 0x23d14 ltac:(try norm_sx32; try unfold zxb; try rewrite (unsigned_lit (bv_unsigned cb)) by lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
apply evt_RZ_done; eapply (TAIL ST_finish mc _); [right; split; [exact C125 | reflexivity] | exact Ld | exact MU | exact WM | exact MI | intros; exact I | exact TOK | exact FR] end.
+ tk3_walk 0x23ea4 ltac:(try norm_sx32; try unfold zxb; try rewrite (unsigned_lit (bv_unsigned cb)) by lia).
subst bse. apply evt_RZ_done. eapply Kerr; [exact N44 | exact N125].
Qed.
End PeOsep.

End RC__1.
End Mq4.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import UEQM.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0.
Import UC8c.Mq0.
Import Qsw7 QJjn QkMG.
Import UG8z.
Import TopUbTac Tk1Tac Tk1Disp.
Import Q6q3.
Import ListNotations. Unset Keyed Unification.
Open Scope Z_scope.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeRedo.
Variable HIx : heap_iface S4L.

#[using="Type"] Lemma seg_redo :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l ->
(forall a3' a4',
realizes rsegs (mkCfg (pe_ms rsegs pf (pe_jt (tl_st l)) (t_co ts) x1 gp t0 t1 t2
(Z_to_bv 64 0) (Z_to_bv 64 (tl_st l)) (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a3' a4' a5 a6 a7
(Z_to_bv 64 q) s6 s7 s8 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s10 t3 t4 t5 t6 F fc m) md) T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_REDO (t_co ts) x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl K.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold_consts.
pose proof (heap_blk S4L HIx _ _ _ _ q (32 * mxd) HP ltac:(unfold pe_blocks; apply in_or_app; right; right; left; reflexivity)) as (_ & Hqal & Hqlo & Hqhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hqhi.
pose proof (LV depth l Hl) as (ST26 & SS26 & _).
pose proof (TSK depth l Hl) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld. unfold srec_cells in Ld.
assert (Hb16 : bse mod 16 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
assert (Ebse : q + Z.of_nat depth * 32 = bse) by (subst bse; lia).
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
pose proof (pe_jtab_ro m MI) as JT. unfold pe_jtab in JT.
clear PB REST HP LV TSK FR.
apply rz_evt; [exact MOK|]. unfold PE_REDO.
step. norm_sx32.
tk1_walk_a 0x21e18 0x21e64 40%nat Ebse.
step. norm_sx32. step. step. if_truex. step.
rewrite (unsigned_lit (tl_st l)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
assert (CASES : exists k : nat, (k <= 26)%nat /\ tl_st l = Z.of_nat k) by (exists (Z.to_nat (tl_st l)); split; lia).
destruct CASES as (k & Hk & Ek). rewrite Ek in *. clear Ebse. subst bse.
match goal with |- context [v_sltiu (Z_to_bv 64 ?x) ?imm] => rewrite (QRUw.v_sltiu_0 (Z_to_bv 64 x) imm) by (rewrite ?(unsigned_lit x) by lia; lia) end.
unfold PE_JTAB.
lazymatch type of JT with ro_cells ?sg ?mm ?AA [CB _ ?tab] =>
let zs := eval vm_compute in ((fix go (bs : list byte) : list Z := match bs with b0 :: b1 :: b2 :: b3 :: r => (bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * bv_unsigned b3)))%Z :: go r | _ => nil end) tab) in
let cs := eval cbn [map] in (map (fun z => C4 (Z_to_bv 64 z)) zs) in
assert (JT4 : ro_cells sg mm AA cs);
[ destruct JT as [JTwf JTb]; split; [ cbn; repeat split | ];
replace (cells_bytes cs) with (cells_bytes [CB 108 tab]) by (cbn [cells_bytes cbytes]; rewrite app_nil_r; apply bytes_eq_by_unsigned; vm_compute; reflexivity); exact JTb | ]
end.
clear JT.
do 27 (destruct k as [|k];
[ match goal with |- context [Z_to_bv 64 (Z.of_nat ?n * 4)] =>
let v := eval vm_compute in (Z.of_nat n * 4) in change (Z.of_nat n * 4) with v;
let w := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with w end;
step; step;
match goal with |- context [sx32 (Z_to_bv 64 ?z)] =>
let v := eval vm_compute in (bv_unsigned (sx32 (Z_to_bv 64 z))) in
replace (sx32 (Z_to_bv 64 z)) with (Z_to_bv 64 v) by (apply bv_eq; vm_compute; reflexivity) end;
step; step;
apply evt_RZ_done; apply K
| ]).
exfalso. lia.
Qed.

End PeRedo.

End RC__1.
End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import UEQM.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0.
Import UC8c.Mq0.
Import Qsw7 QJjn QkMG.
Import UG8z.
Import Q6q3.
Import ListNotations. Unset Keyed Unification.
Open Scope Z_scope.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition pe_jt2 (c : Z) : Z :=
match c with
| 34 => 0x23b60
| 39 => 0x23b54
| 45 => 0x224ac
| 48 => 0x224ac
| 49 => 0x224ac
| 50 => 0x224ac
| 51 => 0x224ac
| 52 => 0x224ac
| 53 => 0x224ac
| 54 => 0x224ac
| 55 => 0x224ac
| 56 => 0x224ac
| 57 => 0x224ac
| 70 => 0x229b0
| 73 => 0x22b6c
| 78 => 0x22b58
| 84 => 0x229b0
| 91 => 0x23b84
| 102 => 0x229b0
| 105 => 0x22b6c
| 110 => 0x22b58
| 116 => 0x229b0
| 123 => 0x23b38
| _ => 0x23db4
end.

Definition pe_jtab2 := Eval vm_compute in match image_bytes rsegs 0x137a8 360 with Some bs => bs | None => [] end.
#[using="Type"] Lemma pe_jtab2_ro : forall m, mem_inv rsegs m -> ro_cells rsegs m 0x137a8 [CB 360 pe_jtab2].
Proof.
intros m MI. change 360%nat with (length pe_jtab2).
apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ].
change (Z.of_nat (length pe_jtab2)) with 360%Z. lia.
Qed.
End RC__1.

Lemma enum_step_Z : forall v lo lo' : Z, lo' = (lo + 1)%Z -> (lo <= v)%Z -> v = lo \/ (lo' <= v)%Z.
Proof. intros v lo lo' -> H. destruct (Z.eq_dec v lo) as [E|N]; [left; exact E | right; lia]. Qed.
Ltac enum_from_go v lo n L :=
lazymatch n with
| O => exfalso; lia
| S ?n' => let E := fresh "E" in let L2 := fresh "EL" in
let lo' := eval vm_compute in (lo + 1)%Z in
destruct (enum_step_Z v lo lo' eq_refl L) as [E | L2]; clear L;
[ rewrite ?E in * | enum_from_go v lo' n' L2 ]
end.
Ltac enum_from v lo n :=
let L := fresh "EL" in assert (L : (lo <= v)%Z) by lia; enum_from_go v lo n L.
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma ro_cells_bytes_at2 : forall segs m A cs, ro_cells segs m A cs -> bytes_at segs m A (cells_bytes cs).
Proof. intros segs m A cs [_ H]. exact H. Qed.

Section PeStartD.
Variable HIx : heap_iface S4L.

#[using="Type"] Lemma seg_start_dispatch :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
(forall a1' a3',
realizes rsegs (mkCfg (pe_ms rsegs pf (pe_jt2 (bv_unsigned cb)) (t_co ts) x1 gp t0 t1 t2 a0 a1' a2 a3' a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m) md) T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf (pe_jt ST_start) (t_co ts) x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV K.
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof (proj1 REST) as HP.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold pe_frame in FR. unfold pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
pose proof (pe_jtab2_ro m MI) as JT.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
clear TOK PB TSK REST HP.
apply rz_evt; [exact MOK|]. unfold ST_start. cbn [pe_jt pf_mxd]. unfold PE_JTAB.
step. change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)). step. step.
destruct (Z_lt_dec (bv_unsigned cb) 34) as [LT | GE].
-
replace (Z_to_bv 64 (bv_unsigned cb + -34)) with (Z_to_bv 64 (bv_unsigned cb + -34 + 2^64)).
2:{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite <- (Z_mod_plus_full (bv_unsigned cb + -34) 1 (2^64)). f_equal. }
step. if_falsex. step. apply evt_RZ_done.
replace (pe_jt2 (bv_unsigned cb)) with 0x23db4 in K.
2:{ assert (R : 0 <= bv_unsigned cb <= 33) by lia. clear - R. enum_from (bv_unsigned cb) 0%Z 34%nat; reflexivity. }
apply K.
- destruct (Z_lt_dec 123 (bv_unsigned cb)) as [GT | LE].
+ step. if_falsex. step. apply evt_RZ_done.
replace (pe_jt2 (bv_unsigned cb)) with 0x23db4 in K. 2:{ assert (R : 124 <= bv_unsigned cb <= 255) by lia. clear - R. enum_from (bv_unsigned cb) 124%Z 132%nat; reflexivity. }
apply K.
+ step. if_truex. step.
rewrite (unsigned_lit (bv_unsigned cb + -34)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
step. step. step.

pose proof (bytes_at_read rsegs m 0x137a8 pe_jtab2 ((bv_unsigned cb + -34) * 4) 4 (ro_cells_bytes_at2 _ _ _ _ JT) ltac:(lia)
ltac:(change (length pe_jtab2) with 360%nat; lia)) as RD.
unfold wa in RD. replace (0x137a8 + (bv_unsigned cb + -34) * 4) with ((bv_unsigned cb + -34) * 4 + 79784) in RD by lia.
step. step. step.
apply evt_RZ_done.
assert (R : 34 <= bv_unsigned cb <= 123) by lia.
match goal with |- realizes _ (mkCfg (MS _ _ ?pc _ _ _ _) _) _ =>
replace pc with (Z_to_bv 64 (pe_jt2 (bv_unsigned cb))); [apply K |] end.
clear - R. enum_from (bv_unsigned cb) 34%Z 90%nat; apply bv_eq; vm_compute; reflexivity.
Qed.

End PeStartD.

End RC__2.
End Mq6.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import UEQM.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0.
Import UC8c.Mq0.
Import Qsw7 QJjn QRUw.Mq0 QkMG.
Import UG8z UPZI.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma le1_zxb : forall b : byte, le1 (Z_to_bv 64 (bv_unsigned b)) = [b].
Proof.
intros b. unfold le1. cbn [Z_to_le_bytes pf_mxd]. f_equal. apply bv_eq.
pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8)%Z with 256%Z in R.
rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256%Z. change (bv_modulus 64) with 18446744073709551616%Z.
Z.div_mod_to_equations. nia.
Qed.

Section PeStartT.
Variable HIx : heap_iface S4L.

#[using="Type"] Lemma start_mode : forall ss c hn, 0 <= ss <= 26 -> lvl_mode ST_start ss = Some (c, hn) -> ss = ST_start /\ c = CNone /\ hn = false.
Proof.
intros ss c hn Hss Hm. unfold lvl_mode, ST_start in Hm. cbn -[zin andb] in Hm.
cbn [zin existsb Z.eqb ws_states val_states esc_states app ST_eatws ST_start ST_finish ST_null ST_comment_start ST_comment ST_comment_eol ST_comment_end
ST_string ST_string_escape ST_escape_unicode ST_esc_need_escape ST_esc_need_u ST_boolean ST_number ST_array ST_array_add ST_array_sep
ST_ofs ST_ofield ST_ofend ST_ovalue ST_ovadd ST_osep ST_array_after_sep ST_ofs_after_sep ST_inf andb orb pf_mxd] in Hm.
assert (CASES : exists k : nat, (k <= 26)%nat /\ ss = Z.of_nat k) by (exists (Z.to_nat ss); split; lia).
destruct CASES as (k & Hk & Ek). rewrite Ek in Hm |- *. unfold ST_start.
do 27 (destruct k as [|k]; [cbn in Hm; first [discriminate Hm | injection Hm as <- <-; repeat split; reflexivity] |]). exfalso; lia.
Qed.

#[using="Type"] Lemma val_mode : forall st, zin st val_states = true -> lvl_mode st ST_start = Some (CNone, false).
Proof.
intros st H. unfold lvl_mode. cbn -[zin andb]. unfold zin in H |- *. cbn [existsb Z.eqb ST_start app ws_states val_states pf_mxd] in *.
unfold val_states, ST_start, ST_null, ST_boolean, ST_number, ST_inf, ST_string in H. cbn in H.
rewrite !Bool.orb_true_iff in H. rewrite !Z.eqb_eq in H.
destruct H as [H|[H|[H|[H|[H|[H|H]]]]]]; try (exfalso; exact (Bool.diff_false_true H) || discriminate H); subst st; reflexivity.
Qed.

#[using="Type"] Lemma seg_start_scalar :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel) (stn : Z)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a1 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_start ->
(stn = ST_boolean \/ stn = ST_inf \/ stn = ST_null) ->

(forall m' x1' a0' a1',
PE_INV HIx pf q LB0 payload me lo m' md A
(TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) (TL stn (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)))
(t_co ts) (t_pb ts) (t_pbs ts)
(TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts))
cb j1 j2 utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_REDO (t_co ts) x1' gp t0 t1 t2 a0' a1' (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m') md) T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x22b7c (t_co ts) x1 gp t0 t1 t2
(Z_to_bv 64 stn) a1 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a3 a4 a5 a6 a7
s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hst Hstn Kredo.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR. unfold pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold_consts.
assert (STN : 0 <= stn <= 26 /\ zin stn val_states = true) by (unfold ST_boolean, ST_inf, ST_null in Hstn; destruct Hstn as [->|[->| ->]]; (split; [lia | reflexivity])).
destruct STN as [STN VS]. stash Hstn.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, (32 * mxd)) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk S4L HIx _ _ _ _ q (32 * mxd) HP INq) as (_ & Hqal & Hqlo & Hqhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hqhi.
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND.
assert (Htq : tk <> q).
{ generalize ND; intros ND'. unfold pe_blocks in ND'. rewrite map_app in ND'. apply NoDup_app_remove_l in ND'.
cbn [map blk_addr fst pf_tk pf_md pf_mxd pf_fl] in ND'. apply List.NoDup_cons_iff in ND' as [Hni _]. intros E. apply Hni. left. symmetry. exact E. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tk 72 q (32 * mxd) HP INtk INq Htq) as Hdtq.

pose proof PB as (buf & bpos & cap & pre & post & Epbs & Lpre & PBC). pose proof PBC as (Hbpos & Hcap & _).
assert (INpb : In (pb, 16) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks, tstate_blocks, ts0; cbn [t_pbs pf_mxd]; rewrite Epbs; left; reflexivity).
assert (INbuf : In (buf, cap) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks, tstate_blocks, ts0; cbn [t_pbs pf_mxd]; rewrite Epbs; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ pb 16 HP INpb) as (_ & Hpbal & Hpblo & Hpbhi & _).
pose proof (heap_blk S4L HIx _ _ _ _ buf cap HP INbuf) as (_ & Hbufal & Hbuflo & Hbufhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hpbhi, Hbufhi.
assert (Hpbbuf : pb <> buf).
{ generalize ND; intros ND'. unfold pe_blocks, tstate_blocks, ts0 in ND'. cbn [t_pbs pf_mxd] in ND'. rewrite Epbs in ND'. cbn [map blk_addr fst app pf_mxd] in ND'.
apply List.NoDup_cons_iff in ND' as [Hni _]. intros E. apply Hni. left. symmetry. exact E. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ pb 16 buf cap HP INpb INbuf Hpbbuf) as Hdpb.
assert (Htkpb : tk <> pb /\ tk <> buf /\ q <> pb /\ q <> buf).
{ generalize ND; intros ND'. unfold pe_blocks, tstate_blocks, ts0 in ND'. cbn [t_pbs t_objbs t_levels pf_tk pf_md pf_mxd pf_fl] in ND'. rewrite Epbs in ND'.
assert (ND2 : List.NoDup (map blk_addr (([(pb, 16); (buf, cap)] ++ (objbs ++ concat (map lvl_blocks levels))) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0))) by exact ND'.
rewrite map_app in ND2.
repeat split; intros E.
- eapply (NoDup_app_in2 _ _ tk ND2); [rewrite E; cbn; left; reflexivity | cbn; left; reflexivity].
- eapply (NoDup_app_in2 _ _ tk ND2); [rewrite E; cbn; right; left; reflexivity | cbn; left; reflexivity].
- eapply (NoDup_app_in2 _ _ q ND2); [rewrite E; cbn; left; reflexivity | cbn; right; left; reflexivity].
- eapply (NoDup_app_in2 _ _ q ND2); [rewrite E; cbn; right; left; reflexivity | cbn; right; left; reflexivity]. }
destruct Htkpb as (Htkpb & Htkbuf & Hqpb & Hqbuf).
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tk 72 pb 16 HP INtk INpb Htkpb) as Hd1.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tk 72 buf cap HP INtk INbuf Htkbuf) as Hd2.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ q (32 * mxd) pb 16 HP INq INpb Hqpb) as Hd3.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ q (32 * mxd) buf cap HP INq INbuf Hqbuf) as Hd4.

stash Hd1. stash Hd2. stash Hd3. stash Hd4. stash Hdpb.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
pose proof (wmono_refl rsegs m) as WM.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
rewrite Hst in Hmode. destruct (start_mode _ _ _ SS26 Hmode) as (Ess & -> & ->).
pose proof (TSK depth l Hl) as Ld. unfold srec_cells in Ld.
remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (munch_refl [(bse, bse + 32)] m) as MU.
stash REST. stash TSK. clear HP LV PB.
apply rz_evt; [exact MOK|]. replace (q + 32 * Z.of_nat depth) with bse by lia.
step.
step.
step.

set (l' := TL stn (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
unstash REST. unstash TSK.
assert (HWA : Forall (pe_wtq (PEF tk oldl newl len lenr sb spf pmd mxd fl) q) [(bse, bse + 32)]) by (apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia | apply Forall_nil]).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TSKA : tstack rsegs mc q (lupd levels depth l'))
by (subst bse; eapply (tstack_put rsegs m _ q levels depth l' []); [exact TSK | (clear - LEN32 D32; lia) | exact MU | exact WM | intros; exact I | unfold srec_cells, l'; cbn [tl_st tl_ss tl_cur tl_name pf_mxd]; exact Ld]);
assert (RESTA : PE_REST HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A ts0 errv)
by (eapply (PE_REST_private_write HIx) with (ts := ts0) in REST; [exact REST | exact STC | exact MU | exact WM | exact MI | apply pe_wtq_private; exact HWA]);
assert (PBCA : pbuf_core rsegs mc pb buf bpos cap (pre ++ [Z_to_bv 8 0] ++ post))
by (unstash Hd3; unstash Hd4; eapply (pbuf_core_agree rsegs [(pb, 16); (buf, cap)]); [exact PBC | | left; reflexivity | right; left; reflexivity];
eapply agree_of_munch; [exact MU | exact WM |]; intros a n [E|[E|[]]]; injection E as <- <-; cbn; (clear - D32 Hd3 Hbse Hd4; lia))
end.
clear REST TSK MU WM Ld PBC.
eapply evt_cut; [eapply printbuf_reset_P; [exact PBCA | lia | lia | lia | lia | lia | unstash Hdpb; exact Hdpb | exact MI] |].
intros ms1 (mr & -> & MUr & WMr & MIr & PBC1).
replace (ret_pc (Z_to_bv 64 0x22b88)) with (Z_to_bv 64 0x22b88) by (symmetry; apply ret_pc_even; [lia | reflexivity]).

assert (HWR : Forall (pe_private (PEF tk oldl newl len lenr sb spf pmd mxd fl) q pbs) [(buf, buf + 1); (pb + 8, pb + 12)]).
{ apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; unfold pe_private; cbn [fst snd pf_tk pf_spf pf_md pf_mxd pf_fl]; right; right; left.
- exists buf, cap. rewrite Epbs. split; [right; left; reflexivity | pose proof PBC1 as (_ & Hc & _); lia].
- exists pb, 16. rewrite Epbs. split; [left; reflexivity | lia]. }
assert (RESTR : PE_REST HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mr md A ts0 errv)
by (eapply (PE_REST_private_write HIx) with (ts := ts0) in RESTA; [exact RESTA | exact STC | exact MUr | exact WMr | exact MIr | exact HWR]).
eapply (rw_cells_transport rsegs _ m0 mr) in TOK; [| exact MUr | exact WMr | unstash Hd1; unstash Hd2; cbn; lia].
eapply (rw_cells_transport rsegs _ m0 mr) in FR; [| exact MUr | exact WMr | cbn; lia].
assert (TSKR : tstack rsegs mr q (lupd levels depth l')).
{ unstash Hd3. unstash Hd4. eapply (tstack_transport rsegs); [exact TSKA | exact MUr | exact WMr |]. intros j Hj. rewrite lupd_length, LEN32 in Hj. cbn. (clear - Hcap Hd3 Hd4 Hj; lia). }
clear RESTA TSKA PBCA MI MUr WMr.

pose proof (wmono_refl rsegs mr) as WM. pose proof (munch_refl [(tk, tk + 72)] mr) as MU.
stash RESTR. stash TSKR. stash PBC1.
stepz. step.
unstash RESTR. unstash TSKR. unstash PBC1.
assert (HWB : Forall (pe_wtf (PEF tk oldl newl len lenr sb spf pmd mxd fl)) [(tk, tk + 72)]) by (apply Forall_cons; [left; cbn [fst snd pf_tk pf_md pf_mxd pf_fl]; lia | apply Forall_nil]).
apply evt_RZ_done. rewrite <- Hbse in Kredo. eapply Kredo.
lazymatch goal with |- PE_INV _ _ _ _ _ _ _ ?mc _ _ _ _ _ _ _ _ _ =>
assert (RESTB : PE_REST HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A ts0 errv)
by (eapply (PE_REST_private_write HIx) with (ts := ts0) in RESTR; [exact RESTR | exact STC | exact MU | exact WM | exact MIr | apply pe_wtf_private; exact HWB]);
assert (TSKB : tstack rsegs mc q (lupd levels depth l'))
by (eapply (tstack_transport rsegs); [exact TSKR | exact MU | exact WM |]; intros j Hj; rewrite lupd_length, LEN32 in Hj; cbn; (clear - Hdtq Hj; lia));
assert (PBCB : pbuf_core rsegs mc pb buf 0 cap ([Z_to_bv 8 0] ++ skipn 1 (pre ++ [Z_to_bv 8 0] ++ post)))
by (unstash Hd1; unstash Hd2; eapply (pbuf_core_agree rsegs [(pb, 16); (buf, cap)]); [exact PBC1 | | left; reflexivity | right; left; reflexivity];
eapply agree_of_munch; [exact MU | exact WM |]; intros a n [E|[E|[]]]; injection E as <- <-; cbn; (clear - Hd1 Hd2; lia))
end.
split.
- unfold PE_CORE. cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj ts_choff ts_isd ts_stpos ts_err ts_ucs ts_high ts_quote pf_len pf_tk pf_spf pf_md pf_mxd pf_fl].
split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [unfold tok_cells, tok_cells_g; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd]; exact TOK|].
split; [| split; [exact Hpb | split; [exact TSKB | unfold pe_frame; exact FR]]].
exists buf, 0, cap, [], (skipn 1 (pre ++ [Z_to_bv 8 0] ++ post)). split; [exact Epbs|]. split; [reflexivity|]. exact PBCB.
- destruct RESTB as (HP' & LV' & OBJ' & ST' & ERR' & STR' & PLEN' & SBin' & HPR' & MDV' & JCG').
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd].
split.
{ match goal with |- HEAP _ _ _ ?L _ _ => replace L with (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0); [exact HP' |] end.
unfold pe_blocks, tstate_blocks, ts0; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd].
fold l'. rewrite (map_lupd_same lvl_blocks levels depth l' l Hl) by reflexivity. reflexivity. }
split; [| split; [| split; [exact ST' | split; [exact ERR' | split; [exact STR' | split; [exact PLEN' | split; [exact SBin' | split; [exact HPR' | split; [exact MDV' | exact JCG']]]]]]]]].
+ cbn [t_levels t_depth pf_mxd]. intros i li Hli. destruct (PeanoNat.Nat.eq_dec i depth) as [-> | NE].
* rewrite nth_error_lupd_eq in Hli by lia. injection Hli as <-.
eapply lvl_cur_restate with (c' := CNone); [exact (LV' depth l Hl) | rewrite Hst; exact Hmode | | exact STN | exact SS26 | left; reflexivity].
rewrite Ess. apply val_mode. exact VS.
* rewrite nth_error_lupd_neq in Hli by congruence. exact (LV' i li Hli).
+ revert OBJ'. unfold cur_st, ts0. cbn [t_levels t_depth t_objs t_objbs t_obj pf_mxd]. rewrite nth_error_lupd_eq by lia. cbn [tl_st l' pf_mxd].
rewrite Hl, Hst. unstash Hstn. replace (zin stn [ST_array_add; ST_ovadd]) with false by (destruct Hstn as [->|[->| ->]]; reflexivity). cbn. intros E; exact E.
Qed.

#[using="Type"] Lemma seg_start_number :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a1 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_start ->

(forall m' x1' a0' a1',
PE_INV HIx pf q LB0 payload me lo m' md A
(TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) (TL ST_number (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)))
(t_co ts) (t_pb ts) (t_pbs ts)
(TS (Z_to_bv 64 0) (ts_stpos (t_x ts)) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))
(t_obj ts) (t_objs ts) (t_objbs ts))
cb j1 j2 utf sv errv ->
pbufc rsegs m' (t_pbs ts) (t_pb ts) [] ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_REDO (t_co ts) x1' gp t0 t1 t2 a0' a1' (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m') md) T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x224ac (t_co ts) x1 gp t0 t1 t2
(Z_to_bv 64 0) a1 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a3 a4 a5 a6 a7
s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hst Kredo.
assert (Hstn : ST_number = ST_number) by reflexivity. set (stn := ST_number) in *.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR. unfold pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold_consts.
assert (STN : 0 <= stn <= 26 /\ zin stn val_states = true) by (subst stn; unfold ST_number; split; [lia | reflexivity]).
destruct STN as [STN VS]. stash Hstn.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, (32 * mxd)) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk S4L HIx _ _ _ _ q (32 * mxd) HP INq) as (_ & Hqal & Hqlo & Hqhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hqhi.
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND.
assert (Htq : tk <> q).
{ generalize ND; intros ND'. unfold pe_blocks in ND'. rewrite map_app in ND'. apply NoDup_app_remove_l in ND'.
cbn [map blk_addr fst pf_tk pf_md pf_mxd pf_fl] in ND'. apply List.NoDup_cons_iff in ND' as [Hni _]. intros E. apply Hni. left. symmetry. exact E. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tk 72 q (32 * mxd) HP INtk INq Htq) as Hdtq.

pose proof PB as (buf & bpos & cap & pre & post & Epbs & Lpre & PBC). pose proof PBC as (Hbpos & Hcap & _).
assert (INpb : In (pb, 16) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks, tstate_blocks, ts0; cbn [t_pbs pf_mxd]; rewrite Epbs; left; reflexivity).
assert (INbuf : In (buf, cap) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks, tstate_blocks, ts0; cbn [t_pbs pf_mxd]; rewrite Epbs; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ pb 16 HP INpb) as (_ & Hpbal & Hpblo & Hpbhi & _).
pose proof (heap_blk S4L HIx _ _ _ _ buf cap HP INbuf) as (_ & Hbufal & Hbuflo & Hbufhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hpbhi, Hbufhi.
assert (Hpbbuf : pb <> buf).
{ generalize ND; intros ND'. unfold pe_blocks, tstate_blocks, ts0 in ND'. cbn [t_pbs pf_mxd] in ND'. rewrite Epbs in ND'. cbn [map blk_addr fst app pf_mxd] in ND'.
apply List.NoDup_cons_iff in ND' as [Hni _]. intros E. apply Hni. left. symmetry. exact E. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ pb 16 buf cap HP INpb INbuf Hpbbuf) as Hdpb.
assert (Htkpb : tk <> pb /\ tk <> buf /\ q <> pb /\ q <> buf).
{ generalize ND; intros ND'. unfold pe_blocks, tstate_blocks, ts0 in ND'. cbn [t_pbs t_objbs t_levels pf_tk pf_md pf_mxd pf_fl] in ND'. rewrite Epbs in ND'.
assert (ND2 : List.NoDup (map blk_addr (([(pb, 16); (buf, cap)] ++ (objbs ++ concat (map lvl_blocks levels))) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0))) by exact ND'.
rewrite map_app in ND2.
repeat split; intros E.
- eapply (NoDup_app_in2 _ _ tk ND2); [rewrite E; cbn; left; reflexivity | cbn; left; reflexivity].
- eapply (NoDup_app_in2 _ _ tk ND2); [rewrite E; cbn; right; left; reflexivity | cbn; left; reflexivity].
- eapply (NoDup_app_in2 _ _ q ND2); [rewrite E; cbn; left; reflexivity | cbn; right; left; reflexivity].
- eapply (NoDup_app_in2 _ _ q ND2); [rewrite E; cbn; right; left; reflexivity | cbn; right; left; reflexivity]. }
destruct Htkpb as (Htkpb & Htkbuf & Hqpb & Hqbuf).
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tk 72 pb 16 HP INtk INpb Htkpb) as Hd1.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tk 72 buf cap HP INtk INbuf Htkbuf) as Hd2.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ q (32 * mxd) pb 16 HP INq INpb Hqpb) as Hd3.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ q (32 * mxd) buf cap HP INq INbuf Hqbuf) as Hd4.

stash Hd1. stash Hd2. stash Hd3. stash Hd4. stash Hdpb.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
pose proof (wmono_refl rsegs m) as WM.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
rewrite Hst in Hmode. destruct (start_mode _ _ _ SS26 Hmode) as (Ess & -> & ->).
pose proof (TSK depth l Hl) as Ld. unfold srec_cells in Ld.
remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (munch_refl [(bse, bse + 32)] m) as MU.
stash REST. stash TSK. clear HP LV PB.
apply rz_evt; [exact MOK|]. replace (q + 32 * Z.of_nat depth) with bse by lia.
step. step. lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => first [replace c with true by (vm_compute; reflexivity) | replace c with false by (vm_compute; reflexivity)]; cbv iota end. step. step.
step.
step.

set (l' := TL stn (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
unstash REST. unstash TSK.
assert (HWA : Forall (pe_wtq (PEF tk oldl newl len lenr sb spf pmd mxd fl) q) [(bse, bse + 32)]) by (apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia | apply Forall_nil]).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TSKA : tstack rsegs mc q (lupd levels depth l'))
by (subst bse; eapply (tstack_put rsegs m _ q levels depth l' []); [exact TSK | (clear - LEN32 D32; lia) | exact MU | exact WM | intros; exact I | unfold srec_cells, l'; cbn [tl_st tl_ss tl_cur tl_name pf_mxd]; unfold ST_number; exact Ld]);
assert (RESTA : PE_REST HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A ts0 errv)
by (eapply (PE_REST_private_write HIx) with (ts := ts0) in REST; [exact REST | exact STC | exact MU | exact WM | exact MI | apply pe_wtq_private; exact HWA]);
assert (PBCA : pbuf_core rsegs mc pb buf bpos cap (pre ++ [Z_to_bv 8 0] ++ post))
by (unstash Hd3; unstash Hd4; eapply (pbuf_core_agree rsegs [(pb, 16); (buf, cap)]); [exact PBC | | left; reflexivity | right; left; reflexivity];
eapply agree_of_munch; [exact MU | exact WM |]; intros a n [E|[E|[]]]; injection E as <- <-; cbn; (clear - D32 Hd3 Hbse Hd4; lia))
end.
clear REST TSK MU WM Ld PBC.
eapply evt_cut; [eapply printbuf_reset_P; [exact PBCA | lia | lia | lia | lia | lia | unstash Hdpb; exact Hdpb | exact MI] |].
intros ms1 (mr & -> & MUr & WMr & MIr & PBC1).
replace (ret_pc (Z_to_bv 64 0x224c8)) with (Z_to_bv 64 0x224c8) by (symmetry; apply ret_pc_even; [lia | reflexivity]).

assert (HWR : Forall (pe_private (PEF tk oldl newl len lenr sb spf pmd mxd fl) q pbs) [(buf, buf + 1); (pb + 8, pb + 12)]).
{ apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; unfold pe_private; cbn [fst snd pf_tk pf_spf pf_md pf_mxd pf_fl]; right; right; left.
- exists buf, cap. rewrite Epbs. split; [right; left; reflexivity | pose proof PBC1 as (_ & Hc & _); lia].
- exists pb, 16. rewrite Epbs. split; [left; reflexivity | lia]. }
assert (RESTR : PE_REST HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mr md A ts0 errv)
by (eapply (PE_REST_private_write HIx) with (ts := ts0) in RESTA; [exact RESTA | exact STC | exact MUr | exact WMr | exact MIr | exact HWR]).
eapply (rw_cells_transport rsegs _ m0 mr) in TOK; [| exact MUr | exact WMr | unstash Hd1; unstash Hd2; cbn; lia].
eapply (rw_cells_transport rsegs _ m0 mr) in FR; [| exact MUr | exact WMr | cbn; lia].
assert (TSKR : tstack rsegs mr q (lupd levels depth l')).
{ unstash Hd3. unstash Hd4. eapply (tstack_transport rsegs); [exact TSKA | exact MUr | exact WMr |]. intros j Hj. rewrite lupd_length, LEN32 in Hj. cbn. (clear - Hcap Hd3 Hd4 Hj; lia). }
clear RESTA TSKA PBCA MI MUr WMr.

pose proof (wmono_refl rsegs mr) as WM. pose proof (munch_refl [(tk, tk + 72)] mr) as MU.
stash RESTR. stash TSKR. stash PBC1.
stepz. step.
unstash RESTR. unstash TSKR. unstash PBC1.
assert (HWB : Forall (pe_wtf (PEF tk oldl newl len lenr sb spf pmd mxd fl)) [(tk, tk + 72)]) by (apply Forall_cons; [left; cbn [fst snd pf_tk pf_md pf_mxd pf_fl]; lia | apply Forall_nil]).
apply evt_RZ_done. rewrite <- Hbse in Kredo. eapply Kredo.
lazymatch goal with |- PE_INV _ _ _ _ _ _ _ ?mc _ _ _ _ _ _ _ _ _ =>
assert (RESTB : PE_REST HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A ts0 errv)
by (eapply (PE_REST_private_write HIx) with (ts := ts0) in RESTR; [exact RESTR | exact STC | exact MU | exact WM | exact MIr | apply pe_wtf_private; exact HWB]);
assert (TSKB : tstack rsegs mc q (lupd levels depth l'))
by (eapply (tstack_transport rsegs); [exact TSKR | exact MU | exact WM |]; intros j Hj; rewrite lupd_length, LEN32 in Hj; cbn; lia);
assert (PBCB : pbuf_core rsegs mc pb buf 0 cap ([Z_to_bv 8 0] ++ skipn 1 (pre ++ [Z_to_bv 8 0] ++ post)))
by (unstash Hd1; unstash Hd2; eapply (pbuf_core_agree rsegs [(pb, 16); (buf, cap)]); [exact PBC1 | | left; reflexivity | right; left; reflexivity];
eapply agree_of_munch; [exact MU | exact WM |]; intros a n [E|[E|[]]]; injection E as <- <-; cbn; lia)
end.
2: { cbn [t_pbs t_pb pf_mxd]. exists buf, 0, cap, (skipn 1 (pre ++ [Z_to_bv 8 0] ++ post)). split; [exact Epbs|]. split; [reflexivity|].
unstash Hd1; unstash Hd2; eapply (pbuf_core_agree rsegs [(pb, 16); (buf, cap)]); [exact PBC1 | | left; reflexivity | right; left; reflexivity];
eapply agree_of_munch; [exact MU | exact WM |]; intros a n [E|[E|[]]]; injection E as <- <-; cbn; lia. }
split.
- unfold PE_CORE. cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj ts_choff ts_isd ts_stpos ts_err ts_ucs ts_high ts_quote pf_len pf_tk pf_spf pf_md pf_mxd pf_fl].
split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [unfold tok_cells, tok_cells_g; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd]; exact TOK|].
split; [| split; [exact Hpb | split; [exact TSKB | unfold pe_frame; exact FR]]].
exists buf, 0, cap, [], (skipn 1 (pre ++ [Z_to_bv 8 0] ++ post)). split; [exact Epbs|]. split; [reflexivity|]. exact PBCB.
- destruct RESTB as (HP' & LV' & OBJ' & ST' & ERR' & STR' & PLEN' & SBin' & HPR' & MDV' & JCG').
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd].
split.
{ match goal with |- HEAP _ _ _ ?L _ _ => replace L with (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0); [exact HP' |] end.
unfold pe_blocks, tstate_blocks, ts0; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd].
fold l'. rewrite (map_lupd_same lvl_blocks levels depth l' l Hl) by reflexivity. reflexivity. }
split; [| split; [| split; [exact ST' | split; [exact ERR' | split; [exact STR' | split; [exact PLEN' | split; [exact SBin' | split; [exact HPR' | split; [exact MDV' | exact JCG']]]]]]]]].
+ cbn [t_levels t_depth pf_mxd]. intros i li Hli. destruct (PeanoNat.Nat.eq_dec i depth) as [-> | NE].
* rewrite nth_error_lupd_eq in Hli by lia. injection Hli as <-.
eapply lvl_cur_restate with (c' := CNone); [exact (LV' depth l Hl) | rewrite Hst; exact Hmode | | unfold ST_number; lia | exact SS26 | left; reflexivity].
rewrite Ess. apply val_mode. reflexivity.
* rewrite nth_error_lupd_neq in Hli by congruence. exact (LV' i li Hli).
+ revert OBJ'. unfold cur_st, ts0. cbn [t_levels t_depth t_objs t_objbs t_obj pf_mxd]. rewrite nth_error_lupd_eq by lia. cbn [tl_st l' pf_mxd].
rewrite Hl, Hst. cbn. intros E; exact E.
Qed.

#[using="Type"] Lemma seg_start_string :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate) (l : tlevel)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a1 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_start ->

(forall m' x1' a0' a1',
PE_INV HIx pf q LB0 payload me lo m' md A
(TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) (TL ST_string (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)))
(t_co ts) (t_pb ts) (t_pbs ts)
(TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) cb)
(t_obj ts) (t_objs ts) (t_objbs ts))
cb j1 j2 utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK2 (t_co ts) x1' gp t0 t1 t2 a0' a1' (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m') md) T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x23b60 (t_co ts) x1 gp t0 t1 t2
(Z_to_bv 64 0) a1 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a3 a4 a5 a6 a7
s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hst Kbreak.
assert (Hstn : ST_string = ST_string) by reflexivity. set (stn := ST_string) in *.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR. unfold pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold_consts.
assert (STN : 0 <= stn <= 26 /\ zin stn val_states = true) by (subst stn; unfold ST_string; split; [lia | reflexivity]).
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
destruct STN as [STN VS]. stash Hstn.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, (32 * mxd)) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk S4L HIx _ _ _ _ q (32 * mxd) HP INq) as (_ & Hqal & Hqlo & Hqhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hqhi.
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND.
assert (Htq : tk <> q).
{ generalize ND; intros ND'. unfold pe_blocks in ND'. rewrite map_app in ND'. apply NoDup_app_remove_l in ND'.
cbn [map blk_addr fst pf_tk pf_md pf_mxd pf_fl] in ND'. apply List.NoDup_cons_iff in ND' as [Hni _]. intros E. apply Hni. left. symmetry. exact E. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tk 72 q (32 * mxd) HP INtk INq Htq) as Hdtq.

pose proof PB as (buf & bpos & cap & pre & post & Epbs & Lpre & PBC). pose proof PBC as (Hbpos & Hcap & _).
assert (INpb : In (pb, 16) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks, tstate_blocks, ts0; cbn [t_pbs pf_mxd]; rewrite Epbs; left; reflexivity).
assert (INbuf : In (buf, cap) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks, tstate_blocks, ts0; cbn [t_pbs pf_mxd]; rewrite Epbs; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ pb 16 HP INpb) as (_ & Hpbal & Hpblo & Hpbhi & _).
pose proof (heap_blk S4L HIx _ _ _ _ buf cap HP INbuf) as (_ & Hbufal & Hbuflo & Hbufhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hpbhi, Hbufhi.
assert (Hpbbuf : pb <> buf).
{ generalize ND; intros ND'. unfold pe_blocks, tstate_blocks, ts0 in ND'. cbn [t_pbs pf_mxd] in ND'. rewrite Epbs in ND'. cbn [map blk_addr fst app pf_mxd] in ND'.
apply List.NoDup_cons_iff in ND' as [Hni _]. intros E. apply Hni. left. symmetry. exact E. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ pb 16 buf cap HP INpb INbuf Hpbbuf) as Hdpb.
assert (Htkpb : tk <> pb /\ tk <> buf /\ q <> pb /\ q <> buf).
{ generalize ND; intros ND'. unfold pe_blocks, tstate_blocks, ts0 in ND'. cbn [t_pbs t_objbs t_levels pf_tk pf_md pf_mxd pf_fl] in ND'. rewrite Epbs in ND'.
assert (ND2 : List.NoDup (map blk_addr (([(pb, 16); (buf, cap)] ++ (objbs ++ concat (map lvl_blocks levels))) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0))) by exact ND'.
rewrite map_app in ND2.
repeat split; intros E.
- eapply (NoDup_app_in2 _ _ tk ND2); [rewrite E; cbn; left; reflexivity | cbn; left; reflexivity].
- eapply (NoDup_app_in2 _ _ tk ND2); [rewrite E; cbn; right; left; reflexivity | cbn; left; reflexivity].
- eapply (NoDup_app_in2 _ _ q ND2); [rewrite E; cbn; left; reflexivity | cbn; right; left; reflexivity].
- eapply (NoDup_app_in2 _ _ q ND2); [rewrite E; cbn; right; left; reflexivity | cbn; right; left; reflexivity]. }
destruct Htkpb as (Htkpb & Htkbuf & Hqpb & Hqbuf).
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tk 72 pb 16 HP INtk INpb Htkpb) as Hd1.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tk 72 buf cap HP INtk INbuf Htkbuf) as Hd2.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ q (32 * mxd) pb 16 HP INq INpb Hqpb) as Hd3.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ q (32 * mxd) buf cap HP INq INbuf Hqbuf) as Hd4.

stash Hd1. stash Hd2. stash Hd3. stash Hd4. stash Hdpb.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
pose proof (wmono_refl rsegs m) as WM.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
rewrite Hst in Hmode. destruct (start_mode _ _ _ SS26 Hmode) as (Ess & -> & ->).
pose proof (TSK depth l Hl) as Ld. unfold srec_cells in Ld.
remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (munch_refl [(bse, bse + 32)] m) as MU.
stash REST. stash TSK. clear HP LV PB.
apply rz_evt; [exact MOK|]. replace (q + 32 * Z.of_nat depth) with bse by lia.
step. step. lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => first [replace c with true by (vm_compute; reflexivity) | replace c with false by (vm_compute; reflexivity)]; cbv iota end. step. step.
step.
step.

set (l' := TL stn (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
unstash REST. unstash TSK.
assert (HWA : Forall (pe_wtq (PEF tk oldl newl len lenr sb spf pmd mxd fl) q) [(bse, bse + 32)]) by (apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia | apply Forall_nil]).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TSKA : tstack rsegs mc q (lupd levels depth l'))
by (subst bse; eapply (tstack_put rsegs m _ q levels depth l' []); [exact TSK | (clear - LEN32 D32; lia) | exact MU | exact WM | intros; exact I | unfold srec_cells, l'; cbn [tl_st tl_ss tl_cur tl_name pf_mxd]; unfold ST_string; exact Ld]);
assert (RESTA : PE_REST HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A ts0 errv)
by (eapply (PE_REST_private_write HIx) with (ts := ts0) in REST; [exact REST | exact STC | exact MU | exact WM | exact MI | apply pe_wtq_private; exact HWA]);
assert (PBCA : pbuf_core rsegs mc pb buf bpos cap (pre ++ [Z_to_bv 8 0] ++ post))
by (unstash Hd3; unstash Hd4; eapply (pbuf_core_agree rsegs [(pb, 16); (buf, cap)]); [exact PBC | | left; reflexivity | right; left; reflexivity];
eapply agree_of_munch; [exact MU | exact WM |]; intros a n [E|[E|[]]]; injection E as <- <-; cbn; (clear - D32 Hd3 Hbse Hd4; lia))
end.
clear REST TSK MU WM Ld PBC.
eapply evt_cut; [eapply printbuf_reset_P; [exact PBCA | lia | lia | lia | lia | lia | unstash Hdpb; exact Hdpb | exact MI] |].
intros ms1 (mr & -> & MUr & WMr & MIr & PBC1).
replace (ret_pc (Z_to_bv 64 0x23b78)) with (Z_to_bv 64 0x23b78) by (symmetry; apply ret_pc_even; [lia | reflexivity]).

assert (HWR : Forall (pe_private (PEF tk oldl newl len lenr sb spf pmd mxd fl) q pbs) [(buf, buf + 1); (pb + 8, pb + 12)]).
{ apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; unfold pe_private; cbn [fst snd pf_tk pf_spf pf_md pf_mxd pf_fl]; right; right; left.
- exists buf, cap. rewrite Epbs. split; [right; left; reflexivity | pose proof PBC1 as (_ & Hc & _); lia].
- exists pb, 16. rewrite Epbs. split; [left; reflexivity | lia]. }
assert (RESTR : PE_REST HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mr md A ts0 errv)
by (eapply (PE_REST_private_write HIx) with (ts := ts0) in RESTA; [exact RESTA | exact STC | exact MUr | exact WMr | exact MIr | exact HWR]).
eapply (rw_cells_transport rsegs _ m0 mr) in TOK; [| exact MUr | exact WMr | unstash Hd1; unstash Hd2; cbn; lia].
eapply (rw_cells_transport rsegs _ m0 mr) in FR; [| exact MUr | exact WMr | cbn; lia].
assert (TSKR : tstack rsegs mr q (lupd levels depth l')).
{ unstash Hd3. unstash Hd4. eapply (tstack_transport rsegs); [exact TSKA | exact MUr | exact WMr |]. intros j Hj. rewrite lupd_length, LEN32 in Hj. cbn. (clear - Hcap Hd3 Hd4 Hj; lia). }
clear RESTA TSKA PBCA MI MUr WMr.

pose proof (wmono_refl rsegs mr) as WM. pose proof (munch_refl [(tk, tk + 72)] mr) as MU.
stash RESTR. stash TSKR. stash PBC1.
step. change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)). step. rewrite le1_zxb. mem_after_store. step.
unstash RESTR. unstash TSKR. unstash PBC1.
assert (HWB : Forall (pe_wtf (PEF tk oldl newl len lenr sb spf pmd mxd fl)) [(tk, tk + 72)]) by (apply Forall_cons; [left; cbn [fst snd pf_tk pf_md pf_mxd pf_fl]; lia | apply Forall_nil]).
apply evt_RZ_done. rewrite <- Hbse in Kbreak. eapply Kbreak.
lazymatch goal with |- PE_INV _ _ _ _ _ _ _ ?mc _ _ _ _ _ _ _ _ _ =>
assert (RESTB : PE_REST HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A ts0 errv)
by (eapply (PE_REST_private_write HIx) with (ts := ts0) in RESTR; [exact RESTR | exact STC | exact MU | exact WM | exact MIr | apply pe_wtf_private; exact HWB]);
assert (TSKB : tstack rsegs mc q (lupd levels depth l'))
by (eapply (tstack_transport rsegs); [exact TSKR | exact MU | exact WM |]; intros j Hj; rewrite lupd_length, LEN32 in Hj; cbn; (clear - Hdtq Hj; lia));
assert (PBCB : pbuf_core rsegs mc pb buf 0 cap ([Z_to_bv 8 0] ++ skipn 1 (pre ++ [Z_to_bv 8 0] ++ post)))
by (unstash Hd1; unstash Hd2; eapply (pbuf_core_agree rsegs [(pb, 16); (buf, cap)]); [exact PBC1 | | left; reflexivity | right; left; reflexivity];
eapply agree_of_munch; [exact MU | exact WM |]; intros a n [E|[E|[]]]; injection E as <- <-; cbn; (clear - Hd1 Hd2; lia))
end.
split.
- unfold PE_CORE. cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj ts_choff ts_isd ts_stpos ts_err ts_ucs ts_high ts_quote pf_len pf_tk pf_spf pf_md pf_mxd pf_fl].
split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [unfold tok_cells, tok_cells_g; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd]; exact TOK|].
split; [| split; [exact Hpb | split; [exact TSKB | unfold pe_frame; exact FR]]].
exists buf, 0, cap, [], (skipn 1 (pre ++ [Z_to_bv 8 0] ++ post)). split; [exact Epbs|]. split; [reflexivity|]. exact PBCB.
- destruct RESTB as (HP' & LV' & OBJ' & ST' & ERR' & STR' & PLEN' & SBin' & HPR' & MDV' & JCG').
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd].
split.
{ match goal with |- HEAP _ _ _ ?L _ _ => replace L with (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0); [exact HP' |] end.
unfold pe_blocks, tstate_blocks, ts0; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd].
fold l'. rewrite (map_lupd_same lvl_blocks levels depth l' l Hl) by reflexivity. reflexivity. }
split; [| split; [| split; [exact ST' | split; [exact ERR' | split; [exact STR' | split; [exact PLEN' | split; [exact SBin' | split; [exact HPR' | split; [exact MDV' | exact JCG']]]]]]]]].
+ cbn [t_levels t_depth pf_mxd]. intros i li Hli. destruct (PeanoNat.Nat.eq_dec i depth) as [-> | NE].
* rewrite nth_error_lupd_eq in Hli by lia. injection Hli as <-.
eapply lvl_cur_restate with (c' := CNone); [exact (LV' depth l Hl) | rewrite Hst; exact Hmode | | unfold ST_string; lia | exact SS26 | left; reflexivity].
rewrite Ess. apply val_mode. reflexivity.
* rewrite nth_error_lupd_neq in Hli by congruence. exact (LV' i li Hli).
+ revert OBJ'. unfold cur_st, ts0. cbn [t_levels t_depth t_objs t_objbs t_obj pf_mxd]. rewrite nth_error_lupd_eq by lia. cbn [tl_st l' pf_mxd].
rewrite Hl, Hst. cbn. intros E; exact E.
Qed.

End PeStartT.

End RC__1.
End Mq7.

