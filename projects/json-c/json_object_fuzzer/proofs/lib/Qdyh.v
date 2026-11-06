(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA QEpW QZDE QbVh QlEo_c1 QWxq_c1 QXup QEQM QRjH QHnV QCcH QfLs Q0Ek Qtgi QjDH QC8c Qsw7 QkMG QG8z QPZI Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QsjA QEpW QZDE QbVh QlEo_c1 QWxq_c1 QXup.
Import QEQM.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0.
Import QC8c.Mq0.
Import Qsw7 QkMG.
Import QG8z QPZI.Mq0.
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
rw_cells rsegs m (0x75e70 - 164) [C4 errv] /\
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
rw_cells rsegs m2 (0x75e70 - 164) [C4 errv2] ->
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
rw_cells rsegs m2 (0x75e70 - 164) [C4 errv2] ->
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
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import QEQM.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0.
Import QC8c.Mq0.
Import Qsw7 QJjn QkMG.
Import QG8z.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeBreak.
Variable HIx : heap_iface S4L.

#[using="Type"] Lemma seg_break2 :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (av : Z),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
t_co ts < pf_len pf ->
0 <= av < 2^64 -> (av = 0 <-> bv_unsigned cb = 0) ->

(forall m' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
bv_unsigned cb = 0 ->
PE_INV HIx pf q LB0 payload me lo m' md A (ts_set_co ts (t_co ts + 1)) cb j1 j2 utf sv errv ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_OUT (t_co ts + 1) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md) T) ->

(forall m' x1' gp' t0' t1' t2' a0' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
bv_unsigned cb <> 0 ->
PE_INV HIx pf q LB0 payload me lo m' md A (ts_set_co ts (t_co ts + 1)) cb j1 j2 utf sv errv ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_LOOP (t_co ts + 1) x1' gp' t0' t1' t2' a0' (Z_to_bv 64 (t_co ts + 1)) a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md) T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK2 (t_co ts) x1 gp t0 t1 t2 (Z_to_bv 64 av) a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until av. intros STC INV Hco AVR AVZ Kout Kloop.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR. unfold pe_ms. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl].
unfold_consts.
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
apply rz_evt; [exact MOK|]. unfold PE_BREAK2.
step. norm_sx32. step. step. norm_w32. step.
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
destruct (Z.eq_dec av 0) as [Hc0 | Hc1].
- step. if_truex. apply evt_RZ_done. eapply Kout; [apply AVZ; exact Hc0 | exact INV' | apply fsaved_refl | intros Hf; exact Hf].
- step. if_falsex. step. apply evt_RZ_done. eapply Kloop; [intros E; apply Hc1; apply AVZ; exact E | exact INV' | apply fsaved_refl | intros Hf; exact Hf].
Qed.

#[using="Type"] Lemma seg_break :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
t_co ts < pf_len pf ->
(forall m' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
bv_unsigned cb = 0 ->
PE_INV HIx pf q LB0 payload me lo m' md A (ts_set_co ts (t_co ts + 1)) cb j1 j2 utf sv errv ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_OUT (t_co ts + 1) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md) T) ->
(forall m' x1' gp' t0' t1' t2' a0' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
bv_unsigned cb <> 0 ->
PE_INV HIx pf q LB0 payload me lo m' md A (ts_set_co ts (t_co ts + 1)) cb j1 j2 utf sv errv ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_LOOP (t_co ts + 1) x1' gp' t0' t1' t2' a0' (Z_to_bv 64 (t_co ts + 1)) a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md) T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK (t_co ts) x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hco Kout Kloop.
pose proof INV as [CORE REST]. pose proof CORE as (_ & _ & _ & _ & _ & _ & _ & _ & FR).
pose proof (proj1 REST) as HP. pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK. pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; unfold pe_frame in FR; unfold pe_ms in *; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
clear CORE REST HP.
apply rz_evt; [exact MOK|]. unfold PE_BREAK. step. change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)).
apply evt_RZ_done. pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
eapply (seg_break2 (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo _ md A ts); [exact STC | exact INV | exact Hco | lia | tauto | exact Kout | exact Kloop].
Qed.
End PeBreak.

End RC__1.
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import QEQM.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0.
Import QC8c.Mq0.
Import Qsw7 QJjn QkMG.
Import QG8z.
Import QJjn.Mq0.
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

#[using="Type"] Lemma seg_loop :
forall (pf : pe_fix) (q : Z) (LB0 : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (ts : tstate)
(cb : byte) (j1 j2 utf : list byte) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
(pf_lenr pf <> pf_len pf -> t_co ts < pf_len pf) ->

(forall m' (c : byte) (a0' : word) (j2' : list byte) x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some c ->
PE_INV HIx pf q LB0 payload me lo m' md A ts c j1 j2' utf sv errv ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_REDO (t_co ts) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md) T) ->

(forall m' (e : word) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc',
t_co ts = pf_len pf ->
PE_INV HIx pf q LB0 payload me lo m' md A (ts_set_err ts e) cb j1 j2 utf sv errv ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_OUT (t_co ts) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F' fc' m') md) T) ->

(forall x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6',
t_co ts < pf_len pf ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR (t_co ts) x1' gp' t0' t1' t2' (Z_to_bv 64 14) a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' F fc m) md) T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_LOOP (t_co ts) x1 gp t0 t1 t2 a0 (Z_to_bv 64 (t_co ts)) a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s10 t3 t4 t5 t6 F fc m) md) T.
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
subst lenr. pose (lenr := len). subst co. step. if_false.
pose proof (munch_refl [(tk, tk + 72)] m) as MU.
step. step. norm_sx32.

assert (TAIL : forall (e : word) mc x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6',
rw_cells rsegs mc tk
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 (Z.of_nat depth)); C4 isd; C4 stpos;
C4 (Z_to_bv 64 len); C4 e; C4 ucs; C4 high; C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)] ->
rw_cells rsegs mc spf [C8 (Z_to_bv 64 obj); CB 16 j1; C4 (nbw j2); CB 3 (skipn 4 j2); C1 cb; CB 8 utf;
C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv); C8 (pe_s7 sv); C8 (pe_s6 sv);
C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)] ->
munch [(tk, tk + 72)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
evt rsegs (RZ rsegs md T)
(MS (mkR x1' (Z_to_bv 64 spf) gp (Z_to_bv 64 482928) t0' t1' t2' (Z_to_bv 64 tk) (Z_to_bv 64 oldl) a0' a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4' s5' s6' (Z_to_bv 64 26) s8' (Z_to_bv 64 (sb + len)) s10' (Z_to_bv 64 79024) t3' t4' t5' t6')
F (Z_to_bv 64 PE_OUT) fc None mc (seg_rom rsegs))).
{ intros e mc x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s10' t3' t4' t5' t6' TOK' FR' MU' WM' MI'.
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
destruct (PeanoNat.Nat.eq_dec depth 0) as [D0 | Dn].
+ subst depth. cbn [Z.of_nat pf_mxd] in TOK |- *. step. if_false.

destruct (nth_error levels 0) as [l0|] eqn:Hl0; [| apply nth_error_None in Hl0; lia].
pose proof (TSK 0%nat l0 Hl0) as L0. rewrite Z.mul_0_r, Z.add_0_r in L0. unfold srec_cells in L0.
pose proof (stash_i _ TSK) as TSK'. clear TSK. rename TSK' into TSK.
pose proof (LV 0%nat l0 Hl0) as (ST26 & SS26 & _).
step. step. norm_sx32.
destruct (Z.eq_dec (tl_st l0) 0) as [S0 | Sn].
* rewrite S0. step. if_false. step. norm_sx32. step.
destruct (Z.eq_dec (tl_ss l0) 2) as [F2 | Fn].
-- rewrite F2. step. if_true. stepz. step. unstash TSK. eapply TAIL; [exact TOK | exact FR | exact MU | exact WM | exact MI].
-- step. if_falsex. step. stepz. unstash TSK. eapply TAIL; [exact TOK | exact FR | exact MU | exact WM | exact MI].
* step. if_truex. step. stepz. unstash TSK. eapply TAIL; [exact TOK | exact FR | exact MU | exact WM | exact MI].
+ step. if_truex. step. stepz. eapply TAIL; [exact TOK | exact FR | exact MU | exact WM | exact MI].
-
assert (Hco : co < len) by lia.
destruct (nth_error payload (Z.to_nat co)) as [c|] eqn:Hc; [| apply nth_error_None in Hc; lia].
pose proof (tok_flags_byte_g mxd fl m tk pb (Z.of_nat depth) q (TS isd stpos (Z_to_bv 64 co) err ucs high quote) TOK) as RDF.
pose proof (payload_byte _ _ _ _ _ STR Hc ltac:(lia)) as RDC.
pose proof (bv_unsigned_in_range 8 c) as CBR; unfold bv_modulus in CBR; cbn in CBR.

assert (JOINR : forall mc (av a1x a2x nv : word),
le1 av = [c] ->
rw_cells rsegs mc spf [C8 (Z_to_bv 64 obj); CB 16 j1; C4 nv; CB 3 (skipn 4 j2); C1 cb; CB 8 utf;
C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv); C8 (pe_s7 sv); C8 (pe_s6 sv);
C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)] ->
munch [(spf, spf + 144)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
evt rsegs (RZ rsegs md T)
(MS (mkR x1 (Z_to_bv 64 spf) gp (Z_to_bv 64 482928) t0 t1 t2 (Z_to_bv 64 tk) (Z_to_bv 64 oldl) av a1x a2x a3 a4 a5 a6 a7
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4 s5 s6 (Z_to_bv 64 26) s8 (Z_to_bv 64 (sb + co)) s10 (Z_to_bv 64 79024) t3 t4 t5 t6)
F (Z_to_bv 64 0x2193c) fc None mc (seg_rom rsegs))).
{ intros mc av a1x a2x nv Hav FRj MUj WMj MIj.
assert (TOKj : rw_cells rsegs mc tk (tok_cells_g mxd fl pb (Z.of_nat depth) q (TS isd stpos (Z_to_bv 64 co) err ucs high quote))).
{ eapply rw_cells_transport; [exact TOK | exact MUj | exact WMj | unfold tok_cells_g; cbn; lia]. }
clear RDF RDC. step. rewrite Hav. mem_after_store.
unstash PB. unstash REST.
assert (HW : Forall (pe_wtf (PEF tk oldl newl len lenr sb spf pmd mxd fl)) [(spf, spf + 144)]) by (apply Forall_cons; [right; unfold PE_FRAME; cbn [pf_spf pf_tk fst snd pf_md pf_mxd pf_fl]; split; [apply Z.le_refl | apply Z.le_refl] | apply Forall_nil]).
lazymatch goal with H : munch _ m ?mf |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
rename H into MUf;
lazymatch goal with W : wmono rsegs m mf |- _ => rename W into WMf end;
lazymatch goal with I : mem_inv rsegs mf |- _ => rename I into MIf end;
lazymatch goal with Fj : rw_cells rsegs mf spf _ |- _ => rename Fj into FRf end
end.
apply evt_RZ_done.
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
eapply (Kredo mf c av (le4 nv ++ skipn 4 j2)); [exact Hco | reflexivity | | apply fsaved_refl | intros Hf; exact Hf] end.
split.
+ unfold PE_CORE; cbn. split; [exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [eapply rw_cells_transport; [exact TOK | exact MUf | exact WMf | unfold tok_cells_g; cbn; lia]|].
split; [| split; [exact Hpb | split; [| apply pe_frame_nb_set; exact FRf]]].
* eapply (pbuf_wtf HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact PB | exact MUf | exact WMf | exact HW].
* eapply (tstack_wtf HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact TSK | exact LEN32 | exact MUf | exact WMf | exact HW].
+ eapply (PE_REST_private_write HIx) with (ts := ts0) in REST;
[exact REST | exact STC | exact MUf | exact WMf | exact MIf | apply pe_wtf_private; exact HW]. }

step. if_truex.
pose proof (munch_refl [(spf, spf + 144)] m) as MU.
step. rewrite (zxb_byte fl).
step. step. rewrite (unsigned_lit (fl mod 256)) by (pose proof (Z.mod_pos_bound fl 256 ltac:(lia)); lia). rewrite (land_mod256 fl 16) by lia.
destruct (land16_cases fl) as [F16 | F16]; rewrite F16.
+
step. if_true.
eapply JOINR; [apply le1_sxb | exact FR | exact MU | exact WM | exact MI].
+
step. if_false.

assert (JOINS : forall (a0v a1x a2x : word),
evt rsegs (RZ rsegs md T)
(MS (mkR x1 (Z_to_bv 64 spf) gp (Z_to_bv 64 482928) t0 t1 t2 (Z_to_bv 64 tk) (Z_to_bv 64 oldl) a0v a1x a2x a3 a4 a5 a6 a7
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4 s5 s6 (Z_to_bv 64 26) s8 (Z_to_bv 64 (sb + co)) s10 (Z_to_bv 64 79024) t3 t4 t5 t6)
F (Z_to_bv 64 0x2192c) fc None m (seg_rom rsegs))).
{ intros a0v a1x a2x. clear RDF RDC. stash STR.
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
pose proof (payload_byte _ _ _ _ _ STR1 Hc ltac:(lia)) as RDC1.
stash REST.
step. step.
eapply JOINR; [apply le1_zxb | exact FR1 | exact MU1 | exact WM1 | exact MI1]. }

step. step.
Local Ltac if_any := lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd; cbv iota end.
if_any.
*
step. if_any.
--
step. step. step. step. if_any.
++  step. step. step. if_any.
**  step. step. step. if_any.
---
step. step. apply evt_RZ_done. eapply Kerr. exact Hco.
--- step. step. apply JOINS.
** step. step. apply JOINS.
++ step. step. apply JOINS.
--  eapply JOINR; [apply le1_sxb | exact FR | exact MU | exact WM | exact MI].
*
step. step. if_any.
--  step. apply JOINS.
-- step. step. step. apply evt_RZ_done. eapply Kerr. exact Hco.
Qed.
End PeLoop.

End RC__1.
End Mq2.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import QEQM.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0.
Import QC8c.Mq0.
Import Qsw7 QJjn QkMG.
Import QG8z.
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
(x1 gp t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_ofend ->
t_co ts < pf_len pf ->

(forall m' a0' a2',
bv_unsigned cb = 58 ->
PE_INV HIx pf q LB0 payload me lo m' md A (ts_set_level ts (TL ST_eatws ST_ovalue (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb j1 j2 utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK (t_co ts) x1 gp t0 t1 t2 a0' (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a2' a3 a4 a5 a6 a7
s4 s5 s6 (Z_to_bv 64 q) (Z_to_bv 64 (Z.of_nat (t_depth ts))) t3 t4 t5 t6 F fc m') md) T) ->

(forall a0' a2',
bv_unsigned cb <> 58 ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR (t_co ts) x1 gp t0 t1 t2 (Z_to_bv 64 10) a0' a2' a3 a4 a5 a6 a7
s4 s5 s6 (Z_to_bv 64 q) (Z_to_bv 64 (Z.of_nat (t_depth ts))) t3 t4 t5 t6 F fc m) md) T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf (pe_jt ST_ofend) (t_co ts) x1 gp t0 t1 t2
(Z_to_bv 64 (32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l)) a3 a4 a5 a6 a7
s4 s5 s6 (Z_to_bv 64 q) (Z_to_bv 64 (Z.of_nat (t_depth ts))) t3 t4 t5 t6 F fc m) md) T.
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
step. change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)). step.

assert (TAIL : forall mc a0v a2v,
bv_unsigned cb = 58 ->
rw_cells rsegs mc bse [C8 (Z_to_bv 64 (ST_ovalue * 2^32)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (tl_cur l)); C8 (Z_to_bv 64 (tl_name l))] ->
munch [(bse, bse + 32)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
(forall H : rw_cells rsegs mc tk [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 (Z.of_nat depth)); C4 isd; C4 stpos;
C4 (Z_to_bv 64 co); C4 err; C4 ucs; C4 high; C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)], True) ->
rw_cells rsegs mc tk [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 (Z.of_nat depth)); C4 isd; C4 stpos;
C4 (Z_to_bv 64 co); C4 err; C4 ucs; C4 high; C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)] ->
rw_cells rsegs mc spf [C8 (Z_to_bv 64 obj); CB 16 j1; C4 (nbw j2); CB 3 (skipn 4 j2); C1 cb; CB 8 utf;
C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv); C8 (pe_s7 sv); C8 (pe_s6 sv);
C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)] ->
realizes rsegs (mkCfg (MS (mkR x1 (Z_to_bv 64 spf) gp (Z_to_bv 64 482928) t0 t1 t2 (Z_to_bv 64 tk) (Z_to_bv 64 oldl)
a0v (Z_to_bv 64 bse) a2v a3 a4 a5 a6 a7
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4 s5 s6 (Z_to_bv 64 26) (Z_to_bv 64 q) (Z_to_bv 64 (sb + co)) (Z_to_bv 64 (Z.of_nat depth)) (Z_to_bv 64 79024) t3 t4 t5 t6)
F (Z_to_bv 64 PE_BREAK) fc None mc (seg_rom rsegs)) md) T).
{ intros mc a0v a2v Hss L8 MU' WM' MI' _ TOK' FR'.
unstash PB. unstash REST. unstash TSK.
set (ss' := ST_ovalue).
pose proof (rw_cells_recast_prefix rsegs mc bse [C8 (Z_to_bv 64 (ST_ovalue * 2^32))] [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 ss')]
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (tl_cur l)); C8 (Z_to_bv 64 (tl_name l))] L8 ltac:(cbn; repeat split)
ltac:(apply bytes_eq_by_unsigned; vm_compute; reflexivity) eq_refl) as L5.
cbn [app pf_mxd] in L5. clear L8.
set (l' := TL ST_eatws ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
assert (HW : Forall (pe_wtq (PEF tk oldl newl len lenr sb spf pmd mxd fl) q) [(bse, bse + 32)]).
{ apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia | apply Forall_nil]. }
subst bse. apply (Kbreak mc a0v a2v Hss). split.
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
- step. if_falsex. step. step. stepz. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
apply evt_RZ_done; eapply (TAIL mc _ _); [exact C58 | exact Ld | exact MU | exact WM | exact MI | intros; exact I | exact TOK | exact FR] end.
- step. if_truex. step. step.
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
Import QEQM.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0.
Import QC8c.Mq0.
Import Qsw7 QJjn QkMG.
Import QG8z.
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
(x1 gp t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_osep ->
t_co ts < pf_len pf ->

(forall m' ss' a2',
(bv_unsigned cb = 44 /\ ss' = ST_ofs_after_sep) \/ (bv_unsigned cb = 125 /\ ss' = ST_finish) ->
PE_INV HIx pf q LB0 payload me lo m' md A (ts_set_level ts (TL ST_eatws ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb j1 j2 utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK2 (t_co ts) x1 gp t0 t1 t2 (Z_to_bv 64 125) (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a2' a3 a4 a5 a6 a7
s4 s5 s6 (Z_to_bv 64 q) (Z_to_bv 64 (Z.of_nat (t_depth ts))) t3 t4 t5 t6 F fc m') md) T) ->

(forall a2',
bv_unsigned cb <> 44 -> bv_unsigned cb <> 125 ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR (t_co ts) x1 gp t0 t1 t2 (Z_to_bv 64 11) (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a2' a3 a4 a5 a6 a7
s4 s5 s6 (Z_to_bv 64 q) (Z_to_bv 64 (Z.of_nat (t_depth ts))) t3 t4 t5 t6 F fc m) md) T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf (pe_jt ST_osep) (t_co ts) x1 gp t0 t1 t2
(Z_to_bv 64 (32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l)) a3 a4 a5 a6 a7
s4 s5 s6 (Z_to_bv 64 q) (Z_to_bv 64 (Z.of_nat (t_depth ts))) t3 t4 t5 t6 F fc m) md) T.
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
step. change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)). step.

assert (TAIL : forall ss' mc a2v,
(bv_unsigned cb = 44 /\ ss' = ST_ofs_after_sep) \/ (bv_unsigned cb = 125 /\ ss' = ST_finish) ->
rw_cells rsegs mc bse [C8 (Z_to_bv 64 (ss' * 2^32)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (tl_cur l)); C8 (Z_to_bv 64 (tl_name l))] ->
munch [(bse, bse + 32)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
(forall H : rw_cells rsegs mc tk [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 (Z.of_nat depth)); C4 isd; C4 stpos;
C4 (Z_to_bv 64 co); C4 err; C4 ucs; C4 high; C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)], True) ->
rw_cells rsegs mc tk [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 (Z.of_nat depth)); C4 isd; C4 stpos;
C4 (Z_to_bv 64 co); C4 err; C4 ucs; C4 high; C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)] ->
rw_cells rsegs mc spf [C8 (Z_to_bv 64 obj); CB 16 j1; C4 (nbw j2); CB 3 (skipn 4 j2); C1 cb; CB 8 utf;
C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv); C8 (pe_s7 sv); C8 (pe_s6 sv);
C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)] ->
realizes rsegs (mkCfg (MS (mkR x1 (Z_to_bv 64 spf) gp (Z_to_bv 64 482928) t0 t1 t2 (Z_to_bv 64 tk) (Z_to_bv 64 oldl)
(Z_to_bv 64 125) (Z_to_bv 64 bse) a2v a3 a4 a5 a6 a7
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4 s5 s6 (Z_to_bv 64 26) (Z_to_bv 64 q) (Z_to_bv 64 (sb + co)) (Z_to_bv 64 (Z.of_nat depth)) (Z_to_bv 64 79024) t3 t4 t5 t6)
F (Z_to_bv 64 PE_BREAK2) fc None mc (seg_rom rsegs)) md) T).
{ intros ss' mc a2v Hss L8 MU' WM' MI' _ TOK' FR'.
unstash PB. unstash REST. unstash TSK.
assert (SS' : 0 <= ss' <= 26) by (unfold ST_ofs_after_sep, ST_finish in Hss; lia).
pose proof (rw_cells_recast_prefix rsegs mc bse [C8 (Z_to_bv 64 (ss' * 2^32))] [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 ss')]
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (tl_cur l)); C8 (Z_to_bv 64 (tl_name l))] L8 ltac:(cbn; repeat split)) as L5.
assert (EQB : cells_bytes [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 ss')] = cells_bytes [C8 (Z_to_bv 64 (ss' * 2 ^ 32))]).
{ destruct Hss as [[_ ->] | [_ ->]]; apply bytes_eq_by_unsigned; vm_compute; reflexivity. }
specialize (L5 EQB eq_refl). cbn [app pf_mxd] in L5. clear L8 EQB.
set (l' := TL ST_eatws ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
assert (HW : Forall (pe_wtq (PEF tk oldl newl len lenr sb spf pmd mxd fl) q) [(bse, bse + 32)]).
{ apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia | apply Forall_nil]. }
subst bse. apply (Kbreak mc ss' a2v Hss). split.
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
- step. if_truex. step. step. stepz. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
apply evt_RZ_done; eapply (TAIL ST_ofs_after_sep mc _); [left; split; [exact C44 | reflexivity] | exact Ld | exact MU | exact WM | exact MI | intros; exact I | exact TOK | exact FR] end.
- step. if_falsex. step.
destruct (Z.eq_dec (bv_unsigned cb) 125) as [C125 | N125].
+ step. if_falsex. step. step. stepz. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
apply evt_RZ_done; eapply (TAIL ST_finish mc _); [right; split; [exact C125 | reflexivity] | exact Ld | exact MU | exact WM | exact MI | intros; exact I | exact TOK | exact FR] end.
+ step. if_truex. step. step.
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
Import QEQM.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0.
Import QC8c.Mq0.
Import Qsw7 QJjn QkMG.
Import QG8z.
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
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l ->
(forall a3',
realizes rsegs (mkCfg (pe_ms rsegs pf (pe_jt (tl_st l)) (t_co ts) x1 gp t0 t1 t2
(Z_to_bv 64 (32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l)) a3' a4 a5 a6 a7
s4 s5 s6 (Z_to_bv 64 q) (Z_to_bv 64 (Z.of_nat (t_depth ts))) t3 t4 t5 t6 F fc m) md) T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_REDO (t_co ts) x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s10 t3 t4 t5 t6 F fc m) md) T.
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
pose proof (LV depth l Hl) as (ST26 & SS26 & _).
pose proof (TSK depth l Hl) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld. unfold srec_cells in Ld.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
pose proof (pe_jtab_ro m MI) as JT. unfold pe_jtab in JT.
clear PB REST HP LV TSK FR.
apply rz_evt; [exact MOK|]. unfold PE_REDO.
step. norm_sx32. step. step.
rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
step. replace (q + Z.of_nat depth * 32) with bse by lia.
step. norm_sx32. step. if_truex. step.
rewrite (unsigned_lit (tl_st l)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
replace (Z.of_nat depth * 32) with (32 * Z.of_nat depth) by lia.
assert (CASES : exists k : nat, (k <= 26)%nat /\ tl_st l = Z.of_nat k) by (exists (Z.to_nat (tl_st l)); split; lia).
destruct CASES as (k & Hk & Ek). rewrite Ek in *. subst bse.
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
Import QEQM.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0.
Import QC8c.Mq0.
Import Qsw7 QJjn QkMG.
Import QG8z.
Import Q6q3.
Import ListNotations. Unset Keyed Unification.
Open Scope Z_scope.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition pe_jt2 (c : Z) : Z :=
match c with
| 34 => 0x22e6c
| 39 => 0x22e60
| 45 => 0x21e18
| 48 => 0x21e18
| 49 => 0x21e18
| 50 => 0x21e18
| 51 => 0x21e18
| 52 => 0x21e18
| 53 => 0x21e18
| 54 => 0x21e18
| 55 => 0x21e18
| 56 => 0x21e18
| 57 => 0x21e18
| 70 => 0x2223c
| 73 => 0x223a8
| 78 => 0x223a0
| 84 => 0x2223c
| 91 => 0x22e9c
| 102 => 0x2223c
| 105 => 0x223a8
| 110 => 0x223a0
| 116 => 0x2223c
| 123 => 0x22e88
| _ => 0x23008
end.

Definition pe_jtab2 := Eval vm_compute in match image_bytes rsegs 0x13798 360 with Some bs => bs | None => [] end.
#[using="Type"] Lemma pe_jtab2_ro : forall m, mem_inv rsegs m -> ro_cells rsegs m 0x13798 [CB 360 pe_jtab2].
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
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
(forall a0' a2',
realizes rsegs (mkCfg (pe_ms rsegs pf (pe_jt2 (bv_unsigned cb)) (t_co ts) x1 gp t0 t1 t2 a0' a1 a2' a3 a4 a5 a6 a7 s4 s5 s6 s8 s10 t3 t4 t5 t6 F fc m) md) T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf (pe_jt ST_start) (t_co ts) x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s10 t3 t4 t5 t6 F fc m) md) T.
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
replace (pe_jt2 (bv_unsigned cb)) with 0x23008 in K.
2:{ assert (R : 0 <= bv_unsigned cb <= 33) by lia. clear - R. enum_from (bv_unsigned cb) 0%Z 34%nat; reflexivity. }
apply K.
- destruct (Z_lt_dec 123 (bv_unsigned cb)) as [GT | LE].
+ step. if_falsex. step. apply evt_RZ_done.
replace (pe_jt2 (bv_unsigned cb)) with 0x23008 in K. 2:{ assert (R : 124 <= bv_unsigned cb <= 255) by lia. clear - R. enum_from (bv_unsigned cb) 124%Z 132%nat; reflexivity. }
apply K.
+ step. if_truex. step.
rewrite (unsigned_lit (bv_unsigned cb + -34)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
step. step. step.

pose proof (bytes_at_read rsegs m 0x13798 pe_jtab2 ((bv_unsigned cb + -34) * 4) 4 (ro_cells_bytes_at2 _ _ _ _ JT) ltac:(lia)
ltac:(change (length pe_jtab2) with 360%nat; lia)) as RD.
unfold wa in RD. replace (0x13798 + (bv_unsigned cb + -34) * 4) with ((bv_unsigned cb + -34) * 4 + 79768) in RD by lia.
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
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import QEQM.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0.
Import QC8c.Mq0.
Import Qsw7 QJjn QRUw.Mq0 QkMG.
Import QG8z QPZI.Mq2.
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
(x1 gp t0 t1 t2 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
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
realizes rsegs (mkCfg (pe_ms rsegs pf PE_REDO (t_co ts) x1' gp t0 t1 t2 a0' a1' a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s10 t3 t4 t5 t6 F fc m') md) T) ->
realizes rsegs (mkCfg (pe_ms rsegs pf 0x223ac (t_co ts) x1 gp t0 t1 t2
(Z_to_bv 64 stn) (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a2 a3 a4 a5 a6 a7
s4 s5 s6 s8 s10 t3 t4 t5 t6 F fc m) md) T.
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
eapply evt_cut; [eapply printbuf_reset_P; [exact PBCA | lia | lia | lia | lia | unstash Hdpb; exact Hdpb | exact MI] |].
intros ms1 (mr & -> & MUr & WMr & MIr & PBC1).
replace (ret_pc (Z_to_bv 64 0x223b8)) with (Z_to_bv 64 0x223b8) by (symmetry; apply ret_pc_even; [lia | reflexivity]).

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
apply evt_RZ_done. eapply Kredo.
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
(x1 gp t0 t1 t2 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
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
realizes rsegs (mkCfg (pe_ms rsegs pf PE_REDO (t_co ts) x1' gp t0 t1 t2 a0' a1' a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s10 t3 t4 t5 t6 F fc m') md) T) ->
forall a0, realizes rsegs (mkCfg (pe_ms rsegs pf 0x21e18 (t_co ts) x1 gp t0 t1 t2
a0 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a2 a3 a4 a5 a6 a7
s4 s5 s6 s8 s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hst Kredo a0.
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
step. step.
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
eapply evt_cut; [eapply printbuf_reset_P; [exact PBCA | lia | lia | lia | lia | unstash Hdpb; exact Hdpb | exact MI] |].
intros ms1 (mr & -> & MUr & WMr & MIr & PBC1).
replace (ret_pc (Z_to_bv 64 0x21e28)) with (Z_to_bv 64 0x21e28) by (symmetry; apply ret_pc_even; [lia | reflexivity]).

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
apply evt_RZ_done. eapply Kredo.
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
(x1 gp t0 t1 t2 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_start ->

(forall m' x1' a1',
PE_INV HIx pf q LB0 payload me lo m' md A
(TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) (TL ST_string (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)))
(t_co ts) (t_pb ts) (t_pbs ts)
(TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) cb)
(t_obj ts) (t_objs ts) (t_objbs ts))
cb j1 j2 utf sv errv ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK2 (t_co ts) x1' gp t0 t1 t2 (Z_to_bv 64 (bv_unsigned cb)) a1' a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s10 t3 t4 t5 t6 F fc m') md) T) ->
forall a0, realizes rsegs (mkCfg (pe_ms rsegs pf 0x22e6c (t_co ts) x1 gp t0 t1 t2
a0 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a2 a3 a4 a5 a6 a7
s4 s5 s6 s8 s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hst Kbreak a0.
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
step. step.
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
eapply evt_cut; [eapply printbuf_reset_P; [exact PBCA | lia | lia | lia | lia | unstash Hdpb; exact Hdpb | exact MI] |].
intros ms1 (mr & -> & MUr & WMr & MIr & PBC1).
replace (ret_pc (Z_to_bv 64 0x22e7c)) with (Z_to_bv 64 0x22e7c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).

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
apply evt_RZ_done. eapply Kbreak.
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

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Hd.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPIU.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC8c.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEQM.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QC8c.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

Module GwI.
Definition segs := rsegs.
Definition base := 0x24d2c%Z.
Definition w_5 := 0x72c2b0ef%Z.
Definition w_8 := 0xfffff617%Z.
Definition w_10 := 0xca060613%Z.
Definition hi_8 := (Z_to_bv 20 1048575).
Definition lo_10 := (Z_to_bv 12 3232).
Definition joff_5 := (Z_to_bv 21 177964).
Lemma CODE : CodeAt.code_at rsegs 0x24d2c (QPIU.Mq8.jonewdouble_code 0x72c2b0ef%Z 0xfffff617%Z 0xca060613%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x24d2c mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x24d2c /\ 0x24d2c + 88 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.

Local Notation gw_RC := Q6q3.RunConsts (only parsing).
Local Ltac gw_lay t := let v := eval cbv beta iota delta [QC8c.Mq0.S4L QCcH.hl_malloc QCcH.hl_free QCcH.hl_calloc QCcH.hl_realloc QCcH.hl_malloc2 QCcH.hl_free2 QCcH.hl_tp QCcH.hl_got_guard QCcH.hl_guard QCcH.hl_auxv QCcH.hl_libc QCcH.hl_img_lo QCcH.hl_img_hi QCcH.hl_consts] in t in lazymatch v with (fun _ => ?n) => exact n end.
Local Ltac gw_hex k := let v := eval cbv beta iota delta [QC8c.Mq0.S4L QCcH.hl_consts] in (fun RC__ : gw_RC => @QCcH.hl_consts RC__ (@QC8c.Mq0.S4L RC__)) in
lazymatch v with (fun _ => cons (pair ?a (?f1 (?f2 ?b))) (cons (pair _ (?f3 (?f4 ?c))) nil)) => lazymatch k with 0%nat => exact a | 1%nat => exact b | _ => exact c end end.
Definition e_malloc : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_malloc RC__ (@QC8c.Mq0.S4L RC__))).
Definition e_free : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_free RC__ (@QC8c.Mq0.S4L RC__))).
Definition e_calloc : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_calloc RC__ (@QC8c.Mq0.S4L RC__))).
Definition e_realloc : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_realloc RC__ (@QC8c.Mq0.S4L RC__))).
Definition e_malloc2 : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_malloc2 RC__ (@QC8c.Mq0.S4L RC__))).
Definition e_free2 : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_free2 RC__ (@QC8c.Mq0.S4L RC__))).
Definition gTP : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_tp RC__ (@QC8c.Mq0.S4L RC__))).
Definition gGOTG : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_got_guard RC__ (@QC8c.Mq0.S4L RC__))).
Definition gGUARD : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_guard RC__ (@QC8c.Mq0.S4L RC__))).
Definition gAUXV : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_auxv RC__ (@QC8c.Mq0.S4L RC__))).
Definition gLIBC : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_libc RC__ (@QC8c.Mq0.S4L RC__))).
Definition gIMG_LO : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_img_lo RC__ (@QC8c.Mq0.S4L RC__))).
Definition gIMG_HI : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_img_hi RC__ (@QC8c.Mq0.S4L RC__))).
Definition gHEXGOT : Z := ltac:(gw_hex 0%nat).  Definition gHEXPTR : Z := ltac:(gw_hex 1%nat).  Definition gHEXCHARS : Z := ltac:(gw_hex 2%nat).
Definition gVOL := QC8c.Mq0.s4_volatile.  Definition gCS := QC8c.Mq0.s4_client_static.
Definition gH1 := fun RC__ : gw_RC => @QCcH.hl_static_in_img RC__ (@QC8c.Mq0.S4L RC__).
Definition gH2 := fun RC__ : gw_RC => @QCcH.hl_img_range RC__ (@QC8c.Mq0.S4L RC__).
Definition gH3 := fun RC__ : gw_RC => @QCcH.hl_scratch_in_img RC__ (@QC8c.Mq0.S4L RC__).
Definition gH4 := fun RC__ : gw_RC => @QCcH.hl_scratch_not_static RC__ (@QC8c.Mq0.S4L RC__).
Definition gH5 := fun RC__ : gw_RC => @QCcH.hl_consts_ok RC__ (@QC8c.Mq0.S4L RC__).
Definition e_fn_obj_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_obj_to_json_string QC8c.Mq0.S4F] in (Q0Ek.fn_obj_to_json_string QC8c.Mq0.S4F).
Definition e_fn_arr_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_arr_to_json_string QC8c.Mq0.S4F] in (Q0Ek.fn_arr_to_json_string QC8c.Mq0.S4F).
Definition e_fn_bool_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_bool_to_json_string QC8c.Mq0.S4F] in (Q0Ek.fn_bool_to_json_string QC8c.Mq0.S4F).
Definition e_fn_dbl_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_dbl_to_json_string QC8c.Mq0.S4F] in (Q0Ek.fn_dbl_to_json_string QC8c.Mq0.S4F).
Definition e_fn_int_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_int_to_json_string QC8c.Mq0.S4F] in (Q0Ek.fn_int_to_json_string QC8c.Mq0.S4F).
Definition e_fn_str_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_str_to_json_string QC8c.Mq0.S4F] in (Q0Ek.fn_str_to_json_string QC8c.Mq0.S4F).
Definition e_fn_ud_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_ud_to_json_string QC8c.Mq0.S4F] in (Q0Ek.fn_ud_to_json_string QC8c.Mq0.S4F).
Definition e_fn_free_userdata := Eval cbv beta iota delta [Q0Ek.fn_free_userdata QC8c.Mq0.S4F] in (Q0Ek.fn_free_userdata QC8c.Mq0.S4F).
Definition e_fn_lh_entry_free := Eval cbv beta iota delta [Q0Ek.fn_lh_entry_free QC8c.Mq0.S4F] in (Q0Ek.fn_lh_entry_free QC8c.Mq0.S4F).
Definition e_fn_lh_char_hash := Eval cbv beta iota delta [Q0Ek.fn_lh_char_hash QC8c.Mq0.S4F] in (Q0Ek.fn_lh_char_hash QC8c.Mq0.S4F).
Definition e_fn_lh_char_equal := Eval cbv beta iota delta [Q0Ek.fn_lh_char_equal QC8c.Mq0.S4F] in (Q0Ek.fn_lh_char_equal QC8c.Mq0.S4F).
Definition e_fn_arr_entry_free := Eval cbv beta iota delta [Q0Ek.fn_arr_entry_free QC8c.Mq0.S4F] in (Q0Ek.fn_arr_entry_free QC8c.Mq0.S4F).
Definition pS4L := Eval cbv beta delta [Q0Hd.gl segs e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI] in
(fun RC__ : gw_RC => @Q0Hd.gl RC__ segs e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI (gH1 RC__) (gH2 RC__) (gH3 RC__) (gH4 RC__) (gH5 RC__)).
Definition pS4F := Eval cbv beta delta [Q0Hd.gf e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free] in
(Q0Hd.gf e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free).
End GwI.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section JoNewDouble.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).

Definition json_object_new_double_entry : Z := 0x24d2c.

Definition new_obj_post (s : jshape) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo : Z)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (r : Z) (errv' : word),
ret_statew S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only md md' /\
stk rsegs m' lo (bv_unsigned sp) /\
heap_pres S4L LB (bv_unsigned sp) m m' /\
rw_cells rsegs m' (0x75e70 - 164) [C4 errv'] /\
( (r = 0 /\ HEAPx A' LB m' md')
\/ (r <> 0 /\ exists BS, jval rsegs S4F s m' BS r 1 /\ HEAPx A' (BS ++ LB) m' md') ).

Local Definition gwt_X : unit := (Q6nq.gwt_pat GwI.pS4L (@QC8c.Mq0.S4L) (Q6nq.gwt_pat GwI.pS4F QC8c.Mq0.S4F Q6nq.gwt_nil)).
#[using="Type"] Lemma json_object_new_double_cps : ltac2:(Q6nq.ty2 'GwI.segs '(@QPIU.Mq8.json_object_new_double_cps) [] '([(-8256); (-164); 482928]%Z : list Z) '(Q6nq.gwt_zc json_object_new_double_entry (Q6nq.gwt_def (@QPIU.Mq8.new_obj_post) (@new_obj_post) (Q6nq.gwt_def (@QPIU.Mq8.json_object_new_double_entry) (@json_object_new_double_entry) gwt_X)))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QPIU.Mq8.json_object_new_double_cps) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QPIU.Mq8.json_object_new_double_cps)]. Qed.
End JoNewDouble.

End RC__1.
