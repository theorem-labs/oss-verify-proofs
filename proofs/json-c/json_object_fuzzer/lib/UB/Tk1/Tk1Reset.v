(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QRjH QHnV QCcH QfLs Q0Ek Qtgi QjDH Qsw7 QJjn QkMG QRUw QAyu QlCE Q6q3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM UC8c UPZI UG8z.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require TopUbTac.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Tk1 Require Tk1Tac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import QXup UEQM OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QRjH QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0.
Import UC8c.Mq0 Qsw7 QJjn QkMG QRUw UPZI.Mq4.
Import TopUbTac Tk1Tac.
Import ListNotations. Unset Keyed Unification.
Open Scope Z_scope.
Import Q6q3.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section ResetLevel.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Hypothesis PUT : put_stmt_P HIx.

Definition reset_level_entry : Z := 0x21a0c.
Definition RESET_STK : Z := 48 + put_stk_P.

Definition reset_level_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(md : Model) (REST LB0 P : list blk) (me mpre : word -> option byte) (lo : Z) (errv : word)
(q r pb depth mxd fl : Z) (x : tscal) (levels : list tlevel) (i : nat) (l : tlevel) (rc : Z)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (rv : word),
ret_statew S4L ra sp gp (Z_to_bv 64 0x77c00) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc rv m' ms' /\
model_vm_only md md' /\
( ((tl_cs l = None \/ rc = 1) /\ HEAPx A' REST m' md')
\/ (exists s', tl_cs l = Some s' /\ 2 <= rc /\ jval rsegs S4F s' m' (tl_cbs l) (tl_cur l) (rc - 1) /\ HEAPx A' (tl_cbs l ++ REST) m' md') ) /\
tstack rsegs m' q (lupd levels i lvl_reset) /\
rw_cells rsegs m' r (tok_cells_g mxd fl pb depth q x) /\
stk rsegs m' lo (bv_unsigned sp) /\
heap_pres S4L LB0 (bv_unsigned sp) me m' /\
rw_cells rsegs m' (0x77c00 - 164) [C4 errv] /\
agree_on rsegs P mpre m'.

Lemma reset_level_cps :
forall (i : nat) (ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m me : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (REST LB0 P : list blk) (lo : Z) (errv : word)
(q r pb depth mxd fl : Z) (x : tscal) (levels : list tlevel) (l : tlevel) (rc : Z),
nth_error levels i = Some l -> Z.of_nat i < mxd -> 1 <= mxd <= 32 -> length levels = Z.to_nat mxd ->
HEAPx A (lvl_blocks l ++ REST) m md ->
REST = P ++ (r, 72) :: (q, 32 * mxd) :: LB0 ->
put_pre S4L S4F (tl_cs l) m (tl_cbs l) (tl_cur l) rc ->
((tl_name l = 0 /\ tl_nbs l = []) \/ (tl_name l <> 0 /\ exists nn, tl_nbs l = [(tl_name l, nn)])) ->
tstack rsegs m q levels ->
rw_cells rsegs m r (tok_cells_g mxd fl pb depth q x) ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RESET_STK ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
heap_pres S4L LB0 (bv_unsigned sp) me m ->
rw_cells rsegs m (0x77c00 - 164) [C4 errv] ->
bv_unsigned ra mod 2 = 0 ->
(forall ms' md', reset_level_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc md REST LB0 P me m lo errv q r pb depth mxd fl x levels i l rc ms' md' ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp (Z_to_bv 64 0x77c00) t0 t1 t2 s0 s1 (Z_to_bv 64 r) (Z_to_bv 64 (Z.of_nat i)) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 reset_level_entry) fc None m (seg_rom rsegs)) md) T.
Proof.
intros until rc. intros Hl Hi MXB LEN HP EREST PP NM TS BLK ST LO LOS SPA HT HPR ERR RA K.
unfold RESET_STK, put_stk_P in LOS. unfold_consts. unfold reset_level_entry. word_range sp SPR.
assert (INrR : In (r, 72) REST) by (rewrite EREST; apply in_or_app; right; left; reflexivity).
assert (INqR : In (q, 32 * mxd) REST) by (rewrite EREST; apply in_or_app; right; right; left; reflexivity).
assert (INr : In (r, 72) (lvl_blocks l ++ REST)) by (apply in_or_app; right; exact INrR).
assert (INq : In (q, 32 * mxd) (lvl_blocks l ++ REST)) by (apply in_or_app; right; exact INqR).
pose proof (heap_blk S4L HIx _ _ _ _ r 72 HP INr) as (_ & Hral & Hrlo & Hrhi & _).
pose proof (heap_blk S4L HIx _ _ _ _ q (32 * mxd) HP INq) as (_ & Hqal & Hqlo & Hqhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hrhi, Hqhi.
pose proof (heap_blk_img S4L HIx _ _ _ _ r 72 HP INr) as Himg_r. cbn [hl_img_lo hl_img_hi S4L] in Himg_r.
pose proof (heap_blk_img S4L HIx _ _ _ _ q (32 * mxd) HP INq) as Himg_q. cbn [hl_img_lo hl_img_hi S4L] in Himg_q.
assert (Hqr : q <> r).
{ intros ->. pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND. rewrite EREST, !map_app in ND. cbn [map blk_addr fst] in ND.
apply NoDup_app_remove_l in ND. apply NoDup_app_remove_l in ND. apply List.NoDup_cons_iff in ND as [Hni _]. apply Hni. left. reflexivity. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ q (32 * mxd) r 72 HP INq INr Hqr) as Hdqr.
pose proof (TS i l Hl) as LV. unfold srec_cells in LV.
remember (q + 32 * Z.of_nat i) as bse eqn:Hbse in LV.
assert (Hb16 : bse mod 16 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
assert (Ebse : q + Z.of_nat i * 32 = bse) by (subst bse; lia).
unfold tok_cells_g in BLK.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs m) as WM.
pose proof (munch_refl [(bse, bse + 32); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
pose proof rc_ceil_range as RCR. pose proof rc_ceil_al16 as RCA.
apply rz_evt; [exact MOK|].
step. carve_frame 48%nat ST.
tk1_walk 0x21a0c 0x21b24 60%nat Ebse.
set (l1 := TL 0 1 (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
assert (HiL : (i < length levels)%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TS1 : tstack rsegs mc q (lupd levels i l1)) end.
{ subst bse. eapply (tstack_put rsegs m _ q levels i l1 [(bv_unsigned sp - 48, bv_unsigned sp)]); [exact TS | lia | exact MU | exact WM | | unfold srec_cells; cbn [tl_st tl_ss tl_cur tl_name l1]; assumption].
intros j Hj Hne. cbn. split; [left; unfold alloc_ceiling in *; lia | exact I]. }
lazymatch goal with H : rw_cells rsegs _ bse _ |- _ => rename H into LV1 end.
clear TS.
assert (PDJ : forall a n, In (a, n) P -> (a + n <= q \/ q + 32 * mxd <= a) /\ a + n <= alloc_ceiling).
{ intros a n Hin.
assert (Haq : a <> q) by (eapply (QAyu.Mq6.nodup_P_notq (lvl_blocks l)); [rewrite <- EREST; exact (heap_blk_nodup S4L HIx _ _ _ _ HP) | exact Hin]).
assert (INa : In (a, n) (lvl_blocks l ++ REST)) by (apply in_or_app; right; rewrite EREST; apply in_or_app; left; exact Hin).
split; [exact (heap_blk_disjoint S4L HIx _ _ _ _ a n q (32 * mxd) HP INa INq Haq)|].
pose proof (heap_blk S4L HIx _ _ _ _ a n HP INa) as (_ & _ & _ & Hahi & _). exact Hahi. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (AGP : agree_on rsegs P m mc) by (eapply agree_of_munch; [exact MU | exact WM | intros a n Hin; cbn; destruct (PDJ a n Hin) as [D1 D2]; split; [lia | split; [unfold alloc_ceiling in *; lia | exact I]]]) end.
unfold lvl_blocks in HP. rewrite <- app_assoc in HP.
apply evt_RZ_done.
assert (INq2 : In (q, 32 * mxd) (tl_cbs l ++ tl_nbs l ++ REST)) by (apply in_or_app; right; apply in_or_app; right; exact INqR).
eapply PUT with (s := tl_cs l) (BS := tl_cbs l) (LB := tl_nbs l ++ REST) (p := tl_cur l) (rc := rc) (lo := lo) (errv := errv);
[ eapply (heap_frame S4L HIx); [exact HP | | exact WM | exact MI];
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU); apply Forall_cons; [right; left; exists q, (32 * mxd); split; [exact INq2 | cbn; lia] | apply Forall_cons; [left; cbn; unfold alloc_ceiling in *; lia | apply Forall_nil]]
| .. ]; try alloc_side.
{ lazymatch goal with |- put_pre _ _ _ ?mc _ _ _ => assert (AG : agree_on rsegs (tl_cbs l) m mc) end.
{ eapply agree_of_munch; [exact MU | exact WM |]. intros a n Hin. cbn.
assert (INa : In (a, n) (tl_cbs l ++ tl_nbs l ++ REST)) by (apply in_or_app; left; exact Hin).
assert (Haq : a <> q).
{ intros ->. refine (nodup_prefix_suffix (tl_cbs l) (tl_nbs l ++ REST) q n (32 * mxd) (heap_blk_nodup S4L HIx _ _ _ _ HP) Hin _).
apply in_or_app; right. exact INqR. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ a n q (32 * mxd) HP INa INq2 Haq) as D1.
pose proof (heap_blk S4L HIx _ _ _ _ a n HP INa) as (_ & _ & _ & Hahi & _).
split; [lia | split; [unfold alloc_ceiling in *; lia | exact I]]. }
unfold put_pre in *. destruct (tl_cs l) as [s'|]; [|exact PP].
destruct PP as (Hc & Hrc & J). split; [exact Hc|]. split; [exact Hrc|]. eapply jval_agree; [exact J | exact AG | apply incl_refl]. }
all: try eassumption.
all: try (unfold put_stk_P; rewrite ?unsigned_lit by lia; lia).
intros ms2 md2 (m2 & A2 & r2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & OUT2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in ST2 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in HPR2 by lia.
assert (HPx : exists LBx, HEAPx A2 (LBx ++ tl_nbs l ++ REST) m2 md2 /\
((LBx = [] /\ (tl_cs l = None \/ rc = 1)) \/ (exists s', tl_cs l = Some s' /\ 2 <= rc /\ LBx = tl_cbs l /\ jval rsegs S4F s' m2 (tl_cbs l) (tl_cur l) (rc - 1)))).
{ destruct OUT2 as [[H1 H2] | (s' & E & R & J & H2)];
[exists []; split; [exact H2 | left; split; [reflexivity | exact H1]] | exists (tl_cbs l); split; [exact H2 | right; exists s'; repeat split; assumption]]. }
destruct HPx as (LBx & HP2 & OUTx). clear OUT2.
assert (INrN0 : In (r, 72) (tl_nbs l ++ REST)) by (apply in_or_app; right; exact INrR).
assert (INqN0 : In (q, 32 * mxd) (tl_nbs l ++ REST)) by (apply in_or_app; right; exact INqR).
assert (INrN : In (r, 72) (LBx ++ tl_nbs l ++ REST)) by (apply in_or_app; right; exact INrN0).
assert (INqN : In (q, 32 * mxd) (LBx ++ tl_nbs l ++ REST)) by (apply in_or_app; right; exact INqN0).
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in BLK; [| eapply client_range_block; [exact INrN0 | lia | cbn; lia]]. cbn [hl_segs S4L] in BLK.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in LV1; [| eapply client_range_block; [exact INqN0 | lia | cbn; lia]]. cbn [hl_segs S4L] in LV1.
apply (UG8z.tstack_pres_g S4L _ _ _ _ _ _ HPR2 INqN0) in TS1; [| rewrite lupd_length; exact LEN].
assert (NQ0 : ~ In (q, 32 * mxd) LB0).
{ pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND. rewrite EREST in ND. exact (QAyu.Mq6.nodup_mid_notin _ _ _ _ _ _ _ _ (32 * mxd) ND). }
assert (HPRa : heap_pres S4L LB0 (bv_unsigned sp) me m2).
{ eapply heap_pres_trans; [exact HPR|]. eapply heap_pres_trans.
- eapply (heap_pres_of_munch S4L LB0 (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros bb Hbb; apply in_or_app; right; apply in_or_app; right; rewrite EREST; apply in_or_app; right; right; right; exact Hbb | clia |].
apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; cbn [fst snd].
+ right; left. exists q, (32 * mxd). split; [exact INq2|]. split; [exact NQ0 | lia].
+ left. lia.
- eapply heap_pres_weaken; [exact HPR2 | lia | intros bb Hbb; apply in_or_app; right; rewrite EREST; apply in_or_app; right; right; right; exact Hbb]. }
assert (AGP2 : agree_on rsegs P m m2).
{ eapply agree_on_trans; [exact AGP|]. eapply (agree_of_heap_pres rsegs S4L); [exact HPR2 | reflexivity | intros b Hb; apply in_or_app; right; rewrite EREST; apply in_or_app; left; exact Hb]. }
clear MU WM MI HPR AGP.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs m2) as WM. pose proof (munch_refl [(bse, bse + 32); (bv_unsigned sp - 48, bv_unsigned sp)] m2) as MU.
reenter MOK2.
tk1_walk 0x21a0c 0x21b24 60%nat Ebse.
set (l2 := TL 0 1 0 None [] (tl_name l) (tl_nbs l)).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TS2 : tstack rsegs mc q (lupd levels i l2)) end.
{ rewrite <- (QAyu.Mq6.lupd_lupd levels i l1 l2). subst bse.
eapply (tstack_put rsegs m2 _ q (lupd levels i l1) i l2 [(bv_unsigned sp - 48, bv_unsigned sp)]); [exact TS1 | rewrite lupd_length; lia | exact MU | exact WM | | unfold srec_cells; cbn [tl_st tl_ss tl_cur tl_name l2]; assumption].
intros j Hj Hne. rewrite ?lupd_length in Hj. cbn. split; [left; unfold alloc_ceiling in *; lia | exact I]. }
clear TS1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (AGP3 : agree_on rsegs P m mc) by (eapply agree_on_trans; [exact AGP2|]; eapply agree_of_munch; [exact MU | exact WM | intros a n Hin; cbn; destruct (PDJ a n Hin) as [D1 D2]; split; [lia | split; [unfold alloc_ceiling in *; lia | exact I]]]) end.
apply evt_RZ_done. eapply (hi_free S4L HIx) with (p := tl_name l) (lo := lo) (LB := LBx ++ tl_nbs l ++ REST);
[ eapply (heap_frame S4L HIx); [exact HP2 | | exact WM | exact MI];
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP2 MU); apply Forall_cons; [right; left; exists q, (32 * mxd); split; [exact INqN | cbn; lia] | apply Forall_cons; [left; cbn; unfold alloc_ceiling in *; lia | apply Forall_nil]]
| .. ]; try alloc_side.
{ destruct NM as [[Hn0 _] | [Hn0 [nn Hnbs]]]; [left; exact Hn0 | right; exists nn; apply in_or_app; right; apply in_or_app; left; rewrite Hnbs; left; reflexivity]. }
all: try (rewrite ?unsigned_lit by lia; lia).
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3. cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in HPR3 by lia.
assert (RAPP : forall p (L1 L2 : list blk), (forall n, ~ In (p, n) L1) -> lb_remove p (L1 ++ L2) = L1 ++ lb_remove p L2).
{ intros p L1 L2. induction L1 as [|[a0 n0] L1 IH]; intros HN; [reflexivity|]. cbn [app].
rewrite lb_remove_other; [f_equal; apply IH; intros n1 Hin; apply (HN n1); right; exact Hin | cbn; intros E; subst a0; apply (HN n0); left; reflexivity]. }
assert (NIN : forall n, ~ In (tl_name l, n) LBx).
{ intros n Hin. destruct NM as [[Hn0 Hnbs] | [Hn0 [nn Hnbs]]].
- pose proof (heap_blk S4L HIx _ _ _ _ (tl_name l) n HP2 ltac:(apply in_or_app; left; exact Hin)) as (_ & _ & H0 & _). lia.
- pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP2) as ND. rewrite !map_app, Hnbs in ND. cbn [map blk_addr fst app] in ND.
apply NoDup_remove_2 in ND. apply ND. apply in_or_app; left. change (tl_name l) with (blk_addr (tl_name l, n)). apply in_map. exact Hin. }
assert (ELB : lb_remove (tl_name l) (LBx ++ tl_nbs l ++ REST) = LBx ++ REST).
{ rewrite (RAPP _ _ _ NIN). f_equal. destruct NM as [[Hn0 Hnbs] | [Hn0 [nn Hnbs]]].
- rewrite Hn0, Hnbs. cbn [app]. apply QlCE.Mq1.lb_remove_notin. intros nn Hin.
pose proof (heap_blk S4L HIx _ _ _ _ 0 nn HP2 ltac:(apply in_or_app; right; rewrite Hnbs; exact Hin)) as (_ & _ & H0 & _). lia.
- rewrite Hnbs. cbn [app]. apply lb_remove_head. }
rewrite ELB in HPR3, HP3.
assert (INrX : In (r, 72) (LBx ++ REST)) by (apply in_or_app; right; exact INrR).
assert (INqX : In (q, 32 * mxd) (LBx ++ REST)) by (apply in_or_app; right; exact INqR).
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in BLK; [| eapply client_range_block; [exact INrX | lia | cbn; lia]]. cbn [hl_segs S4L] in BLK.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in LV1; [| eapply client_range_block; [exact INqX | lia | cbn; lia]]. cbn [hl_segs S4L] in LV1.
apply (UG8z.tstack_pres_g S4L _ _ _ _ _ _ HPR3 INqX) in TS2; [| rewrite lupd_length; exact LEN].
assert (HPRb : heap_pres S4L LB0 (bv_unsigned sp) me m3).
{ eapply heap_pres_trans; [exact HPRa|]. eapply heap_pres_trans.
- eapply (heap_pres_of_munch S4L LB0 (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP2 | intros bb Hbb; apply in_or_app; right; apply in_or_app; right; rewrite EREST; apply in_or_app; right; right; right; exact Hbb | clia |].
apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; cbn [fst snd].
+ right; left. exists q, (32 * mxd). split; [exact INqN|]. split; [exact NQ0 | lia].
+ left. lia.
- eapply heap_pres_weaken; [exact HPR3 | lia | intros bb Hbb; apply in_or_app; right; rewrite EREST; apply in_or_app; right; right; right; exact Hbb]. }
assert (AGP4 : agree_on rsegs P m m3).
{ eapply agree_on_trans; [exact AGP3|]. eapply (agree_of_heap_pres rsegs S4L); [exact HPR3 | reflexivity | intros b Hb; apply in_or_app; right; rewrite EREST; apply in_or_app; left; exact Hb]. }
assert (CBDJ : forall a n, In (a, n) LBx -> disjoint_from [(bse, bse + 32); (bv_unsigned sp - 48, bv_unsigned sp)] a n).
{ intros a n Hin.
assert (NEq : a <> q).
{ intros ->. exact (nodup_prefix_suffix LBx (tl_nbs l ++ REST) q n (32 * mxd) (heap_blk_nodup S4L HIx _ _ _ _ HP2) Hin INqN0). }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ a n q (32 * mxd) HP2 ltac:(apply in_or_app; left; exact Hin) INqN NEq) as DJ.
pose proof (heap_blk S4L HIx _ _ _ _ a n HP2 ltac:(apply in_or_app; left; exact Hin)) as (_ & _ & _ & Hahi & _).
cbn. split; [lia | split; [unfold alloc_ceiling in *; lia | exact I]]. }
assert (AGX3 : agree_on rsegs LBx m2 m3).
{ eapply agree_on_trans; [eapply agree_of_munch; [exact MU | exact WM | exact CBDJ] |].
eapply (agree_of_heap_pres rsegs S4L); [exact HPR3 | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]. }
clear MU WM MI HPRa AGP3.
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs m3) as WM. pose proof (munch_refl [(bse, bse + 32); (bv_unsigned sp - 48, bv_unsigned sp)] m3) as MU.
reenter MOK3.
tk1_walk 0x21a0c 0x21b24 60%nat Ebse.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TS3 : tstack rsegs mc q (lupd levels i lvl_reset)) end.
{ rewrite <- (QAyu.Mq6.lupd_lupd levels i l2 lvl_reset). subst bse.
eapply (tstack_put rsegs m3 _ q (lupd levels i l2) i lvl_reset [(bv_unsigned sp - 48, bv_unsigned sp)]); [exact TS2 | rewrite lupd_length; lia | exact MU | exact WM | | unfold srec_cells; cbn [tl_st tl_ss tl_cur tl_name lvl_reset]; assumption].
intros j Hj Hne. rewrite ?lupd_length in Hj. cbn. split; [left; unfold alloc_ceiling in *; lia | exact I]. }
release_frame FR ST3 (bv_unsigned sp).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => set (mf := mc) in * end.
assert (HP4 : HEAPx A3 (LBx ++ REST) mf md3)
by (eapply (heap_frame S4L HIx); [exact HP3 | | exact WM | exact MI];
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP3 MU); apply Forall_cons; [right; left; exists q, (32 * mxd); split; [exact INqX | cbn; lia] | apply Forall_cons; [left; cbn; unfold alloc_ceiling in *; lia | apply Forall_nil]]).
apply evt_RZ_done. apply K. unfold reset_level_post.
exists mf, A3. eexists.
split; [apply ret_statew_intro; [exact FS2 | exact FRM2]|].
split; [eapply model_vm_only_trans; [exact VM2 | exact VM3]|].
split.
{ destruct OUTx as [[ELx Hc] | (s' & Es & Hrc & ELx & JV)].
- left. split; [exact Hc|]. rewrite ELx in HP4. exact HP4.
- right. exists s'. split; [exact Es|]. split; [exact Hrc|]. rewrite ELx in HP4. split; [| exact HP4].
eapply (jval_agree rsegs S4F s' (tl_cbs l) m2 mf); [exact JV | | apply incl_refl].
rewrite <- ELx. eapply agree_on_trans; [exact AGX3|]. eapply agree_of_munch; [exact MU | exact WM | exact CBDJ]. }
split; [exact TS3|]. split; [unfold tok_cells_g; exact BLK|].
split; [exact ST3|].
split.
{ eapply heap_pres_trans; [exact HPRb|].
eapply (heap_pres_of_munch S4L LB0 (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP3 | intros bb Hbb; apply in_or_app; right; rewrite EREST; apply in_or_app; right; right; right; exact Hbb | clia |].
apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; cbn [fst snd].
+ right; left. exists q, (32 * mxd). split; [exact INqX|]. split; [exact NQ0 | lia].
+ left. lia. }
split; [assumption|].
eapply agree_on_trans; [exact AGP4|]. eapply agree_of_munch; [exact MU | exact WM | intros a n Hin; cbn; destruct (PDJ a n Hin) as [D1 D2]; split; [lia | split; [unfold alloc_ceiling in *; lia | exact I]]].
Qed.

End ResetLevel.
End RC__1.
