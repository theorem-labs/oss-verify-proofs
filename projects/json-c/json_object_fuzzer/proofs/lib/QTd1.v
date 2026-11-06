(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QEQM Lib.GwApply QWxq_c1 Lib.SepCache QRjH QHnV QCcH QfLs Q0Ek Qtgi QjDH QC8c Qsw7 QJjn QRUw QkMG QG8z Qdyh Q2Sr QLbz QIsM Qa8x QXfU QMdR Qzoi QBpZ QT7i Qv6q QzWc QgoP Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import QEQM.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0.
Import QC8c.Mq0.
Import Qsw7 QJjn QRUw.Mq2 QkMG.
Import QG8z Qdyh.Mq0 Q2Sr QLbz QIsM.Mq2 Qa8x.Mq3 Qa8x Qdyh.Mq2 QXfU.Mq4 QXfU.Mq0 QMdR.Mq0.
Import QJjn.Mq0.
Import Qdyh Qzoi.
Import QBpZ QT7i Qv6q.
Import QzWc.
Import QgoP.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition pinf2bytes := Eval vm_compute in match image_bytes rsegs 0x134a0 8 with Some bs => bs | None => [] end.
Definition ninfbytes := Eval vm_compute in match image_bytes rsegs 0x134a8 8 with Some bs => bs | None => [] end.
#[using="Type"] Lemma pinf2_ro : forall m, mem_inv rsegs m -> ro_cells rsegs m 0x134a0 [CB 8 pinf2bytes].
Proof.
intros m MI. change 8%nat with (length pinf2bytes).
apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ]. change (Z.of_nat (length pinf2bytes)) with 8%Z. lia.
Qed.
#[using="Type"] Lemma ninf_ro : forall m, mem_inv rsegs m -> ro_cells rsegs m 0x134a8 [CB 8 ninfbytes].
Proof.
intros m MI. change 8%nat with (length ninfbytes).
apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ]. change (Z.of_nat (length ninfbytes)) with 8%Z. lia.
Qed.
#[using="Type"] Lemma infbytes_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x13000 infbytes.
Proof. intros m MI. exact (ro_cells_bytes_at'' _ _ _ _ (inf_ro m MI)). Qed.
#[using="Type"] Lemma invbytes_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x10eb1 invbytes.
Proof. intros m MI. exact (ro_cells_bytes_at'' _ _ _ _ (inv_ro m MI)). Qed.
#[using="Type"] Lemma infbytes_len : length infbytes = 9%nat. Proof. reflexivity. Qed.

#[using="Type"] Lemma infbytes_nz : forall k b, nth_error infbytes k = Some b -> (k <= 7)%nat -> bv_unsigned b <> 0.
Proof.
intros k b H Hk E. do 8 (destruct k as [|k]; [cbn in H; injection H as <-; revert E; vm_compute; lia|]). lia.
Qed.
#[using="Type"] Lemma invbytes_nz : forall k b, nth_error invbytes k = Some b -> (k <= 7)%nat -> bv_unsigned b <> 0.
Proof.
intros k b H Hk E. do 8 (destruct k as [|k]; [cbn in H; injection H as <-; revert E; vm_compute; lia|]). lia.
Qed.
#[using="Type"] Lemma invbytes_len : length invbytes = 9%nat. Proof. reflexivity. Qed.

Section PeInf.
Variable HIx : heap_iface S4L.

#[using="Type"] Lemma PE_INV_retok_nb : forall pf q LB0 payload me lo m mc md A ts cb cb' j1 j2 j2' utf utf' sv errv x' co',
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
munch [(pf_tk pf, pf_tk pf + 72); (pf_spf pf, pf_spf pf + PE_FRAME)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
rw_cells rsegs mc (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) (t_pb ts) (Z.of_nat (t_depth ts)) q x') ->
0 <= co' <= pf_len pf -> ts_choff x' = Z_to_bv 64 co' ->
pe_frame rsegs mc (pf_spf pf) (t_obj ts) cb' j1 j2' utf' sv ->
PE_INV HIx pf q LB0 payload me lo mc md A
(TST (t_depth ts) (t_levels ts) co' (t_pb ts) (t_pbs ts) x' (t_obj ts) (t_objs ts) (t_objbs ts)) cb' j1 j2' utf' sv errv.
Proof.
intros until co'. intros STC [CORE REST] MU WM MI TOK' Hco' CH FR'.
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
assert (HW : Forall (pe_wtf pf) [(pf_tk pf, pf_tk pf + 72); (pf_spf pf, pf_spf pf + PE_FRAME)]).
{ apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [right; cbn; lia | apply Forall_nil]. }
split.
- unfold PE_CORE; cbn. split; [exact LEN32|]. split; [exact D32|]. split; [exact Hco'|]. split; [exact CH|].
split; [exact TOK'|]. split; [| split; [exact Hpb | split; [| exact FR']]].
+ eapply (pbuf_wtf HIx) with (ts := ts); [exact STC | exact (proj1 REST) | exact PB | exact MU | exact WM | exact HW].
+ eapply (tstack_wtf HIx) with (ts := ts); [exact STC | exact (proj1 REST) | exact TSK | exact LEN32 | exact MU | exact WM | exact HW].
- eapply (PE_REST_private_write HIx) with (ts := ts) in REST; [exact REST | exact STC | exact MU | exact WM | exact MI | apply pe_wtf_private; exact HW].
Qed.
#[using="Type"] Lemma case_inf : forall (pf : pe_fix) (q : Z) (LBc : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(sv : pe_saved) (T : TSet) (F0 : bvmap 5 word) (utf8rep : list byte),
CASE HIx pf q LBc payload me lo sv T F0 utf8rep ST_inf.
Proof.
intros pf q LBc payload me lo sv T F0 utf8rep.
unfold CASE. intros n ts l m md A cb j1 j2 utf errv x1 gp t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 t3 t4 t5 t6 F fc.
change (pe_jt ST_inf) with 138884.
intros STC INV Hl Hst Hco Hcb NUM SP TDOK UTF GOTF CSTR FS FRM Mn (KL & KR & KB & KB2) KO7 KE7.
pose proof (KERR_of_7 _ _ _ _ _ _ _ _ _ _ KE7) as KE. pose proof (KOUT_of_7 _ _ _ _ _ _ _ _ _ _ KO7) as KO.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & (SBL & RR & LENR)).
pose proof INV as [CORE REST].
pose proof CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof (heap_model_ok _ _ _ _ _ _ (proj1 REST)) as MOK.

assert (SPB : SPV (t_x ts) <= t_co ts) by (unfold SPOK in SP; specialize (SP ltac:(unfold cur_st; rewrite Hl, Hst; reflexivity)); lia).
assert (SP0' : 0 <= SPV (t_x ts)) by (unfold SPV; apply Z.mod_pos_bound; lia).
revert INV NUM SP TDOK Mn KL KR KB KB2 KO7 KE7 KE KO SPB SP0'.
destruct ts as [depth levels co pb pbs xx obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct xx as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
intros INV NUM SP TDOK Mn KL KR KB KB2 KO7 KE7 KE KO SPB SP0'.
unfold LB0 in *. cbn [pf_newl pf_mxd] in *.
unfold SPV in SPB, SP0'. cbn [ts_stpos pf_mxd] in SPB, SP0'. set (sp := bv_unsigned stpos mod 2^32) in *.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK.
unfold pe_frame in FR. unfold pe_ms. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl]. unfold_consts.

assert (INtk : In (tk, 72) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) (TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs)))
by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, (32 * mxd)) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) (TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs)))
by (unfold pe_blocks; apply in_or_app; right; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 (proj1 REST) INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk S4L HIx _ _ _ _ q (32 * mxd) (proj1 REST) INq) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ tk 72 (proj1 REST) INtk) as Himg_t. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Himg_t.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hqhi.
assert (Htq : tk <> q).
{ pose proof (heap_blk_nodup S4L HIx _ _ _ _ (proj1 REST)) as ND. unfold pe_blocks in ND. rewrite map_app in ND. apply NoDup_app_remove_l in ND.
cbn [map blk_addr fst pf_tk pf_mxd] in ND. apply List.NoDup_cons_iff in ND as [Hni _]. intros E. apply Hni. left. symmetry. exact E. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tk 72 q (32 * mxd) (proj1 REST) INtk INq Htq) as Hdtq.
stash Himg_t. clear INtk INq.

pose proof (proj1 (proj2 REST) depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & JO & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
rewrite Hst in Hmode. destruct (inf_mode _ _ _ SS26 Hmode) as [-> ->].
cbn [name_ok pf_mxd] in NM0. destruct NM0 as [Hn0 Hnbs0].
destruct (tl_cs l) as [s0c|] eqn:Ecs; [exfalso; exact CLS0|]. cbn [jopt pf_mxd] in JO. destruct JO as [Hc0 Hcbs0].
assert (Eobjbs : objbs = []).
{ generalize (proj1 (proj2 (proj2 REST))). unfold cur_st. cbn [t_levels t_depth t_objbs pf_mxd]. rewrite Hl, Hst. cbn. intros E; exact E. }
subst objbs. clear LVd CLS0 Hmode.

assert (TDX : forall co' pb' pbs' x' obj' objbs', tdepth_ok (TST depth levels co' pb' pbs' x' obj' objs objbs'))
by (intros; eapply tdepth_ok_same; [reflexivity | reflexivity | reflexivity | exact TDOK]).
assert (FS' : fsaved F0 F) by exact FS.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.

assert (FIN70 : forall co1 (cb1 : byte) (stq : word) (j2x : list byte) mX (x1x a0x a1x a2x a3x a4x a5x : word) FX,
co <= co1 < len -> nth_error payload (Z.to_nat co1) = Some cb1 ->
PE_INV HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) payload me lo mX md A
(TST depth levels co1 pb pbs (TS isd stq (Z_to_bv 64 co1) err ucs high quote) obj objs []) cb1 j1 j2x utf sv errv ->
fsaved F0 FX -> dbl_special (Sem.reg_get FX (Z_to_bv 5 10)) ->
realizes rsegs (mkCfg (MS (mkR x1x (Z_to_bv 64 spf) gp (Z_to_bv 64 482928) t0 t1 t2 (Z_to_bv 64 tk) (Z_to_bv 64 oldl) a0x a1x a2x a3x a4x a5x a6 a7
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4 s5 s6 (Z_to_bv 64 26) (Z_to_bv 64 q) (Z_to_bv 64 (sb + co1)) (Z_to_bv 64 (Z.of_nat depth)) (Z_to_bv 64 79024) t3 t4 t5 t6)
FX (Z_to_bv 64 0x221f0) fc None mX (seg_rom rsegs)) md) T).
{ intros co1 cb1 stq j2x mX x1x a0x a1x a2x a3x a4x a5x FX Hco1 Hcb1 INVX FSX DBL.
pose proof INVX as [[_ (_ & _ & _ & TOKX & _ & _ & TSKX & FRX)] RESTX].
unfold tok_cells, tok_cells_g in TOKX. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_tk pf_spf pf_mxd] in TOKX, FRX, TSKX. unfold pe_frame in FRX.
pose proof (heap_model_ok _ _ _ _ _ _ (proj1 RESTX)) as MOKX.
pose proof (heap_mem_inv _ _ _ _ _ _ (proj1 RESTX)) as MIX. cbn [hl_segs S4L pf_mxd] in MIX.
pose proof RESTX as (HPX & _ & _ & STX & ERRX & _). cbn [pf_spf pf_mxd] in STX.
apply rz_evt; [exact MOKX|].
step.
apply evt_RZ_done.
eapply (json_object_new_double_cps HIx) with (LB := pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) (TST depth levels co1 pb pbs (TS isd stq (Z_to_bv 64 co1) err ucs high quote) obj objs [])) (lo := lo);
[ exact HPX | .. ]; try alloc_side.
all: try (rewrite ?unsigned_lit by lia; first [exact STX | exact ERRX]).
all: try (rewrite ?unsigned_lit by lia; unfold PE_FRAME in *; clia).
{ exact DBL. }
clear TOKX FRX MOKX.
intros ms2 md2 (m2 & A2 & r & errv2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & OUT).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp S4L pf_mxd] in *. rewrite ?(unsigned_lit spf) in ST2 by lia. rewrite ?(unsigned_lit spf) in HPR2 by lia.
assert (FS2' : fsaved F0 F2) by (eapply fsaved_trans; [exact FSX | exact FS2]).
specialize (FRM2 FRM).
pose proof INVX as [[_ (_ & _ & _ & TOKX & _ & _ & _ & FRX)] _].
unfold tok_cells, tok_cells_g in TOKX. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_tk pf_spf pf_mxd] in TOKX, FRX. unfold pe_frame in FRX.
assert (INtk2 : In (tk, 72) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) (TST depth levels co1 pb pbs (TS isd stq (Z_to_bv 64 co1) err ucs high quote) obj objs [])))
by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
assert (INq2 : In (q, (32 * mxd)) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) (TST depth levels co1 pb pbs (TS isd stq (Z_to_bv 64 co1) err ucs high quote) obj objs [])))
by (unfold pe_blocks; apply in_or_app; right; right; left; reflexivity).
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FRX; [| left; cbn; lia]. cbn [hl_segs S4L pf_mxd] in FRX.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in TOKX; [| eapply client_range_block; [exact INtk2 | lia | cbn; lia]]. cbn [hl_segs S4L pf_mxd] in TOKX.
apply (tstack_pres_g S4L _ _ _ _ _ _ HPR2 INq2) in TSKX; [| exact LEN32]. cbn [hl_segs S4L pf_mxd] in TSKX.
pose proof (srec_join8 _ _ _ (TSKX depth l Hl)) as Ld. cbn [le4 Z_to_le_bytes app hl_segs S4L pf_mxd] in Ld. rewrite Hc0, Hn0 in Ld.
remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld.
assert (OUT' : exists A2' NB, HEAP S4L HIx A2' (NB ++ pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) (TST depth levels co1 pb pbs (TS isd stq (Z_to_bv 64 co1) err ucs high quote) obj objs [])) m2 md2 /\
((r = 0 /\ NB = []) \/ (r <> 0 /\ jval rsegs S4F (Sdouble false) m2 NB r 1))).
{ destruct OUT as [(-> & HP2) | (Hr & NB & J2 & HP2)].
- exists A2, []. split; [exact HP2 | left; split; reflexivity].
- exists A2, NB. split; [exact HP2 | right; split; [exact Hr | exact J2]]. }
clear OUT. destruct OUT' as (A2' & NB & HP2 & OUT).
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI2. cbn [hl_segs S4L pf_mxd] in MI2.
pose proof (wmono_refl rsegs m2) as WM2. pose proof (munch_refl [(bse, bse + 32)] m2) as MU2.
stash TSKX. stash ST2. stash ERR2. stash HP2.
reenter MOK2.
step. norm_sx32. step.
step. rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
step. replace (q + Z.of_nat depth * 32) with bse by lia.
step.
unstash TSKX. unstash ST2. unstash ERR2. unstash HP2.
destruct OUT as [[-> ->] | [Hr J2]].
-
step. if_true. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
match goal with L8 : rw_cells rsegs mc bse (?c1 :: ?rest) |- _ =>
pose proof (rw_cells_recast_prefix rsegs mc bse [c1] [C4 (Z_to_bv 64 (tl_st l)); C4 (Z_to_bv 64 (tl_ss l))]
rest L8 ltac:(cbn; repeat split) eq_refl eq_refl) as L5; cbn [app pf_mxd] in L5
end end.
apply evt_RZ_done. eapply KE; [ | apply TDX | exact FS2' | exact FRM2]. clear KL KR KB KB2 KO7 KE7 KE KO.
apply (PE_INV_W HIx).
lazymatch goal with |- PE_INV _ _ _ _ _ _ _ ?mc _ _ _ _ _ _ _ _ _ =>
eapply (keep_inv HIx _ q _ payload me lo mX m2 mc md md2 A A2' _ l cb1 j1 j2x utf sv errv errv2 bse);
[ exact STC | exact INVX | exact Hl | exact Hcbs0 | exact Hnbs0 | exact HPR2 | exact VM2 | cbn [app pf_mxd] in HP2; exact HP2 | exact ST2 | exact ERR2
| exact Hbse | exact MU2 | exact WM2 | assumption | unfold srec_cells; rewrite Hc0, Hn0; exact L5 | eassumption | eassumption ]
end.
-
assert (HrR : 0 < r < 2^64).
{ destruct J2 as (pbp & PBS & RB & ENB & OPB & bits & ERB & DS & CELLS).
pose proof (heap_blk S4L HIx _ _ _ _ r 48 HP2 ltac:(apply in_or_app; left; rewrite ENB, ERB; left; reflexivity)) as (_ & _ & HB1 & HB2 & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in HB2. lia. }
step. if_falsex.
step. step. stepz. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
match goal with L8 : rw_cells rsegs mc bse _ |- _ =>
pose proof (rw_cells_recast_prefix rsegs mc bse [C8 (Z_to_bv 64 8589934592)] [C4 (Z_to_bv 64 ST_eatws); C4 (Z_to_bv 64 ST_finish)]
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 r); C8 (Z_to_bv 64 0)] L8 ltac:(cbn; repeat split)
ltac:(apply bytes_eq_by_unsigned; vm_compute; reflexivity) eq_refl) as L5; cbn [app pf_mxd] in L5
end end.
apply evt_RZ_done.
eapply (KR (TST depth (lupd levels depth (TL ST_eatws ST_finish r (Some (Sdouble false)) NB 0 [])) co1 pb pbs (TS isd stq (Z_to_bv 64 co1) err ucs high quote) obj objs []));
clear KL KR KB KB2 KO7 KE7 KE KO.
+ unfold mredo, mbase, cur_st, cur_ss in Mn |- *. cbn [t_co t_levels t_depth pf_len pf_mxd] in Mn |- *. rewrite nth_error_lupd_eq by lia. rewrite Hl, Hst in Mn.
cbn [tl_st tl_ss pf_mxd]. unfold rank in Mn |- *. cbn -[Nat.mul Nat.add Z.to_nat Z.sub] in Mn |- *. lia.
+ lazymatch goal with |- PE_INV _ _ _ _ _ _ _ ?mc _ _ _ _ _ _ _ _ _ =>
eapply (setcur_inv HIx _ q _ payload me lo mX m2 mc md md2 A A2' (TST depth levels co1 pb pbs (TS isd stq (Z_to_bv 64 co1) err ucs high quote) obj objs []) l
cb1 j1 j2x utf sv errv errv2 NB r (Some (Sdouble false)) bse);
[ exact STC | exact INVX | exact Hl | exact Hc0 | exact Hcbs0 | exact Hn0 | exact Hnbs0 | reflexivity
| exact HPR2 | exact VM2 | cbn [app pf_mxd] in HP2; exact HP2 | exact ST2 | exact ERR2
| cbn [jres pf_mxd]; split; [exact Hr | exact J2] | exact Hbse | exact MU2 | exact WM2 | assumption | exact L5 | eassumption | eassumption ]
end.
+ cbn; lia.
+ exact Hcb1.
+ unfold NUMC, cur_st; cbn [t_levels t_depth pf_mxd]; rewrite nth_error_lupd_eq by lia; cbn; intros E; discriminate E.
+ unfold SPOK, cur_st; cbn [t_levels t_depth pf_mxd]; rewrite nth_error_lupd_eq by lia; cbn; intros E; discriminate E.
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs [])); [apply TDX | exact Hl | rewrite Ecs; cbn; lia | cbn; lia | reflexivity].
+ exact FS2'.
+ exact FRM2. }

assert (DONE14 : forall co1 (cb1 : byte) (stq : word) (j2x : list byte) mX (x1x a0x a1x a2x a3x a4x a5x : word),
co <= co1 < len -> nth_error payload (Z.to_nat co1) = Some cb1 ->
PE_INV HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) payload me lo mX md A
(TST depth levels co1 pb pbs (TS isd stq (Z_to_bv 64 co1) err ucs high quote) obj objs []) cb1 j1 j2x utf sv errv ->
realizes rsegs (mkCfg (MS (mkR x1x (Z_to_bv 64 spf) gp (Z_to_bv 64 482928) t0 t1 t2 (Z_to_bv 64 tk) (Z_to_bv 64 oldl) a0x a1x a2x a3x a4x a5x a6 a7
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4 s5 s6 (Z_to_bv 64 26) (Z_to_bv 64 q) (Z_to_bv 64 (sb + co1)) (Z_to_bv 64 (Z.of_nat depth)) (Z_to_bv 64 79024) t3 t4 t5 t6)
F (Z_to_bv 64 0x21f94) fc None mX (seg_rom rsegs)) md) T).
{ intros co1 cb1 stq j2x mX x1x a0x a1x a2x a3x a4x a5x Hco1 Hcb1 INVX.
pose proof INVX as [[_ (_ & _ & _ & TOKX & PBX & _ & _ & FRX)] RESTX].
unfold tok_cells, tok_cells_g in TOKX. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_tk pf_spf pf_mxd] in TOKX, PBX, FRX.
pose proof (heap_model_ok _ _ _ _ _ _ (proj1 RESTX)) as MOKX.
pose proof (heap_mem_inv _ _ _ _ _ _ (proj1 RESTX)) as MIX. cbn [hl_segs S4L pf_mxd] in MIX.
pose proof (pbuf_cstr mX pbs pb PBX) as (buf & bpos & cap & str & rest & Epbs & Hbpos & Hcap & PBH & BUFS & NIN & Lstr & Lcap).
assert (INbuf : In (buf, cap) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) (TST depth levels co1 pb pbs (TS isd stq (Z_to_bv 64 co1) err ucs high quote) obj objs [])))
by (unfold pe_blocks, tstate_blocks; cbn [t_pbs t_objbs t_levels pf_mxd]; rewrite Epbs; apply in_or_app; left; apply in_or_app; left; right; left; reflexivity).
assert (INpb : In (pb, 16) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) (TST depth levels co1 pb pbs (TS isd stq (Z_to_bv 64 co1) err ucs high quote) obj objs [])))
by (unfold pe_blocks, tstate_blocks; cbn [t_pbs t_objbs t_levels pf_mxd]; rewrite Epbs; apply in_or_app; left; apply in_or_app; left; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ buf cap (proj1 RESTX) INbuf) as (_ & _ & Hbuflo & Hbufhi & _).
pose proof (heap_blk S4L HIx _ _ _ _ pb 16 (proj1 RESTX) INpb) as (_ & _ & Hpblo & Hpbhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hbufhi, Hpbhi. clear INbuf INpb.
assert (Ech : exists ch tl, str ++ b0 :: rest = ch :: tl) by (destruct str as [|c' s']; cbn; eauto).
destruct Ech as (ch & tl & Ech). rewrite Ech in BUFS.
pose proof (payload_byte mX buf (ch :: tl) 0 ch BUFS eq_refl ltac:(lia)) as RDB. rewrite Z.add_0_r in RDB.
pose proof (bv_unsigned_in_range 8 ch) as CHR; unfold bv_modulus in CHR; cbn in CHR.
apply rz_evt; [exact MOKX|].
step. step. norm_sx32.
step. destruct (Z.eq_dec bpos 0) as [B0|B0].
-
if_truex. pose proof (pinf_ro mX MIX) as PINF. step. step.
apply evt_RZ_done. eapply (FIN70 co1 cb1 stq j2x mX); [lia | exact Hcb1 | exact INVX | eapply fsaved_trans; [exact FS' | apply fsaved_set10] | ].
unfold dbl_special; rewrite reg_get_set_same_u by (vm_compute; reflexivity); apply Z.leb_le; vm_compute; reflexivity.
- if_falsex. step. step. change (zxb ch) with (Z_to_bv 64 (bv_unsigned ch)).
step. step. step. step. step. step.
destruct (Z.eq_dec (bv_unsigned ch) 45) as [E45|N45].
+
replace (Z_to_bv 64 (79008 + bv_unsigned (v_sltiu (Z_to_bv 64 (bv_unsigned ch + -45)) 1) ≪ 3)) with (Z_to_bv 64 79016)
by (rewrite E45; apply bv_eq; vm_compute; reflexivity).
pose proof (ninf_ro mX MIX) as NINF. step. step.
apply evt_RZ_done. eapply (FIN70 co1 cb1 stq j2x mX); [lia | exact Hcb1 | exact INVX | eapply fsaved_trans; [exact FS' | apply fsaved_set10] | ].
unfold dbl_special; rewrite reg_get_set_same_u by (vm_compute; reflexivity); apply Z.leb_le; vm_compute; reflexivity.
+
replace (Z_to_bv 64 (79008 + bv_unsigned (v_sltiu (Z_to_bv 64 (bv_unsigned ch + -45)) 1) ≪ 3)) with (Z_to_bv 64 79008).
2:{ unfold v_sltiu. change (bv_wrap 64 1) with 1.
replace (bv_unsigned (Z_to_bv 64 (bv_unsigned ch + -45)) <? 1) with false; [rewrite (unsigned_lit 0) by lia; reflexivity|].
symmetry. apply Z.ltb_ge. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616.
destruct (Z.lt_ge_cases (bv_unsigned ch) 45).
* replace (bv_unsigned ch + -45) with ((bv_unsigned ch + -45 + 18446744073709551616) + (-1) * 18446744073709551616) by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
* rewrite Z.mod_small by lia. lia. }
pose proof (pinf2_ro mX MIX) as PINF. step. step.
apply evt_RZ_done. eapply (FIN70 co1 cb1 stq j2x mX); [lia | exact Hcb1 | exact INVX | eapply fsaved_trans; [exact FS' | apply fsaved_set10] | ].
unfold dbl_special; rewrite reg_get_set_same_u by (vm_compute; reflexivity); apply Z.leb_le; vm_compute; reflexivity. }

assert (HWP : Forall (pe_private (PEF tk oldl newl len lenr sb spf pmd mxd fl) q pbs) [(tk, tk + 72); (spf, spf + 144)]).
{ apply pe_wtf_private. apply Forall_cons; [left; cbn [fst snd pf_tk pf_mxd]; lia|].
apply Forall_cons; [right; unfold PE_FRAME; cbn [fst snd pf_spf pf_mxd]; lia | apply Forall_nil]. }
assert (LP : forall (nn : nat) (k co1 : Z) (cb1 : byte) (stq : word) (j2x : list byte) (a5x a3x : word) mX,
8 - k <= Z.of_nat nn -> 0 <= k <= 7 -> co <= co1 < len -> nth_error payload (Z.to_nat co1) = Some cb1 ->
PE_INV HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) payload me lo mX md A
(TST depth levels co1 pb pbs (TS isd stq (Z_to_bv 64 co1) err ucs high quote) obj objs []) cb1 j1 j2x utf sv errv ->
realizes rsegs (mkCfg (MS (mkR x1 (Z_to_bv 64 spf) gp (Z_to_bv 64 482928) t0 t1 t2 (Z_to_bv 64 tk) (Z_to_bv 64 oldl)
(Z_to_bv 64 (77824 + k)) (Z_to_bv 64 (69297 + k)) (Z_to_bv 64 (k + 1)) a3x (Z_to_bv 64 (bv_unsigned cb1)) a5x a6 a7
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4 s5 s6 (Z_to_bv 64 26) (Z_to_bv 64 q) (Z_to_bv 64 (sb + co1)) (Z_to_bv 64 (Z.of_nat depth)) (Z_to_bv 64 79024) t3 t4 t5 t6)
F (Z_to_bv 64 0x21edc) fc None mX (seg_rom rsegs)) md) T).
{ induction nn as [|nn IH]; intros k co1 cb1 stq j2x a5x a3x mX Hnn Hk Hco1 Hcb1 INVX; [exfalso; lia|].
pose proof INVX as [[_ (_ & _ & _ & TOKX & PBX & _ & TSKX & FRX)] RESTX].
unfold tok_cells, tok_cells_g in TOKX. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_tk pf_spf pf_mxd] in TOKX, PBX, FRX, TSKX. unfold pe_frame in FRX.
pose proof (heap_model_ok _ _ _ _ _ _ (proj1 RESTX)) as MOKX.
pose proof (heap_mem_inv _ _ _ _ _ _ (proj1 RESTX)) as MIX. cbn [hl_segs S4L pf_mxd] in MIX.
pose proof RESTX as (HPX & _ & _ & _ & _ & STRX & PLENX & SBinX & _). cbn [pf_sb pf_md pf_mxd pf_fl] in STRX.
destruct (nth_error infbytes (Z.to_nat k)) as [ib|] eqn:Hib; [| exfalso; apply nth_error_None in Hib; rewrite infbytes_len in Hib; lia].
destruct (nth_error invbytes (Z.to_nat k)) as [vb|] eqn:Hvb; [| exfalso; apply nth_error_None in Hvb; rewrite invbytes_len in Hvb; lia].
pose proof (payload_byte mX 77824 infbytes k ib (infbytes_at mX MIX) Hib ltac:(lia)) as RDI.
pose proof (payload_byte mX 69297 invbytes k vb (invbytes_at mX MIX) Hvb ltac:(lia)) as RDV.
pose proof (bv_unsigned_in_range 8 ib) as IBR; unfold bv_modulus in IBR; cbn in IBR.
pose proof (bv_unsigned_in_range 8 vb) as VBR; unfold bv_modulus in VBR; cbn in VBR.
pose proof (bv_unsigned_in_range 8 cb1) as CBR1; unfold bv_modulus in CBR1; cbn in CBR1.
pose proof (wmono_refl rsegs mX) as WM. pose proof (munch_refl [(tk, tk + 72); (spf, spf + 144)] mX) as MU.

assert (JOIN48 : forall mc (c' : byte) (nv a3y a5y : word),
co1 + 1 < len -> nth_error payload (Z.to_nat (co1 + 1)) = Some c' ->
rw_cells rsegs mc tk (tok_cells_g mxd fl pb (Z.of_nat depth) q (TS isd (Z_to_bv 64 (k + 1)) (Z_to_bv 64 (co1 + 1)) err ucs high quote)) ->
rw_cells rsegs mc spf [C8 (Z_to_bv 64 obj); CB 16 j1; C4 nv; CB 3 (skipn 4 j2x); C1 cb1; CB 8 utf;
C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv); C8 (pe_s7 sv); C8 (pe_s6 sv);
C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)] ->
munch [(tk, tk + 72); (spf, spf + 144)] mX mc -> wmono rsegs mX mc -> mem_inv rsegs mc ->
evt rsegs (RZ rsegs md T)
(MS (mkR x1 (Z_to_bv 64 spf) gp (Z_to_bv 64 482928) t0 t1 t2 (Z_to_bv 64 tk) (Z_to_bv 64 oldl)
(Z_to_bv 64 (77824 + k)) (Z_to_bv 64 (69297 + k)) (Z_to_bv 64 (k + 1)) a3y (Z_to_bv 64 (bv_unsigned c')) a5y a6 a7
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4 s5 s6 (Z_to_bv 64 26) (Z_to_bv 64 q) (Z_to_bv 64 (sb + (co1 + 1))) (Z_to_bv 64 (Z.of_nat depth)) (Z_to_bv 64 79024) t3 t4 t5 t6)
F (Z_to_bv 64 0x21ec4) fc None mc (seg_rom rsegs))).
{ intros mc c' nv a3y a5y Hco' Hc' TOKc FRc MUc WMc MIc.
clear TOKX FRX RDI RDV. stash PBX. stash TSKX.
unfold tok_cells_g in TOKc. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOKc.
pose proof (bv_unsigned_in_range 8 c') as CBR'; unfold bv_modulus in CBR'; cbn in CBR'.
step. rewrite le1_zxw. mem_after_store.
step. step. norm_w32. step. step.
step.
destruct (Z.eq_dec (k + 2) 9) as [K7 | K7].
-
if_truex. apply evt_RZ_done.
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?m2 _) _) _ =>
lazymatch goal with TOK2 : rw_cells rsegs m2 tk _ |- _ =>
lazymatch goal with FR2 : rw_cells rsegs m2 spf _ |- _ =>
eapply (DONE14 (co1 + 1) c' (Z_to_bv 64 (k + 1)) (le4 nv ++ skipn 4 j2x) m2); [lia | exact Hc' |];
eapply (PE_INV_retok_nb _ q _ payload me lo mX m2 md A (TST depth levels co1 pb pbs (TS isd stq (Z_to_bv 64 co1) err ucs high quote) obj objs []));
[exact STC | exact INVX | exact MUc | exact WMc | exact MIc | exact TOK2 | cbn; lia | reflexivity | apply pe_frame_nb_set; exact FR2]
end end end.
- if_falsex. apply evt_RZ_done.
replace (Z_to_bv 64 (77824 + k + 1)) with (Z_to_bv 64 (77824 + (k + 1))) by (f_equal; lia).
replace (Z_to_bv 64 (69297 + k + 1)) with (Z_to_bv 64 (69297 + (k + 1))) by (f_equal; lia).
replace (Z_to_bv 64 (k + 2)) with (Z_to_bv 64 ((k + 1) + 1)) by (f_equal; lia).
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?m2 _) _) _ =>
lazymatch goal with TOK2 : rw_cells rsegs m2 tk _ |- _ =>
lazymatch goal with FR2 : rw_cells rsegs m2 spf _ |- _ =>
eapply (IH (k + 1) (co1 + 1) c' (Z_to_bv 64 (k + 1)) (le4 nv ++ skipn 4 j2x) _ _ m2); [lia | lia | lia | exact Hc' |];
eapply (PE_INV_retok_nb _ q _ payload me lo mX m2 md A (TST depth levels co1 pb pbs (TS isd stq (Z_to_bv 64 co1) err ucs high quote) obj objs []));
[exact STC | exact INVX | exact MUc | exact WMc | exact MIc | exact TOK2 | cbn; lia | reflexivity | apply pe_frame_nb_set; exact FR2]
end end end. }

assert (JOINS : forall mc (c' : byte) (nv a3v a4x a5y : word),
co1 + 1 < len -> nth_error payload (Z.to_nat (co1 + 1)) = Some c' ->
rw_cells rsegs mc tk (tok_cells_g mxd fl pb (Z.of_nat depth) q (TS isd (Z_to_bv 64 (k + 1)) (Z_to_bv 64 (co1 + 1)) err ucs high quote)) ->
rw_cells rsegs mc spf [C8 (Z_to_bv 64 obj); CB 16 j1; C4 nv; CB 3 (skipn 4 j2x); C1 cb1; CB 8 utf;
C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv); C8 (pe_s7 sv); C8 (pe_s6 sv);
C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)] ->
munch [(tk, tk + 72); (spf, spf + 144)] mX mc -> wmono rsegs mX mc -> mem_inv rsegs mc ->
evt rsegs (RZ rsegs md T)
(MS (mkR x1 (Z_to_bv 64 spf) gp (Z_to_bv 64 482928) t0 t1 t2 (Z_to_bv 64 tk) (Z_to_bv 64 oldl)
(Z_to_bv 64 (77824 + k)) (Z_to_bv 64 (69297 + k)) (Z_to_bv 64 (k + 1)) a3v a4x a5y a6 a7
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4 s5 s6 (Z_to_bv 64 26) (Z_to_bv 64 q) (Z_to_bv 64 (sb + (co1 + 1))) (Z_to_bv 64 (Z.of_nat depth)) (Z_to_bv 64 79024) t3 t4 t5 t6)
F (Z_to_bv 64 0x21f48) fc None mc (seg_rom rsegs))).
{ intros mc c' nv a3v a4x a5y Hco' Hc' TOKc FRc MUc WMc MIc.
clear TOKX FRX RDI RDV. stash PBX. stash TSKX.
unfold tok_cells_g in TOKc. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOKc.
step. try mem_after_store.

pose proof (payload_private HIx _ _ _ (TST depth levels co1 pb pbs (TS isd stq (Z_to_bv 64 co1) err ucs high quote) obj objs []) _ _ _ _ _ _ _
STC HPX STRX PLENX SBinX MUc HWP) as STR'. cbn [pf_sb pf_mxd] in STR'.
pose proof (payload_byte _ _ _ _ _ STR' Hc' ltac:(lia)) as RDC'.
pose proof (bv_unsigned_in_range 8 c') as CBR'; unfold bv_modulus in CBR'; cbn in CBR'.
step. change (zxb c') with (Z_to_bv 64 (bv_unsigned c')).
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m' _) =>
lazymatch goal with FR' : rw_cells rsegs m' spf _ |- _ =>
eapply (JOIN48 m' c'); [exact Hco' | exact Hc' | exact TOKc | exact FR' | exact MUc | exact WMc | exact MIc]
end end. }
apply rz_evt; [exact MOKX|].

assert (T80 : forall a5y, bv_unsigned cb1 <> 0 -> evt rsegs (RZ rsegs md T)
(MS (mkR x1 (Z_to_bv 64 spf) gp (Z_to_bv 64 482928) t0 t1 t2 (Z_to_bv 64 tk) (Z_to_bv 64 oldl)
(Z_to_bv 64 (77824 + k)) (Z_to_bv 64 (69297 + k)) (Z_to_bv 64 (k + 1)) a3x (Z_to_bv 64 (bv_unsigned cb1)) a5y a6 a7
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4 s5 s6 (Z_to_bv 64 26) (Z_to_bv 64 q) (Z_to_bv 64 (sb + co1)) (Z_to_bv 64 (Z.of_nat depth)) (Z_to_bv 64 79024) t3 t4 t5 t6)
F (Z_to_bv 64 0x21f00) fc None mX (seg_rom rsegs))).
2:{ step. change (zxb ib) with (Z_to_bv 64 (bv_unsigned ib)). step.
destruct (Z.eq_dec (bv_unsigned cb1) (bv_unsigned ib)) as [E1|N1]; [if_truex; apply T80; rewrite E1; exact (infbytes_nz _ _ Hib ltac:(lia))|]. if_falsex.

pose proof (tok_flags_byte_g mxd fl mX tk pb (Z.of_nat depth) q (TS isd stq (Z_to_bv 64 co1) err ucs high quote) TOKX) as RDF.
step. rewrite (zxb_byte fl) by lia.
step. rewrite (unsigned_lit (fl mod 256)) by (pose proof (Z.mod_pos_bound fl 256 ltac:(lia)); lia). rewrite (land_mod256 fl 1) by lia.
destruct (land1_cases fl) as [FL1 | FL1]; rewrite FL1.
-
step. if_true.
step. change (zxb vb) with (Z_to_bv 64 (bv_unsigned vb)). step.
destruct (Z.eq_dec (bv_unsigned cb1) (bv_unsigned vb)) as [E2|N2]; [if_truex; apply T80; rewrite E2; exact (invbytes_nz _ _ Hvb ltac:(lia))|]. if_falsex.

step. step. step. apply evt_RZ_done. eapply (KE _ [] co1 (Z_to_bv 64 4)); [apply (PE_INV_W HIx); exact INVX | apply TDX | exact FS' | exact FRM].
-
step. if_false.
step. step. step. apply evt_RZ_done. eapply (KE _ [] co1 (Z_to_bv 64 4)); [apply (PE_INV_W HIx); exact INVX | apply TDX | exact FS' | exact FRM]. }
intros a5y Hnz.

stash PBX. stash RESTX. stash TSKX. stash STRX. clear HPX.
step. norm_sx32. step. norm_w32. step. step.
step.
destruct (peek_cases (PEF tk oldl newl len lenr sb spf pmd mxd fl) payload co1 cb1 LENR CSTR (proj1 RR) ltac:(cbn [pf_len pf_mxd]; lia) ltac:(cbn [pf_len pf_mxd]; lia) Hcb1 Hnz)
as [[Elenr Heof] | [Hne Hmore]]; [cbn [pf_len pf_lenr pf_mxd] in Elenr, Heof; subst lenr; pose (lenr := len) | cbn [pf_len pf_lenr pf_mxd] in Hne, Hmore].
{
if_falsex. step. unstash PBX. unstash RESTX. unstash TSKX. apply evt_RZ_done.
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mc _) _) _ =>
eapply (pe_eof38 HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) payload me lo mc md A
(TST depth levels len pb pbs (TS isd (Z_to_bv 64 (k + 1)) (Z_to_bv 64 len) err ucs high quote) obj objs []) co1 cb1);
[ exact STC
| eapply (PE_INV_retok HIx _ q _ payload me lo mX mc md A (TST depth levels co1 pb pbs (TS isd stq (Z_to_bv 64 co1) err ucs high quote) obj objs []));
[exact STC | exact INVX | exact MU | exact WM | assumption | rewrite <- Heof; eassumption | cbn; lia | reflexivity | exact FRX]
| reflexivity
| unfold ts_set_err; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd];
intros; eapply KO; [apply (PE_INV_W HIx); eassumption | apply TDX | exact FS' | exact FRM] ]
end. }
if_truex.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
match goal with TOK1 : rw_cells rsegs m1 tk _ |- _ =>
pose proof (tok_flags_byte_g mxd fl m1 tk pb (Z.of_nat depth) q (TS isd (Z_to_bv 64 (k + 1)) (Z_to_bv 64 (co1 + 1)) err ucs high quote) TOK1) as RDF;
assert (INV1 : PE_INV HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) payload me lo m1 md A
(TST depth levels (co1 + 1) pb pbs (TS isd (Z_to_bv 64 (k + 1)) (Z_to_bv 64 (co1 + 1)) err ucs high quote) obj objs []) cb1 j1 j2x utf sv errv)
by (eapply (PE_INV_retok HIx _ q _ payload me lo mX m1 md A (TST depth levels co1 pb pbs (TS isd stq (Z_to_bv 64 co1) err ucs high quote) obj objs []));
[exact STC | exact INVX | exact MU | exact WM | assumption | exact TOK1 | cbn; lia | reflexivity | exact FRX])
end end.
step. rewrite (zxb_byte fl) by lia.
step.
replace (Z_to_bv 64 (sb + co1 + 1)) with (Z_to_bv 64 (sb + (co1 + 1))) by (f_equal; lia).
destruct (nth_error payload (Z.to_nat (co1 + 1))) as [c'|] eqn:Hc'.
2:{ exfalso. apply nth_error_None in Hc'. pose proof INV1 as [_ (_ & _ & _ & _ & _ & _ & PLEN1 & _)]. cbn [pf_len pf_mxd] in PLEN1. lia. }
pose proof INV1 as [_ (_ & _ & _ & _ & _ & STR1 & _)]. cbn [pf_sb pf_md pf_mxd pf_fl] in STR1.
pose proof (payload_byte _ _ _ _ _ STR1 Hc' ltac:(lia)) as RDC.
pose proof (bv_unsigned_in_range 8 c') as CBR'; unfold bv_modulus in CBR'; cbn in CBR'.
stash INV1.
step. change (zxb c') with (Z_to_bv 64 (bv_unsigned c')).
step. rewrite (unsigned_lit (fl mod 256)) by (pose proof (Z.mod_pos_bound fl 256 ltac:(lia)); lia). rewrite (land_mod256 fl 16) by lia.
assert (Hco' : co1 + 1 < len) by lia.
destruct (land16_cases fl) as [F16 | F16]; rewrite F16.
-
step. if_true.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
lazymatch goal with TOK1 : rw_cells rsegs m1 tk _ |- _ =>
lazymatch goal with FR1 : rw_cells rsegs m1 spf _ |- _ =>
eapply (JOIN48 m1 c' (nbw j2x)); [exact Hco' | reflexivity | exact TOK1 | exact FR1 | exact MU | exact WM | assumption]
end end end.
-
step. if_false.
Local Ltac if_any := lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd; cbv iota end.
Local Ltac err14 INV1 KE TDX FS' FRM co1 :=
step; step; step; apply evt_RZ_done; unstash INV1;
eapply (KE _ [] (co1 + 1) (Z_to_bv 64 14)); [apply PE_INV_W; exact INV1 | apply TDX | exact FS' | exact FRM].
step. if_any.
+
step. step. if_any.
*
step. step. step. if_any.
--  step. step. step. if_any.
++  step. step. step. if_any.
**  step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
lazymatch goal with TOK1 : rw_cells rsegs m1 tk _ |- _ =>
lazymatch goal with FR1 : rw_cells rsegs m1 spf _ |- _ =>
eapply (JOINS m1 c' (nbw j2x)); [exact Hco' | reflexivity | exact TOK1 | exact FR1 | exact MU | exact WM | assumption]
end end end.
**  err14 INV1 KE TDX FS' FRM co1.
++  step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
lazymatch goal with TOK1 : rw_cells rsegs m1 tk _ |- _ =>
lazymatch goal with FR1 : rw_cells rsegs m1 spf _ |- _ =>
eapply (JOINS m1 c' (nbw j2x)); [exact Hco' | reflexivity | exact TOK1 | exact FR1 | exact MU | exact WM | assumption]
end end end.
--  step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
lazymatch goal with TOK1 : rw_cells rsegs m1 tk _ |- _ =>
lazymatch goal with FR1 : rw_cells rsegs m1 spf _ |- _ =>
eapply (JOINS m1 c' (nbw j2x)); [exact Hco' | reflexivity | exact TOK1 | exact FR1 | exact MU | exact WM | assumption]
end end end.
*
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
lazymatch goal with TOK1 : rw_cells rsegs m1 tk _ |- _ =>
lazymatch goal with FR1 : rw_cells rsegs m1 spf _ |- _ =>
eapply (JOIN48 m1 c' (nbw j2x)); [exact Hco' | reflexivity | exact TOK1 | exact FR1 | exact MU | exact WM | assumption]
end end end.
+
step. step. step. step. if_any.
*  step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
lazymatch goal with TOK1 : rw_cells rsegs m1 tk _ |- _ =>
lazymatch goal with FR1 : rw_cells rsegs m1 spf _ |- _ =>
eapply (JOINS m1 c' (nbw j2x)); [exact Hco' | reflexivity | exact TOK1 | exact FR1 | exact MU | exact WM | assumption]
end end end.
*  err14 INV1 KE TDX FS' FRM co1. }

pose proof REST as (_ & _ & _ & _ & _ & STR & _). cbn [pf_sb pf_md pf_mxd pf_fl] in STR.
pose proof (payload_byte _ _ _ _ _ STR Hcb ltac:(lia)) as RDC.
clear PB TSK.
apply rz_evt; [exact MOK|].
step. rewrite (sx32_small_mod stpos) by lia. fold sp.
step. step.
destruct (Z.lt_ge_cases 7 sp) as [Hs|Hs].
-
if_truex. apply evt_RZ_done. eapply (DONE14 co cb stpos j2 m); [lia | exact Hcb | exact INV].
- if_falsex. step. try norm_sx32.
step. change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)).
step. step. step. step. step. step. step. step.
apply evt_RZ_done. eapply (LP 8%nat sp co cb stpos j2 _ _ m); [lia | lia | lia | exact Hcb | exact INV].
Qed.
End PeInf.

End RC__1.
End Mq0.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEQM.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qtgi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qtgi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QC8c.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkMG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkMG.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QG8z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QG8z. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdyh.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2Sr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2Sr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLbz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLbz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QIsM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QIsM.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qa8x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qa8x.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXfU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXfU.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXfU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXfU.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMdR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMdR.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qebo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qebo. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qzoi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qzoi.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBpZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBpZ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QT7i.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QT7i. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qv6q.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qv6q.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QzWc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QzWc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgoP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgoP.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qtqc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qtqc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QClN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QClN.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeBool.
Variable HIx : heap_iface S4L.
Hypothesis MEMMOVE : memmove_stmt.
#[using="MEMMOVE"] Lemma case_bool : forall (pf : pe_fix) (q : Z) (LBc : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(sv : pe_saved) (T : TSet) (F0 : bvmap 5 word) (utf8rep : list byte),
CASE HIx pf q LBc payload me lo sv T F0 utf8rep ST_boolean.
Proof.
intros pf q LBc payload me lo sv T F0 utf8rep.
unfold CASE. intros n ts l m md A cb j1 j2 utf errv x1 gp t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 t3 t4 t5 t6 F fc.
change (pe_jt ST_boolean) with 138140.
intros STC INV Hl Hst Hco Hcb NUM SP TDOK UTF GOTF CSTR FS FRM Mn (KL & KR & KB & KB2) KO7 KE7.
pose proof (KERR_of_7 _ _ _ _ _ _ _ _ _ _ KE7) as KE.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
pose proof INV as [CORE REST].
pose proof CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof (heap_model_ok _ _ _ _ _ _ (proj1 REST)) as MOK.

assert (SPB : SPV (t_x ts) <= t_co ts) by (unfold SPOK in SP; specialize (SP ltac:(unfold cur_st; rewrite Hl, Hst; reflexivity)); lia).
assert (SP0' : 0 <= SPV (t_x ts)) by (unfold SPV; apply Z.mod_pos_bound; lia).
revert INV NUM SP TDOK Mn KL KR KB KB2 KO7 KE7 KE SPB SP0'.
destruct ts as [depth levels co pb pbs xx obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct xx as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
intros INV NUM SP TDOK Mn KL KR KB KB2 KO7 KE7 KE SPB SP0'.
unfold LB0 in *. cbn [pf_newl pf_mxd] in *.
unfold SPV in SPB, SP0'. cbn [ts_stpos pf_mxd] in SPB, SP0'. set (sp := bv_unsigned stpos mod 2^32) in *.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK.
unfold pe_frame in FR. unfold pe_ms. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl]. unfold_consts.

assert (INtk : In (tk, 72) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) (TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs)))
by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, (32 * mxd)) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) (TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs)))
by (unfold pe_blocks; apply in_or_app; right; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 (proj1 REST) INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk S4L HIx _ _ _ _ q (32 * mxd) (proj1 REST) INq) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ tk 72 (proj1 REST) INtk) as Himg_t. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Himg_t.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hqhi.
assert (Htq : tk <> q).
{ pose proof (heap_blk_nodup S4L HIx _ _ _ _ (proj1 REST)) as ND. unfold pe_blocks in ND. rewrite map_app in ND. apply NoDup_app_remove_l in ND.
cbn [map blk_addr fst pf_tk pf_mxd] in ND. apply List.NoDup_cons_iff in ND as [Hni _]. intros E. apply Hni. left. symmetry. exact E. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tk 72 q (32 * mxd) (proj1 REST) INtk INq Htq) as Hdtq.
stash Himg_t. clear INtk INq.

pose proof (proj1 (proj2 REST) depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & JO & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
rewrite Hst in Hmode. destruct (bool_mode _ _ _ SS26 Hmode) as [-> ->].
cbn [name_ok pf_mxd] in NM0. destruct NM0 as [Hn0 Hnbs0].
destruct (tl_cs l) as [s0c|] eqn:Ecs; [exfalso; exact CLS0|]. cbn [jopt pf_mxd] in JO. destruct JO as [Hc0 Hcbs0].
assert (Eobjbs : objbs = []).
{ generalize (proj1 (proj2 (proj2 REST))). unfold cur_st. cbn [t_levels t_depth t_objbs pf_mxd]. rewrite Hl, Hst. cbn. intros E; exact E. }
subst objbs. clear LVd CLS0 Hmode.

assert (TDX : forall co' pb' pbs' x' obj' objbs', tdepth_ok (TST depth levels co' pb' pbs' x' obj' objs objbs'))
by (intros; eapply tdepth_ok_same; [reflexivity | reflexivity | reflexivity | exact TDOK]).
clear PB TSK REST CORE.
apply rz_evt; [exact MOK|].
step. step. step. step.
apply evt_RZ_done.
eapply (pe_mapp HIx MEMMOVE (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) payload me lo m md A
(TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs []) co 0x21bac (spf + 31) 1 [cb] cb);
[exact STC | exact INV | exact (pe_frame_cbyte _ _ _ _ _ _ _ _ FR) | reflexivity | lia | left; cbn [pf_spf pf_mxd]; unfold PE_FRAME; lia | reflexivity | lia |].
unfold ts_set_pbs; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_oldl pf_newl pf_len pf_sb pf_tk pf_spf pf_md pf_mxd pf_fl].
clear TOK FR MOK INV NUM. clear m.
intros m md1 A1 pbs1 errv1 r t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F1 fc1 INV Hr FS1 FRM1.
unfold pe_ms; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl].
assert (FS1' : fsaved F0 F1) by (eapply fsaved_trans; [exact FS | exact FS1]). specialize (FRM1 FRM). clear FS FS1 FRM F fc.
pose proof INV as [CORE REST].
pose proof CORE as (_ & _ & _ & _ & TOK & PB & _ & TSK & FR).
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj pf_tk pf_spf pf_mxd] in TOK, PB, TSK, FR.
pose proof (heap_model_ok _ _ _ _ _ _ (proj1 REST)) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ (proj1 REST)) as MI. cbn [hl_segs S4L pf_mxd] in MI.
apply rz_evt; [exact MOK|].
destruct Hr as [-> | ->].
2:{
replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step. if_false. step. step. step. apply evt_RZ_done.
eapply KE; [apply (PE_INV_W HIx); exact INV | apply TDX | exact FS1' | exact FRM1]. }
step. if_true.

unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR.
step. rewrite (sx32_small_mod stpos) by lia. fold sp.
step. norm_w32.

assert (PART : forall mX mdX AX pbsX errvX (x1x a0x a1x a2x a3x a4x a5x a6x a7x t0x t1x t2x t3x t4x t5x t6x s6x s7x s8x : word) FX fcX,
PE_INV HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) payload me lo mX mdX AX
(TST depth levels co pb pbsX (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs []) cb j1 j2 utf sv errvX ->
fsaved F0 FX -> frm0 fcX ->
realizes rsegs (mkCfg (MS (mkR x1x (Z_to_bv 64 spf) gp (Z_to_bv 64 482928) t0x t1x t2x (Z_to_bv 64 tk) (Z_to_bv 64 oldl) a0x a1x a2x a3x a4x a5x a6x a7x
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4 (Z_to_bv 64 (sp + 1)) s6x s7x s8x (Z_to_bv 64 (sb + co)) (Z_to_bv 64 sp) (Z_to_bv 64 79024) t3x t4x t5x t6x)
FX (Z_to_bv 64 0x22630) fcX None mX (seg_rom rsegs)) mdX) T).
{ intros mX mdX AX pbsX errvX x1x a0x a1x a2x a3x a4x a5x a6x a7x t0x t1x t2x t3x t4x t5x t6x s6x s7x s8x FX fcX INVX FSX FRMX.
pose proof INVX as [[_ (_ & _ & _ & TOKX & _ & _ & _ & FRX)] RESTX].
unfold tok_cells, tok_cells_g in TOKX. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_tk pf_spf pf_mxd] in TOKX, FRX. unfold pe_frame in FRX.
pose proof (heap_model_ok _ _ _ _ _ _ (proj1 RESTX)) as MOKX.
pose proof (heap_mem_inv _ _ _ _ _ _ (proj1 RESTX)) as MIX. cbn [hl_segs S4L pf_mxd] in MIX.
pose proof (wmono_refl rsegs mX) as WMX. pose proof (munch_refl [(tk, tk + 72); (spf, spf + 144)] mX) as MUX.
apply rz_evt; [exact MOKX|]. step. step. step. apply evt_RZ_done.
eapply (KB (TST depth levels co pb pbsX (TS isd (Z_to_bv 64 (sp + 1)) (Z_to_bv 64 co) err ucs high quote) obj objs [])); clear KL KR KB KB2 KO7 KE7 KE.
- unfold mbrk, mredo, mbase in *. unfold cur_st, cur_ss in Mn. cbn [t_co t_levels t_depth pf_len pf_mxd] in *. rewrite Hl, Hst in Mn. unfold rank in Mn. cbn -[Nat.mul Nat.add Z.to_nat Z.sub] in Mn. lia.
- eapply (PE_INV_retok HIx _ q _ payload me lo mX _ mdX AX (TST depth levels co pb pbsX (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs []));
[exact STC | exact INVX | exact MUX | exact WMX | exact MIX | exact TOKX | cbn; lia | reflexivity | exact FRX].
- cbn; lia.
- exact Hcb.
- unfold cur_st; cbn [t_levels t_depth pf_mxd]; rewrite Hl, Hst; discriminate.
- unfold SPOK, SPV; cbn [t_x ts_stpos t_co pf_mxd]. intros _. rewrite spv_lit by lia. lia.
- apply TDX.
- exact FSX.
- exact FRMX. }

assert (FINT : forall mX mdX AX pbsX errvX (x1x a0x a1x a2x a3x a4x a5x a6x a7x t0x t1x t2x t3x t4x t5x t6x s6x s7x s8x s10x : word) FX fcX,
PE_INV HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) payload me lo mX mdX AX
(TST depth levels co pb pbsX (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs []) cb j1 j2 utf sv errvX ->
fsaved F0 FX -> frm0 fcX ->
realizes rsegs (mkCfg (MS (mkR x1x (Z_to_bv 64 spf) gp (Z_to_bv 64 482928) t0x t1x t2x (Z_to_bv 64 tk) (Z_to_bv 64 oldl) a0x a1x a2x a3x a4x a5x a6x a7x
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4 (Z_to_bv 64 (sp + 1)) s6x s7x s8x (Z_to_bv 64 (sb + co)) s10x (Z_to_bv 64 79024) t3x t4x t5x t6x)
FX (Z_to_bv 64 0x22140) fcX None mX (seg_rom rsegs)) mdX) T).
{ intros mX mdX AX pbsX errvX x1x a0x a1x a2x a3x a4x a5x a6x a7x t0x t1x t2x t3x t4x t5x t6x s6x s7x s8x s10x FX fcX INVX FSX FRMX.
pose proof INVX as [[_ (_ & _ & _ & TOKX & _ & _ & TSKX & FRX)] RESTX].
unfold tok_cells, tok_cells_g in TOKX. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_tk pf_spf pf_mxd] in TOKX, FRX, TSKX. unfold pe_frame in FRX.
pose proof (heap_model_ok _ _ _ _ _ _ (proj1 RESTX)) as MOKX.
pose proof (heap_mem_inv _ _ _ _ _ _ (proj1 RESTX)) as MIX. cbn [hl_segs S4L pf_mxd] in MIX.
pose proof RESTX as (HPX & _ & _ & STX & ERRX & _). cbn [pf_spf pf_mxd] in STX.
apply rz_evt; [exact MOKX|].
step. step. step.
apply evt_RZ_done.
eapply (json_object_new_boolean_cps HIx) with (LB := pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) (TST depth levels co pb pbsX (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs [])) (lo := lo);
[ exact HPX | .. ]; try alloc_side.
all: try (rewrite ?unsigned_lit by lia; first [exact STX | exact ERRX]).
all: try (rewrite ?unsigned_lit by lia; unfold PE_FRAME in *; clia).
clear TOKX FRX MOKX.
intros ms2 md2 (m2 & A2 & r & errv2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & OUT).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp S4L pf_mxd] in *. rewrite ?(unsigned_lit spf) in ST2 by lia. rewrite ?(unsigned_lit spf) in HPR2 by lia.
assert (FS2' : fsaved F0 F2) by (eapply fsaved_trans; [exact FSX | exact FS2]).
specialize (FRM2 FRMX).
pose proof INVX as [[_ (_ & _ & _ & TOKX & _ & _ & _ & FRX)] _].
unfold tok_cells, tok_cells_g in TOKX. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_tk pf_spf pf_mxd] in TOKX, FRX. unfold pe_frame in FRX.
assert (INtk2 : In (tk, 72) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) (TST depth levels co pb pbsX (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs [])))
by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
assert (INq2 : In (q, (32 * mxd)) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) (TST depth levels co pb pbsX (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs [])))
by (unfold pe_blocks; apply in_or_app; right; right; left; reflexivity).
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FRX; [| left; cbn; lia]. cbn [hl_segs S4L pf_mxd] in FRX.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in TOKX; [| eapply client_range_block; [exact INtk2 | lia | cbn; lia]]. cbn [hl_segs S4L pf_mxd] in TOKX.
apply (tstack_pres_g S4L _ _ _ _ _ _ HPR2 INq2) in TSKX; [| exact LEN32]. cbn [hl_segs S4L pf_mxd] in TSKX.
pose proof (srec_join8 _ _ _ (TSKX depth l Hl)) as Ld. cbn [le4 Z_to_le_bytes app hl_segs S4L pf_mxd] in Ld. rewrite Hc0, Hn0 in Ld.
remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld.

assert (OUT' : exists A2' NB, HEAP S4L HIx A2' (NB ++ pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) (TST depth levels co pb pbsX (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs [])) m2 md2 /\
((r = 0 /\ NB = []) \/ (r <> 0 /\ jval rsegs S4F Sbool m2 NB r 1))).
{ destruct OUT as [(-> & HP2) | (Hr & NB & J2 & HP2)].
- exists A2, []. split; [exact HP2 | left; split; reflexivity].
- exists A2, NB. split; [exact HP2 | right; split; [exact Hr | exact J2]]. }
clear OUT. destruct OUT' as (A2' & NB & HP2 & OUT).
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI2. cbn [hl_segs S4L pf_mxd] in MI2.
pose proof (wmono_refl rsegs m2) as WM2. pose proof (munch_refl [(bse, bse + 32)] m2) as MU2.
stash TSKX. stash ST2. stash ERR2. stash HP2.
reenter MOK2.
step. norm_sx32. step.
step. rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
step. replace (q + Z.of_nat depth * 32) with bse by lia.
step. step.
unstash TSKX. unstash ST2. unstash ERR2. unstash HP2.
destruct OUT as [[-> ->] | [Hr J2]].
-
step. if_true. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
match goal with L8 : rw_cells rsegs mc bse (?c1 :: ?rest) |- _ =>
pose proof (rw_cells_recast_prefix rsegs mc bse [c1] [C4 (Z_to_bv 64 (tl_st l)); C4 (Z_to_bv 64 (tl_ss l))]
rest L8 ltac:(cbn; repeat split) eq_refl eq_refl) as L5; cbn [app pf_mxd] in L5
end end.
apply evt_RZ_done. eapply KE; [ | apply TDX | exact FS2' | exact FRM2]. clear KL KR KB KB2 KO7 KE7 KE.
apply (PE_INV_W HIx).
lazymatch goal with |- PE_INV _ _ _ _ _ _ _ ?mc _ _ _ _ _ _ _ _ _ =>
eapply (keep_inv HIx _ q _ payload me lo mX m2 mc mdX md2 AX A2' _ l cb j1 j2 utf sv errvX errv2 bse);
[ exact STC | exact INVX | exact Hl | exact Hcbs0 | exact Hnbs0 | exact HPR2 | exact VM2 | cbn [app pf_mxd] in HP2; exact HP2 | exact ST2 | exact ERR2
| exact Hbse | exact MU2 | exact WM2 | assumption | unfold srec_cells; rewrite Hc0, Hn0; exact L5 | eassumption | eassumption ]
end.
-
assert (HrR : 0 < r < 2^64).
{ destruct J2 as (pbp & PBS & RB & ENB & OPB & bb & junkb & ERB & CELLS).
pose proof (heap_blk S4L HIx _ _ _ _ r 48 HP2 ltac:(apply in_or_app; left; rewrite ENB, ERB; left; reflexivity)) as (_ & _ & HB1 & HB2 & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in HB2. lia. }
step. if_falsex.
step. stepz. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
match goal with L8 : rw_cells rsegs mc bse _ |- _ =>
pose proof (rw_cells_recast_prefix rsegs mc bse [C8 (Z_to_bv 64 8589934592)] [C4 (Z_to_bv 64 ST_eatws); C4 (Z_to_bv 64 ST_finish)]
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 r); C8 (Z_to_bv 64 0)] L8 ltac:(cbn; repeat split)
ltac:(apply bytes_eq_by_unsigned; vm_compute; reflexivity) eq_refl) as L5; cbn [app pf_mxd] in L5
end end.
apply evt_RZ_done.
eapply (KR (TST depth (lupd levels depth (TL ST_eatws ST_finish r (Some Sbool) NB 0 [])) co pb pbsX (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs []));
clear KL KR KB KB2 KO7 KE7 KE.
+ unfold mredo, mbase, cur_st, cur_ss in Mn |- *. cbn [t_co t_levels t_depth pf_len pf_mxd] in Mn |- *. rewrite nth_error_lupd_eq by lia. rewrite Hl, Hst in Mn.
cbn [tl_st tl_ss pf_mxd]. unfold rank in Mn |- *. cbn -[Nat.mul Nat.add Z.to_nat Z.sub] in Mn |- *. lia.
+ lazymatch goal with |- PE_INV _ _ _ _ _ _ _ ?mc _ _ _ _ _ _ _ _ _ =>
eapply (setcur_inv HIx _ q _ payload me lo mX m2 mc mdX md2 AX A2' (TST depth levels co pb pbsX (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs []) l
cb j1 j2 utf sv errvX errv2 NB r (Some Sbool) bse);
[ exact STC | exact INVX | exact Hl | exact Hc0 | exact Hcbs0 | exact Hn0 | exact Hnbs0 | reflexivity
| exact HPR2 | exact VM2 | cbn [app pf_mxd] in HP2; exact HP2 | exact ST2 | exact ERR2
| cbn [jres pf_mxd]; split; [exact Hr | exact J2] | exact Hbse | exact MU2 | exact WM2 | assumption | exact L5 | eassumption | eassumption ]
end.
+ cbn; lia.
+ exact Hcb.
+ unfold NUMC, cur_st; cbn [t_levels t_depth pf_mxd]; rewrite nth_error_lupd_eq by lia; cbn; intros E; discriminate E.
+ unfold SPOK, cur_st; cbn [t_levels t_depth pf_mxd]; rewrite nth_error_lupd_eq by lia; cbn; intros E; discriminate E.
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs [])); [apply TDX | exact Hl | rewrite Ecs; cbn; lia | cbn; lia | reflexivity].
+ exact FS2'.
+ exact FRM2. }

assert (FINF : forall mX mdX AX pbsX errvX (x1x a0x a1x a2x a3x a4x a5x a6x a7x t0x t1x t2x t3x t4x t5x t6x s6x s7x s8x s10x : word) FX fcX,
PE_INV HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) payload me lo mX mdX AX
(TST depth levels co pb pbsX (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs []) cb j1 j2 utf sv errvX ->
fsaved F0 FX -> frm0 fcX ->
realizes rsegs (mkCfg (MS (mkR x1x (Z_to_bv 64 spf) gp (Z_to_bv 64 482928) t0x t1x t2x (Z_to_bv 64 tk) (Z_to_bv 64 oldl) a0x a1x a2x a3x a4x a5x a6x a7x
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4 (Z_to_bv 64 (sp + 1)) s6x s7x s8x (Z_to_bv 64 (sb + co)) s10x (Z_to_bv 64 79024) t3x t4x t5x t6x)
FX (Z_to_bv 64 0x220c4) fcX None mX (seg_rom rsegs)) mdX) T).
{ intros mX mdX AX pbsX errvX x1x a0x a1x a2x a3x a4x a5x a6x a7x t0x t1x t2x t3x t4x t5x t6x s6x s7x s8x s10x FX fcX INVX FSX FRMX.
pose proof INVX as [[_ (_ & _ & _ & TOKX & _ & _ & TSKX & FRX)] RESTX].
unfold tok_cells, tok_cells_g in TOKX. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_tk pf_spf pf_mxd] in TOKX, FRX, TSKX. unfold pe_frame in FRX.
pose proof (heap_model_ok _ _ _ _ _ _ (proj1 RESTX)) as MOKX.
pose proof (heap_mem_inv _ _ _ _ _ _ (proj1 RESTX)) as MIX. cbn [hl_segs S4L pf_mxd] in MIX.
pose proof RESTX as (HPX & _ & _ & STX & ERRX & _). cbn [pf_spf pf_mxd] in STX.
apply rz_evt; [exact MOKX|].
step. step.
apply evt_RZ_done.
eapply (json_object_new_boolean_cps HIx) with (LB := pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) (TST depth levels co pb pbsX (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs [])) (lo := lo);
[ exact HPX | .. ]; try alloc_side.
all: try (rewrite ?unsigned_lit by lia; first [exact STX | exact ERRX]).
all: try (rewrite ?unsigned_lit by lia; unfold PE_FRAME in *; clia).
clear TOKX FRX MOKX.
intros ms2 md2 (m2 & A2 & r & errv2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & OUT).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp S4L pf_mxd] in *. rewrite ?(unsigned_lit spf) in ST2 by lia. rewrite ?(unsigned_lit spf) in HPR2 by lia.
assert (FS2' : fsaved F0 F2) by (eapply fsaved_trans; [exact FSX | exact FS2]).
specialize (FRM2 FRMX).
pose proof INVX as [[_ (_ & _ & _ & TOKX & _ & _ & _ & FRX)] _].
unfold tok_cells, tok_cells_g in TOKX. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_tk pf_spf pf_mxd] in TOKX, FRX. unfold pe_frame in FRX.
assert (INtk2 : In (tk, 72) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) (TST depth levels co pb pbsX (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs [])))
by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
assert (INq2 : In (q, (32 * mxd)) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) (TST depth levels co pb pbsX (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs [])))
by (unfold pe_blocks; apply in_or_app; right; right; left; reflexivity).
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FRX; [| left; cbn; lia]. cbn [hl_segs S4L pf_mxd] in FRX.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in TOKX; [| eapply client_range_block; [exact INtk2 | lia | cbn; lia]]. cbn [hl_segs S4L pf_mxd] in TOKX.
apply (tstack_pres_g S4L _ _ _ _ _ _ HPR2 INq2) in TSKX; [| exact LEN32]. cbn [hl_segs S4L pf_mxd] in TSKX.
pose proof (srec_join8 _ _ _ (TSKX depth l Hl)) as Ld. cbn [le4 Z_to_le_bytes app hl_segs S4L pf_mxd] in Ld. rewrite Hc0, Hn0 in Ld.
remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld.

assert (OUT' : exists A2' NB, HEAP S4L HIx A2' (NB ++ pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) (TST depth levels co pb pbsX (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs [])) m2 md2 /\
((r = 0 /\ NB = []) \/ (r <> 0 /\ jval rsegs S4F Sbool m2 NB r 1))).
{ destruct OUT as [(-> & HP2) | (Hr & NB & J2 & HP2)].
- exists A2, []. split; [exact HP2 | left; split; reflexivity].
- exists A2, NB. split; [exact HP2 | right; split; [exact Hr | exact J2]]. }
clear OUT. destruct OUT' as (A2' & NB & HP2 & OUT).
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI2. cbn [hl_segs S4L pf_mxd] in MI2.
pose proof (wmono_refl rsegs m2) as WM2. pose proof (munch_refl [(bse, bse + 32)] m2) as MU2.
stash TSKX. stash ST2. stash ERR2. stash HP2.
reenter MOK2.
step.
step. norm_sx32. step.
step. rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
step. replace (q + Z.of_nat depth * 32) with bse by lia.
step. step.
unstash TSKX. unstash ST2. unstash ERR2. unstash HP2.
destruct OUT as [[-> ->] | [Hr J2]].
-
step. if_false. step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
match goal with L8 : rw_cells rsegs mc bse (?c1 :: ?rest) |- _ =>
pose proof (rw_cells_recast_prefix rsegs mc bse [c1] [C4 (Z_to_bv 64 (tl_st l)); C4 (Z_to_bv 64 (tl_ss l))]
rest L8 ltac:(cbn; repeat split) eq_refl eq_refl) as L5; cbn [app pf_mxd] in L5
end end.
apply evt_RZ_done. eapply KE; [ | apply TDX | exact FS2' | exact FRM2]. clear KL KR KB KB2 KO7 KE7 KE.
apply (PE_INV_W HIx).
lazymatch goal with |- PE_INV _ _ _ _ _ _ _ ?mc _ _ _ _ _ _ _ _ _ =>
eapply (keep_inv HIx _ q _ payload me lo mX m2 mc mdX md2 AX A2' _ l cb j1 j2 utf sv errvX errv2 bse);
[ exact STC | exact INVX | exact Hl | exact Hcbs0 | exact Hnbs0 | exact HPR2 | exact VM2 | cbn [app pf_mxd] in HP2; exact HP2 | exact ST2 | exact ERR2
| exact Hbse | exact MU2 | exact WM2 | assumption | unfold srec_cells; rewrite Hc0, Hn0; exact L5 | eassumption | eassumption ]
end.
-
assert (HrR : 0 < r < 2^64).
{ destruct J2 as (pbp & PBS & RB & ENB & OPB & bb & junkb & ERB & CELLS).
pose proof (heap_blk S4L HIx _ _ _ _ r 48 HP2 ltac:(apply in_or_app; left; rewrite ENB, ERB; left; reflexivity)) as (_ & _ & HB1 & HB2 & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in HB2. lia. }
step. if_truex.
step. step. stepz. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
match goal with L8 : rw_cells rsegs mc bse _ |- _ =>
pose proof (rw_cells_recast_prefix rsegs mc bse [C8 (Z_to_bv 64 8589934592)] [C4 (Z_to_bv 64 ST_eatws); C4 (Z_to_bv 64 ST_finish)]
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 r); C8 (Z_to_bv 64 0)] L8 ltac:(cbn; repeat split)
ltac:(apply bytes_eq_by_unsigned; vm_compute; reflexivity) eq_refl) as L5; cbn [app pf_mxd] in L5
end end.
apply evt_RZ_done.
eapply (KR (TST depth (lupd levels depth (TL ST_eatws ST_finish r (Some Sbool) NB 0 [])) co pb pbsX (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs []));
clear KL KR KB KB2 KO7 KE7 KE.
+ unfold mredo, mbase, cur_st, cur_ss in Mn |- *. cbn [t_co t_levels t_depth pf_len pf_mxd] in Mn |- *. rewrite nth_error_lupd_eq by lia. rewrite Hl, Hst in Mn.
cbn [tl_st tl_ss pf_mxd]. unfold rank in Mn |- *. cbn -[Nat.mul Nat.add Z.to_nat Z.sub] in Mn |- *. lia.
+ lazymatch goal with |- PE_INV _ _ _ _ _ _ _ ?mc _ _ _ _ _ _ _ _ _ =>
eapply (setcur_inv HIx _ q _ payload me lo mX m2 mc mdX md2 AX A2' (TST depth levels co pb pbsX (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs []) l
cb j1 j2 utf sv errvX errv2 NB r (Some Sbool) bse);
[ exact STC | exact INVX | exact Hl | exact Hc0 | exact Hcbs0 | exact Hn0 | exact Hnbs0 | reflexivity
| exact HPR2 | exact VM2 | cbn [app pf_mxd] in HP2; exact HP2 | exact ST2 | exact ERR2
| cbn [jres pf_mxd]; split; [exact Hr | exact J2] | exact Hbse | exact MU2 | exact WM2 | assumption | exact L5 | eassumption | eassumption ]
end.
+ cbn; lia.
+ exact Hcb.
+ unfold NUMC, cur_st; cbn [t_levels t_depth pf_mxd]; rewrite nth_error_lupd_eq by lia; cbn; intros E; discriminate E.
+ unfold SPOK, cur_st; cbn [t_levels t_depth pf_mxd]; rewrite nth_error_lupd_eq by lia; cbn; intros E; discriminate E.
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs [])); [apply TDX | exact Hl | rewrite Ecs; cbn; lia | cbn; lia | reflexivity].
+ exact FS2'.
+ exact FRM2. }

assert (JOIN : evt rsegs (RZ rsegs md1 T) (MS (mkR (Z_to_bv 64 0x21bac) (Z_to_bv 64 spf) gp (Z_to_bv 64 482928) t0' t1' t2' (Z_to_bv 64 tk) (Z_to_bv 64 oldl) (Z_to_bv 64 4) (Z_to_bv 64 3) a2' a3' a4' a5' a6' a7' (Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4 (Z_to_bv 64 (sp + 1)) (Z_to_bv 64 (Z.min (sp + 1) 5)) (Z_to_bv 64 26) (Z_to_bv 64 (Z.min (sp + 1) 4)) (Z_to_bv 64 (sb + co)) (Z_to_bv 64 sp) (Z_to_bv 64 PE_JTAB) t3' t4' t5' t6') F1 (Z_to_bv 64 0x21bdc) fc1 None m (seg_rom rsegs))).
2:{ step. step. step.
destruct (Z.lt_ge_cases sp 3) as [Hs3|Hs3].
- step. if_truex. step. step. if_truex.
replace (Z.min (sp + 1) 4) with (sp + 1) in JOIN by lia. replace (Z.min (sp + 1) 5) with (sp + 1) in JOIN by lia. exact JOIN.
- step. if_falsex. step. step.
destruct (Z.lt_ge_cases sp 4) as [Hs4|Hs4].
+ step. if_truex. replace (Z.min (sp + 1) 4) with 4 in JOIN by lia. replace (Z.min (sp + 1) 5) with (sp + 1) in JOIN by lia. exact JOIN.
+ step. if_falsex. step. replace (Z.min (sp + 1) 4) with 4 in JOIN by lia. replace (Z.min (sp + 1) 5) with 5 in JOIN by lia. exact JOIN. }
set (n4 := Z.min (sp + 1) 4). set (n5 := Z.min (sp + 1) 5).

pose proof (pbuf_cstr m pbs1 pb PB) as (buf & bpos & cap & str & rest & Epbs & Hbpos & Hcap & PBH & BUFS & NIN & Lstr & Lcap).
pose proof REST as (HP & _ & _ & ST & _).
assert (INbuf : In (buf, cap) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) (TST depth levels co pb pbs1 (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs [])))
by (unfold pe_blocks, tstate_blocks; cbn [t_pbs t_objbs t_levels pf_mxd]; rewrite Epbs; apply in_or_app; left; apply in_or_app; left; right; left; reflexivity).
assert (INpb : In (pb, 16) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) (TST depth levels co pb pbs1 (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs [])))
by (unfold pe_blocks, tstate_blocks; cbn [t_pbs t_objbs t_levels pf_mxd]; rewrite Epbs; apply in_or_app; left; apply in_or_app; left; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ buf cap HP INbuf) as (_ & _ & Hbuflo & Hbufhi & _).
pose proof (heap_blk S4L HIx _ _ _ _ pb 16 HP INpb) as (_ & _ & Hpblo & Hpbhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hbufhi, Hpbhi.
replace (str ++ b0 :: rest) with ((str ++ [b0]) ++ rest) in BUFS by (rewrite <- app_assoc; reflexivity).
apply bytes_at_app in BUFS. destruct BUFS as [BUFZ _].
clear INbuf INpb HP.

assert (BLK4 : forall mX AX pbsX errvX (x1x a0x a1x a2x a3x a4x a5x a6x a7x t0x t1x t2x t3x t4x t5x t6x s6x s7x s8x : word),
PE_INV HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) payload me lo mX md1 AX
(TST depth levels co pb pbsX (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs []) cb j1 j2 utf sv errvX ->
evt rsegs (RZ rsegs md1 T) (MS (mkR x1x (Z_to_bv 64 spf) gp (Z_to_bv 64 482928) t0x t1x t2x (Z_to_bv 64 tk) (Z_to_bv 64 oldl) a0x a1x a2x a3x a4x a5x a6x a7x
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4 (Z_to_bv 64 (sp + 1)) s6x s7x s8x (Z_to_bv 64 (sb + co)) (Z_to_bv 64 sp) (Z_to_bv 64 PE_JTAB) t3x t4x t5x t6x)
F1 (Z_to_bv 64 0x22138) fc1 None mX (seg_rom rsegs))).
{ intros mX AX pbsX errvX x1x a0x a1x a2x a3x a4x a5x a6x a7x t0x t1x t2x t3x t4x t5x t6x s6x s7x s8x INVX.
step. destruct (Z.eq_dec sp 4) as [E4|N4].
- step. if_falsex. apply evt_RZ_done. eapply FINT; [exact INVX | exact FS1' | exact FRM1].
- step. if_truex. apply evt_RZ_done. eapply PART; [exact INVX | exact FS1' | exact FRM1]. }
assert (BLK5 : forall mX AX pbsX errvX (x1x a0x a1x a2x a3x a4x a5x a6x a7x t0x t1x t2x t3x t4x t5x t6x s6x s7x s8x : word),
PE_INV HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) payload me lo mX md1 AX
(TST depth levels co pb pbsX (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs []) cb j1 j2 utf sv errvX ->
evt rsegs (RZ rsegs md1 T) (MS (mkR x1x (Z_to_bv 64 spf) gp (Z_to_bv 64 482928) t0x t1x t2x (Z_to_bv 64 tk) (Z_to_bv 64 oldl) a0x a1x a2x a3x a4x a5x a6x a7x
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4 (Z_to_bv 64 (sp + 1)) s6x s7x s8x (Z_to_bv 64 (sb + co)) (Z_to_bv 64 sp) (Z_to_bv 64 PE_JTAB) t3x t4x t5x t6x)
F1 (Z_to_bv 64 0x220bc) fc1 None mX (seg_rom rsegs))).
{ intros mX AX pbsX errvX x1x a0x a1x a2x a3x a4x a5x a6x a7x t0x t1x t2x t3x t4x t5x t6x s6x s7x s8x INVX.
step. destruct (Z.eq_dec sp 5) as [E3|N3].
- step. if_falsex. apply evt_RZ_done. eapply FINF; [exact INVX | exact FS1' | exact FRM1].
- step. if_truex. apply evt_RZ_done. eapply PART; [exact INVX | exact FS1' | exact FRM1]. }

assert (FALSECMP : forall mX AX errvX (x1x a0x a1x a2x a3x a4x a5x a6x a7x t0x t1x t2x t3x t4x t5x t6x s8x : word),
PE_INV HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) payload me lo mX md1 AX
(TST depth levels co pb pbs1 (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs []) cb j1 j2 utf sv errvX ->
stk rsegs mX lo spf -> bytes_at rsegs mX buf (str ++ [b0]) -> mem_inv rsegs mX ->
evt rsegs (RZ rsegs md1 T) (MS (mkR x1x (Z_to_bv 64 spf) gp (Z_to_bv 64 482928) t0x t1x t2x (Z_to_bv 64 tk) (Z_to_bv 64 oldl) a0x a1x a2x a3x a4x a5x a6x a7x
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4 (Z_to_bv 64 (sp + 1)) (Z_to_bv 64 n5) (Z_to_bv 64 buf) s8x (Z_to_bv 64 (sb + co)) (Z_to_bv 64 sp) (Z_to_bv 64 PE_JTAB) t3x t4x t5x t6x)
F1 (Z_to_bv 64 0x220a0) fc1 None mX (seg_rom rsegs))).
{ intros mX AX errvX x1x a0x a1x a2x a3x a4x a5x a6x a7x t0x t1x t2x t3x t4x t5x t6x s8x INVe STe BUFZe MIe.
step. step. step. step. step.
pose proof (false_bytes mX MIe) as NANS. destruct (strncmp_model_cstr falsestr str n5) as [v4 Hv4].
eapply evt_cut; [eapply strncmp_spec; [rewrite unsigned_lit by lia; exact NANS | rewrite unsigned_lit by lia; exact BUFZe | rewrite unsigned_lit by lia; exact Hv4 | exact MIe] |].
intros ms' POST; destruct POST as (t0f & t1f & t2f & a1f & a2f & a3f & a4f & a5f & a6f & a7f & t3f & t4f & t5f & t6f & m4' & -> & MUf & WMf & MIf & _ & _).
replace (ret_pc (Z_to_bv 64 0x220b4)) with (Z_to_bv 64 0x220b4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (stk_transport_disjoint rsegs [] _ _ _ _ STe MUf WMf I) as STf.
pose proof (PE_INV_stackw HIx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ STC INVe MUf WMf MIf ltac:(apply Forall_nil) STf) as INVf.
pose proof (strncmp_model_range _ _ _ _ Hv4) as Rv4.
clear INVe STe BUFZe NANS MIe MUf WMf Hv4.
destruct (Z.eq_dec v4 0) as [Ev4 | Nv4].
{ rewrite Ev4. step. if_true. eapply BLK5; exact INVf. }
step. if_false_by (eqb64_0_false v4 Rv4 Nv4).

step. step. step.
apply evt_RZ_done.
eapply (KE7 _ [] co (Z_to_bv 64 6)); [apply (PE_INV_W HIx); exact INVf | apply TDX | exact FS1' | exact FRM1]. }

step.
pose proof (tok_flags_byte_g mxd fl m tk pb (Z.of_nat depth) q (TS isd stpos (Z_to_bv 64 co) err ucs high quote) TOK) as RDF.
step. rewrite (zxb_byte fl) by lia.
step. step. rewrite (unsigned_lit (fl mod 256)) by (pose proof (Z.mod_pos_bound fl 256 ltac:(lia)); lia). rewrite (land_mod256 fl 1) by lia.
clear TOK FR PBH RDF PB TSK CORE REST MOK.
destruct (land1_cases fl) as [FL1|FL1]; rewrite FL1.
-
step. if_false.
step. step. step. step. step.

pose proof (true_bytes m MI) as NULLS.
eapply evt_cut; [eapply strncasecmp_spec; [rewrite unsigned_lit by lia; exact NULLS | rewrite unsigned_lit by lia; exact BUFZ | exact nonul_true | exact NIN | rewrite unsigned_lit by lia; exact ST | rewrite unsigned_lit by lia; lia | rewrite !unsigned_lit by lia; left; cbn; lia | rewrite !unsigned_lit by lia; left; lia | exact MI] |].
intros ms' POST; destruct POST as (t0c & t1c & t2c & a0c & a1c & a2c & a3c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & m' & -> & MUc & WMc & MIc & Ea0 & STc & _ & BUFZc).
rewrite ?unsigned_lit in MUc by lia. rewrite ?unsigned_lit in STc by lia. rewrite ?unsigned_lit in BUFZc by lia. rewrite ?unsigned_lit in Ea0 by lia.
replace (ret_pc (Z_to_bv 64 0x21c04)) with (Z_to_bv 64 0x21c04) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (PE_INV_stackw HIx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ STC INV MUc WMc MIc ltac:(apply Forall_cons; [cbn [fst snd pf_spf pf_mxd]; lia | apply Forall_nil]) STc) as INVc.
subst a0c. pose proof (strncasecmp_model_range truestr str n4) as Rv1. set (v1 := strncasecmp_model truestr str n4) in *.
clear INV ST BUFZ NULLS MI.
destruct (Z.eq_dec v1 0) as [Ev1 | Nv1].
{ rewrite Ev1. step. if_true. eapply BLK4; exact INVc. }
step. if_false_by (eqb64_0_false v1 Rv1 Nv1).
step. step. step. step. step.

pose proof (true_bytes m' MIc) as NULLS. destruct (strncmp_model_cstr truestr str n4) as [v2 Hv2].
eapply evt_cut; [eapply strncmp_spec; [rewrite unsigned_lit by lia; exact NULLS | rewrite unsigned_lit by lia; exact BUFZc | rewrite unsigned_lit by lia; exact Hv2 | exact MIc] |].
intros ms' POST; destruct POST as (t0d & t1d & t2d & a1d & a2d & a3d & a4d & a5d & a6d & a7d & t3d & t4d & t5d & t6d & m2' & -> & MUd & WMd & MId & _ & BUFZd).
rewrite ?unsigned_lit in BUFZd by lia.
replace (ret_pc (Z_to_bv 64 0x21c1c)) with (Z_to_bv 64 0x21c1c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (stk_transport_disjoint rsegs [] _ _ _ _ STc MUd WMd I) as STd.
pose proof (PE_INV_stackw HIx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ STC INVc MUd WMd MId ltac:(apply Forall_nil) STd) as INVd.
pose proof (strncmp_model_range _ _ _ _ Hv2) as Rv2.
clear INVc STc BUFZc NULLS MIc MUd WMd MUc WMc Hv2.
destruct (Z.eq_dec v2 0) as [Ev2 | Nv2].
{ rewrite Ev2. step. if_true. eapply BLK4; exact INVd. }
step. if_false_by (eqb64_0_false v2 Rv2 Nv2).
step. step. step. step. step.

pose proof (false_bytes m2' MId) as NANS.
eapply evt_cut; [eapply strncasecmp_spec; [rewrite unsigned_lit by lia; exact NANS | rewrite unsigned_lit by lia; exact BUFZd | exact nonul_false | exact NIN | rewrite unsigned_lit by lia; exact STd | rewrite unsigned_lit by lia; lia | rewrite !unsigned_lit by lia; left; cbn; lia | rewrite !unsigned_lit by lia; left; lia | exact MId] |].
intros ms' POST; destruct POST as (t0e & t1e & t2e & a0e & a1e & a2e & a3e & a4e & a5e & a6e & a7e & t3e & t4e & t5e & t6e & m3' & -> & MUe & WMe & MIe & Ea0 & STe & _ & BUFZe).
rewrite ?unsigned_lit in MUe by lia. rewrite ?unsigned_lit in STe by lia. rewrite ?unsigned_lit in BUFZe by lia. rewrite ?unsigned_lit in Ea0 by lia.
replace (ret_pc (Z_to_bv 64 0x21c34)) with (Z_to_bv 64 0x21c34) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (PE_INV_stackw HIx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ STC INVd MUe WMe MIe ltac:(apply Forall_cons; [cbn [fst snd pf_spf pf_mxd]; lia | apply Forall_nil]) STe) as INVe.
subst a0e. pose proof (strncasecmp_model_range falsestr str n5) as Rv3. set (v3 := strncasecmp_model falsestr str n5) in *.
clear INVd STd BUFZd NANS MId.
destruct (Z.eq_dec v3 0) as [Ev3 | Nv3].
{ rewrite Ev3. step. if_false. step. eapply BLK5; exact INVe. }
step. if_true_by (f_equal negb (eqb64_0_false v3 Rv3 Nv3)).
eapply FALSECMP; [exact INVe | exact STe | exact BUFZe | exact MIe].
-
step. if_true.
step. step. step. step. step.

pose proof (true_bytes m MI) as NULLS. destruct (strncmp_model_cstr truestr str n4) as [v2 Hv2].
eapply evt_cut; [eapply strncmp_spec; [rewrite unsigned_lit by lia; exact NULLS | rewrite unsigned_lit by lia; exact BUFZ | rewrite unsigned_lit by lia; exact Hv2 | exact MI] |].
intros ms' POST; destruct POST as (t0d & t1d & t2d & a1d & a2d & a3d & a4d & a5d & a6d & a7d & t3d & t4d & t5d & t6d & m2' & -> & MUd & WMd & MId & _ & BUFZd).
rewrite ?unsigned_lit in BUFZd by lia.
replace (ret_pc (Z_to_bv 64 0x2209c)) with (Z_to_bv 64 0x2209c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (stk_transport_disjoint rsegs [] _ _ _ _ ST MUd WMd I) as STd.
pose proof (PE_INV_stackw HIx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ STC INV MUd WMd MId ltac:(apply Forall_nil) STd) as INVd.
pose proof (strncmp_model_range _ _ _ _ Hv2) as Rv2.
clear INV ST BUFZ NULLS MI MUd WMd Hv2.
destruct (Z.eq_dec v2 0) as [Ev2 | Nv2].
{ rewrite Ev2. step. if_true. eapply BLK4; exact INVd. }
step. if_false_by (eqb64_0_false v2 Rv2 Nv2).
eapply FALSECMP; [exact INVd | exact STd | exact BUFZd | exact MId].
Qed.
End PeBool.

End RC__1.
