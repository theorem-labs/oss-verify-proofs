(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qtgi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qtgi. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.Mq2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UtMn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UtMn.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QkMG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkMG.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UG8z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UG8z. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Udyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Udyh.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U2Sr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U2Sr. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require ULbz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import ULbz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UIsM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UIsM.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UXfU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UXfU.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Udyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Udyh.Mq7.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UBpZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UBpZ. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UT7i.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UT7i. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv6q.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv6q.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QgoP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgoP.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UzWc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UzWc.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U4Eu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U4Eu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uc8V.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uc8V.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UfOM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UfOM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uy2A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uy2A. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UdFq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UdFq. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UvXs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UvXs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UX85.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UX85. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UX85.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UX85.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UYrb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UYrb.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UubI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UubI. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UYrb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UYrb. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UbRq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UbRq. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UmOT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UmOT. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UX85.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UX85.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require TopUbTac.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Tk1 Require Tk1Tac.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Tk3 Require Tk3Tac.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Import TopUbTac Tk1Tac Tk3Tac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma firstn_snoc_nth {A} (l : list A) i j x :
nth_error l (i + j) = Some x -> firstn (S j) (skipn i l) = firstn j (skipn i l) ++ [x].
Proof.
intros H. rewrite <- nth_error_skipn in H. revert H. generalize (skipn i l) as s. intros s H.
pose proof (@nth_error_split _ s j x H) as (l1 & l2 & E & L1). rewrite E, <- L1.
replace (S (length l1)) with (length l1 + 1)%nat by lia.
rewrite !firstn_app, firstn_all, Nat.sub_diag by lia. replace (length l1 + 1 - length l1)%nat with 1%nat by lia.
cbn. rewrite firstn_all2, app_nil_r by lia. reflexivity.
Qed.

#[using="Type"] Lemma numb_accept : forall c : byte,
(48 <= bv_unsigned c <= 57 \/ bv_unsigned c = 69 \/ bv_unsigned c = 101 \/ bv_unsigned c = 45 \/ bv_unsigned c = 43 \/ bv_unsigned c = 46) ->
numb c = true.
Proof.
intros c H. unfold numb, numch. rewrite !Bool.orb_true_iff, !Bool.andb_true_iff, !Z.eqb_eq, !Z.leb_le. lia.
Qed.
End RC__1.

Ltac red_ts := repeat match goal with x := TST _ _ _ _ _ _ _ _ _ |- _ => subst x end; unfold mbase; cbn [t_co pf_len t_levels t_depth t_pb t_pbs t_x t_obj pf_mxd].
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

Section PeNumVflush.
Variable HIx : heap_iface S4L.
Variables (pf : pe_fix) (q : Z) (LBc : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(sv : pe_saved) (T : TSet) (F0 : bvmap 5 word).
Hypothesis MEMMOVE : memmove_stmt.
Let LB0 : list blk := LB0 pf LBc.

#[using="MEMMOVE"] Lemma num_vflush :
forall (ts : tstate) (l : tlevel) (co0 : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx)
(cb : byte) (j1 j2 utf : list byte) (errv : word)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l ->
0 <= co0 < t_co ts -> t_co ts <= pf_len pf ->
pbufc rsegs m (t_pbs ts) (t_pb ts) [] ->
tdepth_ok ts ->
fsaved F0 F -> frm0 fc ->
KOUT7 HIx pf q LBc payload me lo sv T F0 -> KERR7 HIx pf q LBc payload me lo sv T F0 ->
realizes rsegs (mkCfg (pe_ms7 rsegs pf 0x23dc4 co0 x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 q) (Z_to_bv 64 (t_pb ts)) (Z_to_bv 64 (t_co ts - co0)) s8 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hco0 Hcol PBC TDOK FS FRM KOUT KERR.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
pose proof INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & JCG).
destruct ts as [depth levels co pb pbs xx obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct xx as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR. unfold pe_ms7, pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold_consts.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
set (LBall := pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) in *.
assert (INtk : In (tk, 72) LBall) by (unfold LBall, pe_blocks; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, (32 * mxd)) LBall) by (unfold LBall, pe_blocks; apply in_or_app; right; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk S4L HIx _ _ _ _ q (32 * mxd) HP INq) as (_ & Hqal & Hqlo & Hqhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hqhi.
assert (Htq : tk <> q).
{ pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND. unfold LBall, pe_blocks in ND. rewrite map_app in ND. apply NoDup_app_remove_l in ND.
cbn [map blk_addr fst pf_mxd] in ND. apply List.NoDup_cons_iff in ND as [Hni _]. intros E. apply Hni. left. symmetry. exact E. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tk 72 q (32 * mxd) HP INtk INq Htq) as Hdtq.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
pose proof (wmono_refl rsegs m) as WM.
pose proof (munch_refl [(tk, tk + 72)] m) as MU.
assert (HW : Forall (pe_wtf (PEF tk oldl newl len lenr sb spf pmd mxd fl)) [(tk, tk + 72)]) by (apply Forall_cons; [left; cbn; lia | apply Forall_nil]).
apply rz_evt; [exact MOK|].
stash PB. stash TSK. stash REST. stash FR.
step. stepz. step. try norm_w32. step. step. step.
unstash PB. unstash TSK. unstash REST. unstash FR.
set (ts1 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) (Z_to_bv 64 14) ucs high quote) obj objs objbs).
rename MU into MU1. rename WM into WM1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
assert (INV1 : PE_INV HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m1 md A ts1 cb j1 j2 utf sv errv)
end.
{ split.
- unfold PE_CORE; cbn. split; [exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [assumption|]. split; [| split; [exact Hpb | split]].
+ eapply (pbuf_wtf HIx) with (ts := ts0); [exact STC | exact HP | exact PB | exact MU1 | exact WM1 | exact HW].
+ eapply (tstack_wtf HIx) with (ts := ts0); [exact STC | exact HP | exact TSK | exact LEN32 | exact MU1 | exact WM1 | exact HW].
+ eapply (rw_cells_transport rsegs _ m); [exact FR | exact MU1 | exact WM1 | cbn; unfold PE_FRAME in *; lia].
- cbn. eapply (PE_REST_private_write HIx) with (ts := ts0) in REST; [exact REST | exact STC | exact MU1 | exact WM1 | assumption | apply pe_wtf_private; exact HW]. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) => assert (PBC1 : pbufc rsegs m1 pbs pb []) end.
{ eapply (pbufc_wtf HIx) with (ts := ts0); [exact STC | exact HP | exact PBC | exact MU1 | exact WM1 | exact HW]. }
clear MU1 WM1 PB TSK FR.

destruct SBin as [L0 | SBin]; [exfalso; lia|].
pose proof INV1 as [_ REST1]. pose proof REST1 as (HP1 & _ & _ & ST1 & ERR1 & _).
pose proof PBC1 as (buf & bpos & cap & post & Epbs & Lpre & PCORE). cbn [length Z.of_nat pf_mxd] in Lpre. subst bpos. pose proof PCORE as (Hbpos & Hcap & _).
pose proof HP1 as HP1'. unfold pe_blocks, tstate_blocks, ts1 in HP1'. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd] in HP1'.
rewrite Epbs in HP1'. cbn [app pf_mxd] in HP1'.
assert (INbuf : In (buf, cap) ((pb, 16) :: (buf, cap) :: (objbs ++ concat (map lvl_blocks levels)) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0)) by (right; left; reflexivity).
pose proof (payload_sep HIx _ _ _ _ _ _ _ _ buf cap STC HP1 SBin ltac:(apply in_or_app; left; unfold ts1, tstate_blocks; cbn [t_pbs t_objbs t_levels pf_mxd]; rewrite Epbs; apply in_or_app; left; right; left; reflexivity)) as Hdsb.
cbn [pf_sb pf_len pf_mxd] in Hdsb.
pose proof REST1 as (_ & _ & _ & _ & _ & STR1 & _).
pose proof (bytes_at_bound _ _ _ _ STR1) as SBB.
pose proof (bytes_at_sub S4L _ sb payload (Z.to_nat co0) (Z.to_nat (co - co0)) STR1 ltac:(lia)) as SRC. cbn [hl_segs S4L pf_mxd] in SRC.
rewrite Z2Nat.id in SRC by lia.
assert (SRCL : Z.of_nat (length (firstn (Z.to_nat (co - co0)) (skipn (Z.to_nat co0) payload))) = co - co0) by (rewrite length_firstn, length_skipn; lia).
apply evt_RZ_done.
eapply (memappend_cps_c HIx MEMMOVE) with (lo := lo) (b := sb + co0) (n := co - co0);
[ exact HP1' | exact PCORE | (clear - Hco0 Hcol LEN; lia) | exact SRC | exact SRCL
| left; eapply (payload_crange (PEF _ _ _ _ _ _ _ _ _ _)); [exact SBin | intros bb Hbb; apply in_or_app; right; right; right; exact Hbb | cbn [pf_spf pf_mxd]; rewrite ?unsigned_lit by (clear - SP0; lia); unfold PE_FRAME; (clear; lia) | (clear - Hco0; lia) | (clear - Hco0; lia) | cbn [pf_len pf_mxd]; (clear - Hcol; lia)] | (clear - Hco0 SB0; lia) | (clear - SBL CO; lia) | (clear - Hco0 Hcol Hdsb; lia) | .. ]; try alloc_side.
all: try (rewrite ?unsigned_lit by lia; first [exact ST1 | exact ERR1]).
all: try (rewrite ?unsigned_lit by lia; unfold PE_FRAME in *; clia).
intros ms2 md2 (m2 & A2 & r & errv2 & buf' & cap' & RS2 & VM2 & ST2 & HPR2 & ERR2 & HP2 & OUT2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp S4L pf_mxd] in *. rewrite ?(unsigned_lit spf) in ST2 by lia. rewrite ?(unsigned_lit spf) in HPR2 by lia.
set (pbs2 := [(pb, 16); (buf', cap')]).
set (ts2 := TST depth levels co pb pbs2 (TS isd stpos (Z_to_bv 64 co) (Z_to_bv 64 14) ucs high quote) obj objs objbs).
pose proof INV1 as [CORE1 _]. destruct CORE1 as (_ & _ & _ & _ & TOK1 & _ & _ & TSK1 & FR1).
unfold tok_cells, tok_cells_g, ts1 in TOK1. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_tk pf_mxd] in TOK1.
unfold ts1 in TSK1. cbn [t_levels pf_mxd] in TSK1. unfold pe_frame, ts1 in FR1. cbn [t_obj pf_spf pf_mxd] in FR1.
assert (INq2 : In (q, (32 * mxd)) ((objbs ++ concat (map lvl_blocks levels)) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0))
by (apply in_or_app; right; right; left; reflexivity).
assert (INtk2 : In (tk, 72) ((objbs ++ concat (map lvl_blocks levels)) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0))
by (apply in_or_app; right; left; reflexivity).
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR1; [| left; cbn; lia]. cbn [hl_segs S4L pf_mxd] in FR1.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in TOK1; [| eapply client_range_block; [exact INtk2 | lia | cbn; lia]]. cbn [hl_segs S4L pf_mxd] in TOK1.
apply (tstack_pres_g S4L _ _ _ _ _ _ HPR2 INq2) in TSK1; [| exact LEN32].
assert (REST2 : PE_REST HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m2 md2 A2 ts2 errv2).
{ eapply (PE_REST_call_pb HIx) with (ts := ts1) (LBc := (objbs ++ concat (map lvl_blocks levels)) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0);
[exact STC | exact REST1 | exact VM2 | exact HPR2 | unfold ts1; cbn [t_objbs t_levels pf_mxd]; intros bb Hb; apply in_or_app;
apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; apply in_or_app; left; exact Hb | apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; right; right; exact Hb]]
| unfold pe_blocks, tstate_blocks; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_md pf_mxd pf_fl]; exact HP2
| exact ST2 | exact ERR2]. }
assert (PBany : pbuf rsegs m2 pbs2 pb).
{ destruct OUT2 as [[_ PBS] | (_ & -> & -> & PC)]; [eapply pbufc_pbuf; exact PBS|].
exists buf, 0, cap, [], post. split; [reflexivity|]. split; [reflexivity | exact PC]. }
assert (INV2 : PE_INV HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m2 md2 A2 ts2 cb j1 j2 utf sv errv2).
{ split; [| exact REST2]. unfold PE_CORE, ts2; cbn. split; [exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [exact TOK1|]. split; [exact PBany|]. split; [exact Hpb|]. split; [exact TSK1 | exact FR1]. }
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
clear HP1' SRC PBany PCORE REST1 INV1.
reenter MOK2.
destruct OUT2 as [[-> _] | (-> & -> & -> & _)].
- step. if_truex. apply evt_RZ_done.
eapply (KOUT ts2 []); [apply (PE_INV_W HIx); exact INV2 | tdok TDOK | eapply fsaved_trans; [exact FS | exact FS2] | apply FRM2; exact FRM].
- replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step. if_false. step. step. apply evt_RZ_done.
eapply (KERR ts2 []); [apply (PE_INV_W HIx); unfold ts2, pbs2; exact INV2 | tdok TDOK | eapply fsaved_trans; [exact FS | exact FS2] | apply FRM2; exact FRM].
Qed.

End PeNumVflush.

Section PeNumLoop.
Variable HIx : heap_iface S4L.
Variables (pf : pe_fix) (q : Z) (LBc : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(sv : pe_saved) (T : TSet) (F0 : bvmap 5 word).
Hypothesis MEMMOVE : memmove_stmt.
Hypothesis STRTOLL : strtox_stmt strtoll_entry.
Hypothesis STRTOULL : strtox_stmt strtoull_entry.
Hypothesis STRTOD : rstrtod_stmt.
Hypothesis STRDUP : strdup_stmt HIx.
Hypothesis CSTR : CSTR_OK pf payload.
Let LB0 : list blk := LB0 pf LBc.

#[using="MEMMOVE STRTOLL STRTOULL STRTOD STRDUP CSTR"] Lemma num_loop :
forall (kk : nat) (n : nat) (ts : tstate) (l : tlevel) (co0 ie po ne : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx)
(cb : byte) (j1 j2 utf : list byte) (errv : word)
(x1 gp t0 t1 t2 a6 a7 s7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (anb : word) ,
(Z.to_nat (pf_len pf - t_co ts) <= kk)%nat ->
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_number ->
pbufc rsegs m (t_pbs ts) (t_pb ts) [] -> 0 <= co0 <= t_co ts ->
Forall (fun b => numb b = true) (firstn (Z.to_nat (t_co ts - co0)) (skipn (Z.to_nat co0) payload)) ->
bytes_at rsegs me GOT_free_userdata (le8 (Z_to_bv 64 (fn_free_userdata S4F))) ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb -> bv_unsigned cb <> 0 ->
(ie = 0 \/ ie = 1) -> (po = 0 \/ po = 1) -> (ne = 0 \/ ne = 1) ->
tdepth_ok ts ->
fsaved F0 F -> frm0 fc ->
(16 * Z.to_nat (pf_len pf - co0) + 8 <= n)%nat ->
KALL HIx pf q LBc payload me lo sv T F0 n -> KOUT7 HIx pf q LBc payload me lo sv T F0 -> KERR7 HIx pf q LBc payload me lo sv T F0 ->
realizes rsegs (mkCfg (pe_ms7 rsegs pf 0x21f70 co0 x1 gp t0 t1 t2 (Z_to_bv 64 ie) (Z_to_bv 64 (t_co ts - co0)) (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 po) anb (Z_to_bv 64 (bv_unsigned cb)) a6 a7
(Z_to_bv 64 q) (Z_to_bv 64 (t_pb ts)) s7 (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 ne) t3 t4 t5 t6 F fc m) md) T.
Proof.
induction kk as [|kk IH]; intros until anb; intros Hkk STC INV Hl Hst PBC Hco0 NUM GOTU Hco Hcb NZ Hie Hpo Hne TDOK FS FRM Hn KALL KOUT KERR; [exfalso; lia|].
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & (SBL & RR & LENR)).
pose proof INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & _).
destruct ts as [depth levels co pb pbs xx obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct xx as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR. unfold pe_ms7, pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold_consts.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
set (LBall := pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) in *.
assert (INtk : In (tk, 72) LBall) by (unfold LBall, pe_blocks; apply in_or_app; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ tk 72 HP INtk) as Himg_t. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Himg_t.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi.
pose proof (bv_unsigned_in_range 8 cb) as CBR. unfold bv_modulus in CBR. cbn in CBR.
set (c := bv_unsigned cb) in *.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
pose proof (wmono_refl rsegs m) as WM. pose proof (munch_refl [(tk, tk + 72); (spf, spf + 144)] m) as MU.
assert (SBP : 0 < sb).
{ pose proof SBin as SBx. destruct SBx as [L0 | SBx]; [exfalso; clear - L0 Hco CO; lia|]. destruct SBx as [SBa | (bb & Hbb & Hb1 & _)]; [cbn [pf_spf pf_sb] in SBa; unfold PE_FRAME in SBa; clear - SBa SP0; lia |].
destruct bb as [ba bn]. pose proof (heap_blk S4L HIx _ _ _ _ ba bn HP ltac:(unfold LBall, pe_blocks; apply in_or_app; right; right; right; exact Hbb)) as (_ & _ & Hba & _).
cbn [blk_addr fst pf_sb] in Hb1. clear - Hb1 Hba; lia. }
assert (SW1 : bv_swrap 32 (co - co0 + 1) = co - co0 + 1).
{ unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296. rewrite Z.mod_small by lia. lia. }
assert (SW2 : bv_swrap 32 (co + 1) = co + 1).
{ unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296. rewrite Z.mod_small by lia. lia. }

assert (KEXIT : forall (r0 r2 r3 r4 r6 r7 s7' s10' : word),
evt rsegs (RZ rsegs md T)
(MS (mkR x1 (Z_to_bv 64 spf) gp (Z_to_bv 64 0x77c00) t0 t1 t2 (Z_to_bv 64 tk) (Z_to_bv 64 oldl) r0 (Z_to_bv 64 (co - co0)) r2 r3 r4 (Z_to_bv 64 c) r6 r7
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) (Z_to_bv 64 q) (Z_to_bv 64 (sb + co0)) (Z_to_bv 64 pb) s7' (Z_to_bv 64 (sb + co)) (Z_to_bv 64 (Z.of_nat depth)) s10' (Z_to_bv 64 PE_JTAB) t3 t4 t5 t6)
F (Z_to_bv 64 0x22f54) fc None m (seg_rom rsegs))).
{ intros r0 r2 r3 r4 r6 r7 s7' s10'.
destruct (Nat.eq_dec depth 0) as [D0 | Dn].
- rewrite D0. cbn [Z.of_nat]. tk3_walk 0x229f4 idtac. apply evt_RZ_done.
eapply (num_flush HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LBc payload me lo sv T F0 MEMMOVE STRTOLL STRTOULL STRTOD STRDUP n ts0 l co0);
[exact STC | exact INV | exact Hl | exact Hst | exact PBC | red_ts; lia | exact NUM | exact GOTU | exact Hco | exact Hcb | tdok TDOK | exact FS | exact FRM
| red_ts; lia | exact KALL | exact KOUT | exact KERR].
- tk3_walk 0x228e0 idtac. apply evt_RZ_done.
eapply (num_charchk_nz HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LBc payload me lo sv T F0 MEMMOVE STRTOLL STRTOULL STRTOD STRDUP n ts0 l co0);
[exact STC | exact INV | exact Hl | exact Hst | exact PBC | red_ts; lia | exact NUM | exact GOTU | exact Hco | exact Hcb | tdok TDOK | red_ts; exact Dn | exact FS | exact FRM
| red_ts; lia | exact KALL | exact KOUT | exact KERR]. }

assert (KPOST : forall (ie' po' : Z) (isd' : word) mc (a5' a6' a7' : word),
(ie' = 0 \/ ie' = 1) -> (po' = 0 \/ po' = 1) -> numb cb = true ->
rw_cells rsegs mc tk
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 (Z.of_nat depth)); C4 isd'; C4 stpos;
C4 (Z_to_bv 64 co); C4 err; C4 ucs; C4 high; C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)] ->
rw_cells rsegs mc spf
[C8 (Z_to_bv 64 obj); CB 16 j1; C4 (nbw j2); CB 3 (skipn 4 j2); C1 cb; CB 8 utf; C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv);
C8 (pe_s7 sv); C8 (pe_s6 sv); C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)] ->
munch [(tk, tk + 72); (spf, spf + 144)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
evt rsegs (RZ rsegs md T)
(MS (mkR x1 (Z_to_bv 64 spf) gp (Z_to_bv 64 0x77c00) t0 t1 t2 (Z_to_bv 64 tk) (Z_to_bv 64 oldl) (Z_to_bv 64 ie') (Z_to_bv 64 (co - co0)) (Z_to_bv 64 (sb + co)) (Z_to_bv 64 po') anb a5' a6' a7'
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) (Z_to_bv 64 q) (Z_to_bv 64 (sb + co0)) (Z_to_bv 64 pb) (Z_to_bv 64 (co - co0 + 1)) (Z_to_bv 64 (sb + co)) (Z_to_bv 64 (Z.of_nat depth)) (Z_to_bv 64 ne) (Z_to_bv 64 PE_JTAB) t3 t4 t5 t6)
F (Z_to_bv 64 0x21ff4) fc None mc (seg_rom rsegs))).
{ intros ie' po' isd' mc a5' a6' a7' Hie' Hpo' NUMcb TOKc FRc MUc WMc MIc.
assert (NUM1 : Forall (fun b => numb b = true) (firstn (Z.to_nat (co + 1 - co0)) (skipn (Z.to_nat co0) payload))).
{ replace (Z.to_nat (co + 1 - co0)) with (S (Z.to_nat (co - co0))) by lia.
rewrite (firstn_snoc_nth payload _ _ cb) by (replace (Z.to_nat co0 + Z.to_nat (co - co0))%nat with (Z.to_nat co) by lia; exact Hcb).
apply Forall_app. split; [exact NUM | constructor; [exact NUMcb | constructor]]. }
clear TOK FR KEXIT. stash PB. stash TSK. stash REST. stash PBC.
tk3_walk 0x22018 ltac:(try norm_sx32; try rewrite (unsigned_lit co) by lia; try rewrite SW2; try norm_w32).
unstash PB. unstash TSK. unstash REST. unstash PBC.
set (x1' := TS isd' stpos (Z_to_bv 64 (co + 1)) err ucs high quote).
set (ts1 := TST depth levels (co + 1) pb pbs x1' obj objs objbs).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
assert (INV1 : PE_INV HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m1 md A ts1 cb j1 j2 utf sv errv);
[ eapply (PE_INV_reframe HIx) with (ts := ts0); [exact STC | exact INV | exact MUc | exact WMc | assumption | | cbn; lia | reflexivity | ];
[ unfold ts0, tok_cells, tok_cells_g, x1'; cbn [t_pb t_depth ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_tk pf_mxd]; assumption
| unfold ts0, pe_frame; cbn [t_obj pf_spf pf_mxd]; assumption ]
| ];
assert (PBC1 : pbufc rsegs m1 pbs pb [])
by (eapply (pbufc_wtf HIx) with (ts := ts0); [exact STC | exact HP | exact PBC | exact MUc | exact WMc
| apply Forall_cons; [left; cbn; lia|]; apply Forall_cons; [right; cbn; unfold PE_FRAME; lia | apply Forall_nil]])
end.
clear PB TSK REST PBC INV MUc WMc.
pose proof INV1 as [_ REST1]. pose proof REST1 as (HP1 & _ & _ & _ & _ & STR1 & _).
step.
destruct (peek_cases (PEF tk oldl newl len lenr sb spf pmd mxd fl) payload co cb LENR CSTR (proj1 RR) ltac:(cbn [pf_len pf_mxd]; lia) ltac:(cbn [pf_len pf_mxd]; lia) Hcb NZ)
as [[Elenr EOF] | [HneL MORE]]; [cbn [pf_len pf_lenr pf_mxd] in Elenr, EOF; subst lenr; pose (lenr := len) | cbn [pf_len pf_lenr pf_mxd] in HneL, MORE].
-
tk3_walk 0x23d7c idtac. apply evt_RZ_done.
replace (co - co0 + 1) with (len - co0) by lia.
eapply (num_eof HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LBc payload me lo sv T F0 MEMMOVE ts1 l co0);
[exact STC | exact INV1 | exact Hl | red_ts; lia | red_ts; lia | exact PBC1 | tdok TDOK | exact FS | exact FRM | exact KOUT | exact KERR].
- tk3_walk 0x22020 idtac.
destruct (nth_error payload (Z.to_nat (co + 1))) as [cb'|] eqn:Hcb'; [| apply nth_error_None in Hcb'; lia].
pose proof (bv_unsigned_in_range 8 cb') as CBR'. unfold bv_modulus in CBR'. cbn in CBR'.
pose proof REST1 as (_ & _ & _ & _ & _ & _ & PLEN1 & SBin1 & _).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
pose proof (tok_flags_byte_g mxd fl m1 tk pb (Z.of_nat depth) q x1' ltac:(unfold x1'; eassumption)) as RDF;
pose proof (payload_byte m1 sb payload (co + 1) cb' STR1 Hcb' ltac:(lia)) as RDC;
pose proof (heap_mem_inv _ _ _ _ _ _ HP1) as MI1; cbn [hl_segs S4L pf_mxd] in MI1;
pose proof (wmono_refl rsegs m1) as WM2; pose proof (munch_refl [(tk, tk + 72); (spf, spf + 144)] m1) as MU2
end.
assert (HWP : Forall (pe_private (PEF tk oldl newl len lenr sb spf pmd mxd fl) q pbs) [(tk, tk + 72); (spf, spf + 144)]).
{ apply pe_wtf_private. apply Forall_cons; [left; cbn [fst snd pf_tk pf_mxd]; lia|].
apply Forall_cons; [right; unfold PE_FRAME; cbn [fst snd pf_spf pf_mxd]; lia | apply Forall_nil]. }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
assert (LATCH : forall mq (nv r4 r6 r7 u0 u1 u2 u3 u4 u5 u6 : word),
rw_cells rsegs mq tk
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 (Z.of_nat depth)); C4 isd'; C4 stpos;
C4 (Z_to_bv 64 (co + 1)); C4 err; C4 ucs; C4 high; C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)] ->
rw_cells rsegs mq spf
[C8 (Z_to_bv 64 obj); CB 16 j1; C4 nv; CB 3 (skipn 4 j2); C1 cb; CB 8 utf; C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv);
C8 (pe_s7 sv); C8 (pe_s6 sv); C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)] ->
munch [(tk, tk + 72); (spf, spf + 144)] m1 mq -> wmono rsegs m1 mq -> mem_inv rsegs mq ->
evt rsegs (RZ rsegs md T)
(MS (mkR x1 (Z_to_bv 64 spf) gp (Z_to_bv 64 0x77c00) u0 u1 u2 (Z_to_bv 64 tk) (Z_to_bv 64 oldl) (Z_to_bv 64 ie') (Z_to_bv 64 (co - co0)) (Z_to_bv 64 (sb + (co + 1))) (Z_to_bv 64 po') r4 (zxb cb') r6 r7
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) (Z_to_bv 64 q) (Z_to_bv 64 (sb + co0)) (Z_to_bv 64 pb) (Z_to_bv 64 (co - co0 + 1)) (Z_to_bv 64 (sb + (co + 1))) (Z_to_bv 64 (Z.of_nat depth)) (Z_to_bv 64 ne) (Z_to_bv 64 PE_JTAB) u3 u4 u5 u6)
F (Z_to_bv 64 0x22058) fc None mq (seg_rom rsegs))) end.
{ intros mq nv r4 r6 r7 u0 u1 u2 u3 u4 u5 u6 TOKq FRq MUq WMq MIq. clear RDF RDC.
stash INV1. stash PBC1. stash STR1.
step. rewrite QZDE.le1_zxb. mem_after_store.
tk3_walk 0x22064 ltac:(try rewrite (unsigned_lit (co - co0)) by lia; try rewrite SW1; try norm_w32).
unstash INV1. unstash PBC1. unstash STR1.
set (ts2 := TST depth levels (co + 1) pb pbs x1' obj objs objbs).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m2 _) =>
assert (INV2 : PE_INV HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m2 md A ts2 cb' j1 (le4 nv ++ skipn 4 j2) utf sv errv);
[ eapply (PE_INV_reframe HIx) with (ts := ts1); [exact STC | exact INV1 | exact MUq | exact WMq | exact MIq | | cbn; lia | reflexivity | ];
[ unfold ts1, tok_cells, tok_cells_g, x1'; cbn [t_pb t_depth ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_tk pf_mxd]; assumption
| unfold ts1; cbn [t_obj pf_spf pf_mxd]; apply pe_frame_nb_set; assumption ]
| ];
assert (PBC2 : pbufc rsegs m2 pbs pb [])
by (eapply (pbufc_wtf HIx) with (ts := ts1); [exact STC | exact HP1 | exact PBC1 | exact MUq | exact WMq
| apply Forall_cons; [left; cbn; lia|]; apply Forall_cons; [right; cbn; unfold PE_FRAME; lia | apply Forall_nil]])
end.
change (zxb cb') with (Z_to_bv 64 (bv_unsigned cb')).
step.
destruct (Z.eq_dec (bv_unsigned cb') 0) as [Z0 | NZ'].
+
tk3_walk 0x228dc idtac. apply evt_RZ_done.
replace (co - co0 + 1) with (co + 1 - co0) by lia.
eapply (num_charchk HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LBc payload me lo sv T F0 MEMMOVE STRTOLL STRTOULL STRTOD STRDUP n ts2 l co0);
[exact STC | exact INV2 | exact Hl | exact Hst | exact PBC2 | red_ts; lia | exact NUM1 | exact GOTU | red_ts; lia | exact Hcb' | tdok TDOK | exact FS | exact FRM
| red_ts; lia | exact KALL | exact KOUT | exact KERR].
+ tk3_walk 0x21f70 idtac. apply evt_RZ_done.
replace (co - co0 + 1) with (co + 1 - co0) by lia.
eapply (IH n ts2 l co0 ie' po'); [red_ts; lia | exact STC | exact INV2 | exact Hl | exact Hst | exact PBC2 | red_ts; lia | exact NUM1 | exact GOTU
| red_ts; lia | exact Hcb' | exact NZ' | exact Hie' | exact Hpo' | first [exact Hpo' | exact Hne] | tdok TDOK | exact FS | exact FRM | exact Hn | exact KALL | exact KOUT | exact KERR]. }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
assert (JOINS : forall mq (nv r4 r5 r6 r7 u0 u1 u2 u3 u4 u5 u6 : word),
rw_cells rsegs mq tk
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 (Z.of_nat depth)); C4 isd'; C4 stpos;
C4 (Z_to_bv 64 (co + 1)); C4 err; C4 ucs; C4 high; C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)] ->
rw_cells rsegs mq spf
[C8 (Z_to_bv 64 obj); CB 16 j1; C4 nv; CB 3 (skipn 4 j2); C1 cb; CB 8 utf; C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv);
C8 (pe_s7 sv); C8 (pe_s6 sv); C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)] ->
munch [(tk, tk + 72); (spf, spf + 144)] m1 mq -> wmono rsegs m1 mq -> mem_inv rsegs mq ->
evt rsegs (RZ rsegs md T)
(MS (mkR x1 (Z_to_bv 64 spf) gp (Z_to_bv 64 0x77c00) u0 u1 u2 (Z_to_bv 64 tk) (Z_to_bv 64 oldl) (Z_to_bv 64 ie') (Z_to_bv 64 (co - co0)) (Z_to_bv 64 (sb + (co + 1))) (Z_to_bv 64 po') r4 r5 r6 r7
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) (Z_to_bv 64 q) (Z_to_bv 64 (sb + co0)) (Z_to_bv 64 pb) (Z_to_bv 64 (co - co0 + 1)) (Z_to_bv 64 (sb + (co + 1))) (Z_to_bv 64 (Z.of_nat depth)) (Z_to_bv 64 ne) (Z_to_bv 64 PE_JTAB) u3 u4 u5 u6)
F (Z_to_bv 64 0x22050) fc None mq (seg_rom rsegs))) end.
{ intros mq nv r4 r5 r6 r7 u0 u1 u2 u3 u4 u5 u6 TOKq FRq MUq WMq MIq. clear RDF RDC.
stash INV1. stash PBC1. stash STR1.
step. try mem_after_store.
pose proof (payload_private HIx _ _ _ ts1 _ _ _ _ _ _ _ STC HP1 ltac:(unstash STR1; exact STR1) PLEN1 SBin1 MUq HWP) as STR'. cbn [pf_sb pf_mxd] in STR'.
pose proof (payload_byte _ sb payload (co + 1) cb' STR' Hcb' ltac:(lia)) as RDC'.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m' _) =>
lazymatch goal with FR' : rw_cells rsegs m' spf _ |- _ =>
eapply (LATCH m'); [exact TOKq | exact FR' | exact MUq | exact WMq | exact MIq]
end end. }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
assert (VERR : forall (r0 r1 r2 r3 r4 r5 r6 r7 s8' s10' u0 u1 u2 u3 u4 u5 u6 : word),
evt rsegs (RZ rsegs md T)
(MS (mkR x1 (Z_to_bv 64 spf) gp (Z_to_bv 64 0x77c00) u0 u1 u2 (Z_to_bv 64 tk) (Z_to_bv 64 oldl) r0 r1 r2 r3 r4 r5 r6 r7
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) (Z_to_bv 64 q) (Z_to_bv 64 (sb + co0)) (Z_to_bv 64 pb) (Z_to_bv 64 (co - co0 + 1)) s8' (Z_to_bv 64 (Z.of_nat depth)) s10' (Z_to_bv 64 PE_JTAB) u3 u4 u5 u6)
F (Z_to_bv 64 0x23dc4) fc None m1 (seg_rom rsegs))) end.
{ intros r0 r1 r2 r3 r4 r5 r6 r7 s8' s10' u0 u1 u2 u3 u4 u5 u6. apply evt_RZ_done.
replace (Z_to_bv 64 (co - co0 + 1)) with (Z_to_bv 64 (t_co ts1 - co0)) by (unfold ts1; cbn [t_co pf_mxd]; f_equal; lia).
eapply (num_vflush HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LBc payload me lo sv T F0 MEMMOVE ts1 l co0); [exact STC | exact INV1 | exact Hl | red_ts; lia | red_ts; lia | exact PBC1 | tdok TDOK | exact FS | exact FRM | exact KOUT | exact KERR]. }
step. rewrite (zxb_byte fl) by lia.
step. rewrite (unsigned_lit (fl mod 256)) by (pose proof (Z.mod_pos_bound fl 256 ltac:(lia)); lia). rewrite (land_mod256 fl 16) by lia.
step. replace (sb + co + 1) with (sb + (co + 1)) by lia.
destruct (land16_cases fl) as [F16 | F16]; rewrite F16.
+
tk3_walk 0x22058 idtac.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
lazymatch goal with TOK1 : rw_cells rsegs m1 tk _ |- _ =>
lazymatch goal with FR1 : rw_cells rsegs m1 spf _ |- _ =>
eapply (LATCH m1 (nbw j2)); [exact TOK1 | exact FR1 | exact MU2 | exact WM2 | exact MI1]
end end end.
+
Local Ltac utf_walk := repeat (lazymatch goal with
| |- evt _ _ (MS _ _ (Z_to_bv 64 0x23dc4) _ _ _ _) => fail
| |- evt _ _ (MS _ _ (Z_to_bv 64 0x22050) _ _ _ _) => fail
| |- evt _ _ (MS _ _ (Z_to_bv 64 0x22058) _ _ _ _) => fail
| |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => first [ub_if_lit_c | destruct cnd; cbv iota]
| |- _ => step
end).
utf_walk.
all: first [ apply VERR
| eapply (JOINS _ (nbw j2)); [eassumption | eassumption | exact MU2 | exact WM2 | exact MI1]
| eapply (LATCH _ (nbw j2)); [eassumption | eassumption | exact MU2 | exact WM2 | exact MI1] ]. }

stash PB. stash TSK. stash REST. stash PBC.
apply rz_evt; [exact MOK|].
assert (Ec : c = bv_unsigned cb) by reflexivity.
assert (DIGC : (48 <= c <= 57) \/ (c < 48 \/ 57 < c)) by lia.
assert (NOTDIG : forall a6' a7', c < 48 \/ 57 < c ->
evt rsegs (RZ rsegs md T)
(MS (mkR x1 (Z_to_bv 64 spf) gp (Z_to_bv 64 0x77c00) t0 t1 t2 (Z_to_bv 64 tk) (Z_to_bv 64 oldl) (Z_to_bv 64 ie) (Z_to_bv 64 (co - co0)) (Z_to_bv 64 (sb + co)) (Z_to_bv 64 po) anb (Z_to_bv 64 c) a6' a7'
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) (Z_to_bv 64 q) (Z_to_bv 64 (sb + co0)) (Z_to_bv 64 pb) s7 (Z_to_bv 64 (sb + co)) (Z_to_bv 64 (Z.of_nat depth)) (Z_to_bv 64 ne) (Z_to_bv 64 PE_JTAB) t3 t4 t5 t6)
F (Z_to_bv 64 0x21f7c) fc None m (seg_rom rsegs))).
{ intros a6' a7' NDIG.
step. step. step. rewrite (unsigned_lit c) by lia.
pose proof (land_lt_pow2 c 223 8 ltac:(lia) ltac:(lia)) as LR. change (2^8) with 256 in LR.
destruct (Z.eq_dec (Z.land c 223) 69) as [E69 | N69].
- assert (CE : c = 69 \/ c = 101).
{ clear - E69 CBR. assert (CASES : exists k : nat, (k < 256)%nat /\ c = Z.of_nat k) by (exists (Z.to_nat c); split; lia).
destruct CASES as (k & Hk & Ec). rewrite Ec in E69 |- *.
do 256 (destruct k as [|k]; [vm_compute in E69; first [discriminate E69 | lia] |]). exfalso; lia. }
if_falsex. step.
destruct Hie as [-> | ->].
+ clearbody c. destruct CE as [-> | ->];
(tk3_walk 0x21ff4 ltac:(try rewrite (unsigned_lit (co - co0)) by lia; try rewrite SW1);
eapply (KPOST 1 1 (Z_to_bv 64 1)); [right; reflexivity | right; reflexivity | apply numb_accept; lia | exact TOK | exact FR | exact MU | exact WM | assumption]).
+ tk3_walk 0x22f54 idtac. apply KEXIT.
- if_truex. step. step.
destruct (Z.eq_dec c 45) as [C45 | N45].
+ if_falsex. step.
destruct Hne as [-> | ->].
* tk3_walk 0x22f54 idtac. apply KEXIT.
* clearbody c. subst c.
tk3_walk 0x21ff4 ltac:(try rewrite (unsigned_lit (co - co0)) by lia; try rewrite SW1).
eapply (KPOST ie 0 isd); [exact Hie | left; reflexivity | apply numb_accept; lia | exact TOK | exact FR | exact MU | exact WM | exact MI].
+ if_truex. step. step.
destruct (Z.eq_dec c 43) as [C43 | N43].
* if_falsex. step.
destruct Hpo as [-> | ->].
-- tk3_walk 0x22f54 idtac. apply KEXIT.
-- clearbody c. subst c.
tk3_walk 0x21ff4 ltac:(try rewrite (unsigned_lit (co - co0)) by lia; try rewrite SW1).
eapply (KPOST ie 0 isd); [exact Hie | left; reflexivity | apply numb_accept; lia | exact TOK | exact FR | exact MU | exact WM | exact MI].
* if_truex. step. step.
destruct (Z.eq_dec c 46) as [C46 | N46].
-- if_truex. step. step.
lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd eqn:Kisd; cbv iota end.
++ clearbody c. subst c.
tk3_walk 0x21ff4 ltac:(try rewrite (unsigned_lit (co - co0)) by lia; try rewrite SW1).
eapply (KPOST ie 1 (Z_to_bv 64 1)); [exact Hie | right; reflexivity | apply numb_accept; lia | exact TOK | exact FR | exact MU | exact WM | assumption].
++ step. apply KEXIT.
-- if_falsex. step. apply KEXIT. }
destruct DIGC as [[GE48 LE57] | NDIG].
{ tk3_walk 0x21ff4 ltac:(try rewrite (unsigned_lit (co - co0)) by lia; try rewrite SW1).
eapply (KPOST ie 0 isd); [exact Hie | left; reflexivity | apply numb_accept; lia | exact TOK | exact FR | exact MU | exact WM | exact MI]. }
step. step. step.
destruct NDIG as [LT48 | GT57]; [rewrite <- (zbv_shift64 (c + -48)) |]; if_falsex; apply NOTDIG; lia.
Qed.
End PeNumLoop.

End RC__2.
