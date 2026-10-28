(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith List Lia Bool Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup UEQM Lib.GwApply QWxq QRjH QHnV QCcH QfLs Q0Ek Qtgi QjDH UC8c Qsw7 QJjn QRUw UtMn QkMG UG8z Udyh U2Sr ULbz UIsM UXfU UBpZ UT7i Uv6q QgoP UzWc U4Eu Uc8V UfOM UdFq Q6q3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require TopUbTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import UEQM.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq.Mq0 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0.
Import UC8c.Mq0.
Import Qsw7 QJjn QRUw.Mq0 QRUw.Mq2.
Import UtMn.
Import QkMG.
Import UG8z Udyh.Mq0 U2Sr ULbz UIsM.Mq2 UXfU.Mq0 Udyh.Mq7.
Import UBpZ UT7i Uv6q.
Import QgoP.
Import UzWc.
Import U4Eu.
Import Uc8V.
Import UfOM.
Import UdFq.
Import TopUbTac.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeNumEof.
Variable HIx : heap_iface S4L.
Variables (pf : pe_fix) (q : Z) (LBc : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(sv : pe_saved) (T : TSet) (F0 : bvmap 5 word).
Hypothesis MEMMOVE : memmove_stmt.
Let LB0 : list blk := LB0 pf LBc.

#[using="MEMMOVE"] Lemma num_eof :
forall (ts : tstate) (l : tlevel) (co0 : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx)
(cb : byte) (j1 j2 utf : list byte) (errv : word)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l ->
t_co ts = pf_len pf -> 0 <= co0 < pf_len pf ->
pbufc rsegs m (t_pbs ts) (t_pb ts) [] ->
tdepth_ok ts ->
fsaved F0 F -> frm0 fc ->
KOUT7 HIx pf q LBc payload me lo sv T F0 -> KERR7 HIx pf q LBc payload me lo sv T F0 ->
realizes rsegs (mkCfg (pe_ms7 rsegs pf 0x23d7c co0 x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 q) (Z_to_bv 64 (t_pb ts)) (Z_to_bv 64 (pf_len pf - co0)) s8 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Heof Hco0 PBC TDOK FS FRM KOUT KERR.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
pose proof INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & JCG).
destruct ts as [depth levels co pb pbs xx obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct xx as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff. subst co.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR. unfold pe_ms7, pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold_consts.
set (ts0 := TST depth levels len pb pbs (TS isd stpos (Z_to_bv 64 len) err ucs high quote) obj objs objbs) in *.
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

assert (TAIL : forall (e : Z) mc (a1' : word),
(e = 0 \/ e = 1) ->
rw_cells rsegs mc tk
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 (Z.of_nat depth)); C4 isd; C4 stpos;
C4 (Z_to_bv 64 len); C4 err; C4 ucs; C4 high; C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)] ->
munch [(tk, tk + 72)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
evt rsegs (RZ rsegs md T)
(MS (mkR x1 (Z_to_bv 64 spf) gp (Z_to_bv 64 0x77c00) t0 t1 t2 (Z_to_bv 64 tk) (Z_to_bv 64 oldl) (Z_to_bv 64 e) a1' a2 a3 a4 a5 a6 a7
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) (Z_to_bv 64 q) (Z_to_bv 64 (sb + co0)) (Z_to_bv 64 pb) (Z_to_bv 64 (len - co0)) s8 (Z_to_bv 64 (Z.of_nat depth)) s10 (Z_to_bv 64 PE_JTAB) t3 t4 t5 t6)
F (Z_to_bv 64 0x23dc8) fc None mc (seg_rom rsegs))).
{ intros e mc a1' He TOK' MU' WM' MI'.

assert (HW : Forall (pe_wtf (PEF tk oldl newl len lenr sb spf pmd mxd fl)) [(tk, tk + 72)]) by (apply Forall_cons; [left; cbn; lia | apply Forall_nil]).
stash PB. stash TSK. stash REST. stash FR.
bstepz. bstep. bstep. bstep. bstep.
unstash PB. unstash TSK. unstash REST. unstash FR.
set (ts1 := TST depth levels len pb pbs (TS isd stpos (Z_to_bv 64 len) (Z_to_bv 64 e) ucs high quote) obj objs objbs).
rename MU' into MU1. rename WM' into WM1.
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
clear MU1 WM1 PB TSK FR MU WM.

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
pose proof (bytes_at_sub S4L _ sb payload (Z.to_nat co0) (Z.to_nat (len - co0)) STR1 ltac:(lia)) as SRC. cbn [hl_segs S4L pf_mxd] in SRC.
rewrite Z2Nat.id in SRC by lia.
assert (SRCL : Z.of_nat (length (firstn (Z.to_nat (len - co0)) (skipn (Z.to_nat co0) payload))) = len - co0) by (rewrite length_firstn, length_skipn; lia).
apply evt_RZ_done.
eapply (memappend_cps_c HIx MEMMOVE) with (lo := lo) (b := sb + co0) (n := len - co0);
[ exact HP1' | exact PCORE | lia | exact SRC | exact SRCL
| left; eapply (payload_crange (PEF _ _ _ _ _ _ _ _ _ _)); [exact SBin | intros bb Hbb; apply in_or_app; right; right; right; exact Hbb | cbn [pf_spf pf_mxd]; rewrite ?unsigned_lit by lia; unfold PE_FRAME; lia | lia | lia | cbn [pf_len pf_mxd]; lia] | lia | lia | lia | .. ]; try alloc_side.
all: try (rewrite ?unsigned_lit by lia; first [exact ST1 | exact ERR1]).
all: try (rewrite ?unsigned_lit by lia; unfold PE_FRAME in *; clia).
intros ms2 md2 (m2 & A2 & r & errv2 & buf' & cap' & RS2 & VM2 & ST2 & HPR2 & ERR2 & HP2 & OUT2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp S4L pf_mxd] in *. rewrite ?(unsigned_lit spf) in ST2 by lia. rewrite ?(unsigned_lit spf) in HPR2 by lia.
set (pbs2 := [(pb, 16); (buf', cap')]).
set (ts2 := TST depth levels len pb pbs2 (TS isd stpos (Z_to_bv 64 len) (Z_to_bv 64 e) ucs high quote) obj objs objbs).
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
- bstep. if_truex. apply evt_RZ_done.
eapply (KOUT ts2 []); [apply (PE_INV_W HIx); exact INV2 | tdok TDOK | eapply fsaved_trans; [exact FS | exact FS2] | apply FRM2; exact FRM].
- replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
bstep. if_false. bstep. bstep. apply evt_RZ_done.
eapply (KERR ts2 []); [apply (PE_INV_W HIx); unfold ts2, pbs2; exact INV2 | tdok TDOK | eapply fsaved_trans; [exact FS | exact FS2] | apply FRM2; exact FRM]. }

stash PB. stash REST. clear LV OBJ HPR.
apply rz_evt; [exact MOK|].
destruct (PeanoNat.Nat.eq_dec depth 0) as [D0 | Dn].
+ subst depth. cbn [Z.of_nat pf_mxd] in TOK, TAIL |- *. bstep. if_false.
destruct (nth_error levels 0) as [l0|] eqn:Hl0; [| apply nth_error_None in Hl0; lia].
pose proof (TSK 0%nat l0 Hl0) as L0. rewrite Z.mul_0_r, Z.add_0_r in L0. unfold srec_cells in L0.
assert (SS26 : 0 <= tl_st l0 <= 26 /\ 0 <= tl_ss l0 <= 26) by (unstash REST; pose proof (proj1 (proj2 REST) 0%nat l0 Hl0) as (A1 & A2 & _); split; [exact A1 | exact A2]).
stash TSK.
bstep. norm_sx32.
destruct (Z.eq_dec (tl_st l0) 0) as [S0 | Sn].
* rewrite S0. bstep. if_false. bstep. norm_sx32. bstep.
destruct (Z.eq_dec (tl_ss l0) 2) as [F2 | Fn].
-- rewrite F2. bstep. if_false. bstep. bstep. unstash TSK. unstash PB. unstash REST. eapply (TAIL 0); [left; reflexivity | exact TOK | exact MU | exact WM | exact MI].
-- bstep. if_truex. bstep. bstep. unstash TSK. unstash PB. unstash REST. eapply (TAIL 1); [right; reflexivity | exact TOK | exact MU | exact WM | exact MI].
* bstep. if_truex. bstep. bstep. unstash TSK. unstash PB. unstash REST. eapply (TAIL 1); [right; reflexivity | exact TOK | exact MU | exact WM | exact MI].
+ bstep. if_truex. bstep. bstep. unstash PB. unstash REST. eapply (TAIL 1); [right; reflexivity | exact TOK | exact MU | exact WM | exact MI].
Qed.
End PeNumEof.

End RC__1.
End Mq0.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import UEQM.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0.
Import UC8c.Mq0.
Import Qsw7 QJjn QRUw.Mq0 QkMG.
Import UG8z Udyh.Mq0 U2Sr ULbz UIsM.Mq2 UXfU.Mq0.
Import UdFq.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeNumErr.
Variable HIx : heap_iface S4L.
Variables (pf : pe_fix) (q : Z) (LBc : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(sv : pe_saved) (T : TSet) (F0 : bvmap 5 word).
Let LB0 : list blk := LB0 pf LBc.

#[using="Type"] Lemma num_err_sw :
forall (ts : tstate) (e : Z) (m : word -> option byte) (md : Model) (A : AS S4L HIx)
(cb : byte) (j1 j2 utf : list byte) (errv : word) (cop : Z)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
0 <= e < 2^32 ->
tdepth_ok ts ->
fsaved F0 F -> frm0 fc ->
KOUT7 HIx pf q LBc payload me lo sv T F0 ->
realizes rsegs (mkCfg (pe_ms7 rsegs pf 0x23e48 cop x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 e) s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV He TDOK FS FRM KOUT.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
pose proof INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR.
unfold pe_ms7, pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold_consts.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ tk 72 HP INtk) as Himg_t. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Himg_t.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
pose proof (wmono_refl rsegs m) as WM.
pose proof (munch_refl [(tk, tk + 72); (spf, spf + PE_FRAME)] m) as MU.
stash PB. stash TSK. stash REST. clear HP.
apply rz_evt; [exact MOK|].
step. step.
unstash PB. unstash TSK. unstash REST.
apply evt_RZ_done.
eapply (KOUT (TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) (Z_to_bv 64 e) ucs high quote) obj objs objbs) []); [ | tdok TDOK | exact FS | exact FRM].
apply (PE_INV_W HIx).
eapply (PE_INV_retok HIx) with (ts := ts0); [exact STC | exact INV | exact MU | exact WM | assumption | | cbn; lia | reflexivity | ].
- unfold ts0, tok_cells, tok_cells_g. cbn [t_pb t_depth ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_tk pf_mxd]. assumption.
- unfold ts0, pe_frame. cbn [t_obj pf_spf pf_mxd]. exact FR.
Qed.
End PeNumErr.

End RC__1.
End Mq1.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QkMG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkMG.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UG8z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UG8z. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Udyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Udyh.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U2Sr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U2Sr. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require ULbz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import ULbz.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QmZZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmZZ. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QKQo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKQo.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uu4M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uu4M.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UdFq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UdFq.
Import TopUbTac.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Ltac enum_z H v :=
let rec go k := lazymatch k with
| 27%nat => exfalso; lia
| _ => let kz := eval vm_compute in (Z.of_nat k) in
let E := fresh "E" in
destruct (Z.eq_dec v kz) as [E | ?]; [ rewrite ?E in * | go (S k) ]
end in go 0%nat.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma number_mode : forall ss c hn, 0 <= ss <= 26 -> lvl_mode ST_number ss = Some (c, hn) -> c = CNone /\ hn = false.
Proof.
intros ss c hn R Hm. enum_z R ss; vm_compute in Hm; first [discriminate Hm | injection Hm as <- <-; split; reflexivity].
Qed.

Section PeNumTail.
Variable HIx : heap_iface S4L.
Variables (pf : pe_fix) (q : Z) (LBc : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(sv : pe_saved) (T : TSet) (F0 : bvmap 5 word).
Let LB0 : list blk := LB0 pf LBc.

Definition jres (s : jshape) (m : word -> option byte) (NB : list blk) (r : Z) : Prop :=
(r = 0 /\ NB = []) \/ (r <> 0 /\ jval rsegs S4F s m NB r 1).

#[using="Type"] Lemma num_tail :
forall (n : nat) (ts : tstate) (l : tlevel) (NB : list blk) (r : Z) (s : jshape)
(m : word -> option byte) (md : Model) (A : AS S4L HIx)
(cb : byte) (j1 j2 utf : list byte) (errv : word) (cop : Z)
(x1 gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INVK HIx pf q LB0 payload me lo m md A ts NB cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_number ->
jres s m NB r -> sdepth s = 0 ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->
tdepth_ok ts ->
fsaved F0 F -> frm0 fc ->
(mbase pf ts + 8 <= n)%nat ->
KALL HIx pf q LBc payload me lo sv T F0 n -> KOUT7 HIx pf q LBc payload me lo sv T F0 ->
realizes rsegs (mkCfg (pe_ms7 rsegs pf 0x22db0 cop x1 gp t0 t1 t2 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
s4 s6 s7 (Z_to_bv 64 (pf_sb pf + t_co ts)) s9 s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hst JR Hs0 Hco Hcb TDOK FS FRM Hn [KLOOP [KREDO [KBRK KBRK2]]] KOUT.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
destruct INV as (CORE & BASE & LV & OBJ).
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof (proj1 BASE) as HP.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR.
unfold pe_ms7, pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold mbase in Hn. cbn [pf_len t_co pf_mxd] in Hn.
unfold_consts.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
set (LBall := pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) in *.
assert (INtk : In (tk, 72) (LBall ++ NB)) by (apply in_or_app; left; unfold LBall, pe_blocks; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, (32 * mxd)) (LBall ++ NB)) by (apply in_or_app; left; unfold LBall, pe_blocks; apply in_or_app; right; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk S4L HIx _ _ _ _ q (32 * mxd) HP INq) as (_ & Hqal & Hqlo & Hqhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hqhi.
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND.
assert (Htq : tk <> q).
{ generalize ND; intros ND'. unfold LBall, pe_blocks in ND'. rewrite !map_app in ND'. apply NoDup_app_remove_r in ND'. apply NoDup_app_remove_l in ND'.
cbn [map blk_addr fst pf_tk pf_md pf_mxd pf_fl] in ND'. apply List.NoDup_cons_iff in ND' as [Hni _]. intros E. apply Hni. left. symmetry. exact E. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tk 72 q (32 * mxd) HP INtk INq Htq) as Hdtq.
assert (NQ0 : forall k, ~ In (q, k) LB0).
{ intros k. generalize ND; intros ND'. unfold LBall, pe_blocks in ND'. rewrite !map_app in ND'. apply NoDup_app_remove_r in ND'. apply NoDup_app_remove_l in ND'.
cbn [map blk_addr fst pf_tk pf_md pf_mxd pf_fl] in ND'.
apply List.NoDup_cons_iff in ND' as [_ ND']. apply List.NoDup_cons_iff in ND' as [Hnq _]. intros Hin. apply Hnq.
change q with (blk_addr (q, k)). apply in_map. exact Hin. }
assert (INCL0 : incl LB0 (LBall ++ NB)) by (unfold LBall, pe_blocks; intros b Hb; apply in_or_app; left; apply in_or_app; right; right; right; exact Hb).
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
pose proof (wmono_refl rsegs m) as WM.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & JO & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
rewrite Hst in Hmode. destruct (number_mode _ _ _ SS26 Hmode) as [-> ->].
cbn [name_ok pf_mxd] in NM0. destruct NM0 as [Hn0 Hnbs0].
destruct (tl_cs l) as [s0c|] eqn:Ecs; [exfalso; exact CLS0|]. cbn [jopt pf_mxd] in JO. destruct JO as [Hc0 Hcbs0].
assert (LB0l : lvl_blocks l = []) by (unfold lvl_blocks; rewrite Hcbs0, Hnbs0; reflexivity).
assert (Eobjbs : objbs = []).
{ revert OBJ. unfold cur_st, ts0. cbn [t_levels t_depth t_objbs pf_mxd]. rewrite Hl, Hst. cbn. intros E; exact E. }
set (BL := concat (map lvl_blocks levels)).
assert (NT0 : forall k, ~ In (tk, k) LB0).
{ intros k. generalize ND; intros ND'. unfold LBall, pe_blocks in ND'. rewrite !map_app in ND'. apply NoDup_app_remove_r in ND'. apply NoDup_app_remove_l in ND'.
cbn [map blk_addr fst pf_tk pf_md pf_mxd pf_fl] in ND'.
apply List.NoDup_cons_iff in ND' as [Hnt _]. intros Hin. apply Hnt. right.
change tk with (blk_addr (tk, k)). apply in_map. exact Hin. }

assert (NEq : forall a k, In (a, k) (NB ++ pbs ++ BL) -> In (a, k) (LBall ++ NB) /\ a <> q /\ a <> tk).
{ intros a k Hin.
assert (CASEs : In (a, k) NB \/ In (a, k) (tstate_blocks ts0)).
{ apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [left; exact Hin | right].
unfold tstate_blocks, ts0. cbn [t_pbs t_objbs t_levels pf_mxd].
apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [apply in_or_app; left; exact Hin | apply in_or_app; right; apply in_or_app; right; exact Hin]. }
clear Hin. assert (HinL : In (a, k) (LBall ++ NB)).
{ destruct CASEs as [Hin|Hin]; [apply in_or_app; right; exact Hin | apply in_or_app; left; unfold LBall, pe_blocks; apply in_or_app; left; exact Hin]. }
split; [exact HinL|].
generalize ND; intros ND'. destruct CASEs as [Hin|Hin].
- rewrite map_app in ND'. split; intros ->.
+ eapply (NoDup_app_in2 _ _ q ND'); [| exact (in_map blk_addr _ _ Hin)]. unfold LBall, pe_blocks. rewrite map_app. apply in_or_app; right. cbn. right; left; reflexivity.
+ eapply (NoDup_app_in2 _ _ tk ND'); [| exact (in_map blk_addr _ _ Hin)]. unfold LBall, pe_blocks. rewrite map_app. apply in_or_app; right. cbn. left; reflexivity.
- rewrite map_app in ND'. apply NoDup_app_remove_r in ND'. unfold LBall, pe_blocks in ND'. split; intros ->.
+ refine (nodup_app_ne _ _ _ _ _ _ ND' Hin _ eq_refl). right; left; reflexivity.
+ refine (nodup_app_ne _ _ _ _ _ _ ND' Hin _ eq_refl). left; reflexivity. }
assert (AGY : forall ma mz W, munch W ma mz -> wmono rsegs ma mz -> HEAP S4L HIx A (LBall ++ NB) ma md ->
Forall (fun iv => (q <= fst iv /\ snd iv <= q + (32 * mxd)) \/ (tk <= fst iv /\ snd iv <= tk + 72)) W ->
forall BS, (forall a k, In (a, k) BS -> In (a, k) (LBall ++ NB) /\ a <> q /\ a <> tk) -> agree_on rsegs BS ma mz).
{ intros ma mz W MU1 WM1 HPa HW BS HBS. eapply agree_of_munch; [exact MU1 | exact WM1 |]. intros a k Hin. destruct (HBS a k Hin) as (HinL & Hnq & Hnt).
pose proof (heap_blk S4L HIx _ _ _ _ a k HPa HinL) as (Hk0 & _ & _ & Hhi & _).
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ a k q (32 * mxd) HPa HinL INq Hnq).
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ a k tk 72 HPa HinL INtk Hnt).
clear - HW H H0 Hhi Hk0 LO LOS. induction W as [|[lo' hi'] W IH]; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. cbn [fst snd pf_mxd] in H1. cbn [disjoint_from pf_mxd]. split; [| apply IH; exact HW]. lia. }
remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (srec_join8 _ _ _ (TSK depth l Hl)) as Ld. cbn [le4 Z_to_le_bytes app hl_segs S4L pf_mxd] in Ld. rewrite Hc0, Hn0 in Ld. rewrite <- Hbse in Ld.
assert (HrR : 0 <= r < 2^64).
{ destruct JR as [[-> ->] | (Hr & J)]; [lia|].
assert (NDN : List.NoDup (map blk_addr NB)) by (generalize ND; intros ND'; rewrite map_app in ND'; apply NoDup_app_remove_l in ND'; exact ND').
pose proof (jval_hdr rsegs S4F _ _ _ _ _ J NDN) as (hs & tojs & pbx & udel & ud & rest & Hin & _).
pose proof (heap_blk S4L HIx _ _ _ _ r hs HP ltac:(apply in_or_app; right; exact Hin)) as (Hhs0 & _ & H0 & Hhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi. lia. }
set (W := [(bse, bse + 32); (tk, tk + 72)]).
assert (HWq : Forall (fun iv => (q <= fst iv /\ snd iv <= q + (32 * mxd)) \/ (tk <= fst iv /\ snd iv <= tk + 72)) W).
{ unfold W. apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [right; cbn; lia | apply Forall_nil]. }
assert (HWb : Forall (base_w (PEF tk oldl newl len lenr sb spf pmd mxd fl) LB0 (LBall ++ NB)) W).
{ unfold W. apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; unfold base_w; cbn [fst snd pf_spf pf_mxd]; left.
- exists q, (32 * mxd). split; [exact INq|]. split; [exact NQ0 | lia].
- exists tk, 72. split; [exact INtk|]. split; [exact NT0 | lia]. }
pose proof (munch_refl W m) as MU. unfold W in MU.
stash PB. stash TSK. stash BASE. stash LV. stash JR. stash HWq. stash HWb. stash FR.
apply rz_evt; [exact MOK|].
assert (Hbal : bse mod 16 = 0) by (subst bse; Z.div_mod_to_equations; lia).
bstep. norm_sx32. bstep.
bstep. rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
bstep. replace (q + Z.of_nat depth * 32) with bse by lia.
ub_skip. if_truex. ub_skip. rewrite (unsigned_lit bse) by lia. rewrite (land7_of_mod16 bse Hbal). ub_if_lit_c.
step. ub_skip. if_truex.
unstash PB. unstash TSK. unstash BASE. unstash LV. unstash JR. unstash HWq. unstash HWb.

assert (REB : forall mc, munch W m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
PE_BASE HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) LB0 payload me lo mc md A (LBall ++ NB) errv /\
pbuf rsegs mc pbs pb /\
agree_on rsegs NB m mc /\
(forall i li, nth_error levels i = Some li -> i <> depth -> lvl_cur rsegs S4F mc depth i li) /\
rw_cells rsegs mc spf
[C8 (Z_to_bv 64 obj); CB 16 j1; C4 (nbw j2); CB 3 (skipn 4 j2); C1 cb; CB 8 utf; C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv);
C8 (pe_s7 sv); C8 (pe_s6 sv); C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)]).
{ intros mc MU1 WM1 MI1. unstash FR. split; [| split; [| split; [| split]]].
- eapply (PE_BASE_write HIx); [exact STC | exact BASE | exact INCL0 | exact MU1 | exact WM1 | exact MI1 | exact HWb].
- eapply pbuf_agree; [exact PB | apply (AGY m mc W MU1 WM1 HP HWq) | apply incl_refl]. intros a k Hin; eapply NEq; apply in_or_app; right; apply in_or_app; left; exact Hin.
- apply (AGY m mc W MU1 WM1 HP HWq). intros a k Hin; eapply NEq; apply in_or_app; left; exact Hin.
- intros i li Hli Hne. eapply (lvl_cur_agree rsegs S4F); [exact (LV i li Hli) | | apply incl_refl].
apply (AGY m mc W MU1 WM1 HP HWq). intros a k Hin; eapply NEq; apply in_or_app; right; apply in_or_app; right.
unfold BL. apply in_concat. exists (lvl_blocks li). split; [| exact Hin]. apply in_map. eapply nth_error_In. exact Hli.
- eapply (rw_cells_transport rsegs _ m mc); [exact FR | exact MU1 | exact WM1 | cbn; unfold PE_FRAME in *; lia]. }
destruct JR as [[-> ->] | (Hr & J2)].
-
step. if_false. step. step. stepz. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
destruct (REB mc MU WM ltac:(assumption)) as (BASE3 & PB3 & AGN & LV3 & FR3) end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with L8 : rw_cells rsegs mc bse (?c1 :: ?rest) |- _ =>
pose proof (rw_cells_recast_prefix rsegs mc bse [c1] [C4 (Z_to_bv 64 (tl_st l)); C4 (Z_to_bv 64 (tl_ss l))]
rest L8 ltac:(cbn; repeat split) eq_refl eq_refl) as L5; cbn [app pf_mxd] in L5 end end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TSK3 : tstack rsegs mc q levels)
by (rewrite <- (lupd_same levels depth l Hl) at 1; subst bse;
eapply (tstack_put rsegs m mc q levels depth l [(tk, tk + 72)]);
[exact TSK | lia | exact MU | exact WM | intros j Hj Hne; cbn; lia | unfold srec_cells; rewrite Hc0, Hn0; exact L5])
end.
apply evt_RZ_done.
eapply (KOUT (TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) (Z_to_bv 64 16) ucs high quote) obj objs objbs) []);
[ | tdok TDOK | exact FS | exact FRM].
apply (PE_INVK_W HIx). split; [| split; [| split]].
+ unfold PE_CORE. cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj ts_choff pf_len pf_tk pf_spf pf_mxd].
split; [exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [unfold tok_cells, tok_cells_g; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd]; assumption|].
split; [exact PB3|]. split; [exact Hpb|]. split; [exact TSK3 | unfold pe_frame; exact FR3].
+ cbn [app pf_mxd] in BASE3 |- *. rewrite app_nil_r in BASE3 |- *. exact BASE3.
+ cbn [t_levels t_depth pf_mxd]. intros i li Hli.
destruct (Nat.eq_dec i depth) as [-> | NE].
* rewrite Hl in Hli. injection Hli as <-.
eapply (lvl_cur_agree rsegs S4F); [exact LVd | | apply incl_refl]. rewrite LB0l. intros a Ha (b & Hb & _). destruct Hb.
* exact (LV3 i li Hli NE).
+ revert OBJ. unfold cur_st, ts0. cbn [t_levels t_depth t_objs t_objbs t_obj pf_mxd]. rewrite Hl, Hst. cbn. intros E; exact E.
-
step. if_truex.
step. step. step. step.
assert (E1 : v_slti (Z_to_bv 64 (Z.of_nat depth)) 0 = Z_to_bv 64 0) by (apply QRUw.v_slti_0; rewrite QRUw.zsig_lit by lia; lia).
assert (E2 : v_sltu (Z_to_bv 64 bse) (Z_to_bv 64 q) = Z_to_bv 64 0)
by (unfold v_sltu, c_ltu, bv_ltu; rewrite !unsigned_lit by lia; destruct (Z.ltb_spec bse q); [lia | reflexivity]).
rewrite E1, E2. ub_if_lit_c.
step. rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
step. replace (q + Z.of_nat depth * 32) with bse by lia. step. step. rewrite (unsigned_lit bse) by lia. rewrite (land7_of_mod16 bse Hbal). ub_if_lit_c.
step. step. stepz. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
destruct (REB mc MU WM ltac:(assumption)) as (BASE3 & PB3 & AGN & LV3 & FR3)
end.
set (l' := TL ST_eatws ST_finish r (Some s) NB 0 []).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
match goal with L8 : rw_cells rsegs mc bse _ |- _ =>
pose proof (rw_cells_recast_prefix rsegs mc bse [C8 (Z_to_bv 64 8589934592)] [C4 (Z_to_bv 64 ST_eatws); C4 (Z_to_bv 64 ST_finish)]
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 r); C8 (Z_to_bv 64 0)] L8 ltac:(cbn; repeat split)
ltac:(apply bytes_eq_by_unsigned; vm_compute; reflexivity) eq_refl) as L5; cbn [app pf_mxd] in L5;
assert (TSK3 : tstack rsegs mc q (lupd levels depth l'))
by (subst bse; eapply (tstack_put rsegs m mc q levels depth l' [(tk, tk + 72)]);
[exact TSK | lia | exact MU | exact WM | intros j Hj Hne; cbn; lia | unfold srec_cells, l'; cbn [tl_st tl_ss tl_cur tl_name pf_mxd]; exact L5])
end end.
set (ts3 := TST depth (lupd levels depth l') co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs).
apply evt_RZ_done.
eapply (KREDO ts3); [ | | unfold ts3; cbn [t_co pf_mxd]; exact Hco | unfold ts3; cbn [t_co pf_mxd]; exact Hcb | | | | exact FS | exact FRM].
+
unfold mredo, mbase, cur_st, cur_ss, ts3. cbn [t_levels t_depth t_co pf_len pf_mxd]. rewrite nth_error_lupd_eq by lia.
unfold l'. cbn [tl_st tl_ss pf_mxd]. change (rank ST_eatws ST_finish) with 6%nat. lia.
+ split.
* unfold PE_CORE, ts3. cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj ts_choff pf_len pf_tk pf_spf pf_mxd].
split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [unfold tok_cells, tok_cells_g; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd]; assumption|].
split; [exact PB3|]. split; [exact Hpb|]. split; [exact TSK3 | unfold pe_frame; exact FR3].
* apply (PE_REST_of_base HIx).
-- eapply (PE_BASE_perm HIx); [exact BASE3|].
unfold LBall, pe_blocks, tstate_blocks, ts0, ts3. cbn [t_pbs t_objbs t_levels pf_tk pf_mxd].
apply (Permutation_trans (l' := pbs ++ objbs ++ (lvl_blocks l' ++ concat (map lvl_blocks levels)) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0)).
++ unfold l', lvl_blocks at 2. cbn [tl_cbs tl_nbs pf_mxd]. fold BL. perm.
++ rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_head. rewrite (app_assoc (lvl_blocks l')).
apply Permutation_app; [| apply Permutation_refl].
apply (concat_lupd_fill levels depth l); [exact Hl | exact LB0l].
-- unfold ts3. cbn [t_levels t_depth pf_mxd]. intros i li Hli.
destruct (Nat.eq_dec i depth) as [-> | NE].
++ rewrite nth_error_lupd_eq in Hli by lia. injection Hli as <-.
split; [cbn; unfold ST_eatws; lia|]. split; [cbn; unfold ST_finish; lia|]. split.
{ cbn [tl_cs tl_cbs tl_cur l' jopt pf_mxd]. split; [exact Hr|]. eapply jval_agree; [exact J2 | exact AGN | apply incl_refl]. }
rewrite Nat.ltb_irrefl, Nat.eqb_refl. exists CAny, false. split; [reflexivity|]. split; [exact I|]. cbn. split; reflexivity.
++ rewrite nth_error_lupd_neq in Hli by congruence. exact (LV3 i li Hli NE).
-- revert OBJ. unfold cur_st, ts0, ts3. cbn [t_levels t_depth t_objs t_objbs t_obj pf_mxd]. rewrite nth_error_lupd_eq by lia. rewrite Hl, Hst. cbn. intros E; exact E.
+
unfold NUMC, cur_st, ts3. cbn [t_levels t_depth pf_mxd]. rewrite nth_error_lupd_eq by lia. cbn. intros E. discriminate E.
+
unfold SPOK, cur_st, ts3. cbn [t_levels t_depth pf_mxd]. rewrite !nth_error_lupd_eq by lia. cbn. first [intros E; discriminate E | split; intros E; discriminate E].
+
unfold ts3, l'. eapply (tdepth_ok_upd ts0 l); [exact TDOK | exact Hl | cbn [odep tl_cs pf_mxd]; rewrite Hs0; pose proof (odep_nonneg (tl_cs l)); lia | unfold ts0; cbn [t_depth pf_mxd]; lia | reflexivity].
Qed.
End PeNumTail.

End RC__1.
