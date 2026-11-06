(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QRjH QHnV QCcH QfLs Q0Ek Qtgi QjDH Qsw7 QJjn QRUw QkMG QG8z Qdyh QbFI Qhd4 Qwm6 QlKV QsKa Qiiq QSHS Ql4f Q1Y6 QrQv Qc5u QAzu Q6vt Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw QkMG. Import QG8z. Import QJjn.Mq0. Import Qdyh.Mq2.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QsKa.Mqd Qiiq QSHS Ql4f.Mq4 Q1Y6.Mq4 QrQv.Mq4.
Import Qdyh.Mq2. Import Qc5u QAzu.Mq0 Q6vt.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeLoopB.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Let PRW := PE_REST_A_private_write HIx GA GA_outside.

Lemma seg_loop_B :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(gp t0 a0 a1 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> pf_fl pf = 0 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
(pf_lenr pf <> pf_len pf -> t_co ts < pf_len pf) ->

(forall m' (c : byte) (nb' : word) gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6',
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some c ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B ts c nb' pj sv errv ->
(forall b, PBOKat m ts b -> PBOKat m' ts b) ->
AJ5 A4L HIx A T md (pe_msA asegs pf pa APE_REDO0 (t_co ts) gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F fc m')) ->

(forall m' (e : word) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (Qdyh.Mq2.ts_set_err ts e) cb nb pj sv errv ->
AJ5 A4L HIx A T md (pe_msO asegs pf pa APE_OUT gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F fc m')) ->
AJ5 A4L HIx A T md (pe_msA asegs pf pa APE_LOOP (t_co ts) gp t0 a0 a1 (Z_to_bv 64 (pf_tk pf + 36)) a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC FL0 INV CLT Kredo Kout. pose proof INV as INV0.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *. subst fl.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold Qdyh.Mq2.ts_set_err in Kout. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in Kout.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH). unfold pe_msA, pe_msO in *.
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd 0) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd 0) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 2 HP INtk ltac:(lia)) as SHT2. replace (tk / 8 + 2 + A_SB) with (tk / 8 + 2147450882) in SHT2 by (unfold A_SB; lia).
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4. replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 7 HP INtk ltac:(lia)) as SHT7. replace (tk / 8 + 7 + A_SB) with (tk / 8 + 2147450887) in SHT7 by (unfold A_SB; lia).
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 8 HP INtk ltac:(lia)) as SHT8. replace (tk / 8 + 8 + A_SB) with (tk / 8 + 2147450888) in SHT8 by (unfold A_SB; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (bytes_at_bound _ _ _ _ STR) as SBB.
pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
assert (INF : In (Ff, 2) ((Ff, 2) :: FRS)) by (left; reflexivity).
assert (INtk' : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd 0) q LB0 ts0 ++ LM)) by (apply in_or_app; left; exact INtk).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF INtk') as DFt. rewrite fr_size_2 in DFt.
assert (GF0' : 0 <= Ff) by lia. assert (GFc' : Ff < alloc_ceiling) by lia.
pose proof (shadow_blk_apart HIx _ _ _ _ _ _ _ _ _ Ff 32 HP INtk' GF0' GFc' ltac:(lia)) as DSt.
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as DSF. rewrite fr_size_2 in DSF. cbn [hl_sb A4L] in DSF.
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd 0 0 HP INq ltac:(lia) ltac:(lia)) as SHQ0. replace (q / 8 + 4 * 0 + 0 + A_SB) with (q / 8 + 2147450880) in SHQ0 by (unfold A_SB; lia).
assert (Hq8 : q mod 8 = 0) by (clear - Hqal; Z.div_mod_to_equations; lia).
unfold APE_LOOP, APE_REDO0, APE_OUT in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash PB. stash INV0. stash Kredo. stash Kout. clear OBJ HPR BUD.
reenterA asegs A4L HIx asegs_wx HP.
step. asan_rechkB.
step.
norm_sx32.
destruct (loop_cases (PEF tk oldl newl len lenr sb spf pmd mxd 0) co LENR (proj1 RR) ltac:(cbn [pf_len pf_mxd]; lia) ltac:(cbn [pf_len pf_mxd]; lia) CLT) as [[Elenr Heof] | [Hne Hmore]]; cbn [pf_len pf_lenr pf_mxd] in *.
-
subst lenr. subst co.
step. if_false.
step.
pose proof (munch_refl [(tk, tk + 72)] m) as MU. clear DFt DSt DSF.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc None ?mm ?rom) =>
assert (CONT : forall a0v a1v, evt asegs (AJ5e A4L HIx A T md) (MS (bvmap_set 11 a1v (bvmap_set 10 a0v R)) FF (Z_to_bv 64 0x993e8) fcc None mm rom)) end.
{ intros a0v a1v.
step. asan_rechkB.
step.
stepz.
step.
unstash INV0. unstash Kout.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
evt_done5;
destruct (PE_INV_A_tokw1 HIx GA GA_outside (PEF tk oldl newl len len sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv len (TS isd stpos (Z_to_bv 64 len) (Z_to_bv 64 1) ucs high quote) STC INV0 MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as [INVe _];
eapply (Kout mc (Z_to_bv 64 1)); exact INVe
end end. }
asan_rechkB.
step. step.
norm_sx32.
step.
destruct (PeanoNat.Nat.eq_dec depth 0) as [D0 | Dn].
+ subst depth. if_false.
step. asan_rechkB.
step. step.
step. if_falsex.
step. ub_land Hq8. step. ub_if_lit.
asan_chkB.
destruct (nth_error levels 0) as [l0|] eqn:Hl0; [| apply nth_error_None in Hl0; lia].
pose proof (TSK 0%nat l0 Hl0) as L0. rewrite Z.mul_0_r, Z.add_0_r in L0. unfold srec_cells in L0.
pose proof (LV 0%nat l0 Hl0) as (ST26 & SS26 & _).
step.
norm_sx32.
step.
step.
destruct (Z.eq_dec (tl_st l0) 0) as [S0 | Sn].
* rewrite S0. if_false.
step.
asan_chkB.
step.
norm_sx32.
step. step.
step.
destruct (Z.eq_dec (tl_ss l0) 2) as [F2 | Fn].
-- rewrite F2. if_false.
step. asan_rechkB.
stepz.
step.
unstash INV0. unstash Kout.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
evt_done5;
destruct (PE_INV_A_tokw1 HIx GA GA_outside (PEF tk oldl newl len len sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv len (TS isd stpos (Z_to_bv 64 len) (Z_to_bv 64 0) ucs high quote) STC INV0 MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as [INVe _];
eapply (Kout mc (Z_to_bv 64 0)); exact INVe
end end.
-- if_truex. apply (CONT _ _).
* if_truex. apply (CONT _ _).
+ if_truex. apply (CONT _ _).
-
step. if_truex.
assert (Hco : co < len) by lia.
destruct (nth_error payload (Z.to_nat co)) as [c|] eqn:Hc; [| apply nth_error_None in Hc; lia].
pose proof (payload_byteA _ _ _ _ _ STR Hc ltac:(lia)) as RDC.
pose proof (bv_unsigned_in_range 8 c) as CBR'; unfold bv_modulus in CBR'; cbn in CBR'.
destruct SBin as [L00 | PL]; [exfalso; lia|].
pose proof (payload_shadow_pe HIx (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) LB0 FRS _ _ _ _ _ _ _ co HP
ltac:(intros bb Hbb; unfold pe_blocksA; apply in_or_app; right; right; right; exact Hbb) PL ltac:(cbn [pf_len]; lia)) as (v & SHP & Hv).
cbn [pf_sb] in SHP, Hv. unfold A_SB in SHP.
assert (SBhi : sb + len <= 2^47).
{ destruct PL as [([b0 n0] & Hb0 & Hb1 & Hb2) | (Fh & kh & HFh & HF1 & HF2 & _)]; cbn [pf_sb pf_len pa_sp0 blk_addr blk_size fst snd] in *.
- pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ b0 n0 HP ltac:(apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; right; right; exact Hb0)) as (_ & _ & _ & Hbhi & _). lia.
- pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP (or_intror HFh)) as (_ & _ & _ & HFhc & _). lia. }
assert (SHPF : (sb + co) / 8 + 2147450880 + 1 <= Ff \/ Ff + 256 <= (sb + co) / 8 + 2147450880) by (clear - DSF SBhi SB0 CO Hmore; Z.div_mod_to_equations; lia).
assert (SBpos : 0 < sb) by (unstash INV0; exact (pe_sb_pos HIx GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV0 ltac:(cbn [pf_len]; lia))).
assert (LE1 : le1 (zxb c) = [c]).
{ unfold le1, zxb. cbn [Z_to_le_bytes pf_mxd]. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256%Z. change (bv_modulus 64) with 18446744073709551616%Z. Z.div_mod_to_equations. nia. }
pose proof (munch_refl [(tk, tk + 72); (Ff + 64, Ff + 65)] m) as MU.
stash Hv. stash GAP. stash SAVED. stash FSH. stash DSt. stash DSF. stash SHPF. stash REST. stash LE1. stash Hc. stash STR. stash RDC.
step. asan_rechkB.
pose proof (tok_flags_byteA mxd 0 m tk pb (Z.of_nat depth) q (TS isd stpos (Z_to_bv 64 co) err ucs high quote) TOK) as RDF.
step. step.
rewrite ?zxb_zero. clear RDF.
step. step.
step. if_true.
step. if_truex.
step.
sh_norm.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc None ?mm ?rom) =>
assert (JOIN : forall a0x a1x, evt asegs (AJ5e A4L HIx A T md) (MS (bvmap_set 10 a0x (bvmap_set 11 a1x R)) FF (Z_to_bv 64 0x93fc8) fcc None mm rom)) end.
2:{ unstash Hv. destruct Hv as [-> | [Hv8 Hvlt]].
- step. rewrite ?sxb_zero. step. if_true. apply JOIN.
- step. rewrite (sxb_small v) by lia. step. if_falsex.
step.
step.
unstash SBhi. rewrite (unsigned_lit (sb + co)) by lia. rewrite (land7_mod8 (sb + co)) by lia.
pose proof (Z.mod_pos_bound (sb + co) 8 ltac:(lia)) as R8. remember ((sb + co) mod 8) as r8 eqn:Er8 in *.
step. if_falsex.
step.
apply JOIN. }
intros a0x a1x. clear SHP. unstash RDC.
step.
change (zxb c) with (Z_to_bv 64 (bv_unsigned c)). clear RDC.
step.
unstash LE1.
step.
replace (le1 (Z_to_bv 64 (bv_unsigned c))) with [c] by (rewrite <- LE1; reflexivity). mem_after_store.

unstash REST. unstash INV0. unstash Kredo. unstash Hc. unstash PB.
assert (HW : Forall (pe_wtfA (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl)) [(tk, tk + 72); (Ff + 64, Ff + 65)]).
{ apply Forall_cons; [left; cbn [fst snd pf_tk]; lia |]. apply Forall_cons; [| apply Forall_nil]. right; right; left. cbn [fst snd pa_F]. lia. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, FFc : rw_cells asegs mc Ff _ |- _ =>
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) c nb pj sv)
by (eapply (pe_frameA_scan HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact FR0 | exact MUc | exact WMc | exact FFc]);
evt_done5;
destruct (PE_INV_A_tokw HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv _ co (TS isd stpos (Z_to_bv 64 co) err ucs high quote) c nb STC INV0 MUc WMc MIc HW TOKc FRc
ltac:(cbn [pf_len]; lia) eq_refl) as [INV1 PBK1];
eapply (Kredo mc c nb); [exact Hco | reflexivity | exact INV1 | exact PBK1]
end end.
Qed.
End PeLoopB.
End RC__1.
End Mq0.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qtgi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qtgi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkMG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkMG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QG8z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QG8z. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdyh.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7UD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7UD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qiiq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qiiq.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1Ey.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1Ey. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql4f.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql4f.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1Y6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1Y6.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrQv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrQv.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeLoopA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Let PRW := PE_REST_A_private_write HIx GA GA_outside.

Ltac if_any_A := lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd; cbv iota end.

Lemma seg_loop_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 t4 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
(pf_lenr pf <> pf_len pf -> t_co ts < pf_len pf) ->

(forall m' (c : byte) (nb' : word) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5',
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some c ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B ts c nb' pj sv errv ->
(forall b, PBOKat m ts b -> PBOKat m' ts b) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_REDO (t_co ts) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5'
(Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F fc m')) ->

(forall m' (e : word) x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_set_err ts e) cb nb pj sv errv ->
AJ5 A4L HIx A T md
(pe_msO asegs pf pa APE_OUT x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' (Z_to_bv 64 (pf_tk pf + 56)) s11' t4' t6' F fc m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_LOOP (t_co ts) gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 (Z_to_bv 64 (pf_tk pf + 56)) t4 F fc m).
Proof.
intros until fc. intros STC INV CLT Kredo Kout.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH). unfold pe_msA, pe_msO in *.
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold pe_savedA_cells in SAVED. unfold ff_cellsA in FF. unfold ffsh_cells, FSH0 in FSH. cbn [map] in FSH.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (bytes_at_bound _ _ _ _ STR) as SBB.
pose proof alloc_ceiling_range as ACR.
unfold APE_LOOP, APE_REDO, APE_OUT in *.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.

assert (INF : In (Ff, 2) ((Ff, 2) :: FRS)) by (left; reflexivity).
assert (INtk' : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0 ++ LM)) by (apply in_or_app; left; exact INtk).
assert (INq' : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0 ++ LM)) by (apply in_or_app; left; exact INq).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF INtk') as DFt. rewrite fr_size_2 in DFt.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF INq') as DFq. rewrite fr_size_2 in DFq.
assert (GF0' : 0 <= Ff) by lia. assert (GFc' : Ff < alloc_ceiling) by lia.
pose proof (shadow_blk_apart HIx _ _ _ _ _ _ _ _ _ Ff 32 HP INtk' GF0' GFc' ltac:(lia)) as DSt.
pose proof (shadow_blk_apart HIx _ _ _ _ _ _ _ _ _ Ff 32 HP INq' GF0' GFc' ltac:(lia)) as DSq.
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as DSF. rewrite fr_size_2 in DSF. cbn [hl_sb A4L] in DSF.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash PB. stash REST. clear OBJ HPR.
reenterA asegs A4L HIx asegs_wx HP.
step. step. if_true.
step. norm_sx32. step. step.
destruct (loop_cases (PEF tk oldl newl len lenr sb spf pmd mxd fl) co LENR (proj1 RR) ltac:(cbn [pf_len pf_mxd]; lia) ltac:(cbn [pf_len pf_mxd]; lia) CLT) as [[Elenr Heof] | [Hne Hmore]]; cbn [pf_len pf_lenr pf_mxd] in *.
-
subst lenr. subst co. if_false.
step. step. step. if_true.
step. norm_sx32. step.
pose proof (munch_refl [(tk, tk + 72)] m) as MU.

assert (TAIL : forall (e : word) mc x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6',
rw_cells asegs mc tk
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 (Z.of_nat depth)); C4 isd; C4 stpos;
C4 (Z_to_bv 64 len); C4 e; C4 ucs; C4 high; C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)] ->
munch [(tk, tk + 72)] m mc -> wmono asegs m mc -> mem_inv asegs mc ->
evt asegs (AJ5e A4L HIx A T md)
(MS (mkR x1' (Z_to_bv 64 spf) gp (Z_to_bv 64 6434400) t0' t1' t2' (Z_to_bv 64 sp0) (Z_to_bv 64 spf) a0' a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 (Ff / 8 + 2147450880)) (Z_to_bv 64 (tk / 8 + 2147450882)) (Z_to_bv 64 (tk + 20)) s5' (Z_to_bv 64 (tk + 36))
s7' (Z_to_bv 64 Ff) (Z_to_bv 64 2147450880) (Z_to_bv 64 (tk + 56)) s11'
(Z_to_bv 64 (tk + 64)) t4' (Z_to_bv 64 (tk / 8 + 2147450888)) t6')
F (Z_to_bv 64 622696) fc None mc (seg_rom asegs))).
{ intros e mc x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' TOK' MU' WM' MI'.
unstash PB. unstash REST.
assert (HW : Forall (pe_wtfA (PEF tk oldl newl len len sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl)) [(tk, tk + 72)]) by (apply Forall_cons; [left; cbn; lia | apply Forall_nil]).
evt_done5. eapply (Kout mc e).
split.
- unfold PE_CORE_A, ts_set_err; cbn. split; [exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [exact TOK'|]. split; [| split; [exact Hpb | split]].
+ eapply (pbuf_wtfA HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact PB | exact MU' | exact WM' | exact HW].
+ eapply (tstack_wtfA HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact TSK | exact LEN32 | exact MU' | exact WM' | exact HW].
+ unfold pe_frameA, pe_slotsA, pe_savedA_cells, ff_cellsA, ffsh_cells, FSH0. cbn [map pf_tk pf_spf pf_lenr pa_F pa_sp0 pa_oldloc pa_newloc]. unfold shA, A_SB.
split; [| split; [| split; [| split]]].
* eapply rw_cells_transport; [exact SLOTS | exact MU' | exact WM' | cbn; lia].
* eapply rw_cells_transport; [exact GAP | exact MU' | exact WM' | cbn; lia].
* eapply rw_cells_transport; [exact SAVED | exact MU' | exact WM' | cbn; lia].
* eapply rw_cells_transport; [exact FF | exact MU' | exact WM' | cbn; lia].
* eapply rw_cells_transport; [exact FSH | exact MU' | exact WM' | cbn; lia].
- unfold ts_set_err; cbn. eapply PRW with (ts := ts0) in REST; [| exact STC | exact MU' | exact WM' | exact MI' | apply pe_wtfA_private; exact HW].
exact REST. }
step.
destruct (PeanoNat.Nat.eq_dec depth 0) as [D0 | Dn].
+ subst depth. cbn [Z.of_nat] in TOK |- *. if_false.
step. step. if_true.
step. step. step. sh_norm.
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd 0 0 HP INq ltac:(lia) ltac:(lia)) as SHQ0.
unfold A_SB in SHQ0. replace (q / 8 + 4 * 0 + 0 + 2147450880) with (q / 8 + 2147450880) in SHQ0 by lia.
step. step. if_true.
destruct (nth_error levels 0) as [l0|] eqn:Hl0; [| apply nth_error_None in Hl0; lia].
pose proof (TSK 0%nat l0 Hl0) as L0. rewrite Z.mul_0_r, Z.add_0_r in L0. unfold srec_cells in L0.
pose proof (stash_i _ TSK) as TSK'. clear TSK. rename TSK' into TSK.
pose proof (LV 0%nat l0 Hl0) as (ST26 & SS26 & _).
step. norm_sx32. step.
destruct (Z.eq_dec (tl_st l0) 0) as [S0 | Sn].
* rewrite S0. if_false.
step. step. step. sh_norm. replace ((q + 4) / 8) with (q / 8) by (Z.div_mod_to_equations; lia).
step. step. if_true.
step. norm_sx32. step. step.
destruct (Z.eq_dec (tl_ss l0) 2) as [F2 | Fn].
-- rewrite F2. if_false.
step. step. step. if_true.
step. step.
unstash TSK. eapply TAIL; [exact TOK | exact MU | exact WM | exact MI].
-- if_truex.
step. step. step. if_true. step. step. step.
unstash TSK. eapply TAIL; [exact TOK | exact MU | exact WM | exact MI].
* if_truex.
step. step. step. if_true. step. step. step.
unstash TSK. eapply TAIL; [exact TOK | exact MU | exact WM | exact MI].
+ if_truex.
step. step. step. if_true. step. step. step.
eapply TAIL; [exact TOK | exact MU | exact WM | exact MI].
-
if_truex.
assert (Hco : co < len) by lia.
destruct (nth_error payload (Z.to_nat co)) as [c|] eqn:Hc; [| apply nth_error_None in Hc; lia].
pose proof (tok_flags_byteA mxd fl m tk pb (Z.of_nat depth) q (TS isd stpos (Z_to_bv 64 co) err ucs high quote) TOK) as RDF.
pose proof (payload_byteA _ _ _ _ _ STR Hc ltac:(lia)) as RDC.
pose proof (bv_unsigned_in_range 8 c) as CBR; unfold bv_modulus in CBR; cbn in CBR.
destruct SBin as [L00 | PL]; [exfalso; lia|].
pose proof (payload_shadow_pe HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) LB0 FRS _ _ _ _ _ _ _ co HP
ltac:(intros bb Hbb; unfold pe_blocksA; apply in_or_app; right; right; right; exact Hbb) PL ltac:(cbn [pf_len]; lia)) as (v & SHP & Hv).
cbn [pf_sb] in SHP, Hv. unfold A_SB in SHP.

assert (SBhi : sb + len <= 2^47).
{ destruct PL as [([b0 n0] & Hb0 & Hb1 & Hb2) | (Fh & kh & HFh & HF1 & HF2 & _)]; cbn [pf_sb pf_len pa_sp0 blk_addr blk_size fst snd] in *.
- pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ b0 n0 HP ltac:(apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; right; right; exact Hb0)) as (_ & _ & _ & Hbhi & _). lia.
- pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP (or_intror HFh)) as (_ & _ & _ & HFhc & _). lia. }
assert (SHPlo : (sb + co) / 8 + 2147450880 + 1 <= alloc_ceiling) by (Z.div_mod_to_equations; lia).
unstash DSF.
assert (SHPF : (sb + co) / 8 + 2147450880 + 1 <= Ff \/ Ff + 256 <= (sb + co) / 8 + 2147450880) by (Z.div_mod_to_equations; lia).
stash DFt. stash DFq. stash DSt. stash DSq. stash DSF. stash Himg_t. stash Himg_q. stash Hv.
stash SHPF.

assert (LE1 : le1 (zxb c) = [c]).
{ unfold le1, zxb. cbn [Z_to_le_bytes pf_mxd]. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256%Z. change (bv_modulus 64) with 18446744073709551616%Z. Z.div_mod_to_equations. nia. }

assert (J30 : forall mc (a0x a1x a2x a3x nb' : word),
pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb' pj sv ->
rw_cells asegs mc tk [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 (Z.of_nat depth)); C4 isd; C4 stpos;
C4 (Z_to_bv 64 co); C4 err; C4 ucs; C4 high; C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)] ->
munch [(spf + 308, spf + 312); (Ff + 64, Ff + 65)] m mc -> wmono asegs m mc -> mem_inv asegs mc ->
evt asegs (AJ5e A4L HIx A T md)
(MS (mkR (Z_to_bv 64 (tk / 8 + 2147450884)) (Z_to_bv 64 spf) gp (Z_to_bv 64 6434400) t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 spf) a0x a1x a2x a3x a4 a5 a6 a7
(Z_to_bv 64 (Ff / 8 + 2147450880)) (Z_to_bv 64 (tk / 8 + 2147450882)) (Z_to_bv 64 (tk + 20)) s5 (Z_to_bv 64 (tk + 36))
(Z_to_bv 64 (tk + 32)) (Z_to_bv 64 Ff) (Z_to_bv 64 2147450880) (Z_to_bv 64 (tk + 56)) (Z_to_bv 64 (sb + co))
(Z_to_bv 64 (tk + 64)) (Z_to_bv 64 (Ff + 64)) (Z_to_bv 64 (tk / 8 + 2147450888)) (Z_to_bv 64 lenr))
F (Z_to_bv 64 603680) fc None mc (seg_rom asegs))).
{ intros mc a0x a1x a2x a3x nb' FRj TOKj MUj WMj MIj. clear RDF.
unfold pe_frameA in FRj. cbn [pf_tk pf_spf pf_lenr pa_F pa_sp0 pa_oldloc pa_newloc] in FRj. destruct FRj as (SLj & GAPj & SAVj & FFj & FSHj).
unfold pe_slotsA in SLj. cbn zeta in SLj. cbn [pf_tk pf_lenr pa_F pa_oldloc pa_newloc] in SLj. unfold pe_savedA_cells in SAVj. unfold ff_cellsA in FFj.
unfold ffsh_cells, FSH0 in FSHj. cbn [map] in FSHj. unfold shA, A_SB in SLj, FSHj.
unstash REST.
assert (HW1 : Forall (pe_privateA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q pbs) [(spf + 308, spf + 312); (Ff + 64, Ff + 65)]).
{ apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; unfold pe_privateA; cbn [fst snd pf_tk pf_spf pa_sp0 pa_F pf_mxd]; lia. }
assert (HWf : Forall (pe_wtfA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl)) [(spf + 308, spf + 312); (Ff + 64, Ff + 65)]).
{ apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; unfold pe_wtfA; cbn [fst snd pf_tk pf_spf pa_sp0 pa_F shA]; unfold A_SB; lia. }
pose proof (payload_privateA HIx _ _ _ _ _ _ _ ts0 _ _ _ _ _ _ _ STC (proj1 REST) STR PLEN (or_intror PL) MUj HW1) as STRj. cbn [pf_sb] in STRj.
pose proof (payload_byteA _ _ _ _ _ STRj Hc ltac:(lia)) as RDCj.
stash REST. unstash DSF. unstash DFt.
step.
change (zxb c) with (Z_to_bv 64 (bv_unsigned c)). step.
replace (le1 (Z_to_bv 64 (bv_unsigned c))) with [c] by (rewrite <- LE1; reflexivity). mem_after_store.
unstash REST.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
lazymatch goal with MUf : munch _ m mf, WMf : wmono asegs m mf, MIf : mem_inv asegs mf |- _ =>
evt_done5; eapply (Kredo mf c nb'); [exact Hco | reflexivity | | intros b PBKb; eapply (PBOKat_wtqA HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact PBKb | exact MUf | exact WMf | apply pe_wtfA_wtqA; exact HWf]];
split;
[ unfold PE_CORE_A; cbn; split; [exact LEN32|]; split; [exact D32|]; split; [lia|]; split; [reflexivity|];
split; [assumption|]; split; [| split; [exact Hpb | split]];
[ eapply (pbuf_wtfA HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | unstash PB; exact PB | exact MUf | exact WMf | exact HWf]
| eapply (tstack_wtfA HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact TSK | exact LEN32 | exact MUf | exact WMf | exact HWf]
| unfold pe_frameA, pe_slotsA, pe_savedA_cells, ff_cellsA, ffsh_cells, FSH0; cbn [map pf_tk pf_spf pf_lenr pa_F pa_sp0 pa_oldloc pa_newloc]; unfold shA, A_SB;
split; [exact SLj | split; [exact GAPj | split; [exact SAVj | split; [exact FFj | exact FSHj]]]] ]
| eapply PRW with (ts := ts0) in REST; [exact REST | exact STC | exact MUf | exact WMf | exact MIf | apply pe_wtfA_private; exact HWf] ]
end end. }

assert (J20 : forall mc (a1x a2x a3x nb' : word),
pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb' pj sv ->
rw_cells asegs mc tk [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 (Z.of_nat depth)); C4 isd; C4 stpos;
C4 (Z_to_bv 64 co); C4 err; C4 ucs; C4 high; C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)] ->
munch [(spf + 308, spf + 312); (Ff + 64, Ff + 65)] m mc -> wmono asegs m mc -> mem_inv asegs mc ->
evt asegs (AJ5e A4L HIx A T md)
(MS (mkR (Z_to_bv 64 (tk / 8 + 2147450884)) (Z_to_bv 64 spf) gp (Z_to_bv 64 6434400) t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 spf) (Z_to_bv 64 ((sb + co) / 8)) a1x a2x a3x a4 a5 a6 a7
(Z_to_bv 64 (Ff / 8 + 2147450880)) (Z_to_bv 64 (tk / 8 + 2147450882)) (Z_to_bv 64 (tk + 20)) s5 (Z_to_bv 64 (tk + 36))
(Z_to_bv 64 (tk + 32)) (Z_to_bv 64 Ff) (Z_to_bv 64 2147450880) (Z_to_bv 64 (tk + 56)) (Z_to_bv 64 (sb + co))
(Z_to_bv 64 (tk + 64)) (Z_to_bv 64 (Ff + 64)) (Z_to_bv 64 (tk / 8 + 2147450888)) (Z_to_bv 64 lenr))
F (Z_to_bv 64 603664) fc None mc (seg_rom asegs))).
{ intros mc a1x a2x a3x nb' FRj TOKj MUj WMj MIj. clear RDF RDC.
unstash SHPF.
assert (SHPj : ro_cells asegs mc ((sb + co) / 8 + 2147450880) [C1 (Z_to_bv 8 v)]).
{ eapply ro_cells_transport; [exact SHP | exact MUj | cbn; lia]. }
stash SHPF.
step.
unstash Hv. destruct Hv as [-> | [Hv8 Hvlt]].
- step. step. if_true.
eapply J30; [exact FRj | exact TOKj | exact MUj | exact WMj | exact MIj].
- step. rewrite (sxb_small v) by lia. step. if_falsex.
step. step. rewrite (unsigned_lit (sb + co)) by lia. rewrite (land7_mod8 (sb + co)) by lia.
pose proof (Z.mod_pos_bound (sb + co) 8 ltac:(lia)) as R8. remember ((sb + co) mod 8) as r8 eqn:Er8 in *.
step. if_falsex.
step.
eapply J30; [exact FRj | exact TOKj | exact MUj | exact WMj | exact MIj]. }

assert (J10 : forall (a1x a2x a3x : word),
evt asegs (AJ5e A4L HIx A T md)
(MS (mkR (Z_to_bv 64 (tk / 8 + 2147450884)) (Z_to_bv 64 spf) gp (Z_to_bv 64 6434400) t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 spf) (Z_to_bv 64 ((sb + co) / 8)) a1x a2x a3x a4 a5 a6 a7
(Z_to_bv 64 (Ff / 8 + 2147450880)) (Z_to_bv 64 (tk / 8 + 2147450882)) (Z_to_bv 64 (tk + 20)) s5 (Z_to_bv 64 (tk + 36))
(Z_to_bv 64 (tk + 32)) (Z_to_bv 64 Ff) (Z_to_bv 64 2147450880) (Z_to_bv 64 (tk + 56)) (Z_to_bv 64 (sb + co))
(Z_to_bv 64 (tk + 64)) (Z_to_bv 64 (Ff + 64)) (Z_to_bv 64 (tk / 8 + 2147450888)) (Z_to_bv 64 lenr))
F (Z_to_bv 64 603648) fc None m (seg_rom asegs))).
{ intros a1x a2x a3x. clear RDF RDC.
pose proof (munch_refl [(spf + 308, spf + 312); (Ff + 64, Ff + 65)] m) as MUs. pose proof (wmono_refl asegs m) as WMs.
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. cbn [pf_tk pf_lenr pa_F pa_oldloc pa_newloc] in SLOTS. unfold shA, A_SB in SLOTS.
step. try mem_after_store.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
lazymatch goal with MUf : munch _ m mf, WMf : wmono asegs m mf, MIf : mem_inv asegs mf, SLf : rw_cells asegs mf spf _ |- _ =>
eapply (J20 mf); [| exact TOK | exact MUf | exact WMf | exact MIf];
unfold pe_frameA, pe_slotsA, pe_savedA_cells, ff_cellsA, ffsh_cells, FSH0; cbn [map pf_tk pf_spf pf_lenr pa_F pa_sp0 pa_oldloc pa_newloc]; unfold shA, A_SB;
split; [exact SLf | split; [exact GAP | split; [exact SAVED | split; [exact FF | exact FSH]]]]
end end. }

assert (ERR14 : forall (a0x a1x a2x a3x : word),
evt asegs (AJ5e A4L HIx A T md)
(MS (mkR (Z_to_bv 64 (tk / 8 + 2147450884)) (Z_to_bv 64 spf) gp (Z_to_bv 64 6434400) t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 spf) a0x a1x a2x a3x a4 a5 a6 a7
(Z_to_bv 64 (Ff / 8 + 2147450880)) (Z_to_bv 64 (tk / 8 + 2147450882)) (Z_to_bv 64 (tk + 20)) s5 (Z_to_bv 64 (tk + 36))
(Z_to_bv 64 (tk + 32)) (Z_to_bv 64 Ff) (Z_to_bv 64 2147450880) (Z_to_bv 64 (tk + 56)) (Z_to_bv 64 (sb + co))
(Z_to_bv 64 (tk + 64)) (Z_to_bv 64 (Ff + 64)) (Z_to_bv 64 (tk / 8 + 2147450888)) (Z_to_bv 64 lenr))
F (Z_to_bv 64 623456) fc None m (seg_rom asegs))).
{ intros a0x a1x a2x a3x. clear RDF RDC.
pose proof (munch_refl [(tk, tk + 72)] m) as MUe.
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. cbn [pf_tk pf_lenr pa_F pa_oldloc pa_newloc] in SLOTS. unfold shA, A_SB in SLOTS.
unstash DFt. unstash DSt.
step. step. step. if_false.
step. step. step.
unstash REST.
assert (HW : Forall (pe_wtfA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl)) [(tk, tk + 72)]) by (apply Forall_cons; [left; cbn; lia | apply Forall_nil]).
evt_done5.
lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ _ _ _ ?mf _) =>
lazymatch goal with MUf : munch _ m mf, WMf : wmono asegs m mf, MIf : mem_inv asegs mf, TOKf : rw_cells asegs mf tk _ |- _ =>
eapply (Kout mf (Z_to_bv 64 14));
split;
[ unfold PE_CORE_A, ts_set_err; cbn; split; [exact LEN32|]; split; [exact D32|]; split; [lia|]; split; [reflexivity|];
split; [exact TOKf|]; split; [| split; [exact Hpb | split]];
[ eapply (pbuf_wtfA HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | unstash PB; exact PB | exact MUf | exact WMf | exact HW]
| eapply (tstack_wtfA HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact TSK | exact LEN32 | exact MUf | exact WMf | exact HW]
| unfold pe_frameA, pe_slotsA, pe_savedA_cells, ff_cellsA, ffsh_cells, FSH0; cbn [map pf_tk pf_spf pf_lenr pa_F pa_sp0 pa_oldloc pa_newloc]; unfold shA, A_SB;
split; [exact SLOTS | split; [exact GAP | split; [exact SAVED | split; [exact FF | exact FSH]]]] ]
| unfold ts_set_err; cbn; eapply PRW with (ts := ts0) in REST; [exact REST | exact STC | exact MUf | exact WMf | exact MIf | apply pe_wtfA_private; exact HW] ]
end end. }

step. step. if_true.
step. rewrite (zxb_byte fl).
step. step. sh_norm. rewrite (unsigned_lit (fl mod 256)) by (pose proof (Z.mod_pos_bound fl 256 ltac:(lia)); lia). rewrite (land_mod256 fl 16) by lia.
destruct (land16_cases fl) as [F16 | F16]; rewrite F16.
+
step. if_true.
eapply (J20 m); [| exact TOK | apply munch_refl | exact WM | exact MI].
unfold pe_frameA, pe_slotsA, pe_savedA_cells, ff_cellsA, ffsh_cells, FSH0; cbn [map pf_tk pf_spf pf_lenr pa_F pa_sp0 pa_oldloc pa_newloc]; unfold shA, A_SB.
split; [exact SLOTS | split; [exact GAP | split; [exact SAVED | split; [exact FF | exact FSH]]]].
+
step. if_false.

assert (JF4 : forall (a1x a2x a3x : word),
evt asegs (AJ5e A4L HIx A T md)
(MS (mkR (Z_to_bv 64 (tk / 8 + 2147450884)) (Z_to_bv 64 spf) gp (Z_to_bv 64 6434400) t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 spf) (Z_to_bv 64 ((sb + co) / 8)) a1x a2x a3x a4 a5 a6 a7
(Z_to_bv 64 (Ff / 8 + 2147450880)) (Z_to_bv 64 (tk / 8 + 2147450882)) (Z_to_bv 64 (tk + 20)) s5 (Z_to_bv 64 (tk + 36))
(Z_to_bv 64 (tk + 32)) (Z_to_bv 64 Ff) (Z_to_bv 64 2147450880) (Z_to_bv 64 (tk + 56)) (Z_to_bv 64 (sb + co))
(Z_to_bv 64 (tk + 64)) (Z_to_bv 64 (Ff + 64)) (Z_to_bv 64 (tk / 8 + 2147450888)) (Z_to_bv 64 lenr))
F (Z_to_bv 64 603620) fc None m (seg_rom asegs))).
{ intros a1x a2x a3x. clear RDF.
unfold pe_slotsA in SLOTS.
step.
step.
step. if_any_A.
*
step. if_any_A.
--  apply J20 with (nb' := nb); [| exact TOK | apply munch_refl | exact WM | exact MI].
split; [exact SLOTS | split; [exact GAP | split; [exact SAVED | split; [exact FF | exact FSH]]]].
--
step. step. step. step. step. if_any_A.
++ step. step. step. if_any_A.
** step. step. step. if_any_A.
--- step. step. apply J10.
--- step. apply ERR14.
** step. step. apply J10.
++ step. step. apply J10.
*
step. step. if_any_A.
-- step. apply J10.
-- step. apply ERR14.                                     }

step.
unstash Hv. destruct Hv as [-> | [Hv8 Hvlt]].
* step. step. if_true. apply JF4.
* step. rewrite (sxb_small v) by lia. step. if_falsex.
step. step. rewrite (unsigned_lit (sb + co)) by lia. rewrite (land7_mod8 (sb + co)) by lia.
pose proof (Z.mod_pos_bound (sb + co) 8 ltac:(lia)) as R8. remember ((sb + co) mod 8) as r8 eqn:Er8 in *. step. if_falsex. step. apply JF4.
Qed.
End PeLoopA.
End RC__1.
