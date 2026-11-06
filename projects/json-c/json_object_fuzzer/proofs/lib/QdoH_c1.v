(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkMG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkMG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QG8z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QG8z. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdyh.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdyh.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdyh.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QIsM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QIsM.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qa8x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qa8x.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLbz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLbz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMdR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMdR.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qa8x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qa8x.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7UD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7UD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qiiq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qiiq.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4v2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4v2.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1Ey.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1Ey. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql4f.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql4f.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1Y6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1Y6.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrQv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrQv.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEUF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEUF. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QW22.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QW22.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdGy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdGy.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYZ0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYZ0.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6oO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6oO. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdGy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdGy.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q63E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q63E.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVob.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVob.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qw5U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qw5U.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMgr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMgr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4xz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4xz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q63E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q63E.Mq6.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac QlEo_c1.solve_load ::= QXup.mkr__solve_load_3. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEUF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEUF.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition pinfdblA : list byte := Eval vm_compute in match image_bytes asegs 0x10340 8 with Some bs => bs | None => [] end.
Definition pinf2dblA : list byte := Eval vm_compute in match image_bytes asegs 0x22c28 8 with Some bs => bs | None => [] end.
Definition ninfdblA : list byte := Eval vm_compute in match image_bytes asegs 0x22c30 8 with Some bs => bs | None => [] end.
Lemma pinfdbl_roA : forall m, mem_inv asegs m -> ro_cells asegs m 0x10340 [CB 8 pinfdblA].
Proof. intros m MI. change 8%nat with (length pinfdblA). apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | cbn; lia]. Qed.
Lemma pinf2dbl_roA : forall m, mem_inv asegs m -> ro_cells asegs m 0x22c28 [CB 8 pinf2dblA].
Proof. intros m MI. change 8%nat with (length pinf2dblA). apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | cbn; lia]. Qed.
Lemma ninfdbl_roA : forall m, mem_inv asegs m -> ro_cells asegs m 0x22c30 [CB 8 ninfdblA].
Proof. intros m MI. change 8%nat with (length ninfdblA). apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | cbn; lia]. Qed.

Definition infstrA : list byte := Eval vm_compute in match image_bytes asegs 0x230c0 9 with Some bs => bs | None => [] end.
Definition invstrA : list byte := Eval vm_compute in match image_bytes asegs 0x230e0 9 with Some bs => bs | None => [] end.
Lemma infstr_atA : forall m, mem_inv asegs m -> bytes_at asegs m 0x230c0 infstrA.
Proof. intros m MI. apply rodata_bytes_at; [exact MI | vm_compute; reflexivity | lia | cbn; lia]. Qed.
Lemma invstr_atA : forall m, mem_inv asegs m -> bytes_at asegs m 0x230e0 invstrA.
Proof. intros m MI. apply rodata_bytes_at; [exact MI | vm_compute; reflexivity | lia | cbn; lia]. Qed.
Lemma infstrA_nz : forall k b, nth_error infstrA k = Some b -> (k <= 7)%nat -> bv_unsigned b <> 0.
Proof. intros k b H Hk. do 8 (destruct k as [|k]; [cbn in H; injection H as <-; vm_compute; discriminate|]). lia. Qed.
Lemma invstrA_nz : forall k b, nth_error invstrA k = Some b -> (k <= 7)%nat -> bv_unsigned b <> 0.
Proof. intros k b H Hk. do 8 (destruct k as [|k]; [cbn in H; injection H as <-; vm_compute; discriminate|]). lia. Qed.

Section PeSInfA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis NEWDBL : jo_new_double_A_stmt HIx.

Ltac pe_openA STC INV :=
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR); pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk);
destruct INV as [CORE REST];
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR);
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD).

Ltac shq_facts HP INq INtk q mxd tk dz j SH SEPc SEPq SEPt :=
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd dz j HP INq ltac:(lia) ltac:(lia)) as SH;
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q (32 * mxd) (4 * dz + j) q (32 * mxd) HP INq ltac:(lia) (in_or_app _ _ _ (or_introl INq))) as (SEPc & SEPq & _);
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q (32 * mxd) (4 * dz + j) tk 72 HP INq ltac:(lia) (in_or_app _ _ _ (or_introl INtk))) as (_ & SEPt & _);
cbn [hl_sb A4L] in SEPc, SEPq, SEPt.

Lemma inf_ctor_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP v2 ra2 : Z) (nB : nat)
(gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOKat m ts kP -> BOK pf pa ts B (S (Z.to_nat 2816 + nB)) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_inf ->
pe_s0 sv = Z_to_bv 64 v2 -> pe_ra sv = Z_to_bv 64 ra2 ->
(v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= v2) /\ 0 <= v2 < 2^64 ->
uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9d9cc) (UWfp ra2 v2) ->
dbl_special (Sem.reg_get F (Z_to_bv 5 10)) ->

(forall m' md' A' B' errv' r BS gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
(length BS <= 3)%nat -> jfresh (Sdouble false) BS 9 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_lvl ts (TL ST_eatws ST_finish r (Some (Sdouble false)) BS 0 [])) cb nb pj sv errv' ->
PBOKat m' (ts_lvl ts (TL ST_eatws ST_finish r (Some (Sdouble false)) BS 0 [])) kP ->
BOK pf pa (ts_lvl ts (TL ST_eatws ST_finish r (Some (Sdouble false)) BS 0 [])) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_REDO (t_co ts) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m')) ->

(forall m' md' A' B' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc',
PE_INVW_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts [] cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_ERRMEM x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' (Z_to_bv 64 (pf_tk pf + 56)) s11' t4' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x94c68 (t_co ts) gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC BSL INV PBK BK Hl Hst S0V RAV HV UWK DBL Kredo Kerr16. pose proof INV as INV0. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
unfold pe_msA, pe_msO in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
pose proof (TSK depth l Hl) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld. unfold srec_cells in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd (Z.of_nat depth) 0 HP INq ltac:(lia) ltac:(lia)) as SHQ.
replace (q / 8 + 4 * Z.of_nat depth + 0 + A_SB) with (q / 8 + 4 * Z.of_nat depth + A_SB) in SHQ by lia.
assert (Hb8 : bse mod 8 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
assert (SHQ4 : ro_cells asegs m (bse / 8 + A_SB) [C1 (Z_to_bv 8 0)]).
{ replace (bse / 8) with (q / 8 + 4 * Z.of_nat depth) by (subst bse; rewrite div8_add_mul32 by lia; lia). exact SHQ. }
pose proof (munch_refl [(bse, bse + 32)] m) as MU.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
unfold APE_BREAK, APE_REDO, APE_OUT, APE_ERRMEM, APE_ERRST, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
unfold SPV in *. cbn [t_x ts_stpos] in *.
assert (SPR : 0 <= bv_unsigned stpos mod 2^32 < 2^32) by (apply Z.mod_pos_bound; lia).
set (sp := bv_unsigned stpos mod 2^32) in *.
destruct (inf_mode _ _ _ SS26 ltac:(rewrite <- Hst; exact Hmode)) as (Ec0 & Ehn0). subst c0 hn0.
cbn [name_ok] in NM0. destruct NM0 as [Hn0 Hnbs0].
assert (Ecs : tl_cs l = None) by (destruct (tl_cs l); [exfalso; exact CLS0 | reflexivity]).
pose proof (LV depth l Hl) as (_ & _ & JO & _). rewrite Ecs in JO. cbn [jopt] in JO. destruct JO as [Ecur Ecbs].
assert (Eobjbs : objbs = []).
{ unfold cur_st in OBJ. cbn [t_levels t_depth t_objbs ts0] in OBJ. rewrite Hl, Hst in OBJ. exact OBJ. }
pose proof (PE_WIN_open HIx GA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 cb nb pj sv errv l INV0 Hl Hn0 Hnbs0 Eobjbs) as WIN0.
rewrite Ecur, Ecs, Ecbs in WIN0.
set (lw0 := TL (tl_st l) (tl_ss l) 0 None [] 0 []) in *. set (tw0 := ts_lvl ts0 lw0) in *.
assert (El : l = lw0) by (unfold lw0; destruct l as [st_ ss_ cur_ cs_ cbs_ name_ nbs_]; cbn [tl_st tl_ss tl_cur tl_cs tl_cbs tl_name tl_nbs] in *; congruence).
assert (Etw0 : tw0 = ts0) by (unfold tw0; rewrite <- El; apply (ts_lvl_same ts0 l Hl)).
assert (PBK0 : PBOKat m tw0 kP) by (exact (PBOKat_same m ts0 tw0 _ eq_refl eq_refl PBK)).
assert (Hlen0 : length (t_levels tw0) = Z.to_nat mxd) by (unfold tw0, ts_lvl, ts0; cbn [t_levels t_depth]; rewrite lupd_length; exact LEN32).
pose proof (BOK_afford (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts0 B nB new_scalar_costA BSL BK ltac:(pose proof (K_ev_pos (PEF tk oldl newl len lenr sb spf pmd mxd fl)); unfold new_scalar_costA; lia)) as COST.
stash Himg_t. stash Himg_q. stash Kredo. stash Kerr16. stash WIN0. stash INV0.
clear PB REST LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin SHT SHQ4 SHQ Ld Hdtq.
reenterA asegs A4L HIx asegs_wx HP.
step.

unstash WIN0.
evt_done5.
eapply (pe_new_double_w HIx GA GA_pres NEWDBL (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B tw0 cb nb pj sv errv T kP v2 ra2);
[ exact STC | exact WIN0 | exact PBK0 | exact COST | exact S0V | exact RAV | exact HV | exact UWK
| exact DBL
| rewrite unsigned_lit by lia; reflexivity |].
intros mn2 md2 A2 B2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 OUT2 PBK2 HB2 HD2 FS2 FRM2.
pose proof FS2 as FS2'.
cbn [pf_spf pa_sp0 pa_F] in *. unfold A_TP in *.
clear TOK SLOTS MU WM MI HP INtk INq Htal Htlo Hthi Hqal Hqlo Hqhi Hqtk WIN0 PBK0 FR0.
assert (Hlw0 : nth_error (t_levels tw0) depth = Some lw0) by (unfold tw0, ts_lvl, ts0; cbn [t_levels t_depth]; apply nth_error_lupd_eq; apply nth_error_Some; rewrite Hl; discriminate).
assert (Eb0 : lvl_blocks l = []) by (unfold lvl_blocks; rewrite Ecbs, Hnbs0; reflexivity).
destruct OUT2 as [(-> & WIN2) | (Hr & BS & LEN3 & JF & Rr & WIN2)].
-
pose proof WIN2 as (CORE2 & BASE2 & _). destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & TSK2 & FR2). pose proof (proj1 BASE2) as HP. clear BASE2.
unfold tw0, ts_lvl, ts0 in TOK. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR2 as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw0 []))) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw0 []))) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q2.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs mn2) as WM.
pose proof (TSK2 depth lw0 Hlw0) as Ld. rewrite <- Hbse in Ld. unfold srec_cells, lw0 in Ld. cbn [tl_st tl_ss tl_cur tl_name] in Ld.
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 2 SHQ2 SEPQ2c SEPQ2q SEPQ2t.
replace (q / 8 + 4 * (Z.of_nat depth) + 2 + A_SB) with (bse / 8 + 2147450882) in SHQ2 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 2) = bse / 8 + 2147450882) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ2c, SEPQ2q, SEPQ2t. clear EQx.
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 0 SHQ0 SEPQ0c SEPQ0q SEPQ0t.
replace (q / 8 + 4 * (Z.of_nat depth) + 0 + A_SB) with (bse / 8 + 2147450880) in SHQ0 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 0) = bse / 8 + 2147450880) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ0c, SEPQ0q, SEPQ0t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 7 HP INtk ltac:(lia)) as SHT7.
replace (tk / 8 + 7 + A_SB) with (tk / 8 + 2147450887) in SHT7 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 7 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT7c & SEPT7q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 7 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT7t & _).
cbn [hl_sb A4L] in SEPT7c, SEPT7q, SEPT7t. assert (EQx : tk / 8 + A_SB + 7 = tk / 8 + 2147450887) by (unfold A_SB; lia). rewrite EQx in SEPT7c, SEPT7q, SEPT7t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 2 HP INtk ltac:(lia)) as SHT2.
replace (tk / 8 + 2 + A_SB) with (tk / 8 + 2147450882) in SHT2 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 2 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT2c & SEPT2q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 2 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT2t & _).
cbn [hl_sb A4L] in SEPT2c, SEPT2q, SEPT2t. assert (EQx : tk / 8 + A_SB + 2 = tk / 8 + 2147450882) by (unfold A_SB; lia). rewrite EQx in SEPT2c, SEPT2q, SEPT2t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT4c & SEPT4q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT4t & _).
cbn [hl_sb A4L] in SEPT4c, SEPT4q, SEPT4t. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4c, SEPT4q, SEPT4t. clear EQx.
pose proof (munch_refl [(bse, bse + 32)] mn2) as MU.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_Q0_L : csep (bse / 8 + 2147450880) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPQ0q HbseR; lia).
assert (cs_T4_L : csep (tk / 8 + 2147450884) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPT4q HbseR; lia).
clear Hdtq SEPQ2c SEPQ2q SEPQ2t SEPQ0c SEPQ0q SEPQ0t SEPT7c SEPT7q SEPT7t SEPT2c SEPT2q SEPT2t SEPT4c SEPT4q SEPT4t.
stash Himg_t2. stash Himg_q2. stash WIN2. stash TSK2. stash FR2.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_rechkA.
step.
asan_rechkM 5.
step.
norm_sx32.
step.
rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
step.
replace (q + Z.of_nat depth * 32) with bse by lia.
step.
asan_chkM 1.
stepz.
step.
if_false.
step.
step.
step.
rewrite ?sxb_zero, ?zxb_zero.
step.
if_true.

unstash WIN2. unstash TSK2. unstash FR2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ mn2 mc, WMc : wmono asegs mn2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5;
assert (INqL : Forall (fun iv => exists a n, In (a, n) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw0 []) ++ LM) /\ a <= fst iv /\ snd iv <= a + n) [(bse, bse + 32)])
by (apply Forall_cons; [exists q, (32 * mxd); cbn [fst snd]; split; [apply in_or_app; left; exact INq | lia] | apply Forall_nil]);
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj sv)
by (eapply (pe_frameA_blkwriteG HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) _ LM FRS B2 A2 mn2 mc md2 lo [(bse, bse + 32)] cb nb pj sv); [exact STC | exact HP | exact INqL | exact FR2 | exact MUc | exact WMc]);
assert (TSKc : tstack asegs mc q (lupd (t_levels tw0) (t_depth tw0) lw0))
by (pose proof MUc as MUc'; pose proof Lc as Lc'; rewrite Hbse in MUc', Lc'; eapply (tstack_put asegs mn2 mc q (t_levels tw0) depth lw0 []);
[exact TSK2 | rewrite Hlen0; lia | exact MUc' | exact WMc | intros; exact I | exact Lc']);
destruct (PE_WIN_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mn2 mc md2 A2 B2 tw0 0 None [] 1
cb nb pj sv errv2 [(bse, bse + 32)] lw0 cb nb pj STC WIN2 MUc WMc MIc
ltac:(apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia | apply Forall_nil])
TOKc TSKc FRc ltac:(unfold lvl_bare, lw0; cbn [tl_st tl_ss tl_cs tl_cbs tl_name tl_nbs]; repeat split; try reflexivity; lia)) as [WIN3 PBT3]
end end.
set (tw2 := ts_lvl tw0 lw0) in *.
assert (Etw2 : tw2 = ts0) by (unfold tw2; rewrite (ts_lvl_same tw0 lw0 Hlw0); exact Etw0).
pose proof (BOK_weak _ _ _ _ _ (BOK_pay (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts0 B B2 nB new_scalar_costA BK ltac:(pose proof (K_ev_pos (PEF tk oldl newl len lenr sb spf pmd mxd fl)); unfold new_scalar_costA; lia) HB2 ltac:(lia))) as [HBw HDw].
pose proof (PE_WIN_close_weak HIx GA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md2 A2 B2 tw2 cb nb pj sv errv2 1 WIN3
ltac:(exists lw0; split; [rewrite Etw2, <- El; exact Hl | reflexivity])
ltac:(rewrite Etw2; exact HBw) HDw) as INVw.
rewrite Etw2 in INVw.
unstash Kerr16. eapply (Kerr16 _ md2 A2 B2 errv2); [exact INVw | exact FS2' | exact FRM2].
-
pose proof WIN2 as (CORE2 & BASE2 & _). destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & TSK2 & FR2). pose proof (proj1 BASE2) as HP. clear BASE2.
unfold tw0, ts_lvl, ts0 in TOK. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR2 as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw0 BS))) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw0 BS))) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q2.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs mn2) as WM.
pose proof (TSK2 depth lw0 Hlw0) as Ld. rewrite <- Hbse in Ld. unfold srec_cells, lw0 in Ld. cbn [tl_st tl_ss tl_cur tl_name] in Ld.
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 2 SHQ2 SEPQ2c SEPQ2q SEPQ2t.
replace (q / 8 + 4 * (Z.of_nat depth) + 2 + A_SB) with (bse / 8 + 2147450882) in SHQ2 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 2) = bse / 8 + 2147450882) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ2c, SEPQ2q, SEPQ2t. clear EQx.
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 0 SHQ0 SEPQ0c SEPQ0q SEPQ0t.
replace (q / 8 + 4 * (Z.of_nat depth) + 0 + A_SB) with (bse / 8 + 2147450880) in SHQ0 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 0) = bse / 8 + 2147450880) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ0c, SEPQ0q, SEPQ0t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 7 HP INtk ltac:(lia)) as SHT7.
replace (tk / 8 + 7 + A_SB) with (tk / 8 + 2147450887) in SHT7 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 7 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT7c & SEPT7q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 7 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT7t & _).
cbn [hl_sb A4L] in SEPT7c, SEPT7q, SEPT7t. assert (EQx : tk / 8 + A_SB + 7 = tk / 8 + 2147450887) by (unfold A_SB; lia). rewrite EQx in SEPT7c, SEPT7q, SEPT7t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 2 HP INtk ltac:(lia)) as SHT2.
replace (tk / 8 + 2 + A_SB) with (tk / 8 + 2147450882) in SHT2 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 2 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT2c & SEPT2q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 2 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT2t & _).
cbn [hl_sb A4L] in SEPT2c, SEPT2q, SEPT2t. assert (EQx : tk / 8 + A_SB + 2 = tk / 8 + 2147450882) by (unfold A_SB; lia). rewrite EQx in SEPT2c, SEPT2q, SEPT2t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT4c & SEPT4q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT4t & _).
cbn [hl_sb A4L] in SEPT4c, SEPT4q, SEPT4t. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4c, SEPT4q, SEPT4t. clear EQx.
pose proof (munch_refl [(bse, bse + 32)] mn2) as MU.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_Q0_L : csep (bse / 8 + 2147450880) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPQ0q HbseR; lia).
assert (cs_T4_L : csep (tk / 8 + 2147450884) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPT4q HbseR; lia).
clear Hdtq SEPQ2c SEPQ2q SEPQ2t SEPQ0c SEPQ0q SEPQ0t SEPT7c SEPT7q SEPT7t SEPT2c SEPT2q SEPT2t SEPT4c SEPT4q SEPT4t.
stash Himg_t2. stash Himg_q2. stash WIN2. stash TSK2. stash FR2.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_rechkA.
step.
asan_rechkM 5.
step.
norm_sx32.
step.
rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
step.
replace (q + Z.of_nat depth * 32) with bse by lia.
step.
asan_chkM 1.
stepz.
step.
if_truex.
step.
asan_chkA.
step.
stepz.
asan_chkA.
stepz.
step.

set (lw2 := TL ST_eatws ST_finish r None [] 0 []).
unstash WIN2. unstash TSK2. unstash FR2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ mn2 mc, WMc : wmono asegs mn2 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5;
assert (INqL : Forall (fun iv => exists a n, In (a, n) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF tw0 BS) ++ LM) /\ a <= fst iv /\ snd iv <= a + n) [(bse, bse + 32)])
by (apply Forall_cons; [exists q, (32 * mxd); cbn [fst snd]; split; [apply in_or_app; left; exact INq | lia] | apply Forall_nil]);
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj sv)
by (eapply (pe_frameA_blkwriteG HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) _ LM FRS B2 A2 mn2 mc md2 lo [(bse, bse + 32)] cb nb pj sv); [exact STC | exact HP | exact INqL | exact FR2 | exact MUc | exact WMc]);
assert (TSKc : tstack asegs mc q (lupd (t_levels tw0) (t_depth tw0) lw2))
by (pose proof MUc as MUc'; pose proof Lc as Lc'; rewrite Hbse in MUc', Lc'; eapply (tstack_put asegs mn2 mc q (t_levels tw0) depth lw2 []);
[exact TSK2 | rewrite Hlen0; lia | exact MUc' | exact WMc | intros; exact I | exact Lc']);
destruct (PE_WIN_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mn2 mc md2 A2 B2 tw0 r (Some (Sdouble false)) BS 1
cb nb pj sv errv2 [(bse, bse + 32)] lw2 cb nb pj STC WIN2 MUc WMc MIc
ltac:(apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia | apply Forall_nil])
TOKc TSKc FRc ltac:(unfold lvl_bare, lw2, ST_eatws, ST_finish; cbn [tl_st tl_ss tl_cs tl_cbs tl_name tl_nbs]; repeat split; try reflexivity; lia)) as [WIN3 PBT3]
end end.
set (tw2 := ts_lvl tw0 lw2) in *.
assert (Etw2 : forall lx, ts_lvl tw2 lx = ts_lvl ts0 lx) by (intros lx; unfold tw2, tw0; rewrite !ts_lvl_lvl; reflexivity).
assert (Hlw2 : nth_error (t_levels tw2) (t_depth tw2) = Some lw2) by (unfold tw2, ts_lvl; cbn [t_levels t_depth]; apply nth_error_lupd_eq; rewrite Hlen0; cbn [t_depth tw0 ts_lvl ts0]; lia).
assert (BKf : BOK (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) (ts_lvl ts0 (TL ST_eatws ST_finish r (Some (Sdouble false)) BS 0 [])) B2 nB).
{ eapply (BOK_attach (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) ts0 B B2 nB l ST_eatws ST_finish r (Sdouble false) BS new_scalar_costA BK Hl Ecs Eb0);
[ unfold phi_level; cbn [tl_cs]; lia
| unfold phi_level; cbn [tl_cs]; pose proof (K_ev_pos (PEF tk oldl newl len lenr sb spf pmd mxd fl)); unfold K_free, new_scalar_costA; lia
| intros kids Ek; discriminate Ek | intros kids Ek; discriminate Ek | exact HB2 | lia ]. }
pose proof (PE_WIN_close_cur HIx GA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md2 A2 B2 tw2 r (Sdouble false) BS cb nb pj sv errv2 lw2 CAny WIN3 Hlw2 eq_refl
ltac:(vm_compute; reflexivity) I ltac:(reflexivity)
ltac:(cbn [tl_st tl_ss lw2]; rewrite Etw2; exact (BOK_weak _ _ _ _ _ BKf))) as INVf.
cbn [tl_st tl_ss lw2] in INVf. rewrite Etw2 in INVf.
unstash Kredo. eapply (Kredo _ md2 A2 B2 errv2 r BS); [exact LEN3 | exact JF | exact INVf | | exact BKf | exact FS2' | exact FRM2].
eapply PBOKat_same with (ts := tw2); [reflexivity | reflexivity |]. exact (PBT3 _ PBK2).
Qed.

Lemma inf_pick_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP v2 ra2 : Z) (nB : nat)
(gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s10 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOKat m ts kP -> BOK pf pa ts B (S (Z.to_nat 2816 + nB)) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_inf ->
pe_s0 sv = Z_to_bv 64 v2 -> pe_ra sv = Z_to_bv 64 ra2 ->
(v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= v2) /\ 0 <= v2 < 2^64 ->
uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9d9cc) (UWfp ra2 v2) ->

(forall m' md' A' B' errv' r BS gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
(length BS <= 3)%nat -> jfresh (Sdouble false) BS 9 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_lvl ts (TL ST_eatws ST_finish r (Some (Sdouble false)) BS 0 [])) cb nb pj sv errv' ->
PBOKat m' (ts_lvl ts (TL ST_eatws ST_finish r (Some (Sdouble false)) BS 0 [])) kP ->
BOK pf pa (ts_lvl ts (TL ST_eatws ST_finish r (Some (Sdouble false)) BS 0 [])) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_REDO (t_co ts) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m')) ->

(forall m' md' A' B' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc',
PE_INVW_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts [] cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_ERRMEM x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' (Z_to_bv 64 (pf_tk pf + 56)) s11' t4' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x94bd8 (t_co ts) gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s10 (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC BSL INV PBK BK Hl Hst S0V RAV HV UWK Kredo Kerr16. pose proof INV as INV0. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
unfold pe_msA, pe_msO in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
pose proof (TSK depth l Hl) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld. unfold srec_cells in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd (Z.of_nat depth) 0 HP INq ltac:(lia) ltac:(lia)) as SHQ.
replace (q / 8 + 4 * Z.of_nat depth + 0 + A_SB) with (q / 8 + 4 * Z.of_nat depth + A_SB) in SHQ by lia.
assert (Hb8 : bse mod 8 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
assert (SHQ4 : ro_cells asegs m (bse / 8 + A_SB) [C1 (Z_to_bv 8 0)]).
{ replace (bse / 8) with (q / 8 + 4 * Z.of_nat depth) by (subst bse; rewrite div8_add_mul32 by lia; lia). exact SHQ. }
pose proof (munch_refl [(bse, bse + 32)] m) as MU.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 1 HP INtk ltac:(lia)) as SHT1.
replace (tk / 8 + 1 + A_SB) with (tk / 8 + 2147450881) in SHT1 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT1c & SEPT1q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 1 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT1t & _).
cbn [hl_sb A4L] in SEPT1c, SEPT1q, SEPT1t. assert (EQx : tk / 8 + A_SB + 1 = tk / 8 + 2147450881) by (unfold A_SB; lia). rewrite EQx in SEPT1c, SEPT1q, SEPT1t. clear EQx.
destruct PB as (buf & bpos & cap & pre & post & Epbs & Lpre & CORE1). destruct CORE1 as (Hbp & Hcap & Hlen & PBC & BUFC).
assert (INpb : In (pb, PB_SZ) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA, tstate_blocks, ts0; cbn [t_pbs]; rewrite Epbs; apply in_or_app; left; left; reflexivity).
assert (INbuf : In (buf, cap) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA, tstate_blocks, ts0; cbn [t_pbs]; rewrite Epbs; apply in_or_app; left; right; left; reflexivity).
assert (CAP32 : 32 <= cap) by (destruct BK as (_ & _ & _ & (X & _) & _); unfold ts0 in X; cbn [t_pbs] in X; rewrite Epbs in X; unfold pb_capA in X; cbn [nth snd] in X; exact X).
blk_factsA A4L HIx HP pb 16 Hpal Hplo Hphi Himg_p.
blk_factsA A4L HIx HP buf cap Hbal Hblo Hbhi Himg_b.
pose proof (blk_granA HIx _ _ _ _ _ _ _ pb 16 0 HP INpb ltac:(lia) ltac:(lia)) as SHP0.
replace (pb / 8 + 0 + A_SB) with (pb / 8 + 2147450880) in SHP0 by (unfold A_SB; lia).
pose proof (blk_granA HIx _ _ _ _ _ _ _ pb 16 1 HP INpb ltac:(lia) ltac:(lia)) as SHP1.
replace (pb / 8 + 1 + A_SB) with (pb / 8 + 2147450881) in SHP1 by (unfold A_SB; lia).
pose proof (blk_granA HIx _ _ _ _ _ _ _ buf cap 0 HP INbuf ltac:(lia) ltac:(lia)) as SHB0.
replace (buf / 8 + 0 + A_SB) with (buf / 8 + 2147450880) in SHB0 by (unfold A_SB; lia).
pose proof (rw_cells_bytes_at' _ _ _ _ BUFC) as BUFB. cbn [cells_bytes cbytes] in BUFB. rewrite app_nil_r in BUFB.
assert (Ech : exists ch tl, pre ++ [Z_to_bv 8 0] ++ post = ch :: tl) by (destruct pre as [|c' s']; cbn; eauto).
destruct Ech as (ch & tl & Ech). rewrite Ech in BUFB.
pose proof (payload_byteA m buf (ch :: tl) 0 ch BUFB eq_refl ltac:(lia)) as RDB. rewrite Z.add_0_r in RDB.
pose proof (bv_unsigned_in_range 8 ch) as CHR; unfold bv_modulus in CHR; cbn in CHR.
pose proof (pinfdbl_roA m MI) as PINF. pose proof (pinf2dbl_roA m MI) as PINF2. pose proof (ninfdbl_roA m MI) as NINF.
unfold APE_BREAK, APE_REDO, APE_OUT, APE_ERRMEM, APE_ERRST, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t. stash Himg_q. stash Himg_p. stash Himg_b. stash Kredo. stash Kerr16. stash INV0. stash BUFC. stash BUFB.
clear REST LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin SHT SHQ4 SHQ Ld Hdtq TSK SEPT1c SEPT1q SEPT1t.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_chkM 1.
step.
step.
asan_chkA.
step.
norm_sx32.
step.
destruct (Z.eq_dec bpos 0) as [B0 | B0].
- if_truex.
step.
step.
evt_done5. unstash INV0. unstash Kredo. unstash Kerr16.
eapply (inf_ctor_A (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 l cb nb pj sv errv T kP v2 ra2 nB);
[ exact STC | exact BSL | exact INV0 | exact PBK | exact BK | exact Hl | exact Hst | exact S0V | exact RAV | exact HV | exact UWK
| unfold dbl_special; rewrite reg_get_set_same_u by (vm_compute; reflexivity); apply Z.leb_le; vm_compute; reflexivity
| intros m' md' A' B' errv' r BS gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc' LEN3 JF INV' PBK' BK' FS' FRM';
eapply (Kredo m' md' A' B' errv' r BS); [exact LEN3 | exact JF | exact INV' | exact PBK' | exact BK' | eapply fsaved_trans; [apply fsaved_set10 | exact FS'] | exact FRM']
| intros m' md' A' B' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc' INVW' FS' FRM';
eapply (Kerr16 m' md' A' B' errv'); [exact INVW' | eapply fsaved_trans; [apply fsaved_set10 | exact FS'] | exact FRM'] ].
- if_falsex.
asan_chkA.
step.
asan_chkA.
step.
change (zxb ch) with (Z_to_bv 64 (bv_unsigned ch)).
step. step. step. step. step. step.
destruct (Z.eq_dec (bv_unsigned ch) 45) as [E45 | N45].
+
replace (Z_to_bv 64 (142376 + bv_unsigned (v_sltiu (Z_to_bv 64 (bv_unsigned ch + -45)) 1) ≪ 3)) with (Z_to_bv 64 142384)
by (rewrite E45; apply bv_eq; vm_compute; reflexivity).
step.
step.
evt_done5. unstash INV0. unstash Kredo. unstash Kerr16.
eapply (inf_ctor_A (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 l cb nb pj sv errv T kP v2 ra2 nB);
[ exact STC | exact BSL | exact INV0 | exact PBK | exact BK | exact Hl | exact Hst | exact S0V | exact RAV | exact HV | exact UWK
| unfold dbl_special; rewrite reg_get_set_same_u by (vm_compute; reflexivity); apply Z.leb_le; vm_compute; reflexivity
| intros m' md' A' B' errv' r BS gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc' LEN3 JF INV' PBK' BK' FS' FRM';
eapply (Kredo m' md' A' B' errv' r BS); [exact LEN3 | exact JF | exact INV' | exact PBK' | exact BK' | eapply fsaved_trans; [apply fsaved_set10 | exact FS'] | exact FRM']
| intros m' md' A' B' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc' INVW' FS' FRM';
eapply (Kerr16 m' md' A' B' errv'); [exact INVW' | eapply fsaved_trans; [apply fsaved_set10 | exact FS'] | exact FRM'] ].
+
replace (Z_to_bv 64 (142376 + bv_unsigned (v_sltiu (Z_to_bv 64 (bv_unsigned ch + -45)) 1) ≪ 3)) with (Z_to_bv 64 142376).
2:{ unfold v_sltiu. change (bv_wrap 64 1) with 1.
replace (bv_unsigned (Z_to_bv 64 (bv_unsigned ch + -45)) <? 1) with false; [rewrite (unsigned_lit 0) by lia; reflexivity|].
symmetry. apply Z.ltb_ge. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616.
destruct (Z.lt_ge_cases (bv_unsigned ch) 45).
* replace (bv_unsigned ch + -45) with ((bv_unsigned ch + -45 + 18446744073709551616) + (-1) * 18446744073709551616) by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
* rewrite Z.mod_small by lia. lia. }
step.
step.
evt_done5. unstash INV0. unstash Kredo. unstash Kerr16.
eapply (inf_ctor_A (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 l cb nb pj sv errv T kP v2 ra2 nB);
[ exact STC | exact BSL | exact INV0 | exact PBK | exact BK | exact Hl | exact Hst | exact S0V | exact RAV | exact HV | exact UWK
| unfold dbl_special; rewrite reg_get_set_same_u by (vm_compute; reflexivity); apply Z.leb_le; vm_compute; reflexivity
| intros m' md' A' B' errv' r BS gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc' LEN3 JF INV' PBK' BK' FS' FRM';
eapply (Kredo m' md' A' B' errv' r BS); [exact LEN3 | exact JF | exact INV' | exact PBK' | exact BK' | eapply fsaved_trans; [apply fsaved_set10 | exact FS'] | exact FRM']
| intros m' md' A' B' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc' INVW' FS' FRM';
eapply (Kerr16 m' md' A' B' errv'); [exact INVW' | eapply fsaved_trans; [apply fsaved_set10 | exact FS'] | exact FRM'] ].
Qed.

Lemma inf_loop_A :
forall (n : nat) (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel) (co00 k0 i kP : Z)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(gp t0 t1 t2 a0 a1 a7 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> pf_fl pf = 0 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOKat m ts kP -> CSTR_OK pf payload ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_inf ->
t_co ts = co00 + i -> 0 <= co00 -> 0 <= i -> t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->
SPV (t_x ts) = k0 + i -> 0 <= k0 -> k0 + i <= 7 -> 8 - (k0 + i) <= Z.of_nat n ->

(forall m' co' cb' stq a0' a1' a2' a3' a4' a5' a6' t0' t1',
t_co ts < co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_set_x ts co' (TS (ts_isd (t_x ts)) stq (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) cb' nb pj sv errv ->
PBOKat m' (ts_set_x ts co' (TS (ts_isd (t_x ts)) stq (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) kP ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x94bd8 co' gp t0' t1' t2 a0' a1' a2' a3' a4' a5' a6' a7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m')) ->

(forall m' co' cb' stq (e : Z) x1' a1' a2' a3' a4' a5' a6' t0' t1' s11',
e = 4 \/ e = 1 -> t_co ts <= co' <= pf_len pf ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_set_x ts co' (TS (ts_isd (t_x ts)) stq (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) cb' nb pj sv errv ->
AJ5 A4L HIx A T md
(pe_msO asegs pf pa APE_ERRST x1' gp t0' t1' t2 (Z_to_bv 64 e) a1' a2' a3' a4' a5' a6' a7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 q) s11'
(Z_to_bv 64 (pa_F pa + 64)) (Z_to_bv 64 (pf_lenr pf)) F fc m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x94440 co00 gp t0 t1 t2 a0 a1 (Z_to_bv 64 (pf_tk pf / 8 + 2147450883)) (Z_to_bv 64 i) (Z_to_bv 64 (143552 + k0)) (Z_to_bv 64 (143584 + k0))
(Z_to_bv 64 (k0 + i + 1)) a7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
induction n as [|n IH]; intros until fc; intros STC FL0 INV PBK CSTR Hl Hst Eco Hco00 Hi Hco Hc ESP Hk0 Hk7 Hn Kfin Kerr.
{ exfalso. cbn in Hn. lia. }
pose proof INV as INV0.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *. subst fl.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold ts_set_x in Kfin, Kerr.
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in Kfin, Kerr.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH). unfold pe_msA, pe_msO in *.
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold pe_savedA_cells in SAVED. unfold ff_cellsA in FF. unfold ffsh_cells, FSH0 in FSH. cbn [map] in FSH.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
unfold SPV in ESP. cbn [ts_stpos] in ESP.
set (k := k0 + i) in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd 0) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd 0) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 3 HP INtk ltac:(lia)) as SHT3.
replace (tk / 8 + 3 + A_SB) with (tk / 8 + 2147450883) in SHT3 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 3 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT3c & SEPT3q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 3 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT3t & _).
cbn [hl_sb A4L] in SEPT3c, SEPT3q, SEPT3t. assert (EQx : tk / 8 + A_SB + 3 = tk / 8 + 2147450883) by (unfold A_SB; lia). rewrite EQx in SEPT3c, SEPT3q, SEPT3t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + 2147450884) in SHT4 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT4c & SEPT4q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT4t & _).
cbn [hl_sb A4L] in SEPT4c, SEPT4q, SEPT4t. assert (EQx : tk / 8 + A_SB + 4 = tk / 8 + 2147450884) by (unfold A_SB; lia). rewrite EQx in SEPT4c, SEPT4q, SEPT4t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 8 HP INtk ltac:(lia)) as SHT8.
replace (tk / 8 + 8 + A_SB) with (tk / 8 + 2147450888) in SHT8 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 8 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT8c & SEPT8q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 8 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT8t & _).
cbn [hl_sb A4L] in SEPT8c, SEPT8q, SEPT8t. assert (EQx : tk / 8 + A_SB + 8 = tk / 8 + 2147450888) by (unfold A_SB; lia). rewrite EQx in SEPT8c, SEPT8q, SEPT8t. clear EQx.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (TSK depth l Hl) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld. unfold srec_cells in Ld. rewrite Hst in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
shq_facts HP INq INtk q mxd tk 0 0 SHQ0 SEPQ0c SEPQ0q SEPQ0t.
replace (q / 8 + 4 * 0 + 0 + A_SB) with (q / 8 + 2147450880) in SHQ0 by (unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * 0 + 0) = q / 8 + 2147450880) by (unfold A_SB; lia). rewrite EQx in SEPQ0c, SEPQ0q, SEPQ0t. clear EQx.
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
destruct SBin as [L00 | PL]; [exfalso; lia|].

destruct (nth_error infstrA (Z.to_nat k)) as [ib|] eqn:Hib; [| exfalso; apply nth_error_None in Hib; change (length infstrA) with 9%nat in Hib; lia].
destruct (nth_error invstrA (Z.to_nat k)) as [vb|] eqn:Hvb; [| exfalso; apply nth_error_None in Hvb; change (length invstrA) with 9%nat in Hvb; lia].
pose proof (payload_byteA m 143552 infstrA k ib (infstr_atA m MI) Hib ltac:(lia)) as RDI.
pose proof (payload_byteA m 143584 invstrA k vb (invstr_atA m MI) Hvb ltac:(lia)) as RDV.
pose proof (bv_unsigned_in_range 8 ib) as IBR; unfold bv_modulus in IBR; cbn in IBR.
pose proof (bv_unsigned_in_range 8 vb) as VBR; unfold bv_modulus in VBR; cbn in VBR.
pose proof (heapA_shadow_img A4L HIx _ _ _ _ _ _ _ 17944 HP ltac:(cbn; lia) ltac:(cbn; lia)) as SHI1. cbn [hl_sb A4L] in SHI1.
replace (img_shadow_val (hl_reg_globals A4L) 17944) with 0 in SHI1 by (vm_compute; reflexivity). apply ro_C1_of_bytes_at in SHI1. change (17944 + A_SB) with 2147468824 in SHI1.
pose proof (heapA_shadow_img A4L HIx _ _ _ _ _ _ _ 17948 HP ltac:(cbn; lia) ltac:(cbn; lia)) as SHI2. cbn [hl_sb A4L] in SHI2.
replace (img_shadow_val (hl_reg_globals A4L) 17948) with 0 in SHI2 by (vm_compute; reflexivity). apply ro_C1_of_bytes_at in SHI2. change (17948 + A_SB) with 2147468828 in SHI2.

pose proof (payload_byteA _ _ _ _ _ STR Hc ltac:(lia)) as RDC0.
pose proof (payload_shadow_pe HIx (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) LB0 FRS _ _ _ _ _ _ _ co HP
ltac:(intros bb Hbb; unfold pe_blocksA; apply in_or_app; right; right; right; exact Hbb) PL ltac:(cbn [pf_len]; lia)) as (v0 & SHP0 & Hv0).
cbn [pf_sb] in SHP0, Hv0, RDC0. unfold A_SB in SHP0.
assert (SBc : sb + len <= alloc_ceiling).
{ destruct PL as [([b0 n0] & Hb0 & Hb1 & Hb2) | (Fh & kh & HFh & HF1 & HF2 & _)]; cbn [pf_sb pf_len pa_sp0 blk_addr blk_size fst snd] in *.
- pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ b0 n0 HP ltac:(apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; right; right; exact Hb0)) as (_ & _ & _ & Hbhi & _). lia.
- pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP (or_intror HFh)) as (_ & _ & _ & HFhc & _). lia. }
assert (SBhi : sb + len <= 2^47) by lia.
unfold APE_ERRST in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8, A_SB in *.
pose proof (munch_refl [(tk, tk + 72); (Ff + 64, Ff + 65)] m) as MU.
assert (HW : Forall (pe_wtfA (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl)) [(tk, tk + 72); (Ff + 64, Ff + 65)]).
{ apply Forall_cons; [left; cbn [fst snd pf_tk]; lia |]. apply Forall_cons; [| apply Forall_nil]. right; right; left. cbn [fst snd pa_F]. lia. }
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_FF_T : csep Ff 248 tk (Z.of_nat 72)) by (unfold csep; clear - DFt; lia).
assert (cs_T_FF : csep tk 72 Ff (Z.of_nat 248)) by (unfold csep; clear - DFt; lia).
assert (cs_Q0_T : csep (q / 8 + 2147450880) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPQ0t; lia).
assert (cs_T4_T : csep (tk / 8 + 2147450884) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPT4t; lia).
assert (cs_T8_T : csep (tk / 8 + 2147450888) 1 tk (Z.of_nat 72)) by (unfold csep; clear - SEPT8t; lia).
clear LV OBJ HPR Hdtq SEPQ0c SEPQ0q SEPQ0t SEPT3c SEPT3q SEPT3t SEPT4c SEPT4q SEPT4t SEPT8c SEPT8q SEPT8t.
stash PB. stash TSK. stash Hv0. stash SLOTS. stash GAP. stash SAVED. stash FSH. stash DSt. stash DSF. stash DFt.
stash IH. stash Kfin. stash Kerr. stash INV0. stash REST. stash FR0. stash PBK. stash SBc. stash SBhi. stash Hc. stash STR. stash HW. stash Hib. stash Hvb. stash RDV. stash SHI2. stash Himg_t. stash Himg_q.
reenterA asegs A4L HIx asegs_wx HP.
step.
replace (sb + co00 + i) with (sb + co) by lia.
step.
step.
sh_norm.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc None ?mm ?rom) =>
assert (JOIN1 : forall a1x t0x, evt asegs (AJ5e A4L HIx A T md) (MS (bvmap_set 11 a1x (bvmap_set 5 t0x R)) FF (Z_to_bv 64 0x94454) fcc None mm rom)) end.
2:{ unstash Hv0. destruct Hv0 as [-> | [Hv8 Hvlt]].
- step. rewrite ?sxb_zero. step. if_false. apply JOIN1.
- step. rewrite (sxb_small v0) by lia. step. if_truex.
step.
unstash SBhi. rewrite (unsigned_lit (sb + co)) by lia. rewrite (land7_mod8 (sb + co)) by lia.
pose proof (Z.mod_pos_bound (sb + co) 8 ltac:(lia)) as R8. remember ((sb + co) mod 8) as r8 eqn:Er8 in *.
step.
if_truex. apply JOIN1. }
intros a1x t0x. clear SHP0.
step.
replace (143552 + k0 + i) with (143552 + k) by (unfold k; lia).
step. step.
rewrite (unsigned_lit (143552 + k)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
replace ((143552 + k) / 8) with 17944 by (clear - Hk0 Hi Hk7; unfold k in *; Z.div_mod_to_equations; lia). change (17944 + 2147450880) with 2147468824.
step.
rewrite ?sxb_zero.
step.
change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)).
step.
if_false.
step.
change (zxb ib) with (Z_to_bv 64 (bv_unsigned ib)).
clear RDI RDC0 SHI1.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc None ?mm ?rom) =>
assert (MATCHJ : forall a1x t1x, bv_unsigned cb <> 0 -> evt asegs (AJ5e A4L HIx A T md) (MS (bvmap_set 11 a1x (bvmap_set 6 t1x R)) FF (Z_to_bv 64 0x944ac) fcc None mm rom)) end.
2:{ step.
destruct (Z.eq_dec (bv_unsigned cb) (bv_unsigned ib)) as [E1 | N1].
{ if_truex. apply MATCHJ. rewrite E1. unstash Hib. exact (infstrA_nz _ _ Hib ltac:(lia)). }
if_falsex.
asan_rechkA.
pose proof (tok_flags_byteA mxd 0 m tk pb (Z.of_nat depth) q (TS isd stpos (Z_to_bv 64 co) err ucs high quote) TOK) as RDF.
step.
rewrite ?zxb_zero. clear RDF.
step.
step.
if_true.
step.
replace (143584 + k0 + i) with (143584 + k) by (unfold k; lia).
step. step.
rewrite (unsigned_lit (143584 + k)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
replace ((143584 + k) / 8) with 17948 by (clear - Hk0 Hi Hk7; unfold k in *; Z.div_mod_to_equations; lia). change (17948 + 2147450880) with 2147468828.
unstash SHI2. unstash RDV.
step.
rewrite ?sxb_zero.
step.
if_false.
step.
change (zxb vb) with (Z_to_bv 64 (bv_unsigned vb)).
step.
destruct (Z.eq_dec (bv_unsigned cb) (bv_unsigned vb)) as [E2 | N2].
{ if_truex. apply MATCHJ. rewrite E2. unstash Hvb. exact (invstrA_nz _ _ Hvb ltac:(lia)). }
if_falsex.
step.
unstash SLOTS.
step.
asan_rechkA.
step.
step.
evt_done5. unstash Kerr. unstash INV0.
eapply (Kerr m co cb stpos 4); [left; reflexivity | lia | exact INV0]. }
intros a1y t1y Hnz0.

unstash SLOTS.
asan_rechkA.
step.
step.
asan_rechkA.
step.
norm_sx32.
step.
norm_w32.
step.
step.
unstash Hc. unstash INV0. unstash REST. unstash FR0. unstash HW.
destruct (peek_cases (PEF tk oldl newl len lenr sb spf pmd mxd 0) payload co cb LENR CSTR (proj1 RR) ltac:(cbn [pf_len pf_mxd]; lia) ltac:(cbn [pf_len pf_mxd]; lia) Hc Hnz0)
as [[Elenr Heof] | [Hne Hmore]]; cbn [pf_len pf_lenr pf_mxd] in *.
{
subst lenr. rewrite Heof. if_false.
step.
lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc None ?mm ?rom) =>
assert (EOFJ : forall a0x, evt asegs (AJ5e A4L HIx A T md) (MS (bvmap_set 10 a0x R) FF (Z_to_bv 64 0x97e94) fcc None mm rom)) end.
2:{ step.
destruct depth as [|dp].
- if_false.
asan_chkA.
subst bse. replace (q + 32 * Z.of_nat 0) with q in * by lia.
step.
norm_sx32.
step.
if_truex. apply EOFJ.
- if_truex. apply EOFJ. }
intros a0x.
step.
asan_rechkA.
step.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, FFc : rw_cells asegs mc Ff _ |- _ =>
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len len sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj sv)
by (eapply (pe_frameA_scan HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact FR0 | exact MUc | exact WMc | exact FFc]);
evt_done5;
destruct (PE_INV_A_tokw HIx GA GA_outside (PEF tk oldl newl len len sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv _ (co + 1) (TS isd (Z_to_bv 64 (k + 1)) (Z_to_bv 64 (co + 1)) err ucs high quote) cb nb STC INV0 MUc WMc MIc HW TOKc FRc
ltac:(cbn [pf_len]; lia) eq_refl) as [INV1 PBK1]
end end.
unstash Kerr. eapply (Kerr _ (co + 1) cb (Z_to_bv 64 (k + 1)) 1); [right; reflexivity | cbn [pf_len]; lia | exact INV1]. }
if_truex.

destruct (nth_error payload (Z.to_nat (co + 1))) as [c'|] eqn:Hc'; [| apply nth_error_None in Hc'; lia].
pose proof (bv_unsigned_in_range 8 c') as CBR'; unfold bv_modulus in CBR'; cbn in CBR'.
pose proof (payload_shadow_pe HIx (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) LB0 FRS _ _ _ _ _ _ _ (co + 1) HP
ltac:(intros bb Hbb; unfold pe_blocksA; apply in_or_app; right; right; right; exact Hbb) PL ltac:(cbn [pf_len]; lia)) as (v1 & SHP1 & Hv1).
cbn [pf_sb] in SHP1, Hv1. unfold A_SB in SHP1. replace (sb + (co + 1)) with (sb + co + 1) in SHP1, Hv1 by lia.
unstash SBhi. unstash DSF. unstash SBc.
pose proof (shadow_blk_apart HIx _ _ _ _ _ _ _ _ _ (sb + co + 1) 1 HP INtk' ltac:(lia) ltac:(lia) ltac:(lia)) as DSPt. unfold shA, A_SB in DSPt.
assert (SHPF : (sb + co + 1) / 8 + 2147450880 + 1 <= Ff \/ Ff + 256 <= (sb + co + 1) / 8 + 2147450880) by (clear - DSF SBhi SB0 CO Hmore; Z.div_mod_to_equations; lia).
lazymatch goal with MUc : munch _ m ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
apply (fun H => ro_cells_transport asegs _ m mc _ _ H MUc) in SHP1; [| cbn [disjoint_from fst snd cells_size csize Z.of_nat]; clear - DSPt SHPF; lia] end.
assert (LE1 : le1 (zxb c') = [c']).
{ unfold le1, zxb. cbn [Z_to_le_bytes pf_mxd]. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256%Z. change (bv_modulus 64) with 18446744073709551616%Z. Z.div_mod_to_equations. nia. }
stash DSF. stash SBc. stash DSPt. stash SHPF. stash Hv1. stash LE1. stash INV0. stash REST. stash FR0. stash HW. stash Hc. stash Hc'.
asan_rechkA.
lazymatch goal with TOKc : rw_cells asegs ?mc tk _ |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (tok_flags_byteA mxd 0 mc tk pb (Z.of_nat depth) q (TS isd (Z_to_bv 64 (k + 1)) (Z_to_bv 64 (co + 1)) err ucs high quote) TOKc) as RDF end.
step.
rewrite ?zxb_zero. clear RDF.
step.
step.
if_true.
step.
step. step.
sh_norm.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc None ?mm ?rom) =>
assert (JOIN2 : forall t0y t1z, evt asegs (AJ5e A4L HIx A T md) (MS (bvmap_set 5 t0y (bvmap_set 6 t1z R)) FF (Z_to_bv 64 0x9453c) fcc None mm rom)) end.
2:{ unstash Hv1. destruct Hv1 as [-> | [Hv8 Hvlt]].
- step. rewrite ?sxb_zero. step. if_false. apply JOIN2.
- step. rewrite (sxb_small v1) by lia. step. if_truex.
step.
rewrite (unsigned_lit (sb + co + 1)) by lia. rewrite (land7_mod8 (sb + co + 1)) by lia.
pose proof (Z.mod_pos_bound (sb + co + 1) 8 ltac:(lia)) as R8. remember ((sb + co + 1) mod 8) as r8 eqn:Er8 in *.
step.
if_truex. apply JOIN2. }
intros t0y t1z. clear SHP1.
unstash REST. unstash STR. unstash HW. unstash Hc'.
lazymatch goal with MUc : munch _ m ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (payload_privateA HIx _ _ _ _ _ _ _ ts0 _ _ _ _ _ _ _ STC (proj1 REST) STR PLEN (or_intror PL) MUc (pe_wtfA_private _ _ q pbs _ HW)) as STRc end.
cbn [pf_sb] in STRc.
pose proof (payload_byteA _ _ _ _ _ STRc Hc' ltac:(lia)) as RDC. replace (sb + (co + 1)) with (sb + co + 1) in RDC by lia.
stash REST. stash STR. stash HW. clear STRc.
step.
change (zxb c') with (Z_to_bv 64 (bv_unsigned c')). clear RDC.
step.
norm_w32.
clear SHT3 SHT4 SHT8 SHQ0 Ld.
unstash LE1.
step.
replace (le1 (Z_to_bv 64 (bv_unsigned c'))) with [c'] by (rewrite <- LE1; reflexivity). mem_after_store.
step. step.
step.
unstash REST. unstash HW. unstash INV0. unstash FR0. unstash PBK.
destruct (Z.eq_dec k 7) as [E7 | N7].
-
if_falsex.
step.
step.
replace (sb + co00 + (i + 1)) with (sb + (co + 1)) by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, FFc : rw_cells asegs mc Ff _ |- _ =>
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) c' nb pj sv)
by (eapply (pe_frameA_scan HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact FR0 | exact MUc | exact WMc | exact FFc]);
evt_done5;
destruct (PE_INV_A_tokw HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv _ (co + 1) (TS isd (Z_to_bv 64 (k + 1)) (Z_to_bv 64 (co + 1)) err ucs high quote) c' nb STC INV0 MUc WMc MIc HW TOKc FRc
ltac:(cbn [pf_len]; lia) eq_refl) as [INV1 PBK1]
end end.
unstash Kfin. eapply (Kfin _ (co + 1) c' (Z_to_bv 64 (k + 1))); [lia | exact Hc' | exact INV1 | exact (PBK1 kP PBK)].
- if_truex.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, FFc : rw_cells asegs mc Ff _ |- _ =>
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) c' nb pj sv)
by (eapply (pe_frameA_scan HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact FR0 | exact MUc | exact WMc | exact FFc]);
evt_done5;
destruct (PE_INV_A_tokw HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv _ (co + 1) (TS isd (Z_to_bv 64 (k + 1)) (Z_to_bv 64 (co + 1)) err ucs high quote) c' nb STC INV0 MUc WMc MIc HW TOKc FRc
ltac:(cbn [pf_len]; lia) eq_refl) as [INV1 PBK1]
end end.
unstash IH. unstash Kfin. unstash Kerr.
replace (Z_to_bv 64 (k + 2)) with (Z_to_bv 64 (k0 + (i + 1) + 1)) by (f_equal; unfold k; lia).
eapply (IH (PEF tk oldl newl len lenr sb spf pmd mxd 0) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md A B (ts_set_x ts0 (co + 1) (TS isd (Z_to_bv 64 (k + 1)) (Z_to_bv 64 (co + 1)) err ucs high quote)) l co00 k0 (i + 1) kP c' nb pj sv errv T);
[ exact STC | reflexivity | exact INV1 | exact (PBK1 kP PBK) | exact CSTR | exact Hl | exact Hst
| cbn [t_co ts_set_x]; lia | exact Hco00 | lia | cbn [t_co ts_set_x pf_len]; lia | cbn [t_co ts_set_x]; exact Hc'
| unfold SPV; cbn [t_x ts_set_x ts_stpos]; rewrite spv_lit by (unfold k in *; lia); unfold k; lia | exact Hk0 | unfold k in *; lia | unfold k in *; lia
| intros m' co' cb' stq a0' a1' a2' a3' a4' a5' a6' t0' t1' Hco' Hcb' INV' PBK'; cbn [t_co ts_set_x pf_len] in Hco'; eapply (Kfin m' co' cb' stq); [lia | exact Hcb' | exact INV' | exact PBK']
| intros m' co' cb' stq e x1' a1' a2' a3' a4' a5' a6' t0' t1' s11' He Hco' INV'; cbn [t_co ts_set_x pf_len] in Hco'; eapply (Kerr m' co' cb' stq e); [exact He | lia | exact INV'] ].
Qed.

Lemma inf_entry_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(gp t0 t1 t2 a3 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_inf -> SPV (t_x ts) <= t_co ts ->

(forall a0' a1' a2' a3' a6',
7 < SPV (t_x ts) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x94bd8 (t_co ts) gp t0 t1 t2 a0' a1' a2' a3' (Z_to_bv 64 APE_JTAB) a5 a6' a7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m)) ->

(forall a0' a1' a7',
SPV (t_x ts) <= 7 ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa 0x94440 (t_co ts) gp t0 t1 t2 a0' a1' (Z_to_bv 64 (pf_tk pf / 8 + 2147450883)) (Z_to_bv 64 0) (Z_to_bv 64 (143552 + SPV (t_x ts))) (Z_to_bv 64 (143584 + SPV (t_x ts)))
(Z_to_bv 64 (SPV (t_x ts) + 0 + 1)) a7' (Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m)) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA ST_inf) (t_co ts) gp t0 t1 t2
(Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l))
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3 (Z_to_bv 64 APE_JTAB) a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC INV Hl Hst SPB Kpick Kloop. pose proof INV as INV0. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
unfold pe_msA in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
pose proof (TSK depth l Hl) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld. unfold srec_cells in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd (Z.of_nat depth) 0 HP INq ltac:(lia) ltac:(lia)) as SHQ.
replace (q / 8 + 4 * Z.of_nat depth + 0 + A_SB) with (q / 8 + 4 * Z.of_nat depth + A_SB) in SHQ by lia.
assert (Hb8 : bse mod 8 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
assert (SHQ4 : ro_cells asegs m (bse / 8 + A_SB) [C1 (Z_to_bv 8 0)]).
{ replace (bse / 8) with (q / 8 + 4 * Z.of_nat depth) by (subst bse; rewrite div8_add_mul32 by lia; lia). exact SHQ. }
pose proof (munch_refl [(bse, bse + 32)] m) as MU.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 3 HP INtk ltac:(lia)) as SHT3.
replace (tk / 8 + 3 + A_SB) with (tk / 8 + 2147450883) in SHT3 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 3 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT3c & SEPT3q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 3 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT3t & _).
cbn [hl_sb A4L] in SEPT3c, SEPT3q, SEPT3t. assert (EQx : tk / 8 + A_SB + 3 = tk / 8 + 2147450883) by (unfold A_SB; lia). rewrite EQx in SEPT3c, SEPT3q, SEPT3t. clear EQx.
unfold APE_BREAK, APE_REDO, APE_OUT, APE_ERRMEM, APE_ERRST, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
unfold SPV in *. cbn [t_x ts_stpos] in *.
assert (SPR : 0 <= bv_unsigned stpos mod 2^32 < 2^32) by (apply Z.mod_pos_bound; lia).
set (sp := bv_unsigned stpos mod 2^32) in *.
stash Himg_t. stash Himg_q. stash Kpick. stash Kloop. clear PB REST LV OBJ HPR BUD GAP SAVED FSH FF STR ERR SBin SHT SHQ4 SHQ Ld Hdtq TSK SEPT3c SEPT3q SEPT3t.
reenterA asegs A4L HIx asegs_wx HP. rewrite Hst. unfold ST_inf. cbn [pe_jtA].
step.
asan_chkA.
step.
rewrite (sx32_small_mod stpos) by (fold sp; lia). fold sp.
step.
step.
destruct (Z_lt_dec 7 sp) as [G7 | L7].
- if_truex. evt_done5. unstash Kpick. eapply (Kpick _ _ _ _ _ G7).
- if_falsex.
step.
step.
step. step.
step. step.
step. step.
step.
replace (Z_to_bv 64 (sp + 143552)) with (Z_to_bv 64 (143552 + sp)) by (f_equal; lia).
replace (Z_to_bv 64 (sp + 143584)) with (Z_to_bv 64 (143584 + sp)) by (f_equal; lia).
replace (Z_to_bv 64 (sp + 1)) with (Z_to_bv 64 (sp + 0 + 1)) by (f_equal; lia).
evt_done5. unstash Kloop. eapply (Kloop _ _ _ ltac:(lia)).
Qed.

Lemma seg_inf_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (b v2 ra2 : Z) (nB : nat)
(gp t0 t1 t2 a3 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa -> pf_fl pf = 0 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOKat m ts b -> BOK pf pa ts B (S (Z.to_nat 2816 + nB)) -> CSTR_OK pf payload ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_inf ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb -> SPV (t_x ts) <= t_co ts ->
pe_s0 sv = Z_to_bv 64 v2 -> pe_ra sv = Z_to_bv 64 ra2 ->
(v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= v2) /\ 0 <= v2 < 2^64 ->
uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9d9cc) (UWfp ra2 v2) ->

(forall m' md' A' B' errv' co' cb' stq r BS gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
t_co ts <= co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' -> (length BS <= 3)%nat -> jfresh (Sdouble false) BS 9 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_lvl (ts_set_x ts co' (TS (ts_isd (t_x ts)) stq (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) (TL ST_eatws ST_finish r (Some (Sdouble false)) BS 0 [])) cb' nb pj sv errv' ->
PBOKat m' (ts_lvl (ts_set_x ts co' (TS (ts_isd (t_x ts)) stq (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) (TL ST_eatws ST_finish r (Some (Sdouble false)) BS 0 [])) b ->
BOK pf pa (ts_lvl (ts_set_x ts co' (TS (ts_isd (t_x ts)) stq (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) (TL ST_eatws ST_finish r (Some (Sdouble false)) BS 0 [])) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_REDO co' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m')) ->

(forall m' md' A' B' errv' co' cb' stq x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc',
t_co ts <= co' < pf_len pf ->
PE_INVW_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_set_x ts co' (TS (ts_isd (t_x ts)) stq (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) [] cb' nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_ERRMEM x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' (Z_to_bv 64 (pf_tk pf + 56)) s11' t4' t6' F' fc' m')) ->

(forall m' co' cb' stq (e : Z) x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s5' s7' s10' s11' t4' t6',
e = 4 \/ e = 1 -> t_co ts <= co' <= pf_len pf ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_set_x ts co' (TS (ts_isd (t_x ts)) stq (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) cb' nb pj sv errv ->
AJ5 A4L HIx A T md
(pe_msO asegs pf pa APE_ERRST x1' gp' t0' t1' t2' (Z_to_bv 64 e) a1' a2' a3' a4' a5' a6' a7' s5' s7' s10' s11' t4' t6' F fc m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA ST_inf) (t_co ts) gp t0 t1 t2
(Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l))
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3 (Z_to_bv 64 APE_JTAB) a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC BSL FL0 INV PBK BK CSTR Hl Hst Hco Hc SPB S0V RAV HV UWK Kredo Kerr16 Kerr.
assert (SP0' : 0 <= SPV (t_x ts)) by (unfold SPV; apply Z.mod_pos_bound; lia).
pose proof INV as [(_ & _ & CO & CHOFF & _) _].
assert (Ets : ts_set_x ts (t_co ts) (TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (Z_to_bv 64 (t_co ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts))) = ts).
{ destruct ts as [depth levels co pb pbs x obj objs objbs]. destruct x as [isd stpos choff err ucs high quote]. unfold ts_set_x; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in *.
rewrite <- CHOFF. reflexivity. }

assert (PICK : forall m1 co' cb' stq (gp1 t0_1 t1_1 t2_1 a0_1 a1_1 a2_1 a3_1 a4_1 a5_1 a6_1 a7_1 s5_1 s10_1 : word),
t_co ts <= co' < pf_len pf -> nth_error payload (Z.to_nat co') = Some cb' ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m1 md A B (ts_set_x ts co' (TS (ts_isd (t_x ts)) stq (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) cb' nb pj sv errv -> PBOKat m1 (ts_set_x ts co' (TS (ts_isd (t_x ts)) stq (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) b ->
AJ5 A4L HIx A T md (pe_msA asegs pf pa 0x94bd8 co' gp1 t0_1 t1_1 t2_1 a0_1 a1_1 a2_1 a3_1 a4_1 a5_1 a6_1 a7_1 s5_1 s10_1 (Z_to_bv 64 (pa_F pa + 64)) F fc m1)).
{ intros m1 co' cb' stq gp1 t0_1 t1_1 t2_1 a0_1 a1_1 a2_1 a3_1 a4_1 a5_1 a6_1 a7_1 s5_1 s10_1 Hco' Hcb' INV1 PBK1.
eapply (inf_pick_A pf pa q LB0 LM FRS payload me lo m1 md A B (ts_set_x ts co' (TS (ts_isd (t_x ts)) stq (Z_to_bv 64 co') (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))) l cb' nb pj sv errv T b v2 ra2 nB gp1 t0_1 t1_1 t2_1 a0_1 a1_1 a2_1 a3_1 a4_1 a5_1 a6_1 a7_1 s5_1 s10_1 F fc
STC BSL INV1 PBK1 (BOK_set_x pf pa ts B _ co' _ (proj1 Hco') BK) Hl Hst S0V RAV HV UWK).
- intros m' md' A' B' errv' r BS gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc' LEN3 JF INV' PBK' BK' FS' FRM'.
eapply (Kredo m' md' A' B' errv' co' cb' stq r BS); [exact Hco' | exact Hcb' | exact LEN3 | exact JF | exact INV' | exact PBK' | exact BK' | exact FS' | exact FRM'].
- intros m' md' A' B' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc' INVW' FS' FRM'.
eapply (Kerr16 m' md' A' B' errv' co' cb' stq); [exact Hco' | exact INVW' | exact FS' | exact FRM']. }
eapply (inf_entry_A pf pa q LB0 LM FRS payload me lo m md A B ts l cb nb pj sv errv T gp t0 t1 t2 a3 a5 a6 a7 F fc STC INV Hl Hst SPB).
-
intros a0' a1' a2' a3' a6' G7.
pose proof (PICK m (t_co ts) cb (ts_stpos (t_x ts)) gp t0 t1 t2 a0' a1' a2' a3' (Z_to_bv 64 APE_JTAB) a5 a6' a7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) ltac:(lia) Hc) as P0.
rewrite Ets in P0. exact (P0 INV PBK).
-
intros a0' a1' a7' L7.
eapply (inf_loop_A 8%nat pf pa q LB0 LM FRS payload me lo m md A B ts l (t_co ts) (SPV (t_x ts)) 0 b cb nb pj sv errv T gp t0 t1 t2 a0' a1' a7' F fc
STC FL0 INV PBK CSTR Hl Hst ltac:(lia) (proj1 CO) ltac:(lia) Hco Hc ltac:(lia) SP0' ltac:(lia) ltac:(lia)).
+ intros m' co' cb' stq a0_1 a1_1 a2_1 a3_1 a4_1 a5_1 a6_1 t0_1 t1_1 Hco' Hcb' INV' PBK'.
eapply (PICK m' co' cb' stq); [lia | exact Hcb' | exact INV' | exact PBK'].
+ intros m' co' cb' stq e x1' a1_1 a2_1 a3_1 a4_1 a5_1 a6_1 t0_1 t1_1 s11_1 He Hco' INV'.
eapply (Kerr m' co' cb' stq e); [exact He | exact Hco' | exact INV'].
Qed.
End PeSInfA.
End RC__1.
