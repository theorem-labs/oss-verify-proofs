(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QWxq_c1 QRjH QHnV QCcH QfLs Q0Ek Qtgi QjDH Qsw7 QJjn QRUw QkMG QG8z Qdyh Q7UD Qhd4 Qwm6 QlKV QsKa Qiiq Q1Ey Ql4f QrQv Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw QkMG. Import QG8z Qdyh.Mq3 Qdyh.Mq4.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QsKa.Mq4 Qiiq.Mq0 Q1Ey Ql4f.Mq1 QsKa.Mq8 QrQv.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSOsepA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Let PRW := PE_REST_A_private_write HIx GA GA_outside.

Ltac pe_openA STC INV :=
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR); pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk);
destruct INV as [CORE REST];
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR);
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD).

Lemma seg_osep_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z)
(gp t0 t1 t2 a3 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_osep ->
t_co ts < pf_len pf ->

(forall m' ss' a1' a2' a3',
(bv_unsigned cb = 44 /\ ss' = ST_ofs_after_sep) \/ (bv_unsigned cb = 125 /\ ss' = ST_finish) ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B
(Qdyh.Mq4.ts_set_level ts (TL ST_eatws ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv ->
PBOK m' (Qdyh.Mq4.ts_set_level ts (TL ST_eatws ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) kP ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_ADV (t_co ts) gp t0 t1 t2 (Z_to_bv 64 125) a1' a2' a3' (Z_to_bv 64 APE_JTAB) a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F fc m')) ->

(forall a1' a3',
bv_unsigned cb <> 44 -> bv_unsigned cb <> 125 ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_ERR2 (t_co ts) gp t0 t1 t2 (Z_to_bv 64 11) a1'
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3' (Z_to_bv 64 APE_JTAB) a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m)) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA ST_osep) (t_co ts) gp t0 t1 t2
(Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l))
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3 (Z_to_bv 64 APE_JTAB) a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC INV PBK Hl Hst Hco Kbreak Kerr. pose proof INV as INV0. pe_openA STC INV.
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
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEP4c & SEP4q & SEP4i). cbn [hl_sb A4L] in SEP4c, SEP4q, SEP4i.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + SB4) in SHT4 by (unfold SB4, A_SB; lia).
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
unfold APE_ADV, APE_ERR2, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (MODE0 : c0 = CObj /\ hn0 = false).
{ rewrite Hst in Hmode. unfold ST_osep in Hmode. clear - Hmode SS26.
assert (R : 0 <= tl_ss l <= 26) by lia. enum_z R (tl_ss l); vm_compute in Hmode; split; congruence. }
destruct MODE0 as [-> ->].
stash Himg_t. stash Himg_q. clear PB REST TSK HP LV OBJ HPR BUD GAP SAVED FSH.
reenterA asegs A4L HIx asegs_wx HP. rewrite Hst. unfold ST_osep. cbn [pe_jtA].
replace (q + 32 * Z.of_nat depth) with bse by lia.
step.
change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)).
step.
destruct (Z.eq_dec (bv_unsigned cb) 44) as [C44 | N44].
- step.
if_truex.
step.
asan_chkA.
step.
stepz.
asan_rechkA.
stepz.
step. step.
asan_rechkA.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5; subst bse;
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv l ST_eatws ST_ofs_after_sep _ _ CObj STC INV0 Hl MUc WMc MIc TOKc Lc Hmode ltac:(vm_compute; reflexivity) ltac:(unfold ST_eatws; lia) ltac:(unfold ST_ofs_after_sep; lia)
(or_introl eq_refl) ltac:(rewrite Hst; vm_compute; reflexivity)) as [INV3 PBK3];
eapply (Kbreak mc ST_ofs_after_sep _ _ _ ltac:(left; split; [exact C44 | reflexivity])); [exact INV3 | exact (PBK3 kP PBK)]
end end.
- step.
if_falsex.
step.
destruct (Z.eq_dec (bv_unsigned cb) 125) as [C125 | N125].
+ step.
if_truex.
step.
asan_chkA.
step.
stepz.
asan_rechkM 1.
stepz.
step.
asan_rechkA.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5; subst bse;
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv l ST_eatws ST_finish _ _ CAny STC INV0 Hl MUc WMc MIc TOKc Lc Hmode ltac:(vm_compute; reflexivity) ltac:(unfold ST_eatws; lia) ltac:(unfold ST_finish; lia)
(or_intror eq_refl) ltac:(rewrite Hst; vm_compute; reflexivity)) as [INV3 PBK3];
eapply (Kbreak mc ST_finish _ _ _ ltac:(right; split; [exact C125 | reflexivity])); [exact INV3 | exact (PBK3 kP PBK)]
end end.
+ step.
if_falsex.
step. step.
asan_rechkA.
step. step.
evt_done5.
subst bse. eapply Kerr; [exact N44 | exact N125].
Qed.
End PeSOsepA.
End RC__1.
End Mq0.
From Stdlib Require NArith Permutation.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTEu Q4v2 QgHv Q1Y6 Q9O6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0. Import QTEu. Import Qsw7 QJjn QRUw QRUw.Mq0.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa Q4v2.Mq0 QgHv.Mq0 Q1Y6.Mq1 QsKa.Mq6 QlKV.Mq2 QsKa Q9O6.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
Local Ltac flia := Qo9G.term_slim ltac:(Zify.zify; xlia zchecker).

Lemma costX_le_potential : forall cap bpos n CAPB, 32 <= cap -> 0 <= bpos -> 0 <= n ->
Z.max (2 * cap) (bpos + n + 9) <= CAPB -> cap <= bpos + n + 1 ->
16 * Z.max (2 * cap) (bpos + n + 9) + 512 <= 64 * (CAPB - cap).
Proof. intros. flia. Qed.
Lemma grow_le_potential : forall cap bpos n, 32 <= cap -> 0 <= bpos -> 0 <= n -> cap <= bpos + n ->
16 * Z.max (2 * cap) (bpos + n + 9) + 512 <= 64 * (Z.max (2 * cap) (bpos + n + 9) - cap).
Proof. intros. flia. Qed.
Lemma grow_in_capb : forall cap0 bpos0 w cap bpos n, 0 <= bpos -> 0 <= n -> cap <= ser_capb cap0 bpos0 w -> bpos + n <= bpos0 + w -> cap <= bpos + n + 1 ->
Z.max (2 * cap) (bpos + n + 9) <= ser_capb cap0 bpos0 w.
Proof. intros. unfold ser_capb in *. flia. Qed.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section ASer.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Variables (sp gp : word) (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS0 : list frame) (B0 : bud) (pb lo : Z).
Variables (bpos0 cap0 w : Z).
Let usp := bv_unsigned sp.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis HT : usp <= hiA_top A4L HIx.
Hypothesis CAP0 : 32 <= cap0 < 2^30.
Hypothesis TXT : bpos0 + w < 2^28.
Hypothesis NEED : ser_need cap0 bpos0 w <= bB B0.
Hypothesis JHEX0 : JHEX_A m0.

Definition chunk_ok (FRSc : list frame) (FA : Z) (ch : Z * list cell) : Prop :=
client_range A4H (LB ++ LM ++ fr_ivs A4L FRSc) FA (fst ch) (Z.of_nat (cells_size (snd ch))).
Definition ser_memA (A : ASA A4L HIx) (FRSc : list frame) (FA : Z) (CH : list (Z * list cell)) (e : Z) (m : word -> option byte) (md : config) : Prop :=
exists (buf cap bpos : Z) (content : list byte) (errv : word) (B : bud),
HEAPAx A ((pb, PB_SZ) :: (buf, cap) :: LB) LM FRSc B m md /\
pbuf_core asegs m pb buf bpos cap content /\
Forall (fun ch => rw_cells asegs m (fst ch) (snd ch)) CH /\ Forall (chunk_ok FRSc FA) CH /\
(forall b, In b (fr_ivs A4L FRS0) -> In b (fr_ivs A4L FRSc)) /\
rw_cells asegs m A_ERRNO [C4 errv] /\
stk asegs m lo FA /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS0) usp m0 m /\ model_vm_only (cfg_model md0) (cfg_model md) /\
(bpos0 <= bpos <= bpos0 + e) /\ (cap0 <= cap <= ser_capb cap0 bpos0 w) /\
bB B0 - 64 * (cap - cap0) <= bB B /\ bD B0 <= bD B.

Lemma ser_memA_mem_inv : forall A FRSc FA CH e m md, ser_memA A FRSc FA CH e m md -> mem_inv asegs m.
Proof. intros A FRSc FA CH e m md (buf & cap & bpos & content & errv & B & HP & _). exact (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP). Qed.

Lemma ser_memA_weaken_e : forall A FRSc FA CH e e' m md, e <= e' -> ser_memA A FRSc FA CH e m md -> ser_memA A FRSc FA CH e' m md.
Proof.
intros A FRSc FA CH e e' m md He (buf & cap & bpos & content & errv & B & HP & PB & C1 & C2 & FS & ERR & ST & HPR & VM & Hb & Hc & HB & HD).
exists buf, cap, bpos, content, errv, B. repeat (split; [assumption|]). split; [lia|]. repeat (split; [assumption|]). assumption.
Qed.

Lemma chunks_pres : forall FRSc FA CH m m', heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRSc) FA m m' ->
Forall (chunk_ok FRSc FA) CH -> Forall (fun ch => rw_cells asegs m (fst ch) (snd ch)) CH -> Forall (fun ch => rw_cells asegs m' (fst ch) (snd ch)) CH.
Proof.
intros FRSc FA CH m m' HPR OK. induction OK as [|ch CH Hch _ IH]; intros H; [constructor|].
inversion H as [|x l Hx Hl]; subst. constructor; [| apply IH; exact Hl].
eapply (heap_pres_rw_cells A4H); [exact HPR | exact Hx | exact Hch].
Qed.

Hypothesis OBL_REALLOC_NF : realloc_nf_stmt HIx.

Lemma ser_appendA :
forall (ret : Z) (x3 t0 t1 t2 x8 x9 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
(F Fc : bvmap 5 word) (fcc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (FRSc : list frame) (FA : Z) (CH : list (Z * list cell)) (e b k : Z) (sb : list byte),
ser_memA A FRSc FA CH e m md ->
bytes_at asegs m b sb -> Z.of_nat (length sb) = k -> 0 <= k < 2^31 -> 0 <= b ->
src_locA LB FRSc b k -> (0 < k -> unpoisoned asegs m A_SB b k) ->
0 <= e -> e + k <= w ->
lo <= FA - 112 - 4096 -> FA mod 16 = 0 -> FA <= usp -> 0 <= FA ->
x3 = gp -> 0 <= ret < 2^64 -> ret mod 2 = 0 ->
fsaved F Fc -> frm0 fcc ->
(forall (A' : ASA A4L HIx) m' md' (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) F' fc',
ser_memA A' FRSc FA CH (e + k) m' md' -> fsaved F F' -> frm0 fc' -> bytes_at asegs m' b sb ->
AJ5 A4L HIx A' T md' (MS (mkR (wz ret) (wz FA) gp (wz A_TP) t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7'
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6') F' (wz ret) fc' None m' (seg_rom asegs))) ->
AJ5 A4L HIx A T md (MS (mkR (wz ret) (wz FA) x3 (wz A_TP) t0 t1 t2 x8 x9 (wz pb) (wz b) (wz k) a3 a4 a5 a6 a7
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) Fc (wz AMEMAPPEND) fcc None m (seg_rom asegs)).
Proof.
intros until sb. intros INV SB SBL Hk Hb SRCB UPS He Hek LOS FAA FAU FA0 -> Hret Hret2 FS FRM K.
destruct INV as (buf & cap & bpos & content & errv & B & HP & PB & CHm & CHok & FSUB & ERR & ST & HPR & VM & Hbp & Hcap & HBB & HBD).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
assert (U2 : bv_unsigned (wz FA) = FA) by (apply unsigned_lit; unfold usp in *; lia).
pose proof PB as (Hb0 & Hsz & Hlen & _).
assert (CAPB : ser_capb cap0 bpos0 w < 2^30) by (unfold ser_capb; flia).
assert (POT : 64 * (ser_capb cap0 bpos0 w - cap) <= bB B) by (unfold ser_need in NEED; flia).
assert (COSTX : memappend_costX cap bpos k <= bB B).
{ unfold memappend_costX, memappend_costB. destruct (Z.leb_spec cap (bpos + k + 1)) as [G|NG].
- pose proof (grow_in_capb cap0 bpos0 w cap bpos k ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) G) as GC.
pose proof (costX_le_potential cap bpos k (ser_capb cap0 bpos0 w) ltac:(lia) ltac:(lia) ltac:(lia) GC G). lia.
- flia. }
unfold AMEMAPPEND.
eapply (memappend_A_cps_nf HIx OBL_REALLOC_NF) with (A := A) (LB := LB) (buf := buf) (bpos := bpos) (cap := cap) (b := b) (n := k)
(lo := lo) (content := content) (src := sb) (errv := errv);
rewrite ?U2.
- exact HP.
- exact PB.
- lia.
- exact SB.
- exact SBL.
- exact Hb.
- exact SRCB.
- exact UPS.
- exact ST.
- exact LO.
- lia.
- exact FAA.
- unfold usp in *. lia.
- exact ERR.
- reflexivity.
- rewrite unsigned_lit by lia. exact Hret2.
- reflexivity.
- reflexivity.
- reflexivity.
- exact COSTX.
- intros ms' md' A' POST.
destruct POST as (m' & r & errv' & buf' & cap' & B' & RS & VM' & ST' & HPR' & ERR' & HB1 & HD1 & HP' & OUT).
destruct RS as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F' & fc' & -> & FS' & FR').
rewrite U2 in ST', HPR'.
replace (ret_pc (wz ret)) with (wz ret) by (symmetry; apply ret_pc_even; [lia | exact Hret2]).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP') as MI'.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
assert (SB' : bytes_at asegs m' b sb).
{ eapply (src_loc_bytes_pres _ LB LM FRSc); [exact HPR' | exact MI | exact MI' | intros bb Hbb; exact Hbb | rewrite SBL; exact SRCB | exact SB]. }
apply K; [| eapply fsaved_trans; [exact FS | exact FS'] | exact (FR' FRM) | exact SB'].
assert (OUT' : exists bpos' content', pbuf_core asegs m' pb buf' bpos' cap' content' /\ bpos <= bpos' <= bpos + k
/\ cap <= cap' <= ser_capb cap0 bpos0 w /\ bB B - 64 * (cap' - cap) <= bB B').
{ destruct OUT as [(_ & -> & PBF) | (_ & -> & -> & HNC & PBC)].
- destruct PBF as (bufq & bposq & sizeq & post & E & L & C). injection E as <- <-.
exists bposq, ((firstn (Z.to_nat bpos) content ++ sb) ++ [Z_to_bv 8 0] ++ post). split; [exact C|].
assert (Lq : bposq = bpos + k).
{ rewrite <- L, length_app, length_firstn. rewrite Nat.min_l by lia. lia. }
split; [lia|]. unfold memappend_cap2, memappend_costX2, memappend_costB in *.
destruct (Z.leb_spec cap (bpos + k)) as [G|NG].
+ replace (cap <? 2^30) with true by (symmetry; apply Z.ltb_lt; lia).
pose proof (grow_in_capb cap0 bpos0 w cap bpos k ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as GC.
pose proof (grow_le_potential cap bpos k ltac:(lia) ltac:(lia) ltac:(lia) G). split; [flia | lia].
+ split; lia.
- exists bpos, content. split; [exact PBC|]. split; [lia|]. split; [lia | lia]. }
destruct OUT' as (bpos' & content' & PB' & Hbp' & Hcap' & HCX).
exists buf', cap', bpos', content', errv', B'.
split; [exact HP'|]. split; [exact PB'|].
split; [eapply chunks_pres; [exact HPR' | exact CHok | exact CHm]|]. split; [exact CHok|]. split; [exact FSUB|].
split; [exact ERR'|]. split; [exact ST'|].
split. { eapply heap_pres_trans; [exact HPR | eapply heap_pres_weaken; [exact HPR' | unfold usp in *; lia |]].
intros bb Hbb. apply in_app_or in Hbb. apply in_or_app. destruct Hbb as [Hbb|Hbb]; [left; exact Hbb | right].
apply in_app_or in Hbb. apply in_or_app. destruct Hbb as [Hbb|Hbb]; [left; exact Hbb | right; apply FSUB; exact Hbb]. }
split; [eapply model_vm_only_trans; [exact VM | exact VM']|].
split; [lia|]. split; [lia|]. split; [lia | lia].
Qed.

Lemma ser_childA :
forall (entry : Z) (s' : jshape), ser_specA HIx entry s' ->
forall (ret : Z) (x3 t0 t1 t2 x8 x9 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
(F Fc : bvmap 5 word) (fcc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (FRSc : list frame) (FA : Z) (CH : list (Z * list cell)) (e : Z)
(RESTc Yc Rc : list blk) (v rc' pbc lvc fl wc : Z),
ser_memA A FRSc FA CH e m md ->
jnode asegs A4F s' m RESTc v rc' pbc -> incl RESTc LB ->
jtx s' (RESTc ++ Yc) = Some (wc, Rc) ->
0 <= e -> e + wc <= w ->
aflags_ok fl -> 0 <= lvc -> lvc + sdepth s' <= 1000 ->
Z.of_nat (length FRSc) + 1 < 4096 ->
lo <= FA - ser_budgetA s' -> FA mod 16 = 0 -> FA <= usp -> 0 <= FA ->
x3 = gp -> 0 <= ret < 2^64 -> ret mod 2 = 0 ->
fsaved F Fc -> frm0 fcc ->
(forall (A' : ASA A4L HIx) m' md' (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) F' fc',
ser_memA A' FRSc FA CH (e + wc) m' md' -> fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A' T md' (MS (mkR (wz ret) (wz FA) gp (wz A_TP) t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7'
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6') F' (wz ret) fc' None m' (seg_rom asegs))) ->
AJ5 A4L HIx A T md (MS (mkR (wz ret) (wz FA) x3 (wz A_TP) t0 t1 t2 x8 x9 (wz v) (wz pb) (wz lvc) (wz fl) a4 a5 a6 a7
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) Fc (wz entry) fcc None m (seg_rom asegs)).
Proof.
intros entry s' SPEC. intros until wc. intros INV JN INCL JTX He Hew FL Hlv Hlvd FRN LOS FAA FAU FA0 -> Hret Hret2 FS FRM K.
destruct INV as (buf & cap & bpos & content & errv & B & HP & PB & CHm & CHok & FSUB & ERR & ST & HPR & VM & Hbp & Hcap & HBB & HBD).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
assert (U2 : bv_unsigned (wz FA) = FA) by (apply unsigned_lit; unfold usp in *; lia).
pose proof (jtx_nonneg _ _ _ _ JTX) as Hwc.
assert (CAPB : ser_capb cap0 bpos0 w < 2^30) by (unfold ser_capb; flia).
assert (NEEDc : ser_need cap bpos wc <= bB B).
{ eapply (ser_need_step cap0 cap bpos0 bpos w wc (bB B0) (bB B)); [exact Hcap | lia | exact NEED | exact HBB]. }
assert (JH : JHEX_A m) by (eapply JHEX_A_pres; [exact HPR | exact JHEX0]).
unfold ser_specA in SPEC.
eapply SPEC with (A := A) (LB := LB) (LM := LM) (FRS := FRSc) (B := B) (buf := buf) (bpos := bpos) (cap := cap) (lo := lo) (content := content) (errv := errv)
(REST := RESTc) (p := v) (rc := rc') (pb0 := pbc) (lv := lvc) (fl := fl) (w := wc) (Y := Yc) (R := Rc);
rewrite ?U2.
- exact HP.
- exact PB.
- exact JN.
- exact INCL.
- exact JTX.
- lia.
- lia.
- exact NEEDc.
- exact FL.
- exact Hlv.
- exact Hlvd.
- exact FRN.
- exact ST.
- exact LO.
- exact LOS.
- exact FAA.
- unfold usp in *. lia.
- exact ERR.
- exact JH.
- reflexivity.
- rewrite unsigned_lit by lia. exact Hret2.
- exact FRM.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- intros ms' md' A' POST.
destruct POST as (m' & r & errv' & buf' & cap' & bpos' & content' & B' & RS & VM' & ST' & HPR' & ERR' & HP' & PB' & Hbp' & Hcap' & HBB' & HBD').
destruct RS as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F' & fc' & -> & FS' & FR').
rewrite U2 in ST', HPR'.
replace (ret_pc (wz ret)) with (wz ret) by (symmetry; apply ret_pc_even; [lia | exact Hret2]).
apply K; [| eapply fsaved_trans; [exact FS | exact FS'] | exact (FR' FRM)].
pose proof (ser_capb_mono cap0 cap bpos0 bpos w wc Hcap ltac:(lia)) as MONO.
exists buf', cap', bpos', content', errv', B'.
split; [exact HP'|]. split; [exact PB'|].
split; [eapply chunks_pres; [exact HPR' | exact CHok | exact CHm]|]. split; [exact CHok|]. split; [exact FSUB|].
split; [exact ERR'|]. split; [exact ST'|].
split. { eapply heap_pres_trans; [exact HPR | eapply heap_pres_weaken; [exact HPR' | unfold usp in *; lia |]].
intros bb Hbb. apply in_app_or in Hbb. apply in_or_app. destruct Hbb as [Hbb|Hbb]; [left; exact Hbb | right].
apply in_app_or in Hbb. apply in_or_app. destruct Hbb as [Hbb|Hbb]; [left; exact Hbb | right; apply FSUB; exact Hbb]. }
split; [eapply model_vm_only_trans; [exact VM | exact VM']|].
split; [lia|]. split; [lia|]. split; [lia | lia].
Qed.
End ASer.
End RC__1.
End Mq1.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache Qfw3_c1 Qc3B QmZZ Q6WR QrPc QYIF QgoP QZAi Qx2n QXUB QJZd Qw5U Qvmy QLHv Qawr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.

Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun QWxq_c1.Mq0 Qfw3_c1.Mq2 Qc3B.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn.
Import Q6WR Q6WR.Mq0 QrPc.
Import QYIF.
Import QgoP.
Import QZAi.Mq1 Qx2n.
Import Q7UD QXUB.Mq0 Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QsKa.Mq4 QlKV.Mqa QsKa.Mq0 QJZd.Mq0 QsKa.Mq8 Qw5U.Mq0.

Import QsKa.Mq6.

Import Qvmy.Mq0 QLHv.Mq0 Qawr.Mq0.
Import Qw5U.Mq3.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma map_unsigned_bytesA : forall bs : list byte, map (Z_to_bv 8) (map bv_unsigned bs) = bs.
Proof. induction bs as [|b bs IH]; [reflexivity|]. cbn. rewrite IH. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma lb_remove_notinA : forall p LB, (forall n, ~ In (p, n) LB) -> lb_remove p LB = LB.
Proof.
induction LB as [|[a n] LB IH]; intros H; [reflexivity|]. cbn [lb_remove blk_addr fst].
destruct (Z.eqb_spec a p) as [->|NE]; [exfalso; apply (H n); left; reflexivity|]. f_equal. apply IH. intros k Hk. apply (H k). right; exact Hk.
Qed.

Ltac gd_fs_tail := let k := fresh "k" in let Hk := fresh "Hk" in let NE := fresh "NE" in intros k Hk NE; cbn [FSAVED In] in Hk;
repeat (destruct Hk as [<- | Hk]); [..| destruct Hk];
first [ exfalso; apply NE; reflexivity
| rewrite ?freg_get_other by (vm_compute; reflexivity);
first [ reflexivity
| match goal with FS : forall k, In k FSAVED -> k <> 8 -> _ |- _ => apply FS; [cbn [FSAVED In]; repeat first [left; reflexivity | right] | lia] end ] ].

Ltac gd_exit EPI XHPg XPD PDb HPb Ab mdb Bb mb VMb CHb :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply (EPI mc Ab mdb Bb);
[ eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
| eapply (XHPg Ab Bb mdb mb mc HPb); assumption | exact VMb | eapply (XPD mb mc PDb Ab mdb Bb HPb); assumption
| exact CHb
| gd_fs_tail | first [intros Hf; exact Hf | intros _; assumption | assumption] ] end.

Section MJoGetDouble.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis ERRNOL : QlKV.Mq4.errno_location_A_stmt.
Hypothesis SCANH : scan_total_stmtA.
Hypothesis STRTOD : astrtod_total_stmt.

Lemma RTC_LCONV : rtc_lconv_stmt HIx.
Proof.
intros A LB LM FR B m md HP. unfold A_LCONV, A_DPSTR. apply (rtc_cell HIx _ _ _ _ _ _ _ _ _ HP). unfold a4_rt_consts.
repeat (first [left; reflexivity | right]).
Qed.

Lemma RTC_GDPC : forall A LB LM FR B m md, HEAPAx A LB LM FR B m md -> bytes_at asegs m 0xe6a60 (le8 (Z_to_bv 64 0x9dde4)).
Proof.
intros A LB LM FR B m md HP. apply (rtc_cell HIx _ _ _ _ _ _ _ _ _ HP). unfold a4_rt_consts.
repeat (first [left; reflexivity | right]).
Qed.

Definition GD_STK_A : Z := 128 + ASTRTOD_DEPTH.

Lemma get_double_A : jo_get_double_A_stmt HIx 0x9dde4 GD_STK_A 512 0.
Proof.
unfold jo_get_double_A_stmt. intros until errv. intros (HP & ST & LO & LOS & SPA16 & HT & ERR & TP & RA) JO FRN BB BD SPA FRM A0 K.
unfold GD_STK_A, ASTRTOD_DEPTH in LOS. subst a0 tp.
assert (FRMfp : Qc3B.frm0 fc) by exact FRM.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof alloc_ceiling_range as ACR.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HP) as (SB1 & SB2 & SB3 & SB4).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2. apply ro_C8_of_bytes_at in SB3.
assert (UARC : ro_cells asegs m (hl_uar_cell A4L) [C4 (Z_to_bv 64 1)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SB4]).
clear SB4. a4l.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)] m) as MU.
unfold A_ERRNO, A_TP in *.
stash ERR.
reenterA asegs A4L HIx asegs_wx HP.
carve_frame 128%nat ST.
step. stepz. do 13 step.
step.
step. step.
rewrite (unsigned_lit (bv_unsigned sp + -128)) by lia. change 18446744073709551584 with (2^64 - 2^5). rewrite OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.land_align_down by lia. change (2^5) with 32.
replace (bv_unsigned sp + -128 - (bv_unsigned sp + -128) mod 32) with (bv_unsigned sp + -128) by (clear - SPA; Z.div_mod_to_equations; lia).
step. step. step. step. step. step. step. step.
norm_sx32. step. if_false. step. step.
evt_done5.
eapply (stack_malloc_full HIx) with (k := 0) (bytes := 64) (lo := lo) (LB := BS ++ LB) (LM := LM) (FR := FRS) (B := B);
[ heap_nowA A4L HIx HP MU WM MI | lia | .. ].
all: rewrite ?unsigned_lit by lia.
1: rewrite fr_size_0; lia.
1: reflexivity.
1: lia.
1: exact ST.
1: exact LO.
1: cbn [hl_stack_A A4L]; lia.
1: clear - SPA; Z.div_mod_to_equations; lia.
1: lia.
1: reflexivity.
1: reflexivity.
intros ms1 m1' md1 A1 Fr RS1 VM1 ST1 HPR1 FRNZ (jff & FF1) SHB1 HP1. open_ret RS1.
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HP1) as (errv1 & ERR1). unfold A_ERRNO, A_TP in ERR1. cbn [hl_tp A4L A4H hla_base] in ERR1.
rewrite ?unsigned_lit in ST1, HPR1 by lia.
clear ERR.
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as (_ & HFal & HF0 & HFc & HFimg & _ & HFshw & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as HFapp.
rewrite fr_size_0 in HFal, HFc, HFimg, HFapp. rewrite fr_shadow_len_0 in HFshw. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFimg, HFapp.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in FR; [| left; cbn; lia].
clear SB1 SB2 SB3 UARC.
pose proof (RTC_GDPC _ _ _ _ _ _ _ HP1) as PCC. apply ro_C8_of_bytes_at in PCC.
assert (FSH1 : rw_cells asegs m1' (shad A4L Fr) [CB 8 (repeat (Z_to_bv 8 0) 8)]).
{ split; [split; [cbn; split; [reflexivity | exact I] | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SHB1] | exact HFshw]. }
rewrite fr_size_0 in FF1. change (Z.to_nat (64 - 8)) with 56%nat in FF1.
unfold shad in FSH1. a4l.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 8 <= 17594333495296) by (unfold sh; clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI1. change (hl_segs A4L) with asegs in MI1. clear MI.
rename MU into MU0. rename WM into WM0. pose proof (wmono_refl asegs m1') as WM. pose proof (munch_refl [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6434236, 6434240)] m1') as MU.
change (6434400 - 164) with 6434236 in ERR1.
unfold A_SB in HFapp.
reenterA asegs A4L HIx asegs_wx HP1.
step. step. step. if_truex.
stepz.
step. step. step. step.
rewrite (unsigned_lit Fr) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
step. step. step. stepz. stepz. stepz. step. step.
fold sh.
stepz. stepz. stepz. stepz. step. stepz. stepz. stepz. stepz.
stepz.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (SHE : ro_cells asegs mc 2148255159 [C1 (Z_to_bv 8 0)]) end.
{ apply QsKa.Mq1.ro_C1_of_bytes_at.
pose proof (heapA_shadow_img A4L HIx _ _ _ _ _ _ _ (6434236 / 8) HP1) as X.
assert (E : img_shadow_val (hl_reg_globals A4L) (6434236 / 8) = 0) by (vm_compute; reflexivity). rewrite E in X.
cbn [hl_sb A4L hl_img_lo hl_img_hi hla_base A4H] in X. unfold A_SB in X.
specialize (X ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
change (6434236 / 8 + 2147450880) with 2148255159 in X.
eapply bytes_at_transport; [exact X | exact MU |]. cbn [disjoint_from length]. change (Z.of_nat 1) with 1. unfold sh. clear - HFimg HFapp HF0 HFc ACR LO LOS SPR. Z.div_mod_to_equations. lia. }

apply (proj1 (rw_cells_app asegs _ _ [_; _; _; _] _)) in FF1. destruct FF1 as [FFa FFe]. cbn [cells_size csize Nat.add] in FFe.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FFe. destruct FFe as [FFe FFb]. cbn [cells_size csize Nat.add] in FFb.
change (Z.of_nat 32) with 32 in FFe, FFb. replace (Fr + 32 + Z.of_nat 8) with (Fr + 40) in FFb by lia.
assert (XHP : forall BX mX, munch [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6434236, 6434240)] m1' mX -> wmono asegs m1' mX -> mem_inv asegs mX ->
forall AX mdX, HEAPAx AX (BS ++ LB) LM ((Fr, 0) :: FRS) BX m1' mdX -> HEAPAx AX (BS ++ LB) LM ((Fr, 0) :: FRS) BX mX mdX).
{ intros BX mX MUX WMX MIX AX mdX HPX. exact (fk0_HEAPA HIx _ _ _ _ _ _ _ _ _ _ _ HPX LO HT MUX WMX MIX). }
assert (PD1 : heap_presD (Fr + 32) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m1').
{ eapply heap_presD_trans; [| eapply heap_presD_of_pres; [exact HPR1 | lia]].
eapply (presD_private HIx _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp) (Fr + 32) HP MU0 WM0); [| lia |].
- intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. exact Hb.
- apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. lia. }
assert (XPD : forall mb mX, heap_presD (Fr + 32) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mb ->
forall AX mdX BX, HEAPAx AX (BS ++ LB) LM ((Fr, 0) :: FRS) BX mb mdX ->
munch [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6434236, 6434240)] mb mX -> wmono asegs mb mX ->
heap_presD (Fr + 32) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mX).
{ intros mb mX PDb AX mdX BX HPb MUX WMX. eapply heap_presD_trans; [exact PDb |].
eapply (fk0_presD HIx); [exact HPb | exact LO | lia | exact MUX | exact WMX]. }
assert (XHPg : forall AX BX mdX mb mX, HEAPAx AX (BS ++ LB) LM ((Fr, 0) :: FRS) BX mb mdX ->
munch [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6434236, 6434240)] mb mX -> wmono asegs mb mX -> mem_inv asegs mX ->
HEAPAx AX (BS ++ LB) LM ((Fr, 0) :: FRS) BX mX mdX).
{ intros AX BX mdX mb mX HPX MUX WMX MIX. exact (fk0_HEAPA HIx _ _ _ _ _ _ _ _ _ _ _ HPX LO HT MUX WMX MIX). }
assert (CH0 : jo_chargeA 512 0 B B) by (split; lia).
clear XHP.

lazymatch type of FR with rw_cells _ _ _ ?frc => lazymatch type of FSH1 with rw_cells _ _ _ ?shc => lazymatch type of FFa with rw_cells _ _ _ ?ffc =>
assert (EPI : forall (mX : word -> option byte) (AX : ASA A4L HIx) (mdX : config) (BX : bud) (F1 : bvmap 5 word) (fc1 : bv 32)
(eX xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs10 xs11 xt3 xt4 xt5 xt6 : word),
mem_inv asegs mX ->
rw_cells asegs mX (bv_unsigned sp + -128) frc -> rw_cells asegs mX sh shc -> rw_cells asegs mX Fr ffc ->
rw_cells asegs mX 6434236 [C4 eX] -> stk asegs mX lo (bv_unsigned sp + -128) ->
HEAPAx AX (BS ++ LB) LM ((Fr, 0) :: FRS) BX mX mdX -> model_vm_only (cfg_model md) (cfg_model mdX) ->
heap_presD (Fr + 32) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mX ->
jo_chargeA 512 0 B BX ->
(forall k, In k FSAVED -> k <> 8 -> reg_get F1 (Z_to_bv 5 k) = reg_get F (Z_to_bv 5 k)) -> (frm0 fc -> frm0 fc1) ->
evt asegs (AJ5e A4L HIx AX T mdX)
(MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -128)) gp (Z_to_bv 64 6434400) xt0 xt1 xt2 sp xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 Fr) xs3 xs4 xs5 xs6 xs7 (Z_to_bv 64 sh) (Z_to_bv 64 Fr) xs10 xs11 xt3 xt4 xt5 xt6)
F1 (Z_to_bv 64 0x9e150) fc1 None mX (seg_rom asegs)))
end end end.
{ intros mX AX mdX BX F1 fc1 eX xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs10 xs11 xt3 xt4 xt5 xt6 MIX FRX FSHX FFX ERRX STX HPX VMX PDX CHX FSX FRMX.
clear MU WM MI1 FR FSH1 FFa FFe FFb ST1 ERR1 SHE PCC.
pose proof (wmono_refl asegs mX) as WM. pose proof (munch_refl [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6434236, 6434240)] mX) as MU.
step. stepz. step. step. stepz. step. if_falsex. step. do 8 stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ mX mc, WMc : wmono asegs mX mc, MIc : mem_inv asegs mc |- _ =>
pose proof (fk0_HEAPA HIx _ _ _ _ _ _ _ _ _ _ _ HPX LO HT MUc WMc MIc) as HPY;
pose proof (XPD mX mc PDX AX mdX BX HPX MUc WMc) as PDY end end.
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HPY INF) as (_ & _ & _ & _ & _ & _ & _ & (fp & FPB & FPR & FPnc & FPimg & FPns & FPfr)).
rewrite fr_size_0 in FPB. replace (Fr + 64 - 8) with (Fr + 56) in FPB by lia.
pose proof (ro_C8_of_bytes_at asegs _ _ _ FPB) as FPC.
step.
evt_done5.
eapply (hiA_frame_release A4L HIx) with (Fr := Fr) (k := 0) (fp := fp) (rX := Z_to_bv 5 10);
[exact HPY | exact INF | rewrite fr_size_0; replace (Fr + 64 - 8) with (Fr + 56) by lia; exact FPB | lia | reflexivity | vm_compute; discriminate | | ].
1: vm_compute; split; reflexivity.
intros m5 md5 A5 VM5 HP5 Hoff Hwv.
cbn [fr_remove fr_base fst Z.eqb] in HP5. rewrite Z.eqb_refl in HP5.
lazymatch type of HPY with HEAPA _ _ _ _ _ _ _ ?mq _ => assert (MUr : munch [(fp, fp + 1)] mq m5) end.
{ intros x Hx. cbn [outside] in Hx. pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR. cbn in XR.
rewrite <- (Z_to_bv_bv_unsigned x). change (Z_to_bv 64 (bv_unsigned x)) with (wa (bv_unsigned x)). apply Hoff; lia. }
lazymatch type of HPY with HEAPA _ _ _ _ _ _ _ ?mq _ => assert (WMr : wmono asegs mq m5) by exact Hwv end.
assert (FPlow : fp < alloc_ceiling) by (destruct (Z.lt_ge_cases fp alloc_ceiling) as [L|G]; [exact L | exfalso; apply FPnc; left; exact G]).
apply (rw_cells_transport asegs [(fp, fp + 1)] _ m5) in FRX; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] _ m5) in ERRX; [| exact MUr | exact WMr | cbn [disjoint_from cells_size csize Nat.add]; cbn [hl_scratch A4L A4H hla_base] in FPns; unfold A_TP in FPns; lia].
apply (stk_transport_disjoint asegs [(fp, fp + 1)] _ m5) in STX; [| exact MUr | exact WMr | cbn [disjoint_from]; lia].
change (647568 + 4) with 647572.
clear FFX FSHX FPC.
reenterA asegs A4L HIx asegs_wx HP5.
do 18 step.
evt_done5.
assert (PD5 : heap_presD (Fr + 32) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m5).
{ eapply heap_presD_trans; [exact PDY |].
eapply (presD_fp HIx _ _ _ _ _ _ _ _ (Fr + 32) _ (bv_unsigned sp) fp HPY); [| lia | exact FPnc | exact FPfr | exact Hoff | exact Hwv].
intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. destruct Hb as [H|H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H]. }
eapply (K _ md5 m5 fp A5 BX).
- split; [| split; [| split; [| split]]].
+ apply ret_statew_intro; [| exact FRMX].
intros k Hk. destruct (Z.eq_dec k 8) as [-> | NE].
* rewrite freg_get_same by (vm_compute; reflexivity). reflexivity.
* rewrite freg_get_other. { apply FSX; [exact Hk | exact NE]. }
cbn [FSAVED In] in Hk.
repeat (destruct Hk as [<- | Hk]); [..| destruct Hk]; first [vm_compute; reflexivity | exfalso; apply NE; reflexivity].
+ eapply model_vm_only_trans; [exact VMX | exact VM5].
+ release_frame FRX STX (bv_unsigned sp). exact STX.
+ eapply (heap_pres_of_presD (Fr + 32)).
* eapply heap_presD_weaken; [exact PD5 | lia |]. intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; apply in_or_app; right; exact Hb | apply in_or_app; right; exact Hb].
* intros a Hd Hc.
destruct (own_frame_fresh HIx Fr 0 (BS ++ LB) LB LM FRS B A1 m1' md1 HP1 ltac:(intros b Hb; apply in_or_app; right; exact Hb)) as [OFF OFS].
assert (Ho : outside [(Fr + 32, Fr + 40)] a).
{ eapply (Q1Ey.client_outsideF HIx A1 (BS ++ LB) LM ((Fr, 0) :: FRS) B (LB ++ LM ++ fr_ivs A4L FRS) m1' md1 [(Fr + 32, Fr + 40)] (bv_unsigned sp) HP1); [| lia | | lia | exact Hc].
- intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. destruct Hb as [H|H]; [left; apply in_app_or in H; apply in_or_app; destruct H as [H|H]; [left; apply in_or_app; right; exact H | right; exact H] | right; cbn [fr_ivs flat_map app]; right; right; exact H].
- apply Forall_cons; [| apply Forall_nil]. right; right; right. exists Fr, 0. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. left. cbn [fst snd]. rewrite fr_size_0. lia. }
cbn [outside] in Ho. lia.
+ eexists. exact ERRX.
- exact CHX.
- eapply (jopt_agree asegs A4F BS m m5 s BS p); [exact JO | | apply incl_refl].
eapply (agree_of_presD (Fr + 32)); [exact PD5 | intros b Hb; apply in_or_app; left; apply in_or_app; left; exact Hb |].
intros a n Hin.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP1 INF ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin)) as DF. rewrite fr_size_0 in DF. lia.
- exact HP5. }
step.
destruct s as [shp|].
2:{  destruct JO as [Hp _]. rewrite Hp in *. if_truex.
gd_exit EPI XHPg XPD PD1 HP1 A1 md1 B m1' VM1 CH0. }
destruct JO as [Hp J].

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m1' mc, WMc : wmono asegs m1' mc, MIc : mem_inv asegs mc |- _ =>
pose proof (XHPg A1 B md1 m1' mc HP1 MUc WMc MIc) as HPc;
assert (AGc : agree_on asegs BS m mc);
[ eapply (agree_of_presD (Fr + 32)); [exact (XPD m1' mc PD1 A1 md1 B HP1 MUc WMc) | intros b Hb; apply in_or_app; left; apply in_or_app; left; exact Hb |];
let a := fresh "a" in let n := fresh "n" in let Hin := fresh "Hin" in intros a n Hin;
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP1 INF ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin)) as DF; rewrite fr_size_0 in DF; lia
| ] end end.
pose proof (jval_agree asegs A4F shp BS m _ BS p 1 J AGc (incl_refl _)) as Jc.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HPc) as ND0.
assert (ND : List.NoDup (map blk_addr BS)) by exact (nodup_app_l' _ _ (nodup_app_l' _ _ ND0)).
destruct (jval_hdr asegs A4F shp _ BS p 1 Jc ND) as (n & tojs & pb & udel & ud & rest & INp & SZ & N48 & HDR & CLOSE).
assert (INpA : In (p, n) (BS ++ LB)) by (apply in_or_app; left; exact INp).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HPc ltac:(apply in_or_app; left; exact INpA)) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HPc ltac:(apply in_or_app; left; exact INpA)) as Hpimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hpimg.
assert (Hp8 : p mod 8 = 0) by (clear - Hpal; Z.div_mod_to_equations; lia).
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p n 0 HPc INpA ltac:(lia) ltac:(lia)) as SH0. rewrite Z.add_0_r in SH0.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p n 5 HPc INpA ltac:(lia) ltac:(lia)) as SH5. replace (p / 8 + 2147450880 + 5) with (p / 8 + 2147450885) in SH5 by lia.
if_falsex.
unfold jhdr_cells in HDR, SZ. cbn [app hl_segs hla_base A4L A4H] in HDR, SZ.
pose proof (jtype_range shp) as JR.
asan_chk0.
step. rewrite sx32_small by lia. step. step.
destruct shp as [|u| |h|kids|kids]; cbn [jtype] in *; unfold JT_BOOLEAN, JT_DOUBLE, JT_INT, JT_STRING, JT_OBJECT, JT_ARRAY in *; if_lit.
-
step. step. if_lit.
destruct Jc as (pb_ & PBS & REST & EBS & OPB & (b & junk_ & ER & CELLS)). cbn [hl_segs hla_base A4L A4H] in CELLS. unfold jhdr_cells in CELLS. cbn [app] in CELLS.
step. asan_chkA.
step. step. step.
gd_exit EPI XHPg XPD PD1 HP1 A1 md1 B m1' VM1 CH0.
-
step. step. if_lit. step. step. if_lit.
destruct Jc as (pb_ & PBS & REST & EBS & OPB & Jc). cbn [hl_segs hla_base A4L A4H] in Jc.
lazymatch type of HPc with HEAPA _ _ _ _ _ _ _ ?mc _ => assert (CELLS : exists tojs' udel' ud' bits, rw_cells asegs mc p (jhdr_cells 2 1 tojs' pb_ udel' ud' ++ [C8 bits])) end.
{ destruct u; [destruct Jc as (bits & ud_ & udn & uds & _ & _ & C & _) | destruct Jc as (bits & _ & _ & C)]; do 4 eexists; exact C. }
clear Jc. destruct CELLS as (tojs' & udel' & ud' & bits & CELLS). unfold jhdr_cells in CELLS. cbn [app] in CELLS.
step. asan_chkA.
step. step.
gd_exit EPI XHPg XPD PD1 HP1 A1 md1 B m1' VM1 CH0.
-
step. step. if_lit.
destruct Jc as (pb_ & PBS & REST & EBS & OPB & (cty & v & junk_ & ER & Hcty & CELLS)). cbn [hl_segs hla_base A4L A4H] in CELLS. unfold jhdr_cells in CELLS. cbn [app] in CELLS.
assert (INp56 : In (p, 56) (BS ++ LB)) by (apply in_or_app; left; rewrite EBS, ER; cbn; left; reflexivity).
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p 56 6 HPc INp56 ltac:(lia) ltac:(lia)) as SH6. replace (p / 8 + 2147450880 + 6) with (p / 8 + 2147450886) in SH6 by lia.
step. asan_chkA.
step. rewrite sx32_small by lia. step. step.
destruct Hcty as [-> | ->]; if_lit.
+
step. if_lit. step. asan_chkA. step. step. step.
gd_exit EPI XHPg XPD PD1 HP1 A1 md1 B m1' VM1 CH0.
+
step. asan_chkA. step. step. step.
gd_exit EPI XHPg XPD PD1 HP1 A1 md1 B m1' VM1 CH0.
-
step. step. if_lit. step. step. if_lit.
destruct Jc as (pb_ & PBS & REST & EBS & OPB & Jc). cbn [hl_segs hla_base A4L A4H] in Jc, OPB.
lazymatch type of HPc with HEAPA _ _ _ _ _ _ _ ?mc _ =>
assert (TXT : exists (TX TB TBN len : Z) (str0 rest0 : list byte) (lencell : list cell),
In (TB, TBN) BS /\ TB <= TX /\ TX + Z.of_nat (length str0) + 1 <= TB + TBN /\ ~ In (Z_to_bv 8 0) str0 /\
Z.of_nat (length str0) < 2^31 /\
bytes_at asegs mc TX (str0 ++ [Z_to_bv 8 0]) /\
rw_cells asegs mc (p + 40) (C8 (Z_to_bv 64 len) :: lencell) /\ -2^31 < len < 2^31 /\
((0 <= len /\ TX = p + 48) \/ (len < 0 /\ lencell = [C8 (Z_to_bv 64 TX)])) /\
(exists pn, In (p, pn) BS /\ 56 <= pn)) end.
{ destruct h.
- destruct Jc as (len & pd & pdn & str & junk2 & ER & Hlen & Hstr & Hpdn & C1 & C2).
destruct (first_nul_split2A str junk2) as (str0 & rest0 & E0 & NIN & L0).
exists pd, pd, pdn, len, str0, rest0, [C8 (Z_to_bv 64 pd)].
split; [rewrite EBS, ER; cbn; right; left; reflexivity|]. split; [lia|]. split; [lia|]. split; [exact NIN|]. split; [lia|].
split. { apply rw_cells_bytes_at in C2. cbn [cells_bytes cbytes app] in C2. rewrite app_nil_r in C2.
eapply bytes_at_cstr_prefix2A; [exact C2 | exact E0]. }
split. { unfold jhdr_cells in C1. cbn [app] in C1. apply rw_cells_app with (cs1 := [_;_;_;_;_;_]) in C1 as [_ C1]. cbn [cells_size csize Nat.add] in C1. change (p + Z.of_nat 40) with (p + 40) in C1. exact C1. }
split; [lia|]. split; [right; split; [lia | reflexivity]|]. exists 56. split; [rewrite EBS, ER; cbn; left; reflexivity | lia].
- destruct Jc as (len & str & junkS & ER & Hlen & Hstr & C1).
destruct (first_nul_split2A str junkS) as (str0 & rest0 & E0 & NIN & L0).
exists (p + 48), p, (str_objsize len), len, str0, rest0, [CB (Z.to_nat (str_objsize len - 48)) (str ++ [Z_to_bv 8 0] ++ junkS)].
split; [rewrite EBS, ER; cbn; left; reflexivity|]. split; [lia|]. split; [unfold str_objsize; lia|]. split; [exact NIN|]. split; [lia|].
unfold jhdr_cells in C1. cbn [app] in C1. apply rw_cells_app with (cs1 := [_;_;_;_;_;_]) in C1 as [_ C1]. cbn [cells_size csize Nat.add] in C1. change (p + Z.of_nat 40) with (p + 40) in C1.
split. { pose proof C1 as C2. apply rw_cells_app with (cs1 := [_]) in C2 as [_ C2]. cbn [cells_size csize Nat.add] in C2.
apply rw_cells_bytes_at in C2. cbn [cells_bytes cbytes app] in C2. rewrite app_nil_r in C2.
change (p + 40 + Z.of_nat 8) with (p + 40 + 8) in C2. replace (p + 40 + 8) with (p + 48) in C2 by lia. eapply bytes_at_cstr_prefix2A; [exact C2 | exact E0]. }
split; [exact C1|]. split; [lia|]. split; [left; split; [lia | reflexivity]|]. exists (str_objsize len). split; [rewrite EBS, ER; cbn; left; reflexivity | unfold str_objsize; lia]. }
clear Jc. destruct TXT as (TX & TB & TBN & len & str0 & rest0 & lencell & INT & TLO & THI & NIN & LS0 & BY & LENC & Hlen & ALT & (pn & INpn & Hpn)).
assert (INTA : In (TB, TBN) ((BS ++ LB) ++ LM)) by (apply in_or_app; left; apply in_or_app; left; exact INT).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ TB TBN HPc INTA) as (_ & _ & Htlo & Hthi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ TB TBN HPc INTA) as Htimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Htimg.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HPc INF INTA) as DFT. rewrite fr_size_0 in DFT.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ TB TBN HPc INTA) as APT. cbn [hl_sb A4L] in APT. unfold A_SB in APT.
assert (INpnA : In (p, pn) (BS ++ LB)) by (apply in_or_app; left; exact INpn).
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p pn 6 HPc INpnA ltac:(lia) ltac:(lia)) as SH6. replace (p / 8 + 2147450880 + 6) with (p / 8 + 2147450886) in SH6 by lia.
apply rw_cells_app with (cs1 := [_]) in LENC as [LEN1 LEN2]. cbn [cells_size csize Nat.add] in LEN2. change (p + 40 + Z.of_nat 8) with (p + 40 + 8) in LEN2. replace (p + 40 + 8) with (p + 48) in LEN2 by lia.
step. asan_chkA. step. step. step.

lazymatch goal with |- evt _ ?Q (MS ?r ?Fx ?pc ?fcx None ?mc ?rom) =>
let r' := open_constr:(mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in unify r r';
lazymatch r' with mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31 =>
assert (CONT : forall xa0 xa1 : word, evt asegs Q
(MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 xa0 xa1 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 TX) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
(bvmap_set 8 (Z_to_bv 64 0) Fx) (Z_to_bv 64 0x9e034) fcx None mc rom))
end end.
2:{ destruct ALT as [[Hl ETX] | [Hl ->]].
+  if_falsex. step. step. rewrite <- ETX. apply CONT.
+  if_truex. asan_chkA. step. step. apply CONT. }
intros xa0 xa1.

pose proof (RTC_LCONV _ _ _ _ _ _ _ HPc) as LCC. apply ro_C8_of_bytes_at in LCC. unfold A_LCONV, A_DPSTR in LCC.
lazymatch type of HPc with HEAPA _ _ _ _ _ _ _ ?mc _ =>
assert (SHL : ro_cells asegs mc 2147568522 [C1 (Z_to_bv 8 0)]);
[ apply QsKa.Mq1.ro_C1_of_bytes_at;
pose proof (heapA_shadow_img A4L HIx _ _ _ _ _ _ _ (0xe5c50 / 8) HPc) as X;
assert (E : img_shadow_val (hl_reg_globals A4L) (0xe5c50 / 8) = 0) by (vm_compute; reflexivity); rewrite E in X;
cbn [hl_sb A4L hl_img_lo hl_img_hi hla_base A4H] in X; unfold A_SB in X;
specialize (X ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate));
change (0xe5c50 / 8 + 2147450880) with 2147568522 in X; exact X |];
assert (SHD : ro_cells asegs mc 2147461387 [C1 (Z_to_bv 8 0)]);
[ apply QsKa.Mq1.ro_C1_of_bytes_at;
pose proof (heapA_shadow_img A4L HIx _ _ _ _ _ _ _ (0x1485d / 8) HPc) as X;
assert (E : img_shadow_val (hl_reg_globals A4L) (0x1485d / 8) = 0) by (vm_compute; reflexivity); rewrite E in X;
cbn [hl_sb A4L hl_img_lo hl_img_hi hla_base A4H] in X; unfold A_SB in X;
specialize (X ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate));
change (0x1485d / 8 + 2147450880) with 2147461387 in X; exact X |];
assert (DPB : ro_cells asegs mc 0x1485d [CB 2 [Z_to_bv 8 46; Z_to_bv 8 0]]);
[ change 2%nat with (length [Z_to_bv 8 46; Z_to_bv 8 0]); apply ro_cells_image; [assumption | vm_compute; reflexivity | lia | cbn; lia] |]
end.
step. step. step. step.
step. step. step. step. rewrite ?zxb_zero, ?sxb_zero. if_false.
step. step. if_false.
step. step. step. step. rewrite ?zxb_zero, ?sxb_zero. if_false.
step. step. step.
if_lit.
step. step. step.
eapply evt_cut; [eapply ERRNOL; reflexivity |]. intros ms9 ->.
replace (ret_pc (Z_to_bv 64 0x9e094)) with (Z_to_bv 64 0x9e094) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
unfold A_ERRNO, A_TP. change (6434400 - 164) with 6434236.
step. step. step. step. rewrite ?sxb_zero. step. if_false.
step. stepz. step. step. step.

set (txtZ := map bv_unsigned str0 ++ [0]).
assert (FA : Forall (fun c => 0 <= c < 256) (map bv_unsigned str0)).
{ apply Forall_map. apply Forall_forall. intros b _. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia. }
destruct (SCANH (map bv_unsigned str0) FA) as (bits & used & SCAN & U0).
assert (LTX : zlength txtZ = Z.of_nat (length str0) + 1) by (unfold zlength, txtZ; rewrite length_app, length_map; cbn [length]; lia).
assert (LPRE : zlength (map bv_unsigned str0) = Z.of_nat (length str0)) by (unfold zlength; rewrite length_map; reflexivity).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m1' mc, WMc : wmono asegs m1' mc, MIc : mem_inv asegs mc |- _ =>
pose proof (XHPg A1 B md1 m1' mc HP1 MUc WMc MIc) as HPs;
pose proof (XPD m1' mc PD1 A1 md1 B HP1 MUc WMc) as PDs end end.
destruct (heapA_canary A4L HIx _ _ _ _ _ _ _ HPs) as (g & CAN1 & CAN2 & _). cbn [hl_got_guard hl_guard A4L A4H hla_base] in CAN1, CAN2.
pose proof (frame_above_img HIx _ _ _ _ _ _ _ _ _ HP1 INF) as HFhi. cbn [hl_img_hi A4H] in HFhi.
pose proof (hiA_top_le A4L HIx) as HT47.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => rename mX into mS end.
eapply evt_cut.
{ eapply STRTOD with (T := TX) (PE := Fr + 32) (txt := txtZ) (pre := map bv_unsigned str0) (post := []) (lo := lo) (bits := bits) (used := used) (canary := g).
- unfold txtZ. rewrite map_app. cbn [map]. rewrite map_unsigned_bytesA. exact BY.
- unfold txtZ. apply Forall_app. split; [exact FA | constructor; [lia | constructor]].
- reflexivity.
- rewrite LPRE. lia.
- rewrite LTX. lia.
- exact FFe.
- exact SCAN.
- rewrite unsigned_lit by lia. eassumption.
- rewrite unsigned_lit by lia. unfold ASTRTOD_DEPTH. lia.
- lia.
- rewrite unsigned_lit by lia. lia.
- lia.
- rewrite LTX. lia.
- rewrite unsigned_lit by lia. left. rewrite LTX. split; [lia | lia].
- lia.
- lia.
- rewrite unsigned_lit by lia. left. lia.
- rewrite LTX. lia.
- exact CAN1.
- exact CAN2.
- unfold A_TP. eassumption.
- assumption.
- exact FRM.
- reflexivity.
- reflexivity.
- reflexivity. }
cbv beta delta [astrtod_post]. rewrite !(unsigned_lit (bv_unsigned sp + -128)) by lia. unfold A_TP. change (6434400 - 164) with 6434236. change (6434400 - 160) with 6434240.
post_call asegs mS.
step. step.

lazymatch goal with FRq : rw_cells asegs _ (bv_unsigned sp + -128) ?frc, FSHq : rw_cells asegs _ sh ?shc, FFq : rw_cells asegs _ Fr ?ffc |- _ =>
assert (KFREE : forall (retpc : Z) (F2 : bvmap 5 word) (fc2 : bv 32) (mc : word -> option byte) (ec : word)
(kt0 kt1 kt2 ka1 ka2 ka3 ka4 ka5 ka6 ka7 kt3 kt4 kt5 kt6 : word),
(retpc = 0x9e0e4 \/ retpc = 0x9e108 \/ retpc = 0x9e14c) ->
(forall k, In k FSAVED -> k <> 8 -> reg_get F2 (Z_to_bv 5 k) = reg_get F (Z_to_bv 5 k)) -> (frm0 fc -> frm0 fc2) ->
mem_inv asegs mc -> munch [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6434236, 6434240)] m1' mc -> wmono asegs m1' mc ->
rw_cells asegs mc (bv_unsigned sp + -128) frc -> rw_cells asegs mc sh shc -> rw_cells asegs mc Fr ffc ->
rw_cells asegs mc 6434236 [C4 ec] -> stk asegs mc lo (bv_unsigned sp + -128) ->
evt asegs (AJ5e A4L HIx A1 T md1)
(MS (mkR (Z_to_bv 64 retpc) (Z_to_bv 64 (bv_unsigned sp + -128)) gp (Z_to_bv 64 6434400) kt0 kt1 kt2 sp (Z_to_bv 64 (bv_unsigned sp + -128))
(Z_to_bv 64 0) ka1 ka2 ka3 ka4 ka5 ka6 ka7
(Z_to_bv 64 Fr) (Z_to_bv 64 6434236) (Z_to_bv 64 0) (Z_to_bv 64 TX) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 2148255159) (Z_to_bv 64 sh) (Z_to_bv 64 Fr)
(Z_to_bv 64 2147450880) (Z_to_bv 64 2147461387) kt3 kt4 kt5 kt6)
F2 (Z_to_bv 64 0x632c4) fc2 None mc (seg_rom asegs))) end.
{ intros retpc F2 fc2 mc ec kt0 kt1 kt2 ka1 ka2 ka3 ka4 ka5 ka6 ka7 kt3 kt4 kt5 kt6 Hret FS2 FRM2 MIc MUc WMc FRc FSHc FFc ERRc STc.
pose proof (XHPg A1 B md1 m1' mc HP1 MUc WMc MIc) as HPf.
pose proof (XPD m1' mc PD1 A1 md1 B HP1 MUc WMc) as PDf.
evt_done5.
eapply (hiA_free A4L HIx) with (p := 0) (u := UWpaid) (lo := lo) (errv := ec);
[ exact HPf | left; reflexivity | rewrite unsigned_lit by lia; exact STc | exact LO | rewrite unsigned_lit by lia; cbn [hl_stack_A A4L]; lia
| rewrite unsigned_lit by lia; clear - SPA; Z.div_mod_to_equations; lia | rewrite unsigned_lit by lia; lia | exact ERRc | reflexivity | reflexivity
| split; cbn; exact I | exact BB | cbn; exact BD | ].
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3.
cbn [hl_segs hl_tp hla_base A4L A4H Z.eqb] in ST3, HPR3, ERR3, HP3. unfold A_TP in ERR3. change (6434400 - 164) with 6434236 in ERR3.
rewrite ?(unsigned_lit (bv_unsigned sp + -128)) in ST3, HPR3 by lia.
assert (Enot : forall n, ~ In (0, n) (BS ++ LB)).
{ intros n0 Hin. pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ 0 n0 HPf (in_or_app _ LM _ (or_introl Hin))) as (_ & _ & H0 & _). lia. }
rewrite (lb_remove_notinA 0 _ Enot) in HPR3, HP3.
set (B3 := charge B 512 0) in *.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FRc; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FFc; [| eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; cbn [fr_ivs flat_map app fr_base fr_class fst snd]; left; reflexivity | lia | cbn [blk_addr blk_size fst snd]; rewrite fr_size_0; cbn; lia]].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FSHc; [| eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; cbn [fr_ivs flat_map app fr_base fr_class fst snd]; right; left; reflexivity | unfold shad; cbn [blk_addr blk_size fst snd hl_sb A4L]; unfold A_SB; fold sh; lia | unfold shad; cbn [blk_addr blk_size fst snd hl_sb A4L]; rewrite fr_shadow_len_0; unfold A_SB; fold sh; cbn; lia]].
change (hl_segs A4H) with asegs in FRc, FFc, FSHc.
assert (PD3 : heap_presD (Fr + 32) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m3).
{ eapply heap_presD_trans; [exact PDf |].
eapply heap_presD_weaken; [eapply (heap_presD_of_pres (Fr + 32)); [exact HPR3 | apply Z.le_refl] | lia |].
intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. rewrite app_assoc. apply in_or_app.
destruct Hb as [Hb|Hb]; [left; exact Hb | right; cbn [fr_ivs flat_map app]; right; right; exact Hb]. }
assert (VM13 : model_vm_only (cfg_model md) (cfg_model md3)) by (eapply model_vm_only_trans; [exact VM1 | exact VM3]).
assert (CH3 : jo_chargeA 512 0 B B3) by (unfold jo_chargeA, B3, charge; cbn [bB bD]; split; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI3. change (hl_segs A4L) with asegs in MI3.
assert (SHE3 : ro_cells asegs m3 2148255159 [C1 (Z_to_bv 8 0)]).
{ apply QsKa.Mq1.ro_C1_of_bytes_at.
pose proof (heapA_shadow_img A4L HIx _ _ _ _ _ _ _ (6434236 / 8) HP3) as X.
assert (E : img_shadow_val (hl_reg_globals A4L) (6434236 / 8) = 0) by (vm_compute; reflexivity). rewrite E in X.
cbn [hl_sb A4L hl_img_lo hl_img_hi hla_base A4H] in X. unfold A_SB in X.
specialize (X ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
change (6434236 / 8 + 2147450880) with 2148255159 in X. exact X. }
clear MU WM. pose proof (wmono_refl asegs m3) as WM. pose proof (munch_refl [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6434236, 6434240)] m3) as MU.
reenterA asegs A4L HIx asegs_wx HP3.
destruct Hret as [-> | [-> | ->]].
-
replace (ret_pc (Z_to_bv 64 647396)) with (Z_to_bv 64 647396) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
step. rewrite ?sxb_zero. step. if_true. step. step. step. step.
gd_exit EPI XHPg XPD PD3 HP3 A3 md3 B3 m3 VM13 CH3.
-
replace (ret_pc (Z_to_bv 64 647432)) with (Z_to_bv 64 647432) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
step. rewrite ?sxb_zero. step. if_false. step. step. step. step.
gd_exit EPI XHPg XPD PD3 HP3 A3 md3 B3 m3 VM13 CH3.
-
replace (ret_pc (Z_to_bv 64 647500)) with (Z_to_bv 64 647500) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
step.
gd_exit EPI XHPg XPD PD3 HP3 A3 md3 B3 m3 VM13 CH3. }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m1' mc, WMc : wmono asegs m1' mc, MIc : mem_inv asegs mc |- _ =>
pose proof (XHPg A1 B md1 m1' mc HP1 MUc WMc MIc) as HPx end end.
pose proof (unpoisoned_of_blk HIx _ _ _ _ _ _ _ TB TBN TX (Z.of_nat (length str0) + 1) HPx ltac:(apply in_or_app; left; exact INT) ltac:(lia) ltac:(lia) ltac:(lia)) as UNS.
rewrite LPRE in POST.
rename x14 into F5. rename x15 into fc5. rename x16 into m5. rename x17 into e5.
assert (FS5 : forall k, In k FSAVED -> k <> 8 -> reg_get F5 (Z_to_bv 5 k) = reg_get F (Z_to_bv 5 k)).
{ intros k Hk NE. cbn [FSAVED In] in Hk.
repeat (destruct Hk as [<- | Hk]); [..| destruct Hk]; first [exfalso; apply NE; reflexivity | idtac];
(rewrite PC0 by (vm_compute; lia)); rewrite !freg_get_other by (vm_compute; reflexivity); reflexivity. }
destruct (Z.eq_dec used 0) as [U0' | UN0].
+
rewrite U0' in *. replace (TX + 0) with TX by lia. if_truex. step. step.
eapply (KFREE 0x9e108 F5 fc5 m5 e5); [right; left; reflexivity | exact FS5 | intros _; exact PC | assumption | assumption | assumption | eassumption | eassumption | eassumption | eassumption | eassumption].
+
if_falsex.
assert (UNk : unpoisoned asegs m5 A_SB (TX + used) 1)
by (eapply (QsKa.Mq1.unpoisoned_sub_any asegs _ A_SB TX (Z.of_nat (length str0) + 1)); [exact UNS | lia | lia | lia]).
destruct (unpoisoned_last asegs _ _ _ _ UNk) as (v & SHk & Hv).
replace (TX + used + 1 - 1) with (TX + used) in SHk, Hv by lia. unfold A_SB in SHk.
assert (HL : (Z.to_nat used < length (map (Z_to_bv 8) txtZ))%nat) by (rewrite length_map; unfold txtZ; rewrite length_app, length_map; cbn [length]; lia).
destruct (nth_error (map (Z_to_bv 8) txtZ) (Z.to_nat used)) as [bu|] eqn:Hbu; [| exfalso; apply nth_error_None in Hbu; lia].
pose proof (bv_unsigned_in_range 8 bu) as BUR. unfold bv_modulus in BUR. cbn in BUR.
pose proof (string_byteG asegs _ TX _ used bu PC4 Hbu ltac:(lia)) as RDU.
lazymatch goal with |- evt _ ?Q (MS ?r ?Fx ?pc ?fcx None ?mc ?rom) =>
let r' := open_constr:(mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in unify r r';
lazymatch r' with mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31 =>
assert (CONT2 : forall ya1 ya2 : word, evt asegs Q
(MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ya1 ya2 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Fx (Z_to_bv 64 0x9e0d4) fcx None mc rom))
end end.
2:{ step. step. sh_norm. step. step.
destruct Hv as [-> | [Hv8 Hvm]].
- rewrite sxb_zero. if_false. apply CONT2.
- rewrite (QsKa.Mq1.sxb_small v) by lia. if_truex. step. step.
rewrite (unsigned_lit (TX + used)) by lia. rewrite QsKa.Mq1.land7_mod8 by lia. if_truex. apply CONT2. }
intros ya1 ya2.
step. unfold zxb. step.
destruct (Z.eq_dec (bv_unsigned bu) 0) as [BZ | BNZ].
*
rewrite BZ. if_truex.
step. step. step.
match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c end.
-- step. step. step.
eapply (KFREE 0x9e14c _ fc5 m5 e5); [right; right; reflexivity | gd_fs_tail | intros _; exact PC | assumption | assumption | assumption | eassumption | eassumption | eassumption | eassumption | eassumption].
-- step. rewrite ?sxb_zero. step. if_false. step. step. step.
match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c end.
++ step. step. step.
eapply (KFREE 0x9e14c _ fc5 m5 e5); [right; right; reflexivity | gd_fs_tail | intros _; exact PC | assumption | assumption | assumption | eassumption | eassumption | eassumption | eassumption | eassumption].
++ step. step. step. step.
eapply (KFREE 0x9e14c _ fc5 m5 e5); [right; right; reflexivity | gd_fs_tail | intros _; exact PC | assumption | assumption | assumption | eassumption | eassumption | eassumption | eassumption | eassumption].
*
if_falsex. step. step.
eapply (KFREE 0x9e0e4 F5 fc5 m5 e5); [left; reflexivity | exact FS5 | intros _; exact PC | assumption | assumption | assumption | eassumption | eassumption | eassumption | eassumption | eassumption].
-
step. step. if_lit. step. step. if_lit.
step. step.
eapply evt_cut; [eapply ERRNOL; reflexivity |]. intros ms9 ->.
replace (ret_pc (Z_to_bv 64 0x9df7c)) with (Z_to_bv 64 0x9df7c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
unfold A_ERRNO, A_TP. change (6434400 - 164) with 6434236.
step. step. step. rewrite ?sxb_zero. step. if_false.
step. step. step. step.
gd_exit EPI XHPg XPD PD1 HP1 A1 md1 B m1' VM1 CH0.
-
step. step. if_lit. step. step. if_lit.
step. step.
eapply evt_cut; [eapply ERRNOL; reflexivity |]. intros ms9 ->.
replace (ret_pc (Z_to_bv 64 0x9df7c)) with (Z_to_bv 64 0x9df7c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
unfold A_ERRNO, A_TP. change (6434400 - 164) with 6434236.
step. step. step. rewrite ?sxb_zero. step. if_false.
step. step. step. step.
gd_exit EPI XHPg XPD PD1 HP1 A1 md1 B m1' VM1 CH0.
Qed.
End MJoGetDouble.
End RC__1.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI QSHS Qc5u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw QkMG. Import QG8z Qdyh.Mq3 Qdyh.Mq4.
Import Qhd4 Qwm6.
Import QbFI Qwm6.Mq4 QlKV.Mqi QsKa.Mqd Qiiq QSHS Ql4f.Mq4 QsKa.Mqh QrQv.Mq4 Qc5u.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSOsepA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Let PRW := PE_REST_A_private_write HIx GA GA_outside.

Ltac pe_openA STC INV :=
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR); pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk);
destruct INV as [CORE REST];
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR);
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD).

Lemma seg_osep_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z)
(gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_osep ->
t_co ts < pf_len pf ->

(forall m' ss' a1' a4' a5',
(bv_unsigned cb = 44 /\ ss' = ST_ofs_after_sep) \/ (bv_unsigned cb = 125 /\ ss' = ST_finish) ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B
(Qdyh.Mq4.ts_set_level ts (TL ST_eatws ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv ->
PBOK m' (Qdyh.Mq4.ts_set_level ts (TL ST_eatws ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) kP ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp t0 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a1' (Z_to_bv 64 0) (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a4' a5' (Z_to_bv 64 APE_JTAB) a7 s3 (Z_to_bv 64 2) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m')) ->

(forall a5',
bv_unsigned cb <> 44 -> bv_unsigned cb <> 125 ->
AJ5 A4L HIx A T md
(pe_msO asegs pf pa APE_ERR3 gp t0 (Z_to_bv 64 (pf_lenr pf)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 11) (Z_to_bv 64 (bv_unsigned cb)) (Z_to_bv 64 0) (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) a5' (Z_to_bv 64 APE_JTAB) a7 s3 (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m)) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA ST_osep) (t_co ts) gp t0 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l)) (Z_to_bv 64 0) (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) a5 (Z_to_bv 64 APE_JTAB) a7 s3 (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC INV PBK Hl Hst Hco Kbreak Kerr. pose proof INV as INV0. pe_openA STC INV.
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
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 4 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEP4c & SEP4q & SEP4i). cbn [hl_sb A4L] in SEP4c, SEP4q, SEP4i.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + SB4) in SHT4 by (unfold SB4, A_SB; lia).
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
unfold APE_BREAK, APE_EATBRK, APE_ERR3, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (MODE0 : c0 = CObj /\ hn0 = false).
{ rewrite Hst in Hmode. unfold ST_osep in Hmode. clear - Hmode SS26.
assert (R : 0 <= tl_ss l <= 26) by lia. enum_z R (tl_ss l); vm_compute in Hmode; split; congruence. }
destruct MODE0 as [-> ->].
stash Himg_t. stash Himg_q. clear PB REST TSK HP LV OBJ HPR BUD GAP SAVED FSH.
reenterA asegs A4L HIx asegs_wx HP. rewrite Hst. unfold ST_osep. cbn [pe_jtA].
replace (q + 32 * Z.of_nat depth) with bse by lia.
step. step.
change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)).
step.
destruct (Z.eq_dec (bv_unsigned cb) 44) as [C44 | N44].
- step. if_truex.
step.
asan_chkB.
step. step.
stepz.
step.
if_true.
step. rewrite ?sxb_zero, ?zxb_zero. step. if_true.
stepz.
step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5; subst bse;
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv l ST_eatws ST_ofs_after_sep _ _ CObj STC INV0 Hl MUc WMc MIc TOKc Lc Hmode ltac:(vm_compute; reflexivity) ltac:(unfold ST_eatws; lia) ltac:(unfold ST_ofs_after_sep; lia)
(or_introl eq_refl) ltac:(rewrite Hst; vm_compute; reflexivity)) as [INV3 PBK3];
eapply (Kbreak mc ST_ofs_after_sep _ _ _ ltac:(left; split; [exact C44 | reflexivity])); [exact INV3 | exact (PBK3 kP PBK)]
end end.
- step. if_falsex.
step.
destruct (Z.eq_dec (bv_unsigned cb) 125) as [C125 | N125].
+ step. if_truex.
step.
asan_chkB.
step. step.
stepz.
step. if_true.
step. rewrite ?sxb_zero, ?zxb_zero. step. if_true.
stepz.
step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5; subst bse;
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv l ST_eatws ST_finish _ _ CAny STC INV0 Hl MUc WMc MIc TOKc Lc Hmode ltac:(vm_compute; reflexivity) ltac:(unfold ST_eatws; lia) ltac:(unfold ST_finish; lia)
(or_intror eq_refl) ltac:(rewrite Hst; vm_compute; reflexivity)) as [INV3 PBK3];
eapply (Kbreak mc ST_finish _ _ _ ltac:(right; split; [exact C125 | reflexivity])); [exact INV3 | exact (PBK3 kP PBK)]
end end.
+ step. if_falsex.
step. step. step. rewrite ?sxb_zero, ?zxb_zero. step. if_true.
step. step.
evt_done5.
subst bse. eapply Kerr; [exact N44 | exact N125].
Qed.
End PeSOsepA.
End RC__1.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0. Import QTEu. Import Qsw7 QJjn QRUw QRUw.Mq0.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj Q4v2 QgHv Q1Y6 QsKa.Mqf. Import QlKV.Mq2 QsKa. Import Q9O6.Mq5.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
Local Ltac flia := Qo9G.term_slim ltac:(Zify.zify; xlia zchecker).

Lemma costX_le_potential : forall cap bpos n CAPB, 32 <= cap -> 0 <= bpos -> 0 <= n ->
Z.max (2 * cap) (bpos + n + 9) <= CAPB -> cap <= bpos + n + 1 ->
16 * Z.max (2 * cap) (bpos + n + 9) + 512 <= 64 * (CAPB - cap).
Proof. intros. flia. Qed.
Lemma grow_le_potential : forall cap bpos n, 32 <= cap -> 0 <= bpos -> 0 <= n -> cap <= bpos + n ->
16 * Z.max (2 * cap) (bpos + n + 9) + 512 <= 64 * (Z.max (2 * cap) (bpos + n + 9) - cap).
Proof. intros. flia. Qed.
Lemma grow_in_capb : forall cap0 bpos0 w cap bpos n, 0 <= bpos -> 0 <= n -> cap <= ser_capb cap0 bpos0 w -> bpos + n <= bpos0 + w -> cap <= bpos + n + 1 ->
Z.max (2 * cap) (bpos + n + 9) <= ser_capb cap0 bpos0 w.
Proof. intros. unfold ser_capb in *. flia. Qed.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section ASer.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Variables (sp gp : word) (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS0 : list frame) (B0 : bud) (pb lo : Z).
Variables (bpos0 cap0 w : Z).
Let usp := bv_unsigned sp.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis HT : usp <= hiA_top A4L HIx.
Hypothesis CAP0 : 32 <= cap0 < 2^30.
Hypothesis TXT : bpos0 + w < 2^28.
Hypothesis NEED : ser_need cap0 bpos0 w <= bB B0.
Hypothesis JHEX0 : JHEX_A m0.

Definition chunk_ok (FRSc : list frame) (FA : Z) (ch : Z * list cell) : Prop :=
client_range A4H (LB ++ LM ++ fr_ivs A4L FRSc) FA (fst ch) (Z.of_nat (cells_size (snd ch))).
Definition ser_memA (A : ASA A4L HIx) (FRSc : list frame) (FA : Z) (CH : list (Z * list cell)) (e : Z) (m : word -> option byte) (md : config) : Prop :=
exists (buf cap bpos : Z) (content : list byte) (errv : word) (B : bud),
HEAPAx A ((pb, PB_SZ) :: (buf, cap) :: LB) LM FRSc B m md /\
pbuf_core asegs m pb buf bpos cap content /\
Forall (fun ch => rw_cells asegs m (fst ch) (snd ch)) CH /\ Forall (chunk_ok FRSc FA) CH /\
(forall b, In b (fr_ivs A4L FRS0) -> In b (fr_ivs A4L FRSc)) /\
rw_cells asegs m A_ERRNO [C4 errv] /\
stk asegs m lo FA /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS0) usp m0 m /\ model_vm_only (cfg_model md0) (cfg_model md) /\
(bpos0 <= bpos <= bpos0 + e) /\ (cap0 <= cap <= ser_capb cap0 bpos0 w) /\
bB B0 - 64 * (cap - cap0) <= bB B /\ bD B0 <= bD B.

Lemma ser_memA_mem_inv : forall A FRSc FA CH e m md, ser_memA A FRSc FA CH e m md -> mem_inv asegs m.
Proof. intros A FRSc FA CH e m md (buf & cap & bpos & content & errv & B & HP & _). exact (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP). Qed.

Lemma ser_memA_weaken_e : forall A FRSc FA CH e e' m md, e <= e' -> ser_memA A FRSc FA CH e m md -> ser_memA A FRSc FA CH e' m md.
Proof.
intros A FRSc FA CH e e' m md He (buf & cap & bpos & content & errv & B & HP & PB & C1 & C2 & FS & ERR & ST & HPR & VM & Hb & Hc & HB & HD).
exists buf, cap, bpos, content, errv, B. repeat (split; [assumption|]). split; [lia|]. repeat (split; [assumption|]). assumption.
Qed.

Lemma chunks_pres : forall FRSc FA CH m m', heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRSc) FA m m' ->
Forall (chunk_ok FRSc FA) CH -> Forall (fun ch => rw_cells asegs m (fst ch) (snd ch)) CH -> Forall (fun ch => rw_cells asegs m' (fst ch) (snd ch)) CH.
Proof.
intros FRSc FA CH m m' HPR OK. induction OK as [|ch CH Hch _ IH]; intros H; [constructor|].
inversion H as [|x l Hx Hl]; subst. constructor; [| apply IH; exact Hl].
eapply (heap_pres_rw_cells A4H); [exact HPR | exact Hx | exact Hch].
Qed.

Hypothesis OBL_REALLOC_NF : realloc_nf_stmt HIx.

Lemma ser_appendA :
forall (ret : Z) (x3 t0 t1 t2 x8 x9 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
(F Fc : bvmap 5 word) (fcc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (FRSc : list frame) (FA : Z) (CH : list (Z * list cell)) (e b k : Z) (sb : list byte),
ser_memA A FRSc FA CH e m md ->
bytes_at asegs m b sb -> Z.of_nat (length sb) = k -> 0 <= k < 2^31 -> 0 <= b ->
src_locA LB FRSc b k -> (0 < k -> unpoisoned asegs m A_SB b k) ->
0 <= e -> e + k <= w ->
lo <= FA - 112 - 4096 -> FA mod 16 = 0 -> FA <= usp -> 0 <= FA ->
x3 = gp -> 0 <= ret < 2^64 -> ret mod 2 = 0 ->
fsaved F Fc -> frm0 fcc ->
(forall (A' : ASA A4L HIx) m' md' (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) F' fc',
ser_memA A' FRSc FA CH (e + k) m' md' -> fsaved F F' -> frm0 fc' -> bytes_at asegs m' b sb ->
AJ5 A4L HIx A' T md' (MS (mkR (wz ret) (wz FA) gp (wz A_TP) t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7'
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6') F' (wz ret) fc' None m' (seg_rom asegs))) ->
AJ5 A4L HIx A T md (MS (mkR (wz ret) (wz FA) x3 (wz A_TP) t0 t1 t2 x8 x9 (wz pb) (wz b) (wz k) a3 a4 a5 a6 a7
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) Fc (wz AMEMAPPEND) fcc None m (seg_rom asegs)).
Proof.
intros until sb. intros INV SB SBL Hk Hb SRCB UPS He Hek LOS FAA FAU FA0 -> Hret Hret2 FS FRM K.
destruct INV as (buf & cap & bpos & content & errv & B & HP & PB & CHm & CHok & FSUB & ERR & ST & HPR & VM & Hbp & Hcap & HBB & HBD).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
assert (U2 : bv_unsigned (wz FA) = FA) by (apply unsigned_lit; unfold usp in *; lia).
pose proof PB as (Hb0 & Hsz & Hlen & _).
assert (CAPB : ser_capb cap0 bpos0 w < 2^30) by (unfold ser_capb; flia).
assert (POT : 64 * (ser_capb cap0 bpos0 w - cap) <= bB B) by (unfold ser_need in NEED; flia).
assert (COSTX : memappend_costX cap bpos k <= bB B).
{ unfold memappend_costX, memappend_costB. destruct (Z.leb_spec cap (bpos + k + 1)) as [G|NG].
- pose proof (grow_in_capb cap0 bpos0 w cap bpos k ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) G) as GC.
pose proof (costX_le_potential cap bpos k (ser_capb cap0 bpos0 w) ltac:(lia) ltac:(lia) ltac:(lia) GC G). lia.
- flia. }
unfold AMEMAPPEND.
eapply (memappend_A_cps_nf HIx OBL_REALLOC_NF) with (A := A) (LB := LB) (buf := buf) (bpos := bpos) (cap := cap) (b := b) (n := k)
(lo := lo) (content := content) (src := sb) (errv := errv);
rewrite ?U2.
- exact HP.
- exact PB.
- lia.
- exact SB.
- exact SBL.
- exact Hb.
- exact SRCB.
- exact UPS.
- exact ST.
- exact LO.
- lia.
- exact FAA.
- unfold usp in *. lia.
- exact ERR.
- reflexivity.
- rewrite unsigned_lit by lia. exact Hret2.
- reflexivity.
- reflexivity.
- reflexivity.
- exact COSTX.
- intros ms' md' A' POST.
destruct POST as (m' & r & errv' & buf' & cap' & B' & RS & VM' & ST' & HPR' & ERR' & HB1 & HD1 & HP' & OUT).
destruct RS as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F' & fc' & -> & FS' & FR').
rewrite U2 in ST', HPR'.
replace (ret_pc (wz ret)) with (wz ret) by (symmetry; apply ret_pc_even; [lia | exact Hret2]).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP') as MI'.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
assert (SB' : bytes_at asegs m' b sb).
{ eapply (src_loc_bytes_pres _ LB LM FRSc); [exact HPR' | exact MI | exact MI' | intros bb Hbb; exact Hbb | rewrite SBL; exact SRCB | exact SB]. }
apply K; [| eapply fsaved_trans; [exact FS | exact FS'] | exact (FR' FRM) | exact SB'].
assert (OUT' : exists bpos' content', pbuf_core asegs m' pb buf' bpos' cap' content' /\ bpos <= bpos' <= bpos + k
/\ cap <= cap' <= ser_capb cap0 bpos0 w /\ bB B - 64 * (cap' - cap) <= bB B').
{ destruct OUT as [(_ & -> & PBF) | (_ & -> & -> & HNC & PBC)].
- destruct PBF as (bufq & bposq & sizeq & post & E & L & C). injection E as <- <-.
exists bposq, ((firstn (Z.to_nat bpos) content ++ sb) ++ [Z_to_bv 8 0] ++ post). split; [exact C|].
assert (Lq : bposq = bpos + k).
{ rewrite <- L, length_app, length_firstn. rewrite Nat.min_l by lia. lia. }
split; [lia|]. unfold memappend_cap2, memappend_costX2, memappend_costB in *.
destruct (Z.leb_spec cap (bpos + k)) as [G|NG].
+ replace (cap <? 2^30) with true by (symmetry; apply Z.ltb_lt; lia).
pose proof (grow_in_capb cap0 bpos0 w cap bpos k ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as GC.
pose proof (grow_le_potential cap bpos k ltac:(lia) ltac:(lia) ltac:(lia) G). split; [flia | lia].
+ split; lia.
- exists bpos, content. split; [exact PBC|]. split; [lia|]. split; [lia | lia]. }
destruct OUT' as (bpos' & content' & PB' & Hbp' & Hcap' & HCX).
exists buf', cap', bpos', content', errv', B'.
split; [exact HP'|]. split; [exact PB'|].
split; [eapply chunks_pres; [exact HPR' | exact CHok | exact CHm]|]. split; [exact CHok|]. split; [exact FSUB|].
split; [exact ERR'|]. split; [exact ST'|].
split. { eapply heap_pres_trans; [exact HPR | eapply heap_pres_weaken; [exact HPR' | unfold usp in *; lia |]].
intros bb Hbb. apply in_app_or in Hbb. apply in_or_app. destruct Hbb as [Hbb|Hbb]; [left; exact Hbb | right].
apply in_app_or in Hbb. apply in_or_app. destruct Hbb as [Hbb|Hbb]; [left; exact Hbb | right; apply FSUB; exact Hbb]. }
split; [eapply model_vm_only_trans; [exact VM | exact VM']|].
split; [lia|]. split; [lia|]. split; [lia | lia].
Qed.

Lemma ser_childA :
forall (entry : Z) (s' : jshape), ser_specA HIx entry s' ->
forall (ret : Z) (x3 t0 t1 t2 x8 x9 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
(F Fc : bvmap 5 word) (fcc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (FRSc : list frame) (FA : Z) (CH : list (Z * list cell)) (e : Z)
(RESTc Yc Rc : list blk) (v rc' pbc lvc fl wc : Z),
ser_memA A FRSc FA CH e m md ->
jnode asegs A4F s' m RESTc v rc' pbc -> incl RESTc LB ->
jtx s' (RESTc ++ Yc) = Some (wc, Rc) ->
0 <= e -> e + wc <= w ->
aflags_ok fl -> 0 <= lvc -> lvc + sdepth s' <= 1000 ->
Z.of_nat (length FRSc) + 1 < 4096 ->
lo <= FA - ser_budgetA s' -> FA mod 16 = 0 -> FA <= usp -> 0 <= FA ->
x3 = gp -> 0 <= ret < 2^64 -> ret mod 2 = 0 ->
fsaved F Fc -> frm0 fcc ->
(forall (A' : ASA A4L HIx) m' md' (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) F' fc',
ser_memA A' FRSc FA CH (e + wc) m' md' -> fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A' T md' (MS (mkR (wz ret) (wz FA) gp (wz A_TP) t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7'
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6') F' (wz ret) fc' None m' (seg_rom asegs))) ->
AJ5 A4L HIx A T md (MS (mkR (wz ret) (wz FA) x3 (wz A_TP) t0 t1 t2 x8 x9 (wz v) (wz pb) (wz lvc) (wz fl) a4 a5 a6 a7
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) Fc (wz entry) fcc None m (seg_rom asegs)).
Proof.
intros entry s' SPEC. intros until wc. intros INV JN INCL JTX He Hew FL Hlv Hlvd FRN LOS FAA FAU FA0 -> Hret Hret2 FS FRM K.
destruct INV as (buf & cap & bpos & content & errv & B & HP & PB & CHm & CHok & FSUB & ERR & ST & HPR & VM & Hbp & Hcap & HBB & HBD).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
assert (U2 : bv_unsigned (wz FA) = FA) by (apply unsigned_lit; unfold usp in *; lia).
pose proof (jtx_nonneg _ _ _ _ JTX) as Hwc.
assert (CAPB : ser_capb cap0 bpos0 w < 2^30) by (unfold ser_capb; flia).
assert (NEEDc : ser_need cap bpos wc <= bB B).
{ eapply (ser_need_step cap0 cap bpos0 bpos w wc (bB B0) (bB B)); [exact Hcap | lia | exact NEED | exact HBB]. }
assert (JH : JHEX_A m) by (eapply JHEX_A_pres; [exact HPR | exact JHEX0]).
unfold ser_specA in SPEC.
eapply SPEC with (A := A) (LB := LB) (LM := LM) (FRS := FRSc) (B := B) (buf := buf) (bpos := bpos) (cap := cap) (lo := lo) (content := content) (errv := errv)
(REST := RESTc) (p := v) (rc := rc') (pb0 := pbc) (lv := lvc) (fl := fl) (w := wc) (Y := Yc) (R := Rc);
rewrite ?U2.
- exact HP.
- exact PB.
- exact JN.
- exact INCL.
- exact JTX.
- lia.
- lia.
- exact NEEDc.
- exact FL.
- exact Hlv.
- exact Hlvd.
- exact FRN.
- exact ST.
- exact LO.
- exact LOS.
- exact FAA.
- unfold usp in *. lia.
- exact ERR.
- exact JH.
- reflexivity.
- rewrite unsigned_lit by lia. exact Hret2.
- exact FRM.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- intros ms' md' A' POST.
destruct POST as (m' & r & errv' & buf' & cap' & bpos' & content' & B' & RS & VM' & ST' & HPR' & ERR' & HP' & PB' & Hbp' & Hcap' & HBB' & HBD').
destruct RS as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F' & fc' & -> & FS' & FR').
rewrite U2 in ST', HPR'.
replace (ret_pc (wz ret)) with (wz ret) by (symmetry; apply ret_pc_even; [lia | exact Hret2]).
apply K; [| eapply fsaved_trans; [exact FS | exact FS'] | exact (FR' FRM)].
pose proof (ser_capb_mono cap0 cap bpos0 bpos w wc Hcap ltac:(lia)) as MONO.
exists buf', cap', bpos', content', errv', B'.
split; [exact HP'|]. split; [exact PB'|].
split; [eapply chunks_pres; [exact HPR' | exact CHok | exact CHm]|]. split; [exact CHok|]. split; [exact FSUB|].
split; [exact ERR'|]. split; [exact ST'|].
split. { eapply heap_pres_trans; [exact HPR | eapply heap_pres_weaken; [exact HPR' | unfold usp in *; lia |]].
intros bb Hbb. apply in_app_or in Hbb. apply in_or_app. destruct Hbb as [Hbb|Hbb]; [left; exact Hbb | right].
apply in_app_or in Hbb. apply in_or_app. destruct Hbb as [Hbb|Hbb]; [left; exact Hbb | right; apply FSUB; exact Hbb]. }
split; [eapply model_vm_only_trans; [exact VM | exact VM']|].
split; [lia|]. split; [lia|]. split; [lia | lia].
Qed.
End ASer.
End RC__1.
End Mq4.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmZZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmZZ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6WR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6WR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6WR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6WR.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrPc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrPc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYIF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYIF.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgoP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgoP.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qx2n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qx2n.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXUB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXUB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRBl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRBl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJZd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJZd.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qw5U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qw5U.Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqf.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSHS.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qvmy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvmy. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLHv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLHv. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qawr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qawr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qw5U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qw5U.Mq8.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma map_unsigned_bytesA : forall bs : list byte, map (Z_to_bv 8) (map bv_unsigned bs) = bs.
Proof. induction bs as [|b bs IH]; [reflexivity|]. cbn. rewrite IH. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma lb_remove_notinA : forall p LB, (forall n, ~ In (p, n) LB) -> lb_remove p LB = LB.
Proof.
induction LB as [|[a n] LB IH]; intros H; [reflexivity|]. cbn [lb_remove blk_addr fst].
destruct (Z.eqb_spec a p) as [->|NE]; [exfalso; apply (H n); left; reflexivity|]. f_equal. apply IH. intros k Hk. apply (H k). right; exact Hk.
Qed.

Ltac gd_fs_tail := let k := fresh "k" in let Hk := fresh "Hk" in let NE := fresh "NE" in intros k Hk NE; cbn [FSAVED In] in Hk;
repeat (destruct Hk as [<- | Hk]); [..| destruct Hk];
first [ exfalso; apply NE; reflexivity
| rewrite ?freg_get_other by (vm_compute; reflexivity);
first [ reflexivity
| match goal with FS : forall k, In k FSAVED -> k <> 8 -> _ |- _ => apply FS; [cbn [FSAVED In]; repeat first [left; reflexivity | right] | lia] end ] ].

Ltac gd_exit EPI XHPg XPD PDb HPb Ab mdb Bb mb VMb CHb :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply (EPI mc Ab mdb Bb);
[ eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
| eapply (XHPg Ab Bb mdb mb mc HPb); assumption | exact VMb | eapply (XPD mb mc PDb Ab mdb Bb HPb); assumption
| exact CHb
| gd_fs_tail | first [intros Hf; exact Hf | intros _; assumption | assumption] ] end.

Section MJoGetDouble.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis ERRNOL : QlKV.Mqe.errno_location_A_stmt.
Hypothesis SCANH : scan_total_stmtA.
Hypothesis STRTOD : astrtod_total_stmt.

Lemma RTC_LCONV : rtc_lconv_stmt HIx.
Proof.
intros A LB LM FR B m md HP. unfold A_LCONV, A_DPSTR. apply (rtc_cell HIx _ _ _ _ _ _ _ _ _ HP). unfold a4_rt_consts.
repeat (first [left; reflexivity | right]).
Qed.

Lemma RTC_GDPC : forall A LB LM FR B m md, HEAPAx A LB LM FR B m md -> bytes_at asegs m 0xe8e68 (le8 (Z_to_bv 64 0x9f8e4)).
Proof.
intros A LB LM FR B m md HP. apply (rtc_cell HIx _ _ _ _ _ _ _ _ _ HP). unfold a4_rt_consts.
repeat (first [left; reflexivity | right]).
Qed.

Definition GD_STK_A : Z := 128 + ASTRTOD_DEPTH.

Lemma get_double_A : jo_get_double_A_stmt HIx 0x9f8e4 GD_STK_A 512 0.
Proof.
unfold jo_get_double_A_stmt. intros until errv. intros (HP & ST & LO & LOS & SPA16 & HT & ERR & TP & RA) JO FRN BB BD SPA FRM A0 K.
unfold GD_STK_A, ASTRTOD_DEPTH in LOS. subst a0 tp.
assert (FRMfp : Qc3B.frm0 fc) by exact FRM.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof alloc_ceiling_range as ACR.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HP) as (SB1 & SB2 & SB3 & SB4).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2. apply ro_C8_of_bytes_at in SB3.
assert (UARC : ro_cells asegs m (hl_uar_cell A4L) [C4 (Z_to_bv 64 1)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SB4]).
clear SB4. a4l.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)] m) as MU.
unfold A_ERRNO, A_TP in *.
stash ERR.
reenterA asegs A4L HIx asegs_wx HP.
carve_frame 128%nat ST.
bstep. bstepz. do 13 bstep.
bstep.
bstep. bstep.
rewrite (unsigned_lit (bv_unsigned sp + -128)) by lia. change 18446744073709551584 with (2^64 - 2^5). rewrite OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.land_align_down by lia. change (2^5) with 32.
replace (bv_unsigned sp + -128 - (bv_unsigned sp + -128) mod 32) with (bv_unsigned sp + -128) by (clear - SPA; Z.div_mod_to_equations; lia).
bstep. bstep. bstep. bstep. bstep. bstep. bstep. bstep.
norm_sx32. bstep. if_false. bstep. bstep.
evt_done5.
eapply (stack_malloc_full HIx) with (k := 0) (bytes := 64) (lo := lo) (LB := BS ++ LB) (LM := LM) (FR := FRS) (B := B);
[ heap_nowA A4L HIx HP MU WM MI | lia | .. ].
all: rewrite ?unsigned_lit by lia.
1: rewrite fr_size_0; lia.
1: reflexivity.
1: lia.
1: exact ST.
1: exact LO.
1: cbn [hl_stack_A A4L]; lia.
1: clear - SPA; Z.div_mod_to_equations; lia.
1: lia.
1: reflexivity.
1: reflexivity.
intros ms1 m1' md1 A1 Fr RS1 VM1 ST1 HPR1 FRNZ (jff & FF1) SHB1 HP1. open_ret RS1.
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HP1) as (errv1 & ERR1). unfold A_ERRNO, A_TP in ERR1. cbn [hl_tp A4L A4H hla_base] in ERR1.
rewrite ?unsigned_lit in ST1, HPR1 by lia.
clear ERR.
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as (_ & HFal & HF0 & HFc & HFimg & _ & HFshw & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as HFapp.
rewrite fr_size_0 in HFal, HFc, HFimg, HFapp. rewrite fr_shadow_len_0 in HFshw. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFimg, HFapp.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in FR; [| left; cbn; lia].
clear SB1 SB2 SB3 UARC.
pose proof (RTC_GDPC _ _ _ _ _ _ _ HP1) as PCC. apply ro_C8_of_bytes_at in PCC.
assert (FSH1 : rw_cells asegs m1' (shad A4L Fr) [CB 8 (repeat (Z_to_bv 8 0) 8)]).
{ split; [split; [cbn; split; [reflexivity | exact I] | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SHB1] | exact HFshw]. }
rewrite fr_size_0 in FF1. change (Z.to_nat (64 - 8)) with 56%nat in FF1.
unfold shad in FSH1. a4l.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 8 <= 17594333495296) by (unfold sh; clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI1. change (hl_segs A4L) with asegs in MI1. clear MI.
rename MU into MU0. rename WM into WM0. pose proof (wmono_refl asegs m1') as WM. pose proof (munch_refl [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6444156, 6444160)] m1') as MU.
change (6444320 - 164) with 6444156 in ERR1.
unfold A_SB in HFapp.
reenterA asegs A4L HIx asegs_wx HP1.
bstep. bstep. bstep. if_truex.
bstepz.
bstep. bstep. bstep. bstep.
rewrite (unsigned_lit Fr) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
bstep. bstep. bstep. bstepz. bstepz. bstepz. bstep. bstep.
fold sh.
bstepz. bstepz. bstepz. bstepz. bstep. bstepz. bstepz. bstepz. bstepz.
bstepz.
bstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (SHE : ro_cells asegs mc 2148256399 [C1 (Z_to_bv 8 0)]) end.
{ apply QsKa.Mqa.ro_C1_of_bytes_at.
pose proof (heapA_shadow_img A4L HIx _ _ _ _ _ _ _ (6444156 / 8) HP1) as X.
assert (E : img_shadow_val (hl_reg_globals A4L) (6444156 / 8) = 0) by (vm_compute; reflexivity). rewrite E in X.
cbn [hl_sb A4L hl_img_lo hl_img_hi hla_base A4H] in X. unfold A_SB in X.
specialize (X ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
change (6444156 / 8 + 2147450880) with 2148256399 in X.
eapply bytes_at_transport; [exact X | exact MU |]. cbn [disjoint_from length]. change (Z.of_nat 1) with 1. unfold sh. clear - HFimg HFapp HF0 HFc ACR LO LOS SPR. Z.div_mod_to_equations. lia. }

apply (proj1 (rw_cells_app asegs _ _ [_; _; _; _] _)) in FF1. destruct FF1 as [FFa FFe]. cbn [cells_size csize Nat.add] in FFe.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FFe. destruct FFe as [FFe FFb]. cbn [cells_size csize Nat.add] in FFb.
change (Z.of_nat 32) with 32 in FFe, FFb. replace (Fr + 32 + Z.of_nat 8) with (Fr + 40) in FFb by lia.
assert (XHP : forall BX mX, munch [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6444156, 6444160)] m1' mX -> wmono asegs m1' mX -> mem_inv asegs mX ->
forall AX mdX, HEAPAx AX (BS ++ LB) LM ((Fr, 0) :: FRS) BX m1' mdX -> HEAPAx AX (BS ++ LB) LM ((Fr, 0) :: FRS) BX mX mdX).
{ intros BX mX MUX WMX MIX AX mdX HPX. exact (fk0_HEAPA HIx _ _ _ _ _ _ _ _ _ _ _ HPX LO HT MUX WMX MIX). }
assert (PD1 : heap_presD (Fr + 32) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m1').
{ eapply heap_presD_trans; [| eapply heap_presD_of_pres; [exact HPR1 | lia]].
eapply (presD_private HIx _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp) (Fr + 32) HP MU0 WM0); [| lia |].
- intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. exact Hb.
- apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. lia. }
assert (XPD : forall mb mX, heap_presD (Fr + 32) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mb ->
forall AX mdX BX, HEAPAx AX (BS ++ LB) LM ((Fr, 0) :: FRS) BX mb mdX ->
munch [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6444156, 6444160)] mb mX -> wmono asegs mb mX ->
heap_presD (Fr + 32) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mX).
{ intros mb mX PDb AX mdX BX HPb MUX WMX. eapply heap_presD_trans; [exact PDb |].
eapply (fk0_presD HIx); [exact HPb | exact LO | lia | exact MUX | exact WMX]. }
assert (XHPg : forall AX BX mdX mb mX, HEAPAx AX (BS ++ LB) LM ((Fr, 0) :: FRS) BX mb mdX ->
munch [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6444156, 6444160)] mb mX -> wmono asegs mb mX -> mem_inv asegs mX ->
HEAPAx AX (BS ++ LB) LM ((Fr, 0) :: FRS) BX mX mdX).
{ intros AX BX mdX mb mX HPX MUX WMX MIX. exact (fk0_HEAPA HIx _ _ _ _ _ _ _ _ _ _ _ HPX LO HT MUX WMX MIX). }
assert (CH0 : jo_chargeA 512 0 B B) by (split; lia).
clear XHP.

lazymatch type of FR with rw_cells _ _ _ ?frc => lazymatch type of FSH1 with rw_cells _ _ _ ?shc => lazymatch type of FFa with rw_cells _ _ _ ?ffc =>
assert (EPI : forall (mX : word -> option byte) (AX : ASA A4L HIx) (mdX : config) (BX : bud) (F1 : bvmap 5 word) (fc1 : bv 32)
(eX xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs10 xs11 xt3 xt4 xt5 xt6 : word),
mem_inv asegs mX ->
rw_cells asegs mX (bv_unsigned sp + -128) frc -> rw_cells asegs mX sh shc -> rw_cells asegs mX Fr ffc ->
rw_cells asegs mX 6444156 [C4 eX] -> stk asegs mX lo (bv_unsigned sp + -128) ->
HEAPAx AX (BS ++ LB) LM ((Fr, 0) :: FRS) BX mX mdX -> model_vm_only (cfg_model md) (cfg_model mdX) ->
heap_presD (Fr + 32) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mX ->
jo_chargeA 512 0 B BX ->
(forall k, In k FSAVED -> k <> 8 -> reg_get F1 (Z_to_bv 5 k) = reg_get F (Z_to_bv 5 k)) -> (frm0 fc -> frm0 fc1) ->
evt asegs (AJ5e A4L HIx AX T mdX)
(MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -128)) gp (Z_to_bv 64 6444320) xt0 xt1 xt2 sp xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 Fr) xs3 xs4 xs5 xs6 xs7 (Z_to_bv 64 sh) (Z_to_bv 64 Fr) xs10 xs11 xt3 xt4 xt5 xt6)
F1 (Z_to_bv 64 0x9fc74) fc1 None mX (seg_rom asegs)))
end end end.
{ intros mX AX mdX BX F1 fc1 eX xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs10 xs11 xt3 xt4 xt5 xt6 MIX FRX FSHX FFX ERRX STX HPX VMX PDX CHX FSX FRMX.
clear MU WM MI1 FR FSH1 FFa FFe FFb ST1 ERR1 SHE PCC.
pose proof (wmono_refl asegs mX) as WM. pose proof (munch_refl [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6444156, 6444160)] mX) as MU.
bstep. bstepz. bstep. bstep. bstepz. bstep. if_falsex. bstep. do 8 bstepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ mX mc, WMc : wmono asegs mX mc, MIc : mem_inv asegs mc |- _ =>
pose proof (fk0_HEAPA HIx _ _ _ _ _ _ _ _ _ _ _ HPX LO HT MUc WMc MIc) as HPY;
pose proof (XPD mX mc PDX AX mdX BX HPX MUc WMc) as PDY end end.
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HPY INF) as (_ & _ & _ & _ & _ & _ & _ & (fp & FPB & FPR & FPnc & FPimg & FPns & FPfr)).
rewrite fr_size_0 in FPB. replace (Fr + 64 - 8) with (Fr + 56) in FPB by lia.
pose proof (ro_C8_of_bytes_at asegs _ _ _ FPB) as FPC.
bstep.
evt_done5.
eapply (hiA_frame_release A4L HIx) with (Fr := Fr) (k := 0) (fp := fp) (rX := Z_to_bv 5 10);
[exact HPY | exact INF | rewrite fr_size_0; replace (Fr + 64 - 8) with (Fr + 56) by lia; exact FPB | lia | reflexivity | vm_compute; discriminate | | ].
1: vm_compute; split; reflexivity.
intros m5 md5 A5 VM5 HP5 Hoff Hwv.
cbn [fr_remove fr_base fst Z.eqb] in HP5. rewrite Z.eqb_refl in HP5.
lazymatch type of HPY with HEAPA _ _ _ _ _ _ _ ?mq _ => assert (MUr : munch [(fp, fp + 1)] mq m5) end.
{ intros x Hx. cbn [outside] in Hx. pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR. cbn in XR.
rewrite <- (Z_to_bv_bv_unsigned x). change (Z_to_bv 64 (bv_unsigned x)) with (wa (bv_unsigned x)). apply Hoff; lia. }
lazymatch type of HPY with HEAPA _ _ _ _ _ _ _ ?mq _ => assert (WMr : wmono asegs mq m5) by exact Hwv end.
assert (FPlow : fp < alloc_ceiling) by (destruct (Z.lt_ge_cases fp alloc_ceiling) as [L|G]; [exact L | exfalso; apply FPnc; left; exact G]).
apply (rw_cells_transport asegs [(fp, fp + 1)] _ m5) in FRX; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] _ m5) in ERRX; [| exact MUr | exact WMr | cbn [disjoint_from cells_size csize Nat.add]; cbn [hl_scratch A4L A4H hla_base] in FPns; unfold A_TP in FPns; lia].
apply (stk_transport_disjoint asegs [(fp, fp + 1)] _ m5) in STX; [| exact MUr | exact WMr | cbn [disjoint_from]; lia].
change (654516 + 4) with 654520.
clear FFX FSHX FPC.
reenterA asegs A4L HIx asegs_wx HP5.
do 19 bstep.
evt_done5.
assert (PD5 : heap_presD (Fr + 32) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m5).
{ eapply heap_presD_trans; [exact PDY |].
eapply (presD_fp HIx _ _ _ _ _ _ _ _ (Fr + 32) _ (bv_unsigned sp) fp HPY); [| lia | exact FPnc | exact FPfr | exact Hoff | exact Hwv].
intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. destruct Hb as [H|H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H]. }
eapply (K _ md5 m5 fp A5 BX).
- split; [| split; [| split; [| split]]].
+ apply ret_statew_intro; [| exact FRMX].
intros k Hk. destruct (Z.eq_dec k 8) as [-> | NE].
* rewrite freg_get_same by (vm_compute; reflexivity). reflexivity.
* rewrite freg_get_other. 1: rewrite freg_get_other. 1: apply FSX; [exact Hk | exact NE].
all: cbn [FSAVED In] in Hk.
all: repeat (destruct Hk as [<- | Hk]); [..| destruct Hk]; first [vm_compute; reflexivity | exfalso; apply NE; reflexivity].
+ eapply model_vm_only_trans; [exact VMX | exact VM5].
+ release_frame FRX STX (bv_unsigned sp). exact STX.
+ eapply (heap_pres_of_presD (Fr + 32)).
* eapply heap_presD_weaken; [exact PD5 | lia |]. intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; apply in_or_app; right; exact Hb | apply in_or_app; right; exact Hb].
* intros a Hd Hc.
destruct (own_frame_fresh HIx Fr 0 (BS ++ LB) LB LM FRS B A1 m1' md1 HP1 ltac:(intros b Hb; apply in_or_app; right; exact Hb)) as [OFF OFS].
assert (Ho : outside [(Fr + 32, Fr + 40)] a).
{ eapply (QSHS.client_outsideF HIx A1 (BS ++ LB) LM ((Fr, 0) :: FRS) B (LB ++ LM ++ fr_ivs A4L FRS) m1' md1 [(Fr + 32, Fr + 40)] (bv_unsigned sp) HP1); [| lia | | lia | exact Hc].
- intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. destruct Hb as [H|H]; [left; apply in_app_or in H; apply in_or_app; destruct H as [H|H]; [left; apply in_or_app; right; exact H | right; exact H] | right; cbn [fr_ivs flat_map app]; right; right; exact H].
- apply Forall_cons; [| apply Forall_nil]. right; right; right. exists Fr, 0. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. left. cbn [fst snd]. rewrite fr_size_0. lia. }
cbn [outside] in Ho. lia.
+ eexists. exact ERRX.
- exact CHX.
- eapply (jopt_agree asegs A4F BS m m5 s BS p); [exact JO | | apply incl_refl].
eapply (agree_of_presD (Fr + 32)); [exact PD5 | intros b Hb; apply in_or_app; left; apply in_or_app; left; exact Hb |].
intros a n Hin.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP1 INF ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin)) as DF. rewrite fr_size_0 in DF. lia.
- exact HP5. }
bstep.
destruct s as [shp|].
2:{  destruct JO as [Hp _]. rewrite Hp in *. if_truex.
gd_exit EPI XHPg XPD PD1 HP1 A1 md1 B m1' VM1 CH0. }
destruct JO as [Hp J].

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m1' mc, WMc : wmono asegs m1' mc, MIc : mem_inv asegs mc |- _ =>
pose proof (XHPg A1 B md1 m1' mc HP1 MUc WMc MIc) as HPc;
assert (AGc : agree_on asegs BS m mc);
[ eapply (agree_of_presD (Fr + 32)); [exact (XPD m1' mc PD1 A1 md1 B HP1 MUc WMc) | intros b Hb; apply in_or_app; left; apply in_or_app; left; exact Hb |];
let a := fresh "a" in let n := fresh "n" in let Hin := fresh "Hin" in intros a n Hin;
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP1 INF ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin)) as DF; rewrite fr_size_0 in DF; lia
| ] end end.
pose proof (jval_agree asegs A4F shp BS m _ BS p 1 J AGc (incl_refl _)) as Jc.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HPc) as ND0.
assert (ND : List.NoDup (map blk_addr BS)) by exact (nodup_app_l' _ _ (nodup_app_l' _ _ ND0)).
destruct (jval_hdr asegs A4F shp _ BS p 1 Jc ND) as (n & tojs & pb & udel & ud & rest & INp & SZ & N48 & HDR & CLOSE).
assert (INpA : In (p, n) (BS ++ LB)) by (apply in_or_app; left; exact INp).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HPc ltac:(apply in_or_app; left; exact INpA)) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HPc ltac:(apply in_or_app; left; exact INpA)) as Hpimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hpimg.
assert (Hp8 : p mod 8 = 0) by (clear - Hpal; Z.div_mod_to_equations; lia).
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p n 0 HPc INpA ltac:(lia) ltac:(lia)) as SH0. rewrite Z.add_0_r in SH0.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p n 5 HPc INpA ltac:(lia) ltac:(lia)) as SH5. replace (p / 8 + 2147450880 + 5) with (p / 8 + 2147450885) in SH5 by lia.
if_falsex.
unfold jhdr_cells in HDR, SZ. cbn [app hl_segs hla_base A4L A4H] in HDR, SZ.
pose proof (jtype_range shp) as JR.
ub_skip. asan_chk0.
bstep. rewrite sx32_small by lia. bstep. bstep.
destruct shp as [|u| |h|kids|kids]; cbn [jtype] in *; unfold JT_BOOLEAN, JT_DOUBLE, JT_INT, JT_STRING, JT_OBJECT, JT_ARRAY in *; if_lit.
-
bstep. bstep. if_lit.
destruct Jc as (pb_ & PBS & REST & EBS & OPB & (b & junk_ & ER & CELLS)). cbn [hl_segs hla_base A4L A4H] in CELLS. unfold jhdr_cells in CELLS. cbn [app] in CELLS.
bstep. asan_chkA.
bstep. bstep. bstep.
gd_exit EPI XHPg XPD PD1 HP1 A1 md1 B m1' VM1 CH0.
-
bstep. bstep. if_lit. bstep. bstep. if_lit.
destruct Jc as (pb_ & PBS & REST & EBS & OPB & Jc). cbn [hl_segs hla_base A4L A4H] in Jc.
lazymatch type of HPc with HEAPA _ _ _ _ _ _ _ ?mc _ => assert (CELLS : exists tojs' udel' ud' bits, rw_cells asegs mc p (jhdr_cells 2 1 tojs' pb_ udel' ud' ++ [C8 bits])) end.
{ destruct u; [destruct Jc as (bits & ud_ & udn & uds & _ & _ & C & _) | destruct Jc as (bits & _ & _ & C)]; do 4 eexists; exact C. }
clear Jc. destruct CELLS as (tojs' & udel' & ud' & bits & CELLS). unfold jhdr_cells in CELLS. cbn [app] in CELLS.
bstep. asan_chkA.
bstep. bstep.
gd_exit EPI XHPg XPD PD1 HP1 A1 md1 B m1' VM1 CH0.
-
bstep. bstep. if_lit.
destruct Jc as (pb_ & PBS & REST & EBS & OPB & (cty & v & junk_ & ER & Hcty & CELLS)). cbn [hl_segs hla_base A4L A4H] in CELLS. unfold jhdr_cells in CELLS. cbn [app] in CELLS.
assert (INp56 : In (p, 56) (BS ++ LB)) by (apply in_or_app; left; rewrite EBS, ER; cbn; left; reflexivity).
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p 56 6 HPc INp56 ltac:(lia) ltac:(lia)) as SH6. replace (p / 8 + 2147450880 + 6) with (p / 8 + 2147450886) in SH6 by lia.
bstep. asan_chkA.
bstep. rewrite sx32_small by lia. bstep. bstep.
destruct Hcty as [-> | ->]; if_lit.
+
bstep. if_lit. bstep. asan_chkA. bstep. bstep. bstep.
gd_exit EPI XHPg XPD PD1 HP1 A1 md1 B m1' VM1 CH0.
+
bstep. asan_chkA. bstep. bstep. bstep.
gd_exit EPI XHPg XPD PD1 HP1 A1 md1 B m1' VM1 CH0.
-
bstep. bstep. if_lit. bstep. bstep. if_lit.
destruct Jc as (pb_ & PBS & REST & EBS & OPB & Jc). cbn [hl_segs hla_base A4L A4H] in Jc, OPB.
lazymatch type of HPc with HEAPA _ _ _ _ _ _ _ ?mc _ =>
assert (TXT : exists (TX TB TBN len : Z) (str0 rest0 : list byte) (lencell : list cell),
In (TB, TBN) BS /\ TB <= TX /\ TX + Z.of_nat (length str0) + 1 <= TB + TBN /\ ~ In (Z_to_bv 8 0) str0 /\
Z.of_nat (length str0) < 2^31 /\
bytes_at asegs mc TX (str0 ++ [Z_to_bv 8 0]) /\
rw_cells asegs mc (p + 40) (C8 (Z_to_bv 64 len) :: lencell) /\ -2^31 < len < 2^31 /\
((0 <= len /\ TX = p + 48) \/ (len < 0 /\ lencell = [C8 (Z_to_bv 64 TX)])) /\
(exists pn, In (p, pn) BS /\ 56 <= pn)) end.
{ destruct h.
- destruct Jc as (len & pd & pdn & str & junk2 & ER & Hlen & Hstr & Hpdn & C1 & C2).
destruct (first_nul_split2A str junk2) as (str0 & rest0 & E0 & NIN & L0).
exists pd, pd, pdn, len, str0, rest0, [C8 (Z_to_bv 64 pd)].
split; [rewrite EBS, ER; cbn; right; left; reflexivity|]. split; [lia|]. split; [lia|]. split; [exact NIN|]. split; [lia|].
split. { apply rw_cells_bytes_at in C2. cbn [cells_bytes cbytes app] in C2. rewrite app_nil_r in C2.
eapply bytes_at_cstr_prefix2A; [exact C2 | exact E0]. }
split. { unfold jhdr_cells in C1. cbn [app] in C1. apply rw_cells_app with (cs1 := [_;_;_;_;_;_]) in C1 as [_ C1]. cbn [cells_size csize Nat.add] in C1. change (p + Z.of_nat 40) with (p + 40) in C1. exact C1. }
split; [lia|]. split; [right; split; [lia | reflexivity]|]. exists 56. split; [rewrite EBS, ER; cbn; left; reflexivity | lia].
- destruct Jc as (len & str & junkS & ER & Hlen & Hstr & C1).
destruct (first_nul_split2A str junkS) as (str0 & rest0 & E0 & NIN & L0).
exists (p + 48), p, (str_objsize len), len, str0, rest0, [CB (Z.to_nat (str_objsize len - 48)) (str ++ [Z_to_bv 8 0] ++ junkS)].
split; [rewrite EBS, ER; cbn; left; reflexivity|]. split; [lia|]. split; [unfold str_objsize; lia|]. split; [exact NIN|]. split; [lia|].
unfold jhdr_cells in C1. cbn [app] in C1. apply rw_cells_app with (cs1 := [_;_;_;_;_;_]) in C1 as [_ C1]. cbn [cells_size csize Nat.add] in C1. change (p + Z.of_nat 40) with (p + 40) in C1.
split. { pose proof C1 as C2. apply rw_cells_app with (cs1 := [_]) in C2 as [_ C2]. cbn [cells_size csize Nat.add] in C2.
apply rw_cells_bytes_at in C2. cbn [cells_bytes cbytes app] in C2. rewrite app_nil_r in C2.
change (p + 40 + Z.of_nat 8) with (p + 40 + 8) in C2. replace (p + 40 + 8) with (p + 48) in C2 by lia. eapply bytes_at_cstr_prefix2A; [exact C2 | exact E0]. }
split; [exact C1|]. split; [lia|]. split; [left; split; [lia | reflexivity]|]. exists (str_objsize len). split; [rewrite EBS, ER; cbn; left; reflexivity | unfold str_objsize; lia]. }
clear Jc. destruct TXT as (TX & TB & TBN & len & str0 & rest0 & lencell & INT & TLO & THI & NIN & LS0 & BY & LENC & Hlen & ALT & (pn & INpn & Hpn)).
assert (INTA : In (TB, TBN) ((BS ++ LB) ++ LM)) by (apply in_or_app; left; apply in_or_app; left; exact INT).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ TB TBN HPc INTA) as (_ & _ & Htlo & Hthi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ TB TBN HPc INTA) as Htimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Htimg.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HPc INF INTA) as DFT. rewrite fr_size_0 in DFT.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ TB TBN HPc INTA) as APT. cbn [hl_sb A4L] in APT. unfold A_SB in APT.
assert (INpnA : In (p, pn) (BS ++ LB)) by (apply in_or_app; left; exact INpn).
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p pn 6 HPc INpnA ltac:(lia) ltac:(lia)) as SH6. replace (p / 8 + 2147450880 + 6) with (p / 8 + 2147450886) in SH6 by lia.
apply rw_cells_app with (cs1 := [_]) in LENC as [LEN1 LEN2]. cbn [cells_size csize Nat.add] in LEN2. change (p + 40 + Z.of_nat 8) with (p + 40 + 8) in LEN2. replace (p + 40 + 8) with (p + 48) in LEN2 by lia.
bstep. asan_chkA. bstep. bstep. bstep.

lazymatch goal with |- evt _ ?Q (MS ?r ?Fx ?pc ?fcx None ?mc ?rom) =>
let r' := open_constr:(mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in unify r r';
lazymatch r' with mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31 =>
assert (CONT : forall xa0 xa1 : word, evt asegs Q
(MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 xa0 xa1 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 TX) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Fx (Z_to_bv 64 0x9fa88) fcx None mc rom))
end end.
2:{ destruct ALT as [[Hl ETX] | [Hl ->]].
+  if_truex. rewrite <- ETX. apply CONT.
+  if_falsex. asan_chkA. bstep. apply CONT. }
intros xa0 xa1.

pose proof (RTC_LCONV _ _ _ _ _ _ _ HPc) as LCC. apply ro_C8_of_bytes_at in LCC. unfold A_LCONV, A_DPSTR in LCC.
lazymatch type of HPc with HEAPA _ _ _ _ _ _ _ ?mc _ =>
assert (SHL : ro_cells asegs mc 2147569674 [C1 (Z_to_bv 8 0)]);
[ apply QsKa.Mqa.ro_C1_of_bytes_at;
pose proof (heapA_shadow_img A4L HIx _ _ _ _ _ _ _ (0xe8050 / 8) HPc) as X;
assert (E : img_shadow_val (hl_reg_globals A4L) (0xe8050 / 8) = 0) by (vm_compute; reflexivity); rewrite E in X;
cbn [hl_sb A4L hl_img_lo hl_img_hi hla_base A4H] in X; unfold A_SB in X;
specialize (X ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate));
change (0xe8050 / 8 + 2147450880) with 2147569674 in X; exact X |];
assert (SHD : ro_cells asegs mc 2147461427 [C1 (Z_to_bv 8 0)]);
[ apply QsKa.Mqa.ro_C1_of_bytes_at;
pose proof (heapA_shadow_img A4L HIx _ _ _ _ _ _ _ (0x1499c / 8) HPc) as X;
assert (E : img_shadow_val (hl_reg_globals A4L) (0x1499c / 8) = 0) by (vm_compute; reflexivity); rewrite E in X;
cbn [hl_sb A4L hl_img_lo hl_img_hi hla_base A4H] in X; unfold A_SB in X;
specialize (X ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate));
change (0x1499c / 8 + 2147450880) with 2147461427 in X; exact X |];
assert (DPB : ro_cells asegs mc 0x1499c [CB 2 [Z_to_bv 8 46; Z_to_bv 8 0]]);
[ change 2%nat with (length [Z_to_bv 8 46; Z_to_bv 8 0]); apply ro_cells_image; [assumption | vm_compute; reflexivity | lia | cbn; lia] |]
end.
bstep. bstep. bstep. bstep.
bstep. ub_resolve. bstep. bstep. ub_resolve.
bstep. bstep. bstep. bstep. rewrite ?zxb_zero, ?sxb_zero. if_false.
bstep. bstep. if_false.
bstep. bstep. bstep. bstep. rewrite ?zxb_zero, ?sxb_zero. if_false.
bstep. bstep. bstep.
if_lit.
bstep. bstep. bstep.
eapply evt_cut; [eapply ERRNOL; reflexivity |]. intros ms9 ->.
replace (ret_pc (Z_to_bv 64 0x9fafc)) with (Z_to_bv 64 0x9fafc) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
unfold A_ERRNO, A_TP. change (6444320 - 164) with 6444156.
bstep. ub_resolve. bstep. bstep. bstep. ub_resolve.
bstep. bstep. bstep. rewrite ?sxb_zero. bstep. if_false.
bstep. bstepz. bstep. bstep. bstep.

set (txtZ := map bv_unsigned str0 ++ [0]).
assert (FA : Forall (fun c => 0 <= c < 256) (map bv_unsigned str0)).
{ apply Forall_map. apply Forall_forall. intros b _. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia. }
destruct (SCANH (map bv_unsigned str0) FA) as (bits & used & SCAN & U0).
assert (LTX : zlength txtZ = Z.of_nat (length str0) + 1) by (unfold zlength, txtZ; rewrite length_app, length_map; cbn [length]; lia).
assert (LPRE : zlength (map bv_unsigned str0) = Z.of_nat (length str0)) by (unfold zlength; rewrite length_map; reflexivity).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m1' mc, WMc : wmono asegs m1' mc, MIc : mem_inv asegs mc |- _ =>
pose proof (XHPg A1 B md1 m1' mc HP1 MUc WMc MIc) as HPs;
pose proof (XPD m1' mc PD1 A1 md1 B HP1 MUc WMc) as PDs end end.
destruct (heapA_canary A4L HIx _ _ _ _ _ _ _ HPs) as (g & CAN1 & CAN2 & _). cbn [hl_got_guard hl_guard A4L A4H hla_base] in CAN1, CAN2.
pose proof (frame_above_img HIx _ _ _ _ _ _ _ _ _ HP1 INF) as HFhi. cbn [hl_img_hi A4H] in HFhi.
pose proof (hiA_top_le A4L HIx) as HT47.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => rename mX into mS end.
eapply evt_cut.
{ eapply STRTOD with (T := TX) (PE := Fr + 32) (txt := txtZ) (pre := map bv_unsigned str0) (post := []) (lo := lo) (bits := bits) (used := used) (canary := g).
- unfold txtZ. rewrite map_app. cbn [map]. rewrite map_unsigned_bytesA. exact BY.
- unfold txtZ. apply Forall_app. split; [exact FA | constructor; [lia | constructor]].
- reflexivity.
- rewrite LPRE. lia.
- rewrite LTX. lia.
- exact FFe.
- exact SCAN.
- rewrite unsigned_lit by lia. eassumption.
- rewrite unsigned_lit by lia. unfold ASTRTOD_DEPTH. lia.
- lia.
- rewrite unsigned_lit by lia. lia.
- lia.
- rewrite LTX. lia.
- rewrite unsigned_lit by lia. left. rewrite LTX. split; [lia | lia].
- lia.
- lia.
- rewrite unsigned_lit by lia. left. lia.
- rewrite LTX. lia.
- exact CAN1.
- exact CAN2.
- unfold A_TP. eassumption.
- assumption.
- exact FRM.
- reflexivity.
- reflexivity.
- reflexivity. }
cbv beta delta [astrtod_post]. rewrite !(unsigned_lit (bv_unsigned sp + -128)) by lia. unfold A_TP. change (6444320 - 164) with 6444156. change (6444320 - 160) with 6444160.
post_call asegs mS.
bstep. bstep.

lazymatch goal with FRq : rw_cells asegs _ (bv_unsigned sp + -128) ?frc, FSHq : rw_cells asegs _ sh ?shc, FFq : rw_cells asegs _ Fr ?ffc |- _ =>
assert (KFREE : forall (retpc : Z) (F2 : bvmap 5 word) (fc2 : bv 32) (mc : word -> option byte) (ec : word)
(kt0 kt1 kt2 ka1 ka2 ka3 ka4 ka5 ka6 ka7 kt3 kt4 kt5 kt6 : word),
(retpc = 0x9fb5c \/ retpc = 0x9fc30 \/ retpc = 0x9fc74) ->
(forall k, In k FSAVED -> k <> 8 -> reg_get F2 (Z_to_bv 5 k) = reg_get F (Z_to_bv 5 k)) -> (frm0 fc -> frm0 fc2) ->
mem_inv asegs mc -> munch [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6444156, 6444160)] m1' mc -> wmono asegs m1' mc ->
rw_cells asegs mc (bv_unsigned sp + -128) frc -> rw_cells asegs mc sh shc -> rw_cells asegs mc Fr ffc ->
rw_cells asegs mc 6444156 [C4 ec] -> stk asegs mc lo (bv_unsigned sp + -128) ->
evt asegs (AJ5e A4L HIx A1 T md1)
(MS (mkR (Z_to_bv 64 retpc) (Z_to_bv 64 (bv_unsigned sp + -128)) gp (Z_to_bv 64 6444320) kt0 kt1 kt2 sp (Z_to_bv 64 (bv_unsigned sp + -128))
(Z_to_bv 64 0) ka1 ka2 ka3 ka4 ka5 ka6 ka7
(Z_to_bv 64 Fr) (Z_to_bv 64 0) (Z_to_bv 64 6444156) (Z_to_bv 64 TX) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 2148256399) (Z_to_bv 64 sh) (Z_to_bv 64 Fr)
(Z_to_bv 64 2147450880) (Z_to_bv 64 2147461427) kt3 kt4 kt5 kt6)
F2 (Z_to_bv 64 0x6369c) fc2 None mc (seg_rom asegs))) end.
{ intros retpc F2 fc2 mc ec kt0 kt1 kt2 ka1 ka2 ka3 ka4 ka5 ka6 ka7 kt3 kt4 kt5 kt6 Hret FS2 FRM2 MIc MUc WMc FRc FSHc FFc ERRc STc.
pose proof (XHPg A1 B md1 m1' mc HP1 MUc WMc MIc) as HPf.
pose proof (XPD m1' mc PD1 A1 md1 B HP1 MUc WMc) as PDf.
evt_done5.
eapply (hiA_free A4L HIx) with (p := 0) (u := UWpaid) (lo := lo) (errv := ec);
[ exact HPf | left; reflexivity | rewrite unsigned_lit by lia; exact STc | exact LO | rewrite unsigned_lit by lia; cbn [hl_stack_A A4L]; lia
| rewrite unsigned_lit by lia; clear - SPA; Z.div_mod_to_equations; lia | rewrite unsigned_lit by lia; lia | exact ERRc | reflexivity | reflexivity
| split; cbn; exact I | exact BB | cbn; exact BD | ].
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3.
cbn [hl_segs hl_tp hla_base A4L A4H Z.eqb] in ST3, HPR3, ERR3, HP3. unfold A_TP in ERR3. change (6444320 - 164) with 6444156 in ERR3.
rewrite ?(unsigned_lit (bv_unsigned sp + -128)) in ST3, HPR3 by lia.
assert (Enot : forall n, ~ In (0, n) (BS ++ LB)).
{ intros n0 Hin. pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ 0 n0 HPf (in_or_app _ LM _ (or_introl Hin))) as (_ & _ & H0 & _). lia. }
rewrite (lb_remove_notinA 0 _ Enot) in HPR3, HP3.
set (B3 := charge B 512 0) in *.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FRc; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FFc; [| eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; cbn [fr_ivs flat_map app fr_base fr_class fst snd]; left; reflexivity | lia | cbn [blk_addr blk_size fst snd]; rewrite fr_size_0; cbn; lia]].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FSHc; [| eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; cbn [fr_ivs flat_map app fr_base fr_class fst snd]; right; left; reflexivity | unfold shad; cbn [blk_addr blk_size fst snd hl_sb A4L]; unfold A_SB; fold sh; lia | unfold shad; cbn [blk_addr blk_size fst snd hl_sb A4L]; rewrite fr_shadow_len_0; unfold A_SB; fold sh; cbn; lia]].
change (hl_segs A4H) with asegs in FRc, FFc, FSHc.
assert (PD3 : heap_presD (Fr + 32) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m3).
{ eapply heap_presD_trans; [exact PDf |].
eapply heap_presD_weaken; [eapply (heap_presD_of_pres (Fr + 32)); [exact HPR3 | apply Z.le_refl] | lia |].
intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. rewrite app_assoc. apply in_or_app.
destruct Hb as [Hb|Hb]; [left; exact Hb | right; cbn [fr_ivs flat_map app]; right; right; exact Hb]. }
assert (VM13 : model_vm_only (cfg_model md) (cfg_model md3)) by (eapply model_vm_only_trans; [exact VM1 | exact VM3]).
assert (CH3 : jo_chargeA 512 0 B B3) by (unfold jo_chargeA, B3, charge; cbn [bB bD]; split; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI3. change (hl_segs A4L) with asegs in MI3.
assert (SHE3 : ro_cells asegs m3 2148256399 [C1 (Z_to_bv 8 0)]).
{ apply QsKa.Mqa.ro_C1_of_bytes_at.
pose proof (heapA_shadow_img A4L HIx _ _ _ _ _ _ _ (6444156 / 8) HP3) as X.
assert (E : img_shadow_val (hl_reg_globals A4L) (6444156 / 8) = 0) by (vm_compute; reflexivity). rewrite E in X.
cbn [hl_sb A4L hl_img_lo hl_img_hi hla_base A4H] in X. unfold A_SB in X.
specialize (X ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
change (6444156 / 8 + 2147450880) with 2148256399 in X. exact X. }
clear MU WM. pose proof (wmono_refl asegs m3) as WM. pose proof (munch_refl [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6444156, 6444160)] m3) as MU.
reenterA asegs A4L HIx asegs_wx HP3.
destruct Hret as [-> | [-> | ->]].
-
replace (ret_pc (Z_to_bv 64 654172)) with (Z_to_bv 64 654172) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
bstep. rewrite ?sxb_zero. bstep. if_true. bstep. bstep. bstep.
gd_exit EPI XHPg XPD PD3 HP3 A3 md3 B3 m3 VM13 CH3.
-
replace (ret_pc (Z_to_bv 64 654384)) with (Z_to_bv 64 654384) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
bstep. rewrite ?sxb_zero. bstep. if_false. bstep. bstep. bstep.
gd_exit EPI XHPg XPD PD3 HP3 A3 md3 B3 m3 VM13 CH3.
-
replace (ret_pc (Z_to_bv 64 654452)) with (Z_to_bv 64 654452) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
gd_exit EPI XHPg XPD PD3 HP3 A3 md3 B3 m3 VM13 CH3. }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m1' mc, WMc : wmono asegs m1' mc, MIc : mem_inv asegs mc |- _ =>
pose proof (XHPg A1 B md1 m1' mc HP1 MUc WMc MIc) as HPx end end.
pose proof (unpoisoned_of_blk HIx _ _ _ _ _ _ _ TB TBN TX (Z.of_nat (length str0) + 1) HPx ltac:(apply in_or_app; left; exact INT) ltac:(lia) ltac:(lia) ltac:(lia)) as UNS.
rewrite LPRE in POST.
rename x14 into F5. rename x15 into fc5. rename x16 into m5. rename x17 into e5.
assert (FS5 : forall k, In k FSAVED -> k <> 8 -> reg_get F5 (Z_to_bv 5 k) = reg_get F (Z_to_bv 5 k)).
{ intros k Hk NE. cbn [FSAVED In] in Hk.
repeat (destruct Hk as [<- | Hk]); [..| destruct Hk]; first [exfalso; apply NE; reflexivity | idtac];
(rewrite PC0 by (vm_compute; lia)); rewrite !freg_get_other by (vm_compute; reflexivity); reflexivity. }
destruct (Z.eq_dec used 0) as [U0' | UN0].
+
rewrite U0' in *. replace (TX + 0) with TX by lia. if_truex. bstep. bstep.
eapply (KFREE 0x9fc30 F5 fc5 m5 e5); [right; left; reflexivity | exact FS5 | intros _; exact PC | assumption | assumption | assumption | eassumption | eassumption | eassumption | eassumption | eassumption].
+
if_falsex. bstep. if_falsex.
assert (UNk : unpoisoned asegs m5 A_SB (TX + used) 1)
by (eapply (QsKa.Mqa.unpoisoned_sub_any asegs _ A_SB TX (Z.of_nat (length str0) + 1)); [exact UNS | lia | lia | lia]).
destruct (unpoisoned_last asegs _ _ _ _ UNk) as (v & SHk & Hv).
replace (TX + used + 1 - 1) with (TX + used) in SHk, Hv by lia. unfold A_SB in SHk.
assert (HL : (Z.to_nat used < length (map (Z_to_bv 8) txtZ))%nat) by (rewrite length_map; unfold txtZ; rewrite length_app, length_map; cbn [length]; lia).
destruct (nth_error (map (Z_to_bv 8) txtZ) (Z.to_nat used)) as [bu|] eqn:Hbu; [| exfalso; apply nth_error_None in Hbu; lia].
pose proof (bv_unsigned_in_range 8 bu) as BUR. unfold bv_modulus in BUR. cbn in BUR.
pose proof (string_byteG asegs _ TX _ used bu PC4 Hbu ltac:(lia)) as RDU.
lazymatch goal with |- evt _ ?Q (MS ?r ?Fx ?pc ?fcx None ?mc ?rom) =>
let r' := open_constr:(mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in unify r r';
lazymatch r' with mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31 =>
assert (CONT2 : forall ya1 ya2 : word, evt asegs Q
(MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ya1 ya2 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Fx (Z_to_bv 64 0x9fb4c) fcx None mc rom))
end end.
2:{ bstep. bstep. sh_norm. bstep. bstep.
destruct Hv as [-> | [Hv8 Hvm]].
- rewrite sxb_zero. if_false. apply CONT2.
- rewrite (QsKa.Mqa.sxb_small v) by lia. if_truex. bstep. bstep.
rewrite (unsigned_lit (TX + used)) by lia. rewrite QsKa.Mqa.land7_mod8 by lia. if_truex. apply CONT2. }
intros ya1 ya2.
bstep. unfold zxb. bstep.
destruct (Z.eq_dec (bv_unsigned bu) 0) as [BZ | BNZ].
*
rewrite BZ. if_truex.
bstep. bstep. bstep.
match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c end.
-- bstep. bstep. bstep.
eapply (KFREE 0x9fc74 _ fc5 m5 e5); [right; right; reflexivity | gd_fs_tail | intros _; exact PC | assumption | assumption | assumption | eassumption | eassumption | eassumption | eassumption | eassumption].
-- bstep. rewrite ?sxb_zero. bstep. if_false. bstep. bstep. bstep.
match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c end.
++ bstep. bstep. bstep.
eapply (KFREE 0x9fc74 _ fc5 m5 e5); [right; right; reflexivity | gd_fs_tail | intros _; exact PC | assumption | assumption | assumption | eassumption | eassumption | eassumption | eassumption | eassumption].
++ bstep. bstep. bstep. bstep.
eapply (KFREE 0x9fc74 _ fc5 m5 e5); [right; right; reflexivity | gd_fs_tail | intros _; exact PC | assumption | assumption | assumption | eassumption | eassumption | eassumption | eassumption | eassumption].
*
if_falsex. bstep. bstep.
eapply (KFREE 0x9fb5c F5 fc5 m5 e5); [left; reflexivity | exact FS5 | intros _; exact PC | assumption | assumption | assumption | eassumption | eassumption | eassumption | eassumption | eassumption].
-
bstep. bstep. if_lit. bstep. bstep. if_lit.
bstep.
eapply evt_cut; [eapply ERRNOL; reflexivity |]. intros ms9 ->.
replace (ret_pc (Z_to_bv 64 0x9fb7c)) with (Z_to_bv 64 0x9fb7c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
unfold A_ERRNO, A_TP. change (6444320 - 164) with 6444156.
bstep. ub_resolve. bstep. bstep. ub_resolve.
bstep. bstep. bstep. rewrite ?sxb_zero. bstep. if_false.
bstep. bstep. bstep.
gd_exit EPI XHPg XPD PD1 HP1 A1 md1 B m1' VM1 CH0.
-
bstep. bstep. if_lit. bstep. bstep. if_lit.
bstep.
eapply evt_cut; [eapply ERRNOL; reflexivity |]. intros ms9 ->.
replace (ret_pc (Z_to_bv 64 0x9fb7c)) with (Z_to_bv 64 0x9fb7c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
unfold A_ERRNO, A_TP. change (6444320 - 164) with 6444156.
bstep. ub_resolve. bstep. bstep. ub_resolve.
bstep. bstep. bstep. rewrite ?sxb_zero. bstep. if_false.
bstep. bstep. bstep.
gd_exit EPI XHPg XPD PD1 HP1 A1 md1 B m1' VM1 CH0.
Qed.
End MJoGetDouble.
End RC__1.
