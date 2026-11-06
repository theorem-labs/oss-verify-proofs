(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QWxq_c1 QRjH QHnV QCcH QfLs Q0Ek Qtgi QjDH Qsw7 QJjn QRUw QkMG QG8z Q7UD QXUB Qhd4 Qwm6 QlKV QsKa Qiiq Q1Ey Ql4f Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw QkMG. Import QG8z.
Import Q7UD QXUB.Mq0 Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QsKa.Mq4 Qiiq.Mq0 Q1Ey Ql4f.Mq1.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeEpiA.
Variable HIx : heap_iface_A A4L.

Definition fp_private_stmt : Prop :=
forall (A : ASA A4L HIx) LB LM FR B m md F k, HEAPA A4L HIx A LB LM FR B m md -> In (F, k) FR ->
exists fp, bytes_at asegs m (F + fr_size k - 8) (le8 (Z_to_bv 64 fp)) /\ 0 < fp < 2^64 /\
~ client_addr A4H (LB ++ LM) alloc_ceiling fp /\ (fp < hl_img_lo A4H \/ hl_img_hi A4H <= fp) /\ ~ hl_scratch A4H fp /\
(forall F' k', In (F', k') FR -> ~ (F' <= fp < F' + fr_size k') /\ ~ (shad A4L F' <= fp < shad A4L F' + fr_shadow_len k')).

Lemma OBL_FP_PRIVATE : fp_private_stmt.
Proof.
intros A LB LM FR B m md F k HP Hin.
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP Hin) as (_ & _ & _ & _ & _ & _ & _ & X). exact X.
Qed.

Lemma pe_epilogue_A :
forall (pf : pe_fix) (pa : pe_fixA) (LBall LM : list blk) (FRS : list frame) (B : bud)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (T : TSet) (lo : Z)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
HEAPA A4L HIx A LBall LM ((pa_F pa, 2) :: FRS) B m md ->
pe_geomA pf pa -> 0 <= pf_spf pf < 2^62 ->
pe_frameA asegs m pf pa cb nb pj sv ->
stk asegs m lo (pf_spf pf) -> alloc_ceiling <= lo -> lo <= pf_spf pf - 12288 ->
bv_unsigned (pe_ra sv) mod 2 = 0 ->
(forall m' md' (A' : ASA A4L HIx) (fp : Z),
model_vm_only (cfg_model md) (cfg_model md') ->
HEAPA A4L HIx A' LBall LM FRS B m' md' ->
stk asegs m' lo (pa_sp0 pa) ->
0 < fp < 2^64 -> ~ client_addr A4H (LBall ++ LM) alloc_ceiling fp -> (fp < hl_img_lo A4H \/ hl_img_hi A4H <= fp) ->
~ hl_scratch A4H fp ->
(forall F' k', In (F', k') FRS -> ~ (F' <= fp < F' + fr_size k') /\ ~ (shad A4L F' <= fp < shad A4L F' + fr_shadow_len k')) ->
munch [(shA (pa_F pa), shA (pa_F pa) + 32); (pa_F pa, pa_F pa + 8); (fp, fp + 1)] m m' ->
wmono asegs m m' -> mem_inv asegs m' ->
AJ5 A4L HIx A' T md'
(MS (mkR (pe_ra sv) (Z_to_bv 64 (pa_sp0 pa)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (pe_s0 sv) (pe_s1 sv) s3 a1 a2 a3 a4 a5 a6 a7
(pe_s2 sv) (pe_s3 sv) (pe_s4 sv) (pe_s5 sv) (pe_s6 sv) (pe_s7 sv) (pe_s8 sv) (pe_s9 sv) (pe_s10 sv) (pe_s11 sv) t3 t4 t5 t6)
F (ret_pc (pe_ra sv)) fc None m' (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (shA (pa_F pa))) s3 s4 (Z_to_bv 64 (pa_F pa)) s6 s7 (Z_to_bv 64 (pa_F pa)) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 APE_EPI) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros HP GEO SP0 FR ST LO LOS RAE K.
pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
unfold ff_cellsA in FF. unfold ffsh_cells, FSH0 in FSH. cbn [map] in FSH. unfold pe_savedA_cells in SAVED.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof alloc_ceiling_range as ACR.
assert (INF : In (Ff, 2) ((Ff, 2) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as DSF. rewrite fr_size_2 in DSF. cbn [hl_sb A4L] in DSF.
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & _ & _ & _ & Himg_F & _). rewrite fr_size_2 in Himg_F. cbn [hl_img_lo hl_img_hi A4L A4H hla_base] in Himg_F.
unfold APE_EPI, shA in *. a4l.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(Ff / 8 + 2147450880, Ff / 8 + 2147450880 + 32); (Ff, Ff + 8)] m) as MU.
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
reenterA asegs A4L HIx asegs_wx HP.
step. stepz.
step. step. stepz.
step. if_falsex.
step.
do 32 stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc |- _ =>
assert (HPc : HEAPA A4L HIx A LBall LM ((Ff, 2) :: FRS) B mc md);
[ eapply (heapA_client_frame A4L HIx); [exact HP | | exact WMc | exact MIc];
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP MUc)
| ] end end.
{ apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; right; right; right; exists Ff, 2; (split; [exact INF|]);
[ right; unfold shad; cbn [fst snd hl_sb A4L]; rewrite ?fr_shadow_len_2; unfold A_SB; lia
| left; cbn [fst snd]; rewrite ?fr_size_2; lia ]. }
destruct (OBL_FP_PRIVATE _ _ _ _ _ _ _ _ _ HPc INF) as (fp & FPB & FPR & FPnc & FPimg & FPns & FPfr).
rewrite fr_size_2 in FPB. replace (Ff + 256 - 8) with (Ff + 248) in FPB by lia.
pose proof (ro_C8_of_bytes_at asegs _ _ _ FPB) as FPC.
step.
evt_done5.
eapply (hiA_frame_release A4L HIx) with (Fr := Ff) (k := 2) (fp := fp) (rX := Z_to_bv 5 10);
[exact HPc | exact INF | rewrite fr_size_2; replace (Ff + 256 - 8) with (Ff + 248) by lia; exact FPB | lia | reflexivity | vm_compute; discriminate | | ].
1: vm_compute; split; reflexivity.
intros m2 md2 A2 VM2 HP2 Hoff Hwv.
cbn [fr_remove fr_base fst Z.eqb] in HP2. rewrite Z.eqb_refl in HP2.
assert (MUr : munch [(fp, fp + 1)] m1 m2).
{ intros x Hx. cbn [outside] in Hx. pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR. cbn in XR.
rewrite <- (Z_to_bv_bv_unsigned x). change (Z_to_bv 64 (bv_unsigned x)) with (wa (bv_unsigned x)). apply Hoff; lia. }
assert (WMr : wmono asegs m1 m2) by exact Hwv.
assert (MI2 : mem_inv asegs m2).
{ intros y b Hb. destruct (Z.eq_dec (bv_unsigned y) fp) as [Ey | Ny].
- destruct (ro_addr asegs y) eqn:RO; [| reflexivity]. exfalso. apply ro_addr_asegs in RO. cbn [hl_img_lo hl_img_hi A4H hla_base A4L] in FPimg. lia.
- apply (MI y b). rewrite <- Hb. symmetry. rewrite <- (Z_to_bv_bv_unsigned y). change (Z_to_bv 64 (bv_unsigned y)) with (wa (bv_unsigned y)). apply Hoff; [| exact Ny].
pose proof (bv_unsigned_in_range 64 y) as YR. unfold bv_modulus in YR. cbn in YR. lia. }
apply (rw_cells_transport asegs [(fp, fp + 1)] m1 m2) in SAVED; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; unfold client_addr in FPnc; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] m1 m2) in SLOTS; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; unfold client_addr in FPnc; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] m1 m2) in GAP; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; unfold client_addr in FPnc; lia].
apply (stk_transport_disjoint asegs [(fp, fp + 1)] m1 m2) in ST; [| exact MUr | exact WMr | cbn [disjoint_from]; unfold client_addr in FPnc; lia].
change (602972 + 4) with 602976.
clear FF FSH FPC.
reenterA asegs A4L HIx asegs_wx HP2.
step. step. step.
replace (sp0 - 104) with (sp0 + -104) in SAVED by lia.
do 13 step.
step. step.
evt_done5.
assert (ST2 : stk asegs m2 lo sp0).
{ pose proof (stk_release asegs _ _ _ _ ST SLOTS ltac:(lia)) as ST1. rewrite pe_slotsA_size in ST1 || cbn [cells_size csize Nat.add] in ST1.
pose proof (stk_release asegs _ _ _ _ ST1 GAP ltac:(lia)) as STg. cbn [cells_size csize Nat.add] in STg.
rewrite Nat.add_0_r, Z2Nat.id in STg by lia.
replace (spf + Z.of_nat 312 + (sp0 - 104 - (spf + 312))) with (sp0 + -104) in STg by lia.
pose proof (stk_release asegs _ _ _ _ STg SAVED ltac:(lia)) as STs. cbn [cells_size csize Nat.add] in STs.
replace (sp0 + -104 + Z.of_nat 104) with sp0 in STs by lia. exact STs. }
eapply K.
all: lazymatch goal with
| |- model_vm_only _ _ => exact VM2
| |- HEAPA _ _ _ _ _ _ _ _ _ => exact HP2
| |- stk _ _ _ _ => exact ST2
| |- 0 < _ < _ => exact FPR
| |- ~ client_addr _ _ _ _ => exact FPnc
| |- _ \/ _ => exact FPimg
| |- ~ hl_scratch _ _ => exact FPns
| |- forall F' k', _ => intros F' k' Hin'; apply FPfr; right; exact Hin'
| |- munch _ _ _ => eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact MUr]]; intros z Hz; cbn [outside] in Hz |- *; tauto
| |- wmono _ _ _ => intros z Hz; apply WMr; apply WM; exact Hz
| |- mem_inv _ _ => exact MI2
end.
Qed.
End PeEpiA.
End RC__1.
End Mq0.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw QkMG. Import QG8z.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QsKa.Mq4 Qiiq.Mq0 Q1Ey Ql4f.Mq1.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeRedoA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.

Lemma seg_redo_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l ->
(forall (a3' : word),
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA (tl_st l)) (t_co ts) gp t0 t1 t2
(Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l))
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3' (Z_to_bv 64 APE_JTAB) a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m)) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_REDO (t_co ts) gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC INV Hl K.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH). unfold pe_msA in *.
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold pe_savedA_cells in SAVED. unfold ff_cellsA in FF. unfold ffsh_cells, FSH0 in FSH. cbn [map] in FSH.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (LV depth l Hl) as (ST26 & SS26 & _).
pose proof (TSK depth l Hl) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld. unfold srec_cells in Ld.
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd (Z.of_nat depth) 0 HP INq ltac:(lia) ltac:(lia)) as SHQ.
replace (q / 8 + 4 * Z.of_nat depth + 0 + A_SB) with (q / 8 + 4 * Z.of_nat depth + A_SB) in SHQ by lia.
pose proof (pe_jtabA_ro m MI) as JT. unfold pe_jtabA in JT.
unfold APE_REDO, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t. stash Himg_q.
clear PB REST LV TSK.
reenterA asegs A4L HIx asegs_wx HP.
step. step. step. if_true.
step. step. step. if_true.
step. norm_sx32.
step. step.
rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
replace (q + Z.of_nat depth * 32) with bse by lia.
step. step. sh_norm.
replace (bse / 8) with (q / 8 + 4 * Z.of_nat depth) by (subst bse; symmetry; apply div8_add_mul32; lia).
step. step. if_true.
step. norm_sx32. step. step. if_truex.
step.
rewrite (unsigned_lit (tl_st l)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
step. step.
assert (CASES : exists k : nat, (k <= 26)%nat /\ tl_st l = Z.of_nat k) by (exists (Z.to_nat (tl_st l)); split; lia).
destruct CASES as (k & Hk & Ek). rewrite Ek in *.
do 27 (destruct k as [|k];
[ match goal with |- context [Z_to_bv 64 (Z.of_nat ?n * 4)] =>
let v := eval vm_compute in (Z.of_nat n * 4) in change (Z.of_nat n * 4) with v;
let w := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with w end;
step; step;
match goal with |- context [sext 64 (bv_extract 0 32 (le_bytes_to_word ?bs))] =>
let v := eval vm_compute in (bv_unsigned (sext 64 (bv_extract 0 32 (le_bytes_to_word bs)))) in
replace (sext 64 (bv_extract 0 32 (le_bytes_to_word bs))) with (Z_to_bv 64 v) by (apply bv_eq; vm_compute; reflexivity) end;
step; step;
subst bse; evt_done5; apply K
| ]).
exfalso. lia.
Qed.
End PeRedoA.
End RC__1.
End Mq1.
From Stdlib Require Permutation.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdyh QKQo Q4v2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import QG8z Qdyh.Mq0. Import QKQo.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq4 Qiiq.Mq0 QsKa.Mq6 Q4v2.Mq0 Q1Ey Ql4f.Mq1.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.

Ltac sh_normO :=
sh_norm;
repeat match goal with
| |- context [ (?p + ?j) / 8 ] => is_Zlit j; rewrite (div8_add p j) by lia; let k := eval vm_compute in (Z.div j 8) in change (j / 8) with k
end;
rewrite ?Z.add_0_r.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition ts_lvl (ts : tstate) (l : tlevel) : tstate :=
TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) l) (t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (t_obj ts) (t_objs ts) (t_objbs ts).

Definition ts_lvl_obj (ts : tstate) (l : tlevel) (obj : Z) (objs : option jshape) (objbs : list blk) : tstate :=
TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) l) (t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) obj objs objbs.

Lemma lb_remove_notinS : forall p LB, (forall n, ~ In (p, n) LB) -> lb_remove p LB = LB.
Proof.
induction LB as [|[a n] LB IH]; intros H; [reflexivity|]. cbn [lb_remove blk_addr fst].
destruct (Z.eqb_spec a p) as [->|NE]; [exfalso; apply (H n); left; reflexivity|]. f_equal. apply IH. intros k Hk. apply (H k). right; exact Hk.
Qed.

Lemma lupd_lupdS : forall {X} (l : list X) i (x y : X), lupd (lupd l i x) i y = lupd l i y.
Proof. induction l as [|h t IH]; intros [|i] x y; cbn; try reflexivity. f_equal. apply IH. Qed.
Lemma ts_lvl_lvl : forall ts l2 l3, ts_lvl (ts_lvl ts l2) l3 = ts_lvl ts l3.
Proof. intros ts l2 l3. unfold ts_lvl; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs]. rewrite lupd_lupdS. reflexivity. Qed.

Lemma lvl_mode_array : forall st ss c hn, (st = ST_array \/ st = ST_array_after_sep) -> 0 <= ss <= 26 -> lvl_mode st ss = Some (c, hn) -> c = CArr /\ hn = false /\ ss <> ST_finish.
Proof.
intros st ss c hn Hst R H. assert (CASES : exists k : nat, (k <= 26)%nat /\ ss = Z.of_nat k) by (exists (Z.to_nat ss); split; lia).
destruct CASES as (k & Hk & ->). clear R.
destruct Hst as [-> | ->]; do 27 (destruct k as [|k]; [vm_compute in H; first [discriminate H | injection H as <- <-; split; [reflexivity | split; [reflexivity | vm_compute; discriminate]]] |]); exfalso; lia.
Qed.
Lemma lvl_mode_ovalue : forall ss c hn, 0 <= ss <= 26 -> lvl_mode ST_ovalue ss = Some (c, hn) -> c = CObj /\ hn = true /\ ss <> ST_finish.
Proof.
intros ss c hn R H. assert (CASES : exists k : nat, (k <= 26)%nat /\ ss = Z.of_nat k) by (exists (Z.to_nat ss); split; lia).
destruct CASES as (k & Hk & ->). clear R.
do 27 (destruct k as [|k]; [vm_compute in H; first [discriminate H | injection H as <- <-; split; [reflexivity | split; [reflexivity | vm_compute; discriminate]]] |]); exfalso; lia.
Qed.

Lemma lvl_mode_ws_ss_noadd : forall st ss c hn, zin st ws_states = true -> lvl_mode st ss = Some (c, hn) -> zin ss [ST_array_add; ST_ovadd] = false.
Proof.
intros st ss c hn H Hm.
assert (C : st = 0 \/ st = 4 \/ st = 5 \/ st = 6 \/ st = 7).
{ unfold zin, ws_states in H. cbn in H. rewrite !Bool.orb_true_iff in H. rewrite !Z.eqb_eq in H. intuition lia. }
destruct (zin ss [ST_array_add; ST_ovadd]) eqn:E; [| reflexivity]. exfalso.
assert (R : ss = 16 \/ ss = 22).
{ unfold zin in E. cbn in E. rewrite !Bool.orb_true_iff in E. rewrite !Z.eqb_eq in E. unfold ST_array_add, ST_ovadd in E. intuition lia. }
destruct C as [->|[->|[->|[->| ->]]]]; destruct R as [-> | ->]; vm_compute in Hm; discriminate Hm.
Qed.

Lemma lupd_sameS : forall {X} (ls : list X) i x, nth_error ls i = Some x -> lupd ls i x = ls.
Proof. induction ls as [|h t IH]; intros i x H; destruct i; cbn in *; try discriminate; [injection H as ->; reflexivity | rewrite IH by exact H; reflexivity]. Qed.
Lemma ts_lvl_same : forall ts l, nth_error (t_levels ts) (t_depth ts) = Some l -> ts_lvl ts l = ts.
Proof. intros [d lv co pb pbs x o os obs] l H. unfold ts_lvl. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *. rewrite (lupd_sameS lv d l H). reflexivity. Qed.
Lemma ts_lvl_obj_lvl : forall ts l2 l3 o os obs, ts_lvl (ts_lvl_obj ts l2 o os obs) l3 = ts_lvl_obj ts l3 o os obs.
Proof. intros. unfold ts_lvl, ts_lvl_obj; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs]. rewrite lupd_lupdS. reflexivity. Qed.
Lemma cur_st_lvl_obj : forall ts l l' o os obs, nth_error (t_levels ts) (t_depth ts) = Some l -> cur_st (ts_lvl_obj ts l' o os obs) = tl_st l'.
Proof. intros ts l l' o os obs Hl. unfold cur_st, ts_lvl_obj; cbn [t_levels t_depth]. rewrite nth_error_lupd_eq by (apply nth_error_Some; rewrite Hl; discriminate). reflexivity. Qed.

Lemma lvl_cur_restateG : forall segs Fn m depth l st' ss' c hn c',
lvl_cur segs Fn m depth depth l ->
lvl_mode (tl_st l) (tl_ss l) = Some (c, hn) ->
lvl_mode st' ss' = Some (c', hn) -> 0 <= st' <= 26 -> 0 <= ss' <= 26 ->
(c' = c \/ c' = CAny) ->
lvl_cur segs Fn m depth depth (TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
Proof.
intros segs Fn m depth l st' ss' c hn c' (R1 & R2 & J & M) Hm Hm' Hst Hss Hc.
rewrite Nat.ltb_irrefl, Nat.eqb_refl in M. destruct M as (c0 & hn0 & E0 & CLS & NM).
rewrite Hm in E0. injection E0 as <- <-.
split; [exact Hst|]. split; [exact Hss|]. split; [exact J|].
cbn [tl_st tl_ss tl_cs]. rewrite Nat.ltb_irrefl, Nat.eqb_refl.
exists c', hn. split; [exact Hm'|]. split.
- destruct Hc as [-> | ->]; [exact CLS | exact I].
- destruct hn; cbn in *; exact NM.
Qed.

Lemma tstack_lupd_srec : forall segs m q levels d l l',
tstack segs m q levels -> nth_error levels d = Some l -> srec_cells l' = srec_cells l -> tstack segs m q (lupd levels d l').
Proof.
intros segs m q levels d l l' TSK Hl E j lj Hj.
destruct (PeanoNat.Nat.eq_dec j d) as [-> | NE].
- rewrite nth_error_lupd_eq in Hj by (apply nth_error_Some; rewrite Hl; discriminate). injection Hj as <-. rewrite E. exact (TSK d l Hl).
- rewrite nth_error_lupd_neq in Hj by congruence. exact (TSK j lj Hj).
Qed.

Definition pe_restblocks (pf : pe_fix) (q : Z) (LB0 : list blk) (ts : tstate) : list blk :=
(t_pbs ts ++ t_objbs ts ++ concat (map lvl_blocks (lupd (t_levels ts) (t_depth ts) lvl_reset))) ++ (pf_tk pf, 72) :: (q, 32 * pf_mxd pf) :: LB0.

Lemma pe_blocksA_lvl_perm : forall pf q LB0 ts l l', nth_error (t_levels ts) (t_depth ts) = Some l ->
Permutation (pe_blocksA pf q LB0 (ts_lvl ts l')) (lvl_blocks l' ++ pe_restblocks pf q LB0 ts).
Proof.
intros pf q LB0 ts l l' Hl. unfold pe_blocksA, pe_restblocks, tstate_blocks, ts_lvl; cbn [t_pbs t_objbs t_levels t_depth].
rewrite (lupd_split _ _ _ l' Hl), (lupd_split _ _ _ lvl_reset Hl). change (lvl_blocks lvl_reset) with (@nil blk). rewrite app_nil_l. perm.
Qed.

Lemma pe_blocksA_cur_perm : forall pf q LB0 ts l, nth_error (t_levels ts) (t_depth ts) = Some l ->
Permutation (pe_blocksA pf q LB0 ts) (lvl_blocks l ++ pe_restblocks pf q LB0 ts).
Proof.
intros pf q LB0 ts l Hl. unfold pe_blocksA, pe_restblocks, tstate_blocks.
rewrite (concat_split _ _ _ Hl), (lupd_split _ _ _ lvl_reset Hl). change (lvl_blocks lvl_reset) with (@nil blk). rewrite app_nil_l. perm.
Qed.

Lemma pe_restblocks_other : forall pf q LB0 ts i li, i <> t_depth ts -> nth_error (t_levels ts) i = Some li -> incl (lvl_blocks li) (pe_restblocks pf q LB0 ts).
Proof.
intros pf q LB0 ts i li NE Hli b Hb. unfold pe_restblocks. apply in_or_app; left. apply in_or_app; right. apply in_or_app; right.
apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map. eapply (nth_error_In _ i). rewrite nth_error_lupd_neq by congruence. exact Hli.
Qed.

Definition pe_restblocks2 (pf : pe_fix) (q : Z) (LB0 : list blk) (ts : tstate) : list blk :=
(t_pbs ts ++ concat (map lvl_blocks (lupd (t_levels ts) (t_depth ts) lvl_reset))) ++ (pf_tk pf, 72) :: (q, 32 * pf_mxd pf) :: LB0.

Lemma pe_blocksA_lvl_obj_perm : forall pf q LB0 ts l l' o os obs, nth_error (t_levels ts) (t_depth ts) = Some l ->
Permutation (pe_blocksA pf q LB0 (ts_lvl_obj ts l' o os obs)) (lvl_blocks l' ++ obs ++ pe_restblocks2 pf q LB0 ts).
Proof.
intros pf q LB0 ts l l' o os obs Hl. unfold pe_blocksA, pe_restblocks2, tstate_blocks, ts_lvl_obj; cbn [t_pbs t_objbs t_levels t_depth].
rewrite (lupd_split _ _ _ l' Hl), (lupd_split _ _ _ lvl_reset Hl). change (lvl_blocks lvl_reset) with (@nil blk). rewrite app_nil_l. perm.
Qed.

Lemma pe_blocksA_cur_perm2 : forall pf q LB0 ts l, nth_error (t_levels ts) (t_depth ts) = Some l ->
Permutation (pe_blocksA pf q LB0 ts) (lvl_blocks l ++ t_objbs ts ++ pe_restblocks2 pf q LB0 ts).
Proof.
intros pf q LB0 ts l Hl. unfold pe_blocksA, pe_restblocks2, tstate_blocks.
rewrite (concat_split _ _ _ Hl), (lupd_split _ _ _ lvl_reset Hl). change (lvl_blocks lvl_reset) with (@nil blk). rewrite app_nil_l. perm.
Qed.

Lemma pe_restblocks2_other : forall pf q LB0 ts i li, i <> t_depth ts -> nth_error (t_levels ts) i = Some li -> incl (lvl_blocks li) (pe_restblocks2 pf q LB0 ts).
Proof.
intros pf q LB0 ts i li NE Hli b Hb. unfold pe_restblocks2. apply in_or_app; left. apply in_or_app; right.
apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map. eapply (nth_error_In _ i). rewrite nth_error_lupd_neq by congruence. exact Hli.
Qed.

Definition tx_err (x : tscal) (e : word) : tscal := TS (ts_isd x) (ts_stpos x) (ts_choff x) e (ts_ucs x) (ts_high x) (ts_quote x).

Definition ts_pbs (ts : tstate) (pbs : list blk) : tstate :=
TST (t_depth ts) (t_levels ts) (t_co ts) (t_pb ts) pbs (t_x ts) (t_obj ts) (t_objs ts) (t_objbs ts).

Definition PBOKat (m : word -> option byte) (ts : tstate) (b : Z) : Prop :=
exists buf bpos size pre post,
t_pbs ts = [(t_pb ts, PB_SZ); (buf, size)] /\ Z.of_nat (length pre) = bpos /\
pbuf_core asegs m (t_pb ts) buf bpos size (pre ++ [Z_to_bv 8 0] ++ post) /\ bpos <= b.
Definition PBOK (m : word -> option byte) (ts : tstate) (k : Z) : Prop := PBOKat m ts (t_co ts + k).

Lemma PBOKat_pbuf : forall m ts b, PBOKat m ts b -> pbuf asegs m (t_pbs ts) (t_pb ts).
Proof. intros m ts b (buf & bpos & size & pre & post & E & L & C & _). exists buf, bpos, size, pre, post. split; [exact E|]. split; [exact L | exact C]. Qed.

Lemma PBOKat_weaken : forall m ts b b', b <= b' -> PBOKat m ts b -> PBOKat m ts b'.
Proof. intros m ts b b' Hk (buf & bpos & size & pre & post & E & L & C & Hb). exists buf, bpos, size, pre, post. split; [exact E|]. split; [exact L|]. split; [exact C | lia]. Qed.
Lemma PBOKat_agree : forall BS m m' ts b, PBOKat m ts b -> agree_on asegs BS m m' -> incl (t_pbs ts) BS -> PBOKat m' ts b.
Proof.
intros BS m m' ts b (buf & bpos & size & pre & post & E & L & C & Hb) AG Hi. exists buf, bpos, size, pre, post.
split; [exact E|]. split; [exact L|]. split; [| exact Hb].
eapply (pbuf_core_agree asegs); [exact C | exact AG | apply Hi; rewrite E; left; reflexivity | apply Hi; rewrite E; right; left; reflexivity].
Qed.

Lemma PBOKat_same : forall m ts ts' b, t_pbs ts' = t_pbs ts -> t_pb ts' = t_pb ts -> PBOKat m ts b -> PBOKat m ts' b.
Proof. intros m ts ts' b E1 E2 (buf & bpos & size & pre & post & E & L & C & Hb). exists buf, bpos, size, pre, post. rewrite E1, E2. split; [exact E|]. split; [exact L|]. split; [exact C | exact Hb]. Qed.

Lemma PBOK_pbuf : forall m ts k, PBOK m ts k -> pbuf asegs m (t_pbs ts) (t_pb ts).
Proof. intros m ts k (buf & bpos & size & pre & post & E & L & C & _). exists buf, bpos, size, pre, post. split; [exact E|]. split; [exact L | exact C]. Qed.

Lemma PBOK_agree : forall BS m m' ts k, PBOK m ts k -> agree_on asegs BS m m' -> incl (t_pbs ts) BS -> PBOK m' ts k.
Proof.
intros BS m m' ts k (buf & bpos & size & pre & post & E & L & C & Hb) AG Hi. exists buf, bpos, size, pre, post.
split; [exact E|]. split; [exact L|]. split; [| exact Hb].
eapply (pbuf_core_agree asegs); [exact C | exact AG | apply Hi; rewrite E; left; reflexivity | apply Hi; rewrite E; right; left; reflexivity].
Qed.

Lemma PBOK_lvl : forall m ts k l', PBOK m ts k -> PBOK m (ts_lvl ts l') k.
Proof. intros m ts k l' H. exact H. Qed.

Lemma potential_step_memappend2 : forall len cap bpos n co,
pb_inv cap co -> 0 <= bpos -> 0 <= n -> bpos + n <= co + 1 -> 0 <= co <= len -> len < 2^26 ->
PhiPB len cap >= memappend_costX2 cap bpos n + PhiPB len (memappend_cap2 cap bpos n)
/\ pb_inv (memappend_cap2 cap bpos n) co /\ 0 <= PhiPB len (memappend_cap2 cap bpos n)
/\ memappend_costX cap bpos n <= PhiPB len cap.
Proof.
intros len cap bpos n co [H32 Hi] Hb Hn Hbn Hco Hlen. unfold PhiPB, memappend_costX2, memappend_cap2, memappend_costX, memappend_costB, pb_inv.
assert (Hsmall : (cap <? 2^30) = true) by (apply Z.ltb_lt; lia). rewrite Hsmall.
destruct (cap <=? bpos + n) eqn:E; destruct (cap <=? bpos + n + 1) eqn:E1;
try apply Z.leb_le in E; try apply Z.leb_gt in E; try apply Z.leb_le in E1; try apply Z.leb_gt in E1;
destruct (Z.max_spec (2 * cap) (bpos + n + 9)) as [[Hm Hx] | [Hm Hx]]; rewrite ?Hx; lia.
Qed.

Lemma PBOKat_appended : forall m ts b pb buf' cap' bpos (content src : list byte),
t_pb ts = pb -> t_pbs ts = [(pb, PB_SZ); (buf', cap')] ->
pbufc asegs m [(pb, PB_SZ); (buf', cap')] pb (firstn (Z.to_nat bpos) content ++ src) ->
0 <= bpos <= Z.of_nat (length content) -> bpos + Z.of_nat (length src) <= b ->
PBOKat m ts b.
Proof.
intros m ts b pb buf' cap' bpos content src Epb Epbs (buf2 & bpos2 & size2 & post2 & E2 & L2 & C2) Hb Hk.
exists buf2, bpos2, size2, (firstn (Z.to_nat bpos) content ++ src), post2.
rewrite Epb, Epbs. split; [exact E2|]. split; [exact L2|]. split; [exact C2|].
rewrite <- L2, length_app, length_firstn, Nat2Z.inj_add, Nat2Z.inj_min, Z2Nat.id by lia. lia.
Qed.

Lemma unpoisoned_sub2 : forall segs m SB s n s' n', unpoisoned segs m SB s n -> s <= s' -> s' + n' <= s + n -> 0 < n' -> unpoisoned segs m SB s' n'.
Proof.
intros segs m SB s n s' n' (Hn & Ha & (v & Hb & Hv) & Hc) H1 H2 H3. split; [exact H3|]. split; [| split].
- intros g Hg. apply Ha. Z.div_mod_to_equations. lia.
- destruct (Z_lt_ge_dec ((s' + n' - 1) / 8) ((s + n - 1) / 8)) as [Hlt | Hge].
+ exists 0. split; [| left; reflexivity]. apply Ha. Z.div_mod_to_equations. lia.
+ assert (E : (s' + n' - 1) / 8 = (s + n - 1) / 8) by (Z.div_mod_to_equations; lia).
exists v. rewrite E. split; [exact Hb|]. destruct Hv as [-> | [Hv8 Hm]]; [left; reflexivity | right]. split; [exact Hv8|]. Z.div_mod_to_equations. lia.
- intros w Hw. apply Hc. Z.div_mod_to_equations. lia.
Qed.

Definition pe_msS (pf : pe_fix) (pa : pe_fixA) (pc : Z) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state :=
let tk := pf_tk pf in
MS (mkR x1 (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2
(Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (shA (pa_F pa))) s3 (Z_to_bv 64 (tk + 20)) s5 (Z_to_bv 64 (tk + 36))
(Z_to_bv 64 (tk + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 A_SB) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None m (seg_rom asegs).

Lemma pe_frameA_cbyte : forall m pf pa cb nb pj sv,
pe_frameA asegs m pf pa cb nb pj sv -> bytes_at asegs m (pa_F pa + 64) [cb].
Proof.
intros m pf pa cb nb pj sv (_ & _ & _ & FF & _). unfold ff_cellsA in FF.
change [CB 24 (pj_fhd pj); CB 40 (pj_f1 pj); C1 cb; CB 183 (pj_f2 pj)] with ([CB 24 (pj_fhd pj); CB 40 (pj_f1 pj)] ++ ([C1 cb] ++ [CB 183 (pj_f2 pj)])) in FF.
apply (proj1 (rw_cells_app asegs _ _ _ _)) in FF as [_ FF]. apply (proj1 (rw_cells_app asegs _ _ _ _)) in FF as [FF _].
cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FF.
destruct FF as [[_ HB] _]. exact HB.
Qed.

Lemma pe_frameA_c_unpoisoned : forall m pf pa cb nb pj sv,
pe_geomA pf pa -> pe_frameA asegs m pf pa cb nb pj sv -> unpoisoned asegs m A_SB (pa_F pa + 64) 1.
Proof.
intros m pf pa cb nb pj sv (_ & _ & _ & GF & GF0 & _) (_ & _ & _ & _ & FSH).
unfold ffsh_cells, FSH0 in FSH. cbn [map] in FSH. unfold shA in FSH.
match type of FSH with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?c15 :: ?rest) =>
change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: c12 :: c13 :: c14 :: c15 :: rest)
with ([c0; c1; c2; c3; c4; c5; c6; c7] ++ ([c8; c9; c10; c11; c12; c13; c14; c15] ++ rest)) in FSH end.
apply (proj1 (rw_cells_app asegs _ _ _ _)) in FSH as [_ W]. apply (proj1 (rw_cells_app asegs _ _ _ _)) in W as [W _].
cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in W.
assert (E8 : (pa_F pa + 64 + 1 - 1) / 8 = pa_F pa / 8 + 8) by (clear - GF; Z.div_mod_to_equations; lia).
assert (Es : (pa_F pa + 64) / 8 = pa_F pa / 8 + 8) by (clear - GF; Z.div_mod_to_equations; lia).
pose proof W as [[_ WB] _]. cbn [cells_bytes cbytes app] in WB.
unfold unpoisoned. split; [lia|]. split; [intros g Hg; rewrite E8, Es in Hg; lia|]. split.
- exists 1. split; [| right; split; [lia | clear - GF; Z.div_mod_to_equations; lia]].
rewrite E8. replace (pa_F pa / 8 + 8 + A_SB) with (pa_F pa / 8 + A_SB + 8) by lia.
match type of WB with bytes_at _ _ _ (?b0 :: ?r) => change (b0 :: r) with ([b0] ++ r) in WB end.
apply (proj1 (bytes_at_app asegs _ _ _ _)) in WB as [WB1 _]. exact WB1.
- intros w Hw. rewrite E8, Es in Hw. exists [Z_to_bv 8 1; Z_to_bv 8 242; Z_to_bv 8 248; Z_to_bv 8 242; Z_to_bv 8 248; Z_to_bv 8 242; Z_to_bv 8 248; Z_to_bv 8 242]. split; [reflexivity|].
replace (w * 8) with (pa_F pa / 8 + A_SB + 8) by (unfold A_SB in *; clear - GF Hw; Z.div_mod_to_equations; lia). exact WB.
Qed.

Section WithIface.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.

Lemma tok_granA : forall A LB LM FR B m md tk i,
HEAPA A4L HIx A LB LM FR B m md -> In (tk, 72) LB -> 0 <= i < 9 ->
ro_cells asegs m (tk / 8 + i + A_SB) [C1 (Z_to_bv 8 0)].
Proof.
intros A LB LM FR B m md tk i HP Hin Hi.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ _ _ HP Hin) as SH. unfold shad in SH. cbn [hl_sb A4L] in SH.
pose proof (shadow_granule0 asegs m (tk / 8 + A_SB) 72 i ltac:(lia) ltac:(lia) SH) as G.
replace (tk / 8 + A_SB + i) with (tk / 8 + i + A_SB) in G by lia. exact G.
Qed.

Definition memappend_A_stmt2 : Prop :=
forall (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud) (lo pb n : Z) (T : TSet)
(t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 tp a0 a1 a2 : word)
(buf bpos cap b : Z) (content src : list byte) (errv : word) (A : ASA A4L HIx),
HEAPA A4L HIx A ((pb, PB_SZ) :: (buf, cap) :: LB) LM FRS B0 m0 md0 ->
pbuf_core asegs m0 pb buf bpos cap content -> 0 <= n < 2^31 ->
bytes_at asegs m0 b src -> Z.of_nat (length src) = n -> 0 <= b ->
src_locA LB FRS b n -> (0 < n -> unpoisoned asegs m0 A_SB b n) ->
stk asegs m0 lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 112 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m0 A_ERRNO [C4 errv] -> tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 pb -> a1 = Z_to_bv 64 b -> a2 = Z_to_bv 64 n ->
memappend_costX cap bpos n <= bB B0 ->
(forall ms' md' A', memappend_A_post_c HIx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 pb buf bpos cap content src n lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md0
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9a0ac) fc None m0 (seg_rom asegs)).

Lemma PE_BUD_restate : forall pf pa ts B l st' ss',
nth_error (t_levels ts) (t_depth ts) = Some l ->
PE_BUD pf pa ts B ->
PE_BUD pf pa (ts_lvl ts (TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B.
Proof.
intros pf pa ts B l st' ss' Hl H.
set (l' := TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
assert (Hblk : tstate_blocks (ts_lvl ts l') = tstate_blocks ts).
{ unfold tstate_blocks, ts_lvl; cbn [t_pbs t_objbs t_levels t_depth]. rewrite (map_lupd_same lvl_blocks (t_levels ts) (t_depth ts) l' l Hl eq_refl). reflexivity. }
unfold PE_BUD. rewrite Hblk. exact H.
Qed.

Lemma PE_REST_A_restateG : forall pf pa q LB0 LM FRS payload me lo m md A B ts errv l st' ss' c hn c',
PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts errv ->
nth_error (t_levels ts) (t_depth ts) = Some l ->
lvl_mode (tl_st l) (tl_ss l) = Some (c, hn) -> lvl_mode st' ss' = Some (c', hn) -> 0 <= st' <= 26 -> 0 <= ss' <= 26 -> (c' = c \/ c' = CAny) ->
(zin st' [ST_array_add; ST_ovadd] = zin (tl_st l) [ST_array_add; ST_ovadd] \/ (zin st' [ST_array_add; ST_ovadd] = false /\ t_objbs ts = [])) ->
PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B (ts_lvl ts (TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) errv.
Proof.
intros pf pa q LB0 LM FRS payload me lo m md A B ts errv l st' ss' c hn c' REST Hl Hm Hm' Hst Hss Hc Hz.
destruct REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD).
set (l' := TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
split.
{ match goal with |- HEAPA _ _ _ ?L _ _ _ _ _ => replace L with (pe_blocksA pf q LB0 ts); [exact HP |] end.
unfold pe_blocksA, tstate_blocks, ts_lvl; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs].
rewrite (map_lupd_same lvl_blocks (t_levels ts) (t_depth ts) l' l Hl eq_refl). reflexivity. }
split.
{ intros i li Hli. unfold ts_lvl in Hli |- *. cbn [t_levels t_depth] in Hli |- *.
destruct (PeanoNat.Nat.eq_dec i (t_depth ts)) as [-> | NE].
- rewrite nth_error_lupd_eq in Hli by exact Hd. injection Hli as <-.
eapply lvl_cur_restateG; [exact (LV (t_depth ts) l Hl) | exact Hm | exact Hm' | exact Hst | exact Hss | exact Hc].
- rewrite nth_error_lupd_neq in Hli by congruence. exact (LV i li Hli). }
split.
{ unfold cur_st, ts_lvl in *; cbn [t_levels t_depth t_objs t_objbs t_obj] in *. rewrite nth_error_lupd_eq by exact Hd. subst l'. cbn [tl_st].
rewrite Hl in OBJ. destruct Hz as [Hz | [Hz E]]; [rewrite Hz; exact OBJ | rewrite Hz; exact E]. }
split; [exact ST|]. split; [exact ERR|]. split; [exact STR|]. split; [exact PLEN|]. split; [exact SBin|]. split; [exact HPR|]. split; [exact MDV|]. split; [exact G|].
apply (PE_BUD_restate pf pa ts B l st' ss' Hl BUD).
Qed.

Lemma PBOKat_wtqA : forall pf pa q LB0 LM FRS B ts A m m' md lo W b,
PE_STATIC_A HIx pf pa lo -> HEAPA A4L HIx A (pe_blocksA pf q LB0 ts) LM ((pa_F pa, 2) :: FRS) B m md ->
PBOKat m ts b -> munch W m m' -> wmono asegs m m' -> Forall (pe_wtqA pf pa q) W -> PBOKat m' ts b.
Proof.
intros pf pa q LB0 LM FRS B ts A m m' md lo W b STC HP PBK MU WM HW.
eapply PBOKat_agree; [exact PBK | | apply incl_refl].
eapply (agree_wtqA HIx); [exact STC | exact HP | exact MU | exact WM | exact HW |].
intros a n Hin. assert (HinL : In (a, n) (pe_blocksA pf q LB0 ts ++ LM)) by (unfold pe_blocksA, tstate_blocks; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hin).
split; [exact HinL|].
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. unfold pe_blocksA in ND. rewrite <- app_assoc in ND. split.
- intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | left; reflexivity].
- intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | right; left; reflexivity].
Qed.

Lemma PBOK_wtqA : forall pf pa q LB0 LM FRS B ts A m m' md lo W k,
PE_STATIC_A HIx pf pa lo -> HEAPA A4L HIx A (pe_blocksA pf q LB0 ts) LM ((pa_F pa, 2) :: FRS) B m md ->
PBOK m ts k -> munch W m m' -> wmono asegs m m' -> Forall (pe_wtqA pf pa q) W -> PBOK m' ts k.
Proof.
intros pf pa q LB0 LM FRS B ts A m m' md lo W k STC HP PBK MU WM HW.
eapply PBOK_agree; [exact PBK | | apply incl_refl].
eapply (agree_wtqA HIx); [exact STC | exact HP | exact MU | exact WM | exact HW |].
intros a n Hin. assert (HinL : In (a, n) (pe_blocksA pf q LB0 ts ++ LM)) by (unfold pe_blocksA, tstate_blocks; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hin).
split; [exact HinL|].
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. unfold pe_blocksA in ND. rewrite <- app_assoc in ND. split.
- intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | left; reflexivity].
- intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | right; left; reflexivity].
Qed.

Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.

Lemma PE_REST_A_call_pb : forall pf pa q LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 ts errv errv2 LBc co2 pb2 pbs2 x2,
PE_STATIC_A HIx pf pa lo ->
PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m1 md A B ts errv ->
model_vm_only (cfg_model md) (cfg_model md2) ->
heap_pres A4H (LBc ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) m1 m2 ->
incl (t_objbs ts ++ concat (map lvl_blocks (t_levels ts)) ++ LB0) LBc ->
let ts2 := TST (t_depth ts) (t_levels ts) co2 pb2 pbs2 x2 (t_obj ts) (t_objs ts) (t_objbs ts) in
HEAPA A4L HIx A2 (pe_blocksA pf q LB0 ts2) LM ((pa_F pa, 2) :: FRS) B2 m2 md2 ->
stk asegs m2 lo (pf_spf pf) ->
rw_cells asegs m2 A_ERRNO [C4 errv2] ->
PE_BUD pf pa ts2 B2 ->
PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts2 errv2.
Proof.
intros pf pa q LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 ts errv errv2 LBc co2 pb2 pbs2 x2 STC
(HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD) VM12 HPRc Hincl ts2 HP2 ST2 ERR2 BUD2.
pose proof STC as (LO & LOS & GEO & _). pose proof GEO as (Gspf & Gsp0 & Gle & _).
assert (AG : agree_on asegs (t_objbs ts ++ concat (map lvl_blocks (t_levels ts)) ++ LB0) m1 m2).
{ eapply (agree_of_heap_pres asegs A4H); [exact HPRc | reflexivity |]. intros b Hb. apply in_or_app; left. exact (Hincl b Hb). }
assert (SBin2 := payload_locA_pres HIx pf pa LB0 FRS _ _ _ _ _ _ _ LBc _ _ _ HP (incl_tl _ (incl_refl _)) HPRc SBin).
assert (FRI : incl (fr_ivs A4L FRS) (LBc ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS))).
{ intros b Hb. apply in_or_app; right. apply in_or_app; right. unfold fr_ivs in *. cbn [flat_map]. apply in_or_app; right. exact Hb. }
split; [exact HP2|]. split; [| split; [| split; [exact ST2 | split; [exact ERR2 | split; [| split; [exact PLEN | split; [exact SBin2 | split; [| split; [| split; [| exact BUD2]]]]]]]]]].
- intros i l Hl. cbn. eapply (lvl_cur_agree asegs A4F); [exact (LV i l Hl) | exact AG |].
intros b Hb. apply in_or_app; right. apply in_or_app; left. apply in_concat. exists (lvl_blocks l). split; [| exact Hb]. apply in_map. eapply nth_error_In; exact Hl.
- revert OBJ. unfold cur_st. cbn [t_levels t_depth t_objs t_objbs t_obj]. destruct (zin _ _); intros OBJ; [| exact OBJ].
eapply (jopt_agree asegs A4F); [exact OBJ | exact AG | intros b Hb; apply in_or_app; left; exact Hb].
- eapply payload_presA; [exact HPRc | intros x Hx; apply in_or_app; left; apply Hincl; apply in_or_app; right; apply in_or_app; right; exact Hx | exact FRI | | exact STR | exact PLEN | exact SBin]. lia.
- eapply heap_presx_trans; [exact HPR|]. eapply heap_presx_weaken; [apply heap_pres_presx; exact HPRc | lia | | intros a Xa; exact Xa].
intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; apply Hincl; apply in_or_app; right; apply in_or_app; right; exact Hb|].
apply in_or_app; right. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right].
unfold fr_ivs in *. cbn [flat_map]. apply in_or_app; right. exact Hb.
- eapply model_vm_only_trans; [exact MDV | exact VM12].
- eapply GA_pres; [exact HPRc | exact G].
Qed.

Lemma PE_REST_A_callG : forall pf pa q LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 ts ts2 errv errv2 LBc,
PE_STATIC_A HIx pf pa lo ->
PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m1 md A B ts errv ->
model_vm_only (cfg_model md) (cfg_model md2) ->
heap_pres A4H (LBc ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) m1 m2 ->
incl LB0 LBc ->
HEAPA A4L HIx A2 (pe_blocksA pf q LB0 ts2) LM ((pa_F pa, 2) :: FRS) B2 m2 md2 ->
(forall i l, nth_error (t_levels ts2) i = Some l -> lvl_cur asegs A4F m2 (t_depth ts2) i l) ->
(if zin (cur_st ts2) [ST_array_add; ST_ovadd] then jopt asegs A4F (t_objs ts2) m2 (t_objbs ts2) (t_obj ts2) else t_objbs ts2 = []) ->
stk asegs m2 lo (pf_spf pf) ->
rw_cells asegs m2 A_ERRNO [C4 errv2] ->
PE_BUD pf pa ts2 B2 ->
PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts2 errv2.
Proof.
intros pf pa q LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 ts ts2 errv errv2 LBc STC
(HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD) VM12 HPRc Hincl HP2 LV2 OBJ2 ST2 ERR2 BUD2.
pose proof STC as (LO & LOS & GEO & _). pose proof GEO as (Gspf & Gsp0 & Gle & _).
split; [exact HP2|]. split; [exact LV2|]. split; [exact OBJ2|]. split; [exact ST2|]. split; [exact ERR2|].
assert (SBin2 := payload_locA_pres HIx pf pa LB0 FRS _ _ _ _ _ _ _ LBc _ _ _ HP (incl_tl _ (incl_refl _)) HPRc SBin).
assert (FRI : incl (fr_ivs A4L FRS) (LBc ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS))).
{ intros b Hb. apply in_or_app; right. apply in_or_app; right. unfold fr_ivs in *. cbn [flat_map]. apply in_or_app; right. exact Hb. }
split; [| split; [exact PLEN | split; [exact SBin2 | split; [| split; [| split; [| exact BUD2]]]]]].
- eapply payload_presA; [exact HPRc | intros x Hx; apply in_or_app; left; apply Hincl; exact Hx | exact FRI | | exact STR | exact PLEN | exact SBin]. lia.
- eapply heap_presx_trans; [exact HPR|]. eapply heap_presx_weaken; [apply heap_pres_presx; exact HPRc | lia | | intros a Xa; exact Xa].
intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; apply Hincl; exact Hb|].
apply in_or_app; right. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right].
unfold fr_ivs in *. cbn [flat_map]. apply in_or_app; right. exact Hb.
- eapply model_vm_only_trans; [exact MDV | exact VM12].
- eapply GA_pres; [exact HPRc | exact G].
Qed.

Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.

Lemma PE_INV_A_lvl_writeG : forall pf pa q LB0 LM FRS payload me lo m mc md A B ts cb nb pj sv errv l st' ss' c hn c',
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l ->
munch [(q + 32 * Z.of_nat (t_depth ts), q + 32 * Z.of_nat (t_depth ts) + 32)] m mc -> wmono asegs m mc -> mem_inv asegs mc ->
rw_cells asegs mc (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) (t_pb ts) (Z.of_nat (t_depth ts)) q (t_x ts)) ->
rw_cells asegs mc (q + 32 * Z.of_nat (t_depth ts)) (srec_cells (TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) ->
lvl_mode (tl_st l) (tl_ss l) = Some (c, hn) -> lvl_mode st' ss' = Some (c', hn) -> 0 <= st' <= 26 -> 0 <= ss' <= 26 -> (c' = c \/ c' = CAny) ->
(zin st' [ST_array_add; ST_ovadd] = zin (tl_st l) [ST_array_add; ST_ovadd] \/ (zin st' [ST_array_add; ST_ovadd] = false /\ t_objbs ts = [])) ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo mc md A B (ts_lvl ts (TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv
/\ (forall k, PBOK m ts k -> PBOK mc (ts_lvl ts (TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) k).
Proof.
intros pf pa q LB0 LM FRS payload me lo m mc md A B ts cb nb pj sv errv l st' ss' c hn c' STC [CORE REST] Hl MU WM MI TOKc Lc Hm Hm' Hst Hss Hc Hz.
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & (MX1 & _)) & _).
assert (HW : Forall (pe_wtqA pf pa q) [(q + 32 * Z.of_nat (t_depth ts), q + 32 * Z.of_nat (t_depth ts) + 32)]).
{ apply Forall_cons; [right; cbn [fst snd]; lia | apply Forall_nil]. }
assert (INq : In (q, 32 * pf_mxd pf) (pe_blocksA pf q LB0 ts)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
split.
- split.
+ unfold PE_CORE_A, ts_lvl; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOKc|]. split; [| split; [exact Hpb | split]].
* eapply (pbuf_wtqA HIx) with (ts := ts); [exact STC | exact (proj1 REST) | exact PB | exact MU | exact WM | exact HW].
* eapply (tstack_put asegs m _ q (t_levels ts) (t_depth ts) _ []); [exact TSK | exact Hd | exact MU | exact WM | intros; exact I | exact Lc].
* eapply (pe_frameA_blkwrite HIx) with (ts := ts); [exact STC | exact (proj1 REST) | | exact FR | exact MU | exact WM].
apply Forall_cons; [exists q, (32 * pf_mxd pf); cbn [fst snd]; split; [apply in_or_app; left; exact INq | lia] | apply Forall_nil].
+ eapply (PE_REST_A_restateG) with (c := c) (hn := hn) (c' := c'); [| exact Hl | exact Hm | exact Hm' | exact Hst | exact Hss | exact Hc | exact Hz].
eapply (PE_REST_A_private_write HIx GA GA_outside) with (ts := ts); [exact STC | exact REST | exact MU | exact WM | exact MI | apply pe_wtqA_private; exact HW].
- intros k PBK. apply PBOK_lvl. eapply PBOK_wtqA with (ts := ts); [exact STC | exact (proj1 REST) | exact PBK | exact MU | exact WM | exact HW].
Qed.

Lemma PE_INV_A_lvl_write : forall pf pa q LB0 LM FRS payload me lo m mc md A B ts cb nb pj sv errv l st' ss' c hn c',
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l ->
munch [(q + 32 * Z.of_nat (t_depth ts), q + 32 * Z.of_nat (t_depth ts) + 32)] m mc -> wmono asegs m mc -> mem_inv asegs mc ->
rw_cells asegs mc (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) (t_pb ts) (Z.of_nat (t_depth ts)) q (t_x ts)) ->
rw_cells asegs mc (q + 32 * Z.of_nat (t_depth ts)) (srec_cells (TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) ->
lvl_mode (tl_st l) (tl_ss l) = Some (c, hn) -> lvl_mode st' ss' = Some (c', hn) -> 0 <= st' <= 26 -> 0 <= ss' <= 26 -> (c' = c \/ c' = CAny) ->
zin st' [ST_array_add; ST_ovadd] = zin (tl_st l) [ST_array_add; ST_ovadd] ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo mc md A B (ts_lvl ts (TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv
/\ (forall k, PBOK m ts k -> PBOK mc (ts_lvl ts (TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) k).
Proof. intros until c'. intros STC INV Hl MU WM MI TOKc Lc Hm Hm' Hst Hss Hc Hz. eapply PE_INV_A_lvl_writeG; eauto. Qed.

Lemma PE_INV_A_idwrite : forall pf pa q LB0 LM FRS payload me lo m mc md A B ts cb nb pj sv errv l,
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l ->
munch [(q + 32 * Z.of_nat (t_depth ts), q + 32 * Z.of_nat (t_depth ts) + 32)] m mc -> wmono asegs m mc -> mem_inv asegs mc ->
rw_cells asegs mc (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) (t_pb ts) (Z.of_nat (t_depth ts)) q (t_x ts)) ->
rw_cells asegs mc (q + 32 * Z.of_nat (t_depth ts)) (srec_cells l) ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo mc md A B ts cb nb pj sv errv /\ (forall b, PBOKat m ts b -> PBOKat mc ts b).
Proof.
intros pf pa q LB0 LM FRS payload me lo m mc md A B ts cb nb pj sv errv l STC INV Hl MU WM MI TOKc Lc.
pose proof (proj1 (proj2 (proj2 INV)) _ _ Hl) as (R1 & R2 & _ & Md). rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c & hn & Hm & _).
destruct (PE_INV_A_lvl_write pf pa q LB0 LM FRS payload me lo m mc md A B ts cb nb pj sv errv l (tl_st l) (tl_ss l) c hn c STC INV Hl MU WM MI TOKc
ltac:(destruct l; exact Lc) Hm Hm R1 R2 (or_introl eq_refl) eq_refl) as [INV' PBK'].
assert (E : ts_lvl ts (TL (tl_st l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)) = ts) by (apply ts_lvl_same; destruct l; exact Hl).
rewrite E in INV', PBK'. split; [exact INV'|].
intros b PBK. specialize (PBK' (b - t_co ts)). unfold PBOK in PBK'. replace (t_co ts + (b - t_co ts)) with b in PBK' by lia. exact (PBK' PBK).
Qed.

Definition ts_push (ts : tstate) (lp : tlevel) : tstate :=
TST (S (t_depth ts)) (lupd (lupd (t_levels ts) (t_depth ts) lp) (S (t_depth ts)) (TL ST_eatws ST_start 0 None [] 0 []))
(t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (t_obj ts) (t_objs ts) (t_objbs ts).

Lemma PE_INV_A_push : forall pf pa q LB0 LM FRS payload me lo m mc md A B ts cb nb pj sv errv l stp,
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> (S (t_depth ts) < Z.to_nat (pf_mxd pf))%nat -> t_objbs ts = [] ->
munch [(pf_tk pf, pf_tk pf + 72); (q + 32 * Z.of_nat (t_depth ts), q + 32 * Z.of_nat (t_depth ts) + 64)] m mc -> wmono asegs m mc -> mem_inv asegs mc ->
rw_cells asegs mc (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) (t_pb ts) (Z.of_nat (S (t_depth ts))) q (t_x ts)) ->
rw_cells asegs mc (q + 32 * Z.of_nat (t_depth ts)) (srec_cells (TL stp (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) ->
rw_cells asegs mc (q + 32 * Z.of_nat (S (t_depth ts))) (srec_cells (TL ST_eatws ST_start 0 None [] 0 [])) ->
(forall c hn, lvl_mode (tl_st l) (tl_ss l) = Some (c, hn) -> (stp = ST_array_add /\ c = CArr /\ hn = false) \/ (stp = ST_ovadd /\ c = CObj /\ hn = true)) ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo mc md A B (ts_push ts (TL stp (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv
/\ (forall b, PBOKat m ts b -> PBOKat mc (ts_push ts (TL stp (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) b).
Proof.
intros pf pa q LB0 LM FRS payload me lo m mc md A B ts cb nb pj sv errv l stp STC [CORE REST] Hl Hd1 Eobj MU WM MI TOKc Lp Ln Hmode.
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
unfold ts_push.
set (lp := TL stp (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)) in *.
set (ln := TL ST_eatws ST_start 0 None [] 0 []) in *.
pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & (MX1 & _)) & _).
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
assert (Hd1' : (S (t_depth ts) < length (t_levels ts))%nat) by (rewrite LEN32; exact Hd1).
destruct (nth_error (t_levels ts) (S (t_depth ts))) as [l1|] eqn:Hl1; [| apply nth_error_None in Hl1; lia].
assert (HW : Forall (pe_wtqA pf pa q) [(pf_tk pf, pf_tk pf + 72); (q + 32 * Z.of_nat (t_depth ts), q + 32 * Z.of_nat (t_depth ts) + 64)]).
{ apply Forall_cons; [left; left; cbn [fst snd]; lia |]. apply Forall_cons; [| apply Forall_nil]. right. cbn [fst snd]. lia. }
assert (INq : In (q, 32 * pf_mxd pf) (pe_blocksA pf q LB0 ts)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
assert (INtk : In (pf_tk pf, 72) (pe_blocksA pf q LB0 ts)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
pose proof (proj1 REST) as HP.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ (pf_tk pf) 72 q (32 * pf_mxd pf) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.

pose proof (PE_REST_A_private_write HIx GA GA_outside _ _ _ _ _ _ _ _ _ _ mc _ _ _ ts _ _ STC REST MU WM MI (pe_wtqA_private _ _ _ _ _ HW)) as REST'.
destruct REST' as (HP' & LV' & OBJ' & ST' & ERR' & STR' & PLEN' & SBin' & HPR' & MDV' & G' & BUD').
pose proof (LV' _ _ Hl) as LVd. pose proof (LV' _ _ Hl1) as LV1.
assert (CL1 : lvl_clean l1).
{ destruct LV1 as (_ & _ & _ & M1). replace (S (t_depth ts) <? t_depth ts)%nat with false in M1 by (symmetry; apply Nat.ltb_ge; lia).
replace (S (t_depth ts) =? t_depth ts)%nat with false in M1 by (symmetry; apply Nat.eqb_neq; lia). exact M1. }
destruct CL1 as (C1 & C2 & C3 & C4 & C5).
assert (Eblk : map lvl_blocks (lupd (lupd (t_levels ts) (t_depth ts) lp) (S (t_depth ts)) ln) = map lvl_blocks (t_levels ts)).
{ rewrite (map_lupd_same lvl_blocks (lupd (t_levels ts) (t_depth ts) lp) (S (t_depth ts)) ln l1);
[| rewrite nth_error_lupd_neq by lia; exact Hl1 | unfold lvl_blocks, ln; cbn [tl_cbs tl_nbs]; rewrite C3, C5; reflexivity].
apply (map_lupd_same lvl_blocks (t_levels ts) (t_depth ts) lp l Hl). reflexivity. }
split.
- split.
+ unfold PE_CORE_A; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. split; [rewrite !lupd_length; exact LEN32|]. split; [exact Hd1|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOKc|]. split; [| split; [exact Hpb | split]].
* eapply (pbuf_wtqA HIx) with (ts := ts); [exact STC | exact HP | exact PB | exact MU | exact WM | exact HW].
* intros j lj Hj.
destruct (PeanoNat.Nat.eq_dec j (S (t_depth ts))) as [-> | N1]; [rewrite nth_error_lupd_eq in Hj by (rewrite lupd_length; lia); injection Hj as <-; exact Ln|].
rewrite nth_error_lupd_neq in Hj by congruence.
destruct (PeanoNat.Nat.eq_dec j (t_depth ts)) as [-> | N0]; [rewrite nth_error_lupd_eq in Hj by lia; injection Hj as <-; exact Lp|].
rewrite nth_error_lupd_neq in Hj by congruence.
pose proof (nth_error_Some_length Hj) as Hjl.
eapply rw_cells_transport; [exact (TSK j lj Hj) | exact MU | exact WM |]. rewrite srec_cells_size. cbn [disjoint_from fst snd Z.of_nat].
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP (in_or_app _ LM _ (or_introl INq))) as (_ & _ & _ & _ & _).
split; [| split; [| exact I]]; lia.
* eapply (pe_frameA_blkwrite HIx) with (ts := ts); [exact STC | exact HP | | exact FR | exact MU | exact WM].
apply Forall_cons; [exists (pf_tk pf), 72; cbn [fst snd]; split; [apply in_or_app; left; exact INtk | lia] |].
apply Forall_cons; [exists q, (32 * pf_mxd pf); cbn [fst snd]; split; [apply in_or_app; left; exact INq | lia] | apply Forall_nil].
+ split.
{ match goal with |- HEAPA _ _ _ ?L _ _ _ _ _ => replace L with (pe_blocksA pf q LB0 ts); [exact HP' |] end.
unfold pe_blocksA, tstate_blocks; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs]. rewrite Eblk. reflexivity. }
split.
{ cbn [t_levels t_depth]. intros i li Hli.
destruct (PeanoNat.Nat.eq_dec i (S (t_depth ts))) as [-> | N1].
- rewrite nth_error_lupd_eq in Hli by (rewrite lupd_length; lia). injection Hli as <-.
split; [cbn; unfold ST_eatws; lia|]. split; [cbn; unfold ST_start; lia|]. split; [cbn; split; reflexivity|].
rewrite Nat.ltb_irrefl, Nat.eqb_refl. exists CNone, false. split; [reflexivity|]. split; [exact I|]. cbn. split; reflexivity.
- rewrite nth_error_lupd_neq in Hli by congruence.
destruct (PeanoNat.Nat.eq_dec i (t_depth ts)) as [-> | N0].
+ rewrite nth_error_lupd_eq in Hli by lia. injection Hli as <-.
destruct LVd as (R1 & R2 & J & Md). rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c & hn & Hm & CLS & NM).
assert (Elt : (t_depth ts <? S (t_depth ts))%nat = true) by (apply Nat.ltb_lt; lia).
destruct (Hmode c hn Hm) as [(-> & -> & ->) | (-> & -> & ->)].
* split; [cbn; unfold ST_array_add; lia|]. split; [exact R2|]. split; [exact J|]. rewrite Elt. left. split; [reflexivity|]. split; [exact CLS | exact NM].
* split; [cbn; unfold ST_ovadd; lia|]. split; [exact R2|]. split; [exact J|]. rewrite Elt. right. split; [reflexivity|]. split; [exact CLS | exact NM].
+ rewrite nth_error_lupd_neq in Hli by congruence. pose proof (LV' i li Hli) as (R1 & R2 & J & M).
split; [exact R1|]. split; [exact R2|]. split; [exact J|].
destruct (Nat.ltb_spec i (t_depth ts)) as [Hlt | Hge].
* replace (i <? S (t_depth ts))%nat with true by (symmetry; apply Nat.ltb_lt; lia). exact M.
* replace (i =? t_depth ts)%nat with false in M by (symmetry; apply Nat.eqb_neq; lia).
replace (i <? S (t_depth ts))%nat with false by (symmetry; apply Nat.ltb_ge; lia).
replace (i =? S (t_depth ts))%nat with false by (symmetry; apply Nat.eqb_neq; lia). exact M. }
split.
{ unfold cur_st. cbn [t_levels t_depth t_objs t_objbs t_obj]. rewrite nth_error_lupd_eq by (rewrite lupd_length; lia). cbn. exact Eobj. }
split; [exact ST'|]. split; [exact ERR'|]. split; [exact STR'|]. split; [exact PLEN'|]. split; [exact SBin'|]. split; [exact HPR'|]. split; [exact MDV'|]. split; [exact G'|].
unfold PE_BUD, tstate_blocks in *. cbn [t_pbs t_objbs t_levels]. rewrite Eblk. exact BUD'.
- intros b PBK. eapply PBOKat_same with (ts := ts); [reflexivity | reflexivity |].
eapply PBOKat_agree; [exact PBK | | apply incl_refl].
eapply (agree_wtqA HIx); [exact STC | exact HP | exact MU | exact WM | exact HW |].
intros a n Hin. assert (HinL : In (a, n) (pe_blocksA pf q LB0 ts ++ LM)) by (unfold pe_blocksA, tstate_blocks; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hin).
split; [exact HinL|].
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. unfold pe_blocksA in ND. rewrite <- app_assoc in ND. split.
+ intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | left; reflexivity].
+ intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | right; left; reflexivity].
Qed.

Lemma ts_push_cur : forall ts lp, (S (t_depth ts) < length (t_levels ts))%nat ->
nth_error (t_levels (ts_push ts lp)) (t_depth (ts_push ts lp)) = Some (TL ST_eatws ST_start 0 None [] 0 []).
Proof. intros ts lp H. unfold ts_push. cbn [t_levels t_depth]. apply nth_error_lupd_eq. rewrite lupd_length. exact H. Qed.

Lemma PE_INV_A_next_clean : forall pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv l1,
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
nth_error (t_levels ts) (S (t_depth ts)) = Some l1 -> lvl_blocks l1 = [].
Proof.
intros pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv l1 INV H1.
pose proof (proj1 (proj2 (proj2 INV)) _ _ H1) as (_ & _ & _ & M1).
replace (S (t_depth ts) <? t_depth ts)%nat with false in M1 by (symmetry; apply Nat.ltb_ge; lia).
replace (S (t_depth ts) =? t_depth ts)%nat with false in M1 by (symmetry; apply Nat.eqb_neq; lia).
destruct M1 as (_ & _ & C3 & _ & C5). unfold lvl_blocks. rewrite C3, C5. reflexivity.
Qed.

Lemma PE_INV_A_set_obj : forall pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv obj' objs',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> t_objbs ts = [] ->
(if zin (cur_st ts) [ST_array_add; ST_ovadd] then jopt asegs A4F objs' m [] obj' else True) ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B
(TST (t_depth ts) (t_levels ts) (t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) obj' objs' []) cb nb pj sv errv.
Proof.
intros pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv obj' objs' [CORE REST] E OBJ'.
destruct ts as [depth levels co pb pbs x obj objs objbs]. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *. subst objbs.
split; [exact CORE|].
destruct REST as (HP & LV & OBJ & RESTT). split; [exact HP|]. split; [exact LV|]. split; [| exact RESTT].
unfold cur_st in *. cbn [t_depth t_levels t_obj t_objs t_objbs] in *. destruct (zin _ _); [exact OBJ' | reflexivity].
Qed.

Lemma pe_frameA_scan : forall pf pa q LB0 LM FRS B ts A m mc md lo cb nb pj sv cb',
PE_STATIC_A HIx pf pa lo -> HEAPA A4L HIx A (pe_blocksA pf q LB0 ts) LM ((pa_F pa, 2) :: FRS) B m md ->
pe_frameA asegs m pf pa cb nb pj sv ->
munch [(pf_tk pf, pf_tk pf + 72); (pa_F pa + 64, pa_F pa + 65)] m mc -> wmono asegs m mc ->
rw_cells asegs mc (pa_F pa) (ff_cellsA cb' pj) ->
pe_frameA asegs mc pf pa cb' nb pj sv.
Proof.
intros pf pa q LB0 LM FRS B ts A m mc md lo cb nb pj sv cb' STC HP (SLOTS & GAP & SAVED & _ & FSH) MU WM FFc.
pose proof STC as (LO & LOS & GEO & HT & SP0 & _). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
pose proof alloc_ceiling_range as ACR.
assert (INtk : In (pf_tk pf, 72) (pe_blocksA pf q LB0 ts ++ LM)) by (apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INF : In (pa_F pa, 2) ((pa_F pa, 2) :: FRS)) by (left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP INtk) as (_ & _ & Htlo & Hthi & _).
pose proof (shadow_blk_apart HIx _ _ _ _ _ _ _ _ _ (pa_F pa) 32 HP INtk ltac:(lia) ltac:(lia) ltac:(lia)) as DSt.
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as DSF. rewrite fr_size_2 in DSF. cbn [hl_sb A4L] in DSF.
pose proof (pe_slotsA_size pf pa nb pj) as SZ.
split; [| split; [| split; [| split; [exact FFc|]]]].
- eapply rw_cells_transport; [exact SLOTS | exact MU | exact WM |]. rewrite SZ. cbn [disjoint_from fst snd]. lia.
- eapply rw_cells_transport; [exact GAP | exact MU | exact WM |]. cbn [cells_size csize disjoint_from fst snd]. lia.
- eapply rw_cells_transport; [exact SAVED | exact MU | exact WM |]. cbn [pe_savedA_cells cells_size csize disjoint_from fst snd Nat.add]. lia.
- eapply rw_cells_transport; [exact FSH | exact MU | exact WM |]. cbn [disjoint_from fst snd]. unfold shA, A_SB in *.
change (Z.of_nat (cells_size (ffsh_cells FSH0))) with 32. Z.div_mod_to_equations. lia.
Qed.

Definition ts_set_x (ts : tstate) (co' : Z) (x' : tscal) : tstate :=
TST (t_depth ts) (t_levels ts) co' (t_pb ts) (t_pbs ts) x' (t_obj ts) (t_objs ts) (t_objbs ts).

Lemma PE_REST_A_set_x : forall pf pa q LB0 LM FRS payload me lo m md A B ts errv co' x',
PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts errv ->
PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B (ts_set_x ts co' x') errv.
Proof. intros until x'. intros H. destruct ts. exact H. Qed.

Lemma PE_INV_A_tokw : forall pf pa q LB0 LM FRS payload me lo m mc md A B ts cb nb pj sv errv W co' x' cb' nb',
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
munch W m mc -> wmono asegs m mc -> mem_inv asegs mc -> Forall (pe_wtfA pf pa) W ->
rw_cells asegs mc (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) (t_pb ts) (Z.of_nat (t_depth ts)) q x') ->
pe_frameA asegs mc pf pa cb' nb' pj sv ->
0 <= co' <= pf_len pf -> ts_choff x' = Z_to_bv 64 co' ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo mc md A B (ts_set_x ts co' x') cb' nb' pj sv errv
/\ (forall b, PBOKat m ts b -> PBOKat mc (ts_set_x ts co' x') b).
Proof.
intros pf pa q LB0 LM FRS payload me lo m mc md A B ts cb nb pj sv errv W co' x' cb' nb' STC [CORE REST] MU WM MI HW TOKc FRc Hco Hch.
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
split.
- split.
+ unfold PE_CORE_A, ts_set_x; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. split; [exact LEN32|]. split; [exact D32|]. split; [exact Hco|]. split; [exact Hch|].
split; [exact TOKc|]. split; [| split; [exact Hpb | split; [| exact FRc]]].
* eapply (pbuf_wtfA HIx) with (ts := ts); [exact STC | exact (proj1 REST) | exact PB | exact MU | exact WM | exact HW].
* eapply (tstack_wtfA HIx) with (ts := ts); [exact STC | exact (proj1 REST) | exact TSK | exact LEN32 | exact MU | exact WM | exact HW].
+ apply PE_REST_A_set_x.
eapply (PE_REST_A_private_write HIx GA GA_outside) with (ts := ts); [exact STC | exact REST | exact MU | exact WM | exact MI | apply pe_wtfA_private; exact HW].
- intros b PBK. eapply PBOKat_same with (ts := ts); [reflexivity | reflexivity |].
eapply PBOKat_agree; [exact PBK | | apply incl_refl].
eapply (agree_wtqA HIx); [exact STC | exact (proj1 REST) | exact MU | exact WM | apply pe_wtfA_wtqA; exact HW |].
intros a n Hin. assert (HinL : In (a, n) (pe_blocksA pf q LB0 ts ++ LM)) by (unfold pe_blocksA, tstate_blocks; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hin).
split; [exact HinL|].
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ (proj1 REST)) as ND. unfold pe_blocksA in ND. rewrite <- app_assoc in ND. split.
+ intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | left; reflexivity].
+ intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | right; left; reflexivity].
Qed.

Lemma PE_INV_A_tokw1 : forall pf pa q LB0 LM FRS payload me lo m mc md A B ts cb nb pj sv errv co' x',
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
munch [(pf_tk pf, pf_tk pf + 72)] m mc -> wmono asegs m mc -> mem_inv asegs mc ->
rw_cells asegs mc (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) (t_pb ts) (Z.of_nat (t_depth ts)) q x') ->
0 <= co' <= pf_len pf -> ts_choff x' = Z_to_bv 64 co' ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo mc md A B (ts_set_x ts co' x') cb nb pj sv errv
/\ (forall b, PBOKat m ts b -> PBOKat mc (ts_set_x ts co' x') b).
Proof.
intros pf pa q LB0 LM FRS payload me lo m mc md A B ts cb nb pj sv errv co' x' STC INV MU WM MI TOKc Hco Hch.
eapply PE_INV_A_tokw; [exact STC | exact INV | exact MU | exact WM | exact MI | | exact TOKc | | exact Hco | exact Hch].
- apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil].
- destruct INV as [CORE REST]. destruct CORE as (_ & _ & _ & _ & _ & _ & _ & _ & FR).
eapply (pe_frameA_blkwrite HIx) with (ts := ts); [exact STC | exact (proj1 REST) | | exact FR | exact MU | exact WM].
apply Forall_cons; [exists (pf_tk pf), 72; cbn [fst snd]; split; [apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; left; reflexivity | lia] | apply Forall_nil].
Qed.
End WithIface.
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
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw QkMG. Import QG8z.
Import Qhd4 Qwm6.
Import QbFI Qwm6.Mq4 QlKV.Mqi QsKa.Mqd Qiiq QSHS Ql4f.Mq4 Qc5u.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section PeRedoA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.

Lemma seg_dispj_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(gp t0 a2 a3 a5 a6 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l ->
(forall (a5' : word),
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA (tl_st l)) (t_co ts) gp t0
(Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l)) (Z_to_bv 64 0)
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) a5' (Z_to_bv 64 APE_JTAB) a7
s3 (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m)) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_DISPJ (t_co ts) gp t0 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 1) a2 a3 (Z_to_bv 64 0) a5 a6 a7
s3 (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC INV Hl K.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH). unfold pe_msA in *.
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold pe_savedA_cells in SAVED. unfold ff_cellsA in FF. unfold ffsh_cells, FSH0 in FSH. cbn [map] in FSH.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (LV depth l Hl) as (ST26 & SS26 & _).
pose proof (TSK depth l Hl) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld. unfold srec_cells in Ld.
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd (Z.of_nat depth) 0 HP INq ltac:(lia) ltac:(lia)) as SHQ.
replace (q / 8 + 4 * Z.of_nat depth + 0 + A_SB) with (q / 8 + 4 * Z.of_nat depth + A_SB) in SHQ by lia.
pose proof (pe_jtabA_ro m MI) as JT. unfold pe_jtabA in JT.
unfold APE_REDO, APE_REDO0, APE_DISPJ, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t. stash Himg_q.
clear PB REST LV TSK.
reenterA asegs A4L HIx asegs_wx HP.
assert (BLO : 0 < bse < 2^63 /\ q <= bse) by (subst bse; lia).
assert (BAL16 : bse mod 16 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
replace (q + 32 * Z.of_nat depth) with bse by lia.
step. step. step. step. ub_nowrap bse q (Z.of_nat depth). step. if_true.
step. step. if_true.
step. rewrite (unsigned_lit bse) by lia. rewrite (land7_of_mod16 bse BAL16). step. if_true.
step. step. sh_norm.
replace (bse / 8) with (q / 8 + 4 * Z.of_nat depth) by (subst bse; symmetry; apply div8_add_mul32; lia).
step. step. if_true.
step. norm_sx32. step. step. if_truex.
step.
rewrite (unsigned_lit (tl_st l)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
step. step.
assert (CASES : exists k : nat, (k <= 26)%nat /\ tl_st l = Z.of_nat k) by (exists (Z.to_nat (tl_st l)); split; lia).
destruct CASES as (k & Hk & Ek). rewrite Ek in *.
do 27 (destruct k as [|k];
[ match goal with |- context [Z_to_bv 64 (Z.of_nat ?n * 4)] =>
let v := eval vm_compute in (Z.of_nat n * 4) in change (Z.of_nat n * 4) with v;
let w := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with w end;
step; step;
match goal with |- context [sext 64 (bv_extract 0 32 (le_bytes_to_word ?bs))] =>
let v := eval vm_compute in (bv_unsigned (sext 64 (bv_extract 0 32 (le_bytes_to_word bs)))) in
replace (sext 64 (bv_extract 0 32 (le_bytes_to_word bs))) with (Z_to_bv 64 v) by (apply bv_eq; vm_compute; reflexivity) end;
step; step;
subst bse; evt_done5; apply K
| ]).
exfalso. lia.
Qed.

Lemma seg_redo_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(gp t0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l ->
(forall (a5' : word),
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA (tl_st l)) (t_co ts) gp t0
(Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l)) (Z_to_bv 64 0)
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) a5' (Z_to_bv 64 APE_JTAB) a7
s3 (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m)) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_REDO (t_co ts) gp t0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC INV Hl K. pose proof INV as INV0. revert INV.
intros INV.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH). unfold pe_msA in *.
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold pe_savedA_cells in SAVED. unfold ff_cellsA in FF. unfold ffsh_cells, FSH0 in FSH. cbn [map] in FSH.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (LV depth l Hl) as (ST26 & SS26 & _).
pose proof (TSK depth l Hl) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld. unfold srec_cells in Ld.
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd (Z.of_nat depth) 0 HP INq ltac:(lia) ltac:(lia)) as SHQ.
replace (q / 8 + 4 * Z.of_nat depth + 0 + A_SB) with (q / 8 + 4 * Z.of_nat depth + A_SB) in SHQ by lia.
pose proof (pe_jtabA_ro m MI) as JT. unfold pe_jtabA in JT.
unfold APE_REDO, APE_REDO0, APE_DISPJ, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t. stash Himg_q.
clear PB REST LV TSK.
reenterA asegs A4L HIx asegs_wx HP.
assert (BLO : 0 < bse < 2^63 /\ q <= bse) by (subst bse; lia).
assert (BAL16 : bse mod 16 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
step. step. step. if_true.
step. step. step. step. rewrite ?sxb_zero, ?zxb_zero. if_false.
step.
step. norm_sx32.
step. step.
rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
replace (q + Z.of_nat depth * 32) with bse by lia.
step. step.
ub_nzpair q bse.
step. if_false. step.
subst bse. evt_done5.
eapply (seg_dispj_A (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 l cb nb pj sv errv T gp t0); [exact STC | exact INV0 | exact Hl | exact K].
Qed.

Lemma seg_redo0_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(gp t0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l ->
(forall (a5' : word),
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA (tl_st l)) (t_co ts) gp t0
(Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l)) (Z_to_bv 64 0)
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) a5' (Z_to_bv 64 APE_JTAB) a7
s3 (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m)) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_REDO0 (t_co ts) gp t0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC INV Hl K. pose proof INV as INV0. revert INV.
intros INV.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH). unfold pe_msA in *.
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold pe_savedA_cells in SAVED. unfold ff_cellsA in FF. unfold ffsh_cells, FSH0 in FSH. cbn [map] in FSH.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (LV depth l Hl) as (ST26 & SS26 & _).
pose proof (TSK depth l Hl) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld. unfold srec_cells in Ld.
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd (Z.of_nat depth) 0 HP INq ltac:(lia) ltac:(lia)) as SHQ.
replace (q / 8 + 4 * Z.of_nat depth + 0 + A_SB) with (q / 8 + 4 * Z.of_nat depth + A_SB) in SHQ by lia.
pose proof (pe_jtabA_ro m MI) as JT. unfold pe_jtabA in JT.
unfold APE_REDO, APE_REDO0, APE_DISPJ, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t. stash Himg_q.
clear PB REST LV TSK.
reenterA asegs A4L HIx asegs_wx HP.
assert (BLO : 0 < bse < 2^63 /\ q <= bse) by (subst bse; lia).
assert (BAL16 : bse mod 16 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
step. step. step. if_true.
step. step. step. step. rewrite ?sxb_zero, ?zxb_zero. if_true.
step.
step. norm_sx32.
step. step.
rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
replace (Z.of_nat depth * 32 + q) with bse by lia.
step. step.
ub_nzpair q bse.
step. if_true.
subst bse. evt_done5.
eapply (seg_dispj_A (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 l cb nb pj sv errv T gp t0); [exact STC | exact INV0 | exact Hl | exact K].
Qed.

End PeRedoA.
End RC__1.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import QG8z Qdyh.Mq0. Import QKQo.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqd Qiiq QsKa.Mqf Q4v2 QSHS Ql4f.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.

Ltac sh_normO :=
sh_norm;
repeat match goal with
| |- context [ (?p + ?j) / 8 ] => is_Zlit j; rewrite (div8_add p j) by lia; let k := eval vm_compute in (Z.div j 8) in change (j / 8) with k
end;
rewrite ?Z.add_0_r.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition ts_lvl (ts : tstate) (l : tlevel) : tstate :=
TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) l) (t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (t_obj ts) (t_objs ts) (t_objbs ts).

Definition ts_lvl_obj (ts : tstate) (l : tlevel) (obj : Z) (objs : option jshape) (objbs : list blk) : tstate :=
TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) l) (t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) obj objs objbs.

Lemma lupd_lupdS : forall {X} (l : list X) i (x y : X), lupd (lupd l i x) i y = lupd l i y.
Proof. induction l as [|h t IH]; intros [|i] x y; cbn; try reflexivity. f_equal. apply IH. Qed.
Lemma ts_lvl_lvl : forall ts l2 l3, ts_lvl (ts_lvl ts l2) l3 = ts_lvl ts l3.
Proof. intros ts l2 l3. unfold ts_lvl; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs]. rewrite lupd_lupdS. reflexivity. Qed.

Lemma lvl_mode_array : forall st ss c hn, (st = ST_array \/ st = ST_array_after_sep) -> 0 <= ss <= 26 -> lvl_mode st ss = Some (c, hn) -> c = CArr /\ hn = false /\ ss <> ST_finish.
Proof.
intros st ss c hn Hst R H. assert (CASES : exists k : nat, (k <= 26)%nat /\ ss = Z.of_nat k) by (exists (Z.to_nat ss); split; lia).
destruct CASES as (k & Hk & ->). clear R.
destruct Hst as [-> | ->]; do 27 (destruct k as [|k]; [vm_compute in H; first [discriminate H | injection H as <- <-; split; [reflexivity | split; [reflexivity | vm_compute; discriminate]]] |]); exfalso; lia.
Qed.
Lemma lvl_mode_ovalue : forall ss c hn, 0 <= ss <= 26 -> lvl_mode ST_ovalue ss = Some (c, hn) -> c = CObj /\ hn = true /\ ss <> ST_finish.
Proof.
intros ss c hn R H. assert (CASES : exists k : nat, (k <= 26)%nat /\ ss = Z.of_nat k) by (exists (Z.to_nat ss); split; lia).
destruct CASES as (k & Hk & ->). clear R.
do 27 (destruct k as [|k]; [vm_compute in H; first [discriminate H | injection H as <- <-; split; [reflexivity | split; [reflexivity | vm_compute; discriminate]]] |]); exfalso; lia.
Qed.

Lemma lvl_mode_ws_ss_noadd : forall st ss c hn, zin st ws_states = true -> lvl_mode st ss = Some (c, hn) -> zin ss [ST_array_add; ST_ovadd] = false.
Proof.
intros st ss c hn H Hm.
assert (C : st = 0 \/ st = 4 \/ st = 5 \/ st = 6 \/ st = 7).
{ unfold zin, ws_states in H. cbn in H. rewrite !Bool.orb_true_iff in H. rewrite !Z.eqb_eq in H. intuition lia. }
destruct (zin ss [ST_array_add; ST_ovadd]) eqn:E; [| reflexivity]. exfalso.
assert (R : ss = 16 \/ ss = 22).
{ unfold zin in E. cbn in E. rewrite !Bool.orb_true_iff in E. rewrite !Z.eqb_eq in E. unfold ST_array_add, ST_ovadd in E. intuition lia. }
destruct C as [->|[->|[->|[->| ->]]]]; destruct R as [-> | ->]; vm_compute in Hm; discriminate Hm.
Qed.

Lemma lupd_sameS : forall {X} (ls : list X) i x, nth_error ls i = Some x -> lupd ls i x = ls.
Proof. induction ls as [|h t IH]; intros i x H; destruct i; cbn in *; try discriminate; [injection H as ->; reflexivity | rewrite IH by exact H; reflexivity]. Qed.
Lemma ts_lvl_same : forall ts l, nth_error (t_levels ts) (t_depth ts) = Some l -> ts_lvl ts l = ts.
Proof. intros [d lv co pb pbs x o os obs] l H. unfold ts_lvl. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *. rewrite (lupd_sameS lv d l H). reflexivity. Qed.
Lemma ts_lvl_obj_lvl : forall ts l2 l3 o os obs, ts_lvl (ts_lvl_obj ts l2 o os obs) l3 = ts_lvl_obj ts l3 o os obs.
Proof. intros. unfold ts_lvl, ts_lvl_obj; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs]. rewrite lupd_lupdS. reflexivity. Qed.
Lemma cur_st_lvl_obj : forall ts l l' o os obs, nth_error (t_levels ts) (t_depth ts) = Some l -> cur_st (ts_lvl_obj ts l' o os obs) = tl_st l'.
Proof. intros ts l l' o os obs Hl. unfold cur_st, ts_lvl_obj; cbn [t_levels t_depth]. rewrite nth_error_lupd_eq by (apply nth_error_Some; rewrite Hl; discriminate). reflexivity. Qed.

Lemma lvl_cur_restateG : forall segs Fn m depth l st' ss' c hn c',
lvl_cur segs Fn m depth depth l ->
lvl_mode (tl_st l) (tl_ss l) = Some (c, hn) ->
lvl_mode st' ss' = Some (c', hn) -> 0 <= st' <= 26 -> 0 <= ss' <= 26 ->
(c' = c \/ c' = CAny) ->
lvl_cur segs Fn m depth depth (TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
Proof.
intros segs Fn m depth l st' ss' c hn c' (R1 & R2 & J & M) Hm Hm' Hst Hss Hc.
rewrite Nat.ltb_irrefl, Nat.eqb_refl in M. destruct M as (c0 & hn0 & E0 & CLS & NM).
rewrite Hm in E0. injection E0 as <- <-.
split; [exact Hst|]. split; [exact Hss|]. split; [exact J|].
cbn [tl_st tl_ss tl_cs]. rewrite Nat.ltb_irrefl, Nat.eqb_refl.
exists c', hn. split; [exact Hm'|]. split.
- destruct Hc as [-> | ->]; [exact CLS | exact I].
- destruct hn; cbn in *; exact NM.
Qed.

Lemma tstack_lupd_srec : forall segs m q levels d l l',
tstack segs m q levels -> nth_error levels d = Some l -> srec_cells l' = srec_cells l -> tstack segs m q (lupd levels d l').
Proof.
intros segs m q levels d l l' TSK Hl E j lj Hj.
destruct (PeanoNat.Nat.eq_dec j d) as [-> | NE].
- rewrite nth_error_lupd_eq in Hj by (apply nth_error_Some; rewrite Hl; discriminate). injection Hj as <-. rewrite E. exact (TSK d l Hl).
- rewrite nth_error_lupd_neq in Hj by congruence. exact (TSK j lj Hj).
Qed.

Definition pe_restblocks (pf : pe_fix) (q : Z) (LB0 : list blk) (ts : tstate) : list blk :=
(t_pbs ts ++ t_objbs ts ++ concat (map lvl_blocks (lupd (t_levels ts) (t_depth ts) lvl_reset))) ++ (pf_tk pf, 72) :: (q, 32 * pf_mxd pf) :: LB0.

Lemma pe_blocksA_lvl_perm : forall pf q LB0 ts l l', nth_error (t_levels ts) (t_depth ts) = Some l ->
Permutation (pe_blocksA pf q LB0 (ts_lvl ts l')) (lvl_blocks l' ++ pe_restblocks pf q LB0 ts).
Proof.
intros pf q LB0 ts l l' Hl. unfold pe_blocksA, pe_restblocks, tstate_blocks, ts_lvl; cbn [t_pbs t_objbs t_levels t_depth].
rewrite (lupd_split _ _ _ l' Hl), (lupd_split _ _ _ lvl_reset Hl). change (lvl_blocks lvl_reset) with (@nil blk). rewrite app_nil_l. perm.
Qed.

Lemma pe_blocksA_cur_perm : forall pf q LB0 ts l, nth_error (t_levels ts) (t_depth ts) = Some l ->
Permutation (pe_blocksA pf q LB0 ts) (lvl_blocks l ++ pe_restblocks pf q LB0 ts).
Proof.
intros pf q LB0 ts l Hl. unfold pe_blocksA, pe_restblocks, tstate_blocks.
rewrite (concat_split _ _ _ Hl), (lupd_split _ _ _ lvl_reset Hl). change (lvl_blocks lvl_reset) with (@nil blk). rewrite app_nil_l. perm.
Qed.

Lemma pe_restblocks_other : forall pf q LB0 ts i li, i <> t_depth ts -> nth_error (t_levels ts) i = Some li -> incl (lvl_blocks li) (pe_restblocks pf q LB0 ts).
Proof.
intros pf q LB0 ts i li NE Hli b Hb. unfold pe_restblocks. apply in_or_app; left. apply in_or_app; right. apply in_or_app; right.
apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map. eapply (nth_error_In _ i). rewrite nth_error_lupd_neq by congruence. exact Hli.
Qed.

Definition pe_restblocks2 (pf : pe_fix) (q : Z) (LB0 : list blk) (ts : tstate) : list blk :=
(t_pbs ts ++ concat (map lvl_blocks (lupd (t_levels ts) (t_depth ts) lvl_reset))) ++ (pf_tk pf, 72) :: (q, 32 * pf_mxd pf) :: LB0.

Lemma pe_blocksA_lvl_obj_perm : forall pf q LB0 ts l l' o os obs, nth_error (t_levels ts) (t_depth ts) = Some l ->
Permutation (pe_blocksA pf q LB0 (ts_lvl_obj ts l' o os obs)) (lvl_blocks l' ++ obs ++ pe_restblocks2 pf q LB0 ts).
Proof.
intros pf q LB0 ts l l' o os obs Hl. unfold pe_blocksA, pe_restblocks2, tstate_blocks, ts_lvl_obj; cbn [t_pbs t_objbs t_levels t_depth].
rewrite (lupd_split _ _ _ l' Hl), (lupd_split _ _ _ lvl_reset Hl). change (lvl_blocks lvl_reset) with (@nil blk). rewrite app_nil_l. perm.
Qed.

Lemma pe_blocksA_cur_perm2 : forall pf q LB0 ts l, nth_error (t_levels ts) (t_depth ts) = Some l ->
Permutation (pe_blocksA pf q LB0 ts) (lvl_blocks l ++ t_objbs ts ++ pe_restblocks2 pf q LB0 ts).
Proof.
intros pf q LB0 ts l Hl. unfold pe_blocksA, pe_restblocks2, tstate_blocks.
rewrite (concat_split _ _ _ Hl), (lupd_split _ _ _ lvl_reset Hl). change (lvl_blocks lvl_reset) with (@nil blk). rewrite app_nil_l. perm.
Qed.

Lemma pe_restblocks2_other : forall pf q LB0 ts i li, i <> t_depth ts -> nth_error (t_levels ts) i = Some li -> incl (lvl_blocks li) (pe_restblocks2 pf q LB0 ts).
Proof.
intros pf q LB0 ts i li NE Hli b Hb. unfold pe_restblocks2. apply in_or_app; left. apply in_or_app; right.
apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map. eapply (nth_error_In _ i). rewrite nth_error_lupd_neq by congruence. exact Hli.
Qed.

Definition tx_err (x : tscal) (e : word) : tscal := TS (ts_isd x) (ts_stpos x) (ts_choff x) e (ts_ucs x) (ts_high x) (ts_quote x).

Definition ts_pbs (ts : tstate) (pbs : list blk) : tstate :=
TST (t_depth ts) (t_levels ts) (t_co ts) (t_pb ts) pbs (t_x ts) (t_obj ts) (t_objs ts) (t_objbs ts).

Definition PBOKat (m : word -> option byte) (ts : tstate) (b : Z) : Prop :=
exists buf bpos size pre post,
t_pbs ts = [(t_pb ts, PB_SZ); (buf, size)] /\ Z.of_nat (length pre) = bpos /\
pbuf_core asegs m (t_pb ts) buf bpos size (pre ++ [Z_to_bv 8 0] ++ post) /\ bpos <= b.
Definition PBOK (m : word -> option byte) (ts : tstate) (k : Z) : Prop := PBOKat m ts (t_co ts + k).

Lemma PBOKat_pbuf : forall m ts b, PBOKat m ts b -> pbuf asegs m (t_pbs ts) (t_pb ts).
Proof. intros m ts b (buf & bpos & size & pre & post & E & L & C & _). exists buf, bpos, size, pre, post. split; [exact E|]. split; [exact L | exact C]. Qed.

Lemma PBOKat_weaken : forall m ts b b', b <= b' -> PBOKat m ts b -> PBOKat m ts b'.
Proof. intros m ts b b' Hk (buf & bpos & size & pre & post & E & L & C & Hb). exists buf, bpos, size, pre, post. split; [exact E|]. split; [exact L|]. split; [exact C | lia]. Qed.
Lemma PBOKat_agree : forall BS m m' ts b, PBOKat m ts b -> agree_on asegs BS m m' -> incl (t_pbs ts) BS -> PBOKat m' ts b.
Proof.
intros BS m m' ts b (buf & bpos & size & pre & post & E & L & C & Hb) AG Hi. exists buf, bpos, size, pre, post.
split; [exact E|]. split; [exact L|]. split; [| exact Hb].
eapply (pbuf_core_agree asegs); [exact C | exact AG | apply Hi; rewrite E; left; reflexivity | apply Hi; rewrite E; right; left; reflexivity].
Qed.

Lemma PBOKat_same : forall m ts ts' b, t_pbs ts' = t_pbs ts -> t_pb ts' = t_pb ts -> PBOKat m ts b -> PBOKat m ts' b.
Proof. intros m ts ts' b E1 E2 (buf & bpos & size & pre & post & E & L & C & Hb). exists buf, bpos, size, pre, post. rewrite E1, E2. split; [exact E|]. split; [exact L|]. split; [exact C | exact Hb]. Qed.

Lemma PBOK_pbuf : forall m ts k, PBOK m ts k -> pbuf asegs m (t_pbs ts) (t_pb ts).
Proof. intros m ts k (buf & bpos & size & pre & post & E & L & C & _). exists buf, bpos, size, pre, post. split; [exact E|]. split; [exact L | exact C]. Qed.

Lemma PBOK_agree : forall BS m m' ts k, PBOK m ts k -> agree_on asegs BS m m' -> incl (t_pbs ts) BS -> PBOK m' ts k.
Proof.
intros BS m m' ts k (buf & bpos & size & pre & post & E & L & C & Hb) AG Hi. exists buf, bpos, size, pre, post.
split; [exact E|]. split; [exact L|]. split; [| exact Hb].
eapply (pbuf_core_agree asegs); [exact C | exact AG | apply Hi; rewrite E; left; reflexivity | apply Hi; rewrite E; right; left; reflexivity].
Qed.

Lemma PBOK_lvl : forall m ts k l', PBOK m ts k -> PBOK m (ts_lvl ts l') k.
Proof. intros m ts k l' H. exact H. Qed.

Lemma potential_step_memappend2 : forall len cap bpos n co,
pb_inv cap co -> 0 <= bpos -> 0 <= n -> bpos + n <= co + 1 -> 0 <= co <= len -> len < 2^26 ->
PhiPB len cap >= memappend_costX2 cap bpos n + PhiPB len (memappend_cap2 cap bpos n)
/\ pb_inv (memappend_cap2 cap bpos n) co /\ 0 <= PhiPB len (memappend_cap2 cap bpos n)
/\ memappend_costX cap bpos n <= PhiPB len cap.
Proof.
intros len cap bpos n co [H32 Hi] Hb Hn Hbn Hco Hlen. unfold PhiPB, memappend_costX2, memappend_cap2, memappend_costX, memappend_costB, pb_inv.
assert (Hsmall : (cap <? 2^30) = true) by (apply Z.ltb_lt; lia). rewrite Hsmall.
destruct (cap <=? bpos + n) eqn:E; destruct (cap <=? bpos + n + 1) eqn:E1;
try apply Z.leb_le in E; try apply Z.leb_gt in E; try apply Z.leb_le in E1; try apply Z.leb_gt in E1;
destruct (Z.max_spec (2 * cap) (bpos + n + 9)) as [[Hm Hx] | [Hm Hx]]; rewrite ?Hx; lia.
Qed.

Lemma PBOKat_appended : forall m ts b pb buf' cap' bpos (content src : list byte),
t_pb ts = pb -> t_pbs ts = [(pb, PB_SZ); (buf', cap')] ->
pbufc asegs m [(pb, PB_SZ); (buf', cap')] pb (firstn (Z.to_nat bpos) content ++ src) ->
0 <= bpos <= Z.of_nat (length content) -> bpos + Z.of_nat (length src) <= b ->
PBOKat m ts b.
Proof.
intros m ts b pb buf' cap' bpos content src Epb Epbs (buf2 & bpos2 & size2 & post2 & E2 & L2 & C2) Hb Hk.
exists buf2, bpos2, size2, (firstn (Z.to_nat bpos) content ++ src), post2.
rewrite Epb, Epbs. split; [exact E2|]. split; [exact L2|]. split; [exact C2|].
rewrite <- L2, length_app, length_firstn, Nat2Z.inj_add, Nat2Z.inj_min, Z2Nat.id by lia. lia.
Qed.

Lemma unpoisoned_sub2 : forall segs m SB s n s' n', unpoisoned segs m SB s n -> s <= s' -> s' + n' <= s + n -> 0 < n' -> unpoisoned segs m SB s' n'.
Proof.
intros segs m SB s n s' n' (Hn & Ha & (v & Hb & Hv) & Hc) H1 H2 H3. split; [exact H3|]. split; [| split].
- intros g Hg. apply Ha. Z.div_mod_to_equations. lia.
- destruct (Z_lt_ge_dec ((s' + n' - 1) / 8) ((s + n - 1) / 8)) as [Hlt | Hge].
+ exists 0. split; [| left; reflexivity]. apply Ha. Z.div_mod_to_equations. lia.
+ assert (E : (s' + n' - 1) / 8 = (s + n - 1) / 8) by (Z.div_mod_to_equations; lia).
exists v. rewrite E. split; [exact Hb|]. destruct Hv as [-> | [Hv8 Hm]]; [left; reflexivity | right]. split; [exact Hv8|]. Z.div_mod_to_equations. lia.
- intros w Hw. apply Hc. Z.div_mod_to_equations. lia.
Qed.

Definition pe_msS (pf : pe_fix) (pa : pe_fixA) (pc : Z) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state :=
let tk := pf_tk pf in
MS (mkR x1 (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2
(Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (shA (pa_F pa))) s3 (Z_to_bv 64 (tk + 20)) s5 (Z_to_bv 64 (tk + 36))
(Z_to_bv 64 (tk + 32)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 A_SB) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None m (seg_rom asegs).

Lemma pe_frameA_cbyte : forall m pf pa cb nb pj sv,
pe_frameA asegs m pf pa cb nb pj sv -> bytes_at asegs m (pa_F pa + 64) [cb].
Proof.
intros m pf pa cb nb pj sv (_ & _ & _ & FF & _). unfold ff_cellsA in FF.
change [CB 24 (pj_fhd pj); CB 40 (pj_f1 pj); C1 cb; CB 183 (pj_f2 pj)] with ([CB 24 (pj_fhd pj); CB 40 (pj_f1 pj)] ++ ([C1 cb] ++ [CB 183 (pj_f2 pj)])) in FF.
apply (proj1 (rw_cells_app asegs _ _ _ _)) in FF as [_ FF]. apply (proj1 (rw_cells_app asegs _ _ _ _)) in FF as [FF _].
cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FF.
destruct FF as [[_ HB] _]. exact HB.
Qed.

Lemma pe_frameA_c_unpoisoned : forall m pf pa cb nb pj sv,
pe_geomA pf pa -> pe_frameA asegs m pf pa cb nb pj sv -> unpoisoned asegs m A_SB (pa_F pa + 64) 1.
Proof.
intros m pf pa cb nb pj sv (_ & _ & _ & GF & GF0 & _) (_ & _ & _ & _ & FSH).
unfold ffsh_cells, FSH0 in FSH. cbn [map] in FSH. unfold shA in FSH.
match type of FSH with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?c15 :: ?rest) =>
change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: c12 :: c13 :: c14 :: c15 :: rest)
with ([c0; c1; c2; c3; c4; c5; c6; c7] ++ ([c8; c9; c10; c11; c12; c13; c14; c15] ++ rest)) in FSH end.
apply (proj1 (rw_cells_app asegs _ _ _ _)) in FSH as [_ W]. apply (proj1 (rw_cells_app asegs _ _ _ _)) in W as [W _].
cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in W.
assert (E8 : (pa_F pa + 64 + 1 - 1) / 8 = pa_F pa / 8 + 8) by (clear - GF; Z.div_mod_to_equations; lia).
assert (Es : (pa_F pa + 64) / 8 = pa_F pa / 8 + 8) by (clear - GF; Z.div_mod_to_equations; lia).
pose proof W as [[_ WB] _]. cbn [cells_bytes cbytes app] in WB.
unfold unpoisoned. split; [lia|]. split; [intros g Hg; rewrite E8, Es in Hg; lia|]. split.
- exists 1. split; [| right; split; [lia | clear - GF; Z.div_mod_to_equations; lia]].
rewrite E8. replace (pa_F pa / 8 + 8 + A_SB) with (pa_F pa / 8 + A_SB + 8) by lia.
match type of WB with bytes_at _ _ _ (?b0 :: ?r) => change (b0 :: r) with ([b0] ++ r) in WB end.
apply (proj1 (bytes_at_app asegs _ _ _ _)) in WB as [WB1 _]. exact WB1.
- intros w Hw. rewrite E8, Es in Hw. exists [Z_to_bv 8 1; Z_to_bv 8 242; Z_to_bv 8 248; Z_to_bv 8 242; Z_to_bv 8 248; Z_to_bv 8 242; Z_to_bv 8 248; Z_to_bv 8 242]. split; [reflexivity|].
replace (w * 8) with (pa_F pa / 8 + A_SB + 8) by (unfold A_SB in *; clear - GF Hw; Z.div_mod_to_equations; lia). exact WB.
Qed.

Section WithIface.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.

Lemma tok_granA : forall A LB LM FR B m md tk i,
HEAPA A4L HIx A LB LM FR B m md -> In (tk, 72) LB -> 0 <= i < 9 ->
ro_cells asegs m (tk / 8 + i + A_SB) [C1 (Z_to_bv 8 0)].
Proof.
intros A LB LM FR B m md tk i HP Hin Hi.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ _ _ HP Hin) as SH. unfold shad in SH. cbn [hl_sb A4L] in SH.
pose proof (shadow_granule0 asegs m (tk / 8 + A_SB) 72 i ltac:(lia) ltac:(lia) SH) as G.
replace (tk / 8 + A_SB + i) with (tk / 8 + i + A_SB) in G by lia. exact G.
Qed.

Definition memappend_A_stmt2 : Prop :=
forall (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud) (lo pb n : Z) (T : TSet)
(t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 tp a0 a1 a2 : word)
(buf bpos cap b : Z) (content src : list byte) (errv : word) (A : ASA A4L HIx),
HEAPA A4L HIx A ((pb, PB_SZ) :: (buf, cap) :: LB) LM FRS B0 m0 md0 ->
pbuf_core asegs m0 pb buf bpos cap content -> 0 <= n < 2^31 ->
bytes_at asegs m0 b src -> Z.of_nat (length src) = n -> 0 <= b ->
src_locA LB FRS b n -> (0 < n -> unpoisoned asegs m0 A_SB b n) ->
stk asegs m0 lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 112 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m0 A_ERRNO [C4 errv] -> tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 pb -> a1 = Z_to_bv 64 b -> a2 = Z_to_bv 64 n ->
memappend_costX cap bpos n <= bB B0 ->
(forall ms' md' A', memappend_A_post_c HIx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 pb buf bpos cap content src n lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md0
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9b4fc) fc None m0 (seg_rom asegs)).

Lemma PE_BUD_restate : forall pf pa ts B l st' ss',
nth_error (t_levels ts) (t_depth ts) = Some l ->
PE_BUD pf pa ts B ->
PE_BUD pf pa (ts_lvl ts (TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B.
Proof.
intros pf pa ts B l st' ss' Hl H.
set (l' := TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
assert (Hblk : tstate_blocks (ts_lvl ts l') = tstate_blocks ts).
{ unfold tstate_blocks, ts_lvl; cbn [t_pbs t_objbs t_levels t_depth]. rewrite (map_lupd_same lvl_blocks (t_levels ts) (t_depth ts) l' l Hl eq_refl). reflexivity. }
unfold PE_BUD. rewrite Hblk. exact H.
Qed.

Lemma PE_REST_A_restateG : forall pf pa q LB0 LM FRS payload me lo m md A B ts errv l st' ss' c hn c',
PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts errv ->
nth_error (t_levels ts) (t_depth ts) = Some l ->
lvl_mode (tl_st l) (tl_ss l) = Some (c, hn) -> lvl_mode st' ss' = Some (c', hn) -> 0 <= st' <= 26 -> 0 <= ss' <= 26 -> (c' = c \/ c' = CAny) ->
(zin st' [ST_array_add; ST_ovadd] = zin (tl_st l) [ST_array_add; ST_ovadd] \/ (zin st' [ST_array_add; ST_ovadd] = false /\ t_objbs ts = [])) ->
PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B (ts_lvl ts (TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) errv.
Proof.
intros pf pa q LB0 LM FRS payload me lo m md A B ts errv l st' ss' c hn c' REST Hl Hm Hm' Hst Hss Hc Hz.
destruct REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD).
set (l' := TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
split.
{ match goal with |- HEAPA _ _ _ ?L _ _ _ _ _ => replace L with (pe_blocksA pf q LB0 ts); [exact HP |] end.
unfold pe_blocksA, tstate_blocks, ts_lvl; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs].
rewrite (map_lupd_same lvl_blocks (t_levels ts) (t_depth ts) l' l Hl eq_refl). reflexivity. }
split.
{ intros i li Hli. unfold ts_lvl in Hli |- *. cbn [t_levels t_depth] in Hli |- *.
destruct (PeanoNat.Nat.eq_dec i (t_depth ts)) as [-> | NE].
- rewrite nth_error_lupd_eq in Hli by exact Hd. injection Hli as <-.
eapply lvl_cur_restateG; [exact (LV (t_depth ts) l Hl) | exact Hm | exact Hm' | exact Hst | exact Hss | exact Hc].
- rewrite nth_error_lupd_neq in Hli by congruence. exact (LV i li Hli). }
split.
{ unfold cur_st, ts_lvl in *; cbn [t_levels t_depth t_objs t_objbs t_obj] in *. rewrite nth_error_lupd_eq by exact Hd. subst l'. cbn [tl_st].
rewrite Hl in OBJ. destruct Hz as [Hz | [Hz E]]; [rewrite Hz; exact OBJ | rewrite Hz; exact E]. }
split; [exact ST|]. split; [exact ERR|]. split; [exact STR|]. split; [exact PLEN|]. split; [exact SBin|]. split; [exact HPR|]. split; [exact MDV|]. split; [exact G|].
apply (PE_BUD_restate pf pa ts B l st' ss' Hl BUD).
Qed.

Lemma PBOKat_wtqA : forall pf pa q LB0 LM FRS B ts A m m' md lo W b,
PE_STATIC_A HIx pf pa lo -> HEAPA A4L HIx A (pe_blocksA pf q LB0 ts) LM ((pa_F pa, 2) :: FRS) B m md ->
PBOKat m ts b -> munch W m m' -> wmono asegs m m' -> Forall (pe_wtqA pf pa q) W -> PBOKat m' ts b.
Proof.
intros pf pa q LB0 LM FRS B ts A m m' md lo W b STC HP PBK MU WM HW.
eapply PBOKat_agree; [exact PBK | | apply incl_refl].
eapply (agree_wtqA HIx); [exact STC | exact HP | exact MU | exact WM | exact HW |].
intros a n Hin. assert (HinL : In (a, n) (pe_blocksA pf q LB0 ts ++ LM)) by (unfold pe_blocksA, tstate_blocks; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hin).
split; [exact HinL|].
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. unfold pe_blocksA in ND. rewrite <- app_assoc in ND. split.
- intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | left; reflexivity].
- intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | right; left; reflexivity].
Qed.

Lemma PBOK_wtqA : forall pf pa q LB0 LM FRS B ts A m m' md lo W k,
PE_STATIC_A HIx pf pa lo -> HEAPA A4L HIx A (pe_blocksA pf q LB0 ts) LM ((pa_F pa, 2) :: FRS) B m md ->
PBOK m ts k -> munch W m m' -> wmono asegs m m' -> Forall (pe_wtqA pf pa q) W -> PBOK m' ts k.
Proof.
intros pf pa q LB0 LM FRS B ts A m m' md lo W k STC HP PBK MU WM HW.
eapply PBOK_agree; [exact PBK | | apply incl_refl].
eapply (agree_wtqA HIx); [exact STC | exact HP | exact MU | exact WM | exact HW |].
intros a n Hin. assert (HinL : In (a, n) (pe_blocksA pf q LB0 ts ++ LM)) by (unfold pe_blocksA, tstate_blocks; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hin).
split; [exact HinL|].
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. unfold pe_blocksA in ND. rewrite <- app_assoc in ND. split.
- intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | left; reflexivity].
- intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | right; left; reflexivity].
Qed.

Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.

Lemma PE_REST_A_call_pb : forall pf pa q LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 ts errv errv2 LBc co2 pb2 pbs2 x2,
PE_STATIC_A HIx pf pa lo ->
PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m1 md A B ts errv ->
model_vm_only (cfg_model md) (cfg_model md2) ->
heap_pres A4H (LBc ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) m1 m2 ->
incl (t_objbs ts ++ concat (map lvl_blocks (t_levels ts)) ++ LB0) LBc ->
let ts2 := TST (t_depth ts) (t_levels ts) co2 pb2 pbs2 x2 (t_obj ts) (t_objs ts) (t_objbs ts) in
HEAPA A4L HIx A2 (pe_blocksA pf q LB0 ts2) LM ((pa_F pa, 2) :: FRS) B2 m2 md2 ->
stk asegs m2 lo (pf_spf pf) ->
rw_cells asegs m2 A_ERRNO [C4 errv2] ->
PE_BUD pf pa ts2 B2 ->
PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts2 errv2.
Proof.
intros pf pa q LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 ts errv errv2 LBc co2 pb2 pbs2 x2 STC
(HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD) VM12 HPRc Hincl ts2 HP2 ST2 ERR2 BUD2.
pose proof STC as (LO & LOS & GEO & _). pose proof GEO as (Gspf & Gsp0 & Gle & _).
assert (AG : agree_on asegs (t_objbs ts ++ concat (map lvl_blocks (t_levels ts)) ++ LB0) m1 m2).
{ eapply (agree_of_heap_pres asegs A4H); [exact HPRc | reflexivity |]. intros b Hb. apply in_or_app; left. exact (Hincl b Hb). }
assert (SBin2 := payload_locA_pres HIx pf pa LB0 FRS _ _ _ _ _ _ _ LBc _ _ _ HP (incl_tl _ (incl_refl _)) HPRc SBin).
assert (FRI : incl (fr_ivs A4L FRS) (LBc ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS))).
{ intros b Hb. apply in_or_app; right. apply in_or_app; right. unfold fr_ivs in *. cbn [flat_map]. apply in_or_app; right. exact Hb. }
split; [exact HP2|]. split; [| split; [| split; [exact ST2 | split; [exact ERR2 | split; [| split; [exact PLEN | split; [exact SBin2 | split; [| split; [| split; [| exact BUD2]]]]]]]]]].
- intros i l Hl. cbn. eapply (lvl_cur_agree asegs A4F); [exact (LV i l Hl) | exact AG |].
intros b Hb. apply in_or_app; right. apply in_or_app; left. apply in_concat. exists (lvl_blocks l). split; [| exact Hb]. apply in_map. eapply nth_error_In; exact Hl.
- revert OBJ. unfold cur_st. cbn [t_levels t_depth t_objs t_objbs t_obj]. destruct (zin _ _); intros OBJ; [| exact OBJ].
eapply (jopt_agree asegs A4F); [exact OBJ | exact AG | intros b Hb; apply in_or_app; left; exact Hb].
- eapply payload_presA; [exact HPRc | intros x Hx; apply in_or_app; left; apply Hincl; apply in_or_app; right; apply in_or_app; right; exact Hx | exact FRI | | exact STR | exact PLEN | exact SBin]. lia.
- eapply heap_presx_trans; [exact HPR|]. eapply heap_presx_weaken; [apply heap_pres_presx; exact HPRc | lia | | intros a Xa; exact Xa].
intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; apply Hincl; apply in_or_app; right; apply in_or_app; right; exact Hb|].
apply in_or_app; right. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right].
unfold fr_ivs in *. cbn [flat_map]. apply in_or_app; right. exact Hb.
- eapply model_vm_only_trans; [exact MDV | exact VM12].
- eapply GA_pres; [exact HPRc | exact G].
Qed.

Lemma PE_REST_A_callG : forall pf pa q LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 ts ts2 errv errv2 LBc,
PE_STATIC_A HIx pf pa lo ->
PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m1 md A B ts errv ->
model_vm_only (cfg_model md) (cfg_model md2) ->
heap_pres A4H (LBc ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) m1 m2 ->
incl LB0 LBc ->
HEAPA A4L HIx A2 (pe_blocksA pf q LB0 ts2) LM ((pa_F pa, 2) :: FRS) B2 m2 md2 ->
(forall i l, nth_error (t_levels ts2) i = Some l -> lvl_cur asegs A4F m2 (t_depth ts2) i l) ->
(if zin (cur_st ts2) [ST_array_add; ST_ovadd] then jopt asegs A4F (t_objs ts2) m2 (t_objbs ts2) (t_obj ts2) else t_objbs ts2 = []) ->
stk asegs m2 lo (pf_spf pf) ->
rw_cells asegs m2 A_ERRNO [C4 errv2] ->
PE_BUD pf pa ts2 B2 ->
PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts2 errv2.
Proof.
intros pf pa q LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 ts ts2 errv errv2 LBc STC
(HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD) VM12 HPRc Hincl HP2 LV2 OBJ2 ST2 ERR2 BUD2.
pose proof STC as (LO & LOS & GEO & _). pose proof GEO as (Gspf & Gsp0 & Gle & _).
split; [exact HP2|]. split; [exact LV2|]. split; [exact OBJ2|]. split; [exact ST2|]. split; [exact ERR2|].
assert (SBin2 := payload_locA_pres HIx pf pa LB0 FRS _ _ _ _ _ _ _ LBc _ _ _ HP (incl_tl _ (incl_refl _)) HPRc SBin).
assert (FRI : incl (fr_ivs A4L FRS) (LBc ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS))).
{ intros b Hb. apply in_or_app; right. apply in_or_app; right. unfold fr_ivs in *. cbn [flat_map]. apply in_or_app; right. exact Hb. }
split; [| split; [exact PLEN | split; [exact SBin2 | split; [| split; [| split; [| exact BUD2]]]]]].
- eapply payload_presA; [exact HPRc | intros x Hx; apply in_or_app; left; apply Hincl; exact Hx | exact FRI | | exact STR | exact PLEN | exact SBin]. lia.
- eapply heap_presx_trans; [exact HPR|]. eapply heap_presx_weaken; [apply heap_pres_presx; exact HPRc | lia | | intros a Xa; exact Xa].
intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; apply Hincl; exact Hb|].
apply in_or_app; right. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right].
unfold fr_ivs in *. cbn [flat_map]. apply in_or_app; right. exact Hb.
- eapply model_vm_only_trans; [exact MDV | exact VM12].
- eapply GA_pres; [exact HPRc | exact G].
Qed.

Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.

Lemma PE_INV_A_lvl_writeG : forall pf pa q LB0 LM FRS payload me lo m mc md A B ts cb nb pj sv errv l st' ss' c hn c',
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l ->
munch [(q + 32 * Z.of_nat (t_depth ts), q + 32 * Z.of_nat (t_depth ts) + 32)] m mc -> wmono asegs m mc -> mem_inv asegs mc ->
rw_cells asegs mc (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) (t_pb ts) (Z.of_nat (t_depth ts)) q (t_x ts)) ->
rw_cells asegs mc (q + 32 * Z.of_nat (t_depth ts)) (srec_cells (TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) ->
lvl_mode (tl_st l) (tl_ss l) = Some (c, hn) -> lvl_mode st' ss' = Some (c', hn) -> 0 <= st' <= 26 -> 0 <= ss' <= 26 -> (c' = c \/ c' = CAny) ->
(zin st' [ST_array_add; ST_ovadd] = zin (tl_st l) [ST_array_add; ST_ovadd] \/ (zin st' [ST_array_add; ST_ovadd] = false /\ t_objbs ts = [])) ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo mc md A B (ts_lvl ts (TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv
/\ (forall k, PBOK m ts k -> PBOK mc (ts_lvl ts (TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) k).
Proof.
intros pf pa q LB0 LM FRS payload me lo m mc md A B ts cb nb pj sv errv l st' ss' c hn c' STC [CORE REST] Hl MU WM MI TOKc Lc Hm Hm' Hst Hss Hc Hz.
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & (MX1 & _)) & _).
assert (HW : Forall (pe_wtqA pf pa q) [(q + 32 * Z.of_nat (t_depth ts), q + 32 * Z.of_nat (t_depth ts) + 32)]).
{ apply Forall_cons; [right; cbn [fst snd]; lia | apply Forall_nil]. }
assert (INq : In (q, 32 * pf_mxd pf) (pe_blocksA pf q LB0 ts)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
split.
- split.
+ unfold PE_CORE_A, ts_lvl; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOKc|]. split; [| split; [exact Hpb | split]].
* eapply (pbuf_wtqA HIx) with (ts := ts); [exact STC | exact (proj1 REST) | exact PB | exact MU | exact WM | exact HW].
* eapply (tstack_put asegs m _ q (t_levels ts) (t_depth ts) _ []); [exact TSK | exact Hd | exact MU | exact WM | intros; exact I | exact Lc].
* eapply (pe_frameA_blkwrite HIx) with (ts := ts); [exact STC | exact (proj1 REST) | | exact FR | exact MU | exact WM].
apply Forall_cons; [exists q, (32 * pf_mxd pf); cbn [fst snd]; split; [apply in_or_app; left; exact INq | lia] | apply Forall_nil].
+ eapply (PE_REST_A_restateG) with (c := c) (hn := hn) (c' := c'); [| exact Hl | exact Hm | exact Hm' | exact Hst | exact Hss | exact Hc | exact Hz].
eapply (PE_REST_A_private_write HIx GA GA_outside) with (ts := ts); [exact STC | exact REST | exact MU | exact WM | exact MI | apply pe_wtqA_private; exact HW].
- intros k PBK. apply PBOK_lvl. eapply PBOK_wtqA with (ts := ts); [exact STC | exact (proj1 REST) | exact PBK | exact MU | exact WM | exact HW].
Qed.

Lemma PE_INV_A_lvl_write : forall pf pa q LB0 LM FRS payload me lo m mc md A B ts cb nb pj sv errv l st' ss' c hn c',
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l ->
munch [(q + 32 * Z.of_nat (t_depth ts), q + 32 * Z.of_nat (t_depth ts) + 32)] m mc -> wmono asegs m mc -> mem_inv asegs mc ->
rw_cells asegs mc (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) (t_pb ts) (Z.of_nat (t_depth ts)) q (t_x ts)) ->
rw_cells asegs mc (q + 32 * Z.of_nat (t_depth ts)) (srec_cells (TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) ->
lvl_mode (tl_st l) (tl_ss l) = Some (c, hn) -> lvl_mode st' ss' = Some (c', hn) -> 0 <= st' <= 26 -> 0 <= ss' <= 26 -> (c' = c \/ c' = CAny) ->
zin st' [ST_array_add; ST_ovadd] = zin (tl_st l) [ST_array_add; ST_ovadd] ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo mc md A B (ts_lvl ts (TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv
/\ (forall k, PBOK m ts k -> PBOK mc (ts_lvl ts (TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) k).
Proof. intros until c'. intros STC INV Hl MU WM MI TOKc Lc Hm Hm' Hst Hss Hc Hz. eapply PE_INV_A_lvl_writeG; eauto. Qed.

Definition ts_push (ts : tstate) (lp : tlevel) : tstate :=
TST (S (t_depth ts)) (lupd (lupd (t_levels ts) (t_depth ts) lp) (S (t_depth ts)) (TL ST_eatws ST_start 0 None [] 0 []))
(t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (t_obj ts) (t_objs ts) (t_objbs ts).

Lemma PE_INV_A_next_clean : forall pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv l1,
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
nth_error (t_levels ts) (S (t_depth ts)) = Some l1 -> lvl_blocks l1 = [].
Proof.
intros pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv l1 INV H1.
pose proof (proj1 (proj2 (proj2 INV)) _ _ H1) as (_ & _ & _ & M1).
replace (S (t_depth ts) <? t_depth ts)%nat with false in M1 by (symmetry; apply Nat.ltb_ge; lia).
replace (S (t_depth ts) =? t_depth ts)%nat with false in M1 by (symmetry; apply Nat.eqb_neq; lia).
destruct M1 as (_ & _ & C3 & _ & C5). unfold lvl_blocks. rewrite C3, C5. reflexivity.
Qed.

Lemma PE_INV_A_set_obj : forall pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv obj' objs',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> t_objbs ts = [] ->
(if zin (cur_st ts) [ST_array_add; ST_ovadd] then jopt asegs A4F objs' m [] obj' else True) ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B
(TST (t_depth ts) (t_levels ts) (t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) obj' objs' []) cb nb pj sv errv.
Proof.
intros pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv obj' objs' [CORE REST] E OBJ'.
destruct ts as [depth levels co pb pbs x obj objs objbs]. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *. subst objbs.
split; [exact CORE|].
destruct REST as (HP & LV & OBJ & RESTT). split; [exact HP|]. split; [exact LV|]. split; [| exact RESTT].
unfold cur_st in *. cbn [t_depth t_levels t_obj t_objs t_objbs] in *. destruct (zin _ _); [exact OBJ' | reflexivity].
Qed.

Lemma pe_frameA_scan : forall pf pa q LB0 LM FRS B ts A m mc md lo cb nb pj sv cb',
PE_STATIC_A HIx pf pa lo -> HEAPA A4L HIx A (pe_blocksA pf q LB0 ts) LM ((pa_F pa, 2) :: FRS) B m md ->
pe_frameA asegs m pf pa cb nb pj sv ->
munch [(pf_tk pf, pf_tk pf + 72); (pa_F pa + 64, pa_F pa + 65)] m mc -> wmono asegs m mc ->
rw_cells asegs mc (pa_F pa) (ff_cellsA cb' pj) ->
pe_frameA asegs mc pf pa cb' nb pj sv.
Proof.
intros pf pa q LB0 LM FRS B ts A m mc md lo cb nb pj sv cb' STC HP (SLOTS & GAP & SAVED & _ & FSH) MU WM FFc.
pose proof STC as (LO & LOS & GEO & HT & SP0 & _). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
pose proof alloc_ceiling_range as ACR.
assert (INtk : In (pf_tk pf, 72) (pe_blocksA pf q LB0 ts ++ LM)) by (apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INF : In (pa_F pa, 2) ((pa_F pa, 2) :: FRS)) by (left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP INtk) as (_ & _ & Htlo & Hthi & _).
pose proof (shadow_blk_apart HIx _ _ _ _ _ _ _ _ _ (pa_F pa) 32 HP INtk ltac:(lia) ltac:(lia) ltac:(lia)) as DSt.
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as DSF. rewrite fr_size_2 in DSF. cbn [hl_sb A4L] in DSF.
pose proof (pe_slotsA_size pf pa nb pj) as SZ.
split; [| split; [| split; [| split; [exact FFc|]]]].
- eapply rw_cells_transport; [exact SLOTS | exact MU | exact WM |]. rewrite SZ. cbn [disjoint_from fst snd]. lia.
- eapply rw_cells_transport; [exact GAP | exact MU | exact WM |]. cbn [cells_size csize disjoint_from fst snd]. lia.
- eapply rw_cells_transport; [exact SAVED | exact MU | exact WM |]. cbn [pe_savedA_cells cells_size csize disjoint_from fst snd Nat.add]. lia.
- eapply rw_cells_transport; [exact FSH | exact MU | exact WM |]. cbn [disjoint_from fst snd]. unfold shA, A_SB in *.
change (Z.of_nat (cells_size (ffsh_cells FSH0))) with 32. Z.div_mod_to_equations. lia.
Qed.

Definition ts_set_x (ts : tstate) (co' : Z) (x' : tscal) : tstate :=
TST (t_depth ts) (t_levels ts) co' (t_pb ts) (t_pbs ts) x' (t_obj ts) (t_objs ts) (t_objbs ts).

Lemma PE_REST_A_set_x : forall pf pa q LB0 LM FRS payload me lo m md A B ts errv co' x',
PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts errv ->
PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B (ts_set_x ts co' x') errv.
Proof. intros until x'. intros H. destruct ts. exact H. Qed.

Lemma PE_INV_A_tokw : forall pf pa q LB0 LM FRS payload me lo m mc md A B ts cb nb pj sv errv W co' x' cb' nb',
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
munch W m mc -> wmono asegs m mc -> mem_inv asegs mc -> Forall (pe_wtfA pf pa) W ->
rw_cells asegs mc (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) (t_pb ts) (Z.of_nat (t_depth ts)) q x') ->
pe_frameA asegs mc pf pa cb' nb' pj sv ->
0 <= co' <= pf_len pf -> ts_choff x' = Z_to_bv 64 co' ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo mc md A B (ts_set_x ts co' x') cb' nb' pj sv errv
/\ (forall b, PBOKat m ts b -> PBOKat mc (ts_set_x ts co' x') b).
Proof.
intros pf pa q LB0 LM FRS payload me lo m mc md A B ts cb nb pj sv errv W co' x' cb' nb' STC [CORE REST] MU WM MI HW TOKc FRc Hco Hch.
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
split.
- split.
+ unfold PE_CORE_A, ts_set_x; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. split; [exact LEN32|]. split; [exact D32|]. split; [exact Hco|]. split; [exact Hch|].
split; [exact TOKc|]. split; [| split; [exact Hpb | split; [| exact FRc]]].
* eapply (pbuf_wtfA HIx) with (ts := ts); [exact STC | exact (proj1 REST) | exact PB | exact MU | exact WM | exact HW].
* eapply (tstack_wtfA HIx) with (ts := ts); [exact STC | exact (proj1 REST) | exact TSK | exact LEN32 | exact MU | exact WM | exact HW].
+ apply PE_REST_A_set_x.
eapply (PE_REST_A_private_write HIx GA GA_outside) with (ts := ts); [exact STC | exact REST | exact MU | exact WM | exact MI | apply pe_wtfA_private; exact HW].
- intros b PBK. eapply PBOKat_same with (ts := ts); [reflexivity | reflexivity |].
eapply PBOKat_agree; [exact PBK | | apply incl_refl].
eapply (agree_wtqA HIx); [exact STC | exact (proj1 REST) | exact MU | exact WM | apply pe_wtfA_wtqA; exact HW |].
intros a n Hin. assert (HinL : In (a, n) (pe_blocksA pf q LB0 ts ++ LM)) by (unfold pe_blocksA, tstate_blocks; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hin).
split; [exact HinL|].
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ (proj1 REST)) as ND. unfold pe_blocksA in ND. rewrite <- app_assoc in ND. split.
+ intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | left; reflexivity].
+ intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | right; left; reflexivity].
Qed.

Lemma PE_INV_A_tokw1 : forall pf pa q LB0 LM FRS payload me lo m mc md A B ts cb nb pj sv errv co' x',
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
munch [(pf_tk pf, pf_tk pf + 72)] m mc -> wmono asegs m mc -> mem_inv asegs mc ->
rw_cells asegs mc (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) (t_pb ts) (Z.of_nat (t_depth ts)) q x') ->
0 <= co' <= pf_len pf -> ts_choff x' = Z_to_bv 64 co' ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo mc md A B (ts_set_x ts co' x') cb nb pj sv errv
/\ (forall b, PBOKat m ts b -> PBOKat mc (ts_set_x ts co' x') b).
Proof.
intros pf pa q LB0 LM FRS payload me lo m mc md A B ts cb nb pj sv errv co' x' STC INV MU WM MI TOKc Hco Hch.
eapply PE_INV_A_tokw; [exact STC | exact INV | exact MU | exact WM | exact MI | | exact TOKc | | exact Hco | exact Hch].
- apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil].
- destruct INV as [CORE REST]. destruct CORE as (_ & _ & _ & _ & _ & _ & _ & _ & FR).
eapply (pe_frameA_blkwrite HIx) with (ts := ts); [exact STC | exact (proj1 REST) | | exact FR | exact MU | exact WM].
apply Forall_cons; [exists (pf_tk pf), 72; cbn [fst snd]; split; [apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; left; reflexivity | lia] | apply Forall_nil].
Qed.
End WithIface.
End RC__1.
End Mq4.

From Stdlib Require Import ZArith List Lia Bool.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkMG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkMG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QG8z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QG8z.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXUB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXUB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qiiq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qiiq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSHS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSHS. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql4f.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql4f.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition APE_EPI1 : Z := 0x93c30.

Section PeEpiB.
Variable HIx : heap_iface_A A4L.

Definition fp_private_stmt : Prop :=
forall (A : ASA A4L HIx) LB LM FR B m md F k, HEAPA A4L HIx A LB LM FR B m md -> In (F, k) FR ->
exists fp, bytes_at asegs m (F + fr_size k - 8) (le8 (Z_to_bv 64 fp)) /\ 0 < fp < 2^64 /\
~ client_addr A4H (LB ++ LM) alloc_ceiling fp /\ (fp < hl_img_lo A4H \/ hl_img_hi A4H <= fp) /\ ~ hl_scratch A4H fp /\
(forall F' k', In (F', k') FR -> ~ (F' <= fp < F' + fr_size k') /\ ~ (shad A4L F' <= fp < shad A4L F' + fr_shadow_len k')).

Lemma OBL_FP_PRIVATE : fp_private_stmt.
Proof.
intros A LB LM FR B m md F k HP Hin.
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP Hin) as (_ & _ & _ & _ & _ & _ & _ & X). exact X.
Qed.

Lemma pe_epilogue_A :
forall (pf : pe_fix) (pa : pe_fixA) (LBall LM : list blk) (FRS : list frame) (B : bud)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (T : TSet) (lo : Z)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
HEAPA A4L HIx A LBall LM ((pa_F pa, 2) :: FRS) B m md ->
pe_geomA pf pa -> 0 <= pf_spf pf < 2^62 ->
pe_frameA asegs m pf pa cb nb pj sv ->
stk asegs m lo (pf_spf pf) -> alloc_ceiling <= lo -> lo <= pf_spf pf - 12288 ->
bv_unsigned (pe_ra sv) mod 2 = 0 ->
(forall m' md' (A' : ASA A4L HIx) (fp : Z),
model_vm_only (cfg_model md) (cfg_model md') ->
HEAPA A4L HIx A' LBall LM FRS B m' md' ->
stk asegs m' lo (pa_sp0 pa) ->
0 < fp < 2^64 -> ~ client_addr A4H (LBall ++ LM) alloc_ceiling fp -> (fp < hl_img_lo A4H \/ hl_img_hi A4H <= fp) ->
~ hl_scratch A4H fp ->
(forall F' k', In (F', k') FRS -> ~ (F' <= fp < F' + fr_size k') /\ ~ (shad A4L F' <= fp < shad A4L F' + fr_shadow_len k')) ->
munch [(shA (pa_F pa), shA (pa_F pa) + 32); (pa_F pa, pa_F pa + 8); (fp, fp + 1)] m m' ->
wmono asegs m m' -> mem_inv asegs m' ->
AJ5 A4L HIx A' T md'
(MS (mkR (pe_ra sv) (Z_to_bv 64 (pa_sp0 pa)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (pe_s0 sv) (pe_s1 sv) a0 (Z_to_bv 64 fp) a2 a3 a4 a5 a6 a7
(pe_s2 sv) (pe_s3 sv) (pe_s4 sv) (pe_s5 sv) (pe_s6 sv) (pe_s7 sv) (pe_s8 sv) (pe_s9 sv) (pe_s10 sv) (pe_s11 sv) t3 t4 t5 t6)
F (ret_pc (pe_ra sv)) fc None m' (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (shA (pa_F pa))) s3 s4 s5 (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pa_F pa)) s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 APE_EPI1) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros HP GEO SP0 FR ST LO LOS RAE K.
pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
unfold ff_cellsA in FF. unfold ffsh_cells, FSH0 in FSH. cbn [map] in FSH. unfold pe_savedA_cells in SAVED.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof alloc_ceiling_range as ACR.
assert (INF : In (Ff, 2) ((Ff, 2) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as DSF. rewrite fr_size_2 in DSF. cbn [hl_sb A4L] in DSF.
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & _ & _ & _ & Himg_F & _). rewrite fr_size_2 in Himg_F. cbn [hl_img_lo hl_img_hi A4L A4H hla_base] in Himg_F.
unfold APE_EPI1, shA in *. a4l.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(Ff / 8 + 2147450880, Ff / 8 + 2147450880 + 32); (Ff, Ff + 8)] m) as MU.
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
reenterA asegs A4L HIx asegs_wx HP.
step. stepz.
step. step. stepz.
step. if_falsex.
step.
do 32 stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc |- _ =>
assert (HPc : HEAPA A4L HIx A LBall LM ((Ff, 2) :: FRS) B mc md);
[ eapply (heapA_client_frame A4L HIx); [exact HP | | exact WMc | exact MIc];
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP MUc)
| ] end end.
{ apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; right; right; right; exists Ff, 2; (split; [exact INF|]);
[ right; unfold shad; cbn [fst snd hl_sb A4L]; rewrite ?fr_shadow_len_2; unfold A_SB; lia
| left; cbn [fst snd]; rewrite ?fr_size_2; lia ]. }
destruct (OBL_FP_PRIVATE _ _ _ _ _ _ _ _ _ HPc INF) as (fp & FPB & FPR & FPnc & FPimg & FPns & FPfr).
rewrite fr_size_2 in FPB. replace (Ff + 256 - 8) with (Ff + 248) in FPB by lia.
pose proof (ro_C8_of_bytes_at asegs _ _ _ FPB) as FPC.
step.
evt_done5.
eapply (hiA_frame_release A4L HIx) with (Fr := Ff) (k := 2) (fp := fp) (rX := Z_to_bv 5 11);
[exact HPc | exact INF | rewrite fr_size_2; replace (Ff + 256 - 8) with (Ff + 248) by lia; exact FPB | lia | reflexivity | vm_compute; discriminate | | ].
1: vm_compute; split; reflexivity.
intros m2 md2 A2 VM2 HP2 Hoff Hwv.
cbn [fr_remove fr_base fst Z.eqb] in HP2. rewrite Z.eqb_refl in HP2.
assert (MUr : munch [(fp, fp + 1)] m1 m2).
{ intros x Hx. cbn [outside] in Hx. pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR. cbn in XR.
rewrite <- (Z_to_bv_bv_unsigned x). change (Z_to_bv 64 (bv_unsigned x)) with (wa (bv_unsigned x)). apply Hoff; lia. }
assert (WMr : wmono asegs m1 m2) by exact Hwv.
assert (MI2 : mem_inv asegs m2).
{ intros y b Hb. destruct (Z.eq_dec (bv_unsigned y) fp) as [Ey | Ny].
- destruct (ro_addr asegs y) eqn:RO; [| reflexivity]. exfalso. apply ro_addr_asegs in RO. cbn [hl_img_lo hl_img_hi A4H hla_base A4L] in FPimg. lia.
- apply (MI y b). rewrite <- Hb. symmetry. rewrite <- (Z_to_bv_bv_unsigned y). change (Z_to_bv 64 (bv_unsigned y)) with (wa (bv_unsigned y)). apply Hoff; [| exact Ny].
pose proof (bv_unsigned_in_range 64 y) as YR. unfold bv_modulus in YR. cbn in YR. lia. }
apply (rw_cells_transport asegs [(fp, fp + 1)] m1 m2) in SAVED; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; unfold client_addr in FPnc; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] m1 m2) in SLOTS; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; unfold client_addr in FPnc; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] m1 m2) in GAP; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; unfold client_addr in FPnc; lia].
apply (stk_transport_disjoint asegs [(fp, fp + 1)] m1 m2) in ST; [| exact MUr | exact WMr | cbn [disjoint_from]; unfold client_addr in FPnc; lia].
change (605392 + 4) with 605396.
clear FF FSH FPC.
reenterA asegs A4L HIx asegs_wx HP2.
step. step.
replace (sp0 - 104) with (sp0 + -104) in SAVED by lia.
do 13 step.
step. step.
evt_done5.
assert (ST2 : stk asegs m2 lo sp0).
{ pose proof (stk_release asegs _ _ _ _ ST SLOTS ltac:(lia)) as ST1. rewrite pe_slotsA_size in ST1 || cbn [cells_size csize Nat.add] in ST1.
pose proof (stk_release asegs _ _ _ _ ST1 GAP ltac:(lia)) as STg. cbn [cells_size csize Nat.add] in STg.
rewrite Nat.add_0_r, Z2Nat.id in STg by lia.
replace (spf + Z.of_nat 312 + (sp0 - 104 - (spf + 312))) with (sp0 + -104) in STg by lia.
pose proof (stk_release asegs _ _ _ _ STg SAVED ltac:(lia)) as STs. cbn [cells_size csize Nat.add] in STs.
replace (sp0 + -104 + Z.of_nat 104) with sp0 in STs by lia. exact STs. }
eapply K.
all: lazymatch goal with
| |- model_vm_only _ _ => exact VM2
| |- HEAPA _ _ _ _ _ _ _ _ _ => exact HP2
| |- stk _ _ _ _ => exact ST2
| |- 0 < _ < _ => exact FPR
| |- ~ client_addr _ _ _ _ => exact FPnc
| |- _ \/ _ => exact FPimg
| |- ~ hl_scratch _ _ => exact FPns
| |- forall F' k', _ => intros F' k' Hin'; apply FPfr; right; exact Hin'
| |- munch _ _ _ => eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact MUr]]; intros z Hz; cbn [outside] in Hz |- *; tauto
| |- wmono _ _ _ => intros z Hz; apply WMr; apply WM; exact Hz
| |- mem_inv _ _ => exact MI2
end.
Qed.
End PeEpiB.
End RC__1.
