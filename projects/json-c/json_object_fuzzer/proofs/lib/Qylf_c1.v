(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply Q5Rg QRjH QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw Q8tj QSL3 QeL5 QLLZ QAIk Ql9N QbFI QRBl Qhd4 Qwm6 QlKV QsKa Q30W QnDr QeVJ Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw Q8tj.
Import QSL3. Import QeL5 QLLZ QAIk Ql9N.Mq0.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqe Q30W.Mq6 QnDr QeVJ.Mq1 QlKV.Mqd.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Local Ltac sepcache_on ::= fail.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section ALhDelete.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis OBL_AMEMSET : amemset_spec_A HIx.
Notation SB0 := 2147450880.

Ltac fastW tt tb sz :=
repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd];
first [ left; split; assumption
| right; left; exists tt, 56; split; [ in_app_prefix | clear; lia ]
| right; left; exists tb, (40 * sz); split; [ in_app_prefix | match goal with R : tb <= ?b /\ ?b + 40 <= tb + 40 * sz |- _ => clear - R; lia end ] ].
Ltac hp_nowF tt tb sz HPx H :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch type of HPx with HEAPA _ _ ?Ax ?LBx ?LMx ?FRx ?Bx ?mb ?mdx =>
match goal with MUc : munch _ mb mc, WMc : wmono asegs mb mc, MIc : mem_inv asegs mc |- _ =>
assert (H : HEAPA A4L HIx Ax LBx LMx FRx Bx mc mdx);
[ eapply (heapA_client_frame A4L HIx);
[ exact HPx | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HPx MUc); fastW tt tb sz | exact WMc | exact MIc ] | ]
end end end.
Ltac hp_nowR HPx H :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch type of HPx with HEAPA _ _ ?Ax ?LBx ?LMx ?FRx ?Bx ?mb ?mdx =>
match goal with MUc : munch _ mb mc, WMc : wmono asegs mb mc, MIc : mem_inv asegs mc |- _ =>
assert (H : HEAPA A4L HIx Ax LBx LMx FRx Bx mc mdx);
[ eapply (heapA_client_frame A4L HIx);
[ exact HPx | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HPx MUc); solve_frameW_withA HPx | exact WMc | exact MIc ] | ]
end end end.

Ltac shadow_inA HP Hin SH :=
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ _ _ HP Hin) as SH;
unfold shad in SH; apply shadow_ro_cells in SH;
lazymatch type of SH with ro_cells _ _ _ (shadow_cells ?n) => let cs := eval cbv in (shadow_cells n) in change (shadow_cells n) with cs in SH end;
cbn [hl_sb hl_segs hla_base A4L A4H] in SH; unfold A_SB in SH.

Ltac slot_shA HP Hin Bx SH :=
lazymatch goal with EBx : Bx = ent_addr ?tb (le_ix ?x) |- _ =>
pose proof (ent_shadowA HIx _ _ _ _ _ _ _ tb _ (le_ix x) HP Hin ltac:(lia) ltac:(lia)) as SH; rewrite <- EBx in SH;
cbn [hl_sb hl_segs hla_base A4L A4H] in SH; unfold A_SB in SH end.

Lemma lh_writes_presA : forall A t tbl size es LB LM FRS B m md m' W SP,
HEAPAx A (lh_blocks t tbl size es ++ LB) LM FRS B m md -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= SP) \/ (t <= fst iv /\ snd iv <= t + 56) \/ (tbl <= fst iv /\ snd iv <= tbl + 40 * size)) W ->
alloc_ceiling <= SP ->
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) SP m m'.
Proof.
intros A t tbl size es LB LM FRS B m md m' W SP HP MU WM HW HSP.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. rewrite <- app_assoc in ND.
eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) SP); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb] | exact HSP |].
clear -HW ND HP. induction W as [|[a b] W IH]; [apply Forall_nil|].
apply Forall_cons_iff in HW as [H1 HW]. apply Forall_cons; [| apply IH; exact HW]. cbn [fst snd] in *.
destruct H1 as [H1 | [H1 | H1]].
- left. exact H1.
- right; left. exists t, 56. split; [apply in_or_app; left; left; reflexivity|]. split; [| lia].
intros IN. apply in_app_or in IN as [IN|IN]; [| apply in_app_or in IN as [IN|IN]].
+ eapply (nodup_prefix_suffix (lh_blocks t tbl size es) (LB ++ LM) t 56 56); [exact ND | left; reflexivity | apply in_or_app; left; exact IN].
+ eapply (nodup_prefix_suffix (lh_blocks t tbl size es) (LB ++ LM) t 56 56); [exact ND | left; reflexivity | apply in_or_app; right; exact IN].
+ exact (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP ltac:(apply in_or_app; left; left; reflexivity) IN).
- right; left. exists tbl, (40 * size). split; [apply in_or_app; left; right; left; reflexivity|]. split; [| lia].
intros IN. apply in_app_or in IN as [IN|IN]; [| apply in_app_or in IN as [IN|IN]].
+ eapply (nodup_prefix_suffix (lh_blocks t tbl size es) (LB ++ LM) tbl (40 * size) (40 * size)); [exact ND | right; left; reflexivity | apply in_or_app; left; exact IN].
+ eapply (nodup_prefix_suffix (lh_blocks t tbl size es) (LB ++ LM) tbl (40 * size) (40 * size)); [exact ND | right; left; reflexivity | apply in_or_app; right; exact IN].
+ exact (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP ltac:(apply in_or_app; left; right; left; reflexivity) IN).
Qed.

Section DelLoopA.
Variables (sp gp : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud).
Variables (lo t tbl size : Z) (ES : list lent) (jf : nat) (ef : lent) (T : TSet).
Variables (rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c s11c : word).
Variable errv : word.
Hypothesis COST : lh_delete_costB ES jf <= bB B0.

Definition del_frameA (m : word -> option byte) : Prop :=
rw_cells asegs m (bv_unsigned sp + -48) [C8 s4c; C8 s3c; C8 s2c; C8 s1c; C8 s0c; C8 rac].

Definition dl_regsA (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 : word) (E : Z) (s4v t3 t4 t5 t6 : word) :=
mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (ent_addr tbl (le_ix ef))) (Z_to_bv 64 t)
a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 E) (Z_to_bv 64 SB0) s4v s5c s6c s7c s8c s9c s10c s11c t3 t4 t5 t6.

Definition del_budA (B : bud) (rem : Z) : Prop := bB B0 - lh_delete_costB ES jf + 512 * rem <= bB B /\ bD B0 <= bD B.

Definition del_exitA (esf : list lent) : Prop :=
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 : word) (E : Z) (s4v t3 t4 t5 t6 : word)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (svsf : list slotv),
HEAPAx A (lh_blocks t tbl size esf ++ LB) LM FRS B m md ->
lh_open asegs A4F m t tbl size esf svsf ->
stk asegs m lo (bv_unsigned sp + -48) -> del_frameA m ->
rw_cells asegs m A_ERRNO [C4 errv] ->
model_vm_only (cfg_model md0) (cfg_model md) -> heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m ->
del_budA B 0 ->
AJ5 A4L HIx A T md
(MS (dl_regsA x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 E s4v t3 t4 t5 t6) F (Z_to_bv 64 0xa5364) fc None m (seg_rom asegs)).

Lemma lh_del_loopA :
forall (d : nat) (es0 : list lent) (e : lent) (svs : list slotv)
(x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4v t3 t4 t5 t6 : word)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud),
(d = length es0 - jf)%nat -> (jf <= length es0)%nat -> nth_error (es0 ++ [e]) jf = Some ef ->
HEAPAx A (lh_blocks t tbl size (es0 ++ [e]) ++ LB) LM FRS B m md ->
lh_open asegs A4F m t tbl size (es0 ++ [e]) svs ->
(forall j x, (jf <= j)%nat -> nth_error (es0 ++ [e]) j = Some x -> le_v x = 0) ->
stk asegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -144 - 16 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
del_frameA m -> rw_cells asegs m A_ERRNO [C4 errv] ->
model_vm_only (cfg_model md0) (cfg_model md) -> heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m ->
del_budA B (Z.of_nat (length es0) + 1 - Z.of_nat jf) ->
del_exitA (firstn jf es0) ->
AJ5 A4L HIx A T md
(MS (dl_regsA x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (ent_addr tbl (le_ix e)) s4v t3 t4 t5 t6) F (Z_to_bv 64 0xa52ec) fc None m (seg_rom asegs)).
Proof.
induction d as [|d IH]; intros until B; intros Hd Hjf Hef HP OPEN VZ ST LO LOS SPA HT FR ERR VM0 HPR BUD KX.
all: pose proof OPEN as (HDR & SL & LINK & KEYS & Hsz & Hcnt & Hlen); unfold lh_hdr, lh_hdrf in HDR.
all: rewrite tl_of_app in HDR.
all: pose proof LINK as (LK1 & LK2 & LK3 & LK4).
all: assert (Ee : nth_error (es0 ++ [e]) (length es0) = Some e) by (rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity).
all: destruct (LK1 (length es0) e Ee) as (se & Ese & Ek & Ekc & Ev & Enx & Epv).
all: pose proof (SL (le_ix e) se Ese) as C; unfold slot_cells in C; rewrite Ek, Ekc, Ev, Enx, Epv in C.
all: rewrite (VZ (length es0) e ltac:(lia) Ee) in C; rewrite (nx_of_app_new tbl es0 e (length es0) eq_refl) in C.
all: pose proof (proj1 (nth_error_Some svs (le_ix e)) ltac:(rewrite Ese; discriminate)) as Hix.
all: destruct (LK1 jf ef Hef) as (sf & Esf & _); pose proof (proj1 (nth_error_Some svs (le_ix ef)) ltac:(rewrite Esf; discriminate)) as Hixf; clear sf Esf.
all: destruct (LK4 e ltac:(apply in_or_app; right; left; reflexivity)) as (Hk0 & HkF & Hkn31 & Hv).
all: unfold del_frameA in FR; unfold del_budA in BUD; unfold lh_delete_costB in BUD, COST; unfold_consts; word_range sp SPR.
all: pose proof (lf_thr_lt size Hsz) as Hlt; pose proof (lf_size_range size Hsz) as HSR.
all: assert (LEN : Z.of_nat (length (es0 ++ [e])) = Z.of_nat (length es0) + 1) by (rewrite length_app; cbn; lia); rewrite LEN in HDR, Hcnt.
all: pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI; cbn [hl_segs hla_base A4L A4H] in MI.
all: pose proof (heapA_budget A4L HIx _ _ _ _ _ _ _ HP) as [BB0 BD0].
all: destruct (lh_heap_factsA HIx _ _ _ _ _ _ _ _ _ _ _ HP) as ((Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & SEP & KF).
all: cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Htimg, Hbimg; unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hbhi, KF.
all: destruct (KF e ltac:(apply in_or_app; right; left; reflexivity)) as (Hkn0 & _ & Hkhi & Hkimg & DKt & DKb); cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hkimg.
all: assert (IXNE : forall j1 j2 y1 y2, nth_error (es0 ++ [e]) j1 = Some y1 -> nth_error (es0 ++ [e]) j2 = Some y2 -> j1 <> j2 -> le_ix y1 <> le_ix y2) by
(intros j1 j2 y1 y2 H1 H2 NE X; apply NE; eapply (proj1 (NoDup_nth_error _) LK3 j1 j2);
[ rewrite length_map; apply (proj1 (nth_error_Some _ j1)); rewrite H1; discriminate
| erewrite nth_error_map, H1, nth_error_map, H2; cbn; rewrite X; reflexivity ]).
all: assert (HPk : HEAPAx A ((le_k e, le_kn e) :: (t, 56) :: (tbl, 40 * size) :: (map kblk es0 ++ LB)) LM FRS B m md) by
(eapply (heapA_perm A4L HIx); [exact HP | apply perm_key_front | apply Permutation_refl | apply Permutation_refl]).
all: assert (INt : In (t, 56) ((le_k e, le_kn e) :: (t, 56) :: (tbl, 40 * size) :: (map kblk es0 ++ LB))) by (right; left; reflexivity).
all: assert (INb : In (tbl, 40 * size) ((le_k e, le_kn e) :: (t, 56) :: (tbl, 40 * size) :: (map kblk es0 ++ LB))) by (right; right; left; reflexivity).

all: destruct (snoc_inv es0) as [E0 | (es1 & el & E0)]; [| destruct (LK1 (length es1) el ltac:(rewrite E0, <- app_assoc; cbn; rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity)) as (sl & Esl & Elk & Elkc & Elv & Elnx & Elpv)].
3:{ exfalso. subst es0. cbn in Hd. lia. }

all: try (pose proof (SL (le_ix el) sl Esl) as Cl; unfold slot_cells in Cl; rewrite Elk, Elkc, Elv, Elnx, Elpv in Cl;
pose proof (proj1 (nth_error_Some svs (le_ix el)) ltac:(rewrite Esl; discriminate)) as Hixl;
assert (L0 : length es0 = S (length es1)) by (rewrite E0, length_app; cbn; lia);
assert (NXl : nx_of tbl (es0 ++ [e]) (length es1) = ent_addr tbl (le_ix e)) by (unfold nx_of; rewrite <- L0, Ee; reflexivity); rewrite NXl in Cl;
assert (PV : pv_of tbl (es0 ++ [e]) (length es0) = ent_addr tbl (le_ix el)) by (rewrite E0; apply pv_of_snoc2); rewrite PV in C;
assert (NEl : le_ix el <> le_ix e) by
(eapply (IXNE (length es1) (length es0)); [rewrite E0, <- app_assoc; cbn; rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity | exact Ee | lia]);
destruct (nth_error es0 0) as [x0|] eqn:Ex0; [| exfalso; apply nth_error_None in Ex0; lia];
assert (HD0 : hd_of tbl (es0 ++ [e]) = ent_addr tbl (le_ix x0)) by (rewrite hd_of_nth, nth_error_app1, Ex0 by lia; reflexivity);
assert (NE0 : le_ix x0 <> le_ix e) by (eapply (IXNE 0%nat (length es0)); [rewrite nth_error_app1 by lia; exact Ex0 | exact Ee | lia]);
destruct (LK1 0%nat x0 ltac:(rewrite nth_error_app1 by lia; exact Ex0)) as (sx0 & Esx0 & _);
pose proof (proj1 (nth_error_Some svs (le_ix x0)) ltac:(rewrite Esx0; discriminate)) as Hix0;
rewrite HD0 in HDR;
destruct (KF el ltac:(rewrite E0; apply in_or_app; left; apply in_or_app; right; left; reflexivity)) as (_ & Hlklo & Hlkhi & _ & DKlt & DKlb)).
1: replace (pv_of tbl (es0 ++ [e]) (length es0)) with 0 in C by (rewrite E0; reflexivity);
replace (hd_of tbl (es0 ++ [e])) with (ent_addr tbl (le_ix e)) in HDR by (rewrite E0; reflexivity);
rewrite E0 in Hef, Hjf; cbn [app] in Hef; cbn in Hjf; assert (Hjf0 : jf = 0%nat) by lia;
rewrite Hjf0 in Hef; cbn in Hef; injection Hef as Eef.
all: remember (ent_addr tbl (le_ix e)) as Bx eqn:EB.
all: assert (HB : Bx = tbl + 40 * Z.of_nat (le_ix e)) by (rewrite EB; reflexivity).
all: assert (EA8 : Bx mod 8 = 0) by (rewrite HB; clear - Hbal; Z.div_mod_to_equations; lia).
all: assert (BXR : tbl <= Bx /\ Bx + 40 <= tbl + 40 * size) by (rewrite HB; clear - Hix Hlen; lia).
all: try (remember (ent_addr tbl (le_ix el)) as Bl eqn:EBl; assert (HBl : Bl = tbl + 40 * Z.of_nat (le_ix el)) by (rewrite EBl; reflexivity);
assert (EAl8 : Bl mod 8 = 0) by (rewrite HBl; clear - Hbal; Z.div_mod_to_equations; lia);
assert (BLR : tbl <= Bl /\ Bl + 40 <= tbl + 40 * size) by (rewrite HBl; clear - Hixl Hlen; lia)).
all: slot_shA HPk INb Bx SHe.
all: shadow_inA HPk INt SHt.
all: a4l.
all: pose proof (wmono_refl asegs m) as WM; pose proof (munch_refl [(t, t + 56); (lo, bv_unsigned sp)] m) as MU.
all: try stash Hkimg; try stash DKt; try stash DKb; try stash DKlt; try stash DKlb; try stash KF; try stash IXNE;
try stash LK1; try stash LK2; try stash LK3; try stash LK4; try stash VZ; try stash KX; try stash SL; try stash KEYS; try stash LINK; try stash OPEN; try stash IH.
all: pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HPk) as [GOT CELL]; cbn [hl_segs hl_sb hl_sb_cell hl_got_sb hla_base A4L A4H] in GOT, CELL; unfold A_SB, A_SB_CELL, A_GOT_SB in GOT, CELL.
all: unfold dl_regsA; reenterA asegs A4L HIx asegs_wx HP.

all: step; if_falsex.
all: step; rewrite (unsigned_lit Bx) by lia; rewrite (ub_land7 Bx EA8); step; if_false.
all: step.
all: step; step; sh_norm; rewrite (div8_add Bx 32) by lia; change (32 / 8) with 4.
all: step; rewrite ?zxb_zero; step; if_false.
all: step.
all: step; step; step.

all: carve_frame 48%nat ST.
all: step; stepz; do 3 step; stepz; stepz.
all: step; if_falsex.
all: step; rewrite (unsigned_lit t) by lia; rewrite (ub_land7 t) by (clear - Htal; Z.div_mod_to_equations; lia); step; if_false.
all: do 3 step.
all: step.
all: step; step; sh_norm; rewrite (div8_add t 24) by lia; change (24 / 8) with 3.
all: step; rewrite ?zxb_zero; step; if_false.
all: step.
all: step; rewrite (unsigned_lit Bx), (unsigned_lit tbl) by lia.
all: step; if_falsex.
all: step; if_falsex.
all: step; step; step; step; ub_resolve.
all: step; rewrite (unsigned_lit Bx) by lia; rewrite (ub_land7 Bx EA8); step; if_false.
all: step; if_falsex.
all: step; replace (tbl + (Bx - tbl)) with Bx by lia.
all: step; step; sh_norm.
all: step; rewrite ?zxb_zero; step; if_false.
all: step.
all: step.
all: step.
all: unfold bv_ltu, bv_leu; rewrite ?(unsigned_lit (le_k e)) by (unfold LH_FREEDv in *; lia);
try replace (bv_unsigned (Z_to_bv 64 (-3))) with 18446744073709551613 by (vm_compute; reflexivity).
all: first [ if_truex | if_true | destruct (Z.ltb_spec _ _); [| exfalso; unfold LH_FREEDv in *; lia] | idtac ].

all: step.
all: step; step; sh_norm; rewrite (div8_add t 4) by lia; change (4 / 8) with 0; rewrite ?Z.add_0_r.
all: step; rewrite ?sxb_zero, ?zxb_zero; step; if_false.
all: step; norm_sx32.
all: step; norm_w32.
all: step; if_falsex.
all: step; rewrite ?sxb_zero, ?zxb_zero; step; if_false.
all: try clear SHt; try clear SHe.
all: stepz.
all: step.
all: hp_nowF t tbl size HPk HPc; shadow_inA HPc INt SHt; slot_shA HPc INb Bx SHe; clear HPc.
all: step; step; sh_norm; rewrite (div8_add t 32) by lia; change (32 / 8) with 4.
all: step; rewrite ?zxb_zero; step; if_false.
all: step.
all: step; if_false.
all: step; step; step.
all: cbn [fn_lh_entry_free A4F]; replace (ret_pc (Z_to_bv 64 644392)) with (Z_to_bv 64 644392) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
all: hp_nowF t tbl size HPk HP1.
all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (SLx : lh_slots asegs mx tbl svs) by
(unstash SL; eapply lh_slots_frame; [exact SL | exact MU | exact WM |]; intros i Hi; rewrite <- Hlen in Hbhi, SEP;
apply Forall_cons; [cbn; unfold ent_addr; clear - Hi SEP; lia | apply Forall_cons; [cbn; unfold ent_addr; clear - Hi Hbhi LO; lia | apply Forall_nil]]);
assert (KEYSx : lh_keys asegs mx es0) by
(unstash KEYS; unstash KF; eapply lh_keys_frame; [unfold lh_keys in KEYS |- *; apply Forall_app in KEYS as [K0 _]; exact K0 | exact MU | exact WM |];
intros y Hy; destruct (KF y ltac:(apply in_or_app; left; exact Hy)) as (Ky0 & Ky1 & Ky2 & Ky3 & Ky4 & Ky5);
apply Forall_cons; [cbn; clear - Ky4; lia | apply Forall_cons; [cbn; clear - Ky2 LO; lia | apply Forall_nil]]);
assert (HPRx : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mx) by
(eapply (lh_writes_presA A t tbl size (es0 ++ [e]) LB LM FRS B m md mx); [exact HP | exact MU | exact WM | | clear - LO SPR LOS; unfold alloc_ceiling, sp_window_lo, stack_max_size; lia];
apply Forall_cons; [cbn; right; left; clear; lia | apply Forall_cons; [cbn; left; clear - LO; unfold alloc_ceiling, sp_window_lo, stack_max_size; lia | apply Forall_nil]])
end.
all: evt_done5;
eapply (lh_entry_free_A_cps HIx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ md T A ((t, 56) :: (tbl, 40 * size) :: (map kblk es0 ++ LB)) LM FRS B
Bx (le_k e) (le_kn e) (sv_pad se) 0 _ lo errv);
[ exact HP1 | exact C | exact SHe | .. ]; a4l_goal; rewrite ?unsigned_lit by lia; try first [eassumption | reflexivity].
all: try lazymatch goal with
| |- 0 < _ => clear - BXR Hblo; lia
| |- _ <= bv_unsigned _ + -96 - 16 - 4096 => clear - LOS; lia
| |- _ + 40 <= alloc_ceiling => clear - BXR Hbhi; unfold alloc_ceiling, sp_window_lo, stack_max_size; lia
| |- _ \/ _ => clear - BXR Hbimg; lia
| |- _ / 8 + _ + 3 <= alloc_ceiling => clear - BXR Hbhi Hblo; unfold alloc_ceiling, sp_window_lo, stack_max_size; Z.div_mod_to_equations; lia
| |- _ mod 16 = 0 => clear - SPA; Z.div_mod_to_equations; lia
| |- _ <= hiA_top _ _ => clear - HT; lia
| |- 512 <= bB _ => clear - BUD COST Hjf; lia
end.
all: intros ms2 md2 A2 (m2 & r2 & RS & VM2 & ST2 & HPR2 & ERR2 & HP2).
all: destruct RS as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & ->); a4l.
all: rewrite ?(unsigned_lit (bv_unsigned sp + -48)), ?(unsigned_lit (bv_unsigned sp + -96)), ?(unsigned_lit (bv_unsigned sp + -48 + -48)) in ST2, HPR2 by lia.
all: apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]; a4l.
all: match goal with FRi : rw_cells asegs _ (bv_unsigned sp + -48 + -48) _ |- _ => apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FRi; [| left; cbn; lia]
| FRi : rw_cells asegs _ (bv_unsigned sp + -96) [_; _; _; _; _; _] |- _ => apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FRi; [| left; cbn; lia] | |- _ => idtac end; a4l.
all: apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in HDR; [| eapply client_range_block; [apply in_or_app; left; left; reflexivity | lia | cbn; lia]]; a4l.
all: apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in C; [| eapply client_range_block; [apply in_or_app; left; right; left; reflexivity | lia | cbn; lia]]; a4l.
all: try (apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in Cl; [| eapply client_range_block; [apply in_or_app; left; right; left; reflexivity | lia | cbn; lia]]; a4l).
all: pose proof (lh_slots_pres A4H _ _ _ _ tbl svs size HPR2 ltac:(apply in_or_app; left; right; left; reflexivity) Hlen SLx) as SL2; a4l.
all: pose proof (lh_keys_pres A4H _ _ _ _ es0 HPR2 ltac:(intros y Hy; apply in_or_app; left; right; right; apply in_or_app; left; apply in_map_iff; exists y; split; [reflexivity | exact Hy]) KEYSx) as KEYS2; a4l.
all: stash SL2; stash KEYS2.
all: assert (HPR' : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m2) by
(eapply heap_pres_trans; [exact HPR|]; eapply heap_pres_trans; [exact HPRx|]; eapply heap_pres_weaken;
[exact HPR2 | lia | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; right; right; apply in_or_app; right; exact Hb | right; exact Hb]]).
all: clear MU WM MI SLx KEYSx HPRx HPk HP1; try clear SHe; try clear SHt; try clear GOT; try clear CELL.
all: pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI; cbn [hl_segs hla_base A4L A4H] in MI.
all: pose proof (heapA_budget A4L HIx _ _ _ _ _ _ _ HP2) as [BB2 BD2]; cbn [bB bD charge] in BB2, BD2.
all: pose proof (wmono_refl asegs m2) as WM.
1: pose proof (munch_refl [(t, t + 56); (Bx, Bx + 40); (lo, bv_unsigned sp)] m2) as MU.
2,3: pose proof (munch_refl [(t, t + 56); (Bx, Bx + 40); (Bl, Bl + 40); (lo, bv_unsigned sp)] m2) as MU.
all: assert (INt2 : In (t, 56) ((t, 56) :: (tbl, 40 * size) :: map kblk es0 ++ LB)) by (left; reflexivity).
all: assert (INb2 : In (tbl, 40 * size) ((t, 56) :: (tbl, 40 * size) :: map kblk es0 ++ LB)) by (right; left; reflexivity).
all: shadow_inA HP2 INt2 SHt.
all: reenterA asegs A4L HIx asegs_wx HP2.
all: step.
all: step; rewrite ?zxb_zero; step; if_false.
all: step.
all: step; replace (tbl + (Bx - tbl)) with Bx by lia.
all: step; if_falsex.
all: step; step; step; step; ub_resolve.
all: step; if_falsex.
all: step; rewrite (unsigned_lit Bx) by lia; rewrite (ub_land7 Bx EA8); step; if_false.
all: step.
all: slot_shA HP2 INb2 Bx SHe.
all: step; step; sh_norm; rewrite (div8_add Bx 16) by lia; change (16 / 8) with 2.
all: step; rewrite ?zxb_zero; step; if_false.
all: try clear SHe; try clear SHt.
all: stepz.
all: step; if_falsex.
all: hp_nowF t tbl size HP2 HPc; slot_shA HPc INb2 Bx SHe; shadow_inA HPc INt2 SHt; clear HPc.
all: step; step; sh_norm.
all: step; rewrite ?zxb_zero; step; if_false.
all: step. all: step.
all: try clear SHe; try clear SHt.
all: stepz.
all: hp_nowF t tbl size HP2 HPc; shadow_inA HPc INt2 SHt; clear HPc.
all: step; step; sh_norm; rewrite (div8_add t 16) by lia; change (16 / 8) with 2.
all: step; rewrite ?zxb_zero; step; if_false.
all: step.
all: step. all: step. all: step.
all: step.
all: rewrite ?(bv_eqb_refl (Z_to_bv 64 Bx)); cbn [negb]; cbv iota.
all: step; step; sh_norm; rewrite (div8_add t 8) by lia; change (8 / 8) with 1.
all: step; rewrite ?zxb_zero; step; if_false.
all: step.
all: step.
1: rewrite ?(bv_eqb_refl (Z_to_bv 64 Bx)); cbv iota.
2,3: unfold ent_addr.
2,3: assert (XX : tbl + 40 * Z.of_nat (le_ix x0) <> Bx) by (rewrite HB; clear - NE0; lia).
2,3: if_falsex; change (tbl + 40 * Z.of_nat (le_ix ef)) with (ent_addr tbl (le_ix ef)).

2,3: step; step; sh_norm; rewrite (div8_add t 8) by lia; change (8 / 8) with 1.
2,3: step; rewrite ?zxb_zero; step; if_false.
2,3: step.
2,3: step; unfold ent_addr; if_falsex; change (tbl + 40 * Z.of_nat (le_ix ef)) with (ent_addr tbl (le_ix ef)).
2,3: step; rewrite ?(bv_eqb_refl (Z_to_bv 64 Bx)); cbv iota.
2,3: step.
2,3: try clear SHe; hp_nowF t tbl size HP2 HPc; slot_shA HPc INb2 Bx SHe; slot_shA HPc INb2 Bl SHl; clear HPc.
2,3: step; step; sh_norm; rewrite (div8_add Bx 32) by lia; change (32 / 8) with 4.
2,3: step; rewrite ?zxb_zero; step; if_false.
2,3: step.
2,3: step; if_falsex.
2,3: step; rewrite (unsigned_lit Bl) by lia; rewrite (ub_land7 Bl EAl8); step; if_false.
2,3: step.
2,3: step; step; sh_norm; rewrite (div8_add Bl 24) by lia; change (24 / 8) with 3.
2,3: step; rewrite ?zxb_zero; step; if_false.
2,3: try clear SHe; try clear SHl; try clear SHt.
2,3: stepz.
2,3: hp_nowF t tbl size HP2 HPc; shadow_inA HPc INt2 SHt; clear HPc.
2,3: step; rewrite ?zxb_zero; step; if_false.
2,3: try clear SHt.
2,3: step.
2,3: step.

1: step; step; step.
1: try clear SHt; try clear SHe.
1: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch type of HDR with rw_cells _ _ _ [?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8] =>
change [c1; c2; c3; c4; c5; c6; c7; c8] with ([c1; c2] ++ [c3; c4] ++ [c5; c6; c7; c8]) in HDR;
destruct (proj1 (rw_cells_app asegs mc t _ _) HDR) as [HD1 HD23]; clear HDR;
destruct (proj1 (rw_cells_app asegs mc _ _ _) HD23) as [HD2 HD3]; clear HD23;
cbn [cells_size csize Nat.add] in HD2, HD3;
replace (t + Z.of_nat 8) with (t + 8) in HD2, HD3 by lia; replace (t + 8 + Z.of_nat 16) with (t + 24) in HD3 by lia;
apply (rw_cells_recast asegs mc (t + 8) _ [CB 16 (cells_bytes [c3; c4])]) in HD2;
[| cbn; repeat split; exact I | cbn [cells_bytes cbytes app]; rewrite ?app_nil_r; reflexivity | reflexivity]
end;
hp_nowF t tbl size HP2 HPc;
match goal with MIc : mem_inv asegs mc, STc : stk asegs mc lo _ |- _ =>
eapply (OBL_AMEMSET _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t 56 (t + 8) 0 16 lo);
[ exact HPc | exact INt2 | lia | lia | reflexivity | reflexivity | reflexivity | lia | lia | exact HD2
| rewrite ?unsigned_lit by lia; exact STc | lia | rewrite ?unsigned_lit by lia; lia
| rewrite ?unsigned_lit by lia; rewrite <- Zplus_mod_idemp_l, SPA; reflexivity
| rewrite ?unsigned_lit by lia; lia | exact MIc | reflexivity | ]; clear HPc end end.
1: intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' mA MUA WMA MIA DSTA STA.
1: rewrite ?unsigned_lit in MUA, STA by lia.
1: lazymatch type of MUA with munch _ ?mc _ =>
transport_after_call asegs mc mA MUA WMA; try match goal with H : mem_inv asegs mc |- _ => clear H end end.
1: clear MUA WMA.
1: replace (ret_pc (Z_to_bv 64 0xa518c)) with (Z_to_bv 64 0xa518c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
1: change (Z.to_nat 16) with 16%nat in DSTA; cbn [repeat] in DSTA.
1: apply (rw_cells_recast asegs mA (t + 8) _ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) in DSTA; [| cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity].
1: lazymatch type of HD1 with rw_cells _ _ _ [?c1; ?c2] => lazymatch type of HD3 with rw_cells _ _ _ [?c5; ?c6; ?c7; ?c8] =>
assert (HDR : rw_cells asegs mA t ([c1; c2] ++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ++ [c5; c6; c7; c8]));
[ apply (proj2 (rw_cells_app asegs mA t _ _)); cbn [cells_size csize Nat.add]; replace (t + Z.of_nat 8) with (t + 8) by lia; split; [exact HD1|];
apply (proj2 (rw_cells_app asegs mA (t + 8) _ _)); cbn [cells_size csize Nat.add]; replace (t + 8 + Z.of_nat 16) with (t + 24) by lia; split; [exact DSTA | exact HD3]
| clear HD1 DSTA HD3; cbn [app] in HDR ] end end.

all: hp_nowF t tbl size HP2 HPc; slot_shA HPc INb2 Bx SHe; clear HPc.
all: step; step; sh_norm; rewrite (div8_add Bx 32) by lia; change (32 / 8) with 4.
all: step; rewrite ?zxb_zero; step; if_false.
all: try clear SHe; try clear SHt; try clear SHl.
all: stepz.
all: hp_nowF t tbl size HP2 HPc; slot_shA HPc INb2 Bx SHe; clear HPc.
all: step; step; sh_norm; rewrite (div8_add Bx 24) by lia; change (24 / 8) with 3.
all: step; rewrite ?zxb_zero; step; if_false.
all: try clear SHe.
all: stepz.
all: do 6 step.
all: step.
all: match goal with FRi : rw_cells asegs _ (bv_unsigned sp + -48 + -48) _, STi : stk asegs _ lo (bv_unsigned sp + -48 + -48) |- _ => release_frame FRi STi (bv_unsigned sp + -48)
| FRi : rw_cells asegs _ (bv_unsigned sp + -96) _, STi : stk asegs _ lo (bv_unsigned sp + -96) |- _ => release_frame FRi STi (bv_unsigned sp + -48) end.
all: step.

all: step; if_true.
all: step.
2: assert (Eef : e = ef) by (replace jf with (length es0) in Hef by lia; rewrite Ee in Hef; injection Hef as X; exact X).
1,2: match goal with |- context [Z.lxor ?x ?y] => replace (Z.lxor x y) with 0 by (symmetry; rewrite <- Eef; unfold ent_addr; rewrite <- ?HB, ?(unsigned_lit Bx) by lia; apply Z.lxor_nilpotent) end.
1,2: step; step; step; if_truex.
1,2: step; step; if_falsex.
3: assert (NEf : le_ix e <> le_ix ef) by (unstash IXNE; eapply (IXNE (length es0) jf); [exact Ee | exact Hef | lia]).
3: rewrite ?(unsigned_lit Bx) by lia; unfold ent_addr; rewrite ?unsigned_lit by (clear - Hixf Hlen Hbhi Hblo LO; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia).
3: step.
3: lazymatch goal with |- context [v_sltiu (Z_to_bv 64 (Z.lxor ?bx ?ee)) 1] =>
assert (XNZ : 0 < Z.lxor bx ee < 2 ^ 64);
[ pose proof (lxor_bound bx ee 64 ltac:(clear; lia) ltac:(clear - BXR Hblo Hbhi; lia) ltac:(clear - Hixf Hlen Hbhi Hblo HSR; lia)) as XB;
destruct (Z.eq_dec (Z.lxor bx ee) 0) as [X0|X0]; [exfalso; apply (proj1 (lxor_zero_iff bx ee)) in X0; clear - X0 HB NEf; lia | clear - XB X0; lia]
| rewrite (v_sltiu_0 (Z_to_bv 64 (Z.lxor bx ee)) 1) by (rewrite ?unsigned_lit by (clear - XNZ; lia); clear - XNZ; lia) ] end.
3: step; step; try if_falsex.
3: change (tbl + 40 * Z.of_nat (le_ix ef)) with (ent_addr tbl (le_ix ef)).
3: step; step; unfold ent_addr; if_falsex.
3: change (tbl + 40 * Z.of_nat (le_ix ef)) with (ent_addr tbl (le_ix ef)).
3: step; step; if_true.
3: step; step; if_falsex.
all: try clear ST; try clear ERR; try clear FR0.
all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
all: try clear SHt; try clear SHe; try clear SHl.
all: try unstash Hkimg; try unstash DKt; try unstash DKb; try unstash DKlt; try unstash DKlb; try unstash KF; try unstash IXNE;
try unstash LK1; try unstash LK2; try unstash LK3; try unstash LK4; try unstash VZ; try unstash KX; try unstash SL; try unstash KEYS; try unstash LINK; try unstash OPEN; try unstash IH; try unstash SL2; try unstash KEYS2.
all: hp_nowF t tbl size HP2 HPF.
all: change ((t, 56) :: (tbl, 40 * size) :: map kblk es0 ++ LB) with (lh_blocks t tbl size es0 ++ LB) in HPF.
all: assert (HPRF : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 mF) by
(eapply heap_pres_trans; [exact HPR'|]; eapply (lh_writes_presA A2 t tbl size es0 LB LM FRS _ m2 md2 mF);
[exact HP2 | exact MU | exact WM | | clear - LO SPR LOS; unfold alloc_ceiling, sp_window_lo, stack_max_size; lia];
repeat (apply Forall_cons; [cbn [fst snd];
first [ right; left; clear; lia
| right; right; match goal with R : tbl <= ?b /\ ?b + 40 <= tbl + 40 * size |- tbl <= ?b /\ _ => clear - R; lia end
| left; clear - LO SPR; unfold alloc_ceiling, sp_window_lo, stack_max_size; lia ] |]); apply Forall_nil).
all: assert (KEYSF : lh_keys asegs mF es0) by
(eapply lh_keys_frame; [exact KEYS2 | exact MU | exact WM |];
intros y Hy; destruct (KF y ltac:(apply in_or_app; left; exact Hy)) as (Ky0 & Ky1 & Ky2 & Ky3 & Ky4 & Ky5);
repeat (apply Forall_cons; [cbn [fst snd];
first [ clear - Ky4; lia
| match goal with R : tbl <= ?b /\ ?b + 40 <= tbl + 40 * size |- _ \/ ?b + 40 <= _ => clear - Ky5 R; lia | R : tbl <= ?b /\ ?b + 40 <= tbl + 40 * size |- _ <= ?b \/ _ => clear - Ky5 R; lia end
| clear - Ky2 LO; lia ] |]); apply Forall_nil).
all: assert (C' : rw_cells asegs mF (ent_addr tbl (le_ix e)) (slot_cells (del_slot se))) by
(unfold slot_cells, del_slot; cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv]; rewrite Ekc, <- EB; exact C).
2,3: assert (Cl' : rw_cells asegs mF (ent_addr tbl (le_ix el)) (slot_cells (clr_nx sl))) by
(unfold slot_cells, clr_nx; cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv]; rewrite Elk, Elkc, Elv, Elpv, <- EBl; exact Cl).
1: assert (SLF : lh_slots asegs mF tbl (upd svs (le_ix e) (del_slot se))) by
(eapply (lh_slots_write1 asegs m2 mF tbl svs _ (le_ix e) (del_slot se)); [exact SL2 | exact Hix | exact MU | exact WM | | exact C'];
intros i NE Hi; unfold ivs_miss_slot; rewrite <- Hlen in Hbhi, SEP;
repeat (apply Forall_cons; [cbn [fst snd]; unfold ent_addr;
first [ clear - Hi SEP; lia | clear - NE HB; lia | clear - Hi Hbhi LO; lia ] |]); apply Forall_nil).
2,3: assert (SLF : lh_slots asegs mF tbl (upd (upd svs (le_ix e) (del_slot se)) (le_ix el) (clr_nx sl))) by
(eapply (lh_slots_write2 asegs m2 mF tbl svs _ (le_ix e) (del_slot se) (le_ix el) (clr_nx sl));
[exact SL2 | exact Hix | exact Hixl | exact (not_eq_sym NEl) | exact MU | exact WM | | exact C' | exact Cl'];
intros i NE1 NE2 Hi; unfold ivs_miss_slot; rewrite <- Hlen in Hbhi, SEP;
repeat (apply Forall_cons; [cbn [fst snd]; unfold ent_addr;
first [ clear - Hi SEP; lia | clear - NE1 HB; lia | clear - NE2 HBl; lia | clear - Hi Hbhi LO; lia ] |]); apply Forall_nil).
all: try replace (Z.of_nat (length es0) + 1 + -1) with (Z.of_nat (length es0)) in HDR by lia.
1: assert (OPENF : lh_open asegs A4F mF t tbl size [] (upd svs (le_ix e) (del_slot se))).
1:{ split; [| split; [exact SLF | split; [exact (lh_link_unsnoc_nil tbl es0 e svs se LINK Ese E0) | split; [constructor | split; [exact Hsz | split; [cbn; lia | rewrite upd_length; exact Hlen]]]]]].
unfold lh_hdrf. rewrite E0 in HDR. exact HDR. }
2,3: assert (OPENF : lh_open asegs A4F mF t tbl size es0 (upd (upd svs (le_ix e) (del_slot se)) (le_ix el) (clr_nx sl))).
2:{ split; [| split; [exact SLF | split; [exact (lh_link_unsnoc_cons tbl es0 e svs se LINK Ese es1 el sl E0 Esl) | split; [exact KEYSF | split; [exact Hsz | split; [lia | rewrite !upd_length; exact Hlen]]]]]].
unfold lh_hdrf. rewrite hd_of_nth, Ex0. replace (tl_of tbl es0) with (ent_addr tbl (le_ix el)) by (rewrite E0; symmetry; apply tl_of_app). rewrite <- EBl. exact HDR. }
3:{ split; [| split; [exact SLF | split; [exact (lh_link_unsnoc_cons tbl es0 e svs se LINK Ese es1 el sl E0 Esl) | split; [exact KEYSF | split; [exact Hsz | split; [lia | rewrite !upd_length; exact Hlen]]]]]].
unfold lh_hdrf. rewrite hd_of_nth, Ex0. replace (tl_of tbl es0) with (ent_addr tbl (le_ix el)) by (rewrite E0; symmetry; apply tl_of_app). rewrite <- EBl. exact HDR. }

1: rewrite E0, firstn_nil in KX; rewrite E0 in HPF.
2: rewrite firstn_all2 in KX by lia.
1,2: evt_done5; eapply KX; first [exact HPF | exact OPENF | exact HPRF | eapply model_vm_only_trans; [exact VM0 | exact VM2] | unfold del_frameA; eassumption | idtac].
all: try (unfold A_ERRNO; eassumption).
all: try (solve [unfold del_budA, lh_delete_costB in *; cbn [bB bD charge] in *; split; lia]).

all: try (replace (Z_to_bv 64 Bl) with (Z_to_bv 64 (ent_addr tbl (le_ix el))) by (rewrite EBl; reflexivity)).
all: try (rewrite E0, firstn_snoc_le in KX by lia).
all: try (rewrite E0 in HPF, OPENF).
all: evt_done5.
all: eapply (IH es1 el _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mF md2 A2);
first [exact HPF | exact OPENF | exact HPRF | exact KX | exact LO | exact SPA | exact HT | idtac].
+ lia.
+ lia.
+ rewrite <- E0. rewrite nth_error_app1 in Hef by lia. exact Hef.
+ intros j x Hj Hx. apply (VZ j x Hj). rewrite <- E0 in Hx.
rewrite nth_error_app1 by (apply (proj1 (nth_error_Some es0 j)); rewrite Hx; discriminate). exact Hx.
+ eassumption.
+ lia.
+ unfold del_frameA. eassumption.
+ unfold A_ERRNO. eassumption.
+ eapply model_vm_only_trans; [exact VM0 | exact VM2].
+ unfold del_budA, lh_delete_costB in *. cbn [bB bD charge] in *. rewrite E0, length_app in BUD. cbn [length] in BUD. split; lia.
Qed.

Lemma del_exit_okA : forall (esf : list lent),
bv_unsigned rac mod 2 = 0 -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -48 ->
(forall (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (svsf : list slotv)
(t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
HEAPAx A (lh_blocks t tbl size esf ++ LB) LM FRS B m md -> lh_open asegs A4F m t tbl size esf svsf ->
stk asegs m lo (bv_unsigned sp) -> rw_cells asegs m A_ERRNO [C4 errv] ->
model_vm_only (cfg_model md0) (cfg_model md) -> heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m -> del_budA B 0 ->
AJ5 A4L HIx A T md
(MS (mkR rac sp gp (Z_to_bv 64 A_TP) t0 t1 t2 s0c s1c (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2c s3c s4c s5c s6c s7c s8c s9c s10c s11c t3 t4 t5 t6)
F (ret_pc rac) fc None m (seg_rom asegs))) ->
del_exitA esf.
Proof.
intros esf RAC LO LOS K. unfold del_exitA. intros until svsf; intros HP OPEN ST FR ERR VM0 HPR BUD.
unfold del_frameA in FR. unfold_consts. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [] m) as MU.
unfold dl_regsA. a4l. reenterA asegs A4L HIx asegs_wx HP.
step. step. do 6 step. step.
release_frame FR ST (bv_unsigned sp). step.
evt_done5.
eapply K; [exact HP | exact OPEN | exact ST | exact ERR | exact VM0 | exact HPR | exact BUD].
Qed.
End DelLoopA.

Lemma lh_delete_tail_A_cps : lh_delete_tail_A_stmt HIx.
Proof.
unfold lh_delete_tail_A_stmt. intros until ef. intros HP OPEN Hef VZ ST LO LOS SPA HT ERR TP RA A0 A1 COST K.
pose proof OPEN as (HDR & SL & LINK & KEYS & Hsz & Hcnt & Hlen). unfold lh_hdr, lh_hdrf in HDR.
destruct (snoc_inv es) as [Enil | (es0 & e & E0)]; [rewrite Enil in Hef; destruct jf; discriminate|].
pose proof (proj1 (nth_error_Some es jf) ltac:(rewrite Hef; discriminate)) as Hjf. rewrite E0, length_app in Hjf. cbn in Hjf.
replace (tl_of tbl es) with (ent_addr tbl (le_ix e)) in HDR by (rewrite E0, tl_of_app; reflexivity).
remember (hd_of tbl es) as HDv eqn:EHD.
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR.
unfold_consts. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
destruct (lh_heap_factsA HIx _ _ _ _ _ _ _ _ _ _ _ HP) as ((Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & SEP & KF).
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Htimg, Hbimg. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hbhi, KF.
assert (BELOW : lh_below lo t tbl size es).
{ split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros x Hx. destruct (KF x Hx). lia. }
assert (INt : In (t, 56) (lh_blocks t tbl size es ++ LB)) by (left; reflexivity).
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
shadow_inA HP INt SHt.
a4l.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
subst a0 a1 tp. unfold lh_delete_tail_A_entry. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 48%nat ST.
do 7 step.
step. if_falsex.
step.
step. rewrite (unsigned_lit t) by lia. rewrite (ub_land7 t) by (clear - Htal; Z.div_mod_to_equations; lia). step. if_false.
step.
do 3 step.
step.
step. step. sh_norm. rewrite (div8_add t 16) by lia. change (16 / 8) with 2.
step. rewrite ?zxb_zero. step. if_false.
step.
step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (OPEN1 : lh_open asegs A4F mx t tbl size es svs) by
(eapply (lh_open_frame asegs A4F _ m mx t tbl size es svs _ lo); [exact OPEN | exact BELOW | exact MU | exact WM | apply Forall_cons; [cbn; lia | apply Forall_nil]]);
assert (HPR1 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mx) by
(eapply (lh_writes_presA A t tbl size es LB LM FRS B m md mx); [exact HP | exact MU | exact WM | apply Forall_cons; [cbn; left; clia | apply Forall_nil] | clia]);
rename mx into m1
end.
hp_nowR HP HP1.
rewrite E0 in HP1, OPEN1, Hef, VZ, COST.
unfold lh_delete_tail_A_post in K. rewrite E0, (firstn_snoc_le _ es0 e jf) in K by lia.
evt_done5.
eapply lh_del_loopA with (m0 := m) (md0 := md) (B0 := B) (ES := es0 ++ [e]) (d := (length es0 - jf)%nat) (es0 := es0) (e := e) (svs := svs)
(LB := LB) (LM := LM) (FRS := FRS) (lo := lo) (tbl := tbl) (size := size) (jf := jf) (rac := ra) (errv := errv) (T := T);
first [exact COST | reflexivity | exact Hef | exact HP1 | exact OPEN1 | exact VZ | apply model_vm_only_refl | exact HPR1 | exact SPA | exact HT | idtac].
- lia.
- exact ST.
- clia.
- lia.
- unfold del_frameA. eassumption.
- unfold A_ERRNO in *. eassumption.
- unfold del_budA, lh_delete_costB. rewrite length_app. cbn [length]. split; lia.
- apply del_exit_okA; [exact RA | clia | lia |].
intros m' md' A' B' svsf u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 HPf OPENf STf ERRf VMf HPRf BUDf.
apply K. exists m', svsf, B'.
split; [unfold ret_state; do 14 eexists; reflexivity|].
split; [exact VMf|]. split; [exact STf|]. split; [exact HPRf|]. split; [exact ERRf|]. split; [exact OPENf|].
unfold del_budA, lh_delete_costB in *. rewrite ?length_app in *. cbn [length] in *.
split; [lia|]. split; [lia|]. exact HPf.
Qed.
End ALhDelete.
End RC__1.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8tj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QeL5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QeL5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLLZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLLZ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QAIk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QAIk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql9N.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql9N.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7UD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7UD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q30W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q30W.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnDr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDr.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QeVJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QeVJ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq3.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Local Ltac sepcache_on ::= fail.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section ALhDelete.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis OBL_AMEMSET : amemset_spec_A HIx.
Notation SB0 := 2147450880.

Ltac fastW tt tb sz :=
repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd];
first [ left; split; assumption
| right; left; exists tt, 56; split; [ in_app_prefix | clear; lia ]
| right; left; exists tb, (40 * sz); split; [ in_app_prefix | match goal with R : tb <= ?b /\ ?b + 40 <= tb + 40 * sz |- _ => clear - R; lia end ] ].
Ltac hp_nowF tt tb sz HPx H :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch type of HPx with HEAPA _ _ ?Ax ?LBx ?LMx ?FRx ?Bx ?mb ?mdx =>
match goal with MUc : munch _ mb mc, WMc : wmono asegs mb mc, MIc : mem_inv asegs mc |- _ =>
assert (H : HEAPA A4L HIx Ax LBx LMx FRx Bx mc mdx);
[ eapply (heapA_client_frame A4L HIx);
[ exact HPx | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HPx MUc); fastW tt tb sz | exact WMc | exact MIc ] | ]
end end end.
Ltac hp_nowR HPx H :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch type of HPx with HEAPA _ _ ?Ax ?LBx ?LMx ?FRx ?Bx ?mb ?mdx =>
match goal with MUc : munch _ mb mc, WMc : wmono asegs mb mc, MIc : mem_inv asegs mc |- _ =>
assert (H : HEAPA A4L HIx Ax LBx LMx FRx Bx mc mdx);
[ eapply (heapA_client_frame A4L HIx);
[ exact HPx | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HPx MUc); solve_frameW_withA HPx | exact WMc | exact MIc ] | ]
end end end.

Ltac shadow_inA HP Hin SH :=
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ _ _ HP Hin) as SH;
unfold shad in SH; apply shadow_ro_cells in SH;
lazymatch type of SH with ro_cells _ _ _ (shadow_cells ?n) => let cs := eval cbv in (shadow_cells n) in change (shadow_cells n) with cs in SH end;
cbn [hl_sb hl_segs hla_base A4L A4H] in SH; unfold A_SB in SH.

Ltac slot_shA HP Hin Bx SH :=
lazymatch goal with EBx : Bx = ent_addr ?tb (le_ix ?x) |- _ =>
pose proof (ent_shadowA HIx _ _ _ _ _ _ _ tb _ (le_ix x) HP Hin ltac:(lia) ltac:(lia)) as SH; rewrite <- EBx in SH;
cbn [hl_sb hl_segs hla_base A4L A4H] in SH; unfold A_SB in SH end.

Lemma lh_writes_presA : forall A t tbl size es LB LM FRS B m md m' W SP,
HEAPAx A (lh_blocks t tbl size es ++ LB) LM FRS B m md -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= SP) \/ (t <= fst iv /\ snd iv <= t + 56) \/ (tbl <= fst iv /\ snd iv <= tbl + 40 * size)) W ->
alloc_ceiling <= SP ->
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) SP m m'.
Proof.
intros A t tbl size es LB LM FRS B m md m' W SP HP MU WM HW HSP.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. rewrite <- app_assoc in ND.
eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) SP); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb] | exact HSP |].
clear -HW ND HP. induction W as [|[a b] W IH]; [apply Forall_nil|].
apply Forall_cons_iff in HW as [H1 HW]. apply Forall_cons; [| apply IH; exact HW]. cbn [fst snd] in *.
destruct H1 as [H1 | [H1 | H1]].
- left. exact H1.
- right; left. exists t, 56. split; [apply in_or_app; left; left; reflexivity|]. split; [| lia].
intros IN. apply in_app_or in IN as [IN|IN]; [| apply in_app_or in IN as [IN|IN]].
+ eapply (nodup_prefix_suffix (lh_blocks t tbl size es) (LB ++ LM) t 56 56); [exact ND | left; reflexivity | apply in_or_app; left; exact IN].
+ eapply (nodup_prefix_suffix (lh_blocks t tbl size es) (LB ++ LM) t 56 56); [exact ND | left; reflexivity | apply in_or_app; right; exact IN].
+ exact (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP ltac:(apply in_or_app; left; left; reflexivity) IN).
- right; left. exists tbl, (40 * size). split; [apply in_or_app; left; right; left; reflexivity|]. split; [| lia].
intros IN. apply in_app_or in IN as [IN|IN]; [| apply in_app_or in IN as [IN|IN]].
+ eapply (nodup_prefix_suffix (lh_blocks t tbl size es) (LB ++ LM) tbl (40 * size) (40 * size)); [exact ND | right; left; reflexivity | apply in_or_app; left; exact IN].
+ eapply (nodup_prefix_suffix (lh_blocks t tbl size es) (LB ++ LM) tbl (40 * size) (40 * size)); [exact ND | right; left; reflexivity | apply in_or_app; right; exact IN].
+ exact (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP ltac:(apply in_or_app; left; right; left; reflexivity) IN).
Qed.

Section DelLoopA.
Variables (sp gp : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud).
Variables (lo t tbl size : Z) (ES : list lent) (jf : nat) (ef : lent) (T : TSet).
Variables (rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c s11c : word) (junk8 : list byte).
Variable errv : word.
Hypothesis COST : lh_delete_costB ES jf <= bB B0.

Definition del_frameA (m : word -> option byte) : Prop :=
rw_cells asegs m (bv_unsigned sp + -144)
[CB 8 junk8; C8 (Z_to_bv 64 7); C8 (Z_to_bv 64 (t / 8 + 2147450884)); C8 (Z_to_bv 64 (t / 8 + 2147450880)); C8 (Z_to_bv 64 (t + 32));
C8 s11c; C8 s10c; C8 s9c; C8 s8c; C8 s7c; C8 s6c; C8 s5c; C8 s4c; C8 s3c; C8 s2c; C8 s1c; C8 s0c; C8 rac].

Definition dl_regsA (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 : word) (E : Z) (s9 t3 t4 t5 t6 : word) :=
mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (t + 16)) (Z_to_bv 64 (ent_addr tbl (le_ix ef)))
a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (t + 24)) (Z_to_bv 64 (t + 8)) (Z_to_bv 64 (t + 4)) s5 (Z_to_bv 64 E) (Z_to_bv 64 SB0)
(Z_to_bv 64 (t / 8 + 2147450882)) s9 (Z_to_bv 64 (t / 8 + 2147450881)) (Z_to_bv 64 (t / 8 + 2147450883)) t3 t4 t5 t6.

Definition del_budA (B : bud) (rem : Z) : Prop := bB B0 - lh_delete_costB ES jf + 512 * rem <= bB B /\ bD B0 <= bD B.

Definition del_exitA (esf : list lent) : Prop :=
forall (x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s5 : word) (E : Z) (s9 t3 t4 t5 t6 : word)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (svsf : list slotv),
HEAPAx A (lh_blocks t tbl size esf ++ LB) LM FRS B m md ->
lh_open asegs A4F m t tbl size esf svsf ->
stk asegs m lo (bv_unsigned sp + -144) -> del_frameA m ->
rw_cells asegs m A_ERRNO [C4 errv] ->
model_vm_only (cfg_model md0) (cfg_model md) -> heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m ->
del_budA B 0 ->
AJ5 A4L HIx A T md
(MS (dl_regsA x1 t0 t1 t2 a0 (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s5 E s9 t3 t4 t5 t6) F (Z_to_bv 64 0xa2c80) fc None m (seg_rom asegs)).

Lemma lh_del_loopA :
forall (d : nat) (es0 : list lent) (e : lent) (svs : list slotv)
(x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s9 t3 t4 t5 t6 : word)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud),
(d = length es0 - jf)%nat -> (jf <= length es0)%nat -> nth_error (es0 ++ [e]) jf = Some ef ->
HEAPAx A (lh_blocks t tbl size (es0 ++ [e]) ++ LB) LM FRS B m md ->
lh_open asegs A4F m t tbl size (es0 ++ [e]) svs ->
(forall j x, (jf <= j)%nat -> nth_error (es0 ++ [e]) j = Some x -> le_v x = 0) ->
stk asegs m lo (bv_unsigned sp + -144) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -144 - 16 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
del_frameA m -> rw_cells asegs m A_ERRNO [C4 errv] ->
model_vm_only (cfg_model md0) (cfg_model md) -> heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m ->
del_budA B (Z.of_nat (length es0) + 1 - Z.of_nat jf) ->
del_exitA (firstn jf es0) ->
AJ5 A4L HIx A T md
(MS (dl_regsA x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 (ent_addr tbl (le_ix e)) s9 t3 t4 t5 t6) F (Z_to_bv 64 0xa2a5c) fc None m (seg_rom asegs)).
Proof.
induction d as [|d IH]; intros until B; intros Hd Hjf Hef HP OPEN VZ ST LO LOS SPA HT FR ERR VM0 HPR BUD KX.
all: pose proof OPEN as (HDR & SL & LINK & KEYS & Hsz & Hcnt & Hlen); unfold lh_hdr, lh_hdrf in HDR.
all: rewrite tl_of_app in HDR.
all: pose proof LINK as (LK1 & LK2 & LK3 & LK4).
all: assert (Ee : nth_error (es0 ++ [e]) (length es0) = Some e) by (rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity).
all: destruct (LK1 (length es0) e Ee) as (se & Ese & Ek & Ekc & Ev & Enx & Epv).
all: pose proof (SL (le_ix e) se Ese) as C; unfold slot_cells in C; rewrite Ek, Ekc, Ev, Enx, Epv in C.
all: rewrite (VZ (length es0) e ltac:(lia) Ee) in C; rewrite (nx_of_app_new tbl es0 e (length es0) eq_refl) in C.
all: pose proof (proj1 (nth_error_Some svs (le_ix e)) ltac:(rewrite Ese; discriminate)) as Hix.
all: destruct (LK1 jf ef Hef) as (sf & Esf & _); pose proof (proj1 (nth_error_Some svs (le_ix ef)) ltac:(rewrite Esf; discriminate)) as Hixf; clear sf Esf.
all: destruct (LK4 e ltac:(apply in_or_app; right; left; reflexivity)) as (Hk0 & HkF & Hkn31 & Hv).
all: unfold del_frameA in FR; unfold del_budA in BUD; unfold lh_delete_costB in BUD, COST; unfold_consts; word_range sp SPR.
all: pose proof (lf_thr_lt size Hsz) as Hlt; pose proof (lf_size_range size Hsz) as HSR.
all: assert (LEN : Z.of_nat (length (es0 ++ [e])) = Z.of_nat (length es0) + 1) by (rewrite length_app; cbn; lia); rewrite LEN in HDR, Hcnt.
all: pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI; cbn [hl_segs hla_base A4L A4H] in MI.
all: pose proof (heapA_budget A4L HIx _ _ _ _ _ _ _ HP) as [BB0 BD0].
all: destruct (lh_heap_factsA HIx _ _ _ _ _ _ _ _ _ _ _ HP) as ((Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & SEP & KF).
all: cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Htimg, Hbimg; unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hbhi, KF.
all: destruct (KF e ltac:(apply in_or_app; right; left; reflexivity)) as (Hkn0 & _ & Hkhi & Hkimg & DKt & DKb); cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hkimg.
all: assert (IXNE : forall j1 j2 y1 y2, nth_error (es0 ++ [e]) j1 = Some y1 -> nth_error (es0 ++ [e]) j2 = Some y2 -> j1 <> j2 -> le_ix y1 <> le_ix y2) by
(intros j1 j2 y1 y2 H1 H2 NE X; apply NE; eapply (proj1 (NoDup_nth_error _) LK3 j1 j2);
[ rewrite length_map; apply (proj1 (nth_error_Some _ j1)); rewrite H1; discriminate
| erewrite nth_error_map, H1, nth_error_map, H2; cbn; rewrite X; reflexivity ]).
all: assert (HPk : HEAPAx A ((le_k e, le_kn e) :: (t, 56) :: (tbl, 40 * size) :: (map kblk es0 ++ LB)) LM FRS B m md) by
(eapply (heapA_perm A4L HIx); [exact HP | apply perm_key_front | apply Permutation_refl | apply Permutation_refl]).
all: assert (INt : In (t, 56) ((le_k e, le_kn e) :: (t, 56) :: (tbl, 40 * size) :: (map kblk es0 ++ LB))) by (right; left; reflexivity).
all: assert (INb : In (tbl, 40 * size) ((le_k e, le_kn e) :: (t, 56) :: (tbl, 40 * size) :: (map kblk es0 ++ LB))) by (right; right; left; reflexivity).

all: destruct (snoc_inv es0) as [E0 | (es1 & el & E0)]; [| destruct (LK1 (length es1) el ltac:(rewrite E0, <- app_assoc; cbn; rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity)) as (sl & Esl & Elk & Elkc & Elv & Elnx & Elpv)].
3:{ exfalso. subst es0. cbn in Hd. lia. }

all: try (pose proof (SL (le_ix el) sl Esl) as Cl; unfold slot_cells in Cl; rewrite Elk, Elkc, Elv, Elnx, Elpv in Cl;
pose proof (proj1 (nth_error_Some svs (le_ix el)) ltac:(rewrite Esl; discriminate)) as Hixl;
assert (L0 : length es0 = S (length es1)) by (rewrite E0, length_app; cbn; lia);
assert (NXl : nx_of tbl (es0 ++ [e]) (length es1) = ent_addr tbl (le_ix e)) by (unfold nx_of; rewrite <- L0, Ee; reflexivity); rewrite NXl in Cl;
assert (PV : pv_of tbl (es0 ++ [e]) (length es0) = ent_addr tbl (le_ix el)) by (rewrite E0; apply pv_of_snoc2); rewrite PV in C;
assert (NEl : le_ix el <> le_ix e) by
(eapply (IXNE (length es1) (length es0)); [rewrite E0, <- app_assoc; cbn; rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity | exact Ee | lia]);
destruct (nth_error es0 0) as [x0|] eqn:Ex0; [| exfalso; apply nth_error_None in Ex0; lia];
assert (HD0 : hd_of tbl (es0 ++ [e]) = ent_addr tbl (le_ix x0)) by (rewrite hd_of_nth, nth_error_app1, Ex0 by lia; reflexivity);
assert (NE0 : le_ix x0 <> le_ix e) by (eapply (IXNE 0%nat (length es0)); [rewrite nth_error_app1 by lia; exact Ex0 | exact Ee | lia]);
destruct (LK1 0%nat x0 ltac:(rewrite nth_error_app1 by lia; exact Ex0)) as (sx0 & Esx0 & _);
pose proof (proj1 (nth_error_Some svs (le_ix x0)) ltac:(rewrite Esx0; discriminate)) as Hix0;
rewrite HD0 in HDR;
destruct (KF el ltac:(rewrite E0; apply in_or_app; left; apply in_or_app; right; left; reflexivity)) as (_ & Hlklo & Hlkhi & _ & DKlt & DKlb)).
1: replace (pv_of tbl (es0 ++ [e]) (length es0)) with 0 in C by (rewrite E0; reflexivity);
replace (hd_of tbl (es0 ++ [e])) with (ent_addr tbl (le_ix e)) in HDR by (rewrite E0; reflexivity);
rewrite E0 in Hef, Hjf; cbn [app] in Hef; cbn in Hjf; assert (Hjf0 : jf = 0%nat) by lia;
rewrite Hjf0 in Hef; cbn in Hef; injection Hef as Eef.
all: remember (ent_addr tbl (le_ix e)) as Bx eqn:EB.
all: assert (HB : Bx = tbl + 40 * Z.of_nat (le_ix e)) by (rewrite EB; reflexivity).
all: assert (EA8 : Bx mod 8 = 0) by (rewrite HB; clear - Hbal; Z.div_mod_to_equations; lia).
all: assert (BXR : tbl <= Bx /\ Bx + 40 <= tbl + 40 * size) by (rewrite HB; clear - Hix Hlen; lia).
all: try (remember (ent_addr tbl (le_ix el)) as Bl eqn:EBl; assert (HBl : Bl = tbl + 40 * Z.of_nat (le_ix el)) by (rewrite EBl; reflexivity);
assert (EAl8 : Bl mod 8 = 0) by (rewrite HBl; clear - Hbal; Z.div_mod_to_equations; lia);
assert (BLR : tbl <= Bl /\ Bl + 40 <= tbl + 40 * size) by (rewrite HBl; clear - Hixl Hlen; lia)).
all: slot_shA HPk INb Bx SHe.
all: shadow_inA HPk INt SHt.
all: a4l.
all: pose proof (wmono_refl asegs m) as WM; pose proof (munch_refl [(t, t + 56); (lo, bv_unsigned sp)] m) as MU.
all: try stash Hkimg; try stash DKt; try stash DKb; try stash DKlt; try stash DKlb; try stash KF; try stash IXNE;
try stash LK1; try stash LK2; try stash LK3; try stash LK4; try stash VZ; try stash KX; try stash SL; try stash KEYS; try stash LINK; try stash OPEN; try stash IH.
all: unfold dl_regsA; reenterA asegs A4L HIx asegs_wx HP.
all: step.
all: step; step; sh_norm; rewrite (div8_add Bx 32) by lia; change (32 / 8) with 4.
all: step; rewrite ?zxb_zero; step; if_false.
all: step; rewrite ?zxb_zero; step; if_false.
all: step.
all: step; rewrite (unsigned_lit Bx), (unsigned_lit tbl) by lia.
all: step.
all: step; if_falsex.
all: step; replace (tbl + (Bx - tbl)) with Bx by lia.
all: step; step; sh_norm.
all: step; rewrite ?zxb_zero; step; if_false.
all: step.
all: step.
all: step.
all: replace (bv_ltu (Z_to_bv 64 (-3)) (Z_to_bv 64 (le_k e))) with false by
(symmetry; unfold bv_ltu; rewrite (unsigned_lit (le_k e)) by (unfold LH_FREEDv in *; lia);
replace (bv_unsigned (Z_to_bv 64 (-3))) with 18446744073709551613 by (vm_compute; reflexivity);
apply Z.ltb_ge; unfold LH_FREEDv in *; lia).
all: cbv iota.
all: step.
all: step; rewrite ?sxb_zero, ?zxb_zero.
all: step.
all: step; if_false.
all: step; norm_sx32; step.
all: try clear SHt; try clear SHe.
all: stepz.
all: step.
all: try clear SHt; try clear SHe.
all: hp_nowF t tbl size HPk HPc; shadow_inA HPc INt SHt; slot_shA HPc INb Bx SHe; clear HPc.
all: step; rewrite ?zxb_zero; step; if_false.
all: step; step.
all: step; if_false.
all: step; step.
all: cbn [fn_lh_entry_free A4F]; replace (ret_pc (Z_to_bv 64 638272)) with (Z_to_bv 64 638272) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
all: hp_nowF t tbl size HPk HP1.
all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (SLx : lh_slots asegs mx tbl svs) by
(unstash SL; eapply lh_slots_frame; [exact SL | exact MU | exact WM |]; intros i Hi; rewrite <- Hlen in Hbhi, SEP;
apply Forall_cons; [cbn; unfold ent_addr; clear - Hi SEP; lia | apply Forall_cons; [cbn; unfold ent_addr; clear - Hi Hbhi LO; lia | apply Forall_nil]]);
assert (KEYSx : lh_keys asegs mx es0) by
(unstash KEYS; unstash KF; eapply lh_keys_frame; [unfold lh_keys in KEYS |- *; apply Forall_app in KEYS as [K0 _]; exact K0 | exact MU | exact WM |];
intros y Hy; destruct (KF y ltac:(apply in_or_app; left; exact Hy)) as (Ky0 & Ky1 & Ky2 & Ky3 & Ky4 & Ky5);
apply Forall_cons; [cbn; clear - Ky4; lia | apply Forall_cons; [cbn; clear - Ky2 LO; lia | apply Forall_nil]]);
assert (HPRx : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mx) by
(eapply (lh_writes_presA A t tbl size (es0 ++ [e]) LB LM FRS B m md mx); [exact HP | exact MU | exact WM | | clear - LO SPR LOS; unfold alloc_ceiling, sp_window_lo, stack_max_size; lia];
apply Forall_cons; [cbn; right; left; clear; lia | apply Forall_cons; [cbn; left; clear - LO; unfold alloc_ceiling, sp_window_lo, stack_max_size; lia | apply Forall_nil]])
end.
all: evt_done5;
eapply (lh_entry_free_A_cps HIx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ md T A ((t, 56) :: (tbl, 40 * size) :: (map kblk es0 ++ LB)) LM FRS B
Bx (le_k e) (le_kn e) (sv_pad se) 0 _ lo errv);
[ exact HP1 | exact C | exact SHe | .. ]; a4l_goal; rewrite ?unsigned_lit by lia; try first [eassumption | reflexivity].
all: try lazymatch goal with
| |- _ + 40 <= alloc_ceiling => clear - BXR Hbhi; unfold alloc_ceiling, sp_window_lo, stack_max_size; lia
| |- _ \/ _ => clear - BXR Hbimg; lia
| |- _ / 8 + _ + 3 <= alloc_ceiling => clear - BXR Hbhi Hblo; unfold alloc_ceiling, sp_window_lo, stack_max_size; Z.div_mod_to_equations; lia
| |- _ mod 16 = 0 => clear - SPA; Z.div_mod_to_equations; lia
| |- _ <= hiA_top _ _ => clear - HT; lia
| |- 512 <= bB _ => clear - BUD COST Hjf; lia
end.
all: intros ms2 md2 A2 (m2 & r2 & RS & VM2 & ST2 & HPR2 & ERR2 & HP2).
all: destruct RS as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & ->); a4l.
all: rewrite ?(unsigned_lit (bv_unsigned sp + -144)) in ST2, HPR2 by lia.
all: apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]; a4l.
all: apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in HDR; [| eapply client_range_block; [apply in_or_app; left; left; reflexivity | lia | cbn; lia]]; a4l.
all: apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in C; [| eapply client_range_block; [apply in_or_app; left; right; left; reflexivity | lia | cbn; lia]]; a4l.
all: try (apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in Cl; [| eapply client_range_block; [apply in_or_app; left; right; left; reflexivity | lia | cbn; lia]]; a4l).
all: pose proof (lh_slots_pres A4H _ _ _ _ tbl svs size HPR2 ltac:(apply in_or_app; left; right; left; reflexivity) Hlen SLx) as SL2; a4l.
all: pose proof (lh_keys_pres A4H _ _ _ _ es0 HPR2 ltac:(intros y Hy; apply in_or_app; left; right; right; apply in_or_app; left; apply in_map_iff; exists y; split; [reflexivity | exact Hy]) KEYSx) as KEYS2; a4l.
all: stash SL2; stash KEYS2.
all: assert (HPR' : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m2) by
(eapply heap_pres_trans; [exact HPR|]; eapply heap_pres_trans; [exact HPRx|]; eapply heap_pres_weaken;
[exact HPR2 | lia | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; right; right; apply in_or_app; right; exact Hb | right; exact Hb]]).
all: clear MU WM MI SLx KEYSx HPRx HPk HP1; try clear SHe; try clear SHt.
all: pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI; cbn [hl_segs hla_base A4L A4H] in MI.
all: pose proof (heapA_budget A4L HIx _ _ _ _ _ _ _ HP2) as [BB2 BD2]; cbn [bB bD charge] in BB2, BD2.
all: pose proof (wmono_refl asegs m2) as WM.
1: pose proof (munch_refl [(t, t + 56); (Bx, Bx + 40); (lo, bv_unsigned sp)] m2) as MU.
2,3: pose proof (munch_refl [(t, t + 56); (Bx, Bx + 40); (Bl, Bl + 40); (lo, bv_unsigned sp)] m2) as MU.
all: assert (INt2 : In (t, 56) ((t, 56) :: (tbl, 40 * size) :: map kblk es0 ++ LB)) by (left; reflexivity).
all: assert (INb2 : In (tbl, 40 * size) ((t, 56) :: (tbl, 40 * size) :: map kblk es0 ++ LB)) by (right; left; reflexivity).
all: shadow_inA HP2 INt2 SHt.
all: reenterA asegs A4L HIx asegs_wx HP2.
all: step; rewrite ?zxb_zero; step; if_false.
all: step.
all: step; replace (tbl + (Bx - tbl)) with Bx by lia.
all: step.
all: slot_shA HP2 INb2 Bx SHe.
all: step; step; sh_norm; rewrite (div8_add Bx 16) by lia; change (16 / 8) with 2.
all: step; rewrite ?zxb_zero; step; if_false.
all: try clear SHe; try clear SHt.
all: stepz.
all: try clear SHe; try clear SHt.
all: hp_nowF t tbl size HP2 HPc; slot_shA HPc INb2 Bx SHe; shadow_inA HPc INt2 SHt; clear HPc.
all: step; step; sh_norm.
all: step; rewrite ?zxb_zero; step; if_false.
all: step.
all: try clear SHe; try clear SHt.
all: stepz.
all: try clear SHe; try clear SHt.
all: hp_nowF t tbl size HP2 HPc; shadow_inA HPc INt2 SHt; clear HPc.
all: step; rewrite ?zxb_zero; step; if_false.
all: step; rewrite ?zxb_zero; step; if_false.
all: try clear SHt.
all: step. all: step.
all: step.
all: step. all: replace (bv_eqb (Z_to_bv 64 Bx) (Z_to_bv 64 Bx)) with true by (symmetry; apply bv_eqb_refl); cbv iota.
all: step.
1: replace (bv_eqb (Z_to_bv 64 Bx) (Z_to_bv 64 Bx)) with true by (symmetry; apply bv_eqb_refl); cbv iota.
2,3: unfold ent_addr.
2,3: assert (XX : tbl + 40 * Z.of_nat (le_ix x0) <> Bx) by (rewrite HB; clear - NE0; lia).
2,3: if_falsex; change (tbl + 40 * Z.of_nat (le_ix ef)) with (ent_addr tbl (le_ix ef)).

2,3: step.
2,3: try clear SHe; hp_nowF t tbl size HP2 HPc; slot_shA HPc INb2 Bx SHe; slot_shA HPc INb2 Bl SHl; clear HPc.
2,3: step; step; sh_norm; rewrite (div8_add Bx 32) by lia; change (32 / 8) with 4.
2,3: step; rewrite ?zxb_zero; step; if_false.
2,3: step.
2,3: step.
2,3: step; step; sh_norm; rewrite (div8_add Bl 24) by lia; change (24 / 8) with 3.
2,3: step; rewrite ?zxb_zero; step; if_false.
2,3: try clear SHe; try clear SHl; try clear SHt.
2,3: stepz.
2,3: try clear SHe; try clear SHl; try clear SHt.
2,3: hp_nowF t tbl size HP2 HPc; shadow_inA HPc INt2 SHt; clear HPc.
2,3: step; rewrite ?zxb_zero; step; if_false.
2,3: try clear SHt.
2,3: step.
2,3: step.

1: step; step; step; step; step.
1: try clear SHt; try clear SHe.
1: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch type of HDR with rw_cells _ _ _ [?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8] =>
change [c1; c2; c3; c4; c5; c6; c7; c8] with ([c1; c2] ++ [c3; c4] ++ [c5; c6; c7; c8]) in HDR;
destruct (proj1 (rw_cells_app asegs mc t _ _) HDR) as [HD1 HD23]; clear HDR;
destruct (proj1 (rw_cells_app asegs mc _ _ _) HD23) as [HD2 HD3]; clear HD23;
cbn [cells_size csize Nat.add] in HD2, HD3;
replace (t + Z.of_nat 8) with (t + 8) in HD2, HD3 by lia; replace (t + 8 + Z.of_nat 16) with (t + 24) in HD3 by lia;
apply (rw_cells_recast asegs mc (t + 8) _ [CB 16 (cells_bytes [c3; c4])]) in HD2;
[| cbn; repeat split; exact I | cbn [cells_bytes cbytes app]; rewrite ?app_nil_r; reflexivity | reflexivity]
end;
hp_nowF t tbl size HP2 HPc;
match goal with MIc : mem_inv asegs mc, STc : stk asegs mc lo _ |- _ =>
eapply (OBL_AMEMSET _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t 56 (t + 8) 0 16 lo);
[ exact HPc | exact INt2 | lia | lia | reflexivity | reflexivity | reflexivity | lia | lia | exact HD2
| rewrite ?(unsigned_lit (bv_unsigned sp + -144)) by lia; exact STc | lia | rewrite ?(unsigned_lit (bv_unsigned sp + -144)) by lia; lia
| rewrite ?(unsigned_lit (bv_unsigned sp + -144)) by lia; rewrite <- Zplus_mod_idemp_l, SPA; reflexivity
| rewrite ?(unsigned_lit (bv_unsigned sp + -144)) by lia; lia | exact MIc | reflexivity | ]; clear HPc end end.
1: intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' mA MUA WMA MIA DSTA STA.
1: rewrite ?(unsigned_lit (bv_unsigned sp + -144)) in MUA, STA by lia.
1: lazymatch type of MUA with munch _ ?mc _ =>
transport_after_call asegs mc mA MUA WMA; try match goal with H : mem_inv asegs mc |- _ => clear H end end.
1: replace (ret_pc (Z_to_bv 64 0xa2c40)) with (Z_to_bv 64 0xa2c40) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
1: change (Z.to_nat 16) with 16%nat in DSTA; cbn [repeat] in DSTA.
1: apply (rw_cells_recast asegs mA (t + 8) _ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) in DSTA; [| cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity].
1: lazymatch type of HD1 with rw_cells _ _ _ [?c1; ?c2] => lazymatch type of HD3 with rw_cells _ _ _ [?c5; ?c6; ?c7; ?c8] =>
assert (HDR : rw_cells asegs mA t ([c1; c2] ++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ++ [c5; c6; c7; c8]));
[ apply (proj2 (rw_cells_app asegs mA t _ _)); cbn [cells_size csize Nat.add]; replace (t + Z.of_nat 8) with (t + 8) by lia; split; [exact HD1|];
apply (proj2 (rw_cells_app asegs mA (t + 8) _ _)); cbn [cells_size csize Nat.add]; replace (t + 8 + Z.of_nat 16) with (t + 24) by lia; split; [exact DSTA | exact HD3]
| clear HD1 DSTA HD3; cbn [app] in HDR ] end end.
1: step.

all: step; step; step.
all: try clear SHt; try clear SHe; try clear SHl.
all: lazymatch type of C with rw_cells _ ?mc _ [?c1; ?c2; ?c3; ?c4; ?c5; ?c6] =>
change [c1; c2; c3; c4; c5; c6] with ([c1; c2; c3; c4] ++ [c5; c6]) in C;
destruct (proj1 (rw_cells_app asegs mc Bx _ _) C) as [CG4 NP]; clear C;
cbn [cells_size csize Nat.add] in NP; replace (Bx + Z.of_nat 24) with (Bx + 24) in NP by lia;
apply (rw_cells_recast asegs mc (Bx + 24) _ [CB 16 (cells_bytes [c5; c6])]) in NP;
[| cbn; repeat split; exact I | cbn [cells_bytes cbytes app]; rewrite ?app_nil_r; reflexivity | reflexivity] end.
all: hp_nowF t tbl size HP2 HPc;
match goal with MIc : mem_inv asegs ?mc, STc : stk asegs ?mc lo _ |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply (OBL_AMEMSET _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tbl (40 * size) (Bx + 24) 0 16 lo);
[ exact HPc | exact INb2 | rewrite HB; lia | rewrite HB; rewrite <- Hlen in *; nia | reflexivity | reflexivity | reflexivity | lia | lia | exact NP
| rewrite ?(unsigned_lit (bv_unsigned sp + -144)) by lia; exact STc | lia | rewrite ?(unsigned_lit (bv_unsigned sp + -144)) by lia; lia
| rewrite ?(unsigned_lit (bv_unsigned sp + -144)) by lia; rewrite <- Zplus_mod_idemp_l, SPA; reflexivity
| rewrite ?(unsigned_lit (bv_unsigned sp + -144)) by lia; lia | exact MIc | reflexivity | ]; clear HPc end.
all: intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' mB MUB WMB MIB DSTB STB.
all: rewrite ?(unsigned_lit (bv_unsigned sp + -144)) in MUB, STB by lia.
all: try clear MUA; try clear WMA; try clear MIA.
all: lazymatch type of MUB with munch _ ?mc _ =>
transport_after_call asegs mc mB MUB WMB; try match goal with H : mem_inv asegs mc |- _ => clear H end end.
all: replace (ret_pc (Z_to_bv 64 0xa2c50)) with (Z_to_bv 64 0xa2c50) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
all: change (Z.to_nat 16) with 16%nat in DSTB; cbn [repeat] in DSTB.
all: apply (rw_cells_recast asegs mB (Bx + 24) _ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) in DSTB; [| cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity].
all: lazymatch type of CG4 with rw_cells _ _ _ [?c1; ?c2; ?c3; ?c4] =>
assert (C : rw_cells asegs mB Bx ([c1; c2; c3; c4] ++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]));
[ apply (proj2 (rw_cells_app asegs mB Bx _ _)); cbn [cells_size csize Nat.add]; replace (Bx + Z.of_nat 24) with (Bx + 24) by lia; split; [exact CG4 | exact DSTB]
| clear CG4 DSTB; cbn [app] in C ] end.
all: step.
all: step.
2: assert (Eef : e = ef) by (replace jf with (length es0) in Hef by lia; rewrite Ee in Hef; injection Hef as X; exact X).
1,2: replace (bv_eqb (Z_to_bv 64 Bx) (Z_to_bv 64 (ent_addr tbl (le_ix ef)))) with true by (symmetry; rewrite <- Eef, <- EB; apply bv_eqb_refl); cbv iota.
3: assert (NEf : le_ix e <> le_ix ef) by (unstash IXNE; eapply (IXNE (length es0) jf); [exact Ee | exact Hef | lia]).
3: unfold ent_addr; if_falsex; change (tbl + 40 * Z.of_nat (le_ix ef)) with (ent_addr tbl (le_ix ef)); step.
all: step.
all: step.
1,2: replace (bv_eqb (Z_to_bv 64 Bx) (Z_to_bv 64 (ent_addr tbl (le_ix ef)))) with true by (symmetry; rewrite <- Eef, <- EB; apply bv_eqb_refl); cbv iota.
3: unfold ent_addr; if_falsex; change (tbl + 40 * Z.of_nat (le_ix ef)) with (ent_addr tbl (le_ix ef)).
3: step; step; if_truex.

all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
all: try clear SHt; try clear SHe; try clear SHl.
all: try unstash Hkimg; try unstash DKt; try unstash DKb; try unstash DKlt; try unstash DKlb; try unstash KF; try unstash IXNE;
try unstash LK1; try unstash LK2; try unstash LK3; try unstash LK4; try unstash VZ; try unstash KX; try unstash SL; try unstash KEYS; try unstash LINK; try unstash OPEN; try unstash IH; try unstash SL2; try unstash KEYS2.
all: hp_nowF t tbl size HP2 HPF.
all: change ((t, 56) :: (tbl, 40 * size) :: map kblk es0 ++ LB) with (lh_blocks t tbl size es0 ++ LB) in HPF.
all: assert (HPRF : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 mF) by
(eapply heap_pres_trans; [exact HPR'|]; eapply (lh_writes_presA A2 t tbl size es0 LB LM FRS _ m2 md2 mF);
[exact HP2 | exact MU | exact WM | | clear - LO SPR LOS; unfold alloc_ceiling, sp_window_lo, stack_max_size; lia];
repeat (apply Forall_cons; [cbn [fst snd];
first [ right; left; clear; lia
| right; right; match goal with R : tbl <= ?b /\ ?b + 40 <= tbl + 40 * size |- tbl <= ?b /\ _ => clear - R; lia end
| left; clear - LO SPR; unfold alloc_ceiling, sp_window_lo, stack_max_size; lia ] |]); apply Forall_nil).
all: assert (KEYSF : lh_keys asegs mF es0) by
(eapply lh_keys_frame; [exact KEYS2 | exact MU | exact WM |];
intros y Hy; destruct (KF y ltac:(apply in_or_app; left; exact Hy)) as (Ky0 & Ky1 & Ky2 & Ky3 & Ky4 & Ky5);
repeat (apply Forall_cons; [cbn [fst snd];
first [ clear - Ky4; lia
| match goal with R : tbl <= ?b /\ ?b + 40 <= tbl + 40 * size |- _ \/ ?b + 40 <= _ => clear - Ky5 R; lia | R : tbl <= ?b /\ ?b + 40 <= tbl + 40 * size |- _ <= ?b \/ _ => clear - Ky5 R; lia end
| clear - Ky2 LO; lia ] |]); apply Forall_nil).
all: assert (C' : rw_cells asegs mF (ent_addr tbl (le_ix e)) (slot_cells (del_slot se))) by
(unfold slot_cells, del_slot; cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv]; rewrite Ekc, <- EB; exact C).
2,3: assert (Cl' : rw_cells asegs mF (ent_addr tbl (le_ix el)) (slot_cells (clr_nx sl))) by
(unfold slot_cells, clr_nx; cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv]; rewrite Elk, Elkc, Elv, Elpv, <- EBl; exact Cl).
1: assert (SLF : lh_slots asegs mF tbl (upd svs (le_ix e) (del_slot se))) by
(eapply (lh_slots_write1 asegs m2 mF tbl svs _ (le_ix e) (del_slot se)); [exact SL2 | exact Hix | exact MU | exact WM | | exact C'];
intros i NE Hi; unfold ivs_miss_slot; rewrite <- Hlen in Hbhi, SEP;
repeat (apply Forall_cons; [cbn [fst snd]; unfold ent_addr;
first [ clear - Hi SEP; lia | clear - NE HB; lia | clear - Hi Hbhi LO; lia ] |]); apply Forall_nil).
2,3: assert (SLF : lh_slots asegs mF tbl (upd (upd svs (le_ix e) (del_slot se)) (le_ix el) (clr_nx sl))) by
(eapply (lh_slots_write2 asegs m2 mF tbl svs _ (le_ix e) (del_slot se) (le_ix el) (clr_nx sl));
[exact SL2 | exact Hix | exact Hixl | exact (not_eq_sym NEl) | exact MU | exact WM | | exact C' | exact Cl'];
intros i NE1 NE2 Hi; unfold ivs_miss_slot; rewrite <- Hlen in Hbhi, SEP;
repeat (apply Forall_cons; [cbn [fst snd]; unfold ent_addr;
first [ clear - Hi SEP; lia | clear - NE1 HB; lia | clear - NE2 HBl; lia | clear - Hi Hbhi LO; lia ] |]); apply Forall_nil).
all: try replace (Z.of_nat (length es0) + 1 + -1) with (Z.of_nat (length es0)) in HDR by lia.
1: assert (OPENF : lh_open asegs A4F mF t tbl size [] (upd svs (le_ix e) (del_slot se))).
1:{ split; [| split; [exact SLF | split; [exact (lh_link_unsnoc_nil tbl es0 e svs se LINK Ese E0) | split; [constructor | split; [exact Hsz | split; [cbn; lia | rewrite upd_length; exact Hlen]]]]]].
unfold lh_hdrf. rewrite E0 in HDR. exact HDR. }
2,3: assert (OPENF : lh_open asegs A4F mF t tbl size es0 (upd (upd svs (le_ix e) (del_slot se)) (le_ix el) (clr_nx sl))).
2:{ split; [| split; [exact SLF | split; [exact (lh_link_unsnoc_cons tbl es0 e svs se LINK Ese es1 el sl E0 Esl) | split; [exact KEYSF | split; [exact Hsz | split; [lia | rewrite !upd_length; exact Hlen]]]]]].
unfold lh_hdrf. rewrite hd_of_nth, Ex0. replace (tl_of tbl es0) with (ent_addr tbl (le_ix el)) by (rewrite E0; symmetry; apply tl_of_app). rewrite <- EBl. exact HDR. }
3:{ split; [| split; [exact SLF | split; [exact (lh_link_unsnoc_cons tbl es0 e svs se LINK Ese es1 el sl E0 Esl) | split; [exact KEYSF | split; [exact Hsz | split; [lia | rewrite !upd_length; exact Hlen]]]]]].
unfold lh_hdrf. rewrite hd_of_nth, Ex0. replace (tl_of tbl es0) with (ent_addr tbl (le_ix el)) by (rewrite E0; symmetry; apply tl_of_app). rewrite <- EBl. exact HDR. }

1: rewrite E0, firstn_nil in KX; rewrite E0 in HPF.
2: rewrite firstn_all2 in KX by lia.
1,2: evt_done5; eapply KX; first [exact HPF | exact OPENF | exact HPRF | eapply model_vm_only_trans; [exact VM0 | exact VM2] | unfold del_frameA; eassumption | idtac].
all: try (unfold A_ERRNO; eassumption).
all: try (solve [unfold del_budA, lh_delete_costB in *; cbn [bB bD charge] in *; split; lia]).

all: try (replace (Z_to_bv 64 Bl) with (Z_to_bv 64 (ent_addr tbl (le_ix el))) by (rewrite EBl; reflexivity)).
all: try (rewrite E0, firstn_snoc_le in KX by lia).
all: try (rewrite E0 in HPF, OPENF).
all: evt_done5.
all: eapply (IH es1 el _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mF md2 A2);
first [exact HPF | exact OPENF | exact HPRF | exact KX | exact LO | exact SPA | exact HT | idtac].
+ lia.
+ lia.
+ rewrite <- E0. rewrite nth_error_app1 in Hef by lia. exact Hef.
+ intros j x Hj Hx. apply (VZ j x Hj). rewrite <- E0 in Hx.
rewrite nth_error_app1 by (apply (proj1 (nth_error_Some es0 j)); rewrite Hx; discriminate). exact Hx.
+ eassumption.
+ lia.
+ unfold del_frameA. eassumption.
+ unfold A_ERRNO. eassumption.
+ eapply model_vm_only_trans; [exact VM0 | exact VM2].
+ unfold del_budA, lh_delete_costB in *. cbn [bB bD charge] in *. rewrite E0, length_app in BUD. cbn [length] in BUD. split; lia.
Qed.

Lemma del_exit_okA : forall (esf : list lent),
bv_unsigned rac mod 2 = 0 -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -144 ->
(forall (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (svsf : list slotv)
(t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
HEAPAx A (lh_blocks t tbl size esf ++ LB) LM FRS B m md -> lh_open asegs A4F m t tbl size esf svsf ->
stk asegs m lo (bv_unsigned sp) -> rw_cells asegs m A_ERRNO [C4 errv] ->
model_vm_only (cfg_model md0) (cfg_model md) -> heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m -> del_budA B 0 ->
AJ5 A4L HIx A T md
(MS (mkR rac sp gp (Z_to_bv 64 A_TP) t0 t1 t2 s0c s1c (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2c s3c s4c s5c s6c s7c s8c s9c s10c s11c t3 t4 t5 t6)
F (ret_pc rac) fc None m (seg_rom asegs))) ->
del_exitA esf.
Proof.
intros esf RAC LO LOS K. unfold del_exitA. intros until svsf; intros HP OPEN ST FR ERR VM0 HPR BUD.
unfold del_frameA in FR. unfold_consts. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [] m) as MU.
unfold dl_regsA. a4l. reenterA asegs A4L HIx asegs_wx HP.
step. do 13 step. step.
release_frame FR ST (bv_unsigned sp). step.
evt_done5.
eapply K; [exact HP | exact OPEN | exact ST | exact ERR | exact VM0 | exact HPR | exact BUD].
Qed.
End DelLoopA.

Lemma lh_delete_tail_A_cps : lh_delete_tail_A_stmt HIx.
Proof.
unfold lh_delete_tail_A_stmt. intros until ef. intros HP OPEN Hef VZ ST LO LOS SPA HT ERR TP RA A0 A1 COST K.
pose proof OPEN as (HDR & SL & LINK & KEYS & Hsz & Hcnt & Hlen). unfold lh_hdr, lh_hdrf in HDR.
destruct (snoc_inv es) as [Enil | (es0 & e & E0)]; [rewrite Enil in Hef; destruct jf; discriminate|].
pose proof (proj1 (nth_error_Some es jf) ltac:(rewrite Hef; discriminate)) as Hjf. rewrite E0, length_app in Hjf. cbn in Hjf.
replace (tl_of tbl es) with (ent_addr tbl (le_ix e)) in HDR by (rewrite E0, tl_of_app; reflexivity).
remember (hd_of tbl es) as HDv eqn:EHD.
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR.
unfold_consts. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
destruct (lh_heap_factsA HIx _ _ _ _ _ _ _ _ _ _ _ HP) as ((Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & SEP & KF).
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Htimg, Hbimg. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hbhi, KF.
assert (BELOW : lh_below lo t tbl size es).
{ split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros x Hx. destruct (KF x Hx). lia. }
assert (INt : In (t, 56) (lh_blocks t tbl size es ++ LB)) by (left; reflexivity).
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
shadow_inA HP INt SHt.
a4l.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)] m) as MU.
subst a0 a1 tp. unfold lh_delete_tail_A_entry. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 144%nat ST.
do 14 step.
do 3 step.
step.
step. step. sh_norm. rewrite (div8_add t 16) by lia. change (16 / 8) with 2.
step. rewrite ?zxb_zero. step. if_false.
step. step.
step. step. step. step.
step. sh_norm. rewrite (div8_add t 24) by lia. change (24 / 8) with 3.
step. sh_norm. rewrite (div8_add t 4) by lia. change (4 / 8) with 0.
step. rewrite ?(unsigned_lit (t + 4)) by lia.
replace (Z.land (t + 4) 7) with 4 by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2 ^ 3) with 8; Z.div_mod_to_equations; lia).
step.
step. sh_norm. rewrite (div8_add t 32) by lia. change (32 / 8) with 4.
step. step.
step.
step.
stepz.
step.
step.
step. sh_norm. rewrite (div8_add t 8) by lia. change (8 / 8) with 1. step.
replace (t / 8 + 0) with (t / 8) in * by lia.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (OPEN1 : lh_open asegs A4F mx t tbl size es svs) by
(eapply (lh_open_frame asegs A4F _ m mx t tbl size es svs _ lo); [exact OPEN | exact BELOW | exact MU | exact WM | apply Forall_cons; [cbn; lia | apply Forall_nil]]);
assert (HPR1 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mx) by
(eapply (lh_writes_presA A t tbl size es LB LM FRS B m md mx); [exact HP | exact MU | exact WM | apply Forall_cons; [cbn; left; clia | apply Forall_nil] | clia]);
rename mx into m1
end.
hp_nowR HP HP1.
rewrite E0 in HP1, OPEN1, Hef, VZ, COST.
unfold lh_delete_tail_A_post in K. rewrite E0, (firstn_snoc_le _ es0 e jf) in K by lia.
evt_done5.
eapply lh_del_loopA with (m0 := m) (md0 := md) (B0 := B) (ES := es0 ++ [e]) (d := (length es0 - jf)%nat) (es0 := es0) (e := e) (svs := svs)
(LB := LB) (LM := LM) (FRS := FRS) (lo := lo) (tbl := tbl) (size := size) (jf := jf) (rac := ra) (errv := errv) (T := T);
first [exact COST | reflexivity | exact Hef | exact HP1 | exact OPEN1 | exact VZ | apply model_vm_only_refl | exact HPR1 | exact SPA | exact HT | idtac].
- lia.
- exact ST.
- clia.
- lia.
- unfold del_frameA. eassumption.
- unfold A_ERRNO in *. eassumption.
- unfold del_budA, lh_delete_costB. rewrite length_app. cbn [length]. split; lia.
- apply del_exit_okA; [exact RA | clia | lia |].
intros m' md' A' B' svsf u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 HPf OPENf STf ERRf VMf HPRf BUDf.
apply K. exists m', svsf, B'.
split; [unfold ret_state; do 14 eexists; reflexivity|].
split; [exact VMf|]. split; [exact STf|]. split; [exact HPRf|]. split; [exact ERRf|]. split; [exact OPENf|].
unfold del_budA, lh_delete_costB in *. rewrite ?length_app in *. cbn [length] in *.
split; [lia|]. split; [lia|]. exact HPf.
Qed.
End ALhDelete.
End RC__1.
