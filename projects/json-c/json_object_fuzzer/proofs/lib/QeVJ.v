(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply Q5Rg QRjH QHnV QCcH QfLs Q0Ek QjDH QmZZ Qsw7 QJjn QKQo Q8tj QSL3 QeL5 Q6WR QrPc QeuE Q7UD Qhd4 Qwm6 QlKV QsKa Q30W QkXq Qiiq Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn QKQo Q8tj.
Import QSL3. Import QeL5.
Import Q6WR Q6WR.Mq0 QrPc. Import QeuE.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QsKa.Mq5 Q30W.Mq3 QlKV.Mq3 QkXq.Mq3 Qiiq.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section DescA.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Variables (sp gp : word) (lo : Z) (errv : word) (LM : list blk) (FRS : list frame).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp + -112 - 4352.
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HT : bv_unsigned sp <= hiA_top A4L HIx.
Hypothesis DEL : lh_delete_tail_A_stmt HIx.

Notation SPR := (Z_to_bv 64 (bv_unsigned sp + -112)).
Notation TP := (Z_to_bv 64 6434400).
Notation SBR := (Z_to_bv 64 2147450880).
Notation CM1 := (Z_to_bv 64 18446744073709551615).
Notation ERRNO := (6434400 - 164).
Notation NEXT := (next_postA HIx sp gp lo errv LM FRS).
Notation head_stmt' := (head_stmtA HIx sp gp lo errv LM FRS).
Notation zhead := (zhead).

Lemma descend_tailA : forall (isobjc isobjp : bool) (ck kids : list (option jshape))
(x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x25 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (LB XBS2 bs : list blk) (x q v : Z) (T : TSet),
head_stmt' isobjc ck -> head_stmt' isobjp kids ->
HEAPAx A (bs ++ XBS2 ++ LB) LM FRS B m md ->
zhead isobjc m v x ck bs -> zhead isobjp m x q kids XBS2 ->
stk asegs m lo (bv_unsigned sp + -112) -> rw_cells asegs m ERRNO [C4 errv] ->
512 * (Z.of_nat (length bs) + Z.of_nat (length XBS2)) <= bB B ->
(forall ms' md' A', NEXT q F1 fc1 m md LB B (512 * (Z.of_nat (length bs) + Z.of_nat (length XBS2))) ms' md' A' -> AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR x1 SPR gp TP t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 v) x19 x20 x21 x22 SBR (Z_to_bv 64 4) x25 (Z_to_bv 64 5) CM1 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x9a808) fc1 None m (seg_rom asegs)).
Proof.
intros until T. intros HC HK HP ZC ZP ST ERR BB K.
unfold_consts. word_range sp SPW.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND.
destruct (zhead_hdr isobjc m v x ck bs ZC (nodup_app_l' _ _ (nodup_app_l' _ _ ND))) as (pbc & cfc & INv & _ & _).
assert (INv2 : In (v, 48) ((bs ++ XBS2 ++ LB) ++ LM)) by (apply in_or_app; left; apply in_or_app; left; exact INv).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ v 48 HP INv2) as (_ & _ & Hvlo & Hvhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hvhi.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [] m) as MU.
reenterA asegs A4L HIx asegs_wx HP.
step. step. if_falsex.
evt_done5.
eapply HC; [exact HP | exact ZC | exact ST | exact ERR | lia |].
intros ms5 md5 A5 (m5 & F5 & fc5 & B5 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w18 & w19 & w20 & w21 & w22 & w23 & -> & FS5 & FRM5 & VM5 & HP5 & ST5 & HPR5 & ERR5 & HB5 & HD5).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP5) as MI5.
assert (INx : In (x, 48) (XBS2 ++ LB)).
{ destruct (zhead_hdr isobjp m x q kids XBS2 ZP (nodup_app_l' _ _ (nodup_app_r' _ _ (nodup_app_l' _ _ ND)))) as (pbp & cfp & INx & _ & _).
apply in_or_app; left; exact INx. }
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ x 48 HP5 ltac:(apply in_or_app; left; exact INx)) as (_ & _ & Hxlo & Hxhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hxhi.
clear MU WM MI. pose proof (wmono_refl asegs m5) as WM. pose proof (munch_refl [] m5) as MU.
reenterA asegs A4L HIx asegs_wx HP5.
step. step. if_falsex.
evt_done5.
eapply HK; [exact HP5 | | exact ST5 | exact ERR5 | lia |].
{ eapply (zhead_agree isobjp (XBS2 ++ LB)); [exact ZP | | intros b Hb; apply in_or_app; left; exact Hb].
eapply (agree_of_heap_pres asegs A4H); [exact HPR5 | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]. }
intros ms' md' A' NP. apply K. eapply next_postA_w; [exact FS5 | exact FRM5 | exact VM5 | | exact HB5 | exact HD5 | exact NP | lia].
eapply heap_pres_weaken; [exact HPR5 | lia | intros b Hb; apply in_or_app; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb]].
Qed.

Ltac shadow48 HP a Hin SH :=
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ a 48 HP Hin) as SH;
unfold shad in SH; apply shadow_ro_cells in SH;
let cs := eval cbv in (shadow_cells 48) in change (shadow_cells 48) with cs in SH.

Lemma descend_objA : forall c kids,
desc_stmtA HIx sp gp lo errv LM FRS c -> head_stmt' true kids ->
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x20 x21 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (LB XBS1 bs : list blk) (x q v : Z) (T : TSet)
(nz : nat) (t tbl size : Z) (es2 : list lent) (svs2 : list slotv) (e2 : lent),
HEAPAx A (bs ++ XBS1 ++ LB) LM FRS B m md ->
zomb asegs A4F c m v bs ->
zobj asegs A4F m x q kids (S nz) t tbl size es2 svs2 XBS1 -> nth_error es2 (length kids) = Some e2 ->
stk asegs m lo (bv_unsigned sp + -112) -> rw_cells asegs m ERRNO [C4 errv] ->
512 * (Z.of_nat (length bs) + Z.of_nat (length XBS1)) <= bB B ->
(forall ms' md' A', NEXT q F1 fc1 m md LB B (512 * (Z.of_nat (length bs) + Z.of_nat (length XBS1))) ms' md' A' -> AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR x1 SPR gp TP t0 t1 t2 (Z_to_bv 64 x) (Z_to_bv 64 (x + 40)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 v) (Z_to_bv 64 (ent_addr tbl (le_ix e2))) x20 x21
(Z_to_bv 64 (x / 8 + 2147450885)) SBR (Z_to_bv 64 4) (Z_to_bv 64 (x / 8 + 2147450880)) (Z_to_bv 64 5) CM1 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x9a9fc) fc1 None m (seg_rom asegs)).
Proof.
intros c kids KD HK. intros until e2. intros HP ZC Z Hes2 ST ERR BB K.
unfold_consts. word_range sp SPW.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
destruct Z as (pb & PBS & KBS & esk & esz & Ees2 & Lz & Fz & EX1 & OPB & HDR & OPEN & OK).
pose proof (okids_len _ _ _ _ _ _ OK) as [L _]. rewrite length_map in L.
assert (VZ : forall j y, (length kids <= j)%nat -> nth_error es2 j = Some y -> le_v y = 0).
{ intros j y Hj Hy. rewrite Ees2, nth_error_app2 in Hy by lia. exact (proj1 (Forall_forall _ _) Fz y (nth_error_In _ _ Hy)). }
destruct (zomb_zhead HIx sp gp lo errv LM FRS c m v bs ZC KD) as (isobjc & ck & ZCH & HC). clear ZC KD.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND0. pose proof (nodup_app_l' _ _ ND0) as ND.
destruct (zhead_hdr isobjc m v 0 ck bs ZCH (nodup_app_l' _ _ ND)) as (pbc & cfc & INv & HDRC & CLOSEC).
assert (INv' : In (v, 48) (bs ++ XBS1 ++ LB)) by in_sub INv.
assert (INx : In (x, 48) (bs ++ XBS1 ++ LB)) by (rewrite EX1; in_elem).
assert (INv2 : In (v, 48) ((bs ++ XBS1 ++ LB) ++ LM)) by (apply in_or_app; left; exact INv').
assert (INx2 : In (x, 48) ((bs ++ XBS1 ++ LB) ++ LM)) by (apply in_or_app; left; exact INx).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ v 48 HP INv2) as (_ & Hval & Hvlo & Hvhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ v 48 HP INv2) as Hvimg.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ x 48 HP INx2) as (_ & Hxal & Hxlo & Hxhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ x 48 HP INx2) as Hximg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hvhi, Hxhi.
assert (NVX : forall k, ~ In (v, k) (XBS1 ++ LB)) by (intros k; exact (nodup_prefix_suffix bs (XBS1 ++ LB) v 48 k ND INv)).
assert (Hxv : x <> v) by (intros ->; apply (NVX 48); rewrite EX1; in_elem).
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ x 48 v 48 HP INx2 INv2 Hxv) as Dxv.
assert (HPl : HEAPAx A (lh_blocks t tbl size es2 ++ ((x, 48) :: concat KBS ++ PBS ++ bs ++ LB)) LM FRS B m md).
{ eapply (heapA_perm A4L HIx); [exact HP | rewrite EX1; hperm | apply Permutation_refl | apply Permutation_refl]. }
unfold lh_blocks in HPl. cbn [app] in HPl.
blk_factsA A4L HIx HPl t 56 Htal Htlo Hthi Htimg.
blk_factsA A4L HIx HPl tbl (40 * size) Hbal Hblo Hbhi Hbimg.
clear HPl.
shadow48 HP v INv' SHv.
shadow48 HP x INx SHx.

pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ v 48 0 v 48 HP INv' ltac:(lia) INv2) as SEPv0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ v 48 5 v 48 HP INv' ltac:(cbn; lia) INv2) as SEPv5.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ x 48 0 v 48 HP INx ltac:(lia) INv2) as SEPx0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ x 48 5 v 48 HP INx ltac:(cbn; lia) INv2) as SEPx5.
a4l.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(v + 24, v + 40)] m) as MU.
unfold jhdr_cells in HDRC. cbn [app] in HDRC. unfold jhdr_cells in HDR. cbn [app fn_obj_to_json_string A4F] in HDR.
reenterA asegs A4L HIx asegs_wx HP.
step. asan_chkA.
step.
step. asan_chkA.
stepz.
step. step. if_false. rewrite ?sxb_zero, ?zxb_zero.
step. step. if_false. rewrite ?sxb_zero, ?zxb_zero.
step. norm_w32. step. step. if_false.
step. step.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
assert (HP1 : HEAPAx A (bs ++ XBS1 ++ LB) LM FRS B m1 md) by heap_nowA A4L HIx HP MU WM MI.
assert (AGV : agree_on asegs (others v (bs ++ XBS1 ++ LB)) m m1).
{ eapply (agree_others_gen asegs); [exact MU | exact WM |]. intros a k Hin Hne.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HP ltac:(apply in_or_app; left; exact Hin)) as (Hk & _ & _ & Hahi & _).
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ v 48 a k HP INv2 ltac:(apply in_or_app; left; exact Hin) ltac:(congruence)) as D.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hahi. cbn. lia. }
assert (AGX : agree_on asegs (XBS1 ++ LB) m m1).
{ eapply agree_on_incl; [exact AGV|]. intros [ba bk] Hb. apply in_others; [in_sub Hb | intros ->; exact (NVX bk Hb)]. }
assert (HPR1 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp + -112) m m1).
{ eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp + -112)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; apply in_or_app; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; in_sub Hb | right; exact Hb] | clia |].
apply Forall_cons; [cbn [fst snd] | apply Forall_nil]. right; left. exists v, 48.
split; [exact INv2|]. split; [| lia]. intros Hk. apply (NVX 48). apply in_or_app. right. apply in_app_or in Hk. destruct Hk as [Hk|Hk]; [exact Hk|].
apply in_app_or in Hk. destruct Hk as [Hk|Hk]; [| exfalso; exact (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP INv2 Hk)].
exfalso. exact (nodup_prefix_suffix (bs ++ XBS1 ++ LB) LM v 48 48 ND0 INv' Hk). }
assert (ZCH1 : zhead isobjc m1 v x ck bs).
{ apply (CLOSEC m1 x); [unfold jhdr_cells; cbn [app]; assumption |].
eapply agree_on_incl; [exact AGV|]. intros [ba bk] Hb. apply in_others_iff in Hb as [Hb Hne]. apply in_others; [in_sub Hb | exact Hne]. }
assert (OPEN1 : lh_open asegs A4F m1 t tbl size es2 svs2).
{ eapply (lh_open_agree asegs A4F); [exact OPEN | exact AGX | intros b Hb; rewrite EX1; in_sub Hb]. }
clear CLOSEC HDRC SHv SHx SEPv0 SEPv5 SEPx0 SEPx5.
evt_done5.
pose proof DEL as DELx. unfold lh_delete_tail_A_stmt in DELx.
eapply DELx with (LB := (x, 48) :: concat KBS ++ PBS ++ bs ++ LB) (es := es2) (svs := svs2) (jf := length kids) (ef := e2) (lo := lo);
[ eapply (heapA_perm A4L HIx); [exact HP1 | rewrite EX1; hperm | apply Permutation_refl | apply Permutation_refl] | exact OPEN1 | exact Hes2 | exact VZ | .. ];
a4l_goal; rewrite ?unsigned_lit by lia; try first [exact ST | reflexivity | lia].
all: try (replace (bv_unsigned sp + -112) with (bv_unsigned sp - 112) by lia; rewrite Zminus_mod, SPA; reflexivity).
all: try exact ERR. all: try assumption.
all: try (clear K DELx; unfold lh_delete_costB; rewrite EX1 in BB; unfold lh_blocks in BB; cbn [length app] in BB;
rewrite ?length_app, ?length_map in BB; cbn [length] in BB; rewrite ?length_app in BB;
rewrite Ees2, length_app, Lz; rewrite Ees2, ?length_app, Lz in BB; unfold blk in *; lia).
intros ms4 md4 A4 (m4 & svs4 & B4 & RS4 & VM4 & ST4 & HPR4 & ERR4 & OPEN4 & BB4 & BD4 & HP4). open_ret RS4. a4l.
rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in ST4 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in HPR4 by lia.
replace (firstn (length kids) es2) with esk in OPEN4, HP4 by (rewrite Ees2, <- L; symmetry; apply firstn_app_len).
match goal with H : rw_cells _ m1 x _ |- _ => rename H into HDR1 end.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in HDR1; [| eapply client_range_block; [apply in_or_app; left; left; reflexivity | lia | cbn; lia]].
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI4.
clear MU WM. pose proof (wmono_refl asegs m4) as WM. pose proof (munch_refl [] m4) as MU.
reenterA asegs A4L HIx asegs_wx HP4. step.
evt_done5.
eapply (descend_tailA isobjc true ck kids) with (XBS2 := ((x, 48) :: lh_blocks t tbl size esk ++ concat KBS) ++ PBS) (bs := bs) (LB := LB) (q := q);
[exact HC | exact HK | eapply (heapA_perm A4L HIx); [exact HP4 | hperm | apply Permutation_refl | apply Permutation_refl] | | | exact ST4 | exact ERR4 | |].
- eapply (zhead_agree isobjc); [exact ZCH1 | eapply (agree_of_heap_pres asegs A4H); [exact HPR4 | reflexivity | intros b Hb; exact Hb] | intros b Hb; in_sub Hb].
- exists t, tbl, size, esk, svs4. exists pb, PBS, KBS, esk, (@nil lent).
split; [rewrite app_nil_r; reflexivity|]. split; [reflexivity|]. split; [apply Forall_nil|]. split; [reflexivity|].
split; [| split; [unfold jhdr_cells; cbn [app fn_obj_to_json_string A4F]; exact HDR1 | split; [exact OPEN4|]]].
+ eapply opt_pbuf_agree; [exact OPB | | apply incl_refl]. eapply agree_on_trans.
* eapply agree_on_incl; [exact AGX | intros b Hb; rewrite EX1; in_sub Hb].
* eapply (agree_of_heap_pres asegs A4H); [exact HPR4 | reflexivity | intros b Hb; in_sub Hb].
+ eapply okids_agree; [exact OK | | apply incl_refl]. eapply agree_on_trans.
* eapply agree_on_incl; [exact AGX | intros b Hb; rewrite EX1; in_sub Hb].
* eapply (agree_of_heap_pres asegs A4H); [exact HPR4 | reflexivity | intros b Hb; in_sub Hb].
- clear K DELx. unfold lh_delete_costB in BB4. rewrite EX1 in BB. unfold lh_blocks in *. cbn [length app] in *.
rewrite ?length_app, ?length_map in *. cbn [length] in *. rewrite ?length_app in *.
rewrite Ees2, ?length_app, Lz in BB4. rewrite Ees2, ?length_app, Lz in BB. unfold blk in *. lia.
- intros ms' md' A' NP. apply K. eapply next_postA_w; [apply fsaved_refl | intros Hf; exact Hf | exact VM4 | | exact BB4 | exact BD4 | exact NP |].
+ eapply heap_pres_trans; [exact HPR1 | eapply heap_pres_weaken; [exact HPR4 | lia | intros b Hb; in_sub Hb]].
+ clear K DELx. unfold lh_delete_costB. rewrite EX1. unfold lh_blocks. cbn [length app].
rewrite ?length_app, ?length_map. cbn [length]. rewrite ?length_app. rewrite Ees2, ?length_app, Lz, <- L. unfold blk. lia.
Qed.
End DescA.
End RC__1.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw Q22i Q6us QLLZ QbFI QRBl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw Q8tj.
Import QSL3. Import Q22i Q6us QLLZ.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqe Q30W.Mq6 Qiiq.Mq8.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section StoreA.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis OBL_AMEMSET : amemset_spec_A HIx.

Variables (sp gp tp : word) (s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (t tbl size k v : Z) (svs : list slotv) (ffn : Z) (lo : Z).
Variables (rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c : word).

Variables (m0 : word -> option byte) (md : config) (A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B0 : bud).
Hypothesis HP0 : HEAPAx A LB LM FRS B0 m0 md.
Hypothesis INt : In (t, 56) LB.
Hypothesis INb : In (tbl, 40 * size) LB.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp - 96 - 4096.
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HT : bv_unsigned sp <= hiA_top A4L HIx.
Notation SB0 := 2147450880.

Definition ins_frameA (m : word -> option byte) (junk8 : list byte) : Prop :=
rw_cells asegs m (bv_unsigned sp + -96) [CB 8 junk8; C8 s9c; C8 s8c; C8 s7c; C8 s6c; C8 s5c; C8 s4c; C8 s3c; C8 s2c; C8 s1c; C8 s0c; C8 rac].

Definition hdr_cellsA (sz cnt hd tl : Z) : list cell :=
[C4 (Z_to_bv 64 sz); C4 (Z_to_bv 64 cnt); C8 (Z_to_bv 64 hd); C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 tbl);
C8 (Z_to_bv 64 ffn); C8 (Z_to_bv 64 (fn_lh_char_hash A4F)); C8 (Z_to_bv 64 (fn_lh_char_equal A4F))].

Lemma heapA_nowS : forall m, munch [(t, t + 56); (tbl, tbl + 40 * size); (lo, bv_unsigned sp)] m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
HEAPAx A LB LM FRS B0 m md.
Proof.
intros m MU WM MI. eapply (heapA_client_frame A4L HIx); [exact HP0 | | exact WM | exact MI].
eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP0 MU).
apply Forall_cons; [right; left; exists t, 56; split; [apply in_or_app; left; exact INt | cbn; lia] |].
apply Forall_cons; [right; left; exists tbl, (40 * size); split; [apply in_or_app; left; exact INb | cbn; lia] |].
apply Forall_cons; [left; cbn; split; lia | apply Forall_nil].
Qed.

Ltac hp_nowS H :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
match goal with MUc : munch _ m0 mc, WMc : wmono asegs m0 mc, MIc : mem_inv asegs mc |- _ =>
pose proof (heapA_nowS mc MUc WMc MIc) as H end end.
Ltac sh_hdrS :=
let H := fresh "HPc" in
hp_nowS H;
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ t 56 H INt) as SHt; clear H;
unfold shad in SHt; apply shadow_ro_cells in SHt;
change (shadow_cells 56) with [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] in SHt;
cbn [hl_sb hl_segs hla_base A4L A4H] in SHt; unfold A_SB in SHt.

Ltac sh_slotS Bx :=
let H := fresh "HPc" in
hp_nowS H;
lazymatch goal with EBx : Bx = tbl + 40 * ?gi |- _ =>
pose proof (ent_shadowA HIx _ _ _ _ _ _ _ tbl size (Z.to_nat gi) H INb ltac:(lia) ltac:(lia)) as SHs;
unfold ent_addr in SHs; rewrite Z2Nat.id in SHs by lia;
rewrite <- EBx in SHs; cbn [hl_sb hl_segs hla_base A4L A4H] in SHs; unfold A_SB in SHs; clear H
end.

Lemma lh_store_blockA :
forall (g : Z) (sg : slotv) (cnt hd tl : Z) (ixl : nat) (sl : slotv)
(x1 x9 x20 x22 x23 x24 x25 x29 x30 x31 : word) (m : word -> option byte) (junk8 : list byte),
0 <= g < size -> In size lf_sizes -> Z.of_nat (length svs) = size -> nth_error svs (Z.to_nat g) = Some sg ->
0 <= cnt < size -> 0 <= k < 2^64 -> 0 <= v < 2^64 -> 0 <= ffn < 2^64 ->
(hd = 0 /\ tl = 0) \/ (hd <> 0 /\ tl = ent_addr tbl ixl /\ nth_error svs ixl = Some sl /\ ixl <> Z.to_nat g /\ 0 <= hd < 2^64) ->
0 <= t -> t + 56 <= lo -> 0 < tbl ->
tbl + 40 * size <= lo -> (t + 56 <= tbl \/ tbl + 40 * size <= t) -> t mod 16 = 0 -> tbl mod 16 = 0 ->
mem_inv asegs m ->
munch [(t, t + 56); (tbl, tbl + 40 * size); (lo, bv_unsigned sp)] m0 m -> wmono asegs m0 m ->
rw_cells asegs m t (hdr_cellsA size cnt hd tl) ->
lh_slots asegs m tbl svs ->
ins_frameA m junk8 -> stk asegs m lo (bv_unsigned sp + -96) ->
evt asegs (fun ms' => exists (x5 x6' x7' x11 x12 x13 x14 x15 x16 x17 x28' x29' x30' x31' : word) m',
ms' = MS (mkR rac sp gp tp x5 x6' x7' s0c s1c (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
s2c s3c s4c s5c s6c s7c s8c s9c s10 s11 x28' x29' x30' x31')
F (ret_pc rac) fc None m' (seg_rom asegs)
/\ munch [(t, t + 56); (tbl, tbl + 40 * size); (lo, bv_unsigned sp)] m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m'
/\ rw_cells asegs m' t (hdr_cellsA size (cnt + 1) (if hd =? 0 then ent_addr tbl (Z.to_nat g) else hd) (ent_addr tbl (Z.to_nat g)))
/\ lh_slots asegs m' tbl (ins_svs svs (Z.to_nat g) sg k v hd tl ixl sl tbl)
/\ stk asegs m' lo (bv_unsigned sp))
(MS (ins_regsA sp gp tp s10 s11 t tbl size k v 0 x1 (Z_to_bv 64 0) x9 (Z_to_bv 64 (tbl + g * 40)) g x20 x22 x23 x24 x25
(Z_to_bv 64 ((tbl + 40 * g) / 8 + SB0)) x29 x30 x31)
F (Z_to_bv 64 0xa4958) fc None m (seg_rom asegs)).
Proof.
intros until junk8. intros Hg Hsz Hlen Esg Hcnt Hk Hv Hffn TAIL Ht0 Ht Hb0 Hb SEP Hal16 Hbal16 MI MU WM HDR SL FR ST.
pose proof (lf_size_range size Hsz) as HSR. word_range sp SPR. unfold_consts. unfold ins_frameA in FR. unfold hdr_cellsA in HDR.
pose proof (SL _ _ Esg) as CG. unfold ent_addr, slot_cells in CG. rewrite Z2Nat.id in CG by lia.
unfold ins_regsA. replace (tbl + g * 40) with (tbl + 40 * g) by lia.
pose proof OBL_AMEMSET as OBL_unused_on_B.

remember (tbl + 40 * g) as B eqn:EB.
assert (EB8 : B mod 8 = 0) by (subst B; Z.div_mod_to_equations; lia).
destruct TAIL as [[Hhd Htl] | (Hhd & Htl & Esl & NEl & HhdR)].
-
subst hd tl.
pose proof (munch_refl [(t, t + 56); (B, B + 40)] m) as MU2. pose proof (wmono_refl asegs m) as WM2.
step. step. if_falsex.
sh_slotS B. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false. try clear SHs.
step.
step.
sh_slotS B. step. step. sh_norm. rewrite (div8_add B 8) by lia. change (8 / 8) with 1. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false. try clear SHs.
step. change (Z.land (bv_unsigned (Z_to_bv 64 0)) (bv_unsigned (Z_to_bv 64 4))) with 0.
step.
stepz.
sh_slotS B. step. step. sh_norm. rewrite (div8_add B 16) by lia. change (16 / 8) with 2. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false. try clear SHs.
step.
sh_hdrS. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false. try clear SHt.
step. norm_sx32. step. norm_w32. step. if_falsex.
sh_hdrS. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false. try clear SHt.
stepz.
step.
sh_hdrS. step. step. sh_norm. rewrite (div8_add t 8) by lia. change (8 / 8) with 1. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false. try clear SHt.
step. step. step. if_true.
sh_hdrS. step. step. sh_norm. rewrite (div8_add t 16) by lia. change (16 / 8) with 2. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false. try clear SHt.
step.
sh_hdrS. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false. try clear SHt.
step.
step.
sh_slotS B. step. step. sh_norm. rewrite (div8_add B 32) by lia. change (32 / 8) with 4. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false. try clear SHs.
stepz.
step.
sh_slotS B. step. step. sh_norm. rewrite (div8_add B 24) by lia. change (24 / 8) with 3. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false. try clear SHs.
stepz.
step. do 11 step.
lazymatch goal with H : rw_cells asegs ?mx (bv_unsigned sp + -96) _, STx : stk asegs ?mx lo _ |- _ => release_frame H STx (bv_unsigned sp) end.
step. step. subst B.
apply evt_done. do 14 eexists. eexists. split; [reflexivity|].
split; [assumption|]. split; [assumption|]. split; [assumption|].
split. { unfold hdr_cellsA. cbn [Z.eqb]. unfold ent_addr. rewrite Z2Nat.id by lia. assumption. }
split; [| assumption].
unfold ins_svs. cbn [Z.eqb]. eapply (lh_slots_write1 asegs m); [exact SL | lia | exact MU2 | exact WM2 | | ].
+ intros i NE Hi. unfold ivs_miss_slot. apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; cbn; unfold ent_addr.
* destruct SEP; [right; lia | left; nia].
* assert (Z.of_nat i + 1 <= g \/ g + 1 <= Z.of_nat i) as [L|R] by lia; [left; nia | right; nia].
+ unfold ent_addr, slot_cells, new_slot. cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv]. rewrite Z2Nat.id by lia. assumption.
-
pose proof (SL _ _ Esl) as CL. unfold ent_addr, slot_cells in CL.
pose proof (proj1 (nth_error_Some svs ixl) ltac:(rewrite Esl; discriminate)) as Hixl.
assert (NEg : Z.of_nat ixl <> g) by (intros X; apply NEl; lia).
pose proof (munch_refl [(t, t + 56); (tbl + 40 * g, tbl + 40 * g + 40); (tbl + 40 * Z.of_nat ixl, tbl + 40 * Z.of_nat ixl + 40)] m) as MU2. pose proof (wmono_refl asegs m) as WM2.
rewrite <- EB in MU2. remember (tbl + 40 * Z.of_nat ixl) as TL eqn:ETL.
assert (ETL8 : TL mod 8 = 0) by (subst TL; Z.div_mod_to_equations; lia).
assert (ETL0 : 0 < TL) by (subst TL; nia).
replace tl with TL in * by (subst tl TL; unfold ent_addr; reflexivity).
step. step. if_falsex.
sh_slotS B. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false. try clear SHs.
step.
step.
sh_slotS B. step. step. sh_norm. rewrite (div8_add B 8) by lia. change (8 / 8) with 1. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false. try clear SHs.
step. change (Z.land (bv_unsigned (Z_to_bv 64 0)) (bv_unsigned (Z_to_bv 64 4))) with 0.
step.
stepz.
sh_slotS B. step. step. sh_norm. rewrite (div8_add B 16) by lia. change (16 / 8) with 2. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false. try clear SHs.
step.
sh_hdrS. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false. try clear SHt.
step. norm_sx32. step. norm_w32. step. if_falsex.
sh_hdrS. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false. try clear SHt.
stepz.
step.
sh_hdrS. step. step. sh_norm. rewrite (div8_add t 8) by lia. change (8 / 8) with 1. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false. try clear SHt.
step. step. step. if_falsex.
sh_hdrS. step. step. sh_norm. rewrite (div8_add t 16) by lia. change (16 / 8) with 2. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false. try clear SHt.
step.
step. if_falsex.
step. rewrite (unsigned_lit TL) by lia. rewrite (ub_land7 TL ETL8). step. if_false.
step.
sh_slotS TL. step. step. sh_norm. rewrite (div8_add TL 24) by lia. change (24 / 8) with 3. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false. try clear SHs.
step.
step.
sh_slotS B. step. step. sh_norm. rewrite (div8_add B 32) by lia. change (32 / 8) with 4. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false. try clear SHs.
step.
step.
sh_slotS B. step. step. sh_norm. rewrite (div8_add B 24) by lia. change (24 / 8) with 3. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false. try clear SHs.
stepz.
sh_hdrS. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false. try clear SHt.
step.
step.
step. do 11 step.
lazymatch goal with H : rw_cells asegs ?mx (bv_unsigned sp + -96) _, STx : stk asegs ?mx lo _ |- _ => release_frame H STx (bv_unsigned sp) end.
step. step. subst B.
apply evt_done. do 14 eexists. eexists. split; [reflexivity|].
split. { eapply munch_weaken; [| eassumption]. intros x Hx. cbn in Hx |- *. subst TL. lia. }
split; [assumption|]. split; [assumption|].
split. { unfold hdr_cellsA. destruct (Z.eqb_spec hd 0); [lia|]. unfold ent_addr. rewrite Z2Nat.id by lia. assumption. }
split; [| assumption].
unfold ins_svs. destruct (Z.eqb_spec hd 0); [lia|].
eapply (lh_slots_write2 asegs m); [exact SL | lia | exact Hixl | lia | exact MU2 | exact WM2 | | | ].
+ intros i NE1 NE2 Hi. unfold ivs_miss_slot. subst TL.
apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]; cbn; unfold ent_addr.
* destruct SEP; [right; lia | left; nia].
* assert (Z.of_nat i + 1 <= g \/ g + 1 <= Z.of_nat i) as [L|R] by lia; [left; nia | right; nia].
* assert (i + 1 <= ixl \/ ixl + 1 <= i)%nat as [L|R] by lia; [left; nia | right; nia].
+ unfold ent_addr, slot_cells, new_slot. cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv]. rewrite Z2Nat.id by lia. subst TL. unfold ent_addr in *. assumption.
+ unfold ent_addr, slot_cells. cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv]. rewrite Z2Nat.id by lia. subst TL. assumption.
Qed.
End StoreA.
End RC__1.
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn QKQo Q8tj.
Import QSL3. Import QeL5.
Import Q6WR Q6WR.Mq0 QrPc. Import QeuE.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QsKa.Mqe Q30W.Mq6 QlKV.Mqd QkXq.Mq7 Qiiq.Mqb.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section DescA.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Variables (sp gp : word) (lo : Z) (errv : word) (LM : list blk) (FRS : list frame).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp + -112 - 4352.
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HT : bv_unsigned sp <= hiA_top A4L HIx.
Hypothesis DEL : lh_delete_tail_A_stmt HIx.

Notation SPR := (Z_to_bv 64 (bv_unsigned sp + -112)).
Notation TP := (Z_to_bv 64 6444320).
Notation SBR := (Z_to_bv 64 2147450880).
Notation CM1 := (Z_to_bv 64 18446744073709551615).
Notation ERRNO := (6444320 - 164).
Notation NEXT := (next_postA HIx sp gp lo errv LM FRS).
Notation spill' := (spillA sp).

Ltac spl1 mq :=
match goal with
| S : rw_cells _ mq (bv_unsigned _ + -112) [_] |- _ =>
let bs := fresh "sbs" in let S2 := fresh "SPL" in
destruct (rw_cells_forget asegs _ _ _ S) as [bs S2]; cbn [cells_size csize Nat.add] in S2; eexists; exact S2
| S : rw_cells _ ?ma (bv_unsigned _ + -112) [_], H : heap_pres A4H _ _ ?ma ?mb |- _ =>
lazymatch mb with ma => fail | _ => idtac end;
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ H) in S; [ spl1 mq | left; cbn; lia ]
| |- _ => fail 1 "spill slot: no slot hypothesis / heap_pres chain to the current memory"
end.
Ltac spl := lazymatch goal with
| |- spillA _ ?mq /\ _ => split; [spl1 mq|] | |- spillA ?mq /\ _ => split; [spl1 mq|]
| |- spillA _ ?mq => spl1 mq | |- spillA ?mq => spl1 mq | |- _ => idtac end.
Ltac hpw H := eapply heap_pres_weaken; [exact H | lia | intros b' Hb'; exact Hb'].
Notation head_stmt' := (head_stmtA HIx sp gp lo errv LM FRS).
Notation zhead := (zhead).

Lemma descend_tailA : forall (isobjc isobjp : bool) (ck kids : list (option jshape))
(x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x25 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (LB XBS2 bs : list blk) (x q v : Z) (T : TSet),
head_stmt' isobjc ck -> head_stmt' isobjp kids ->
HEAPAx A (bs ++ XBS2 ++ LB) LM FRS B m md ->
zhead isobjc m v x ck bs -> zhead isobjp m x q kids XBS2 ->
stk asegs m lo (bv_unsigned sp + -112) -> rw_cells asegs m ERRNO [C4 errv] ->
512 * (Z.of_nat (length bs) + Z.of_nat (length XBS2)) <= bB B ->
spill' m ->
(forall ms' md' A', NEXT q F1 fc1 m md LB B (512 * (Z.of_nat (length bs) + Z.of_nat (length XBS2))) ms' md' A' -> AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR x1 SPR gp TP t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 v) x19 x20 x21 x22 SBR (Z_to_bv 64 4) x25 (Z_to_bv 64 5) CM1 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x9be3c) fc1 None m (seg_rom asegs)).
Proof.
intros until T. intros HC HK HP ZC ZP ST ERR BB [sbs SPL] K.
unfold_consts. word_range sp SPW.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND.
destruct (zhead_hdr isobjc m v x ck bs ZC (nodup_app_l' _ _ (nodup_app_l' _ _ ND))) as (pbc & cfc & INv & _ & _).
assert (INv2 : In (v, 48) ((bs ++ XBS2 ++ LB) ++ LM)) by (apply in_or_app; left; apply in_or_app; left; exact INv).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ v 48 HP INv2) as (_ & _ & Hvlo & Hvhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hvhi.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [] m) as MU.
reenterA asegs A4L HIx asegs_wx HP.
bstep. bstep. if_falsex.
evt_done5.
eapply HC; [exact HP | exact ZC | exact ST | exact ERR | lia | spl |].
intros ms5 md5 A5 (m5 & F5 & fc5 & B5 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w18 & w19 & w20 & w21 & w22 & w23 & -> & FS5 & FRM5 & VM5 & HP5 & [sbsHP5x SPLHP5x] & ST5 & HPR5 & ERR5 & HB5 & HD5).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP5) as MI5.
assert (INx : In (x, 48) (XBS2 ++ LB)).
{ destruct (zhead_hdr isobjp m x q kids XBS2 ZP (nodup_app_l' _ _ (nodup_app_r' _ _ (nodup_app_l' _ _ ND)))) as (pbp & cfp & INx & _ & _).
apply in_or_app; left; exact INx. }
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ x 48 HP5 ltac:(apply in_or_app; left; exact INx)) as (_ & _ & Hxlo & Hxhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hxhi.
clear MU WM MI. pose proof (wmono_refl asegs m5) as WM. pose proof (munch_refl [] m5) as MU.
reenterA asegs A4L HIx asegs_wx HP5.
bstep. bstep. if_falsex.
evt_done5.
eapply HK; [exact HP5 | | exact ST5 | exact ERR5 | lia | spl |].
{ eapply (zhead_agree isobjp (XBS2 ++ LB)); [exact ZP | | intros b Hb; apply in_or_app; left; exact Hb].
eapply (agree_of_heap_pres asegs A4H); [exact HPR5 | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]. }
intros ms' md' A' NP. apply K. eapply next_postA_w; [exact FS5 | exact FRM5 | exact VM5 | | exact HB5 | exact HD5 | exact NP | lia].
eapply heap_pres_weaken; [exact HPR5 | lia | intros b Hb; apply in_or_app; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb]].
Qed.

Ltac shadow48 HP a Hin SH :=
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ a 48 HP Hin) as SH;
unfold shad in SH; apply shadow_ro_cells in SH;
let cs := eval cbv in (shadow_cells 48) in change (shadow_cells 48) with cs in SH.

Lemma descend_objA : forall c kids,
desc_stmtA HIx sp gp lo errv LM FRS c -> head_stmt' true kids ->
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x20 x21 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (LB XBS1 bs : list blk) (x q v : Z) (T : TSet)
(nz : nat) (t tbl size : Z) (es2 : list lent) (svs2 : list slotv) (e2 : lent),
HEAPAx A (bs ++ XBS1 ++ LB) LM FRS B m md ->
zomb asegs A4F c m v bs ->
zobj asegs A4F m x q kids (S nz) t tbl size es2 svs2 XBS1 -> nth_error es2 (length kids) = Some e2 ->
stk asegs m lo (bv_unsigned sp + -112) -> rw_cells asegs m ERRNO [C4 errv] ->
512 * (Z.of_nat (length bs) + Z.of_nat (length XBS1)) <= bB B ->
spill' m ->
(forall ms' md' A', NEXT q F1 fc1 m md LB B (512 * (Z.of_nat (length bs) + Z.of_nat (length XBS1))) ms' md' A' -> AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR x1 SPR gp TP t0 t1 t2 (Z_to_bv 64 x) (Z_to_bv 64 (x + 40)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 v) (Z_to_bv 64 (ent_addr tbl (le_ix e2))) x20 x21
(Z_to_bv 64 (x / 8 + 2147450885)) SBR (Z_to_bv 64 4) (Z_to_bv 64 (x / 8 + 2147450880)) (Z_to_bv 64 5) CM1 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x9c068) fc1 None m (seg_rom asegs)).
Proof.
intros c kids KD HK. intros until e2. intros HP ZC Z Hes2 ST ERR BB [sbs SPL] K.
unfold_consts. word_range sp SPW.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
destruct Z as (pb & PBS & KBS & esk & esz & Ees2 & Lz & Fz & EX1 & OPB & HDR & OPEN & OK).
pose proof (okids_len _ _ _ _ _ _ OK) as [L _]. rewrite length_map in L.
assert (VZ : forall j y, (length kids <= j)%nat -> nth_error es2 j = Some y -> le_v y = 0).
{ intros j y Hj Hy. rewrite Ees2, nth_error_app2 in Hy by lia. exact (proj1 (Forall_forall _ _) Fz y (nth_error_In _ _ Hy)). }
destruct (zomb_zhead HIx sp gp lo errv LM FRS c m v bs ZC KD) as (isobjc & ck & ZCH & HC). clear ZC KD.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND0. pose proof (nodup_app_l' _ _ ND0) as ND.
destruct (zhead_hdr isobjc m v 0 ck bs ZCH (nodup_app_l' _ _ ND)) as (pbc & cfc & INv & HDRC & CLOSEC).
assert (INv' : In (v, 48) (bs ++ XBS1 ++ LB)) by in_sub INv.
assert (INx : In (x, 48) (bs ++ XBS1 ++ LB)) by (rewrite EX1; in_elem).
assert (INv2 : In (v, 48) ((bs ++ XBS1 ++ LB) ++ LM)) by (apply in_or_app; left; exact INv').
assert (INx2 : In (x, 48) ((bs ++ XBS1 ++ LB) ++ LM)) by (apply in_or_app; left; exact INx).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ v 48 HP INv2) as (_ & Hval & Hvlo & Hvhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ v 48 HP INv2) as Hvimg.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ x 48 HP INx2) as (_ & Hxal & Hxlo & Hxhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ x 48 HP INx2) as Hximg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hvhi, Hxhi.
assert (NVX : forall k, ~ In (v, k) (XBS1 ++ LB)) by (intros k; exact (nodup_prefix_suffix bs (XBS1 ++ LB) v 48 k ND INv)).
assert (Hxv : x <> v) by (intros ->; apply (NVX 48); rewrite EX1; in_elem).
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ x 48 v 48 HP INx2 INv2 Hxv) as Dxv.
assert (HPl : HEAPAx A (lh_blocks t tbl size es2 ++ ((x, 48) :: concat KBS ++ PBS ++ bs ++ LB)) LM FRS B m md).
{ eapply (heapA_perm A4L HIx); [exact HP | rewrite EX1; hperm | apply Permutation_refl | apply Permutation_refl]. }
unfold lh_blocks in HPl. cbn [app] in HPl.
blk_factsA A4L HIx HPl t 56 Htal Htlo Hthi Htimg.
blk_factsA A4L HIx HPl tbl (40 * size) Hbal Hblo Hbhi Hbimg.
clear HPl.
shadow48 HP v INv' SHv.
shadow48 HP x INx SHx.

pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ v 48 0 v 48 HP INv' ltac:(lia) INv2) as SEPv0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ v 48 5 v 48 HP INv' ltac:(cbn; lia) INv2) as SEPv5.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ x 48 0 v 48 HP INx ltac:(lia) INv2) as SEPx0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ x 48 5 v 48 HP INx ltac:(cbn; lia) INv2) as SEPx5.
a4l.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(v + 24, v + 40)] m) as MU.
unfold jhdr_cells in HDRC. cbn [app] in HDRC. unfold jhdr_cells in HDR. cbn [app fn_obj_to_json_string A4F] in HDR.
reenterA asegs A4L HIx asegs_wx HP.
bstep. asan_chkA.
bstep.
bstep. asan_chkA.
bstepz.
bstep. bstep. if_false. rewrite ?sxb_zero, ?zxb_zero.
bstep. bstep. if_false. rewrite ?sxb_zero, ?zxb_zero.
bstep. norm_w32. bstep. bstep. if_false.
bstep. bstep.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
assert (HP1 : HEAPAx A (bs ++ XBS1 ++ LB) LM FRS B m1 md) by heap_nowA A4L HIx HP MU WM MI.
assert (AGV : agree_on asegs (others v (bs ++ XBS1 ++ LB)) m m1).
{ eapply (agree_others_gen asegs); [exact MU | exact WM |]. intros a k Hin Hne.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HP ltac:(apply in_or_app; left; exact Hin)) as (Hk & _ & _ & Hahi & _).
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ v 48 a k HP INv2 ltac:(apply in_or_app; left; exact Hin) ltac:(congruence)) as D.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hahi. cbn. lia. }
assert (AGX : agree_on asegs (XBS1 ++ LB) m m1).
{ eapply agree_on_incl; [exact AGV|]. intros [ba bk] Hb. apply in_others; [in_sub Hb | intros ->; exact (NVX bk Hb)]. }
assert (HPR1 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp + -112) m m1).
{ eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp + -112)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; apply in_or_app; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; in_sub Hb | right; exact Hb] | clia |].
apply Forall_cons; [cbn [fst snd] | apply Forall_nil]. right; left. exists v, 48.
split; [exact INv2|]. split; [| lia]. intros Hk. apply (NVX 48). apply in_or_app. right. apply in_app_or in Hk. destruct Hk as [Hk|Hk]; [exact Hk|].
apply in_app_or in Hk. destruct Hk as [Hk|Hk]; [| exfalso; exact (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP INv2 Hk)].
exfalso. exact (nodup_prefix_suffix (bs ++ XBS1 ++ LB) LM v 48 48 ND0 INv' Hk). }
assert (ZCH1 : zhead isobjc m1 v x ck bs).
{ apply (CLOSEC m1 x); [unfold jhdr_cells; cbn [app]; assumption |].
eapply agree_on_incl; [exact AGV|]. intros [ba bk] Hb. apply in_others_iff in Hb as [Hb Hne]. apply in_others; [in_sub Hb | exact Hne]. }
assert (OPEN1 : lh_open asegs A4F m1 t tbl size es2 svs2).
{ eapply (lh_open_agree asegs A4F); [exact OPEN | exact AGX | intros b Hb; rewrite EX1; in_sub Hb]. }
clear CLOSEC HDRC SHv SHx SEPv0 SEPv5 SEPx0 SEPx5.
evt_done5.
pose proof DEL as DELx. unfold lh_delete_tail_A_stmt in DELx.
eapply DELx with (LB := (x, 48) :: concat KBS ++ PBS ++ bs ++ LB) (es := es2) (svs := svs2) (jf := length kids) (ef := e2) (lo := lo);
[ eapply (heapA_perm A4L HIx); [exact HP1 | rewrite EX1; hperm | apply Permutation_refl | apply Permutation_refl] | exact OPEN1 | exact Hes2 | exact VZ | .. ];
a4l_goal; rewrite ?unsigned_lit by lia; try first [exact ST | reflexivity | lia].
all: try (replace (bv_unsigned sp + -112) with (bv_unsigned sp - 112) by lia; rewrite Zminus_mod, SPA; reflexivity).
all: try exact ERR. all: try assumption.
all: try (clear K DELx; unfold lh_delete_costB; rewrite EX1 in BB; unfold lh_blocks in BB; cbn [length app] in BB;
rewrite ?length_app, ?length_map in BB; cbn [length] in BB; rewrite ?length_app in BB;
rewrite Ees2, length_app, Lz; rewrite Ees2, ?length_app, Lz in BB; unfold blk in *; lia).
intros ms4 md4 A4 (m4 & svs4 & B4 & RS4 & VM4 & ST4 & HPR4 & ERR4 & OPEN4 & BB4 & BD4 & HP4). open_ret RS4. a4l.
rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in ST4 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in HPR4 by lia.
replace (firstn (length kids) es2) with esk in OPEN4, HP4 by (rewrite Ees2, <- L; symmetry; apply firstn_app_len).
match goal with H : rw_cells _ m1 x _ |- _ => rename H into HDR1 end.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in HDR1; [| eapply client_range_block; [apply in_or_app; left; left; reflexivity | lia | cbn; lia]].
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI4.
clear MU WM. pose proof (wmono_refl asegs m4) as WM. pose proof (munch_refl [] m4) as MU.
reenterA asegs A4L HIx asegs_wx HP4. bstep.
evt_done5.
eapply (descend_tailA isobjc true ck kids) with (XBS2 := ((x, 48) :: lh_blocks t tbl size esk ++ concat KBS) ++ PBS) (bs := bs) (LB := LB) (q := q);
[exact HC | exact HK | eapply (heapA_perm A4L HIx); [exact HP4 | hperm | apply Permutation_refl | apply Permutation_refl] | | | exact ST4 | exact ERR4 | | spl |].
- eapply (zhead_agree isobjc); [exact ZCH1 | eapply (agree_of_heap_pres asegs A4H); [exact HPR4 | reflexivity | intros b Hb; exact Hb] | intros b Hb; in_sub Hb].
- exists t, tbl, size, esk, svs4. exists pb, PBS, KBS, esk, (@nil lent).
split; [rewrite app_nil_r; reflexivity|]. split; [reflexivity|]. split; [apply Forall_nil|]. split; [reflexivity|].
split; [| split; [unfold jhdr_cells; cbn [app fn_obj_to_json_string A4F]; exact HDR1 | split; [exact OPEN4|]]].
+ eapply opt_pbuf_agree; [exact OPB | | apply incl_refl]. eapply agree_on_trans.
* eapply agree_on_incl; [exact AGX | intros b Hb; rewrite EX1; in_sub Hb].
* eapply (agree_of_heap_pres asegs A4H); [exact HPR4 | reflexivity | intros b Hb; in_sub Hb].
+ eapply okids_agree; [exact OK | | apply incl_refl]. eapply agree_on_trans.
* eapply agree_on_incl; [exact AGX | intros b Hb; rewrite EX1; in_sub Hb].
* eapply (agree_of_heap_pres asegs A4H); [exact HPR4 | reflexivity | intros b Hb; in_sub Hb].
- clear K DELx. unfold lh_delete_costB in BB4. rewrite EX1 in BB. unfold lh_blocks in *. cbn [length app] in *.
rewrite ?length_app, ?length_map in *. cbn [length] in *. rewrite ?length_app in *.
rewrite Ees2, ?length_app, Lz in BB4. rewrite Ees2, ?length_app, Lz in BB. unfold blk in *. lia.
- intros ms' md' A' NP. apply K. eapply next_postA_w; [apply fsaved_refl | intros Hf; exact Hf | exact VM4 | | exact BB4 | exact BD4 | exact NP |].
+ eapply heap_pres_trans; [hpw HPR1 | eapply heap_pres_weaken; [exact HPR4 | lia | intros b Hb; in_sub Hb]].
+ clear K DELx. unfold lh_delete_costB. rewrite EX1. unfold lh_blocks. cbn [length app].
rewrite ?length_app, ?length_map. cbn [length]. rewrite ?length_app. rewrite Ees2, ?length_app, Lz, <- L. unfold blk. lia.
Qed.
End DescA.
End RC__1.
End Mq2.

From Stdlib Require Import ZArith NArith List Lia Bool.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q22i.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q22i. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6us.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6us. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLLZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLLZ.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7UD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7UD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q30W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q30W.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qiiq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qiiq.Mq1.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section StoreA.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis OBL_AMEMSET : amemset_spec_A HIx.

Variables (sp gp tp : word) (s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (t tbl size k v : Z) (svs : list slotv) (ffn : Z) (lo : Z).
Variables (rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c : word).

Variables (m0 : word -> option byte) (md : config) (A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B0 : bud).
Hypothesis HP0 : HEAPAx A LB LM FRS B0 m0 md.
Hypothesis INt : In (t, 56) LB.
Hypothesis INb : In (tbl, 40 * size) LB.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp - 96 - 4096.
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HT : bv_unsigned sp <= hiA_top A4L HIx.

Definition ins_frameA (m : word -> option byte) (junk8 : list byte) : Prop :=
rw_cells asegs m (bv_unsigned sp + -96) [CB 8 junk8; C8 s9c; C8 s8c; C8 s7c; C8 s6c; C8 s5c; C8 s4c; C8 s3c; C8 s2c; C8 s1c; C8 s0c; C8 rac].

Definition hdr_cellsA (sz cnt hd tl : Z) : list cell :=
[C4 (Z_to_bv 64 sz); C4 (Z_to_bv 64 cnt); C8 (Z_to_bv 64 hd); C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 tbl);
C8 (Z_to_bv 64 ffn); C8 (Z_to_bv 64 (fn_lh_char_hash A4F)); C8 (Z_to_bv 64 (fn_lh_char_equal A4F))].

Lemma heapA_nowS : forall m, munch [(t, t + 56); (tbl, tbl + 40 * size); (lo, bv_unsigned sp)] m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
HEAPAx A LB LM FRS B0 m md.
Proof.
intros m MU WM MI. eapply (heapA_client_frame A4L HIx); [exact HP0 | | exact WM | exact MI].
eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP0 MU).
apply Forall_cons; [right; left; exists t, 56; split; [apply in_or_app; left; exact INt | cbn; lia] |].
apply Forall_cons; [right; left; exists tbl, (40 * size); split; [apply in_or_app; left; exact INb | cbn; lia] |].
apply Forall_cons; [left; cbn; split; lia | apply Forall_nil].
Qed.

Ltac hp_nowS H :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
match goal with MUc : munch _ m0 mc, WMc : wmono asegs m0 mc, MIc : mem_inv asegs mc |- _ =>
pose proof (heapA_nowS mc MUc WMc MIc) as H end end.
Ltac sh_hdrS :=
let H := fresh "HPc" in
hp_nowS H;
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ t 56 H INt) as SHt; clear H;
unfold shad in SHt; apply shadow_ro_cells in SHt;
change (shadow_cells 56) with [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] in SHt;
cbn [hl_sb hl_segs hla_base A4L A4H] in SHt; unfold A_SB in SHt.

Ltac sh_slotS Bx :=
let H := fresh "HPc" in
hp_nowS H;
lazymatch goal with EBx : Bx = tbl + 40 * ?gi |- _ =>
pose proof (ent_shadowA HIx _ _ _ _ _ _ _ tbl size (Z.to_nat gi) H INb ltac:(lia) ltac:(lia)) as SHs;
unfold ent_addr in SHs; rewrite Z2Nat.id in SHs by lia;
rewrite <- EBx in SHs; cbn [hl_sb hl_segs hla_base A4L A4H] in SHs; unfold A_SB in SHs; clear H
end.

Lemma lh_store_blockA :
forall (g : Z) (sg : slotv) (cnt hd tl : Z) (ixl : nat) (sl : slotv)
(x1 x6 x7 x18 x19 x23 x24 x25 x28 x29 x30 x31 : word) (a3v t0v : Z) (m : word -> option byte) (junk8 : list byte),
0 <= g < size -> In size lf_sizes -> Z.of_nat (length svs) = size -> nth_error svs (Z.to_nat g) = Some sg ->
0 <= cnt < size -> 0 <= k < 2^64 -> 0 <= v < 2^64 -> 0 <= ffn < 2^64 ->
(hd = 0 /\ tl = 0) \/ (hd <> 0 /\ tl = ent_addr tbl ixl /\ nth_error svs ixl = Some sl /\ ixl <> Z.to_nat g /\ 0 <= hd < 2^64) ->
0 <= t -> t + 56 <= lo -> 0 <= tbl -> tbl + 40 * size <= lo -> (t + 56 <= tbl \/ tbl + 40 * size <= t) -> t mod 16 = 0 -> tbl mod 16 = 0 ->
mem_inv asegs m ->
munch [(t, t + 56); (tbl, tbl + 40 * size); (lo, bv_unsigned sp)] m0 m -> wmono asegs m0 m ->
rw_cells asegs m t (hdr_cellsA size cnt hd tl) ->
lh_slots asegs m tbl svs ->
ins_frameA m junk8 -> stk asegs m lo (bv_unsigned sp + -96) ->
evt asegs (fun ms' => exists (x5 x6' x7' x11 x12 x13 x14 x15 x16 x17 x28' x29' x30' x31' : word) m',
ms' = MS (mkR rac sp gp tp x5 x6' x7' s0c s1c (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
s2c s3c s4c s5c s6c s7c s8c s9c s10 s11 x28' x29' x30' x31')
F (ret_pc rac) fc None m' (seg_rom asegs)
/\ munch [(t, t + 56); (tbl, tbl + 40 * size); (lo, bv_unsigned sp)] m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m'
/\ rw_cells asegs m' t (hdr_cellsA size (cnt + 1) (if hd =? 0 then ent_addr tbl (Z.to_nat g) else hd) (ent_addr tbl (Z.to_nat g)))
/\ lh_slots asegs m' tbl (ins_svs svs (Z.to_nat g) sg k v hd tl ixl sl tbl)
/\ stk asegs m' lo (bv_unsigned sp))
(MS (ins_regsA sp gp tp x18 x19 x23 x24 x25 s10 s11 t tbl size k v 0 x1 x6 x7 (Z_to_bv 64 (tbl + g * 40)) a3v g t0v x28 x29 x30 x31)
F (Z_to_bv 64 0xa2488) fc None m (seg_rom asegs)).
Proof.
intros until junk8. intros Hg Hsz Hlen Esg Hcnt Hk Hv Hffn TAIL Ht0 Ht Hb0 Hb SEP Hal16 Hbal16 MI MU WM HDR SL FR ST.
pose proof (lf_size_range size Hsz) as HSR. word_range sp SPR. unfold_consts. unfold ins_frameA in FR. unfold hdr_cellsA in HDR.
pose proof (SL _ _ Esg) as CG. unfold ent_addr, slot_cells in CG. rewrite Z2Nat.id in CG by lia.
unfold ins_regsA. replace (tbl + g * 40) with (tbl + 40 * g) by lia.
destruct TAIL as [[Hhd Htl] | (Hhd & Htl & Esl & NEl & HhdR)].
-
subst hd tl.
pose proof (munch_refl [(t, t + 56); (tbl + 40 * g, tbl + 40 * g + 40); (lo, bv_unsigned sp + -96)] m) as MU2. pose proof (wmono_refl asegs m) as WM2.
remember (tbl + 40 * g) as B eqn:EB.
assert (EB8 : B mod 8 = 0) by (subst B; Z.div_mod_to_equations; lia).
sh_slotS B. step. step. sh_norm. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false. try clear SHs.
step.
step. step. rewrite (unsigned_lit g) by lia. step. replace (tbl + g * 40) with B by lia.
step.
sh_slotS B. step. step. sh_norm. rewrite (div8_add B 8) by lia. change (8 / 8) with 1. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false. try clear SHs.
step. change (Z.land (bv_unsigned (Z_to_bv 64 0)) (bv_unsigned (Z_to_bv 64 4))) with 0.
step.
stepz.
sh_slotS B. step. step. sh_norm. rewrite (div8_add B 16) by lia. change (16 / 8) with 2. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false. try clear SHs.
step.
sh_hdrS. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false. try clear SHt.
step. norm_sx32. step. step. step. norm_w32. stepz.
sh_hdrS. step. sh_norm. rewrite (div8_add t 8) by lia. change (8 / 8) with 1. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false. try clear SHt.
step. step. step. if_true.
sh_hdrS. step. step. sh_norm. rewrite (div8_add t 16) by lia. change (16 / 8) with 2. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false.
step.
try clear SHt. sh_hdrS. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false. try clear SHt.
step.
step. step. rewrite (unsigned_lit g) by lia. step. replace (tbl + g * 40) with B by lia. step.
step. step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with CGc : rw_cells asegs mc B [?c1; ?c2; ?c3; ?c4; ?c5; ?c6] |- _ =>
change [c1; c2; c3; c4; c5; c6] with ([c1; c2; c3; c4] ++ [c5; c6]) in CGc;
destruct (proj1 (rw_cells_app asegs mc B _ _) CGc) as [CG4 NP]; clear CGc;
cbn [cells_size csize Nat.add] in NP; replace (B + Z.of_nat 24) with (B + 24) in NP by lia;
apply (rw_cells_recast asegs mc (B + 24) _ [CB 16 (cells_bytes [c5; c6])]) in NP;
[| cbn; repeat split; exact I | cbn [cells_bytes cbytes app]; rewrite ?app_nil_r; reflexivity | reflexivity]
end;
match goal with MIc : mem_inv asegs mc, STc : stk asegs mc lo _ |- _ =>
assert (HPc : HEAPAx A LB LM FRS B0 mc md) by (apply (heapA_nowS mc); assumption);
eapply (OBL_AMEMSET _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tbl (40 * size) (B + 24) 0 16 lo);
[ exact HPc | exact INb | subst B; lia | subst B; lia | reflexivity | reflexivity | reflexivity | lia | lia | exact NP
| rewrite ?(unsigned_lit (bv_unsigned sp + -96)) by lia; exact STc | lia | rewrite ?(unsigned_lit (bv_unsigned sp + -96)) by lia; lia
| rewrite ?(unsigned_lit (bv_unsigned sp + -96)) by lia; rewrite <- Zplus_mod_idemp_l, SPA; reflexivity
| rewrite ?(unsigned_lit (bv_unsigned sp + -96)) by lia; lia | exact MIc | reflexivity | ] end end.
intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m4 MU4 WM4 MI4 DST4 ST4.
rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in MU4, ST4 by lia.
lazymatch type of MU4 with munch _ ?mc _ =>
transport_after_call asegs mc m4 MU4 WM4; try match goal with H : mem_inv asegs mc |- _ => clear H end end.
replace (ret_pc (Z_to_bv 64 0xa2610)) with (Z_to_bv 64 0xa2610) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
change (Z.to_nat 16) with 16%nat in DST4. cbn [repeat] in DST4.
apply (rw_cells_recast asegs m4 (B + 24) _ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) in DST4; [| cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity].
step.
step. do 11 step.
lazymatch goal with H : rw_cells asegs ?mx (bv_unsigned sp + -96) _ |- _ => release_frame H ST4 (bv_unsigned sp) end.
step. step. subst B.
apply evt_done. do 14 eexists. eexists. split; [reflexivity|].
split; [assumption|]. split; [assumption|]. split; [exact MI4|].
split. { unfold hdr_cellsA. cbn [Z.eqb]. unfold ent_addr. rewrite Z2Nat.id by lia. assumption. }
split; [| assumption].
unfold ins_svs. cbn [Z.eqb]. eapply (lh_slots_write1 asegs m); [exact SL | lia | exact MU2 | exact WM2 | | ].
+ intros i NE Hi. unfold ivs_miss_slot. apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]; cbn; unfold ent_addr.
* destruct SEP; [right; lia | left; nia].
* assert (Z.of_nat i + 1 <= g \/ g + 1 <= Z.of_nat i) as [L|R] by lia; [left; nia | right; nia].
* left. nia.
+ unfold ent_addr, slot_cells, new_slot. cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv]. rewrite Z2Nat.id by lia.
lazymatch goal with |- rw_cells _ ?mf _ [?c1; ?c2; ?c3; ?c4; ?c5; ?c6] =>
change [c1; c2; c3; c4; c5; c6] with ([c1; c2; c3; c4] ++ [c5; c6]);
apply (proj2 (rw_cells_app asegs mf (tbl + 40 * g) _ _)); cbn [cells_size csize Nat.add];
replace (tbl + 40 * g + Z.of_nat 24) with (tbl + 40 * g + 24) by lia; split; assumption end.
-
pose proof (SL _ _ Esl) as CL. unfold ent_addr, slot_cells in CL.
pose proof (proj1 (nth_error_Some svs ixl) ltac:(rewrite Esl; discriminate)) as Hixl.
assert (NEg : Z.of_nat ixl <> g) by (intros X; apply NEl; lia).
pose proof (munch_refl [(t, t + 56); (tbl + 40 * g, tbl + 40 * g + 40); (tbl + 40 * Z.of_nat ixl, tbl + 40 * Z.of_nat ixl + 40)] m) as MU2. pose proof (wmono_refl asegs m) as WM2.
remember (tbl + 40 * g) as B eqn:EB. remember (tbl + 40 * Z.of_nat ixl) as TL eqn:ETL.
assert (EB8 : B mod 8 = 0) by (subst B; Z.div_mod_to_equations; lia).
assert (ETL8 : TL mod 8 = 0) by (subst TL; Z.div_mod_to_equations; lia).
replace tl with TL in * by (subst tl TL; unfold ent_addr; reflexivity).
sh_slotS B. step. step. sh_norm. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false. try clear SHs.
step.
step. step. rewrite (unsigned_lit g) by lia. step. replace (tbl + g * 40) with B by lia.
step.
sh_slotS B. step. step. sh_norm. rewrite (div8_add B 8) by lia. change (8 / 8) with 1. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false. try clear SHs.
step. change (Z.land (bv_unsigned (Z_to_bv 64 0)) (bv_unsigned (Z_to_bv 64 4))) with 0.
step.
stepz.
sh_slotS B. step. step. sh_norm. rewrite (div8_add B 16) by lia. change (16 / 8) with 2. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false. try clear SHs.
step.
sh_hdrS. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false. try clear SHt.
step. norm_sx32. step. step. step. norm_w32. stepz.
sh_hdrS. step. sh_norm. rewrite (div8_add t 8) by lia. change (8 / 8) with 1. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false. try clear SHt.
step. step. step. if_falsex.
sh_hdrS. step. step. sh_norm. rewrite (div8_add t 16) by lia. change (16 / 8) with 2. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false. try clear SHt.
step.
step.
sh_slotS TL. step. step. sh_norm. rewrite (div8_add TL 24) by lia. change (24 / 8) with 3. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false. try clear SHs.
step.
step. step. rewrite (unsigned_lit g) by lia. step. replace (tbl + g * 40) with B by lia.
step.
sh_slotS B. step. step. sh_norm. rewrite (div8_add B 32) by lia. change (32 / 8) with 4. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false. try clear SHs.
step.
step.
sh_slotS B. step. step. sh_norm. rewrite (div8_add B 24) by lia. change (24 / 8) with 3. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false. try clear SHs.
step. stepz.
step.
step.
step. do 11 step.
lazymatch goal with H : rw_cells asegs ?mx (bv_unsigned sp + -96) _ |- _ => release_frame H ST (bv_unsigned sp) end.
step. step. subst B.
apply evt_done. do 14 eexists. eexists. split; [reflexivity|].
split. { eapply munch_weaken; [| eassumption]. intros x Hx. cbn in Hx |- *. subst TL. lia. }
split; [assumption|]. split; [assumption|].
split. { unfold hdr_cellsA. destruct (Z.eqb_spec hd 0); [lia|]. unfold ent_addr. rewrite Z2Nat.id by lia. assumption. }
split; [| assumption].
unfold ins_svs. destruct (Z.eqb_spec hd 0); [lia|].
eapply (lh_slots_write2 asegs m); [exact SL | lia | exact Hixl | lia | exact MU2 | exact WM2 | | | ].
+ intros i NE1 NE2 Hi. unfold ivs_miss_slot. subst TL.
apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]; cbn; unfold ent_addr.
* destruct SEP; [right; lia | left; nia].
* assert (Z.of_nat i + 1 <= g \/ g + 1 <= Z.of_nat i) as [L|R] by lia; [left; nia | right; nia].
* assert (i + 1 <= ixl \/ ixl + 1 <= i)%nat as [L|R] by lia; [left; nia | right; nia].
+ unfold ent_addr, slot_cells, new_slot. cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv]. rewrite Z2Nat.id by lia. subst TL. unfold ent_addr in *. assumption.
+ unfold ent_addr, slot_cells. cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv]. rewrite Z2Nat.id by lia. subst TL. assumption.
Qed.
End StoreA.
End RC__1.
