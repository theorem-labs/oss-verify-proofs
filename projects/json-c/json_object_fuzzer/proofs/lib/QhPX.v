(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply Q5Rg QRjH QHnV QCcH QfLs Q0Ek QjDH QmZZ Qsw7 QJjn QKQo Q8tj QSL3 Q3jZ Q6WR QrPc QeuE Q7UD Qhd4 Qwm6 QlKV QsKa Q30W QW22 QI6Z Qiiq QkXq QeVJ Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn QKQo Q8tj.
Import QSL3. Import Q3jZ.
Import Q6WR Q6WR.Mq0 QrPc. Import QeuE.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QsKa.Mq5 Q30W.Mq3 QlKV.Mq3 QW22 QI6Z.Mq1 Qiiq.Mq2 QkXq.Mq3 Qiiq.Mq4 QeVJ.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section BodyOA.
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

Ltac shadowN HP a n Hin SH :=
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ a n HP Hin) as SH;
unfold shad in SH; apply shadow_ro_cells in SH;
let cs := eval cbv in (shadow_cells n) in change (shadow_cells n) with cs in SH.

Lemma body_obj_okA : forall kids k,
desc_optA HIx sp gp lo errv LM FRS k ->
cont_stmtA HIx sp gp lo errv LM FRS true kids ->
head_stmtA HIx sp gp lo errv LM FRS true kids ->
body_stmtA HIx sp gp lo errv LM FRS true kids k.
Proof.
intros kids k KD CONT HEADK.
unfold body_stmtA. intros until cur. intros HP ZB ST ERR BB K.
unfold_consts. word_range sp SPW. cbn [tyof].
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
destruct ZB as (t & tbl & size & es & svs & e0 & Z0 & He0 & Ecur).
destruct (zobj_last asegs A4F _ _ _ _ _ _ _ _ _ _ _ _ Z0) as (pb & PBS & KBS1 & bs & esk1 & e & esz & Ees & Lk & Lz & Fz & EX & OPB & HDR & OPEN & OK1 & Hk).
assert (Ee : e0 = e) by (rewrite Ees, <- Lk, nth_error_app_len in He0; injection He0 as He0; symmetry; exact He0). subst e0.
clear Z0.

pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as NDall.
assert (HPl : HEAPAx A (lh_blocks t tbl size es ++ ((x, 48) :: concat KBS1 ++ bs ++ PBS ++ LB)) LM FRS B m md).
{ eapply (heapA_perm A4L HIx); [exact HP | rewrite EX; perm | apply Permutation_refl | apply Permutation_refl]. }
destruct (lh_heap_factsA HIx _ _ _ _ _ _ _ _ _ _ _ HPl) as ((Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & Httb & KEYF).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hbhi.
assert (INx : In (x, 48) (XBS ++ LB)) by (rewrite EX; in_elem).
assert (INx2 : In (x, 48) ((XBS ++ LB) ++ LM)) by (apply in_or_app; left; exact INx).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ x 48 HP INx2) as (_ & Hxal & Hxlo & Hxhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ x 48 HP INx2) as Hximg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hxhi.
assert (INtb : In (tbl, 40 * size) (XBS ++ LB)) by (rewrite EX; unfold lh_blocks; in_elem).
assert (INtb2 : In (tbl, 40 * size) ((XBS ++ LB) ++ LM)) by (apply in_or_app; left; exact INtb).
assert (NXT : x <> tbl).
{ intros E. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HPl) as ND. unfold lh_blocks in ND. cbn [map blk_addr fst app] in ND.
inversion ND as [|y l Hn1 ND1]; subst. inversion ND1 as [|y' l' Hn2 ND2]; subst. apply Hn2.
apply in_map_iff. exists (tbl, 48). split; [reflexivity | in_elem]. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ x 48 tbl (40 * size) HP INx2 INtb2 NXT) as Dxtb.
clear HPl.

destruct (lh_open_slot asegs A4F _ _ _ _ _ _ _ (length kids) e OPEN ltac:(rewrite Ees, <- Lk; apply nth_error_app_len)) as (sl & Esl & Hix & SLOT).
pose proof OPEN as (_ & _ & _ & _ & Hsz & Hcnt & Hlen).
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR.
assert (Hixz : 0 <= Z.of_nat (le_ix e) /\ Z.of_nat (le_ix e) + 1 <= size) by lia.
pose proof (ent_shadowA HIx _ _ _ _ _ _ _ tbl size (le_ix e) HP INtb ltac:(lia) ltac:(lia)) as SHe.
unfold ent_addr in SLOT, Ecur, SHe. subst cur.
set (ea := tbl + 40 * Z.of_nat (le_ix e)) in *.
assert (EAR : tbl <= ea /\ ea + 40 <= tbl + 40 * size) by (subst ea; lia).
assert (EA8 : ea mod 8 = 0) by (subst ea; clear - Hbal; Z.div_mod_to_equations; lia).
shadowN HP x 48 INx SHx. a4l.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(ea + 16, ea + 24)] m) as MU.
pose proof HDR as HDR0. unfold jhdr_cells in HDR. cbn [app fn_obj_to_json_string A4F] in HDR.
stash Hk. stash KEYF. stash OPB. stash OK1. stash HDR0.
reenterA asegs A4L HIx asegs_wx HP.
step. step. if_false. rewrite ?sxb_zero, ?zxb_zero.
step. norm_w32. step. if_falsex. step. if_falsex.
step. asan_chkA.
step. stepz.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
try clear SHx. try clear SHe.
assert (HP2 : HEAPAx A (XBS ++ LB) LM FRS B m2 md) by heap_nowA A4L HIx HP MU WM MI.
assert (AG2 : agree_on asegs (others tbl (XBS ++ LB)) m m2).
{ eapply (agree_others_gen asegs); [exact MU | exact WM |]. intros a' kk Hin Hne.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a' kk HP ltac:(apply in_or_app; left; exact Hin)) as (Hk0 & _ & _ & Hahi' & _).
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tbl (40 * size) a' kk HP INtb2 ltac:(apply in_or_app; left; exact Hin) ltac:(congruence)) as D.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hahi'. cbn. lia. }
pose proof (nodup_app_l' _ _ NDall) as NDX.
assert (NTB : forall k, ~ In (tbl, k) LB).
{ intros kk Hkk. eapply (nodup_prefix_suffix XBS LB tbl (40 * size) kk NDX); [rewrite EX; unfold lh_blocks; in_elem | exact Hkk]. }
assert (HPR2 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp + -112) m m2).
{ eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp + -112)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; apply in_or_app; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; in_sub Hb | right; exact Hb] | clia |].
apply Forall_cons; [cbn [fst snd] | apply Forall_nil]. right; left. exists tbl, (40 * size).
split; [exact INtb2|]. split; [| lia]. intros Hkk. apply in_app_or in Hkk. destruct Hkk as [Hkk|Hkk]; [exact (NTB _ Hkk)|].
apply in_app_or in Hkk. destruct Hkk as [Hkk|Hkk]; [| exfalso; exact (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP INtb2 Hkk)].
exact (nodup_prefix_suffix (XBS ++ LB) LM tbl (40 * size) (40 * size) NDall INtb Hkk). }
unstash KEYF.
assert (OPEN2 : lh_open asegs A4F m2 t tbl size (esk1 ++ with_v e 0 :: esz) (upd svs (le_ix e) (sv_with_v sl 0))).
{ replace (esk1 ++ with_v e 0 :: esz) with (upd es (length kids) (with_v e 0)) by (rewrite Ees, <- Lk; apply upd_app_len').
eapply (lh_open_set_val asegs A4F); [exact OPEN | rewrite Ees, <- Lk; apply nth_error_app_len | exact Esl | lia | exact MU | exact WM | | exact Httb | | ].
- apply Forall_cons; [cbn; subst ea; unfold ent_addr; lia | apply Forall_nil].
- intros y Hy. destruct (KEYF y Hy) as (_ & _ & _ & _ & _ & D). exact D.
- unfold ent_addr. fold ea. assumption. }
stash KEYF.
set (es2 := esk1 ++ with_v e 0 :: esz) in OPEN2.
set (svs2 := upd svs (le_ix e) (sv_with_v sl 0)) in OPEN2.
set (XBS1 := ((x, 48) :: lh_blocks t tbl size es ++ concat KBS1) ++ PBS).
assert (ELB : lh_blocks t tbl size es2 = lh_blocks t tbl size es).
{ subst es2. rewrite Ees. unfold lh_blocks. rewrite !map_app. reflexivity. }
assert (Z2 : zobj asegs A4F m2 x q kids (S nz) t tbl size es2 svs2 XBS1).
{ unstash HDR0. unstash OPB. unstash OK1. subst XBS1. rewrite <- ELB.
eapply (zobj_last_close asegs A4F m m2); [exact Lz | exact Fz | exact OPB | exact HDR0 | exact OK1 | exact OPEN2 | ].
eapply agree_on_incl; [exact AG2 | intros [ba bk] Hb; apply in_others; [rewrite EX; in_sub Hb|]].
intros ->. eapply (nodup_in_ne (XBS ++ LB) [(tbl, 40 * size)] ((t, 56) :: map (fun e1 => (le_k e1, le_kn e1)) es ++ (x, 48) :: concat KBS1 ++ bs ++ PBS ++ LB));
[rewrite EX; hperm | exact NDX | left; reflexivity | in_sub Hb | reflexivity]. }
assert (Hes2 : nth_error es2 (length kids) = Some (with_v e 0)) by (subst es2; rewrite <- Lk; apply nth_error_app_len).
assert (VZ2 : forall j y, (length kids <= j)%nat -> nth_error es2 j = Some y -> le_v y = 0).
{ intros j y Hj Hy. subst es2. rewrite nth_error_app2 in Hy by lia.
destruct (j - length esk1)%nat as [|j'] eqn:Ej; cbn in Hy.
- injection Hy as <-. reflexivity.
- exact (proj1 (Forall_forall _ _) Fz y (nth_error_In _ _ Hy)). }
clear HDR0 OPB OK1 OPEN.

assert (TAIL : forall (mm : word -> option byte) (Am : ASA A4L HIx) (Bm : bud) (mdm : config) (Fm : bvmap 5 word) (fcm : bv 32)
(y1 yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y18 yt3 yt4 yt5 yt6 : word),
HEAPAx Am (XBS1 ++ LB) LM FRS Bm mm mdm ->
zobj asegs A4F mm x q kids (S nz) t tbl size es2 svs2 XBS1 ->
stk asegs mm lo (bv_unsigned sp + -112) -> rw_cells asegs mm ERRNO [C4 errv] ->
512 * Z.of_nat (length XBS1) <= bB Bm ->
(forall ms' md' A', NEXT q Fm fcm mm mdm LB Bm (512 * Z.of_nat (length XBS1)) ms' md' A' -> AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx Am T mdm
(MS (mkR y1 SPR gp TP yt0 yt1 yt2 (Z_to_bv 64 x) (Z_to_bv 64 (x + 40)) ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7
y18 (Z_to_bv 64 ea) (Z_to_bv 64 (Z.of_nat (length kids))) (Z_to_bv 64 (Z.of_nat nz + 1))
(Z_to_bv 64 (x / 8 + 2147450885)) SBR (Z_to_bv 64 4) (Z_to_bv 64 (x / 8 + 2147450880)) (Z_to_bv 64 5) CM1 yt3 yt4 yt5 yt6)
Fm (Z_to_bv 64 0x9a914) fcm None mm (seg_rom asegs))).
{ intros until yt6. intros HPm Zm STm ERRm BBm Km.
clear MU WM MI HP HP2 AG2 HPR2 ST ERR Hk BB K OPEN2 SLOT HDR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HPm) as MIm.
pose proof Zm as (pbm & PBSm & KBSm & eskm & eszm & Eesm & Lzm & Fzm & EXm & OPBm & HDRm & OPENm & OKm).
destruct (lh_open_slot asegs A4F _ _ _ _ _ _ _ (length kids) (with_v e 0) OPENm Hes2) as (slm & Eslm & Hixm & SLOTm).
cbn [le_ix le_k le_v with_v] in SLOTm. unfold ent_addr in SLOTm. fold ea in SLOTm.
assert (INx1 : In (x, 48) (XBS1 ++ LB)) by (subst XBS1; in_elem).
assert (INtb1 : In (tbl, 40 * size) (XBS1 ++ LB)) by (subst XBS1; unfold lh_blocks; in_elem).
shadowN HPm x 48 INx1 SHxm.
pose proof (ent_shadowA HIx _ _ _ _ _ _ _ tbl size (le_ix e) HPm INtb1 ltac:(lia) ltac:(lia)) as SHem.
unfold ent_addr in SHem. fold ea in SHem. a4l.
unfold jhdr_cells in HDRm. cbn [app fn_obj_to_json_string A4F] in HDRm.
pose proof (wmono_refl asegs mm) as WM. pose proof (munch_refl [] mm) as MU.
reenterA asegs A4L HIx asegs_wx HPm.
step. step. if_false. rewrite ?sxb_zero, ?zxb_zero.
step. norm_w32. step. if_false.
step. asan_chkA.
step. step.
evt_done5.
replace (Z.of_nat nz + 1) with (Z.of_nat (S nz)) by lia.
eapply CONT; [eapply (heapA_client_frame A4L HIx); [exact HPm | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HPm MU); apply Forall_nil | exact WM | exact MIm] | | exact STm | exact ERRm | exact BBm | exact Km].
exists t, tbl, size, es2, svs2. split; [exact Zm|].
intros kids1 kl Ek.
assert (Hj : (length kids1 < length esk1)%nat) by (rewrite Lk, Ek, length_app; cbn; lia).
destruct (nth_error esk1 (length kids1)) as [e'|] eqn:En; [| apply nth_error_None in En; lia].
exists e'. split; [subst es2; rewrite nth_error_app1 by lia; exact En|].
rewrite pv_of_spec, Ek, length_app. cbn [length]. rewrite Nat.add_1_r. cbn [pv_of].
subst es2. rewrite nth_error_app1 by lia. rewrite En. reflexivity. }
step.
unstash Hk. destruct k as [c|].
-
destruct Hk as [Hv J].
assert (J2 : jval asegs A4F c m2 bs (le_v e) 1).
{ eapply jval_agree; [exact J | eapply agree_on_incl; [exact AG2|] | apply incl_refl].
intros [ba bk] Hb. apply in_others; [rewrite EX; in_sub Hb|].
intros ->. eapply (nodup_in_ne (XBS ++ LB) [(tbl, 40 * size)] ((t, 56) :: map (fun e1 => (le_k e1, le_kn e1)) es ++ (x, 48) :: concat KBS1 ++ bs ++ PBS ++ LB));
[rewrite EX; hperm | exact NDX | left; reflexivity | in_sub Hb | reflexivity]. }
clear J.
assert (HPc : HEAPAx A (bs ++ XBS1 ++ LB) LM FRS B m2 md) by (eapply (heapA_perm A4L HIx); [exact HP2 | subst XBS1; rewrite EX; hperm | apply Permutation_refl | apply Permutation_refl]).
pose proof (nodup_app_l' _ _ (nodup_app_l' _ _ (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HPc))) as NDbs.
destruct (jval_hdr asegs A4F c m2 bs (le_v e) 1 J2 NDbs) as (cn & tojs_ & pb_ & udel_ & ud_ & rest_ & INc & _ & N48c & _ & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ (le_v e) cn HPc ltac:(apply in_or_app; left; in_sub INc)) as (_ & Hcal & Hclo & Hchi & _). clear tojs_ pb_ udel_ ud_ rest_.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hchi.
if_truex. step. step. step.
evt_done5.
eapply (maybe_free_A_closed HIx) with (s := c) (BS := bs) (LB := XBS1 ++ LB) (x := le_v e) (rc := 1) (lo := lo);
[ exact HPc | lia | lia | exact J2 | .. ]; a4l_goal; rewrite ?unsigned_lit by lia; try first [exact ST | exact ERR | assumption | reflexivity | lia].
all: try (replace (bv_unsigned sp + -112) with (bv_unsigned sp - 112) by lia; rewrite Zminus_mod, SPA; reflexivity).
all: try (intros _; clear - BB EX; rewrite EX in BB; cbn [length app] in BB; rewrite ?length_app in BB; cbn [length] in BB; rewrite ?length_app in BB; unfold blk in *; lia).
intros ms3 md3 A3 (m3 & r & B3 & RS3 & VM3 & ST3 & HPR3 & ERR3 & BD3 & OUT3).
destruct RS3 as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F3 & fc3 & -> & FS3 & FRM3).
a4l. rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in HPR3 by lia.
assert (Z3 : zobj asegs A4F m3 x q kids (S nz) t tbl size es2 svs2 XBS1).
{ eapply (zobj_agree asegs A4F (XBS1 ++ LB)); [exact Z2 | eapply (agree_of_heap_pres asegs A4H); [exact HPR3 | reflexivity | intros b Hb; apply in_or_app; left; exact Hb] | intros b Hb; in_sub Hb]. }
assert (HPR23 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp + -112) m m3).
{ eapply heap_pres_trans; [exact HPR2 | eapply heap_pres_weaken; [exact HPR3 | lia | intros b Hb; apply in_or_app; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; in_sub Hb | right; exact Hb]]]. }
clear MU WM MI HP2 HP AG2 ST J2 HPc SLOT HDR.
destruct OUT3 as [(_ & Habs & _) | [(Er & _ & BB3 & HP3) | (Er & _ & ZC & BB3 & HP3)]]; [lia | |]; rewrite ?unsigned_lit in Er by lia; subst r.
+
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI.
pose proof (munch_refl [] m3) as MU. pose proof (wmono_refl asegs m3) as WM.
reenterA asegs A4L HIx asegs_wx HP3.
step. step. if_falsex.
evt_done5.
eapply TAIL; [eapply (heapA_client_frame A4L HIx); [exact HP3 | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP3 MU); apply Forall_nil | exact WM | exact MI] | exact Z3 | exact ST3 | exact ERR3 | |].
* clear - BB BB3 EX. subst XBS1. rewrite EX in BB. cbn [length app] in *. rewrite ?length_app in *. cbn [length] in *. rewrite ?length_app in *. unfold blk in *. lia.
* intros ms' md' A' NP. apply K. eapply next_postA_w; [exact FS3 | exact FRM3 | exact VM3 | exact HPR23 | exact BB3 | exact BD3 | exact NP |].
clear - EX. subst XBS1. rewrite EX. cbn [length app]. rewrite ?length_app. cbn [length]. rewrite ?length_app. unfold blk. lia.
+
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI.
pose proof (munch_refl [] m3) as MU. pose proof (wmono_refl asegs m3) as WM.
reenterA asegs A4L HIx asegs_wx HP3.
step. step. if_truex.
evt_done5.
destruct c as [| | | |ck|ck]; cbn in ZC; try contradiction.
all: eapply (descend_objA HIx sp gp lo errv LM FRS LO LOS SPA HT DEL _ kids KD HEADK) with (e2 := with_v e 0);
[exact HP3 | exact ZC | exact Z3 | exact Hes2 | exact ST3 | exact ERR3 | |].
all: try (clear - BB BB3 EX; subst XBS1; rewrite EX in BB; cbn [length app] in *; rewrite ?length_app in *; cbn [length] in *; rewrite ?length_app in *; unfold blk in *; lia).
all: intros ms' md' A' NP; apply K; eapply next_postA_w; [exact FS3 | exact FRM3 | exact VM3 | exact HPR23 | | exact BD3 | exact NP |];
[ instantiate (1 := 0); lia
| clear - EX; subst XBS1; rewrite EX; cbn [length app]; rewrite ?length_app; cbn [length]; rewrite ?length_app; unfold blk; lia ].
-
destruct Hk as [Hv Ebs]. rewrite Hv. if_false. step.
evt_done5.
assert (HPn : HEAPAx A (XBS1 ++ LB) LM FRS B m2 md) by (eapply (heapA_perm A4L HIx); [exact HP2 | subst XBS1 bs; rewrite EX; hperm | apply Permutation_refl | apply Permutation_refl]).
eapply TAIL; [exact HPn | exact Z2 | exact ST | assumption | |].
+ clear - BB EX Ebs. subst XBS1 bs. rewrite EX in BB. cbn [length app] in *. rewrite ?length_app in *. cbn [length] in *. rewrite ?length_app in *. unfold blk in *. lia.
+ intros ms' md' A' NP. apply K. eapply next_postA_w; [apply fsaved_refl | intros Hf; exact Hf | apply model_vm_only_refl | exact HPR2 | | | exact NP |].
* instantiate (1 := 0). lia.
* lia.
* clear - EX Ebs. subst XBS1 bs. rewrite EX. cbn [length app]. rewrite ?length_app. cbn [length]. rewrite ?length_app. unfold blk. lia.
Qed.
End BodyOA.
End RC__1.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnCn QnDr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn QKQo Q8tj.
Import QSL3.
Import QnCn.Mq0.
Import Q6WR Q6WR.Mq0 QrPc. Import QeuE.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq7 QsKa.Mq3 Q30W.Mq0 QI6Z.Mq0 QsKa.Mq5 QnDr.Mq1 QkXq.Mq3 Qiiq.Mq4 QeVJ.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section DescA2.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Variables (sp gp : word) (lo : Z) (errv : word) (LM : list blk) (FRS : list frame).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp + -112 - 4352.
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HT : bv_unsigned sp <= hiA_top A4L HIx.

Notation SPR := (Z_to_bv 64 (bv_unsigned sp + -112)).
Notation TP := (Z_to_bv 64 6434400).
Notation SBR := (Z_to_bv 64 2147450880).
Notation CM1 := (Z_to_bv 64 18446744073709551615).
Notation ERRNO := (6434400 - 164).
Notation NEXT := (next_postA HIx sp gp lo errv LM FRS).
Notation head_stmt' := (head_stmtA HIx sp gp lo errv LM FRS).

Ltac shadowN HP a n Hin SH :=
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ a n HP Hin) as SH;
unfold shad in SH; apply shadow_ro_cells in SH;
let cs := eval cbv in (shadow_cells n) in change (shadow_cells n) with cs in SH.
Ltac shadow48 HP a Hin SH := shadowN HP a 48 Hin SH.

Lemma descend_arrA : forall c kids,
desc_stmtA HIx sp gp lo errv LM FRS c -> head_stmt' false kids ->
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (LB XBS1 bs : list blk) (x q v : Z) (T : TSet)
(nz : nat) (a arr size : Z),
HEAPAx A (bs ++ XBS1 ++ LB) LM FRS B m md ->
zomb asegs A4F c m v bs ->
zarr asegs A4F m x q kids (S nz) a arr size XBS1 ->
stk asegs m lo (bv_unsigned sp + -112) -> rw_cells asegs m ERRNO [C4 errv] ->
512 * (Z.of_nat (length bs) + Z.of_nat (length XBS1)) <= bB B ->
(forall ms' md' A', NEXT q F1 fc1 m md LB B (512 * (Z.of_nat (length bs) + Z.of_nat (length XBS1))) ms' md' A' -> AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR x1 SPR gp TP t0 t1 t2 (Z_to_bv 64 x) (Z_to_bv 64 (x + 40)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 v) x19 (Z_to_bv 64 (Z.of_nat (length kids))) (Z_to_bv 64 (Z.of_nat nz + 1))
(Z_to_bv 64 (x / 8 + 2147450885)) SBR (Z_to_bv 64 4) (Z_to_bv 64 (x / 8 + 2147450880)) (Z_to_bv 64 5) CM1 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x9a9fc) fc1 None m (seg_rom asegs)).
Proof.
intros c kids KD HK. intros until size. intros HP ZC Z ST ERR BB K.
unfold_consts. word_range sp SPW.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
destruct Z as (pb & PBS & KBS & ps & EX1 & OPB & HDR & AL & OK).
pose proof (okids_len _ _ _ _ _ _ OK) as [L _].
destruct (zomb_zhead HIx sp gp lo errv LM FRS c m v bs ZC KD) as (isobjc & ck & ZCH & HC). clear ZC KD.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND0. pose proof (nodup_app_l' _ _ ND0) as ND.
destruct (zhead_hdr isobjc m v 0 ck bs ZCH (nodup_app_l' _ _ ND)) as (pbc & cfc & INv & HDRC & CLOSEC).
assert (INv' : In (v, 48) (bs ++ XBS1 ++ LB)) by in_sub INv.
assert (INx : In (x, 48) (bs ++ XBS1 ++ LB)) by (rewrite EX1; in_elem).
assert (INa : In (a, 32) (bs ++ XBS1 ++ LB)) by (rewrite EX1; in_elem).
assert (INr : In (arr, 8 * size) (bs ++ XBS1 ++ LB)) by (rewrite EX1; in_elem).
assert (INv2 : In (v, 48) ((bs ++ XBS1 ++ LB) ++ LM)) by (apply in_or_app; left; exact INv').
assert (INx2 : In (x, 48) ((bs ++ XBS1 ++ LB) ++ LM)) by (apply in_or_app; left; exact INx).
assert (INa2 : In (a, 32) ((bs ++ XBS1 ++ LB) ++ LM)) by (apply in_or_app; left; exact INa).
assert (INr2 : In (arr, 8 * size) ((bs ++ XBS1 ++ LB) ++ LM)) by (apply in_or_app; left; exact INr).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ v 48 HP INv2) as (_ & Hval & Hvlo & Hvhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ v 48 HP INv2) as Hvimg.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ x 48 HP INx2) as (_ & Hxal & Hxlo & Hxhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ x 48 HP INx2) as Hximg.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a 32 HP INa2) as (_ & Haal & Halo & Hahi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ a 32 HP INa2) as Haimg.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ arr (8 * size) HP INr2) as (Hr0 & Hral & Hrlo & Hrhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ arr (8 * size) HP INr2) as Hrimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hvhi, Hxhi, Hahi, Hrhi.
assert (NVX : forall k, ~ In (v, k) (XBS1 ++ LB)) by (intros k; exact (nodup_prefix_suffix bs (XBS1 ++ LB) v 48 k ND INv)).
assert (Hxv : x <> v) by (intros ->; apply (NVX 48); rewrite EX1; in_elem).
assert (Hva : v <> a) by (intros E; apply (NVX 32); rewrite E, EX1; in_elem).
assert (Hvr : v <> arr) by (intros E; apply (NVX (8 * size)); rewrite E; rewrite EX1; in_elem).
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ x 48 v 48 HP INx2 INv2 Hxv) as Dxv.
assert (HPal : HEAPAx A ((a, 32) :: (arr, 8 * size) :: (x, 48) :: concat KBS ++ PBS ++ bs ++ LB) LM FRS B m md).
{ eapply (heapA_perm A4L HIx); [exact HP | rewrite EX1; hperm | apply Permutation_refl | apply Permutation_refl]. }
destruct (blocks2A HIx _ _ _ _ _ _ _ _ _ _ _ HPal) as (_ & _ & Har).
assert (Hxa : x <> a).
{ intros ->. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HPal) as ND2. cbn [map blk_addr fst app] in ND2.
inversion ND2 as [|y l Hn1 ND3]; subst. apply Hn1. right. left. reflexivity. }
assert (Hxr : x <> arr).
{ intros ->. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HPal) as ND2. cbn [map blk_addr fst app] in ND2.
inversion ND2 as [|y l Hn1 ND3]; subst. inversion ND3 as [|y' l' Hn2 ND4]; subst. apply Hn2. left. reflexivity. }
clear HPal.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ v 48 a 32 HP INv2 INa2 Hva) as Dva.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ v 48 arr (8 * size) HP INv2 INr2 Hvr) as Dvr.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ x 48 a 32 HP INx2 INa2 Hxa) as Dxa.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ x 48 arr (8 * size) HP INx2 INr2 Hxr) as Dxr.
shadow48 HP v INv' SHv.
shadow48 HP x INx SHx.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ v 48 0 v 48 HP INv' ltac:(lia) INv2) as SEPv0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ v 48 5 v 48 HP INv' ltac:(cbn; lia) INv2) as SEPv5.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ x 48 0 v 48 HP INx ltac:(lia) INv2) as SEPx0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ x 48 5 v 48 HP INx ltac:(cbn; lia) INv2) as SEPx5.
a4l.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(v + 24, v + 40)] m) as MU.
unfold jhdr_cells in HDRC. cbn [app] in HDRC. unfold jhdr_cells in HDR. cbn [app fn_arr_to_json_string A4F] in HDR.
stash Dxa. stash Dxr. stash Dva. stash Dvr. clear GOT CELL.
reenterA asegs A4L HIx asegs_wx HP.
step. asan_chkA.
step.
step. asan_chkA.
stepz.
step. step. if_false. rewrite ?sxb_zero, ?zxb_zero.
step. step. if_false. rewrite ?sxb_zero, ?zxb_zero.
step. norm_w32. step. step. if_true.
step. step. step.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
assert (HP1 : HEAPAx A (bs ++ XBS1 ++ LB) LM FRS B m1 md) by heap_nowA A4L HIx HP MU WM MI.
assert (AGV : agree_on asegs (others v (bs ++ XBS1 ++ LB)) m m1).
{ eapply (agree_others_gen asegs); [exact MU | exact WM |]. intros a' k Hin Hne.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a' k HP ltac:(apply in_or_app; left; exact Hin)) as (Hk & _ & _ & Hahi' & _).
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ v 48 a' k HP INv2 ltac:(apply in_or_app; left; exact Hin) ltac:(congruence)) as D.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hahi'. cbn. lia. }
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
assert (AL1 : alist asegs A4F m1 [(a, 32); (arr, 8 * size)] a (ps ++ repeat 0 (S nz))).
{ eapply (alist_agree asegs A4F); [exact AL | exact AGX | intros b Hb; rewrite EX1; in_sub Hb]. }
clear CLOSEC SHv SHx SEPv0 SEPv5 SEPx0 SEPx5.
match goal with H : rw_cells _ m1 v _ |- _ => clear H end.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI1.
shadowN HP1 a 32 INa SHa1.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ arr (8 * size) HP1 INr) as SHr1. unfold shad in SHr1. a4l.
clear MU WM. pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP1) as [GOT1 CELL1]. a4l.
pose proof (wmono_refl asegs m1) as WM. pose proof (munch_refl [(lo, bv_unsigned sp + -112); (a, a + AL_SZ); (arr, arr + 8 * size)] m1) as MU.
pose proof (nodup_app_l' _ _ (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP1)) as ND1.
assert (NEa : forall bb kk, In (bb, kk) (bs ++ (x, 48) :: concat KBS ++ PBS ++ LB) -> a <> bb /\ arr <> bb).
{ intros bb kk Hb. split.
- eapply (nodup_in_ne (bs ++ XBS1 ++ LB) [(a, 32); (arr, 8 * size)] (bs ++ (x, 48) :: concat KBS ++ PBS ++ LB)); [rewrite EX1; hperm | exact ND1 | in_elem | exact Hb].
- eapply (nodup_in_ne (bs ++ XBS1 ++ LB) [(a, 32); (arr, 8 * size)] (bs ++ (x, 48) :: concat KBS ++ PBS ++ LB)); [rewrite EX1; hperm | exact ND1 | in_elem | exact Hb]. }
stash Hvimg. stash Hximg. stash Dxv. stash NVX. stash AGV. stash AGX. stash NEa. stash ZCH1. stash OPB. stash OK.
unstash Dxa. unstash Dxr.
callA (array_list_del_idx_A (Z_to_bv 64 0x9a808) SPR gp TP (Z_to_bv 64 x) (Z_to_bv 64 (x + 40)) (Z_to_bv 64 v) x19
(Z_to_bv 64 (Z.of_nat (length kids))) (Z_to_bv 64 (Z.of_nat nz + 1)) (Z_to_bv 64 (x / 8 + 2147450885)) SBR (Z_to_bv 64 4)
(Z_to_bv 64 (x / 8 + 2147450880)) (Z_to_bv 64 5) CM1 F1 fc1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 lo _ a arr size ps (repeat 0 (S nz))).
all: try (unfold small_pre; rewrite ?unsigned_lit by lia; split; [exact MI1|]; split; [assumption|]; split; [lia|]; split; [lia|]; split; [exact GOT1|]; split; [exact CELL1|];
unfold alloc_ceiling, sp_window_lo, stack_max_size; lia).
all: try (rewrite ?unsigned_lit by lia; lia).
all: try (eapply (asan_rt_ok_of_HEAPA HIx); exact HP1).
all: try exact AL1. all: try apply Forall_repeat0. all: try exact Har.
all: try (unfold al_blkA; unfold alloc_ceiling, sp_window_lo, stack_max_size; lia).
all: try exact SHa1. all: try exact SHr1.
all: try (replace (bv_unsigned sp + -112) with (bv_unsigned sp - 112) by lia; rewrite Zminus_mod, SPA; reflexivity).
all: try (rewrite L; reflexivity).
all: try (apply f_equal; rewrite repeat_length; lia).
all: try reflexivity.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
match goal with H : mem_inv asegs m4 |- _ => rename H into MI4 end.
match goal with H : stk asegs m4 _ _ |- _ => rename H into ST4 end.
match goal with H : alist _ _ m4 _ _ _ |- _ => rename H into AL4 end.
rename MU into MU4. rename WM into WM4.
unstash Hvimg. unstash Hximg. unstash Dxv. unstash NVX. unstash AGV. unstash AGX. unstash NEa. unstash ZCH1. unstash OPB. unstash OK.
assert (AG4 : agree_on asegs (bs ++ (x, 48) :: concat KBS ++ PBS ++ LB) m1 m4).
{ eapply (agree_of_munch asegs); [exact MU4 | exact WM4 |]. intros bb kk Hb.
assert (Hb' : In (bb, kk) ((bs ++ XBS1 ++ LB) ++ LM)) by (apply in_or_app; left; rewrite EX1; in_sub Hb).
destruct (NEa bb kk Hb) as [N1 N2].
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ bb kk HP1 Hb') as (Hk0 & _ & _ & Hbhi & _). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hbhi.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ a 32 bb kk HP1 INa2 Hb' N1) as D1.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ arr (8 * size) bb kk HP1 INr2 Hb' N2) as D2.
cbn. clear - D1 D2 Hbhi Hk0 LO LOS SPW. lia. }
assert (HP4 : HEAPAx A (bs ++ XBS1 ++ LB) LM FRS B m4 md) by heap_nowA A4L HIx HP1 MU4 WM4 MI4.
assert (HPR4 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp + -112) m1 m4).
{ eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp + -112)); [exact MU4 | exact WM4 |].
eapply (client_outsideA A4L HIx); [exact HP1 | intros b Hb; apply in_or_app; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; in_sub Hb | right; exact Hb] | clia |].
apply Forall_cons; [cbn [fst snd]; left; clia |].
apply Forall_cons; [cbn [fst snd]; right; left; exists a, 32; split; [exact INa2|]; split; [| lia] |].
{ intros Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [exact (proj1 (NEa a 32 ltac:(in_sub Hin)) eq_refl) |].
apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [| exfalso; exact (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP1 INa2 Hin)].
exact (nodup_prefix_suffix (bs ++ XBS1 ++ LB) LM a 32 32 (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP1) INa Hin). }
apply Forall_cons; [cbn [fst snd]; right; left; exists arr, (8 * size); split; [exact INr2|]; split; [| lia] | apply Forall_nil].
{ intros Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [exact (proj2 (NEa arr (8 * size) ltac:(in_sub Hin)) eq_refl) |].
apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [| exfalso; exact (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP1 INr2 Hin)].
exact (nodup_prefix_suffix (bs ++ XBS1 ++ LB) LM arr (8 * size) (8 * size) (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP1) INr Hin). } }
evt_done5.
eapply (descend_tailA HIx sp gp lo errv LM FRS isobjc false ck kids)
with (XBS2 := ((x, 48) :: [(a, 32); (arr, 8 * size)] ++ concat KBS) ++ PBS) (bs := bs) (LB := LB) (q := q);
[exact HC | exact HK | eapply (heapA_perm A4L HIx); [exact HP4 | rewrite EX1; hperm | apply Permutation_refl | apply Permutation_refl] | | | exact ST4 | assumption | rewrite EX1 in BB; exact BB |].
- eapply (zhead_agree isobjc); [exact ZCH1 | exact AG4 | intros b Hb; in_sub Hb].
- exists a, arr, size. exists pb, PBS, KBS, ps. split; [reflexivity|].
split; [| split; [unfold jhdr_cells; cbn [app fn_arr_to_json_string A4F]; assumption | split; [cbn [repeat]; rewrite app_nil_r; exact AL4|]]].
+ eapply opt_pbuf_agree; [exact OPB | | apply incl_refl]. eapply agree_on_trans.
* eapply agree_on_incl; [exact AGX | intros b Hb; rewrite EX1; in_sub Hb].
* eapply agree_on_incl; [exact AG4 | intros b Hb; in_sub Hb].
+ eapply okids_agree; [exact OK | | apply incl_refl]. eapply agree_on_trans.
* eapply agree_on_incl; [exact AGX | intros b Hb; rewrite EX1; in_sub Hb].
* eapply agree_on_incl; [exact AG4 | intros b Hb; in_sub Hb].
- intros ms' md' A' NP. apply K. eapply next_postA_w; [apply fsaved_refl | intros Hf; exact Hf | apply model_vm_only_refl | | | | exact NP |].
+ eapply heap_pres_trans; [exact HPR1 | exact HPR4].
+ instantiate (1 := 0). lia.
+ lia.
+ rewrite EX1. lia.
Qed.
End DescA2.
End RC__1.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw Q22i Q6us QLLZ QAIk QT7b QqWD QbFI QRBl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw Q8tj.
Import QSL3. Import Q22i Q6us QLLZ QAIk QT7b QqWD.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqe Q30W.Mq6 Qiiq.Mq8 QeVJ.Mq1.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section InsertTailA.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis OBL_AMEMSET : amemset_spec_A HIx.

Variables (sp gp tp : word) (s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (t tbl size k v : Z) (es : list lent) (svs : list slotv) (ffn : Z) (lo : Z).
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

Definition ins_tail_postA (cnt : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists (g : nat) (sg : slotv) (ixl : nat) (sl : slotv) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) m',
(g < length svs)%nat /\ nth_error svs g = Some sg /\ is_free sg /\ ~ In g (map le_ix es) /\
(es <> [] -> exists jl el, nth_error es jl = Some el /\ (S jl = length es)%nat /\ ixl = le_ix el /\ nth_error svs ixl = Some sl) /\
ms' = MS (mkR rac sp gp tp x5 x6 x7 s0c s1c (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
s2c s3c s4c s5c s6c s7c s8c s9c s10 s11 x28 x29 x30 x31)
F (ret_pc rac) fc None m' (seg_rom asegs)
/\ munch [(t, t + 56); (tbl, tbl + 40 * size); (lo, bv_unsigned sp)] m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m'
/\ rw_cells asegs m' t (hdr_cellsA tbl ffn size (cnt + 1) (match es with [] => ent_addr tbl g | _ => hd_of tbl es end) (ent_addr tbl g))
/\ lh_slots asegs m' tbl (ins_svs svs g sg k v (hd_of tbl es) (tl_of tbl es) ixl sl tbl)
/\ stk asegs m' lo (bv_unsigned sp).

Lemma lh_insert_tailA :
forall (h cnt : Z) (x1 x5 x6 x7 x9 a5 a7 x20 x22 x23 x24 x25 x28 x29 x30 x31 : word) (m : word -> option byte) (junk8 : list byte),
0 <= h < 2^64 -> In size lf_sizes -> Z.of_nat (length svs) = size -> cnt = Z.of_nat (length es) -> cnt < size ->
lh_link tbl es svs -> lh_keys asegs m es -> 0 <= k < 2^64 -> 0 <= v < 2^64 -> 0 <= ffn < 2^64 ->
0 <= t -> t + 56 <= lo -> 0 < tbl -> tbl + 40 * size <= lo -> (t + 56 <= tbl \/ tbl + 40 * size <= t) -> t mod 16 = 0 -> tbl mod 16 = 0 ->
mem_inv asegs m ->
munch [(t, t + 56); (tbl, tbl + 40 * size); (lo, bv_unsigned sp)] m0 m -> wmono asegs m0 m ->
rw_cells asegs m t (hdr_cellsA tbl ffn size cnt (hd_of tbl es) (tl_of tbl es)) ->
lh_slots asegs m tbl svs ->
ins_frameA sp rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c m junk8 -> stk asegs m lo (bv_unsigned sp + -96) ->
evt asegs (ins_tail_postA cnt m)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (Z_to_bv 64 (t + 4)) x9
(Z_to_bv 64 t) (Z_to_bv 64 k) (Z_to_bv 64 v) (Z_to_bv 64 h) (Z_to_bv 64 0) a5 (Z_to_bv 64 size) a7
(Z_to_bv 64 SB0) (Z_to_bv 64 (t / 8 + SB0)) x20 (Z_to_bv 64 (t / 8 + SB0)) x22 x23 x24 x25 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xa4890) fc None m (seg_rom asegs)).
Proof.
intros until junk8. intros Hh Hsz Hlen Hcnt Hcs LINK KEYS Hk Hv Hffn Ht0 Ht Hb0 Hb SEP Hal16 Hbal16 MI MU WM HDR SL FR ST.
pose proof (lf_size_range size Hsz) as HSR. word_range sp SPR. unfold_consts. unfold hdr_cellsA in HDR.
pose proof FR as FR0. unfold ins_frameA in FR.
pose proof LINK as (LK1 & LK2 & LK3 & LK4).

pose proof (heapA_nowS HIx sp t tbl size lo m0 md A LB LM FRS B0 HP0 INt INb LO HT m MU WM MI) as HPc.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ t 56 HPc INt) as SHt. unfold shad in SHt. apply shadow_ro_cells in SHt.
change (shadow_cells 56) with [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] in SHt.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ t 56 6 t 56 HPc INt ltac:(cbn; lia) ltac:(apply in_or_app; left; exact INt)) as SPt6.
pose proof (tbl_shadowA HIx _ _ _ _ _ _ _ tbl size HPc INb ltac:(lia)) as TSH.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ tbl (40 * size) HPc ltac:(apply in_or_app; left; exact INb)) as (_ & _ & _ & Hbhi & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tbl (40 * size) (5 * size - 1) t 56 HPc INb ltac:(Z.div_mod_to_equations; nia) ltac:(apply in_or_app; left; exact INt)) as SPbl.
cbn [hl_sb hl_segs hl_img_lo hl_img_hi hla_base A4L A4H] in SHt, SPt6, TSH, SPbl. unfold A_SB in *.
assert (XSt : t / 8 + SB0 + 7 <= rc_ceil) by lia.
assert (TSHhi : tbl / 8 + SB0 + 5 * size <= rc_ceil) by lia.
clear SPt6 SPbl HPc.

assert (LIVEK : forall i s, nth_error svs i = Some s -> ~ is_free s -> 0 <= sv_k s < LH_FREEDv).
{ intros i s E NF. destruct (in_dec Nat.eq_dec i (map le_ix es)) as [IN | NI].
- apply in_map_iff in IN as (e & Hix & He). destruct (In_nth_error _ _ He) as [j Hj].
destruct (LK1 j e Hj) as (s' & Es' & Ek & _). rewrite Hix, E in Es'. injection Es' as <-.
destruct (LK4 e He) as (K0 & KF & _ & _). destruct (lh_key_bytes asegs m es e KEYS He) as (_ & _ & KL). rewrite Ek. lia.
- exfalso. apply NF. exact (LK2 i s E NI). }
step. if_falsex.
step.
step. step. sh_norm. rewrite (div8_add t 24) by lia. change (24 / 8) with 3. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false.
step.
step. rewrite remu_lit by lia.
pose proof (Z.mod_pos_bound h size ltac:(lia)) as HM. set (n := h mod size) in *.
step. step. rewrite (unsigned_lit n) by lia.
step. step. step.
step. ub_resolve.
step. ub_resolve.
step. step. step. step. rewrite (mul40_chk n) by lia.
step. if_false.
step. step.
ub_cmp_norm.

pose proof (lf_thr_lt size Hsz) as Hlt.
destruct (free_slot_exists (map le_ix es) (length svs) LK3 ltac:(rewrite length_map; lia)) as (f & Hf & NIf).
destruct (nth_error svs f) as [sf|] eqn:Esf; [| exfalso; apply nth_error_None in Esf; lia].
pose proof (LK2 f sf Esf NIf) as FRf.
eapply evt_cut.
{
eapply (lh_probe_loopA sp gp tp s10 s11 F fc t tbl size k v 0 svs (Z.to_nat ((Z.of_nat f - n) mod size)) n (Z.of_nat f)
x1 x9 (Z_to_bv 64 0) x20 x22 x23 x24 x25 (Z_to_bv 64 1) x29 x30 x31);
first [exact Hsz | exact Hlen | exact LIVEK | exact MI | exact SL | exact TSH | lia | unfold A_SB; unfold_consts; lia | idtac].
- rewrite Nat2Z.id. exact Esf.
- exact FRf. }
cbv beta. intros ms' (gz & sgz & Hgz & Esgz & FREEz & ->).

set (g := Z.to_nat gz).
assert (NIN : ~ In g (map le_ix es)).
{ intros IN. apply in_map_iff in IN as (e & Hix & He). destruct (In_nth_error _ _ He) as [j Hj].
destruct (LK1 j e Hj) as (s' & Es' & Ek & _). rewrite Hix in Es'. unfold g in Es'. rewrite Esgz in Es'. injection Es' as <-.
destruct (LK4 e He) as (K0 & KF & _ & _). unfold is_free, LH_EMPTYv, LH_FREEDv in FREEz. unfold LH_FREEDv in KF.
destruct (lh_key_bytes asegs m es e KEYS He) as (_ & _ & KL). destruct FREEz; lia. }
assert (TL : exists ixl sl,
((hd_of tbl es = 0 /\ tl_of tbl es = 0) \/ (hd_of tbl es <> 0 /\ tl_of tbl es = ent_addr tbl ixl /\ nth_error svs ixl = Some sl /\ ixl <> Z.to_nat gz /\ 0 <= hd_of tbl es < 2^64))
/\ (es <> [] -> exists jl el, nth_error es jl = Some el /\ (S jl = length es)%nat /\ ixl = le_ix el /\ nth_error svs ixl = Some sl)).
{ destruct es as [|e0 es'] eqn:EES.
- exists 0%nat, sgz. split; [left; split; reflexivity | intros X; exfalso; apply X; reflexivity].
- rewrite <- EES in *.
assert (HL : (length es - 1 < length es)%nat) by (rewrite EES; cbn; lia).
destruct (nth_error es (length es - 1)) as [el|] eqn:El; [| exfalso; apply nth_error_None in El; lia].
destruct (LK1 _ _ El) as (sl & Esl & _).
destruct (LK1 0%nat e0 ltac:(rewrite EES; reflexivity)) as (s0' & Es0 & _).
pose proof (proj1 (nth_error_Some svs (le_ix e0)) ltac:(rewrite Es0; discriminate)) as Hix0.
pose proof (proj1 (nth_error_Some svs (le_ix el)) ltac:(rewrite Esl; discriminate)) as Hixl.
exists (le_ix el), sl. split.
+ right. assert (HD0 : hd_of tbl es = ent_addr tbl (le_ix e0)) by (rewrite EES; reflexivity). rewrite !HD0. unfold ent_addr.
split; [lia|]. split; [rewrite (tl_of_last tbl es (length es - 1) el El ltac:(lia)); reflexivity|]. split; [exact Esl|]. split; [| lia].
intros X. apply NIN. unfold g. rewrite <- X. apply in_map. eapply nth_error_In. exact El.
+ intros _. exists (length es - 1)%nat, el. repeat split; try assumption. lia. }
destruct TL as (ixl & sl & TAIL & LAST).
eapply evt_mono.
- eapply (lh_store_blockA HIx OBL_AMEMSET sp gp tp s10 s11 F fc t tbl size k v svs ffn lo rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c
m0 md A LB LM FRS B0 HP0 INt INb LO LOS HT gz sgz cnt (hd_of tbl es) (tl_of tbl es) ixl sl);
first [exact Esgz | exact Hsz | exact Hlen | exact TAIL | exact MI | exact HDR | exact SL | exact FR0 | exact ST | exact SEP | exact Hffn | exact MU | exact WM | lia | idtac].
all: try lia.
- cbv beta. intros ms' (x5' & x6'' & x7'' & x11' & x12' & x13' & x14' & x15' & x16' & x17' & x28' & x29' & x30' & x31' & m' & -> & MU' & WM' & MI' & HDR' & SL' & ST').
unfold ins_tail_postA. exists g, sgz, ixl, sl, x5', x6'', x7'', x11', x12', x13', x14', x15', x16', x17', x28', x29', x30', x31', m'.
assert (GZ : Z.of_nat g = gz) by (unfold g; lia).
try rewrite GZ.
split; [unfold g; lia|]. split; [exact Esgz|]. split; [exact FREEz|]. split; [exact NIN|]. split; [exact LAST|].
split; [reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [| split; [| exact ST']].
+ destruct es; cbn [hd_of] in HDR' |- *; [exact HDR' |]. unfold ent_addr in HDR' |- *.
destruct (Z.eqb_spec (tbl + 40 * Z.of_nat (le_ix l)) 0); [lia | exact HDR'].
+ replace g with (Z.to_nat gz) by reflexivity. exact SL'.
Qed.
End InsertTailA.
End RC__1.
End Mq2.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn QKQo Q8tj.
Import QSL3. Import Q3jZ.
Import Q6WR Q6WR.Mq0 QrPc. Import QeuE.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QsKa.Mqe Q30W.Mq6 QlKV.Mqd QW22.Mq6 QI6Z.Mq4 Qiiq.Mq9 QkXq.Mq7 Qiiq.Mqb QeVJ.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section BodyOA.
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

Ltac shadowN HP a n Hin SH :=
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ a n HP Hin) as SH;
unfold shad in SH; apply shadow_ro_cells in SH;
let cs := eval cbv in (shadow_cells n) in change (shadow_cells n) with cs in SH.

Lemma body_obj_okA : forall kids k,
desc_optA HIx sp gp lo errv LM FRS k ->
cont_stmtA HIx sp gp lo errv LM FRS true kids ->
head_stmtA HIx sp gp lo errv LM FRS true kids ->
body_stmtA HIx sp gp lo errv LM FRS true kids k.
Proof.
intros kids k KD CONT HEADK.
unfold body_stmtA. intros until cur. intros HP ZB ST ERR BB [sbs SPL] K.
unfold_consts. word_range sp SPW. cbn [tyof].
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
destruct ZB as (t & tbl & size & es & svs & e0 & Z0 & He0 & Ecur).
destruct (zobj_last asegs A4F _ _ _ _ _ _ _ _ _ _ _ _ Z0) as (pb & PBS & KBS1 & bs & esk1 & e & esz & Ees & Lk & Lz & Fz & EX & OPB & HDR & OPEN & OK1 & Hk).
assert (Ee : e0 = e) by (rewrite Ees, <- Lk, nth_error_app_len in He0; injection He0 as He0; symmetry; exact He0). subst e0.
clear Z0.

pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as NDall.
assert (HPl : HEAPAx A (lh_blocks t tbl size es ++ ((x, 48) :: concat KBS1 ++ bs ++ PBS ++ LB)) LM FRS B m md).
{ eapply (heapA_perm A4L HIx); [exact HP | rewrite EX; perm | apply Permutation_refl | apply Permutation_refl]. }
destruct (lh_heap_factsA HIx _ _ _ _ _ _ _ _ _ _ _ HPl) as ((Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & Httb & KEYF).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hbhi.
assert (INx : In (x, 48) (XBS ++ LB)) by (rewrite EX; in_elem).
assert (INx2 : In (x, 48) ((XBS ++ LB) ++ LM)) by (apply in_or_app; left; exact INx).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ x 48 HP INx2) as (_ & Hxal & Hxlo & Hxhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ x 48 HP INx2) as Hximg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hxhi.
assert (INtb : In (tbl, 40 * size) (XBS ++ LB)) by (rewrite EX; unfold lh_blocks; in_elem).
assert (INtb2 : In (tbl, 40 * size) ((XBS ++ LB) ++ LM)) by (apply in_or_app; left; exact INtb).
assert (NXT : x <> tbl).
{ intros E. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HPl) as ND. unfold lh_blocks in ND. cbn [map blk_addr fst app] in ND.
inversion ND as [|y l Hn1 ND1]; subst. inversion ND1 as [|y' l' Hn2 ND2]; subst. apply Hn2.
apply in_map_iff. exists (tbl, 48). split; [reflexivity | in_elem]. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ x 48 tbl (40 * size) HP INx2 INtb2 NXT) as Dxtb.
clear HPl.

destruct (lh_open_slot asegs A4F _ _ _ _ _ _ _ (length kids) e OPEN ltac:(rewrite Ees, <- Lk; apply nth_error_app_len)) as (sl & Esl & Hix & SLOT).
pose proof OPEN as (_ & _ & _ & _ & Hsz & Hcnt & Hlen).
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR.
assert (Hixz : 0 <= Z.of_nat (le_ix e) /\ Z.of_nat (le_ix e) + 1 <= size) by lia.
pose proof (ent_shadowA HIx _ _ _ _ _ _ _ tbl size (le_ix e) HP INtb ltac:(lia) ltac:(lia)) as SHe.
unfold ent_addr in SLOT, Ecur, SHe. subst cur.
set (ea := tbl + 40 * Z.of_nat (le_ix e)) in *.
assert (EAR : tbl <= ea /\ ea + 40 <= tbl + 40 * size) by (subst ea; lia).
assert (EA8 : ea mod 8 = 0) by (subst ea; clear - Hbal; Z.div_mod_to_equations; lia).
shadowN HP x 48 INx SHx. a4l.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(ea + 16, ea + 24)] m) as MU.
pose proof HDR as HDR0. unfold jhdr_cells in HDR. cbn [app fn_obj_to_json_string A4F] in HDR.
stash Hk. stash KEYF. stash OPB. stash OK1. stash HDR0.
reenterA asegs A4L HIx asegs_wx HP.
bstep. bstep. if_false. rewrite ?sxb_zero, ?zxb_zero.
bstep. norm_w32. bstep. if_falsex. bstep. if_falsex.
bstep. asan_chkA.
bstep. bstepz.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
try clear SHx. try clear SHe.
assert (HP2 : HEAPAx A (XBS ++ LB) LM FRS B m2 md) by heap_nowA A4L HIx HP MU WM MI.
assert (AG2 : agree_on asegs (others tbl (XBS ++ LB)) m m2).
{ eapply (agree_others_gen asegs); [exact MU | exact WM |]. intros a' kk Hin Hne.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a' kk HP ltac:(apply in_or_app; left; exact Hin)) as (Hk0 & _ & _ & Hahi' & _).
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tbl (40 * size) a' kk HP INtb2 ltac:(apply in_or_app; left; exact Hin) ltac:(congruence)) as D.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hahi'. cbn. lia. }
pose proof (nodup_app_l' _ _ NDall) as NDX.
assert (NTB : forall k, ~ In (tbl, k) LB).
{ intros kk Hkk. eapply (nodup_prefix_suffix XBS LB tbl (40 * size) kk NDX); [rewrite EX; unfold lh_blocks; in_elem | exact Hkk]. }
assert (HPR2 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp + -112) m m2).
{ eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp + -112)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; apply in_or_app; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; in_sub Hb | right; exact Hb] | clia |].
apply Forall_cons; [cbn [fst snd] | apply Forall_nil]. right; left. exists tbl, (40 * size).
split; [exact INtb2|]. split; [| lia]. intros Hkk. apply in_app_or in Hkk. destruct Hkk as [Hkk|Hkk]; [exact (NTB _ Hkk)|].
apply in_app_or in Hkk. destruct Hkk as [Hkk|Hkk]; [| exfalso; exact (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP INtb2 Hkk)].
exact (nodup_prefix_suffix (XBS ++ LB) LM tbl (40 * size) (40 * size) NDall INtb Hkk). }
unstash KEYF.
assert (OPEN2 : lh_open asegs A4F m2 t tbl size (esk1 ++ with_v e 0 :: esz) (upd svs (le_ix e) (sv_with_v sl 0))).
{ replace (esk1 ++ with_v e 0 :: esz) with (upd es (length kids) (with_v e 0)) by (rewrite Ees, <- Lk; apply upd_app_len').
eapply (lh_open_set_val asegs A4F); [exact OPEN | rewrite Ees, <- Lk; apply nth_error_app_len | exact Esl | lia | exact MU | exact WM | | exact Httb | | ].
- apply Forall_cons; [cbn; subst ea; unfold ent_addr; lia | apply Forall_nil].
- intros y Hy. destruct (KEYF y Hy) as (_ & _ & _ & _ & _ & D). exact D.
- unfold ent_addr. fold ea. assumption. }
stash KEYF.
set (es2 := esk1 ++ with_v e 0 :: esz) in OPEN2.
set (svs2 := upd svs (le_ix e) (sv_with_v sl 0)) in OPEN2.
set (XBS1 := ((x, 48) :: lh_blocks t tbl size es ++ concat KBS1) ++ PBS).
assert (ELB : lh_blocks t tbl size es2 = lh_blocks t tbl size es).
{ subst es2. rewrite Ees. unfold lh_blocks. rewrite !map_app. reflexivity. }
assert (Z2 : zobj asegs A4F m2 x q kids (S nz) t tbl size es2 svs2 XBS1).
{ unstash HDR0. unstash OPB. unstash OK1. subst XBS1. rewrite <- ELB.
eapply (zobj_last_close asegs A4F m m2); [exact Lz | exact Fz | exact OPB | exact HDR0 | exact OK1 | exact OPEN2 | ].
eapply agree_on_incl; [exact AG2 | intros [ba bk] Hb; apply in_others; [rewrite EX; in_sub Hb|]].
intros ->. eapply (nodup_in_ne (XBS ++ LB) [(tbl, 40 * size)] ((t, 56) :: map (fun e1 => (le_k e1, le_kn e1)) es ++ (x, 48) :: concat KBS1 ++ bs ++ PBS ++ LB));
[rewrite EX; hperm | exact NDX | left; reflexivity | in_sub Hb | reflexivity]. }
assert (Hes2 : nth_error es2 (length kids) = Some (with_v e 0)) by (subst es2; rewrite <- Lk; apply nth_error_app_len).
assert (VZ2 : forall j y, (length kids <= j)%nat -> nth_error es2 j = Some y -> le_v y = 0).
{ intros j y Hj Hy. subst es2. rewrite nth_error_app2 in Hy by lia.
destruct (j - length esk1)%nat as [|j'] eqn:Ej; cbn in Hy.
- injection Hy as <-. reflexivity.
- exact (proj1 (Forall_forall _ _) Fz y (nth_error_In _ _ Hy)). }
clear HDR0 OPB OK1 OPEN.

assert (TAIL : forall (mm : word -> option byte) (Am : ASA A4L HIx) (Bm : bud) (mdm : config) (Fm : bvmap 5 word) (fcm : bv 32)
(y1 yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y18 yt3 yt4 yt5 yt6 : word),
HEAPAx Am (XBS1 ++ LB) LM FRS Bm mm mdm ->
zobj asegs A4F mm x q kids (S nz) t tbl size es2 svs2 XBS1 ->
stk asegs mm lo (bv_unsigned sp + -112) -> rw_cells asegs mm ERRNO [C4 errv] ->
512 * Z.of_nat (length XBS1) <= bB Bm ->
spill' mm ->
(forall ms' md' A', NEXT q Fm fcm mm mdm LB Bm (512 * Z.of_nat (length XBS1)) ms' md' A' -> AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx Am T mdm
(MS (mkR y1 SPR gp TP yt0 yt1 yt2 (Z_to_bv 64 x) (Z_to_bv 64 (x + 40)) ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7
y18 (Z_to_bv 64 ea) (Z_to_bv 64 (Z.of_nat (length kids))) (Z_to_bv 64 (Z.of_nat nz + 1))
(Z_to_bv 64 (x / 8 + 2147450885)) SBR (Z_to_bv 64 4) (Z_to_bv 64 (x / 8 + 2147450880)) (Z_to_bv 64 5) CM1 yt3 yt4 yt5 yt6)
Fm (Z_to_bv 64 0x9bf6c) fcm None mm (seg_rom asegs))).
{ intros until yt6. intros HPm Zm STm ERRm BBm [sbsm SPLm] Km.
clear MU WM MI HP HP2 AG2 HPR2 ST ERR Hk BB K OPEN2 SLOT HDR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HPm) as MIm.
pose proof Zm as (pbm & PBSm & KBSm & eskm & eszm & Eesm & Lzm & Fzm & EXm & OPBm & HDRm & OPENm & OKm).
destruct (lh_open_slot asegs A4F _ _ _ _ _ _ _ (length kids) (with_v e 0) OPENm Hes2) as (slm & Eslm & Hixm & SLOTm).
cbn [le_ix le_k le_v with_v] in SLOTm. unfold ent_addr in SLOTm. fold ea in SLOTm.
assert (INx1 : In (x, 48) (XBS1 ++ LB)) by (subst XBS1; in_elem).
assert (INtb1 : In (tbl, 40 * size) (XBS1 ++ LB)) by (subst XBS1; unfold lh_blocks; in_elem).
shadowN HPm x 48 INx1 SHxm.
pose proof (ent_shadowA HIx _ _ _ _ _ _ _ tbl size (le_ix e) HPm INtb1 ltac:(lia) ltac:(lia)) as SHem.
unfold ent_addr in SHem. fold ea in SHem. a4l.
unfold jhdr_cells in HDRm. cbn [app fn_obj_to_json_string A4F] in HDRm.
pose proof (wmono_refl asegs mm) as WM. pose proof (munch_refl [] mm) as MU.
reenterA asegs A4L HIx asegs_wx HPm.
bstep. bstep. if_false. rewrite ?sxb_zero, ?zxb_zero.
bstep. norm_w32. bstep. if_false.
bstep. asan_chkA.
bstep. bstep.
evt_done5.
replace (Z.of_nat nz + 1) with (Z.of_nat (S nz)) by lia.
eapply CONT; [eapply (heapA_client_frame A4L HIx); [exact HPm | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HPm MU); apply Forall_nil | exact WM | exact MIm] | | exact STm | exact ERRm | exact BBm | spl | exact Km].
exists t, tbl, size, es2, svs2. split; [exact Zm|].
intros kids1 kl Ek.
assert (Hj : (length kids1 < length esk1)%nat) by (rewrite Lk, Ek, length_app; cbn; lia).
destruct (nth_error esk1 (length kids1)) as [e'|] eqn:En; [| apply nth_error_None in En; lia].
exists e'. split; [subst es2; rewrite nth_error_app1 by lia; exact En|].
rewrite pv_of_spec, Ek, length_app. cbn [length]. rewrite Nat.add_1_r. cbn [pv_of].
subst es2. rewrite nth_error_app1 by lia. rewrite En. reflexivity. }
bstep.
unstash Hk. destruct k as [c|].
-
destruct Hk as [Hv J].
assert (J2 : jval asegs A4F c m2 bs (le_v e) 1).
{ eapply jval_agree; [exact J | eapply agree_on_incl; [exact AG2|] | apply incl_refl].
intros [ba bk] Hb. apply in_others; [rewrite EX; in_sub Hb|].
intros ->. eapply (nodup_in_ne (XBS ++ LB) [(tbl, 40 * size)] ((t, 56) :: map (fun e1 => (le_k e1, le_kn e1)) es ++ (x, 48) :: concat KBS1 ++ bs ++ PBS ++ LB));
[rewrite EX; hperm | exact NDX | left; reflexivity | in_sub Hb | reflexivity]. }
clear J.
assert (HPc : HEAPAx A (bs ++ XBS1 ++ LB) LM FRS B m2 md) by (eapply (heapA_perm A4L HIx); [exact HP2 | subst XBS1; rewrite EX; hperm | apply Permutation_refl | apply Permutation_refl]).
pose proof (nodup_app_l' _ _ (nodup_app_l' _ _ (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HPc))) as NDbs.
destruct (jval_hdr asegs A4F c m2 bs (le_v e) 1 J2 NDbs) as (cn & tojs_ & pb_ & udel_ & ud_ & rest_ & INc & _ & N48c & _ & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ (le_v e) cn HPc ltac:(apply in_or_app; left; in_sub INc)) as (_ & Hcal & Hclo & Hchi & _). clear tojs_ pb_ udel_ ud_ rest_.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hchi.
if_truex. bstep. bstep. bstep.
evt_done5.
eapply (maybe_free_A_closed HIx) with (s := c) (BS := bs) (LB := XBS1 ++ LB) (x := le_v e) (rc := 1) (lo := lo);
[ exact HPc | lia | lia | exact J2 | .. ]; a4l_goal; rewrite ?unsigned_lit by lia; try first [exact ST | exact ERR | assumption | reflexivity | lia].
all: try (replace (bv_unsigned sp + -112) with (bv_unsigned sp - 112) by lia; rewrite Zminus_mod, SPA; reflexivity).
all: try (intros _; clear - BB EX; rewrite EX in BB; cbn [length app] in BB; rewrite ?length_app in BB; cbn [length] in BB; rewrite ?length_app in BB; unfold blk in *; lia).
intros ms3 md3 A3 (m3 & r & B3 & RS3 & VM3 & ST3 & HPR3 & ERR3 & BD3 & OUT3).
destruct RS3 as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F3 & fc3 & -> & FS3 & FRM3).
a4l. rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in HPR3 by lia.
assert (Z3 : zobj asegs A4F m3 x q kids (S nz) t tbl size es2 svs2 XBS1).
{ eapply (zobj_agree asegs A4F (XBS1 ++ LB)); [exact Z2 | eapply (agree_of_heap_pres asegs A4H); [exact HPR3 | reflexivity | intros b Hb; apply in_or_app; left; exact Hb] | intros b Hb; in_sub Hb]. }
assert (HPR23 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp + -112) m m3).
{ eapply heap_pres_trans; [hpw HPR2 | eapply heap_pres_weaken; [exact HPR3 | lia | intros b Hb; apply in_or_app; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; in_sub Hb | right; exact Hb]]]. }
clear MU WM MI HP2 HP AG2 ST J2 HPc SLOT HDR.
destruct OUT3 as [(_ & Habs & _) | [(Er & _ & BB3 & HP3) | (Er & _ & ZC & BB3 & HP3)]]; [lia | |]; rewrite ?unsigned_lit in Er by lia; subst r.
+
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI.
pose proof (munch_refl [] m3) as MU. pose proof (wmono_refl asegs m3) as WM.
reenterA asegs A4L HIx asegs_wx HP3.
bstep. bstep. if_falsex.
evt_done5.
eapply TAIL; [eapply (heapA_client_frame A4L HIx); [exact HP3 | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP3 MU); apply Forall_nil | exact WM | exact MI] | exact Z3 | exact ST3 | exact ERR3 | | spl |].
* clear - BB BB3 EX. subst XBS1. rewrite EX in BB. cbn [length app] in *. rewrite ?length_app in *. cbn [length] in *. rewrite ?length_app in *. unfold blk in *. lia.
* intros ms' md' A' NP. apply K. eapply next_postA_w; [exact FS3 | exact FRM3 | exact VM3 | hpw HPR23 | exact BB3 | exact BD3 | exact NP |].
clear - EX. subst XBS1. rewrite EX. cbn [length app]. rewrite ?length_app. cbn [length]. rewrite ?length_app. unfold blk. lia.
+
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI.
pose proof (munch_refl [] m3) as MU. pose proof (wmono_refl asegs m3) as WM.
reenterA asegs A4L HIx asegs_wx HP3.
bstep. bstep. if_truex.
ub_skip.
evt_done5.
destruct c as [| | | |ck|ck]; cbn in ZC; try contradiction.
all: eapply (descend_objA HIx sp gp lo errv LM FRS LO LOS SPA HT DEL _ kids KD HEADK) with (e2 := with_v e 0);
[exact HP3 | exact ZC | exact Z3 | exact Hes2 | exact ST3 | exact ERR3 | | spl |].
all: try (clear - BB BB3 EX; subst XBS1; rewrite EX in BB; cbn [length app] in *; rewrite ?length_app in *; cbn [length] in *; rewrite ?length_app in *; unfold blk in *; lia).
all: intros ms' md' A' NP; apply K; eapply next_postA_w; [exact FS3 | exact FRM3 | exact VM3 | hpw HPR23 | | exact BD3 | exact NP |];
[ instantiate (1 := 0); lia
| clear - EX; subst XBS1; rewrite EX; cbn [length app]; rewrite ?length_app; cbn [length]; rewrite ?length_app; unfold blk; lia ].
-
destruct Hk as [Hv Ebs]. rewrite Hv. if_false. bstep.
evt_done5.
assert (HPn : HEAPAx A (XBS1 ++ LB) LM FRS B m2 md) by (eapply (heapA_perm A4L HIx); [exact HP2 | subst XBS1 bs; rewrite EX; hperm | apply Permutation_refl | apply Permutation_refl]).
eapply TAIL; [exact HPn | exact Z2 | exact ST | assumption | | spl |].
+ clear - BB EX Ebs. subst XBS1 bs. rewrite EX in BB. cbn [length app] in *. rewrite ?length_app in *. cbn [length] in *. rewrite ?length_app in *. unfold blk in *. lia.
+ intros ms' md' A' NP. apply K. eapply next_postA_w; [apply fsaved_refl | intros Hf; exact Hf | apply model_vm_only_refl | hpw HPR2 | | | exact NP |].
* instantiate (1 := 0). lia.
* lia.
* clear - EX Ebs. subst XBS1 bs. rewrite EX. cbn [length app]. rewrite ?length_app. cbn [length]. rewrite ?length_app. unfold blk. lia.
Qed.
End BodyOA.
End RC__1.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn QKQo Q8tj.
Import QSL3.
Import QnCn.Mq0.
Import Q6WR Q6WR.Mq0 QrPc. Import QeuE.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqg QsKa.Mqc Q30W.Mq4 QI6Z.Mq3 QsKa.Mqe QnDr.Mq4 QkXq.Mq7 Qiiq.Mqb QeVJ.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section DescA2.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Variables (sp gp : word) (lo : Z) (errv : word) (LM : list blk) (FRS : list frame).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp + -112 - 4352.
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HT : bv_unsigned sp <= hiA_top A4L HIx.

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

Ltac shadowN HP a n Hin SH :=
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ a n HP Hin) as SH;
unfold shad in SH; apply shadow_ro_cells in SH;
let cs := eval cbv in (shadow_cells n) in change (shadow_cells n) with cs in SH.
Ltac shadow48 HP a Hin SH := shadowN HP a 48 Hin SH.

Lemma descend_arrA : forall c kids,
desc_stmtA HIx sp gp lo errv LM FRS c -> head_stmt' false kids ->
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (LB XBS1 bs : list blk) (x q v : Z) (T : TSet)
(nz : nat) (a arr size : Z),
HEAPAx A (bs ++ XBS1 ++ LB) LM FRS B m md ->
zomb asegs A4F c m v bs ->
zarr asegs A4F m x q kids (S nz) a arr size XBS1 ->
stk asegs m lo (bv_unsigned sp + -112) -> rw_cells asegs m ERRNO [C4 errv] ->
512 * (Z.of_nat (length bs) + Z.of_nat (length XBS1)) <= bB B ->
spill' m ->
(forall ms' md' A', NEXT q F1 fc1 m md LB B (512 * (Z.of_nat (length bs) + Z.of_nat (length XBS1))) ms' md' A' -> AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR x1 SPR gp TP t0 t1 t2 (Z_to_bv 64 x) (Z_to_bv 64 (x + 40)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 v) x19 (Z_to_bv 64 (Z.of_nat (length kids))) (Z_to_bv 64 (Z.of_nat nz + 1))
(Z_to_bv 64 (x / 8 + 2147450885)) SBR (Z_to_bv 64 4) (Z_to_bv 64 (x / 8 + 2147450880)) (Z_to_bv 64 5) CM1 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x9c068) fc1 None m (seg_rom asegs)).
Proof.
intros c kids KD HK. intros until size. intros HP ZC Z ST ERR BB [sbs SPL] K.
unfold_consts. word_range sp SPW.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
destruct Z as (pb & PBS & KBS & ps & EX1 & OPB & HDR & AL & OK).
pose proof (okids_len _ _ _ _ _ _ OK) as [L _].
destruct (zomb_zhead HIx sp gp lo errv LM FRS c m v bs ZC KD) as (isobjc & ck & ZCH & HC). clear ZC KD.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND0. pose proof (nodup_app_l' _ _ ND0) as ND.
destruct (zhead_hdr isobjc m v 0 ck bs ZCH (nodup_app_l' _ _ ND)) as (pbc & cfc & INv & HDRC & CLOSEC).
assert (INv' : In (v, 48) (bs ++ XBS1 ++ LB)) by in_sub INv.
assert (INx : In (x, 48) (bs ++ XBS1 ++ LB)) by (rewrite EX1; in_elem).
assert (INa : In (a, 32) (bs ++ XBS1 ++ LB)) by (rewrite EX1; in_elem).
assert (INr : In (arr, 8 * size) (bs ++ XBS1 ++ LB)) by (rewrite EX1; in_elem).
assert (INv2 : In (v, 48) ((bs ++ XBS1 ++ LB) ++ LM)) by (apply in_or_app; left; exact INv').
assert (INx2 : In (x, 48) ((bs ++ XBS1 ++ LB) ++ LM)) by (apply in_or_app; left; exact INx).
assert (INa2 : In (a, 32) ((bs ++ XBS1 ++ LB) ++ LM)) by (apply in_or_app; left; exact INa).
assert (INr2 : In (arr, 8 * size) ((bs ++ XBS1 ++ LB) ++ LM)) by (apply in_or_app; left; exact INr).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ v 48 HP INv2) as (_ & Hval & Hvlo & Hvhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ v 48 HP INv2) as Hvimg.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ x 48 HP INx2) as (_ & Hxal & Hxlo & Hxhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ x 48 HP INx2) as Hximg.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a 32 HP INa2) as (_ & Haal & Halo & Hahi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ a 32 HP INa2) as Haimg.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ arr (8 * size) HP INr2) as (Hr0 & Hral & Hrlo & Hrhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ arr (8 * size) HP INr2) as Hrimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hvhi, Hxhi, Hahi, Hrhi.
assert (NVX : forall k, ~ In (v, k) (XBS1 ++ LB)) by (intros k; exact (nodup_prefix_suffix bs (XBS1 ++ LB) v 48 k ND INv)).
assert (Hxv : x <> v) by (intros ->; apply (NVX 48); rewrite EX1; in_elem).
assert (Hva : v <> a) by (intros E; apply (NVX 32); rewrite E, EX1; in_elem).
assert (Hvr : v <> arr) by (intros E; apply (NVX (8 * size)); rewrite E; rewrite EX1; in_elem).
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ x 48 v 48 HP INx2 INv2 Hxv) as Dxv.
assert (HPal : HEAPAx A ((a, 32) :: (arr, 8 * size) :: (x, 48) :: concat KBS ++ PBS ++ bs ++ LB) LM FRS B m md).
{ eapply (heapA_perm A4L HIx); [exact HP | rewrite EX1; hperm | apply Permutation_refl | apply Permutation_refl]. }
destruct (blocks2A HIx _ _ _ _ _ _ _ _ _ _ _ HPal) as (_ & _ & Har).
assert (Hxa : x <> a).
{ intros ->. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HPal) as ND2. cbn [map blk_addr fst app] in ND2.
inversion ND2 as [|y l Hn1 ND3]; subst. apply Hn1. right. left. reflexivity. }
assert (Hxr : x <> arr).
{ intros ->. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HPal) as ND2. cbn [map blk_addr fst app] in ND2.
inversion ND2 as [|y l Hn1 ND3]; subst. inversion ND3 as [|y' l' Hn2 ND4]; subst. apply Hn2. left. reflexivity. }
clear HPal.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ v 48 a 32 HP INv2 INa2 Hva) as Dva.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ v 48 arr (8 * size) HP INv2 INr2 Hvr) as Dvr.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ x 48 a 32 HP INx2 INa2 Hxa) as Dxa.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ x 48 arr (8 * size) HP INx2 INr2 Hxr) as Dxr.
shadow48 HP v INv' SHv.
shadow48 HP x INx SHx.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ v 48 0 v 48 HP INv' ltac:(lia) INv2) as SEPv0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ v 48 5 v 48 HP INv' ltac:(cbn; lia) INv2) as SEPv5.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ x 48 0 v 48 HP INx ltac:(lia) INv2) as SEPx0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ x 48 5 v 48 HP INx ltac:(cbn; lia) INv2) as SEPx5.
a4l.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(v + 24, v + 40)] m) as MU.
unfold jhdr_cells in HDRC. cbn [app] in HDRC. unfold jhdr_cells in HDR. cbn [app fn_arr_to_json_string A4F] in HDR.
stash Dxa. stash Dxr. stash Dva. stash Dvr. clear GOT CELL.
reenterA asegs A4L HIx asegs_wx HP.
bstep. asan_chkA.
bstep.
bstep. asan_chkA.
bstepz.
bstep. bstep. if_false. rewrite ?sxb_zero, ?zxb_zero.
bstep. bstep. if_false. rewrite ?sxb_zero, ?zxb_zero.
bstep. norm_w32. bstep. bstep. if_true.
bstep. bstep. bstep.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
assert (HP1 : HEAPAx A (bs ++ XBS1 ++ LB) LM FRS B m1 md) by heap_nowA A4L HIx HP MU WM MI.
assert (AGV : agree_on asegs (others v (bs ++ XBS1 ++ LB)) m m1).
{ eapply (agree_others_gen asegs); [exact MU | exact WM |]. intros a' k Hin Hne.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a' k HP ltac:(apply in_or_app; left; exact Hin)) as (Hk & _ & _ & Hahi' & _).
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ v 48 a' k HP INv2 ltac:(apply in_or_app; left; exact Hin) ltac:(congruence)) as D.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hahi'. cbn. lia. }
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
assert (AL1 : alist asegs A4F m1 [(a, 32); (arr, 8 * size)] a (ps ++ repeat 0 (S nz))).
{ eapply (alist_agree asegs A4F); [exact AL | exact AGX | intros b Hb; rewrite EX1; in_sub Hb]. }
clear CLOSEC SHv SHx SEPv0 SEPv5 SEPx0 SEPx5.
match goal with H : rw_cells _ m1 v _ |- _ => clear H end.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI1.
shadowN HP1 a 32 INa SHa1.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ arr (8 * size) HP1 INr) as SHr1. unfold shad in SHr1. a4l.
clear MU WM. pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP1) as [GOT1 CELL1]. a4l.
pose proof (wmono_refl asegs m1) as WM. pose proof (munch_refl [(lo, bv_unsigned sp + -112); (a, a + AL_SZ); (arr, arr + 8 * size)] m1) as MU.
pose proof (nodup_app_l' _ _ (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP1)) as ND1.
assert (NEa : forall bb kk, In (bb, kk) (bs ++ (x, 48) :: concat KBS ++ PBS ++ LB) -> a <> bb /\ arr <> bb).
{ intros bb kk Hb. split.
- eapply (nodup_in_ne (bs ++ XBS1 ++ LB) [(a, 32); (arr, 8 * size)] (bs ++ (x, 48) :: concat KBS ++ PBS ++ LB)); [rewrite EX1; hperm | exact ND1 | in_elem | exact Hb].
- eapply (nodup_in_ne (bs ++ XBS1 ++ LB) [(a, 32); (arr, 8 * size)] (bs ++ (x, 48) :: concat KBS ++ PBS ++ LB)); [rewrite EX1; hperm | exact ND1 | in_elem | exact Hb]. }
stash Hvimg. stash Hximg. stash Dxv. stash NVX. stash AGV. stash AGX. stash NEa. stash ZCH1. stash OPB. stash OK.
unstash Dxa. unstash Dxr.
callA (array_list_del_idx_A (Z_to_bv 64 0x9be3c) SPR gp TP (Z_to_bv 64 x) (Z_to_bv 64 (x + 40)) (Z_to_bv 64 v) x19
(Z_to_bv 64 (Z.of_nat (length kids))) (Z_to_bv 64 (Z.of_nat nz + 1)) (Z_to_bv 64 (x / 8 + 2147450885)) SBR (Z_to_bv 64 4)
(Z_to_bv 64 (x / 8 + 2147450880)) (Z_to_bv 64 5) CM1 F1 fc1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 lo _ a arr size ps (repeat 0 (S nz))).
all: try (unfold small_pre; rewrite ?unsigned_lit by lia; split; [exact MI1|]; split; [assumption|]; split; [lia|]; split; [lia|]; split; [exact GOT1|]; split; [exact CELL1|];
unfold alloc_ceiling, sp_window_lo, stack_max_size; lia).
all: try (rewrite ?unsigned_lit by lia; lia).
all: try (eapply (asan_rt_ok_of_HEAPA HIx); exact HP1).
all: try exact AL1. all: try apply Forall_repeat0. all: try exact Har.
all: try (unfold al_blkA; unfold alloc_ceiling, sp_window_lo, stack_max_size; lia).
all: try exact SHa1. all: try exact SHr1.
all: try (replace (bv_unsigned sp + -112) with (bv_unsigned sp - 112) by lia; rewrite Zminus_mod, SPA; reflexivity).
all: try (rewrite L; reflexivity).
all: try (apply f_equal; rewrite repeat_length; lia).
all: try reflexivity.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
match goal with H : mem_inv asegs m4 |- _ => rename H into MI4 end.
match goal with H : stk asegs m4 _ _ |- _ => rename H into ST4 end.
match goal with H : alist _ _ m4 _ _ _ |- _ => rename H into AL4 end.
rename MU into MU4. rename WM into WM4.
unstash Hvimg. unstash Hximg. unstash Dxv. unstash NVX. unstash AGV. unstash AGX. unstash NEa. unstash ZCH1. unstash OPB. unstash OK.
assert (AG4 : agree_on asegs (bs ++ (x, 48) :: concat KBS ++ PBS ++ LB) m1 m4).
{ eapply (agree_of_munch asegs); [exact MU4 | exact WM4 |]. intros bb kk Hb.
assert (Hb' : In (bb, kk) ((bs ++ XBS1 ++ LB) ++ LM)) by (apply in_or_app; left; rewrite EX1; in_sub Hb).
destruct (NEa bb kk Hb) as [N1 N2].
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ bb kk HP1 Hb') as (Hk0 & _ & _ & Hbhi & _). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hbhi.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ a 32 bb kk HP1 INa2 Hb' N1) as D1.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ arr (8 * size) bb kk HP1 INr2 Hb' N2) as D2.
cbn. clear - D1 D2 Hbhi Hk0 LO LOS SPW. lia. }
assert (HP4 : HEAPAx A (bs ++ XBS1 ++ LB) LM FRS B m4 md) by heap_nowA A4L HIx HP1 MU4 WM4 MI4.
assert (HPR4 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp + -112) m1 m4).
{ eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp + -112)); [exact MU4 | exact WM4 |].
eapply (client_outsideA A4L HIx); [exact HP1 | intros b Hb; apply in_or_app; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; in_sub Hb | right; exact Hb] | clia |].
apply Forall_cons; [cbn [fst snd]; left; clia |].
apply Forall_cons; [cbn [fst snd]; right; left; exists a, 32; split; [exact INa2|]; split; [| lia] |].
{ intros Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [exact (proj1 (NEa a 32 ltac:(in_sub Hin)) eq_refl) |].
apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [| exfalso; exact (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP1 INa2 Hin)].
exact (nodup_prefix_suffix (bs ++ XBS1 ++ LB) LM a 32 32 (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP1) INa Hin). }
apply Forall_cons; [cbn [fst snd]; right; left; exists arr, (8 * size); split; [exact INr2|]; split; [| lia] | apply Forall_nil].
{ intros Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [exact (proj2 (NEa arr (8 * size) ltac:(in_sub Hin)) eq_refl) |].
apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [| exfalso; exact (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP1 INr2 Hin)].
exact (nodup_prefix_suffix (bs ++ XBS1 ++ LB) LM arr (8 * size) (8 * size) (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP1) INr Hin). } }
evt_done5.
eapply (descend_tailA HIx sp gp lo errv LM FRS isobjc false ck kids)
with (XBS2 := ((x, 48) :: [(a, 32); (arr, 8 * size)] ++ concat KBS) ++ PBS) (bs := bs) (LB := LB) (q := q);
[exact HC | exact HK | eapply (heapA_perm A4L HIx); [exact HP4 | rewrite EX1; hperm | apply Permutation_refl | apply Permutation_refl] | | | exact ST4 | assumption | rewrite EX1 in BB; exact BB | spl |].
- eapply (zhead_agree isobjc); [exact ZCH1 | exact AG4 | intros b Hb; in_sub Hb].
- exists a, arr, size. exists pb, PBS, KBS, ps. split; [reflexivity|].
split; [| split; [unfold jhdr_cells; cbn [app fn_arr_to_json_string A4F]; assumption | split; [cbn [repeat]; rewrite app_nil_r; exact AL4|]]].
+ eapply opt_pbuf_agree; [exact OPB | | apply incl_refl]. eapply agree_on_trans.
* eapply agree_on_incl; [exact AGX | intros b Hb; rewrite EX1; in_sub Hb].
* eapply agree_on_incl; [exact AG4 | intros b Hb; in_sub Hb].
+ eapply okids_agree; [exact OK | | apply incl_refl]. eapply agree_on_trans.
* eapply agree_on_incl; [exact AGX | intros b Hb; rewrite EX1; in_sub Hb].
* eapply agree_on_incl; [exact AG4 | intros b Hb; in_sub Hb].
- intros ms' md' A' NP. apply K. eapply next_postA_w; [apply fsaved_refl | intros Hf; exact Hf | apply model_vm_only_refl | | | | exact NP |].
+ eapply heap_pres_trans; [hpw HPR1 | hpw HPR4].
+ instantiate (1 := 0). lia.
+ lia.
+ rewrite EX1. lia.
Qed.
End DescA2.
End RC__1.
End Mq4.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLLZ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QAIk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QAIk.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qiiq.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QeVJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QeVJ.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section InsertTailA.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis OBL_AMEMSET : amemset_spec_A HIx.

Variables (sp gp tp : word) (s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (t tbl size k v : Z) (es : list lent) (svs : list slotv) (ffn : Z) (lo : Z).
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

Definition ins_tail_postA (cnt : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists (g : nat) (sg : slotv) (ixl : nat) (sl : slotv) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) m',
(g < length svs)%nat /\ nth_error svs g = Some sg /\ is_free sg /\ ~ In g (map le_ix es) /\
(es <> [] -> exists jl el, nth_error es jl = Some el /\ (S jl = length es)%nat /\ ixl = le_ix el /\ nth_error svs ixl = Some sl) /\
ms' = MS (mkR rac sp gp tp x5 x6 x7 s0c s1c (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
s2c s3c s4c s5c s6c s7c s8c s9c s10 s11 x28 x29 x30 x31)
F (ret_pc rac) fc None m' (seg_rom asegs)
/\ munch [(t, t + 56); (tbl, tbl + 40 * size); (lo, bv_unsigned sp)] m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m'
/\ rw_cells asegs m' t (hdr_cellsA tbl ffn size (cnt + 1) (match es with [] => ent_addr tbl g | _ => hd_of tbl es end) (ent_addr tbl g))
/\ lh_slots asegs m' tbl (ins_svs svs g sg k v (hd_of tbl es) (tl_of tbl es) ixl sl tbl)
/\ stk asegs m' lo (bv_unsigned sp).

Lemma lh_insert_tailA :
forall (h cnt : Z) (x1 x5 x6 x7 a1 a5 a6 a7 x18 x19 x23 x24 x25 x28 x29 x30 x31 : word) (m : word -> option byte) (junk8 : list byte),
0 <= h < 2^64 -> In size lf_sizes -> Z.of_nat (length svs) = size -> cnt = Z.of_nat (length es) -> cnt < size ->
lh_link tbl es svs -> lh_keys asegs m es -> 0 <= k < 2^64 -> 0 <= v < 2^64 -> 0 <= ffn < 2^64 ->
0 <= t -> t + 56 <= lo -> 0 < tbl -> tbl + 40 * size <= lo -> (t + 56 <= tbl \/ tbl + 40 * size <= t) -> t mod 16 = 0 -> tbl mod 16 = 0 ->
mem_inv asegs m ->
munch [(t, t + 56); (tbl, tbl + 40 * size); (lo, bv_unsigned sp)] m0 m -> wmono asegs m0 m ->
rw_cells asegs m t (hdr_cellsA tbl ffn size cnt (hd_of tbl es) (tl_of tbl es)) ->
lh_slots asegs m tbl svs ->
ins_frameA sp rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c m junk8 -> stk asegs m lo (bv_unsigned sp + -96) ->
evt asegs (ins_tail_postA cnt m)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (Z_to_bv 64 (t + 4)) (Z_to_bv 64 k)
(Z_to_bv 64 t) a1 (Z_to_bv 64 v) (Z_to_bv 64 h) (Z_to_bv 64 0) a5 a6 a7
x18 x19 (Z_to_bv 64 SB0) (Z_to_bv 64 (t / 8 + SB0)) (Z_to_bv 64 (t / 8 + SB0)) x23 x24 x25 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xa23f8) fc None m (seg_rom asegs)).
Proof.
intros until junk8. intros Hh Hsz Hlen Hcnt Hcs LINK KEYS Hk Hv Hffn Ht0 Ht Hb0 Hb SEP Hal16 Hbal16 MI MU WM HDR SL FR ST.
pose proof (lf_size_range size Hsz) as HSR. word_range sp SPR. unfold_consts. unfold hdr_cellsA in HDR.
pose proof FR as FR0. unfold ins_frameA in FR.
pose proof LINK as (LK1 & LK2 & LK3 & LK4).

pose proof (heapA_nowS HIx sp t tbl size lo m0 md A LB LM FRS B0 HP0 INt INb LO HT m MU WM MI) as HPc.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ t 56 HPc INt) as SHt. unfold shad in SHt. apply shadow_ro_cells in SHt.
change (shadow_cells 56) with [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] in SHt.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ t 56 6 t 56 HPc INt ltac:(cbn; lia) ltac:(apply in_or_app; left; exact INt)) as SPt6.
pose proof (tbl_shadowA HIx _ _ _ _ _ _ _ tbl size HPc INb ltac:(lia)) as TSH.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ tbl (40 * size) HPc ltac:(apply in_or_app; left; exact INb)) as (_ & _ & _ & Hbhi & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tbl (40 * size) (5 * size - 1) t 56 HPc INb ltac:(Z.div_mod_to_equations; nia) ltac:(apply in_or_app; left; exact INt)) as SPbl.
cbn [hl_sb hl_segs hl_img_lo hl_img_hi hla_base A4L A4H] in SHt, SPt6, TSH, SPbl. unfold A_SB in *.
assert (XSt : t / 8 + SB0 + 7 <= rc_ceil) by lia.
assert (TSHhi : tbl / 8 + SB0 + 5 * size <= rc_ceil) by lia.
clear SPt6 SPbl HPc.
step. rewrite ?sxb_zero, ?zxb_zero. step. if_false.
step. step. step. sh_norm. rewrite (div8_add t 24) by lia. change (24 / 8) with 3. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false.
step. norm_sx32. step. step. rewrite remu_lit by lia.
pose proof (Z.mod_pos_bound h size ltac:(lia)) as HM. set (n := h mod size) in *.
destruct (nth_error svs (Z.to_nat n)) as [sn|] eqn:Esn.
2:{ exfalso. apply nth_error_None in Esn. lia. }
pose proof (SL _ _ Esn) as C. unfold ent_addr, slot_cells in C. rewrite Z2Nat.id in C by lia.
pose proof (bytes_at_repeat_sub asegs m _ _ _ (Z.to_nat (5 * n)) 1 TSH ltac:(lia)) as SH1.
apply ro_cells_of_repeat in SH1. cbn [map repeat] in SH1. rewrite Z2Nat.id in SH1 by lia.
step. step. rewrite (unsigned_lit n) by lia. step.
replace (tbl + n * 40) with (tbl + 40 * n) by lia. remember (tbl + 40 * n) as Bn eqn:EB.
assert (EB8 : Bn mod 8 = 0) by (subst Bn; Z.div_mod_to_equations; lia).
replace (tbl / 8 + SB0 + 5 * n) with (Bn / 8 + SB0) in SH1 by (subst Bn; Z.div_mod_to_equations; lia).
step. step. sh_norm. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false.
step. subst Bn.
clear SH1.

assert (CONT : forall (gz : Z) (sgz : slotv) (x6' x7' : word) (a1' : word) (a3v t0v : Z) (mq : word -> option byte),
mq = m ->
0 <= gz < size -> nth_error svs (Z.to_nat gz) = Some sgz -> is_free sgz -> a1' = Z_to_bv 64 (tbl + gz * 40) ->
evt asegs (ins_tail_postA cnt m)
(MS (ins_regsA sp gp tp x18 x19 x23 x24 x25 s10 s11 t tbl size k v 0 x1 x6' x7' a1' a3v gz t0v x28 x29 x30 x31)
F (Z_to_bv 64 0xa2488) fc None mq (seg_rom asegs))).
{ intros gz sgz x6' x7' a1' a3v t0v mq -> Hgz Esgz FREEz ->.
set (g := Z.to_nat gz).
assert (NIN : ~ In g (map le_ix es)).
{ intros IN. apply in_map_iff in IN as (e & Hix & He). destruct (In_nth_error _ _ He) as [j Hj].
destruct (LK1 j e Hj) as (s' & Es' & Ek & _). rewrite Hix in Es'. unfold g in Es'. rewrite Esgz in Es'. injection Es' as <-.
destruct (LK4 e He) as (K0 & KF & _ & _). unfold is_free, LH_EMPTYv, LH_FREEDv in FREEz. unfold LH_FREEDv in KF.
destruct (lh_key_bytes asegs m es e KEYS He) as (_ & _ & KL). destruct FREEz; lia. }
assert (TL : exists ixl sl,
((hd_of tbl es = 0 /\ tl_of tbl es = 0) \/ (hd_of tbl es <> 0 /\ tl_of tbl es = ent_addr tbl ixl /\ nth_error svs ixl = Some sl /\ ixl <> Z.to_nat gz /\ 0 <= hd_of tbl es < 2^64))
/\ (es <> [] -> exists jl el, nth_error es jl = Some el /\ (S jl = length es)%nat /\ ixl = le_ix el /\ nth_error svs ixl = Some sl)).
{ destruct es as [|e0 es'] eqn:EES.
- exists 0%nat, sgz. split; [left; split; reflexivity | intros X; exfalso; apply X; reflexivity].
- rewrite <- EES in *.
assert (HL : (length es - 1 < length es)%nat) by (rewrite EES; cbn; lia).
destruct (nth_error es (length es - 1)) as [el|] eqn:El; [| exfalso; apply nth_error_None in El; lia].
destruct (LK1 _ _ El) as (sl & Esl & _).
destruct (LK1 0%nat e0 ltac:(rewrite EES; reflexivity)) as (s0' & Es0 & _).
pose proof (proj1 (nth_error_Some svs (le_ix e0)) ltac:(rewrite Es0; discriminate)) as Hix0.
pose proof (proj1 (nth_error_Some svs (le_ix el)) ltac:(rewrite Esl; discriminate)) as Hixl.
exists (le_ix el), sl. split.
+ right. assert (HD0 : hd_of tbl es = ent_addr tbl (le_ix e0)) by (rewrite EES; reflexivity). rewrite !HD0. unfold ent_addr.
split; [lia|]. split; [rewrite (tl_of_last tbl es (length es - 1) el El ltac:(lia)); reflexivity|]. split; [exact Esl|]. split; [| lia].
intros X. apply NIN. unfold g. rewrite <- X. apply in_map. eapply nth_error_In. exact El.
+ intros _. exists (length es - 1)%nat, el. repeat split; try assumption. lia. }
destruct TL as (ixl & sl & TAIL & LAST).
eapply evt_mono.
- eapply (lh_store_blockA HIx OBL_AMEMSET sp gp tp s10 s11 F fc t tbl size k v svs ffn lo rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c
m0 md A LB LM FRS B0 HP0 INt INb LO LOS SPA HT gz sgz cnt (hd_of tbl es) (tl_of tbl es) ixl sl _ _ _ _ _ _ _ _ _ _ _ _ a3v t0v);
first [exact Esgz | exact Hsz | exact Hlen | exact TAIL | exact MI | exact HDR | exact SL | exact FR0 | exact ST | exact SEP | exact Hffn | exact MU | exact WM | lia | idtac].
all: try lia.
- cbv beta. intros ms' (x5' & x6'' & x7'' & x11' & x12' & x13' & x14' & x15' & x16' & x17' & x28' & x29' & x30' & x31' & m' & -> & MU' & WM' & MI' & HDR' & SL' & ST').
unfold ins_tail_postA. exists g, sgz, ixl, sl, x5', x6'', x7'', x11', x12', x13', x14', x15', x16', x17', x28', x29', x30', x31', m'.
assert (GZ : Z.of_nat g = gz) by (unfold g; lia).
try rewrite GZ.
split; [unfold g; lia|]. split; [exact Esgz|]. split; [exact FREEz|]. split; [exact NIN|]. split; [exact LAST|].
split; [reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [| split; [| exact ST']].
+ destruct es; cbn [hd_of] in HDR' |- *; [exact HDR' |]. unfold ent_addr in HDR' |- *.
destruct (Z.eqb_spec (tbl + 40 * Z.of_nat (le_ix l)) 0); [lia | exact HDR'].
+ replace g with (Z.to_nat gz) by reflexivity. exact SL'. }

assert (LIVEK : forall i s, nth_error svs i = Some s -> ~ is_free s -> 0 <= sv_k s < LH_FREEDv).
{ intros i s E NF. destruct (in_dec Nat.eq_dec i (map le_ix es)) as [IN | NI].
- apply in_map_iff in IN as (e & Hix & He). destruct (In_nth_error _ _ He) as [j Hj].
destruct (LK1 j e Hj) as (s' & Es' & Ek & _). rewrite Hix, E in Es'. injection Es' as <-.
destruct (LK4 e He) as (K0 & KF & _ & _). destruct (lh_key_bytes asegs m es e KEYS He) as (_ & _ & KL). rewrite Ek. lia.
- exfalso. apply NF. exact (LK2 i s E NI). }
step.
step.
assert (FD : is_free sn \/ ~ is_free sn).
{ unfold is_free. destruct (Z.eq_dec (sv_k sn) LH_EMPTYv); [left; left; assumption|].
destruct (Z.eq_dec (sv_k sn) LH_FREEDv); [left; right; assumption|]. right. intros [X|X]; contradiction. }
destruct FD as [FRn | NFn].
-
assert (HK : sv_k sn = LH_EMPTYv \/ sv_k sn = LH_FREEDv) by exact FRn. unfold LH_EMPTYv, LH_FREEDv in HK.
unfold bv_ltu. change (bv_unsigned (Z_to_bv 64 (-3))) with 18446744073709551613. rewrite (unsigned_lit (sv_k sn)) by lia. if_true.
apply (CONT n sn _ _ _ (sv_k sn) (-3) m eq_refl); [lia | exact Esn | exact FRn | f_equal; lia].
-
pose proof (LIVEK _ _ Esn NFn) as HKn. unfold LH_FREEDv in HKn.
unfold bv_ltu. change (bv_unsigned (Z_to_bv 64 (-3))) with 18446744073709551613. rewrite (unsigned_lit (sv_k sn)) by lia. if_false.
step. step.
pose proof (lf_thr_lt size Hsz) as Hlt.
destruct (free_slot_exists (map le_ix es) (length svs) LK3 ltac:(rewrite length_map; lia)) as (f & Hf & NIf).
destruct (nth_error svs f) as [sf|] eqn:Esf; [| exfalso; apply nth_error_None in Esf; lia].
pose proof (LK2 f sf Esf NIf) as FRf.
eapply evt_cut.
{ eapply (lh_probe_loopA sp gp tp x18 x19 x23 x24 x25 s10 s11 F fc t tbl size k v 0 svs (Z.to_nat ((Z.of_nat f - n) mod size)) n (Z.of_nat f));
first [exact Hsz | exact Hlen | exact LIVEK | exact MI | exact SL | exact TSH | lia | unfold A_SB; unfold_consts; lia | idtac].
- rewrite Nat2Z.id. exact Esf.
- exact FRf.
- exists sn. split; [exact Esn | exact NFn]. }
cbv beta. intros ms' (g' & sg' & Hg' & Esg' & FRg' & ->).
apply (CONT g' sg' _ _ _ 40 (-2) m eq_refl); [exact Hg' | exact Esg' | exact FRg' | reflexivity].
Qed.
End InsertTailA.
End RC__1.
