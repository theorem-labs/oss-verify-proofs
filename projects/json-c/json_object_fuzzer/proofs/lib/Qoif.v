(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Q5Rg QRjH QHnV QCcH QfLs Q0Ek QJjn Q8tj Qu4M Q7UD Qhd4 Qwm6 QlKV QsKa Q1Y6 Qiiq Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QJjn Q8tj. Import Qu4M.Mq0.
Import Q7UD Qhd4.
Import Qwm6.Mq0 QlKV.Mq7 QsKa.Mq5 QsKa.Mq4 Q1Y6.Mq0 Qiiq.Mq0 QlKV.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition strdup_costB (klen : Z) : Z := 16 * (klen + 1) + 512.

Definition oadd_costB (klen cap cnt : Z) : Z := strdup_costB klen + ins_costB cap cnt.

Definition obj_grownA (cap cnt cap' : Z) : Prop := (cap' = cap /\ cnt < lf_thr cap) \/ (cap' = lh_ns cap /\ lf_thr cap <= cnt).

Definition json_object_object_add_A_entry : Z := 0x9be64.

Section S.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Definition jo_post_framexA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (lo : Z)
(r : Z) (m' : word -> option byte) (ms' : machine_state) (md' : config) : Prop :=
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_presx A4H a4_volatile (LB ++ LM) (bv_unsigned sp) m m' /\
(exists errv', rw_cells asegs m' A_ERRNO [C4 errv']).

Definition jo_object_add_A_stmt (entry stkb : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB OBS VBS LM : list blk) (FRS : list frame) (B : bud) (lo p v k kn : Z) (ks : list byte)
(kids : list (option jshape)) (vs : option jshape) (errv : word),
jo_preA HIx A (OBS ++ VBS ++ LB) LM FRS B m md sp tp ra lo stkb errv -> lh_globA m ->
jval asegs A4F (Sobj kids) m OBS p 1 -> jopt asegs A4F vs m VBS v ->
In (k, kn) LB -> cstr asegs m k kn ks -> kn <= 2^31 ->
frm0 fc ->
Z.of_nat (length FRS) < 4096 ->
a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 k -> a2 = Z_to_bv 64 v ->
oadd_costB (Z.of_nat (length ks)) (obj_capA OBS) (Z.of_nat (length kids)) <= bB B ->
512 * Z.of_nat (length OBS) <= bB B ->
0 <= bD B ->
(forall ms' md' m' r (A' : ASA A4L HIx) (B' : bud),
jo_post_framexA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB (LM ++ fr_ivs A4L FRS) lo r m' ms' md' ->
lh_globA m' -> bD B <= bD B' ->
((r = 0 /\ exists OBS' kids', jval asegs A4F (Sobj kids') m' OBS' p 1 /\ HEAPAx A' (OBS' ++ LB) LM FRS B' m' md'
/\ Z.of_nat (length kids') <= Z.of_nat (length kids) + 1
/\ okmax kids' <= Z.max (okmax kids) (odep vs)
/\ ( (
Z.of_nat (length kids') = Z.of_nat (length kids) + 1
/\ bB B - oadd_costB (Z.of_nat (length ks)) (obj_capA OBS) (Z.of_nat (length kids)) <= bB B'
/\ Z.of_nat (length OBS') = Z.of_nat (length OBS) + Z.of_nat (length VBS) + 1
/\ obj_grownA (obj_capA OBS) (Z.of_nat (length kids)) (obj_capA OBS')
/\ (forall w wv, jtx (Sobj kids) OBS = Some (w, []) -> jtx_opt vs VBS = Some (wv, []) ->
jtx (Sobj kids') OBS' = Some (w + (key_w (Z.of_nat (length ks) + 1) + wv), [])))
\/ (
Z.of_nat (length kids') = Z.of_nat (length kids)
/\ bB B - 512 * (Z.of_nat (length OBS) + Z.of_nat (length VBS) - Z.of_nat (length OBS')) <= bB B'
/\ Z.of_nat (length OBS') <= Z.of_nat (length OBS) + Z.of_nat (length VBS)
/\ obj_capA OBS' = obj_capA OBS
/\ (forall w wv, jtx (Sobj kids) OBS = Some (w, []) -> jtx_opt vs VBS = Some (wv, []) ->
exists w', jtx (Sobj kids') OBS' = Some (w', []) /\ w' <= w + wv)))) \/
(r = 2^64 - 1 /\ exists REM, jval asegs A4F (Sobj kids) m' OBS p 1 /\ jopt asegs A4F vs m' VBS v
/\ HEAPAx A' (OBS ++ VBS ++ REM ++ LB) LM FRS B' m' md'
/\ bB B - oadd_costB (Z.of_nat (length ks)) (obj_capA OBS) (Z.of_nat (length kids)) <= bB B')) ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

End S.

Definition jo_object_add_A (HIx : heap_iface_A A4L) (HD : Z) := jo_object_add_A_stmt HIx json_object_object_add_A_entry (64 + 96 + 4096 + 128 + HD).

End RC__1.
End Mq0.
From Stdlib Require Permutation.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply QjDH QmZZ Qsw7 QKQo QSL3 QAIk QnCn Q6WR QrPc QeuE Q30W QnDr QkXq QeVJ QhPX QWQx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn QKQo Q8tj.
Import QSL3. Import QAIk.
Import QnCn.Mq0.
Import Q6WR Q6WR.Mq0 QrPc. Import QeuE.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq7 QsKa.Mq3 Q30W.Mq0 QsKa.Mq5 Q30W.Mq2 QlKV.Mq3 QnDr.Mq1 Qiiq.Mq2 QkXq.Mq3 Qiiq.Mq4 QeVJ.Mq0 QhPX.Mq1 QhPX.Mq0 QWQx.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section Loop3A.
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
Notation NEXT := (next_postA HIx sp gp lo errv LM FRS).
Notation head_stmt' := (head_stmtA HIx sp gp lo errv LM FRS).
Notation cont_stmt' := (cont_stmtA HIx sp gp lo errv LM FRS).
Notation body_stmt' := (body_stmtA HIx sp gp lo errv LM FRS).

Ltac shadowN HP a n Hin SH :=
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ a n HP Hin) as SH;
unfold shad in SH; apply shadow_ro_cells in SH;
let cs := eval cbv in (shadow_cells n) in change (shadow_cells n) with cs in SH.

Lemma zcont_len : forall isobj m x q kids nz cur XBS,
zcont isobj m x q kids nz cur XBS -> Z.of_nat (length kids) < 2^62.
Proof.
clear. intros isobj m x q kids nz cur XBS ZC. destruct isobj.
- destruct ZC as (t & tbl & size & es & svs & Z0 & _).
destruct Z0 as (pb & PBS & KBS & esk & esz & Ees & Lz & Fz & EX & OPB & HDR & OPEN & OK).
pose proof (okids_len _ _ _ _ _ _ OK) as [L1 _]. rewrite length_map in L1.
pose proof OPEN as (_ & _ & _ & _ & Hsz & Hcnt & _). pose proof (lf_thr_lt size Hsz). pose proof (lf_size_range size Hsz).
assert (length esk <= length es)%nat by (rewrite Ees, length_app; lia). lia.
- destruct ZC as (a & arr & size & pb & PBS & KBS & ps & EX & OPB & HDR & AL & OK).
pose proof (okids_len _ _ _ _ _ _ OK) as [L1 _].
destruct AL as (arr' & size' & junk & E & Hlen & Hsz & _). rewrite length_app in Hlen. lia.
Qed.

Lemma cont_okA : forall isobj kids,
(forall kids1 kl, kids = kids1 ++ [kl] -> body_stmt' isobj kids1 kl) -> cont_stmt' isobj kids.
Proof.
intros isobj kids BODY. unfold cont_stmtA. intros until cur. intros HP ZC ST ERR BB K.
unfold_consts. word_range sp SPW.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (zcont_len _ _ _ _ _ _ _ _ ZC) as LK.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [] m) as MU.
reenterA asegs A4L HIx asegs_wx HP.
step. step. step.
destruct (snoc_inv_gen kids) as [-> | (kids1 & kl & ->)].
- cbn [length Z.of_nat Z.add]. if_true.
evt_done5.
eapply (pop_okA HIx sp gp lo errv LM FRS LO LOS SPA HT isobj); [exact HP | | exact ST | exact ERR | exact BB | exact K].
destruct isobj; [destruct ZC as (t & tbl & size & es & svs & Z0 & _); exists t, tbl, size, es, svs; exact Z0 | exact ZC].
- rewrite length_app in LK |- *. cbn [length] in LK |- *.
if_falsex.
replace (Z.of_nat (length kids1 + 1) + -1) with (Z.of_nat (length kids1)) by lia.
evt_done5.
eapply (BODY kids1 kl eq_refl); [exact HP | | exact ST | exact ERR | exact BB | exact K].
destruct isobj.
+ destruct ZC as (t & tbl & size & es & svs & Z0 & CUR). destruct (CUR kids1 kl eq_refl) as (e & He & Ec).
exists t, tbl, size, es, svs, e. split; [exact Z0 | split; [exact He | exact Ec]].
+ exact ZC.
Qed.

Lemma head_okA : forall isobj kids,
(forall kids1 kl, kids = kids1 ++ [kl] -> body_stmt' isobj kids1 kl) -> head_stmt' isobj kids.
Proof.
intros isobj kids BODY. unfold head_stmtA. intros until T. intros HP ZH ST ERR BB K.
unfold_consts. word_range sp SPW.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(lo, bv_unsigned sp + -112)] m) as MU.
assert (KW : forall mm (MUm : munch [(lo, bv_unsigned sp + -112)] m mm) (WMm : wmono asegs m mm) ms' md' A',
NEXT q F1 fc1 mm md LB B (512 * Z.of_nat (length XBS)) ms' md' A' -> AJ5 A4L HIx A' T md' ms').
{ intros mm MUm WMm ms' md' A' NP. apply K. eapply next_postA_w; [apply fsaved_refl | intros Hf; exact Hf | apply model_vm_only_refl | | | | exact NP |]; [| instantiate (1 := 0); lia | lia | lia].
eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp + -112)); [exact MUm | exact WMm |].
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; apply in_or_app; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb] | clia |].
apply Forall_cons; [cbn [fst snd]; left; clia | apply Forall_nil]. }
destruct isobj.
- destruct ZH as (t & tbl & size & es & svs & Z0).
pose proof Z0 as (pb & PBS & KBS & esk & esz & Ees & Lz & Fz & EX & OPB & HDR & OPEN & OK).
pose proof (okids_len _ _ _ _ _ _ OK) as [L1 _]. rewrite length_map in L1.
destruct esz; [| cbn in Lz; discriminate]. rewrite app_nil_r in Ees. subst esk.
pose proof OPEN as (HDRT & _ & _ & _ & Hsz & Hcnt & Hlen). unfold lh_hdrf in HDRT.
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR.
assert (HPl : HEAPAx A (lh_blocks t tbl size es ++ ((x, 48) :: concat KBS ++ PBS ++ LB)) LM FRS B m md).
{ eapply (heapA_perm A4L HIx); [exact HP | rewrite EX; hperm | apply Permutation_refl | apply Permutation_refl]. }
destruct (lh_heap_factsA HIx _ _ _ _ _ _ _ _ _ _ _ HPl) as ((Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & Httb & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hbhi. clear HPl.
assert (INx : In (x, 48) (XBS ++ LB)) by (rewrite EX; in_elem).
assert (INt : In (t, 56) (XBS ++ LB)) by (rewrite EX; unfold lh_blocks; in_elem).
assert (INx2 : In (x, 48) ((XBS ++ LB) ++ LM)) by (apply in_or_app; left; exact INx).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ x 48 HP INx2) as (_ & Hxal & Hxlo & Hxhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ x 48 HP INx2) as Hximg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hxhi.
assert (LT : lhtab2 asegs A4F m (lh_blocks t tbl size es) t (map (fun e => (le_k e, le_v e)) es)).
{ exists tbl, size, es, svs. split; [reflexivity|]. split; [reflexivity | exact OPEN]. }
shadowN HP x 48 INx SHx. shadowN HP t 56 INt SHt.
a4l. destruct (proj1 (ro_cells_app asegs m (t / 8 + 2147450880) [C1 (Z_to_bv 8 0)] _) SHt) as [SHt0 _].
unfold jhdr_cells in HDR. cbn [app fn_obj_to_json_string A4F] in HDR.
stash OPB. stash OK. stash Z0.
reenterA asegs A4L HIx asegs_wx HP.
asan_chk0.
step. asan_chkA.
step. norm_w32. step. step. if_false.
step.
callS (lh_table_length_A _ SPR gp TP _ _ _ (Z_to_bv 64 x) (Z_to_bv 64 (x + 40)) (Z_to_bv 64 4) _ _ _ _ _ _ x18 x19 x20 x21 (Z_to_bv 64 (x / 8 + 2147450885)) SBR (Z_to_bv 64 4)
(Z_to_bv 64 (x / 8 + 2147450880)) (Z_to_bv 64 5) CM1 _ _ _ _ F1 fc1 m lo _ (lh_blocks t tbl size es) t (map (fun e => (le_k e, le_v e)) es)).
all: try (unfold small_pre; rewrite ?unsigned_lit by lia; split; [exact MI|]; split; [exact ST|]; split; [lia|]; split; [lia|]; split; [exact GOT|]; split; [exact CELL|];
unfold alloc_ceiling, sp_window_lo, stack_max_size; lia).
all: try exact LT. all: try exact SHt0.
all: try (unfold A_SB; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia).
all: try first [reflexivity | lia].
rewrite length_map.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
match goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
match goal with H : stk asegs m2 _ _ |- _ => rename H into ST2 end.
assert (HP2 : HEAPAx A (XBS ++ LB) LM FRS B m2 md) by heap_nowA A4L HIx HP MU WM MI2.
try clear SHx; try clear SHt; try clear SHt0.
shadowN HP2 x 48 INx SHx. shadowN HP2 t 56 INt SHt. a4l.
step. step. if_false. rewrite ?sxb_zero, ?zxb_zero.
step. step. asan_chkA.
step.
step.
assert (Z2 : zobj asegs A4F m2 x q kids 0 t tbl size es svs XBS).
{ unstash Z0. eapply (zobj_agree asegs A4F (XBS ++ LB)); [exact Z0 | eapply (agree_of_munch asegs); [exact MU | exact WM |] | intros b Hb; in_sub Hb].
intros b kk Hb. pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ b kk HP ltac:(apply in_or_app; left; exact Hb)) as (Hk0 & _ & _ & Hbhi' & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hbhi'. cbn. lia. }
destruct (snoc_inv_gen kids) as [-> | (kids1 & kl & ->)].
+ destruct es; [| cbn in L1; discriminate]. cbn [length Z.of_nat]. if_false. step.
evt_done5.
eapply (pop_okA HIx sp gp lo errv LM FRS LO LOS SPA HT true); [exact HP2 | exists t, tbl, size, (@nil lent), svs; exact Z2 | exact ST2 | assumption | exact BB | exact (KW m2 MU WM)].
+ rewrite length_app in L1. cbn [length] in L1.
if_truex. step. step. step.
replace (Z.of_nat (length es) + -1) with (Z.of_nat (length kids1)) by lia.
destruct (snoc_inv_gen es) as [-> | (es1 & el & ->)]; [cbn in L1; lia|].
rewrite length_app in L1. cbn [length] in L1.
rewrite (tl_of_last tbl (es1 ++ [el]) (length kids1) el) by (first [rewrite nth_error_app2 by lia; replace (length kids1 - length es1)%nat with 0%nat by lia; reflexivity | rewrite length_app; cbn; lia]).
evt_done5. change (Z_to_bv 64 1) with (Z_to_bv 64 (Z.of_nat 0 + 1)).
eapply (BODY kids1 kl eq_refl); [exact HP2 | | exact ST2 | assumption | exact BB | exact (KW m2 MU WM)].
exists t, tbl, size, (es1 ++ [el]), svs, el. split; [exact Z2 | split; [rewrite nth_error_app2 by lia; replace (length kids1 - length es1)%nat with 0%nat by lia; reflexivity | reflexivity]].
- destruct ZH as (a & arr & size & Z0).
pose proof Z0 as (pb & PBS & KBS & ps & EX & OPB & HDR & AL & OK).
pose proof (okids_len _ _ _ _ _ _ OK) as [L1 _]. cbn [repeat] in AL. rewrite app_nil_r in AL.
pose proof AL as (arr' & size' & junk & Eal & Hlen & Hsz & _ & _). injection Eal as E1 E2. assert (size' = size) by lia. subst arr' size'. clear E2.
assert (INx : In (x, 48) (XBS ++ LB)) by (rewrite EX; in_elem).
assert (INa : In (a, 32) (XBS ++ LB)) by (rewrite EX; in_elem).
assert (INr : In (arr, 8 * size) (XBS ++ LB)) by (rewrite EX; in_elem).
assert (INx2 : In (x, 48) ((XBS ++ LB) ++ LM)) by (apply in_or_app; left; exact INx).
assert (INa2 : In (a, 32) ((XBS ++ LB) ++ LM)) by (apply in_or_app; left; exact INa).
assert (INr2 : In (arr, 8 * size) ((XBS ++ LB) ++ LM)) by (apply in_or_app; left; exact INr).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ x 48 HP INx2) as (_ & Hxal & Hxlo & Hxhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ x 48 HP INx2) as Hximg.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a 32 HP INa2) as (_ & Haal & Halo & Hahi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ arr (8 * size) HP INr2) as (Hr0 & Hral & Hrlo & Hrhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hxhi, Hahi, Hrhi.
shadowN HP x 48 INx SHx. shadowN HP a 32 INa SHa. a4l.
unfold jhdr_cells in HDR. cbn [app fn_arr_to_json_string A4F] in HDR.
stash OPB. stash OK. stash Z0.
reenterA asegs A4L HIx asegs_wx HP.
asan_chk0.
step. asan_chkA.
step. norm_w32. step. step. if_true.
step.
callA (array_list_length_A _ SPR gp TP _ _ _ (Z_to_bv 64 x) (Z_to_bv 64 (x + 40)) _ _ _ x18 x19 x20 x21 (Z_to_bv 64 (x / 8 + 2147450885)) SBR (Z_to_bv 64 4)
(Z_to_bv 64 (x / 8 + 2147450880)) (Z_to_bv 64 5) CM1 _ _ _ _ F1 fc1 _ _ _ _ _ m lo _ a arr size ps).
all: try (unfold small_pre; rewrite ?unsigned_lit by lia; split; [exact MI|]; split; [exact ST|]; split; [lia|]; split; [lia|]; split; [exact GOT|]; split; [exact CELL|];
unfold alloc_ceiling, sp_window_lo, stack_max_size; lia).
all: try exact AL. all: try exact SHa.
all: try (unfold al_blkA; unfold alloc_ceiling, sp_window_lo, stack_max_size; lia).
all: try first [reflexivity | lia].
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
match goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
match goal with H : stk asegs m2 _ _ |- _ => rename H into ST2 end.
assert (HP2 : HEAPAx A (XBS ++ LB) LM FRS B m2 md) by heap_nowA A4L HIx HP MU WM MI2.
step. step.
assert (Z2 : zarr asegs A4F m2 x q kids 0 a arr size XBS).
{ unstash Z0. eapply (zarr_agree asegs A4F (XBS ++ LB)); [exact Z0 | eapply (agree_of_munch asegs); [exact MU | exact WM |] | intros b Hb; in_sub Hb].
intros b kk Hb. pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ b kk HP ltac:(apply in_or_app; left; exact Hb)) as (Hk0 & _ & _ & Hbhi' & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hbhi'. cbn. lia. }
destruct (snoc_inv_gen kids) as [-> | (kids1 & kl & ->)].
+ destruct ps; [| cbn in L1; discriminate]. cbn [length Z.of_nat]. if_true.
evt_done5.
eapply (pop_okA HIx sp gp lo errv LM FRS LO LOS SPA HT false); [exact HP2 | exists a, arr, size; exact Z2 | exact ST2 | assumption | exact BB | exact (KW m2 MU WM)].
+ rewrite length_app in L1. cbn [length] in L1.
if_falsex. step. step. step.
replace (Z.of_nat (length ps) + -1) with (Z.of_nat (length kids1)) by lia.
evt_done5. change (Z_to_bv 64 1) with (Z_to_bv 64 (Z.of_nat 0 + 1)).
eapply (BODY kids1 kl eq_refl); [exact HP2 | exists a, arr, size; exact Z2 | exact ST2 | assumption | exact BB | exact (KW m2 MU WM)].
Qed.

Lemma loop_allA : forall isobj kids, kids_descA HIx sp gp lo errv LM FRS kids -> cont_stmt' isobj kids /\ head_stmt' isobj kids.
Proof.
intros isobj kids. induction kids as [|k kids IH] using rev_ind; intros KD.
- split; [apply cont_okA | apply head_okA]; intros kids1 kl E; destruct kids1; discriminate.
- assert (KD1 : kids_descA HIx sp gp lo errv LM FRS kids) by (intros k' Hk'; apply KD; apply in_or_app; left; exact Hk').
destruct (IH KD1) as [CONT HEAD].
assert (B : body_stmt' isobj kids k).
{ destruct isobj; [apply (body_obj_okA HIx sp gp lo errv LM FRS LO LOS SPA HT DEL) | apply (body_arr_okA HIx sp gp lo errv LM FRS LO LOS SPA HT)];
try assumption; apply KD; apply in_or_app; right; left; reflexivity. }
split; [apply cont_okA | apply head_okA]; intros kids1 kl E; apply app_inj_last in E as [<- <-]; exact B.
Qed.

Theorem desc_allA : forall c, desc_stmtA HIx sp gp lo errv LM FRS c.
Proof.
apply jshape_ind2; try (intros; exact I).
- intros kids IH. cbn. apply (proj2 (loop_allA true kids ltac:(intros [c|] Hin; [exact (IH c Hin) | exact I]))).
- intros kids IH. cbn. apply (proj2 (loop_allA false kids ltac:(intros [c|] Hin; [exact (IH c Hin) | exact I]))).
Qed.
End Loop3A.
End RC__1.
End Mq1.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache QWxq_c1 Qfw3_c1 Qc3B QRUw Qvbw QYIF QR2u QrIB QXUB QJZd Qw5U Q1Ey Qvmy Qawr QB6X.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.

Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun QWxq_c1.Mq0 Qfw3_c1.Mq2 Qc3B Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn QKQo Q8tj QRUw.Mq2.
Import QSL3.
Import Qvbw QYIF.
Import QnCn.Mq0 QR2u.

Import Q7UD QXUB.Mq0 Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QsKa.Mq4 QlKV.Mqa QsKa.Mq7 QsKa.Mq0 QJZd.Mq0 QsKa.Mq8 Qw5U.Mq0 QsKa.Mq3 QsKa.Mq2 QlKV.Mq7 QsKa.Mq5 QlKV.Mq5 QlKV.Mq2 QsKa Qiiq.Mq0.

Import Qvmy.Mq0 Qawr.Mq0.
Import Qwm6.Mq2.
Import QB6X.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition DCR_A : Z := 0x9f78c.
Definition DC_A : Z := 0x9f694.
Definition DC_KB : Z := 646.
Definition DC_F : Z := 192.
Definition DC_C : Z := 8720 + 64.
Definition dc_stkA (d : Z) : Z := DC_F + DC_C + DC_F * d.

Section MDcDefs.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Notation wz := (Z_to_bv 64).
Notation jroot_repA := (jroot_rep A4H A4F).

Definition fresA (m : word -> option byte) (CBS : list blk) (q : Z) : Prop :=
(q = 0 /\ CBS = []) \/ (q <> 0 /\ exists s, jval asegs A4F s m CBS q 1).

Definition dc_wtA (r : jroot) (m : word -> option byte) (BS : list blk) (p w : Z) : Prop :=
match r with
| JRtree s => exists Y R, jtx s (BS ++ Y) = Some (w, R)
| JRstrx => exists L, str_lenA m p L /\ 6 * Z.max L 8 + 2 <= w
| JRdblx _ => 9 <= w
| JRnull => False
end.

Definition dc_cwA (d : jroot) (CBS : list blk) (w : Z) : Prop :=
match d with JRtree s' => exists w', jtx s' CBS = Some (w', []) /\ w' <= w | _ => True end.

Definition dc_resA (r : jroot) (BS LB LM : list blk) (FRS : list frame) (D w : Z) (B : bud)
(m' : word -> option byte) (md' : config) (rv : Z) (A' : ASA A4L HIx) (B' : bud) : Prop :=
bD B - w <= bD B' /\
( (rv = 0 /\ exists (d : jroot) (q : Z) (CBS REM : list blk),
copy_of r d /\ dc_cwA d CBS w /\ q <> 0 /\ rw_cells asegs m' D [C8 (wz q)] /\ jroot_repA d m' CBS q /\
bB B - DC_KB * w + 512 * Z.of_nat (length CBS) <= bB B' /\
HEAPAx A' (BS ++ CBS ++ REM ++ LB) LM FRS B' m' md')
\/ (rv = 2^64 - 1 /\ exists (q : Z) (CBS REM : list blk),
rw_cells asegs m' D [C8 (wz q)] /\ fresA m' CBS q /\
bB B - DC_KB * w + 512 * Z.of_nat (length CBS) <= bB B' /\
HEAPAx A' (BS ++ CBS ++ REM ++ LB) LM FRS B' m' md') ).

Definition DCOPY (r : jroot) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB BS LM : list blk) (FRS : list frame) (B : bud) (lo p D w : Z) (errv : word),
HEAPAx A (BS ++ LB) LM FRS B m md -> jroot_repA r m BS p -> r <> JRnull -> lh_globA m ->
rw_cells asegs m D [C8 (wz 0)] -> arg_locA FRS D 8 -> unpoisoned asegs m A_SB D 8 -> D mod 8 = 0 ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - dc_stkA (rdepth r) ->
bv_unsigned sp mod 32 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> tp = wz A_TP -> bv_unsigned ra mod 2 = 0 -> frm0 fc ->
Z.of_nat (length FRS) + (1 + rdepth r) < 4096 ->
dc_wtA r m BS p w -> w < 2^28 -> DC_KB * w <= bB B -> w <= bD B ->
a0 = wz p -> a4 = wz D -> a5 = wz SH_A ->
(forall ms' md' m' rv (A' : ASA A4L HIx) (B' : bud),
jo_post_frameDA D ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md (BS ++ LB) (LM ++ fr_ivs A4L FRS) lo rv m' ms' md' ->
lh_globA m' -> jroot_repA r m' BS p -> dc_resA r BS LB LM FRS D w B m' md' rv A' B' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz DCR_A) fc None m (seg_rom asegs)).
End MDcDefs.

Section MDcBase.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Notation wz := (Z_to_bv 64).
Notation jroot_repA := (jroot_rep A4H A4F).
Notation presxD := (QYIF.heap_presxD A4H).
Hypothesis SHALLOW : shallow_A_stmt HIx.
Hypothesis PUT : put_stmt_A HIx.

Lemma fk1_HEAPA : forall A LBall LM FRS B m md Fr lo SP mX,
HEAPAx A LBall LM ((Fr, 1) :: FRS) B m md -> alloc_ceiling <= lo -> SP <= hiA_top A4L HIx ->
munch [(lo, SP); (Fr, Fr + 120); (Fr / 8 + 2147450880, Fr / 8 + 2147450880 + 16); (6434236, 6434240)] m mX ->
wmono asegs m mX -> mem_inv asegs mX -> HEAPAx A LBall LM ((Fr, 1) :: FRS) B mX md.
Proof.
intros A LBall LM FRS B m md Fr lo SP mX HP LO HT MU WM MI.
assert (INF : In (Fr, 1) ((Fr, 1) :: FRS)) by (left; reflexivity).
eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | exact MI].
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP MU).
apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]].
- left. cbn [fst snd]. lia.
- right; right; right. exists Fr, 1. split; [exact INF|]. left. cbn [fst snd]. rewrite fr_size_1. lia.
- right; right; right. exists Fr, 1. split; [exact INF|]. right. unfold shad. cbn [fst snd hl_sb A4L]. rewrite fr_shadow_len_1. unfold A_SB. lia.
- right; right; left. intros x Hx. cbn [fst snd] in Hx. cbn [hl_scratch A4L A4H hla_base]. unfold A_TP. lia.
Qed.

Lemma fk1_pres : forall A LBall LM FRS B m md Fr lo SP mX,
HEAPAx A LBall LM ((Fr, 1) :: FRS) B m md -> alloc_ceiling <= lo -> alloc_ceiling <= SP ->
munch [(lo, SP); (Fr, Fr + 120); (Fr / 8 + 2147450880, Fr / 8 + 2147450880 + 16); (6434236, 6434240)] m mX ->
wmono asegs m mX -> heap_pres A4H (LBall ++ LM ++ fr_ivs A4L FRS) SP m mX.
Proof.
intros A LBall LM FRS B m md Fr lo SP mX HP LO HSP MU WM.
assert (INF : In (Fr, 1) ((Fr, 1) :: FRS)) by (left; reflexivity).
destruct (own_frame_fresh HIx Fr 1 LBall LBall LM FRS B A m md HP (incl_refl _)) as [OFF OFS].
eapply (heap_pres_of_munch A4H _ SP); [exact MU | exact WM |].
eapply (Q1Ey.client_outsideF HIx A LBall LM ((Fr, 1) :: FRS) B (LBall ++ LM ++ fr_ivs A4L FRS) m md _ SP HP); [| exact HSP |].
- intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. destruct Hb as [H|H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H].
- apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]].
+ left. cbn [fst snd]. lia.
+ right; right; right. exists Fr, 1. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. left. cbn [fst snd]. rewrite fr_size_1. lia.
+ right; right; right. exists Fr, 1. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. right. unfold shad. cbn [fst snd hl_sb A4L]. rewrite fr_shadow_len_1. unfold A_SB. lia.
+ right; right; left. intros x Hx. cbn [fst snd] in Hx. cbn [hl_scratch A4L A4H hla_base]. unfold A_TP. lia.
Qed.

Lemma fk1_HEAPA_W : forall Ax LBall LMx FRx Bx mx md Fr lox SP W mX,
HEAPAx Ax LBall LMx ((Fr, 1) :: FRx) Bx mx md -> alloc_ceiling <= lox -> SP <= hiA_top A4L HIx ->
Forall (fun iv => exists a n, In (a, n) (LBall ++ LMx) /\ a <= fst iv /\ snd iv <= a + n) W ->
munch ([(lox, SP); (Fr, Fr + 120); (Fr / 8 + 2147450880, Fr / 8 + 2147450880 + 16); (6434236, 6434240)] ++ W) mx mX ->
wmono asegs mx mX -> mem_inv asegs mX -> HEAPAx Ax LBall LMx ((Fr, 1) :: FRx) Bx mX md.
Proof.
intros Ax LBall LMx FRx Bx mx md Fr lox SP W mX HP LOx HTx HW MU WM MI.
assert (INF : In (Fr, 1) ((Fr, 1) :: FRx)) by (left; reflexivity).
eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | exact MI].
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP MU).
apply Forall_app. split.
- apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]].
+ left. cbn [fst snd]. lia.
+ right; right; right. exists Fr, 1. split; [exact INF|]. left. cbn [fst snd]. rewrite fr_size_1. lia.
+ right; right; right. exists Fr, 1. split; [exact INF|]. right. unfold shad. cbn [fst snd hl_sb A4L]. rewrite fr_shadow_len_1. unfold A_SB. lia.
+ right; right; left. intros x Hx. cbn [fst snd] in Hx. cbn [hl_scratch A4L A4H hla_base]. unfold A_TP. lia.
- eapply Forall_impl; [| exact HW]. intros iv (a & n & Hin & H1 & H2). right; left. exists a, n. split; [exact Hin | lia].
Qed.

Lemma fk1_pres_W : forall Ax LBall LMx FRx Bx mx md Fr lox SP W L0 mX,
HEAPAx Ax LBall LMx ((Fr, 1) :: FRx) Bx mx md -> alloc_ceiling <= lox -> alloc_ceiling <= SP ->
(forall b, In b L0 -> In b (LBall ++ LMx) \/ In b (fr_ivs A4L FRx)) ->
Forall (fun iv => exists a n, In (a, n) (LBall ++ LMx) /\ ~ In (a, n) L0 /\ a <= fst iv /\ snd iv <= a + n) W ->
munch ([(lox, SP); (Fr, Fr + 120); (Fr / 8 + 2147450880, Fr / 8 + 2147450880 + 16); (6434236, 6434240)] ++ W) mx mX ->
wmono asegs mx mX -> heap_pres A4H L0 SP mx mX.
Proof.
intros Ax LBall LMx FRx Bx mx md Fr lox SP W L0 mX HP LOx HSP HL0 HW MU WM.
assert (INF : In (Fr, 1) ((Fr, 1) :: FRx)) by (left; reflexivity).
destruct (own_frame_fresh HIx Fr 1 LBall LBall LMx FRx Bx Ax mx md HP (incl_refl _)) as [OFF OFS].
assert (OFF' : ~ In (Fr, fr_size 1 - 8) L0).
{ intros H. destruct (HL0 _ H) as [H1 | H1]; apply OFF; [apply in_or_app; left | apply in_or_app; right; apply in_or_app; right].
- apply in_app_or in H1 as [H1|H1]; [exact H1 | exfalso; apply OFF; apply in_or_app; right; apply in_or_app; left; exact H1].
- exact H1. }
assert (OFS' : ~ In (shad A4L Fr, fr_shadow_len 1) L0).
{ intros H. destruct (HL0 _ H) as [H1 | H1]; apply OFS; [rewrite app_assoc; apply in_or_app; left; exact H1 | apply in_or_app; right; apply in_or_app; right; exact H1]. }
eapply (heap_pres_of_munch A4H _ SP); [exact MU | exact WM |].
eapply (Q1Ey.client_outsideF HIx Ax LBall LMx ((Fr, 1) :: FRx) Bx L0 mx md _ SP HP); [| exact HSP |].
- intros b Hb. destruct (HL0 _ Hb) as [H|H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H].
- apply Forall_app. split.
+ apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]].
* left. cbn [fst snd]. lia.
* right; right; right. exists Fr, 1. split; [exact INF|]. split; [exact OFF'|]. split; [exact OFS'|]. left. cbn [fst snd]. rewrite fr_size_1. lia.
* right; right; right. exists Fr, 1. split; [exact INF|]. split; [exact OFF'|]. split; [exact OFS'|]. right. unfold shad. cbn [fst snd hl_sb A4L]. rewrite fr_shadow_len_1. unfold A_SB. lia.
* right; right; left. intros x Hx. cbn [fst snd] in Hx. cbn [hl_scratch A4L A4H hla_base]. unfold A_TP. lia.
+ eapply Forall_impl; [| exact HW]. intros iv (a & n & Hin & Hni & H1 & H2). right; left. exists a, n. split; [exact Hin|]. split; [exact Hni | lia].
Qed.

Lemma dc_blk_notfr : forall Ax LBx LMx FRx Bx mx mdx a n,
HEAPAx Ax LBx LMx FRx Bx mx mdx -> In (a, n) (LBx ++ LMx) -> 0 < n -> ~ In (a, n) (fr_ivs A4L FRx).
Proof.
intros Ax LBx LMx FRx Bx mx mdx a n HP Hin Hn Hf. destruct (Q1Ey.in_fr_ivs _ _ Hf) as (F0 & k & HF & [E | E]).
- injection E as E1 E2. subst a. pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP HF Hin) as DF.
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP HF) as (Hk & _). pose proof (fr_size_pos k ltac:(lia)). lia.
- injection E as E1 E2. subst a.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP Hin) as APP. cbn [hl_sb A4L] in APP. unfold A_SB in APP.
change ((2 ^ 47 - 1) / 8 + 2147450880 + 1) with 17594333495296 in APP.
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP HF) as (Hk & _ & HF0 & HFc & _). pose proof (fr_size_pos k ltac:(lia)) as FSP.
pose proof alloc_ceiling_range as ACR. unfold shad in APP. cbn [hl_sb A4L] in APP. unfold A_SB in APP.
clear - APP HF0 HFc FSP ACR Hn. Z.div_mod_to_equations. lia.
Qed.
Lemma fresA_agree : forall m m' CBS BSx q, fresA m CBS q -> agree_on asegs BSx m m' -> incl CBS BSx -> fresA m' CBS q.
Proof.
intros m m' CBS BSx q [H | (Hq & s & J)] AG INCL; [left; exact H | right]. split; [exact Hq|]. exists s.
eapply (jval_agree asegs A4F); [exact J | exact AG | exact INCL].
Qed.

Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB BS LM : list blk) (FRS : list frame) (B0 : bud) (lo p D w : Z) (r : jroot) (T : TSet).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp - dc_stkA (rdepth r).
Hypothesis SPA : bv_unsigned sp mod 32 = 0.
Hypothesis HT : bv_unsigned sp <= hiA_top A4L HIx.
Hypothesis RA : bv_unsigned ra mod 2 = 0.
Hypothesis FRM0 : frm0 fc.
Hypothesis DLOC : arg_locA FRS D 8.
Hypothesis DAL : D mod 8 = 0.
Hypothesis NN : r <> JRnull.
Hypothesis JR0 : jroot_repA r m0 BS p.
Hypothesis Kont : forall ms' md' m' rv (A' : ASA A4L HIx) (B' : bud),
jo_post_frameDA D ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 (BS ++ LB) (LM ++ fr_ivs A4L FRS) lo rv m' ms' md' ->
lh_globA m' -> jroot_repA r m' BS p -> dc_resA HIx r BS LB LM FRS D w B0 m' md' rv A' B' ->
AJ5 A4L HIx A' T md' ms'.

Definition ASP : Z := bv_unsigned sp + -192.

Definition dc_save (m : word -> option byte) : Prop :=
rw_cells asegs m (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition dc_inv (mc : word -> option byte) (mdc : config) : Prop :=
model_vm_only (cfg_model md0) (cfg_model mdc) /\ presxD D ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 mc /\
stk asegs mc lo ASP /\ dc_save mc /\ lh_globA mc.

Definition dc_resX (LBx : list blk) (BX : bud) (mX : word -> option byte) (rv : Z) : Prop :=
bD B0 - w <= bD BX /\
( (rv = 0 /\ exists (d : jroot) (q : Z) (CBS REM : list blk),
LBx = BS ++ CBS ++ REM ++ LB /\ copy_of r d /\ dc_cwA d CBS w /\ q <> 0 /\ rw_cells asegs mX D [C8 (wz q)] /\ jroot_repA d mX CBS q /\
bB B0 - DC_KB * w + 512 * Z.of_nat (length CBS) <= bB BX)
\/ (rv = 2^64 - 1 /\ exists (q : Z) (CBS REM : list blk),
LBx = BS ++ CBS ++ REM ++ LB /\ rw_cells asegs mX D [C8 (wz q)] /\ fresA mX CBS q /\
bB B0 - DC_KB * w + 512 * Z.of_nat (length CBS) <= bB BX) ).

Definition dc_dst (mc : word -> option byte) (q : Z) : Prop :=
rw_cells asegs mc D [C8 (wz q)] /\ ro_cells asegs mc (D / 8 + 2147450880) [C1 (Z_to_bv 8 0)].

Lemma dc_dfacts : forall A LBx B mx mdx Fr, HEAPAx A LBx LM ((Fr, 1) :: FRS) B mx mdx ->
6574080 <= D /\ D + 16 <= alloc_ceiling /\ (D + 24 <= 2147450880 \/ 17594333495296 <= D) /\ (Fr + 128 <= D \/ D + 16 <= Fr) /\
(forall a k, In (a, k) (LBx ++ LM) -> D + 16 <= a \/ a + k <= D) /\ Fr mod 128 = 0 /\ 0 < Fr /\ Fr + 128 <= alloc_ceiling /\
(Fr + 136 <= 2147450880 \/ 17594333495296 <= Fr) /\
2147450880 <= D / 8 + 2147450880 < 17594333495296 /\ (D / 8 + 2147450880 + 1 <= Fr / 8 + 2147450880 \/ Fr / 8 + 2147450880 + 16 <= D / 8 + 2147450880) /\
2147450880 <= Fr / 8 + 2147450880 /\ Fr / 8 + 2147450880 + 16 <= 17594333495296.
Proof.
intros A LBx B mx mdx Fr HP. destruct DLOC as (Fd & kd & HFd & H1 & H2).
assert (INF : In (Fr, 1) ((Fr, 1) :: FRS)) by (left; reflexivity).
assert (IND : In (Fd, kd) ((Fr, 1) :: FRS)) by (right; exact HFd).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP IND) as (Hkd & HFdal & HFd0 & HFdc & _).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & HFal & HF0 & HFc & _). rewrite fr_size_1 in HFc.
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as HFapp. rewrite fr_size_1 in HFapp. cbn [hl_sb A4L] in HFapp. unfold A_SB in HFapp.
change ((2 ^ 47 - 1) / 8 + 2147450880 + 1) with 17594333495296 in HFapp. pose proof alloc_ceiling_range as ACR.
pose proof (heapA_frame_above A4L HIx _ _ _ _ _ _ _ _ _ HP IND) as HFi. cbn [hl_img_hi hla_base A4L A4H] in HFi.
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP IND) as HFa. cbn [hl_sb A4L] in HFa. unfold A_SB in HFa.
change ((2 ^ 47 - 1) / 8 + 2147450880 + 1) with 17594333495296 in HFa.
assert (FNE : Fr <> Fd).
{ intros ->. pose proof (proj1 (stdpp.base.NoDup_ListNoDup _) (heapA_frame_nodup A4L HIx _ _ _ _ _ _ _ HP)) as ND. cbn in ND.
apply List.NoDup_cons_iff in ND as [Hni _]. apply Hni. exact (in_map fr_base _ _ HFd). }
pose proof (heapA_frame_apart A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF IND FNE) as FAP. rewrite fr_size_1 in FAP, HFal.
pose proof (fr_size_pos kd ltac:(lia)) as FSP.
assert (DX : 6574080 <= D /\ D + 16 <= alloc_ceiling /\ (Fr + 128 <= D \/ D + 16 <= Fr)) by lia. destruct DX as (DX1 & DX2 & DX3).
split; [exact DX1|]. split; [exact DX2|]. split; [lia|]. split; [exact DX3|].
split; [intros a k Hin; pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ a k HP IND Hin); lia |].
split; [exact HFal|]. split; [exact HF0|]. split; [exact HFc|]. split; [lia|].
split; [clear - DX1 DX2 ACR; Z.div_mod_to_equations; lia |].
split; [clear - DX3 HFal HF0 DX1; Z.div_mod_to_equations; lia |].
clear - HF0 HFc ACR. Z.div_mod_to_equations. lia.
Qed.

Lemma dc_dst_munch : forall A LBx B mx mdx Fr mc m' q,
HEAPAx A LBx LM ((Fr, 1) :: FRS) B mx mdx -> dc_dst mc q ->
munch [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (Fr / 8 + 2147450880, Fr / 8 + 2147450880 + 16); (6434236, 6434240)] mc m' -> wmono asegs mc m' ->
dc_dst m' q.
Proof.
intros A LBx B mx mdx Fr mc m' q HP [DC DSH] MU WM.
destruct (dc_dfacts _ _ _ _ _ _ HP) as (D1 & D2 & D3 & D4 & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13). pose proof alloc_ceiling_range as ACR.
set (sh := Fr / 8 + 2147450880) in *. set (dsh := D / 8 + 2147450880) in *.
split.
- eapply (rw_cells_transport asegs); [exact DC | exact MU | exact WM |]. cbn [disjoint_from cells_size csize Nat.add]. clear - D1 D2 D3 D4 D8 D9 D12 D13 LO ACR. lia.
- eapply (ro_cells_transport asegs); [exact DSH | exact MU |]. cbn [disjoint_from cells_size csize Nat.add]. clear - D8 D9 D10 D11 LO ACR. lia.
Qed.

Lemma dc_dsh_range : forall A LBx B mx mdx Fr X L0 SP,
HEAPAx A LBx LM ((Fr, 1) :: FRS) B mx mdx ->
client_rangex A4H X (L0 ++ LM ++ fr_ivs A4L ((Fr, 1) :: FRS)) SP (D / 8 + 2147450880) 1.
Proof.
intros A LBx B mx mdx Fr X L0 SP HP. destruct DLOC as (Fd & kd & HFd & H1 & H2).
assert (IND : In (Fd, kd) ((Fr, 1) :: FRS)) by (right; exact HFd).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP IND) as (Hkd & HFdal & HFd0 & HFdc & _).
eapply client_rangex_block; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_shadow; exact IND | |].
- unfold shad. cbn [hl_sb A4L]. unfold A_SB. clear - H1. Z.div_mod_to_equations. lia.
- unfold shad. cbn [hl_sb A4L]. unfold A_SB, fr_shadow_len.
assert (HF8 : Fd mod 64 = 0).
{ apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ (fr_size kd)); [| apply Z.mod_divide; [pose proof (fr_size_pos kd ltac:(lia)); lia | exact HFdal]].
exists (2 ^ kd). unfold fr_size. lia. }
unfold fr_size in H2. clear - H1 H2 HF8 Hkd. assert (K : kd = 0 \/ kd = 1 \/ kd = 2 \/ kd = 3) by lia. destruct K as [-> | [-> | [-> | ->]]]; cbn in *; Z.div_mod_to_equations; lia.
Qed.

Lemma dc_dst_presx : forall A LBx B mx mdx Fr X L0 SP mc m' q,
HEAPAx A LBx LM ((Fr, 1) :: FRS) B mx mdx -> dc_dst mc q ->
heap_presx A4H X (L0 ++ LM ++ fr_ivs A4L ((Fr, 1) :: FRS)) SP mc m' -> dc_dst m' q.
Proof.
intros A LBx B mx mdx Fr X L0 SP mc m' q HP [DC DSH] HPR. destruct DLOC as (Fd & kd & HFd & H1 & H2).
assert (IND : In (Fd, kd) ((Fr, 1) :: FRS)) by (right; exact HFd).
split.
- eapply (heap_presx_rw_cells A4H); [exact HPR | exact DC |].
eapply client_rangex_block; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact IND | cbn; lia | cbn; lia].
- destruct DSH as [Hwf Hb]. split; [exact Hwf|].
eapply (heap_presx_bytes_at A4H); [exact HPR | exact Hb |]. cbn [cells_bytes cbytes app length]. exact (dc_dsh_range _ _ _ _ _ _ _ _ _ HP).
Qed.

Lemma dc_dsh_presxD : forall A LBx B mx mdx Fr L0 SP mc m',
HEAPAx A LBx LM ((Fr, 1) :: FRS) B mx mdx -> ro_cells asegs mc (D / 8 + 2147450880) [C1 (Z_to_bv 8 0)] ->
presxD D (L0 ++ LM ++ fr_ivs A4L ((Fr, 1) :: FRS)) SP mc m' -> ro_cells asegs m' (D / 8 + 2147450880) [C1 (Z_to_bv 8 0)].
Proof.
intros A LBx B mx mdx Fr L0 SP mc m' HP [Hwf Hb] PX. split; [exact Hwf|].
destruct (dc_dfacts _ _ _ _ _ _ HP) as (D1 & D2 & D3 & _ & _ & _ & _ & _ & _ & D10 & _).
eapply (QrIB.Mq0.presxD_bytes_at A4H); [exact PX | exact Hb | cbn [cells_bytes cbytes app length]; exact (dc_dsh_range _ _ _ _ _ _ _ _ _ HP) |].
cbn [cells_bytes cbytes app length]. clear - D1 D2 D3 D10. lia.
Qed.

Lemma dc_dst_pres : forall A LBx B mx mdx Fr L0 SP mc m' q,
HEAPAx A LBx LM ((Fr, 1) :: FRS) B mx mdx -> dc_dst mc q ->
heap_pres A4H (L0 ++ LM ++ fr_ivs A4L ((Fr, 1) :: FRS)) SP mc m' -> dc_dst m' q.
Proof. intros A LBx B mx mdx Fr L0 SP mc m' q HP DD HPR. eapply (dc_dst_presx _ _ _ _ _ _ (fun _ => False)); [exact HP | exact DD | apply heap_pres_presx; exact HPR]. Qed.

Lemma dc_blkW_disj : forall Ax LBx Bx mx mdx Fr W A0 n0,
HEAPAx Ax LBx LM ((Fr, 1) :: FRS) Bx mx mdx ->
Forall (fun iv => exists a n, In (a, n) (LBx ++ LM) /\ a <= fst iv /\ snd iv <= a + n) W ->
(alloc_ceiling <= A0 \/ (Fr <= A0 /\ A0 + n0 <= Fr + 128) \/ (2147450880 <= A0 /\ A0 + n0 <= 17594333495296)
\/ (D <= A0 /\ A0 + n0 <= D + 8)) ->
disjoint_from W A0 n0.
Proof.
intros Ax LBx Bx mx mdx Fr W A0 n0 HP HW KIND.
assert (INF : In (Fr, 1) ((Fr, 1) :: FRS)) by (left; reflexivity).
destruct (dc_dfacts _ _ _ _ _ _ HP) as (_ & _ & _ & _ & DBLK & _).
induction W as [|[wl wh] W IH]; cbn [disjoint_from]; [exact I|].
apply Forall_cons_iff in HW as [(a & n & Hin & H1 & H2) HW]. cbn [fst snd] in H1, H2. split; [| exact (IH HW)].
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a n HP Hin) as (_ & _ & Ha0 & Hac & _).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF Hin) as DF. rewrite fr_size_1 in DF.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ a n HP Hin) as APP. cbn [hl_sb A4L] in APP. unfold A_SB in APP.
change ((2 ^ 47 - 1) / 8 + 2147450880 + 1) with 17594333495296 in APP.
pose proof (DBLK a n Hin) as DB.
clear - KIND H1 H2 Ha0 Hac DF APP DB. lia.
Qed.

Lemma dc_dst_blkW : forall Ax LBx Bx mx mdx Fr W mc m' q,
HEAPAx Ax LBx LM ((Fr, 1) :: FRS) Bx mx mdx ->
Forall (fun iv => exists a n, In (a, n) (LBx ++ LM) /\ a <= fst iv /\ snd iv <= a + n) W ->
munch W mc m' -> wmono asegs mc m' -> dc_dst mc q -> dc_dst m' q.
Proof.
intros Ax LBx Bx mx mdx Fr W mc m' q HP HW MU WM [DC DSH].
destruct (dc_dfacts _ _ _ _ _ _ HP) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & D10 & _).
split.
- eapply (rw_cells_transport asegs); [exact DC | exact MU | exact WM |]. cbn [cells_size csize Nat.add].
eapply (dc_blkW_disj _ _ _ _ _ _ _ _ _ HP HW). right; right; right. lia.
- eapply (ro_cells_transport asegs); [exact DSH | exact MU |]. cbn [cells_size csize Nat.add].
eapply (dc_blkW_disj _ _ _ _ _ _ _ _ _ HP HW). right; right; left. lia.
Qed.

Lemma dc_epi :
forall (x1 xsp t0 t1 t2 xs1 a1 a2 a3 a4 a5 a6 a7 x19 x20 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(mX : word -> option byte) (mdX : config) (AX : ASA A4L HIx) (BX : bud) (LBx : list blk) (Fr rv : Z)
(cs : list cell) (w0 : word) (frest : list cell) (x0 x1' x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : byte),
dc_inv mX mdX -> fsaved F F1 -> frm0 fc1 ->
HEAPAx AX LBx LM ((Fr, 1) :: FRS) BX mX mdX ->
rw_cells asegs mX ASP cs -> Z.of_nat (cells_size cs) = 88 ->
rw_cells asegs mX Fr (C8 w0 :: frest) -> Z.of_nat (cells_size frest) = 112 ->
rw_cells asegs mX (Fr / 8 + 2147450880) [C1 x0; C1 x1'; C1 x2; C1 x3; C1 x4; C1 x5; C1 x6; C1 x7; C1 x8; C1 x9; C1 x10; C1 x11; C1 x12; C1 x13; C1 x14; C1 x15] ->
jroot_repA r mX BS p ->
dc_resX LBx BX mX rv ->
AJ5 A4L HIx AX T mdX
(MS (mkR x1 xsp gp (wz A_TP) t0 t1 t2 sp xs1 (wz rv) a1 a2 a3 a4 a5 a6 a7
(wz (Fr / 8 + 2147450880)) x19 x20 (wz Fr) (wz Fr) x23 x24 x25 x26 x27 t3 t4 t5 t6)
F1 (wz 0x9fce4) fc1 None mX (seg_rom asegs)).
Proof.
intros until x15. intros (VMX & PRESX & STX & SAVE & GX) FS FRM1 HPX SCR SCRsz FFX FFsz FSHX JRX RES.
unfold dc_save in SAVE. unfold ASP in *. pose proof LOS as LOSu. unfold dc_stkA, DC_F, DC_C in LOSu.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (INF : In (Fr, 1) ((Fr, 1) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HPX INF) as (_ & HFal & HF0 & HFc & HFimg & _ & _ & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HPX INF) as HFapp.
rewrite fr_size_1 in HFal, HFc, HFimg, HFapp. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFimg, HFapp. unfold A_SB in HFapp.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 16 <= 17594333495296) by (unfold sh; clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HPX) as MI. change (hl_segs A4L) with asegs in MI.
pose proof (wmono_refl asegs mX) as WM. pose proof (munch_refl [(lo, bv_unsigned sp + -192); (Fr, Fr + 120); (sh, sh + 16); (6434236, 6434240)] mX) as MU.
stash RES. stash JRX. stash GX. stash PRESX.
unfold A_TP. a4l. reenterA asegs A4L HIx asegs_wx HPX.
step. step. stepz. step. if_falsex. step. do 16 stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ mX mc, WMc : wmono asegs mX mc, MIc : mem_inv asegs mc |- _ =>
pose proof (fk1_HEAPA _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -192) _ HPX LO ltac:(lia) MUc WMc MIc) as HPY;
pose proof (fk1_pres _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -192) _ HPX LO ltac:(lia) MUc WMc) as HPRXY end end.
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HPY INF) as (_ & _ & _ & _ & _ & _ & _ & (fp & FPB & FPR & FPnc & FPimg & FPns & FPfr)).
rewrite fr_size_1 in FPB. replace (Fr + 128 - 8) with (Fr + 120) in FPB by lia.
pose proof (ro_C8_of_bytes_at asegs _ _ _ FPB) as FPC.
step.
evt_done5.
eapply (hiA_frame_release A4L HIx) with (Fr := Fr) (k := 1) (fp := fp) (rX := Z_to_bv 5 11);
[exact HPY | exact INF | rewrite fr_size_1; replace (Fr + 128 - 8) with (Fr + 120) by lia; exact FPB | lia | reflexivity | vm_compute; discriminate | | ].
1: vm_compute; split; reflexivity.
intros m5 md5 A5 VM5 HP5 Hoff Hwv.
cbn [fr_remove fr_base fst Z.eqb] in HP5. rewrite Z.eqb_refl in HP5.

lazymatch type of HPY with HEAPA _ _ _ _ _ _ _ ?mq _ => assert (MUr : munch [(fp, fp + 1)] mq m5) end.
{ intros x Hx. cbn [outside] in Hx. pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR. cbn in XR.
rewrite <- (Z_to_bv_bv_unsigned x). change (Z_to_bv 64 (bv_unsigned x)) with (wa (bv_unsigned x)). apply Hoff; lia. }
lazymatch type of HPY with HEAPA _ _ _ _ _ _ _ ?mq _ => assert (WMr : wmono asegs mq m5) by exact Hwv end.
assert (FPlow : fp < alloc_ceiling) by (destruct (Z.lt_ge_cases fp alloc_ceiling) as [L|G]; [exact L | exfalso; apply FPnc; left; exact G]).
apply (rw_cells_transport asegs [(fp, fp + 1)] _ m5) in SAVE; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] _ m5) in SCR; [| exact MUr | exact WMr | cbn [disjoint_from]; lia].
apply (stk_transport_disjoint asegs [(fp, fp + 1)] _ m5) in STX; [| exact MUr | exact WMr | cbn [disjoint_from]; lia].
eapply stk_release in SCR; [| exact STX | lia]. rewrite SCRsz in SCR.
replace (bv_unsigned sp + -192 + 88) with (bv_unsigned sp + -104) in SCR by lia.
clear FPC.
change (654652 + 4) with 654656.
reenterA asegs A4L HIx asegs_wx HP5.
do 17 step.
rename SCR into ST5. release_frame SAVE ST5 (bv_unsigned sp).
evt_done5. unstash RES. unstash JRX. unstash GX. unstash PRESX.

assert (HPRX5 : heap_pres A4H (LBx ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) mX m5).
{ eapply heap_pres_trans; [eapply heap_pres_weaken; [exact HPRXY | lia | intros b Hb; exact Hb] |].
eapply (heap_pres_of_presD (Fr + 32)).
+ eapply (presD_fp HIx _ _ _ _ _ _ _ _ (Fr + 32) _ (bv_unsigned sp) fp HPY); [| lia | exact FPnc | exact FPfr | exact Hoff | exact Hwv].
intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. destruct Hb as [H|H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H].
+ intros a Hd Hc.
destruct (own_frame_fresh HIx Fr 1 LBx LBx LM FRS BX AX _ mdX HPY (incl_refl _)) as [OFF OFS].
assert (Ho : outside [(Fr + 32, Fr + 40)] a).
{ eapply (Q1Ey.client_outsideF HIx AX LBx LM ((Fr, 1) :: FRS) BX (LBx ++ LM ++ fr_ivs A4L FRS) _ mdX [(Fr + 32, Fr + 40)] (bv_unsigned sp) HPY); [| lia | | lia | exact Hc].
- intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. destruct Hb as [H|H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H].
- apply Forall_cons; [| apply Forall_nil]. right; right; right. exists Fr, 1. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. left. cbn [fst snd]. rewrite fr_size_1. lia. }
cbn [outside] in Ho. lia. }
assert (ELB : exists CBS REM, LBx = BS ++ CBS ++ REM ++ LB).
{ destruct RES as (_ & [(_ & d & q & CBS & REM & E & _) | (_ & q & CBS & REM & E & _)]); exists CBS, REM; exact E. }
destruct ELB as (CBS0 & REM0 & ELB).
assert (INCL : forall b, In b ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) -> In b (LBx ++ LM ++ fr_ivs A4L FRS)).
{ intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb as [Hb|Hb]; [| apply in_or_app; right; apply in_or_app; right; exact Hb].
apply in_app_or in Hb as [Hb|Hb]; [| apply in_or_app; right; apply in_or_app; left; exact Hb].
apply in_or_app; left. rewrite ELB. apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb]. }
assert (AGX : forall BSx, incl BSx LBx -> agree_on asegs BSx mX m5).
{ intros BSx Hi. eapply (agree_of_heap_pres asegs A4H); [exact HPRX5 | reflexivity | intros b Hb; apply in_or_app; left; apply Hi; exact Hb]. }
eapply (Kont _ md5 m5 rv A5 BX).
- unfold jo_post_frameDA.
split; [apply ret_statew_intro; [exact FS | intros _; exact FRM1] |].
split; [eapply model_vm_only_trans; [exact VMX | exact VM5] |].
split; [exact ST5|].
split; [| exact (heapA_errno A4L HIx _ _ _ _ _ _ _ HP5)].
eapply (QrIB.Mq0.presxD_trans A4H); [exact PRESX|]. apply (QrIB.Mq0.pres_presxD A4H).
eapply heap_pres_weaken; [exact HPRX5 | lia | exact INCL].
- eapply lh_globA_client; [exact HPRX5 | exact GX].
- eapply (QrIB.Mq0.jroot_rep_agree A4H A4F); [exact JRX | apply (AGX BS); rewrite ELB; apply incl_appl; apply incl_refl | apply incl_refl].
- destruct RES as (BDX & RES). split; [exact BDX|].
destruct DLOC as (Fd & kd & HFd & HD1 & HD2).
assert (DCX : forall v, rw_cells asegs mX D [C8 v] -> rw_cells asegs m5 D [C8 v]).
{ intros v H. eapply (heap_pres_rw_cells A4H); [exact HPRX5 | exact H |].
eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact HFd | cbn; lia | cbn; lia]. }
destruct RES as [(Hrv & d & q & CBS & REM & E & CO & CW & Hq & DC & JD & BBX) | (Hrv & q & CBS & REM & E & DC & FRES & BBX)].
+ left. split; [exact Hrv|]. exists d, q, CBS, REM. split; [exact CO|]. split; [exact CW|]. split; [exact Hq|]. split; [exact (DCX _ DC)|].
split; [eapply (QrIB.Mq0.jroot_rep_agree A4H A4F); [exact JD | apply (AGX CBS); rewrite E; apply incl_appr; apply incl_appl; apply incl_refl | apply incl_refl] |].
split; [exact BBX|]. rewrite <- E. exact HP5.
+ right. split; [exact Hrv|]. exists q, CBS, REM. split; [exact (DCX _ DC)|].
split; [eapply fresA_agree; [exact FRES | apply (AGX CBS); rewrite E; apply incl_appr; apply incl_appl; apply incl_refl | apply incl_refl] |].
split; [exact BBX|]. rewrite <- E. exact HP5.
Qed.

Lemma dc_pro :
forall (t0 t1 t2 a1 a2 a3 a6 a7 t3 t4 t5 t6 : word) (A : ASA A4L HIx) (n : Z),
HEAPAx A (BS ++ LB) LM FRS B0 m0 md0 -> stk asegs m0 lo (bv_unsigned sp) -> lh_globA m0 ->
rw_cells asegs m0 D [C8 (wz 0)] -> unpoisoned asegs m0 A_SB D 8 ->
Z.of_nat (length FRS) < 4096 ->
sh_lenA r m0 p n -> sh_needB r n <= bB B0 -> 2 <= bD B0 ->
DC_KB * w <= bB B0 -> w <= bD B0 -> sh_needB r n <= DC_KB * w -> 2 <= w ->
(forall (Fr q : Z) (CBS : list blk) (m3 : word -> option byte) (md3 : config) (A3 : ASA A4L HIx) (B3 : bud) (j40 j16 jf : list byte) (F3 : bvmap 5 word) (fc3 : bv 32)
(x1 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x19 t3' t4' t5' t6' : word),
dc_inv m3 md3 -> fsaved F F3 -> frm0 fc3 ->
HEAPAx A3 (BS ++ CBS ++ LB) LM ((Fr, 1) :: FRS) B3 m3 md3 ->
rw_cells asegs m3 ASP [C8 (wz 0); CB 40 j40; C8 (wz SH_A); C8 (wz D); CB 16 j16; C8 (wz Fr)] ->
rw_cells asegs m3 Fr [C8 (wz 1102416563); C8 (wz 139913); C8 (wz 653196); CB 96 jf] ->
rw_cells asegs m3 (Fr / 8 + 2147450880) [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
jroot_repA r m3 BS p ->
q <> 0 -> dc_dst m3 q -> QrIB.Mq0.scopy A4H A4F r m3 CBS q -> sh_shapeA r n CBS ->
bB B0 - sh_okB r n <= bB B3 -> bD B0 - 1 <= bD B3 ->
AJ5 A4L HIx A3 T md3
(MS (mkR x1 (wz ASP) gp (wz A_TP) t0' t1' t2' sp (wz ASP) (wz 1) a1' a2' a3' a4' a5' a6' a7'
(wz (Fr / 8 + 2147450880)) x19 (wz 2147450880) (wz Fr) (wz Fr) (wz p) s8 s9 s10 s11 t3' t4' t5' t6')
F3 (wz 0x9f8d8) fc3 None m3 (seg_rom asegs))) ->
AJ5 A4L HIx A T md0
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz p) a1 a2 a3 (wz D) (wz SH_A) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz DCR_A) fc None m0 (seg_rom asegs)).
Proof.
intros until n. intros HP ST G0 DC0 DU0 FRN LEN0 SHB SHD BBW BDW SHW W2 KOK.
pose proof LOS as LOSu. unfold dc_stkA, DC_F, DC_C in LOSu.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
unfold DCR_A. unfold ASP in *.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof alloc_ceiling_range as ACR.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HP) as (SB1 & SB2 & SB3 & SB4).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2. apply ro_C8_of_bytes_at in SB3.
assert (UARC : ro_cells asegs m0 (hl_uar_cell A4L) [C4 (Z_to_bv 64 1)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SB4]).
clear SB4. a4l.
pose proof (wmono_refl asegs m0) as WM. pose proof (munch_refl [(bv_unsigned sp - 192, bv_unsigned sp)] m0) as MU.
unfold A_TP in *.
stash G0. stash DC0. stash DU0. stash LEN0. stash KOK.
reenterA asegs A4L HIx asegs_wx HP.
carve_frame 192%nat ST.
step. stepz. do 13 step.
step. step.
rewrite (unsigned_lit (bv_unsigned sp + -192)) by lia. change 18446744073709551584 with (2^64 - 2^5). rewrite OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.land_align_down by lia. change (2^5) with 32.
replace ((bv_unsigned sp + -192) mod 32) with 0 by (clear - SPA; Z.div_mod_to_equations; lia). rewrite Z.sub_0_r.
step.
step. step.
do 6 step. step.
norm_sx32. step. if_false.
step. step. step. step. step.
evt_done5.
eapply (stack_malloc_full HIx) with (k := 1) (bytes := 96) (lo := lo) (LB := BS ++ LB) (LM := LM) (FR := FRS) (B := B0);
[ heap_nowA A4L HIx HP MU WM MI | lia | .. ].
all: rewrite ?unsigned_lit by lia.
1: rewrite fr_size_1; lia.
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

assert (INF : In (Fr, 1) ((Fr, 1) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as (_ & HFal & HF0 & HFc & HFimg & _ & HFshw & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as HFapp.
rewrite fr_size_1 in HFal, HFc, HFimg, HFapp. rewrite fr_shadow_len_1 in HFshw. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFimg, HFapp.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in FR; [| left; cbn; lia].
change (hl_segs A4H) with asegs in FR.
clear SB1 SB2 SB3 UARC.
assert (FSH1 : rw_cells asegs m1' (shad A4L Fr) [CB 16 (repeat (Z_to_bv 8 0) 16)]).
{ split; [split; [cbn; split; [reflexivity | exact I] | cbn [cells_bytes cbytes app]; rewrite app_nil_r; rewrite fr_shadow_len_1 in SHB1; exact SHB1] | exact HFshw]. }
rewrite fr_size_1 in FF1. change (Z.to_nat (128 - 8)) with 120%nat in FF1.
unfold shad in FSH1. a4l.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 16 <= 17594333495296) by (unfold sh; clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI1. change (hl_segs A4L) with asegs in MI1. clear MI.
assert (HPR01 : heap_pres A4H ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m1').
{ eapply heap_pres_trans.
- eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; exact Hb | clia |].
apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil].
- eapply heap_pres_weaken; [exact HPR1 | lia | intros b Hb; exact Hb]. }
clear MU WM. pose proof (wmono_refl asegs m1') as WM. pose proof (munch_refl [(lo, bv_unsigned sp); (Fr, Fr + 120); (sh, sh + 16); (6434236, 6434240)] m1') as MU.
unfold A_SB in HFapp.
reenterA asegs A4L HIx asegs_wx HP1.
step. step. step. step. step. step. if_truex.
step.
step. step. step. step.
rewrite (unsigned_lit Fr) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
step. step. step. step. stepz. stepz. stepz. step. step.
fold sh.
stepz. stepz. stepz. stepz. step. stepz. stepz. stepz. stepz. step. stepz. stepz. stepz. stepz.
step. step. step. unfold SH_A. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m1' mc, WMc : wmono asegs m1' mc, MIc : mem_inv asegs mc |- _ =>
pose proof (fk1_HEAPA _ _ _ _ _ _ _ _ lo (bv_unsigned sp) _ HP1 LO HT MUc WMc MIc) as HP2;
pose proof (fk1_pres _ _ _ _ _ _ _ _ lo (bv_unsigned sp) _ HP1 LO ltac:(lia) MUc WMc) as HPR12 end end.
lazymatch type of HP2 with HEAPA _ _ _ _ _ _ _ ?mc _ =>
assert (HPR02 : heap_pres A4H ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 mc) by (eapply heap_pres_trans; [exact HPR01 | exact HPR12]) end.
unstash G0. unstash DC0. unstash DU0. unstash LEN0. unstash KOK.
pose proof (agree_of_heap_pres asegs A4H _ _ (BS ++ LB) _ _ HPR02 eq_refl ltac:(intros b Hb; apply in_or_app; left; exact Hb)) as AG02.
pose proof (QrIB.Mq0.jroot_rep_agree A4H A4F _ _ _ _ _ _ JR0 AG02 ltac:(apply incl_appl; apply incl_refl)) as JR2.
pose proof (lh_globA_client _ _ _ _ HPR02 G0) as G2.
destruct DLOC as (Fd & kd & HFd & HD1 & HD2).
lazymatch type of HP2 with HEAPA _ _ _ _ _ _ _ ?mc _ =>
assert (DC2 : rw_cells asegs mc D [C8 (wz 0)]);
[ eapply (heap_pres_rw_cells A4H); [exact HPR02 | exact DC0 |];
eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact HFd | cbn; lia | cbn; lia] |];
assert (DU2 : unpoisoned asegs mc A_SB D 8) by (eapply (QsKa.Mq6.unpoisoned_pres_frame HIx); [exact HP | exact HFd | exact HD1 | exact HD2 | exact DU0 | exact HPR02]);
assert (LEN2 : sh_lenA r mc p n)
end.
{ destruct (QrIB.Mq0.jroot_rep_root_in A4H A4F r m0 BS p JR0 NN) as (np & INp & Hnp).
assert (X : forall len0 : Z, bytes_at asegs m0 (p + 40) (le8 (wz len0)) -> bytes_at asegs m2 (p + 40) (le8 (wz len0))).
{ intros len0 Hb. eapply (bytes_at_agree asegs); [exact Hb | exact AG02 |]. exists p, np. split; [apply in_or_app; left; exact INp | rewrite length_le8; lia]. }
unfold sh_lenA, str_lenA in LEN0 |- *. destruct r as [|[|u| |h|kids|kids]|tojs|]; try exact I;
(destruct LEN0 as (len0 & Hb & Hr & Hn); exists len0; split; [exact (X _ Hb) | split; [exact Hr | exact Hn]]). }
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HP2) as (errv2 & ERR2).
evt_done5.
eapply (SHALLOW) with (LB := LB) (BS := BS) (FRS := (Fr, 1) :: FRS) (B := B0) (lo := lo) (p := p) (D := D) (n := n) (dold := wz 0) (r := r) (errv := errv2).
all: rewrite ?unsigned_lit by lia.
1: exact HP2. 1: exact JR2. 1: exact NN. 1: exact G2. 1: exact DC2.
1: exists Fd, kd; split; [right; exact HFd | split; [exact HD1 | exact HD2]].
1: exact DU2. 1: exact DAL. 1: eassumption. 1: exact LO. 1: unfold SH_STK_A; lia.
1: clear - SPA; Z.div_mod_to_equations; lia. 1: lia. 1: exact ERR2. 1: reflexivity. 1: reflexivity.
1: exact LEN2. 1: exact SHB. 1: exact SHD. 1: reflexivity. 1: reflexivity.
intros ms3 md3 m3 rv A3 B3 POST G3 JR3 RES3.
destruct POST as (RS3 & VM3 & ST3 & PXD3 & (errv3 & ERR3)).
destruct RS3 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F3 & fc3 & -> & FS3 & FRM3).
rewrite ?(unsigned_lit (bv_unsigned sp + -192)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -192)) in PXD3 by lia.

pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP1 ltac:(right; exact HFd)) as (Hkd & _ & HFd0 & HFdc & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 ltac:(right; exact HFd)) as HFdapp. cbn [hl_sb A4L] in HFdapp. unfold A_SB in HFdapp.
change ((2 ^ 47 - 1) / 8 + 2147450880 + 1) with 17594333495296 in HFdapp.
assert (FNE : Fr <> Fd).
{ intros ->. pose proof (proj1 (stdpp.base.NoDup_ListNoDup _) (heapA_frame_nodup A4L HIx _ _ _ _ _ _ _ HP1)) as ND. cbn in ND.
apply List.NoDup_cons_iff in ND as [Hni _]. apply Hni. exact (in_map fr_base _ _ HFd). }
pose proof (heapA_frame_apart A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP1 INF ltac:(right; exact HFd) FNE) as FAP. rewrite fr_size_1 in FAP.
pose proof (fr_size_pos kd ltac:(lia)) as FSP.

assert (PXR : forall A0 cs0, rw_cells asegs m2 A0 cs0 ->
client_rangex A4H (hl_volatile A4H) ((BS ++ LB) ++ LM ++ fr_ivs A4L ((Fr, 1) :: FRS)) (bv_unsigned sp + -192) A0 (Z.of_nat (cells_size cs0)) ->
(A0 + Z.of_nat (cells_size cs0) <= D \/ D + 8 <= A0) -> rw_cells asegs m3 A0 cs0).
{ intros A0 cs0 H1 H2 H3. exact (QrIB.Mq0.presxD_rw_cells A4H D _ _ m2 m3 A0 cs0 PXD3 H1 H2 H3). }
apply PXR in FR; [| left; lia | right; cbn [cells_size csize Nat.add]; clia].
apply PXR in FF1.
2: { eapply client_rangex_block; [apply in_or_app; right; apply in_or_app; right; left; reflexivity | cbn [fr_base fst]; lia | cbn [cells_size csize Nat.add fr_base fr_class fst snd]; rewrite fr_size_1; lia]. }
2: { cbn [cells_size csize Nat.add]. lia. }
apply PXR in FSH1.
2: { eapply client_rangex_block; [apply in_or_app; right; apply in_or_app; right; right; left; reflexivity | unfold shad; cbn [fr_base fst hl_sb A4L]; unfold A_SB; fold sh; lia
| unfold shad; cbn [cells_size csize Nat.add fr_base fr_class fst snd hl_sb A4L]; rewrite fr_shadow_len_1; unfold A_SB; fold sh; lia]. }
2: { cbn [cells_size csize Nat.add]. clear - SHR HFdapp HD1 HD2 FSP. lia. }
clear PXR.

assert (PX03 : presxD D ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m3).
{ eapply (QrIB.Mq0.presxD_trans A4H); [apply (QrIB.Mq0.pres_presxD A4H); exact HPR02 |].
eapply (QrIB.Mq0.presxD_weaken A4H); [exact PXD3 | lia |].
intros b Hb. apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb |].
apply in_or_app; right. apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; cbn [fr_ivs flat_map app]; right; right; exact Hb]. }
assert (INV3 : dc_inv m3 md3).
{ split; [eapply model_vm_only_trans; [exact VM1 | exact VM3] |]. split; [exact PX03|]. split; [exact ST3|]. split; [| exact G3].
unfold dc_save. lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?rest) =>
change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: rest) with ([c0; c1; c2; c3; c4; c5] ++ rest) in FR end.
destruct (proj1 (rw_cells_app asegs m3 _ _ _) FR) as [_ SAVE]. cbn [cells_size csize Nat.add] in SAVE.
replace (bv_unsigned sp + -192 + Z.of_nat 88) with (bv_unsigned sp + -104) in SAVE by lia. exact SAVE. }

lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?rest) =>
change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: rest) with ([c0; c1; c2; c3; c4; c5] ++ rest) in FR end.
destruct (proj1 (rw_cells_app asegs m3 _ _ _) FR) as [SCR SAVE]. clear FR. cbn [cells_size csize Nat.add] in SAVE.
replace (bv_unsigned sp + -192 + Z.of_nat 88) with (bv_unsigned sp + -104) in SAVE by lia.
destruct RES3 as [(-> & q & CBS & Hq & DC3 & SC3 & SHP3 & BB3 & BD3 & HP3) | (-> & DC3 & BB3 & BD3 & HP3)].
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI3. change (hl_segs A4L) with asegs in MI3.
pose proof (wmono_refl asegs m3) as WM3. pose proof (munch_refl [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6434236, 6434240)] m3) as MU3.
replace (ret_pc (wz 653524)) with (wz 653524) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
reenterA asegs A4L HIx asegs_wx HP3.
step. if_lit.
evt_done5.
lazymatch type of SCR with rw_cells _ _ _ [_; CB 40 ?j40; _; _; CB 16 ?j16; _] =>
lazymatch type of FF1 with rw_cells _ _ _ [_; _; _; CB 96 ?jf] =>
eapply (KOK Fr q CBS m3 md3 A3 B3 j40 j16 jf F3 fc3) end end;
[ exact INV3 | exact FS3 | apply FRM3; exact FRM0 | exact HP3 | exact SCR | exact FF1 | | exact JR3 | exact Hq | split; [exact DC3 | exact (dc_dsh_presxD _ _ _ _ _ _ _ _ _ _ HP2 (unpoisoned8_cell asegs _ A_SB D DU2 DAL) PXD3)] | exact SC3 | exact SHP3 | exact BB3 | exact BD3 ].
eapply rw_cells_recast; [exact FSH1 | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity].

-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI3. change (hl_segs A4L) with asegs in MI3.
pose proof (errno_shadowA HIx _ _ _ _ _ _ _ HP3) as ESH. a4l. change ((6434400 - 164) / 8 + 2147450880) with 2148255159 in ESH.
unfold A_ERRNO, A_TP in ERR3. change (6434400 - 164) with 6434236 in ERR3.
pose proof (wmono_refl asegs m3) as WM3. pose proof (munch_refl [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6434236, 6434240)] m3) as MU3.
replace (ret_pc (wz 653524)) with (wz 653524) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
stash KOK. pose proof DC3 as DC3k. stash DC3k.
reenterA asegs A4L HIx asegs_wx HP3.
step. if_lit.
step. step. step. step.
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
step. step. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false.
step. stepz. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m3 mc, WMc : wmono asegs m3 mc, MIc : mem_inv asegs mc |- _ =>
pose proof (fk1_HEAPA _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -104) _ HP3 LO ltac:(lia) MUc WMc MIc) as HPY;
pose proof (fk1_pres _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -104) _ HP3 LO ltac:(lia) MUc WMc) as HPR3Y end end.
evt_done5.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
lazymatch type of HPY with HEAPA _ _ _ _ _ _ _ ?mY _ =>
eapply (dc_epi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F3 fc3 mY md3 A3 B3 (BS ++ LB) Fr (2^64 - 1)) end.
+ split; [eapply model_vm_only_trans; [exact VM1 | exact VM3] |].
split; [eapply (QrIB.Mq0.presxD_trans A4H); [exact PX03 |]; apply (QrIB.Mq0.pres_presxD A4H); eapply heap_pres_weaken; [exact HPR3Y | lia | intros b Hb; exact Hb] |].
split; [eassumption|]. split; [unfold dc_save; exact SAVE|].
eapply lh_globA_client; [exact HPR3Y | exact G3].
+ exact FS3.
+ apply FRM3. exact FRM0.
+ exact HPY.
+ exact SCR.
+ reflexivity.
+ exact FF1.
+ reflexivity.
+ eapply rw_cells_recast; [exact FSH1 | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity].
+ eapply (QrIB.Mq0.jroot_rep_agree A4H A4F); [exact JR3 | | apply incl_appl; apply incl_refl].
eapply (agree_of_heap_pres asegs A4H); [exact HPR3Y | reflexivity | intros b Hb; apply in_or_app; left; exact Hb].
+ split; [cbn [bD] in *; lia|]. right. split; [reflexivity|]. exists 0, [], []. split; [reflexivity|].
split; [| split; [left; split; reflexivity | cbn [length Z.of_nat]; lia]].
unstash DC3k. eapply (heap_pres_rw_cells A4H); [exact HPR3Y | exact DC3k |].
eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact HFd | cbn; lia | cbn; lia].
Qed.

Definition dc_scr (Fr : Z) (v0 : word) (c24 : cell) (j16 : list byte) : list cell :=
[C8 v0; C8 (wz 1); C8 (wz Fr); c24; C8 (wz Fr); C8 (wz p); C8 (wz SH_A); C8 (wz D); CB 16 j16; C8 (wz Fr)].

Lemma dc_body :
forall (Fr q : Z) (CBS : list blk) (m3 : word -> option byte) (md3 : config) (A3 : ASA A4L HIx) (B3 : bud) (j40 j16 : list byte) (F3 : bvmap 5 word) (fc3 : bv 32)
(x1 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x19 t3' t4' t5' t6' : word) (ty np : Z),
HEAPAx A3 (BS ++ CBS ++ LB) LM ((Fr, 1) :: FRS) B3 m3 md3 ->
rw_cells asegs m3 ASP [C8 (wz 0); CB 40 j40; C8 (wz SH_A); C8 (wz D); CB 16 j16; C8 (wz Fr)] ->
In (p, np) BS -> 48 <= np -> rw_cells asegs m3 p [C4 (wz ty)] -> 1 <= ty <= 6 ->
(forall (mc : word -> option byte) (j24 : list byte) (y10 y11 y12 : word),
munch [(ASP, bv_unsigned sp + -104)] m3 mc -> wmono asegs m3 mc -> mem_inv asegs mc ->
rw_cells asegs mc ASP (dc_scr Fr (wz 0) (CB 8 j24) j16) ->
AJ5 A4L HIx A3 T md3
(MS (mkR x1 (wz ASP) gp (wz A_TP) t0' t1' t2' sp (wz ASP) y10 y11 y12 a3' a4' a5' a6' a7'
(wz (Fr / 8 + 2147450880)) x19 (wz 2147450880) (wz Fr) (wz Fr) (wz p) s8 s9 s10 s11 t3' t4' t5' t6')
F3 (wz (if ty =? 5 then 0x9fadc else if ty =? 4 then 0x9f90c else 0x9fba8)) fc3 None mc (seg_rom asegs))) ->
AJ5 A4L HIx A3 T md3
(MS (mkR x1 (wz ASP) gp (wz A_TP) t0' t1' t2' sp (wz ASP) (wz 1) a1' a2' a3' a4' a5' a6' a7'
(wz (Fr / 8 + 2147450880)) x19 (wz 2147450880) (wz Fr) (wz Fr) (wz p) s8 s9 s10 s11 t3' t4' t5' t6')
F3 (wz 0x9f8d8) fc3 None m3 (seg_rom asegs)).
Proof.
intros until np. intros HP3 SCR INp Hnp TYC TY KD.
pose proof LOS as LOSu. unfold dc_stkA, DC_F, DC_C in LOSu. unfold ASP, dc_scr in *.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (INF : In (Fr, 1) ((Fr, 1) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP3 INF) as (_ & HFal & HF0 & HFc & HFimg & _ & _ & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP3 INF) as HFapp.
rewrite fr_size_1 in HFal, HFc, HFimg, HFapp. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFimg, HFapp. unfold A_SB in HFapp.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 16 <= 17594333495296) by (unfold sh; clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
assert (INp2 : In (p, np) (BS ++ CBS ++ LB)) by (apply in_or_app; left; exact INp).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p np HP3 ltac:(apply in_or_app; left; exact INp2)) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ p np HP3 ltac:(apply in_or_app; left; exact INp2)) as Hpimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hpimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p np 0 HP3 INp2 ltac:(lia) ltac:(lia)) as SHp0. rewrite Z.add_0_r in SHp0.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI3. change (hl_segs A4L) with asegs in MI3.
pose proof (wmono_refl asegs m3) as WM3. pose proof (munch_refl [(bv_unsigned sp + -192, bv_unsigned sp + -104)] m3) as MU3.
unfold A_TP. a4l. stash KD.
reenterA asegs A4L HIx asegs_wx HP3.
asan_chkA.
stepz. step. step. step. step. step.
unstash KD.
assert (CASES : ty = 5 \/ ty = 4 \/ ty = 1 \/ ty = 2 \/ ty = 3 \/ ty = 6) by lia.
destruct CASES as [-> | [-> | [-> | [-> | [-> | ->]]]]].
- step. if_lit. evt_done5. eapply (KD _ _ _ _ _); [eassumption | eassumption | eassumption | eassumption].
- step. if_lit. step. step. if_lit. evt_done5. eapply (KD _ _ _ _ _); [eassumption | eassumption | eassumption | eassumption].
- step. if_lit. step. step. if_lit. evt_done5. eapply (KD _ _ _ _ _); [eassumption | eassumption | eassumption | eassumption].
- step. if_lit. step. step. if_lit. evt_done5. eapply (KD _ _ _ _ _); [eassumption | eassumption | eassumption | eassumption].
- step. if_lit. step. step. if_lit. evt_done5. eapply (KD _ _ _ _ _); [eassumption | eassumption | eassumption | eassumption].
- step. if_lit. step. step. if_lit. evt_done5. eapply (KD _ _ _ _ _); [eassumption | eassumption | eassumption | eassumption].
Qed.

Lemma dc_tail0 :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(mc : word -> option byte) (mdc : config) (A : ASA A4L HIx) (Bc : bud) (Fr : Z) (v0 : word) (c24 : cell) (j16 : list byte)
(w0 : word) (frest : list cell) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : byte)
(d : jroot) (q np ty tojs pb : Z) (CBS REM : list blk),
dc_inv mc mdc -> fsaved F F1 -> frm0 fc1 ->
HEAPAx A (BS ++ CBS ++ REM ++ LB) LM ((Fr, 1) :: FRS) Bc mc mdc ->
rw_cells asegs mc ASP (dc_scr Fr v0 c24 j16) -> csize c24 = 8%nat ->
rw_cells asegs mc Fr (C8 w0 :: frest) -> Z.of_nat (cells_size frest) = 112 ->
rw_cells asegs mc (Fr / 8 + 2147450880) [C1 y0; C1 y1; C1 y2; C1 y3; C1 y4; C1 y5; C1 y6; C1 y7; C1 y8; C1 y9; C1 y10; C1 y11; C1 y12; C1 y13; C1 y14; C1 y15] ->
jroot_repA r mc BS p -> In (p, np) BS -> 48 <= np ->
rw_cells asegs mc p (jhdr_cells ty 1 tojs pb 0 0) ->
copy_of r d -> dc_cwA d CBS w -> q <> 0 -> dc_dst mc q -> jroot_repA d mc CBS q ->
bD B0 - w <= bD Bc -> bB B0 - DC_KB * w + 512 * Z.of_nat (length CBS) <= bB Bc ->
AJ5 A4L HIx A T mdc
(MS (mkR x1 (wz ASP) gp (wz A_TP) t0 t1 t2 sp (wz ASP) a0 a1 a2 a3 a4 a5 a6 a7
(wz (Fr / 8 + 2147450880)) x19 (wz 2147450880) x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
F1 (wz 0x9fba8) fc1 None mc (seg_rom asegs)).
Proof.
intros until REM. intros INV FS FRM1 HP SCR C24 FF FFsz FSH JRc INp Hnp SRC CO CW Hq [DC DSH] JD BDc BBc.
pose proof LOS as LOSu. unfold dc_stkA, DC_F, DC_C in LOSu. unfold ASP, dc_scr in *.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
destruct (dc_dfacts _ _ _ _ _ _ HP) as (D1 & D2 & D3 & D4 & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13).
pose proof (rw_cells_bound asegs mc D _ DC) as DR. cbn [cells_size csize Nat.add] in DR.
assert (INp2 : In (p, np) (BS ++ CBS ++ REM ++ LB)) by (apply in_or_app; left; exact INp).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p np HP ltac:(apply in_or_app; left; exact INp2)) as (_ & Hpal & Hplo & Hphi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p np 3 HP INp2 ltac:(lia) ltac:(lia)) as SHp3.
replace (p / 8 + 2147450880 + 3) with (p / 8 + 2147450883) in SHp3 by lia.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p np 4 HP INp2 ltac:(lia) ltac:(lia)) as SHp4.
replace (p / 8 + 2147450880 + 4) with (p / 8 + 2147450884) in SHp4 by lia.
set (sh := Fr / 8 + 2147450880) in *.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. change (hl_segs A4L) with asegs in MI.
pose proof (wmono_refl asegs mc) as WM. pose proof (munch_refl [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6434236, 6434240)] mc) as MU.
unfold jhdr_cells in SRC.

lazymatch type of SCR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?rest) => change (c0 :: c1 :: c2 :: c3 :: rest) with ([c0; c1; c2] ++ ([c3] ++ rest)) in SCR end.
destruct (proj1 (rw_cells_app asegs mc _ _ _) SCR) as [SCRa SCRx]. cbn [cells_size csize Nat.add] in SCRx.
destruct (proj1 (rw_cells_app asegs mc _ _ _) SCRx) as [SCR24 SCRb]. cbn [cells_size Nat.add] in SCRb. rewrite C24 in SCRb.
replace (bv_unsigned sp + -192 + Z.of_nat 24 + Z.of_nat (8 + 0)) with (bv_unsigned sp + -160) in SCRb by lia.
replace (bv_unsigned sp + -192 + Z.of_nat 24) with (bv_unsigned sp + -168) in SCR24 by lia.
stash SCR24. stash SCR. clear SCRx.
stash JD. stash JRc. stash CO. stash CW. stash INV.
unfold A_TP. a4l.
reenterA asegs A4L HIx asegs_wx HP.
step. step. step. step. if_lit.
step. asan_chkM 1.
step. step. asan_chkA.
step. step. step. step. if_falsex.
step. asan_chkA.
step. step. if_truex.
step. step.
evt_done5. unstash JD. unstash JRc. unstash CO. unstash CW. unstash INV. unstash SCR.
eapply (dc_epi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 mc mdc A Bc (BS ++ CBS ++ REM ++ LB) Fr 0);
[ exact INV | exact FS | exact FRM1 | exact HP | exact SCR | rewrite !cells_size_app; cbn [cells_size]; rewrite C24; reflexivity | exact FF | exact FFsz | exact FSH | exact JRc | ].
split; [exact BDc|]. left. split; [reflexivity|]. exists d, q, CBS, REM.
split; [reflexivity|]. split; [exact CO|]. split; [exact CW|]. split; [exact Hq|]. split; [exact DC|]. split; [exact JD | exact BBc].
Qed.
End MDcBase.
End RC__1.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdgq_c1 Q2Do.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.

Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun QWxq_c1.Mq0 Qfw3_c1.Mq2 Qc3B.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn.
Import Q6WR Q6WR.Mq0 QrPc.
Import Qvbw QYIF.
Import QnCn.Mq0 QR2u.

Import Q7UD QXUB.Mq0 Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QsKa.Mq4 QlKV.Mqa QsKa.Mq0 QJZd.Mq0 QsKa.Mq8 Qw5U.Mq0 QsKa.Mq3 Q2Do.Mq3.

Import Qvmy.Mq0 Qawr.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition VISIT_A : Z := 0xa3f90.
Definition JCVISIT_A : Z := 0xa3f28.
Definition EMIT_A : Z := 0x925a4.
Definition VIS_STK1 : Z := 176.
Definition VIS_STK0 : Z := 176 + 4096.

Section MJoVisit.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Notation joptA := (jopt asegs A4F).
Notation wz := (Z_to_bv 64).

Definition VIS (s : option jshape) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LBa BS LM : list blk) (FRS : list frame) (B : bud) (lo p : Z),
HEAPAx A LBa LM FRS B m md -> incl BS LBa ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - (VIS_STK0 + VIS_STK1 * odepth s) ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
tp = wz A_TP -> bv_unsigned ra mod 2 = 0 ->
joptA s m BS p -> Z.of_nat (length FRS) + (1 + odepth s) < 4096 ->
a0 = wz p -> a4 = wz EMIT_A ->
(forall ms' md' m' (A' : ASA A4L HIx),
ret_state A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (wz 0) m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (LBa ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' ->
HEAPAx A' LBa LM FRS B m' md' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz VISIT_A) fc None m (seg_rom asegs)).

Lemma vk_HEAPA : forall A LBa LM FRS B m md Fr lo SP mX,
HEAPAx A LBa LM ((Fr, 0) :: FRS) B m md -> alloc_ceiling <= lo -> SP <= hiA_top A4L HIx ->
munch [(lo, SP); (Fr, Fr + 56); (Fr / 8 + 2147450880, Fr / 8 + 2147450880 + 8)] m mX ->
wmono asegs m mX -> mem_inv asegs mX -> HEAPAx A LBa LM ((Fr, 0) :: FRS) B mX md.
Proof.
intros A LBa LM FRS B m md Fr lo SP mX HP LO HT MU WM MI.
eapply (fk0_HEAPA HIx); [exact HP | exact LO | exact HT | | exact WM | exact MI].
eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. intros a (H1 & H2 & H3 & _). repeat split; assumption.
Qed.

Lemma vk_pres : forall A LBa LM FRS B m md Fr lo SP mX,
HEAPAx A LBa LM ((Fr, 0) :: FRS) B m md -> alloc_ceiling <= lo -> alloc_ceiling <= SP ->
munch [(lo, SP); (Fr, Fr + 56); (Fr / 8 + 2147450880, Fr / 8 + 2147450880 + 8)] m mX ->
wmono asegs m mX -> heap_pres A4H (LBa ++ LM ++ fr_ivs A4L FRS) SP m mX.
Proof.
intros A LBa LM FRS B m md Fr lo SP mX HP LO HSP MU WM.
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
destruct (own_frame_fresh HIx Fr 0 LBa LBa LM FRS B A m md HP (incl_refl _)) as [OFF OFS].
eapply (heap_pres_of_munch A4H _ SP); [exact MU | exact WM |].
eapply (Q1Ey.client_outsideF HIx A LBa LM ((Fr, 0) :: FRS) B (LBa ++ LM ++ fr_ivs A4L FRS) m md _ SP HP); [| exact HSP |].
- intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. destruct Hb as [H|H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H].
- apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]].
+ left. cbn [fst snd]. lia.
+ right; right; right. exists Fr, 0. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. left. cbn [fst snd]. rewrite fr_size_0. lia.
+ right; right; right. exists Fr, 0. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. right. unfold shad. cbn [fst snd hl_sb A4L]. rewrite fr_shadow_len_0. unfold A_SB. lia.
Qed.

Lemma vis_pro :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LBa LM : list blk) (FRS : list frame) (B : bud) (lo : Z),
HEAPAx A LBa LM FRS B m md ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - VIS_STK0 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
tp = wz A_TP -> Z.of_nat (length FRS) < 4096 ->
(forall (ASP d Fr : Z) (m1 : word -> option byte) (md1 : config) (A1 : ASA A4L HIx) (jA jG jf : list byte)
(xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
(d = 0 \/ d = 16) -> ASP = bv_unsigned sp + -160 - d ->
HEAPAx A1 LBa LM ((Fr, 0) :: FRS) B m1 md1 ->
model_vm_only (cfg_model md) (cfg_model md1) ->
heap_pres A4H (LBa ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m1 ->
stk asegs m1 lo ASP ->
rw_cells asegs m1 (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs m1 ASP [CB 48 jA; C8 (wz Fr)] ->
rw_cells asegs m1 (ASP + 56) [CB (Z.to_nat d) jG] ->
rw_cells asegs m1 Fr [C8 (wz 1102416563); C8 (wz 0x13c47); C8 (wz 0xa3f90); CB 32 jf] ->
rw_cells asegs m1 (Fr / 8 + 2147450880) [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243)] ->
AJ5 A4L HIx A1 T md1
(MS (mkR xra (wz ASP) gp (wz 6434400) xt0 xt1 xt2 sp (wz ASP) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
(wz Fr) a4 a5 a0 (wz 2147450880) a2 a1 a3 (wz (Fr / 8 + 2147450880)) (wz Fr) xt3 xt4 xt5 xt6)
F (wz 0xa40a8) fc None m1 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz VISIT_A) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros HP ST LO LOS SPA HT TP FRN KP.
unfold VIS_STK0 in LOS. unfold VISIT_A. subst tp.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof alloc_ceiling_range as ACR.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HP) as (SB1 & SB2 & SB3 & SB4).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2. apply ro_C8_of_bytes_at in SB3.
assert (UARC : ro_cells asegs m (hl_uar_cell A4L) [C4 (Z_to_bv 64 1)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SB4]).
clear SB4. a4l.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp)] m) as MU.
unfold A_TP in *.
reenterA asegs A4L HIx asegs_wx HP.
carve_frame 160%nat ST.
step. stepz. do 13 step.
step. step.
rewrite (unsigned_lit (bv_unsigned sp + -160)) by lia. change 18446744073709551584 with (2^64 - 2^5). rewrite OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.land_align_down by lia. change (2^5) with 32.
assert (Hd : (bv_unsigned sp + -160) mod 32 = 0 \/ (bv_unsigned sp + -160) mod 32 = 16) by (clear - SPA; Z.div_mod_to_equations; lia).
lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?rest) => change (c0 :: c1 :: rest) with ([c0; c1] ++ rest) in FR end.
destruct (proj1 (rw_cells_app asegs m1 _ _ _) FR) as [LOW SAVE]. clear FR. cbn [cells_size csize Nat.add] in SAVE.
replace (bv_unsigned sp + -160 + Z.of_nat 56) with (bv_unsigned sp + -104) in SAVE by lia.
lazymatch type of LOW with rw_cells _ _ _ [C8 ?w; CB 48 ?jb] =>
apply (rw_cells_recast asegs _ _ _ [CB 56 (le8 w ++ jb)]) in LOW;
[| split; [| exact I]; cbn [cell_wf]; rewrite length_app, length_le8; destruct LOW as [[[_ [Hw _]] _] _]; cbn [cell_wf] in Hw; lia
| cbn [cells_bytes cbytes app]; rewrite ?app_nil_r; reflexivity | reflexivity] end.
lazymatch goal with |- evt _ ?Q (MS ?rg ?Fx ?pc ?fcx None ?mc ?rom) =>
let r' := open_constr:(mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in unify rg r';
lazymatch r' with mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31 =>
assert (REST : forall (ASP d : Z) (jA jG : list byte), (d = 0 \/ d = 16) -> ASP = bv_unsigned sp + -160 - d ->
stk asegs mc lo ASP -> rw_cells asegs mc ASP [CB 56 jA] -> rw_cells asegs mc (ASP + 56) [CB (Z.to_nat d) jG] ->
evt asegs Q (MS (mkR x1 (wz ASP) x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Fx pc fcx None mc rom))
end end.
2:{ destruct Hd as [Hd | Hd]; rewrite Hd.
- replace (bv_unsigned sp + -160 - 0) with (bv_unsigned sp + -160) by lia.
eapply (REST (bv_unsigned sp + -160) 0 _ []); [left; reflexivity | lia | exact ST | exact LOW |].
split; [split; [cbn; auto | cbn [cells_bytes cbytes app]; apply bytes_at_nil; lia] |].
unfold wr_at. cbn [cells_size csize Nat.add]. change (Z.of_nat 0) with 0. split; [lia|]. split; [lia|]. intros i Hi. lia.
- replace (bv_unsigned sp + -160 - 16) with (bv_unsigned sp + -176) by lia.
carve_frame 16%nat ST. rename FR into FRX.
destruct (rw_cells_CB_cut asegs _ _ _ _ 40%nat LOW ltac:(lia)) as [LOWa LOWb].
replace (bv_unsigned sp + -160 + Z.of_nat 40) with (bv_unsigned sp + -120) in LOWb by lia.
pose proof (rw_cells_CB_join asegs _ _ _ _ _ _ FRX ltac:(replace (bv_unsigned sp + -176 + Z.of_nat 16) with (bv_unsigned sp + -160) by lia; exact LOWa)) as JN.
eapply (REST (bv_unsigned sp + -176) 16 _ _); [right; reflexivity | lia | exact ST | exact JN |].
replace (bv_unsigned sp + -176 + 56) with (bv_unsigned sp + -120) by lia. exact LOWb. }
intros ASP d jA jG Hd0 HASP STa SCRA GAP. clear LOW ST Hd.
do 6 step. step. step. step. step. step. step. step.
norm_sx32. step. if_false. step. step.
evt_done5.
eapply (stack_malloc_full HIx) with (k := 0) (bytes := 64) (lo := lo) (LB := LBa) (LM := LM) (FR := FRS) (B := B);
[ heap_nowA A4L HIx HP MU WM MI | lia | .. ].
all: rewrite ?unsigned_lit by lia.
1: rewrite fr_size_0; lia.
1: reflexivity.
1: lia.
1: exact STa.
1: exact LO.
1: cbn [hl_stack_A A4L]; lia.
1: clear - SPA HASP Hd0; Z.div_mod_to_equations; lia.
1: lia.
1: reflexivity.
1: reflexivity.
intros ms1 m1' md1 A1 Fr RS1 VM1 ST1 HPR1 FRNZ (jff & FF1) SHB1 HP1. open_ret RS1.
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as (_ & HFal & HF0 & HFc & HFimg & _ & HFshw & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as HFapp.
rewrite fr_size_0 in HFal, HFc, HFimg, HFapp. rewrite fr_shadow_len_0 in HFshw. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFimg, HFapp.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in SAVE; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in SCRA; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in GAP; [| left; cbn [cells_size csize Nat.add]; lia].
change (hl_segs A4H) with asegs in SAVE, SCRA, GAP.
clear SB1 SB2 SB3 UARC.
assert (FSH1 : rw_cells asegs m1' (shad A4L Fr) [CB 8 (repeat (Z_to_bv 8 0) 8)]).
{ split; [split; [cbn; split; [reflexivity | exact I] | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SHB1] | exact HFshw]. }
rewrite fr_size_0 in FF1. change (Z.to_nat (64 - 8)) with 56%nat in FF1.
unfold shad in FSH1. a4l.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 8 <= 17594333495296) by (unfold sh; clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI1. change (hl_segs A4L) with asegs in MI1. clear MI.
assert (HPR01 : heap_pres A4H (LBa ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m1').
{ eapply heap_pres_trans.
- eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; exact Hb | clia |].
apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil].
- eapply heap_pres_weaken; [exact HPR1 | lia | intros b Hb; exact Hb]. }
clear MU WM. pose proof (wmono_refl asegs m1') as WM. pose proof (munch_refl [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8)] m1') as MU.
unfold A_SB in HFapp.
reenterA asegs A4L HIx asegs_wx HP1.
step. step. step. if_truex.
step.
step. step. step. step.
rewrite (unsigned_lit Fr) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
step. step. step. step. stepz. stepz. stepz. step. step.
fold sh.
stepz. stepz. stepz. stepz. step. stepz. stepz. stepz. stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m1' mc, WMc : wmono asegs m1' mc, MIc : mem_inv asegs mc |- _ =>
pose proof (vk_HEAPA _ _ _ _ _ _ _ _ _ _ _ HP1 LO HT MUc WMc MIc) as HP2;
pose proof (vk_pres _ _ _ _ _ _ _ _ lo (bv_unsigned sp) _ HP1 LO ltac:(lia) MUc WMc) as HPR12 end end.
evt_done5.
eapply (KP ASP d Fr _ md1 A1 _ jG); [exact Hd0 | exact HASP | exact HP2 | exact VM1 | eapply heap_pres_trans; [exact HPR01 | exact HPR12] | eassumption | eassumption | exact SCRA | eassumption | exact FF1 | exact FSH1].
Qed.

Lemma vis_epi :
forall (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(LBa LM : list blk) (FRS : list frame) (B : bud) (lo rv : Z),
alloc_ceiling <= lo -> lo <= bv_unsigned sp - VIS_STK0 -> bv_unsigned sp <= hiA_top A4L HIx -> 0 <= bv_unsigned sp < 2^64 ->
(forall ms' md' m' (A' : ASA A4L HIx),
ret_state A4H ra sp gp (wz 6434400) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (wz rv) m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (LBa ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' ->
HEAPAx A' LBa LM FRS B m' md' ->
AJ5 A4L HIx A' T md' ms') ->
forall (ASP d Fr : Z) (mX : word -> option byte) (mdX : config) (AX : ASA A4L HIx) (cs : list cell) (jG : list byte) (w0 : word) (frest : list cell)
(x0 x1 x2 x3 x4 x5 x6 x7 : byte)
(xra xt0 xt1 xt2 xs1 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 : word),
(d = 0 \/ d = 16) -> ASP = bv_unsigned sp + -160 - d ->
HEAPAx AX LBa LM ((Fr, 0) :: FRS) B mX mdX ->
model_vm_only (cfg_model md) (cfg_model mdX) ->
heap_pres A4H (LBa ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mX ->
stk asegs mX lo ASP ->
rw_cells asegs mX (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs mX ASP cs -> Z.of_nat (cells_size cs) = 56 ->
rw_cells asegs mX (ASP + 56) [CB (Z.to_nat d) jG] ->
rw_cells asegs mX Fr (C8 w0 :: frest) ->
rw_cells asegs mX (Fr / 8 + 2147450880) [C1 x0; C1 x1; C1 x2; C1 x3; C1 x4; C1 x5; C1 x6; C1 x7] ->
AJ5 A4L HIx AX T mdX
(MS (mkR xra (wz ASP) gp (wz 6434400) xt0 xt1 xt2 sp xs1 xa0 xa1 (wz rv) xa3 xa4 xa5 xa6 xa7
(wz Fr) xs3 xs4 xs5 xs6 xs7 xs8 xs9 (wz (Fr / 8 + 2147450880)) (wz Fr) xt3 xt4 xt5 xt6)
F (wz 0xa4118) fc None mX (seg_rom asegs)).
Proof.
intros until rv. intros LO LOS HT SPR K. unfold VIS_STK0 in LOS. intros until xt6. intros Hd0 HASP HPX VMX HPRX STX SAVE SCR SCRsz GAP FFX FSHX.
pose proof alloc_ceiling_range as ACR.
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HPX INF) as (_ & HFal & HF0 & HFc & HFimg & _ & _ & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HPX INF) as HFapp.
rewrite fr_size_0 in HFal, HFc, HFimg, HFapp. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFimg, HFapp. unfold A_SB in HFapp.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 8 <= 17594333495296) by (unfold sh; clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HPX) as MI. change (hl_segs A4L) with asegs in MI.
pose proof (wmono_refl asegs mX) as WM. pose proof (munch_refl [(lo, ASP); (Fr, Fr + 56); (sh, sh + 8)] mX) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HPX.
step. step. stepz. step. if_falsex. step. do 8 stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ mX mc, WMc : wmono asegs mX mc, MIc : mem_inv asegs mc |- _ =>
pose proof (vk_HEAPA _ _ _ _ _ _ _ _ lo ASP _ HPX LO ltac:(lia) MUc WMc MIc) as HPY;
pose proof (vk_pres _ _ _ _ _ _ _ _ lo ASP _ HPX LO ltac:(lia) MUc WMc) as HPRXY end end.
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
apply (rw_cells_transport asegs [(fp, fp + 1)] _ m5) in SAVE; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] _ m5) in SCR; [| exact MUr | exact WMr | cbn [disjoint_from]; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] _ m5) in GAP; [| exact MUr | exact WMr | cbn [disjoint_from cells_size csize Nat.add]; lia].
apply (stk_transport_disjoint asegs [(fp, fp + 1)] _ m5) in STX; [| exact MUr | exact WMr | cbn [disjoint_from]; lia].

eapply stk_release in SCR; [| exact STX | lia]. rewrite SCRsz in SCR.
eapply stk_release in GAP; [| exact SCR | lia]. cbn [cells_size csize] in GAP.
replace (ASP + 56 + Z.of_nat (Z.to_nat d + 0)) with (bv_unsigned sp + -104) in GAP by lia.
clear FPC.
change (672080 + 4) with 672084.
reenterA asegs A4L HIx asegs_wx HP5.
do 18 step.
lazymatch goal with H : rw_cells asegs ?mc (bv_unsigned sp + -104) _ |- _ => rename H into SAVE5 end.
rename GAP into ST5.
release_frame SAVE5 ST5 (bv_unsigned sp).
evt_done5.
eapply (K _ md5 m5 A5).
- do 14 eexists. reflexivity.
- eapply model_vm_only_trans; [exact VMX | exact VM5].
- exact ST5.
- eapply heap_pres_trans; [exact HPRX|]. eapply heap_pres_trans; [eapply heap_pres_weaken; [exact HPRXY | lia | intros b Hb; exact Hb] |].
eapply (heap_pres_of_presD (Fr + 32)).
+ eapply (presD_fp HIx _ _ _ _ _ _ _ _ (Fr + 32) _ (bv_unsigned sp) fp HPY); [| lia | exact FPnc | exact FPfr | exact Hoff | exact Hwv].
intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. destruct Hb as [H|H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H].
+ intros a Hd Hc.
destruct (own_frame_fresh HIx Fr 0 LBa LBa LM FRS B AX _ mdX HPY (incl_refl _)) as [OFF OFS].
assert (Ho : outside [(Fr + 32, Fr + 40)] a).
{ eapply (Q1Ey.client_outsideF HIx AX LBa LM ((Fr, 0) :: FRS) B (LBa ++ LM ++ fr_ivs A4L FRS) _ mdX [(Fr + 32, Fr + 40)] (bv_unsigned sp) HPY); [| lia | | lia | exact Hc].
- intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. destruct Hb as [H|H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H].
- apply Forall_cons; [| apply Forall_nil]. right; right; right. exists Fr, 0. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. left. cbn [fst snd]. rewrite fr_size_0. lia. }
cbn [outside] in Ho. lia.
- exact HP5.
Qed.

Lemma vis_null : VIS None.
Proof.
unfold VIS. intros until p. intros HP INC ST LO LOS SPA HT TP RA JO FRN A0 A4 K.
destruct JO as [-> ->]. cbn [odepth] in LOS, FRN. subst a0 a4 tp.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
eapply vis_pro; [exact HP | exact ST | exact LO | unfold VIS_STK0, VIS_STK1 in *; lia | exact SPA | exact HT | reflexivity | lia |].
intros ASP d Fr m1 md1 A1 jA jG jf xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 Hd0 HASP HP1 VM1 HPR1 ST1 SAVE SCRA GAP FF FSH.
unfold VIS_STK0, VIS_STK1 in LOS.
pose proof alloc_ceiling_range as ACR.
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as (_ & HFal & HF0 & HFc & HFimg & _ & _ & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as HFapp.
rewrite fr_size_0 in HFal, HFc, HFimg, HFapp. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFimg, HFapp. unfold A_SB in HFapp.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 8 <= 17594333495296) by (unfold sh; clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI. change (hl_segs A4L) with asegs in MI.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HP1) as (SB1 & SB2 & _ & _).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2. a4l.
pose proof (wmono_refl asegs m1) as WM. pose proof (munch_refl [(lo, ASP); (Fr, Fr + 56); (sh, sh + 8)] m1) as MU.
reenterA asegs A4L HIx asegs_wx HP1.
do 6 step. step.
unfold EMIT_A. replace (ret_pc (wz 0x925a4)) with (wz 0x925a4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
step. step.
replace (ret_pc (wz 0xa40c4)) with (wz 0xa40c4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
step. step. step. if_lit. step. step. if_lit. step. if_lit. step. step.

eapply evt_cut.
{ eapply jo_get_type_null_A with (lo := lo) (sbcell := 981752).
unfold small_pre, A_GOT_SB, A_SB. rewrite ?unsigned_lit by lia.
split; [assumption|]. split; [eassumption|]. split; [lia|]. split; [exact LO|]. split; [eassumption|]. split; [eassumption|]. lia. }
intros ms' (m' & (w & x & y & ->) & MUg & WMg & MIg & STg).
rewrite ?unsigned_lit in MUg, STg by lia.
lazymatch type of MUg with munch _ ?mq _ =>
transport_after_call asegs mq m' MUg WMg; try match goal with H : mem_inv asegs mq |- _ => clear H end; clear MUg WMg end.
replace (ret_pc (wz 0xa4104)) with (wz 0xa4104) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
step. step. step. if_lit. step. step. if_lit.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m1 mc, WMc : wmono asegs m1 mc, MIc : mem_inv asegs mc |- _ =>
pose proof (vk_HEAPA _ _ _ _ _ _ _ _ lo ASP _ HP1 LO ltac:(lia) MUc WMc MIc) as HPe;
pose proof (vk_pres _ _ _ _ _ _ _ _ lo ASP _ HP1 LO ltac:(lia) MUc WMc) as HPRe end end.
evt_done5.
eapply (vis_epi ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md T LBa LM FRS B lo 0 LO ltac:(unfold VIS_STK0; lia) HT SPR K ASP d Fr _ md1 A1 _ jG);
[ exact Hd0 | exact HASP | exact HPe | exact VM1
| eapply heap_pres_trans; [exact HPR1 | eapply heap_pres_weaken; [exact HPRe | lia | intros b Hb; exact Hb]]
| eassumption | eassumption | exact SCRA | reflexivity | eassumption | exact FF | exact FSH ].
Qed.

Lemma vis_scalar : forall s, jtype s <> JT_OBJECT -> jtype s <> JT_ARRAY -> VIS (Some s).
Proof.
intros s NO NA. unfold VIS. intros until p. intros HP INC ST LO LOS SPA HT TP RA JO FRN A0 A4 K.
destruct JO as [Hp J]. subst a0 a4 tp.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (DN : 0 <= odepth (Some s)) by (cbn [odepth]; apply sdepth_nonneg).
destruct (Qdgq_c1.jval_hdr_rd asegs A4F s m BS p 1 J) as (n & tojs & pb & udel & ud & INp & N48 & HDRH).
assert (INpA : In (p, n) (LBa ++ LM)) by (apply in_or_app; left; apply INC; exact INp).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p n HP INpA) as (_ & Hpal & Hplo & Hphi & _).
pose proof (jtype_range s) as TYR.
eapply vis_pro; [exact HP | exact ST | exact LO | unfold VIS_STK0, VIS_STK1 in *; lia | exact SPA | exact HT | reflexivity | lia |].
intros ASP d Fr m1 md1 A1 jA jG jf xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 Hd0 HASP HP1 VM1 HPR1 ST1 SAVE SCRA GAP FF FSH.
unfold VIS_STK0, VIS_STK1 in LOS.
pose proof alloc_ceiling_range as ACR.
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as (_ & HFal & HF0 & HFc & HFimg & _ & _ & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as HFapp.
rewrite fr_size_0 in HFal, HFc, HFimg, HFapp. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFimg, HFapp. unfold A_SB in HFapp.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 8 <= 17594333495296) by (unfold sh; clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI. change (hl_segs A4L) with asegs in MI.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HP1) as (SB1 & SB2 & _ & _).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in HDRH; [| eapply client_range_block; [apply in_or_app; left; apply INC; exact INp | lia | unfold jhdr_cells; cbn; lia]].
change (hl_segs A4H) with asegs in HDRH.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p n 0 HP1 ltac:(apply INC; exact INp) ltac:(lia) ltac:(lia)) as SH0. rewrite Z.add_0_r in SH0.
a4l.
pose proof (wmono_refl asegs m1) as WM. pose proof (munch_refl [(lo, ASP); (Fr, Fr + 56); (sh, sh + 8)] m1) as MU.
reenterA asegs A4L HIx asegs_wx HP1.
do 6 step. step.
unfold EMIT_A. replace (ret_pc (wz 0x925a4)) with (wz 0x925a4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
step. step.
replace (ret_pc (wz 0xa40c4)) with (wz 0xa40c4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
step. step. step. if_lit. step. step. if_lit. step. if_lit. step. step.

eapply evt_cut.
{ eapply jo_get_type_A with (lo := lo) (sbcell := 981752) (p := p) (ty := jtype s) (rc := 1) (tojs := tojs) (pb := pb) (udel := udel) (ud := ud).
- unfold small_pre, A_GOT_SB, A_SB. rewrite ?unsigned_lit by lia.
split; [assumption|]. split; [eassumption|]. split; [lia|]. split; [exact LO|]. split; [eassumption|]. split; [eassumption|]. lia.
- exact HDRH.
- lia.
- lia.
- clear - Hpal; Z.div_mod_to_equations; lia.
- lia.
- unfold A_SB. exact SH0.
- unfold A_SB. clear - Hphi ACR Hplo N48. Z.div_mod_to_equations; lia. }
intros ms' (m' & (w & x & y & ->) & MUg & WMg & MIg & STg).
rewrite ?unsigned_lit in MUg, STg by lia.
lazymatch type of MUg with munch _ ?mq _ =>
transport_after_call asegs mq m' MUg WMg; try match goal with H : mem_inv asegs mq |- _ => clear H end; clear MUg WMg end.
replace (ret_pc (wz 0xa4104)) with (wz 0xa4104) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
step. step.
assert (TC : jtype s <= 3 \/ jtype s = 6).
{ destruct s; cbn in *; unfold JT_BOOLEAN, JT_DOUBLE, JT_INT, JT_STRING, JT_OBJECT, JT_ARRAY in *; lia. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m1 mc, WMc : wmono asegs m1 mc, MIc : mem_inv asegs mc |- _ =>
pose proof (vk_HEAPA _ _ _ _ _ _ _ _ lo ASP _ HP1 LO ltac:(lia) MUc WMc MIc) as HPe;
pose proof (vk_pres _ _ _ _ _ _ _ _ lo ASP _ HP1 LO ltac:(lia) MUc WMc) as HPRe end end.
destruct TC as [T3 | T6].
-
step. if_falsex. step. step. if_falsex.
evt_done5.
eapply (vis_epi ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md T LBa LM FRS B lo 0 LO ltac:(unfold VIS_STK0; lia) HT SPR K ASP d Fr _ md1 A1 _ jG);
[ exact Hd0 | exact HASP | exact HPe | exact VM1
| eapply heap_pres_trans; [exact HPR1 | eapply heap_pres_weaken; [exact HPRe | lia | intros b Hb; exact Hb]]
| eassumption | eassumption | exact SCRA | reflexivity | eassumption | exact FF | exact FSH ].
-
rewrite T6 in *. step. if_lit. step. step. if_lit.
evt_done5.
eapply (vis_epi ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md T LBa LM FRS B lo 0 LO ltac:(unfold VIS_STK0; lia) HT SPR K ASP d Fr _ md1 A1 _ jG);
[ exact Hd0 | exact HASP | exact HPe | exact VM1
| eapply heap_pres_trans; [exact HPR1 | eapply heap_pres_weaken; [exact HPRe | lia | intros b Hb; exact Hb]]
| eassumption | eassumption | exact SCRA | reflexivity | eassumption | exact FF | exact FSH ].
Qed.

Lemma vis_tail :
forall (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(LBa LM : list blk) (FRS : list frame) (B : bud) (lo : Z),
alloc_ceiling <= lo -> lo <= bv_unsigned sp - VIS_STK0 -> bv_unsigned sp <= hiA_top A4L HIx -> 0 <= bv_unsigned sp < 2^64 ->
(forall ms' md' m' (A' : ASA A4L HIx),
ret_state A4H ra sp gp (wz 6434400) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (wz 0) m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (LBa ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' ->
HEAPAx A' LBa LM FRS B m' md' ->
AJ5 A4L HIx A' T md' ms') ->
forall (ASP d Fr : Z) (mX : word -> option byte) (mdX : config) (AX : ASA A4L HIx) (j0 jG : list byte) (w8 w0 : word) (srest frest : list cell)
(x0 x1 x2 x3 x4 x5 x6 x7 : byte) (jsow uaw keyw parw : word)
(xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 xt5 xt6 : word),
(d = 0 \/ d = 16) -> ASP = bv_unsigned sp + -160 - d ->
HEAPAx AX LBa LM ((Fr, 0) :: FRS) B mX mdX ->
model_vm_only (cfg_model md) (cfg_model mdX) ->
heap_pres A4H (LBa ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mX ->
stk asegs mX lo ASP ->
rw_cells asegs mX (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs mX ASP (CB 8 j0 :: C8 w8 :: srest) -> Z.of_nat (cells_size srest) = 40 ->
rw_cells asegs mX (ASP + 56) [CB (Z.to_nat d) jG] ->
rw_cells asegs mX Fr (C8 w0 :: frest) ->
rw_cells asegs mX (Fr / 8 + 2147450880) [C1 x0; C1 x1; C1 x2; C1 x3; C1 x4; C1 x5; C1 x6; C1 x7] ->
AJ5 A4L HIx AX T mdX
(MS (mkR xra (wz ASP) gp (wz 6434400) xt0 xt1 xt2 sp (wz ASP) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
(wz Fr) (wz EMIT_A) uaw jsow (wz 2147450880) keyw parw xs9 (wz (Fr / 8 + 2147450880)) (wz Fr) xt3 xt4 xt5 xt6)
F (wz 0xa4338) fc None mX (seg_rom asegs)).
Proof.
intros until lo. intros LO LOS HT SPR K. intros until xt6. intros Hd0 HASP HPX VMX HPRX STX SAVE SCR SCRsz GAP FFX FSHX.
pose proof LOS as LOS'. unfold VIS_STK0 in LOS'.
pose proof alloc_ceiling_range as ACR.
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HPX INF) as (_ & HFal & HF0 & HFc & HFimg & _ & _ & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HPX INF) as HFapp.
rewrite fr_size_0 in HFal, HFc, HFimg, HFapp. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFimg, HFapp. unfold A_SB in HFapp.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 8 <= 17594333495296) by (unfold sh; clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HPX) as MI. change (hl_segs A4L) with asegs in MI.
pose proof (wmono_refl asegs mX) as WM. pose proof (munch_refl [(lo, ASP); (Fr, Fr + 56); (sh, sh + 8)] mX) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HPX.
do 6 step. step.
unfold EMIT_A. replace (ret_pc (wz 0x925a4)) with (wz 0x925a4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
step. step.
replace (ret_pc (wz 0xa4354)) with (wz 0xa4354) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
step. step. step. if_lit. step. step. if_lit. step. if_lit.
evt_done5.
eapply (vis_epi ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md T LBa LM FRS B lo 0 LO LOS HT SPR K ASP d Fr _ mdX AX _ jG);
[ exact Hd0 | exact HASP | exact HPX | exact VMX | exact HPRX | eassumption | eassumption | eassumption
| cbn [cells_size csize Nat.add]; lia | eassumption | eassumption | exact FSHX ].
Qed.
End MJoVisit.
End RC__1.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI QRBl QDwa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QJjn Q8tj. Import Qu4M.Mq0.
Import QbFI. Import QRBl. Import Qhd4.
Import Qwm6.Mq4 QlKV.Mqh QsKa.Mqe QsKa.Mqd QDwa Qiiq. Import QlKV.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition strdup_costB (klen : Z) : Z := 16 * (klen + 1) + 512.

Definition oadd_costB (klen cap cnt : Z) : Z := strdup_costB klen + ins_costB cap cnt.

Definition obj_grownA (cap cnt cap' : Z) : Prop := (cap' = cap /\ cnt < lf_thr cap) \/ (cap' = lh_ns cap /\ lf_thr cap <= cnt).

Definition json_object_object_add_A_entry : Z := 0x9d820.

Section S.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Definition jo_post_framexA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (lo : Z)
(r : Z) (m' : word -> option byte) (ms' : machine_state) (md' : config) : Prop :=
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_presx A4H a4_volatile (LB ++ LM) (bv_unsigned sp) m m' /\
(exists errv', rw_cells asegs m' A_ERRNO [C4 errv']).

Definition jo_object_add_A_stmt (entry stkb : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB OBS VBS LM : list blk) (FRS : list frame) (B : bud) (lo p v k kn : Z) (ks : list byte)
(kids : list (option jshape)) (vs : option jshape) (errv : word),
jo_preA HIx A (OBS ++ VBS ++ LB) LM FRS B m md sp tp ra lo stkb errv -> lh_globA m ->
jval asegs A4F (Sobj kids) m OBS p 1 -> jopt asegs A4F vs m VBS v ->
In (k, kn) LB -> cstr asegs m k kn ks -> kn <= 2^31 ->
frm0 fc ->
Z.of_nat (length FRS) < 4096 ->
a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 k -> a2 = Z_to_bv 64 v ->
oadd_costB (Z.of_nat (length ks)) (obj_capA OBS) (Z.of_nat (length kids)) <= bB B ->
512 * Z.of_nat (length OBS) <= bB B ->
0 <= bD B ->
(forall ms' md' m' r (A' : ASA A4L HIx) (B' : bud),
jo_post_framexA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB (LM ++ fr_ivs A4L FRS) lo r m' ms' md' ->
lh_globA m' -> bD B <= bD B' ->
((r = 0 /\ exists OBS' kids', jval asegs A4F (Sobj kids') m' OBS' p 1 /\ HEAPAx A' (OBS' ++ LB) LM FRS B' m' md'
/\ Z.of_nat (length kids') <= Z.of_nat (length kids) + 1
/\ okmax kids' <= Z.max (okmax kids) (odep vs)
/\ ( (
Z.of_nat (length kids') = Z.of_nat (length kids) + 1
/\ bB B - oadd_costB (Z.of_nat (length ks)) (obj_capA OBS) (Z.of_nat (length kids)) <= bB B'
/\ Z.of_nat (length OBS') = Z.of_nat (length OBS) + Z.of_nat (length VBS) + 1
/\ obj_grownA (obj_capA OBS) (Z.of_nat (length kids)) (obj_capA OBS')
/\ (forall w wv, jtx (Sobj kids) OBS = Some (w, []) -> jtx_opt vs VBS = Some (wv, []) ->
jtx (Sobj kids') OBS' = Some (w + (key_w (Z.of_nat (length ks) + 1) + wv), [])))
\/ (
Z.of_nat (length kids') = Z.of_nat (length kids)
/\ bB B - 512 * (Z.of_nat (length OBS) + Z.of_nat (length VBS) - Z.of_nat (length OBS')) <= bB B'
/\ Z.of_nat (length OBS') <= Z.of_nat (length OBS) + Z.of_nat (length VBS)
/\ obj_capA OBS' = obj_capA OBS
/\ (forall w wv, jtx (Sobj kids) OBS = Some (w, []) -> jtx_opt vs VBS = Some (wv, []) ->
exists w', jtx (Sobj kids') OBS' = Some (w', []) /\ w' <= w + wv)))) \/
(r = 2^64 - 1 /\ exists REM, jval asegs A4F (Sobj kids) m' OBS p 1 /\ jopt asegs A4F vs m' VBS v
/\ HEAPAx A' (OBS ++ VBS ++ REM ++ LB) LM FRS B' m' md'
/\ bB B - oadd_costB (Z.of_nat (length ks)) (obj_capA OBS) (Z.of_nat (length kids)) <= bB B')) ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

End S.

Definition jo_object_add_A (HIx : heap_iface_A A4L) (HD : Z) := jo_object_add_A_stmt HIx json_object_object_add_A_entry (80 + 96 + 4096 + 144 + HD).

End RC__1.
End Mq4.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn QKQo Q8tj.
Import QSL3. Import QAIk.
Import QnCn.Mq0.
Import Q6WR Q6WR.Mq0 QrPc. Import QeuE.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqg QsKa.Mqc Q30W.Mq4 QsKa.Mqe Q30W.Mq5 QlKV.Mqd QnDr.Mq4 Qiiq.Mq9 QkXq.Mq7 Qiiq.Mqb QeVJ.Mq2 QhPX.Mq4 QhPX.Mq3 QWQx.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section Loop3A.
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
Notation NEXT := (next_postA HIx sp gp lo errv LM FRS).

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
Notation head_stmt' := (head_stmtA HIx sp gp lo errv LM FRS).
Notation cont_stmt' := (cont_stmtA HIx sp gp lo errv LM FRS).
Notation body_stmt' := (body_stmtA HIx sp gp lo errv LM FRS).

Ltac shadowN HP a n Hin SH :=
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ a n HP Hin) as SH;
unfold shad in SH; apply shadow_ro_cells in SH;
let cs := eval cbv in (shadow_cells n) in change (shadow_cells n) with cs in SH.

Lemma zcont_len : forall isobj m x q kids nz cur XBS,
zcont isobj m x q kids nz cur XBS -> Z.of_nat (length kids) < 2^62.
Proof.
clear. intros isobj m x q kids nz cur XBS ZC. destruct isobj.
- destruct ZC as (t & tbl & size & es & svs & Z0 & _).
destruct Z0 as (pb & PBS & KBS & esk & esz & Ees & Lz & Fz & EX & OPB & HDR & OPEN & OK).
pose proof (okids_len _ _ _ _ _ _ OK) as [L1 _]. rewrite length_map in L1.
pose proof OPEN as (_ & _ & _ & _ & Hsz & Hcnt & _). pose proof (lf_thr_lt size Hsz). pose proof (lf_size_range size Hsz).
assert (length esk <= length es)%nat by (rewrite Ees, length_app; lia). lia.
- destruct ZC as (a & arr & size & pb & PBS & KBS & ps & EX & OPB & HDR & AL & OK).
pose proof (okids_len _ _ _ _ _ _ OK) as [L1 _].
destruct AL as (arr' & size' & junk & E & Hlen & Hsz & _). rewrite length_app in Hlen. lia.
Qed.

Lemma cont_okA : forall isobj kids,
(forall kids1 kl, kids = kids1 ++ [kl] -> body_stmt' isobj kids1 kl) -> cont_stmt' isobj kids.
Proof.
intros isobj kids BODY. unfold cont_stmtA. intros until cur. intros HP ZC ST ERR BB [sbs SPL] K.
unfold_consts. word_range sp SPW.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (zcont_len _ _ _ _ _ _ _ _ ZC) as LK.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [] m) as MU.
reenterA asegs A4L HIx asegs_wx HP.
bstep. bstep. bstep.
destruct (snoc_inv_gen kids) as [-> | (kids1 & kl & ->)].
- cbn [length Z.of_nat Z.add]. if_true.
evt_done5.
eapply (pop_okA HIx sp gp lo errv LM FRS LO LOS SPA HT isobj); [exact HP | | exact ST | exact ERR | exact BB | spl | exact K].
destruct isobj; [destruct ZC as (t & tbl & size & es & svs & Z0 & _); exists t, tbl, size, es, svs; exact Z0 | exact ZC].
- rewrite length_app in LK |- *. cbn [length] in LK |- *.
if_falsex.
replace (Z.of_nat (length kids1 + 1) + -1) with (Z.of_nat (length kids1)) by lia.
evt_done5.
eapply (BODY kids1 kl eq_refl); [exact HP | | exact ST | exact ERR | exact BB | spl | exact K].
destruct isobj.
+ destruct ZC as (t & tbl & size & es & svs & Z0 & CUR). destruct (CUR kids1 kl eq_refl) as (e & He & Ec).
exists t, tbl, size, es, svs, e. split; [exact Z0 | split; [exact He | exact Ec]].
+ exact ZC.
Qed.

Lemma head_okA : forall isobj kids,
(forall kids1 kl, kids = kids1 ++ [kl] -> body_stmt' isobj kids1 kl) -> head_stmt' isobj kids.
Proof.
intros isobj kids BODY. unfold head_stmtA. intros until T. intros HP ZH ST ERR BB [sbs SPL] K.
unfold_consts. word_range sp SPW.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(lo, bv_unsigned sp + -104)] m) as MU.
assert (KW : forall mm (MUm : munch [(lo, bv_unsigned sp + -104)] m mm) (WMm : wmono asegs m mm) ms' md' A',
NEXT q F1 fc1 mm md LB B (512 * Z.of_nat (length XBS)) ms' md' A' -> AJ5 A4L HIx A' T md' ms').
{ intros mm MUm WMm ms' md' A' NP. apply K. eapply next_postA_w; [apply fsaved_refl | intros Hf; exact Hf | apply model_vm_only_refl | | | | exact NP |]; [| instantiate (1 := 0); lia | lia | lia].
eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp + -104)); [exact MUm | exact WMm |].
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; apply in_or_app; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb] | clia |].
apply Forall_cons; [cbn [fst snd]; left; clia | apply Forall_nil]. }
destruct isobj.
- destruct ZH as (t & tbl & size & es & svs & Z0).
pose proof Z0 as (pb & PBS & KBS & esk & esz & Ees & Lz & Fz & EX & OPB & HDR & OPEN & OK).
pose proof (okids_len _ _ _ _ _ _ OK) as [L1 _]. rewrite length_map in L1.
destruct esz; [| cbn in Lz; discriminate]. rewrite app_nil_r in Ees. subst esk.
pose proof OPEN as (HDRT & _ & _ & _ & Hsz & Hcnt & Hlen). unfold lh_hdrf in HDRT.
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR.
assert (HPl : HEAPAx A (lh_blocks t tbl size es ++ ((x, 48) :: concat KBS ++ PBS ++ LB)) LM FRS B m md).
{ eapply (heapA_perm A4L HIx); [exact HP | rewrite EX; hperm | apply Permutation_refl | apply Permutation_refl]. }
destruct (lh_heap_factsA HIx _ _ _ _ _ _ _ _ _ _ _ HPl) as ((Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & Httb & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hbhi. clear HPl.
assert (INx : In (x, 48) (XBS ++ LB)) by (rewrite EX; in_elem).
assert (INt : In (t, 56) (XBS ++ LB)) by (rewrite EX; unfold lh_blocks; in_elem).
assert (INx2 : In (x, 48) ((XBS ++ LB) ++ LM)) by (apply in_or_app; left; exact INx).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ x 48 HP INx2) as (_ & Hxal & Hxlo & Hxhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ x 48 HP INx2) as Hximg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hxhi.
assert (LT : lhtab2 asegs A4F m (lh_blocks t tbl size es) t (map (fun e => (le_k e, le_v e)) es)).
{ exists tbl, size, es, svs. split; [reflexivity|]. split; [reflexivity | exact OPEN]. }
shadowN HP x 48 INx SHx. shadowN HP t 56 INt SHt.
a4l. destruct (proj1 (ro_cells_app asegs m (t / 8 + 2147450880) [C1 (Z_to_bv 8 0)] _) SHt) as [SHt0 _].
unfold jhdr_cells in HDR. cbn [app fn_obj_to_json_string A4F] in HDR.
stash OPB. stash OK. stash Z0.
reenterA asegs A4L HIx asegs_wx HP.
bstep.
bstepz.
bstep. ub_resolve.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch type of LT with lhtab2 _ _ _ ?L ?tt ?kv =>
assert (LTc : lhtab2 asegs A4F mc L tt kv);
[ exists tbl, size, es, svs; split; [reflexivity|]; split; [reflexivity|];
eapply (lh_open_agree asegs A4F); [exact OPEN | eapply (agree_of_munch asegs); [exact MU | exact WM |] | apply incl_refl];
intros b_ kk_ Hb_; pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ b_ kk_ HP ltac:(apply in_or_app; left; rewrite EX; in_sub Hb_)) as (Hk0_ & _ & _ & Hbhi_ & _);
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hbhi_; cbn; lia
| clear LT; rename LTc into LT ] end end.
asan_chk0.
bstep. asan_chkA.
bstep. norm_w32. bstep. bstep. if_false.
bstep.
callS (lh_table_length_A _ SPR gp TP _ _ _ (Z_to_bv 64 x) (Z_to_bv 64 (x + 40)) (Z_to_bv 64 4) _ _ _ _ _ _ x18 x19 x20 x21 (Z_to_bv 64 (x / 8 + 2147450885)) SBR (Z_to_bv 64 4)
(Z_to_bv 64 (x / 8 + 2147450880)) (Z_to_bv 64 5) CM1 _ _ _ _ F1 fc1 _ lo _ (lh_blocks t tbl size es) t (map (fun e => (le_k e, le_v e)) es)).
all: try (unfold small_pre; rewrite ?unsigned_lit by lia; split; [exact MI|]; spl; split; [exact ST|]; split; [lia|]; split; [lia|]; split; [exact GOT|]; split; [exact CELL|];
unfold alloc_ceiling, sp_window_lo, stack_max_size; lia).
all: try exact LT. all: try exact SHt0.
all: try (unfold A_SB; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia).
all: try first [reflexivity | lia].
rewrite length_map.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
match goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
match goal with H : stk asegs m2 _ _ |- _ => rename H into ST2 end.
assert (HP2 : HEAPAx A (XBS ++ LB) LM FRS B m2 md) by heap_nowA A4L HIx HP MU WM MI2.
try clear SHx; try clear SHt; try clear SHt0.
shadowN HP2 x 48 INx SHx. shadowN HP2 t 56 INt SHt. a4l.
bstep. bstep. if_false. rewrite ?sxb_zero, ?zxb_zero.
bstep. bstep. asan_chkA.
bstep.
bstep.
assert (Z2 : zobj asegs A4F m2 x q kids 0 t tbl size es svs XBS).
{ unstash Z0. eapply (zobj_agree asegs A4F (XBS ++ LB)); [exact Z0 | eapply (agree_of_munch asegs); [exact MU | exact WM |] | intros b Hb; in_sub Hb].
intros b kk Hb. pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ b kk HP ltac:(apply in_or_app; left; exact Hb)) as (Hk0 & _ & _ & Hbhi' & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hbhi'. cbn. lia. }
destruct (snoc_inv_gen kids) as [-> | (kids1 & kl & ->)].
+ destruct es; [| cbn in L1; discriminate]. cbn [length Z.of_nat]. if_false. bstep.
evt_done5.
eapply (pop_okA HIx sp gp lo errv LM FRS LO LOS SPA HT true); [exact HP2 | exists t, tbl, size, (@nil lent), svs; exact Z2 | exact ST2 | assumption | exact BB | spl | exact (KW m2 MU WM)].
+ rewrite length_app in L1. cbn [length] in L1.
if_truex. bstep. bstep. bstep.
replace (Z.of_nat (length es) + -1) with (Z.of_nat (length kids1)) by lia.
destruct (snoc_inv_gen es) as [-> | (es1 & el & ->)]; [cbn in L1; lia|].
rewrite length_app in L1. cbn [length] in L1.
rewrite (tl_of_last tbl (es1 ++ [el]) (length kids1) el) by (first [rewrite nth_error_app2 by lia; replace (length kids1 - length es1)%nat with 0%nat by lia; reflexivity | rewrite length_app; cbn; lia]).
evt_done5. change (Z_to_bv 64 1) with (Z_to_bv 64 (Z.of_nat 0 + 1)).
eapply (BODY kids1 kl eq_refl); [exact HP2 | | exact ST2 | assumption | exact BB | spl | exact (KW m2 MU WM)].
exists t, tbl, size, (es1 ++ [el]), svs, el. split; [exact Z2 | split; [rewrite nth_error_app2 by lia; replace (length kids1 - length es1)%nat with 0%nat by lia; reflexivity | reflexivity]].
- destruct ZH as (a & arr & size & Z0).
pose proof Z0 as (pb & PBS & KBS & ps & EX & OPB & HDR & AL & OK).
pose proof (okids_len _ _ _ _ _ _ OK) as [L1 _]. cbn [repeat] in AL. rewrite app_nil_r in AL.
pose proof AL as (arr' & size' & junk & Eal & Hlen & Hsz & _ & _). injection Eal as E1 E2. assert (size' = size) by lia. subst arr' size'. clear E2.
assert (INx : In (x, 48) (XBS ++ LB)) by (rewrite EX; in_elem).
assert (INa : In (a, 32) (XBS ++ LB)) by (rewrite EX; in_elem).
assert (INr : In (arr, 8 * size) (XBS ++ LB)) by (rewrite EX; in_elem).
assert (INx2 : In (x, 48) ((XBS ++ LB) ++ LM)) by (apply in_or_app; left; exact INx).
assert (INa2 : In (a, 32) ((XBS ++ LB) ++ LM)) by (apply in_or_app; left; exact INa).
assert (INr2 : In (arr, 8 * size) ((XBS ++ LB) ++ LM)) by (apply in_or_app; left; exact INr).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ x 48 HP INx2) as (_ & Hxal & Hxlo & Hxhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ x 48 HP INx2) as Hximg.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a 32 HP INa2) as (_ & Haal & Halo & Hahi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ arr (8 * size) HP INr2) as (Hr0 & Hral & Hrlo & Hrhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hxhi, Hahi, Hrhi.
shadowN HP x 48 INx SHx. shadowN HP a 32 INa SHa. a4l.
unfold jhdr_cells in HDR. cbn [app fn_arr_to_json_string A4F] in HDR.
stash OPB. stash OK. stash Z0.
reenterA asegs A4L HIx asegs_wx HP.
bstep.
bstepz.
bstep. ub_resolve.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch type of AL with alist _ _ _ ?L ?aa ?pp =>
assert (ALc : alist asegs A4F mc L aa pp);
[ eapply (alist_agree asegs A4F); [exact AL | eapply (agree_of_munch asegs); [exact MU | exact WM |] | apply incl_refl];
intros b_ kk_ Hb_; pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ b_ kk_ HP ltac:(apply in_or_app; left; rewrite EX; in_sub Hb_)) as (Hk0_ & _ & _ & Hbhi_ & _);
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hbhi_; cbn; lia
| clear AL; rename ALc into AL ] end end.
asan_chk0.
bstep. asan_chkA.
bstep. norm_w32. bstep. bstep. if_true.
bstep.
callA (array_list_length_A _ SPR gp TP _ _ _ (Z_to_bv 64 x) (Z_to_bv 64 (x + 40)) _ _ _ x18 x19 x20 x21 (Z_to_bv 64 (x / 8 + 2147450885)) SBR (Z_to_bv 64 4)
(Z_to_bv 64 (x / 8 + 2147450880)) (Z_to_bv 64 5) CM1 _ _ _ _ F1 fc1 _ _ _ _ _ _ lo _ a arr size ps).
all: try (unfold small_pre; rewrite ?unsigned_lit by lia; split; [exact MI|]; spl; split; [exact ST|]; split; [lia|]; split; [lia|]; split; [exact GOT|]; split; [exact CELL|];
unfold alloc_ceiling, sp_window_lo, stack_max_size; lia).
all: try exact AL. all: try exact SHa.
all: try (unfold al_blkA; unfold alloc_ceiling, sp_window_lo, stack_max_size; lia).
all: try first [reflexivity | lia].
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
match goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
match goal with H : stk asegs m2 _ _ |- _ => rename H into ST2 end.
assert (HP2 : HEAPAx A (XBS ++ LB) LM FRS B m2 md) by heap_nowA A4L HIx HP MU WM MI2.
bstep. bstep.
assert (Z2 : zarr asegs A4F m2 x q kids 0 a arr size XBS).
{ unstash Z0. eapply (zarr_agree asegs A4F (XBS ++ LB)); [exact Z0 | eapply (agree_of_munch asegs); [exact MU | exact WM |] | intros b Hb; in_sub Hb].
intros b kk Hb. pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ b kk HP ltac:(apply in_or_app; left; exact Hb)) as (Hk0 & _ & _ & Hbhi' & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hbhi'. cbn. lia. }
destruct (snoc_inv_gen kids) as [-> | (kids1 & kl & ->)].
+ destruct ps; [| cbn in L1; discriminate]. cbn [length Z.of_nat]. if_true.
evt_done5.
eapply (pop_okA HIx sp gp lo errv LM FRS LO LOS SPA HT false); [exact HP2 | exists a, arr, size; exact Z2 | exact ST2 | assumption | exact BB | spl | exact (KW m2 MU WM)].
+ rewrite length_app in L1. cbn [length] in L1.
if_falsex. bstep. bstep. bstep.
replace (Z.of_nat (length ps) + -1) with (Z.of_nat (length kids1)) by lia.
evt_done5. change (Z_to_bv 64 1) with (Z_to_bv 64 (Z.of_nat 0 + 1)).
eapply (BODY kids1 kl eq_refl); [exact HP2 | exists a, arr, size; exact Z2 | exact ST2 | assumption | exact BB | spl | exact (KW m2 MU WM)].
Qed.

Lemma loop_allA : forall isobj kids, kids_descA HIx sp gp lo errv LM FRS kids -> cont_stmt' isobj kids /\ head_stmt' isobj kids.
Proof.
intros isobj kids. induction kids as [|k kids IH] using rev_ind; intros KD.
- split; [apply cont_okA | apply head_okA]; intros kids1 kl E; destruct kids1; discriminate.
- assert (KD1 : kids_descA HIx sp gp lo errv LM FRS kids) by (intros k' Hk'; apply KD; apply in_or_app; left; exact Hk').
destruct (IH KD1) as [CONT HEAD].
assert (B : body_stmt' isobj kids k).
{ destruct isobj; [apply (body_obj_okA HIx sp gp lo errv LM FRS LO LOS SPA HT DEL) | apply (body_arr_okA HIx sp gp lo errv LM FRS LO LOS SPA HT)];
try assumption; apply KD; apply in_or_app; right; left; reflexivity. }
split; [apply cont_okA | apply head_okA]; intros kids1 kl E; apply app_inj_last in E as [<- <-]; exact B.
Qed.

Theorem desc_allA : forall c, desc_stmtA HIx sp gp lo errv LM FRS c.
Proof.
apply jshape_ind2; try (intros; exact I).
- intros kids IH. cbn. apply (proj2 (loop_allA true kids ltac:(intros [c|] Hin; [exact (IH c Hin) | exact I]))).
- intros kids IH. cbn. apply (proj2 (loop_allA false kids ltac:(intros [c|] Hin; [exact (IH c Hin) | exact I]))).
Qed.
End Loop3A.
End RC__1.
End Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSHS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.

Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun QWxq_c1.Mq0 Qfw3_c1.Mq2 Qc3B Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn QKQo Q8tj QRUw.Mq2.
Import QSL3.
Import Qvbw QYIF.
Import QnCn.Mq0 QR2u.

Import QbFI QXUB. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QsKa.Mqd QlKV.Mqj QsKa.Mqg QsKa.Mq9 QJZd.Mq9 QsKa.Mqh Qw5U.Mq5 QsKa.Mqc QsKa.Mqb QlKV.Mqh QsKa.Mqe QlKV.Mqf. Import QlKV.Mq2 QsKa. Import Qiiq.

Import Qvmy Qawr.
Import Qwm6.Mq2.
Import QB6X.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition DCR_A : Z := 0xa15e8.
Definition DC_A : Z := 0xa14d8.
Definition DC_KB : Z := 646.
Definition DC_F : Z := 192.
Definition DC_C : Z := 8720 + 64.
Definition dc_stkA (d : Z) : Z := DC_F + DC_C + DC_F * d.

Section MDcDefs.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Notation wz := (Z_to_bv 64).
Notation jroot_repA := (jroot_rep A4H A4F).

Definition fresA (m : word -> option byte) (CBS : list blk) (q : Z) : Prop :=
(q = 0 /\ CBS = []) \/ (q <> 0 /\ exists s, jval asegs A4F s m CBS q 1).

Definition dc_wtA (r : jroot) (m : word -> option byte) (BS : list blk) (p w : Z) : Prop :=
match r with
| JRtree s => exists Y R, jtx s (BS ++ Y) = Some (w, R)
| JRstrx => exists L, str_lenA m p L /\ 6 * Z.max L 8 + 2 <= w
| JRdblx _ => 9 <= w
| JRnull => False
end.

Definition dc_cwA (d : jroot) (CBS : list blk) (w : Z) : Prop :=
match d with JRtree s' => exists w', jtx s' CBS = Some (w', []) /\ w' <= w | _ => True end.

Definition dc_resA (r : jroot) (BS LB LM : list blk) (FRS : list frame) (D w : Z) (B : bud)
(m' : word -> option byte) (md' : config) (rv : Z) (A' : ASA A4L HIx) (B' : bud) : Prop :=
bD B - w <= bD B' /\
( (rv = 0 /\ exists (d : jroot) (q : Z) (CBS REM : list blk),
copy_of r d /\ dc_cwA d CBS w /\ q <> 0 /\ rw_cells asegs m' D [C8 (wz q)] /\ jroot_repA d m' CBS q /\
bB B - DC_KB * w + 512 * Z.of_nat (length CBS) <= bB B' /\
HEAPAx A' (BS ++ CBS ++ REM ++ LB) LM FRS B' m' md')
\/ (rv = 2^64 - 1 /\ exists (q : Z) (CBS REM : list blk),
rw_cells asegs m' D [C8 (wz q)] /\ fresA m' CBS q /\
bB B - DC_KB * w + 512 * Z.of_nat (length CBS) <= bB B' /\
HEAPAx A' (BS ++ CBS ++ REM ++ LB) LM FRS B' m' md') ).

Definition DCOPY (r : jroot) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB BS LM : list blk) (FRS : list frame) (B : bud) (lo p D w : Z) (errv : word),
HEAPAx A (BS ++ LB) LM FRS B m md -> jroot_repA r m BS p -> r <> JRnull -> lh_globA m ->
rw_cells asegs m D [C8 (wz 0)] -> arg_locA FRS D 8 -> unpoisoned asegs m A_SB D 8 -> D mod 8 = 0 ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - dc_stkA (rdepth r) ->
bv_unsigned sp mod 32 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> tp = wz A_TP -> bv_unsigned ra mod 2 = 0 -> frm0 fc ->
Z.of_nat (length FRS) + (1 + rdepth r) < 4096 ->
dc_wtA r m BS p w -> w < 2^28 -> DC_KB * w <= bB B -> w <= bD B ->
a0 = wz p -> a4 = wz D -> a5 = wz SH_A ->
(forall ms' md' m' rv (A' : ASA A4L HIx) (B' : bud),
jo_post_frameDA D ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md (BS ++ LB) (LM ++ fr_ivs A4L FRS) lo rv m' ms' md' ->
lh_globA m' -> jroot_repA r m' BS p -> dc_resA r BS LB LM FRS D w B m' md' rv A' B' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz DCR_A) fc None m (seg_rom asegs)).
End MDcDefs.

Section MDcBase.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Notation wz := (Z_to_bv 64).
Notation jroot_repA := (jroot_rep A4H A4F).
Notation presxD := (QYIF.heap_presxD A4H).
Hypothesis SHALLOW : shallow_A_stmt HIx.
Hypothesis PUT : put_stmt_A HIx.

Lemma fk1_HEAPA : forall A LBall LM FRS B m md Fr lo SP mX,
HEAPAx A LBall LM ((Fr, 1) :: FRS) B m md -> alloc_ceiling <= lo -> SP <= hiA_top A4L HIx ->
munch [(lo, SP); (Fr, Fr + 120); (Fr / 8 + 2147450880, Fr / 8 + 2147450880 + 16); (6444156, 6444160)] m mX ->
wmono asegs m mX -> mem_inv asegs mX -> HEAPAx A LBall LM ((Fr, 1) :: FRS) B mX md.
Proof.
intros A LBall LM FRS B m md Fr lo SP mX HP LO HT MU WM MI.
assert (INF : In (Fr, 1) ((Fr, 1) :: FRS)) by (left; reflexivity).
eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | exact MI].
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP MU).
apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]].
- left. cbn [fst snd]. lia.
- right; right; right. exists Fr, 1. split; [exact INF|]. left. cbn [fst snd]. rewrite fr_size_1. lia.
- right; right; right. exists Fr, 1. split; [exact INF|]. right. unfold shad. cbn [fst snd hl_sb A4L]. rewrite fr_shadow_len_1. unfold A_SB. lia.
- right; right; left. intros x Hx. cbn [fst snd] in Hx. cbn [hl_scratch A4L A4H hla_base]. unfold A_TP. lia.
Qed.

Lemma fk1_pres : forall A LBall LM FRS B m md Fr lo SP mX,
HEAPAx A LBall LM ((Fr, 1) :: FRS) B m md -> alloc_ceiling <= lo -> alloc_ceiling <= SP ->
munch [(lo, SP); (Fr, Fr + 120); (Fr / 8 + 2147450880, Fr / 8 + 2147450880 + 16); (6444156, 6444160)] m mX ->
wmono asegs m mX -> heap_pres A4H (LBall ++ LM ++ fr_ivs A4L FRS) SP m mX.
Proof.
intros A LBall LM FRS B m md Fr lo SP mX HP LO HSP MU WM.
assert (INF : In (Fr, 1) ((Fr, 1) :: FRS)) by (left; reflexivity).
destruct (own_frame_fresh HIx Fr 1 LBall LBall LM FRS B A m md HP (incl_refl _)) as [OFF OFS].
eapply (heap_pres_of_munch A4H _ SP); [exact MU | exact WM |].
eapply (QSHS.client_outsideF HIx A LBall LM ((Fr, 1) :: FRS) B (LBall ++ LM ++ fr_ivs A4L FRS) m md _ SP HP); [| exact HSP |].
- intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. destruct Hb as [H|H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H].
- apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]].
+ left. cbn [fst snd]. lia.
+ right; right; right. exists Fr, 1. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. left. cbn [fst snd]. rewrite fr_size_1. lia.
+ right; right; right. exists Fr, 1. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. right. unfold shad. cbn [fst snd hl_sb A4L]. rewrite fr_shadow_len_1. unfold A_SB. lia.
+ right; right; left. intros x Hx. cbn [fst snd] in Hx. cbn [hl_scratch A4L A4H hla_base]. unfold A_TP. lia.
Qed.

Lemma fk1_HEAPA_W : forall Ax LBall LMx FRx Bx mx md Fr lox SP W mX,
HEAPAx Ax LBall LMx ((Fr, 1) :: FRx) Bx mx md -> alloc_ceiling <= lox -> SP <= hiA_top A4L HIx ->
Forall (fun iv => exists a n, In (a, n) (LBall ++ LMx) /\ a <= fst iv /\ snd iv <= a + n) W ->
munch ([(lox, SP); (Fr, Fr + 120); (Fr / 8 + 2147450880, Fr / 8 + 2147450880 + 16); (6444156, 6444160)] ++ W) mx mX ->
wmono asegs mx mX -> mem_inv asegs mX -> HEAPAx Ax LBall LMx ((Fr, 1) :: FRx) Bx mX md.
Proof.
intros Ax LBall LMx FRx Bx mx md Fr lox SP W mX HP LOx HTx HW MU WM MI.
assert (INF : In (Fr, 1) ((Fr, 1) :: FRx)) by (left; reflexivity).
eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | exact MI].
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP MU).
apply Forall_app. split.
- apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]].
+ left. cbn [fst snd]. lia.
+ right; right; right. exists Fr, 1. split; [exact INF|]. left. cbn [fst snd]. rewrite fr_size_1. lia.
+ right; right; right. exists Fr, 1. split; [exact INF|]. right. unfold shad. cbn [fst snd hl_sb A4L]. rewrite fr_shadow_len_1. unfold A_SB. lia.
+ right; right; left. intros x Hx. cbn [fst snd] in Hx. cbn [hl_scratch A4L A4H hla_base]. unfold A_TP. lia.
- eapply Forall_impl; [| exact HW]. intros iv (a & n & Hin & H1 & H2). right; left. exists a, n. split; [exact Hin | lia].
Qed.

Lemma fk1_pres_W : forall Ax LBall LMx FRx Bx mx md Fr lox SP W L0 mX,
HEAPAx Ax LBall LMx ((Fr, 1) :: FRx) Bx mx md -> alloc_ceiling <= lox -> alloc_ceiling <= SP ->
(forall b, In b L0 -> In b (LBall ++ LMx) \/ In b (fr_ivs A4L FRx)) ->
Forall (fun iv => exists a n, In (a, n) (LBall ++ LMx) /\ ~ In (a, n) L0 /\ a <= fst iv /\ snd iv <= a + n) W ->
munch ([(lox, SP); (Fr, Fr + 120); (Fr / 8 + 2147450880, Fr / 8 + 2147450880 + 16); (6444156, 6444160)] ++ W) mx mX ->
wmono asegs mx mX -> heap_pres A4H L0 SP mx mX.
Proof.
intros Ax LBall LMx FRx Bx mx md Fr lox SP W L0 mX HP LOx HSP HL0 HW MU WM.
assert (INF : In (Fr, 1) ((Fr, 1) :: FRx)) by (left; reflexivity).
destruct (own_frame_fresh HIx Fr 1 LBall LBall LMx FRx Bx Ax mx md HP (incl_refl _)) as [OFF OFS].
assert (OFF' : ~ In (Fr, fr_size 1 - 8) L0).
{ intros H. destruct (HL0 _ H) as [H1 | H1]; apply OFF; [apply in_or_app; left | apply in_or_app; right; apply in_or_app; right].
- apply in_app_or in H1 as [H1|H1]; [exact H1 | exfalso; apply OFF; apply in_or_app; right; apply in_or_app; left; exact H1].
- exact H1. }
assert (OFS' : ~ In (shad A4L Fr, fr_shadow_len 1) L0).
{ intros H. destruct (HL0 _ H) as [H1 | H1]; apply OFS; [rewrite app_assoc; apply in_or_app; left; exact H1 | apply in_or_app; right; apply in_or_app; right; exact H1]. }
eapply (heap_pres_of_munch A4H _ SP); [exact MU | exact WM |].
eapply (QSHS.client_outsideF HIx Ax LBall LMx ((Fr, 1) :: FRx) Bx L0 mx md _ SP HP); [| exact HSP |].
- intros b Hb. destruct (HL0 _ Hb) as [H|H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H].
- apply Forall_app. split.
+ apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]].
* left. cbn [fst snd]. lia.
* right; right; right. exists Fr, 1. split; [exact INF|]. split; [exact OFF'|]. split; [exact OFS'|]. left. cbn [fst snd]. rewrite fr_size_1. lia.
* right; right; right. exists Fr, 1. split; [exact INF|]. split; [exact OFF'|]. split; [exact OFS'|]. right. unfold shad. cbn [fst snd hl_sb A4L]. rewrite fr_shadow_len_1. unfold A_SB. lia.
* right; right; left. intros x Hx. cbn [fst snd] in Hx. cbn [hl_scratch A4L A4H hla_base]. unfold A_TP. lia.
+ eapply Forall_impl; [| exact HW]. intros iv (a & n & Hin & Hni & H1 & H2). right; left. exists a, n. split; [exact Hin|]. split; [exact Hni | lia].
Qed.

Lemma dc_blk_notfr : forall Ax LBx LMx FRx Bx mx mdx a n,
HEAPAx Ax LBx LMx FRx Bx mx mdx -> In (a, n) (LBx ++ LMx) -> 0 < n -> ~ In (a, n) (fr_ivs A4L FRx).
Proof.
intros Ax LBx LMx FRx Bx mx mdx a n HP Hin Hn Hf. destruct (QSHS.in_fr_ivs _ _ Hf) as (F0 & k & HF & [E | E]).
- injection E as E1 E2. subst a. pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP HF Hin) as DF.
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP HF) as (Hk & _). pose proof (fr_size_pos k ltac:(lia)). lia.
- injection E as E1 E2. subst a.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP Hin) as APP. cbn [hl_sb A4L] in APP. unfold A_SB in APP.
change ((2 ^ 47 - 1) / 8 + 2147450880 + 1) with 17594333495296 in APP.
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP HF) as (Hk & _ & HF0 & HFc & _). pose proof (fr_size_pos k ltac:(lia)) as FSP.
pose proof alloc_ceiling_range as ACR. unfold shad in APP. cbn [hl_sb A4L] in APP. unfold A_SB in APP.
clear - APP HF0 HFc FSP ACR Hn. Z.div_mod_to_equations. lia.
Qed.
Lemma fresA_agree : forall m m' CBS BSx q, fresA m CBS q -> agree_on asegs BSx m m' -> incl CBS BSx -> fresA m' CBS q.
Proof.
intros m m' CBS BSx q [H | (Hq & s & J)] AG INCL; [left; exact H | right]. split; [exact Hq|]. exists s.
eapply (jval_agree asegs A4F); [exact J | exact AG | exact INCL].
Qed.

Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB BS LM : list blk) (FRS : list frame) (B0 : bud) (lo p D w : Z) (r : jroot) (T : TSet).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp - dc_stkA (rdepth r).
Hypothesis SPA : bv_unsigned sp mod 32 = 0.
Hypothesis HT : bv_unsigned sp <= hiA_top A4L HIx.
Hypothesis RA : bv_unsigned ra mod 2 = 0.
Hypothesis FRM0 : frm0 fc.
Hypothesis DLOC : arg_locA FRS D 8.
Hypothesis DAL : D mod 8 = 0.
Hypothesis NN : r <> JRnull.
Hypothesis JR0 : jroot_repA r m0 BS p.
Hypothesis Kont : forall ms' md' m' rv (A' : ASA A4L HIx) (B' : bud),
jo_post_frameDA D ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 (BS ++ LB) (LM ++ fr_ivs A4L FRS) lo rv m' ms' md' ->
lh_globA m' -> jroot_repA r m' BS p -> dc_resA HIx r BS LB LM FRS D w B0 m' md' rv A' B' ->
AJ5 A4L HIx A' T md' ms'.

Definition ASP : Z := bv_unsigned sp + -192.

Definition dc_save (m : word -> option byte) : Prop :=
rw_cells asegs m (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition dc_inv (mc : word -> option byte) (mdc : config) : Prop :=
model_vm_only (cfg_model md0) (cfg_model mdc) /\ presxD D ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 mc /\
stk asegs mc lo ASP /\ dc_save mc /\ lh_globA mc.

Definition dc_resX (LBx : list blk) (BX : bud) (mX : word -> option byte) (rv : Z) : Prop :=
bD B0 - w <= bD BX /\
( (rv = 0 /\ exists (d : jroot) (q : Z) (CBS REM : list blk),
LBx = BS ++ CBS ++ REM ++ LB /\ copy_of r d /\ dc_cwA d CBS w /\ q <> 0 /\ rw_cells asegs mX D [C8 (wz q)] /\ jroot_repA d mX CBS q /\
bB B0 - DC_KB * w + 512 * Z.of_nat (length CBS) <= bB BX)
\/ (rv = 2^64 - 1 /\ exists (q : Z) (CBS REM : list blk),
LBx = BS ++ CBS ++ REM ++ LB /\ rw_cells asegs mX D [C8 (wz q)] /\ fresA mX CBS q /\
bB B0 - DC_KB * w + 512 * Z.of_nat (length CBS) <= bB BX) ).

Definition dc_dst (mc : word -> option byte) (q : Z) : Prop :=
rw_cells asegs mc D [C8 (wz q)] /\ ro_cells asegs mc (D / 8 + 2147450880) [C1 (Z_to_bv 8 0)].

Lemma dc_dfacts : forall A LBx B mx mdx Fr, HEAPAx A LBx LM ((Fr, 1) :: FRS) B mx mdx ->
6582272 <= D /\ D + 16 <= alloc_ceiling /\ (D + 24 <= 2147450880 \/ 17594333495296 <= D) /\ (Fr + 128 <= D \/ D + 16 <= Fr) /\
(forall a k, In (a, k) (LBx ++ LM) -> D + 16 <= a \/ a + k <= D) /\ Fr mod 128 = 0 /\ 0 < Fr /\ Fr + 128 <= alloc_ceiling /\
(Fr + 136 <= 2147450880 \/ 17594333495296 <= Fr) /\
2147450880 <= D / 8 + 2147450880 < 17594333495296 /\ (D / 8 + 2147450880 + 1 <= Fr / 8 + 2147450880 \/ Fr / 8 + 2147450880 + 16 <= D / 8 + 2147450880) /\
2147450880 <= Fr / 8 + 2147450880 /\ Fr / 8 + 2147450880 + 16 <= 17594333495296.
Proof.
intros A LBx B mx mdx Fr HP. destruct DLOC as (Fd & kd & HFd & H1 & H2).
assert (INF : In (Fr, 1) ((Fr, 1) :: FRS)) by (left; reflexivity).
assert (IND : In (Fd, kd) ((Fr, 1) :: FRS)) by (right; exact HFd).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP IND) as (Hkd & HFdal & HFd0 & HFdc & _).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & HFal & HF0 & HFc & _). rewrite fr_size_1 in HFc.
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as HFapp. rewrite fr_size_1 in HFapp. cbn [hl_sb A4L] in HFapp. unfold A_SB in HFapp.
change ((2 ^ 47 - 1) / 8 + 2147450880 + 1) with 17594333495296 in HFapp. pose proof alloc_ceiling_range as ACR.
pose proof (heapA_frame_above A4L HIx _ _ _ _ _ _ _ _ _ HP IND) as HFi. cbn [hl_img_hi hla_base A4L A4H] in HFi.
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP IND) as HFa. cbn [hl_sb A4L] in HFa. unfold A_SB in HFa.
change ((2 ^ 47 - 1) / 8 + 2147450880 + 1) with 17594333495296 in HFa.
assert (FNE : Fr <> Fd).
{ intros ->. pose proof (proj1 (stdpp.base.NoDup_ListNoDup _) (heapA_frame_nodup A4L HIx _ _ _ _ _ _ _ HP)) as ND. cbn in ND.
apply List.NoDup_cons_iff in ND as [Hni _]. apply Hni. exact (in_map fr_base _ _ HFd). }
pose proof (heapA_frame_apart A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF IND FNE) as FAP. rewrite fr_size_1 in FAP, HFal.
pose proof (fr_size_pos kd ltac:(lia)) as FSP.
assert (DX : 6582272 <= D /\ D + 16 <= alloc_ceiling /\ (Fr + 128 <= D \/ D + 16 <= Fr)) by lia. destruct DX as (DX1 & DX2 & DX3).
split; [exact DX1|]. split; [exact DX2|]. split; [lia|]. split; [exact DX3|].
split; [intros a k Hin; pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ a k HP IND Hin); lia |].
split; [exact HFal|]. split; [exact HF0|]. split; [exact HFc|]. split; [lia|].
split; [clear - DX1 DX2 ACR; Z.div_mod_to_equations; lia |].
split; [clear - DX3 HFal HF0 DX1; Z.div_mod_to_equations; lia |].
clear - HF0 HFc ACR. Z.div_mod_to_equations. lia.
Qed.

Lemma dc_dst_munch : forall A LBx B mx mdx Fr mc m' q,
HEAPAx A LBx LM ((Fr, 1) :: FRS) B mx mdx -> dc_dst mc q ->
munch [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (Fr / 8 + 2147450880, Fr / 8 + 2147450880 + 16); (6444156, 6444160)] mc m' -> wmono asegs mc m' ->
dc_dst m' q.
Proof.
intros A LBx B mx mdx Fr mc m' q HP [DC DSH] MU WM.
destruct (dc_dfacts _ _ _ _ _ _ HP) as (D1 & D2 & D3 & D4 & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13). pose proof alloc_ceiling_range as ACR.
set (sh := Fr / 8 + 2147450880) in *. set (dsh := D / 8 + 2147450880) in *.
split.
- eapply (rw_cells_transport asegs); [exact DC | exact MU | exact WM |]. cbn [disjoint_from cells_size csize Nat.add]. clear - D1 D2 D3 D4 D8 D9 D12 D13 LO ACR. lia.
- eapply (ro_cells_transport asegs); [exact DSH | exact MU |]. cbn [disjoint_from cells_size csize Nat.add]. clear - D8 D9 D10 D11 LO ACR. lia.
Qed.

Lemma dc_dsh_range : forall A LBx B mx mdx Fr X L0 SP,
HEAPAx A LBx LM ((Fr, 1) :: FRS) B mx mdx ->
client_rangex A4H X (L0 ++ LM ++ fr_ivs A4L ((Fr, 1) :: FRS)) SP (D / 8 + 2147450880) 1.
Proof.
intros A LBx B mx mdx Fr X L0 SP HP. destruct DLOC as (Fd & kd & HFd & H1 & H2).
assert (IND : In (Fd, kd) ((Fr, 1) :: FRS)) by (right; exact HFd).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP IND) as (Hkd & HFdal & HFd0 & HFdc & _).
eapply client_rangex_block; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_shadow; exact IND | |].
- unfold shad. cbn [hl_sb A4L]. unfold A_SB. clear - H1. Z.div_mod_to_equations. lia.
- unfold shad. cbn [hl_sb A4L]. unfold A_SB, fr_shadow_len.
assert (HF8 : Fd mod 64 = 0).
{ apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ (fr_size kd)); [| apply Z.mod_divide; [pose proof (fr_size_pos kd ltac:(lia)); lia | exact HFdal]].
exists (2 ^ kd). unfold fr_size. lia. }
unfold fr_size in H2. clear - H1 H2 HF8 Hkd. assert (K : kd = 0 \/ kd = 1 \/ kd = 2 \/ kd = 3) by lia. destruct K as [-> | [-> | [-> | ->]]]; cbn in *; Z.div_mod_to_equations; lia.
Qed.

Lemma dc_dst_presx : forall A LBx B mx mdx Fr X L0 SP mc m' q,
HEAPAx A LBx LM ((Fr, 1) :: FRS) B mx mdx -> dc_dst mc q ->
heap_presx A4H X (L0 ++ LM ++ fr_ivs A4L ((Fr, 1) :: FRS)) SP mc m' -> dc_dst m' q.
Proof.
intros A LBx B mx mdx Fr X L0 SP mc m' q HP [DC DSH] HPR. destruct DLOC as (Fd & kd & HFd & H1 & H2).
assert (IND : In (Fd, kd) ((Fr, 1) :: FRS)) by (right; exact HFd).
split.
- eapply (heap_presx_rw_cells A4H); [exact HPR | exact DC |].
eapply client_rangex_block; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact IND | cbn; lia | cbn; lia].
- destruct DSH as [Hwf Hb]. split; [exact Hwf|].
eapply (heap_presx_bytes_at A4H); [exact HPR | exact Hb |]. cbn [cells_bytes cbytes app length]. exact (dc_dsh_range _ _ _ _ _ _ _ _ _ HP).
Qed.

Lemma dc_dsh_presxD : forall A LBx B mx mdx Fr L0 SP mc m',
HEAPAx A LBx LM ((Fr, 1) :: FRS) B mx mdx -> ro_cells asegs mc (D / 8 + 2147450880) [C1 (Z_to_bv 8 0)] ->
presxD D (L0 ++ LM ++ fr_ivs A4L ((Fr, 1) :: FRS)) SP mc m' -> ro_cells asegs m' (D / 8 + 2147450880) [C1 (Z_to_bv 8 0)].
Proof.
intros A LBx B mx mdx Fr L0 SP mc m' HP [Hwf Hb] PX. split; [exact Hwf|].
destruct (dc_dfacts _ _ _ _ _ _ HP) as (D1 & D2 & D3 & _ & _ & _ & _ & _ & _ & D10 & _).
eapply (QrIB.Mq0.presxD_bytes_at A4H); [exact PX | exact Hb | cbn [cells_bytes cbytes app length]; exact (dc_dsh_range _ _ _ _ _ _ _ _ _ HP) |].
cbn [cells_bytes cbytes app length]. clear - D1 D2 D3 D10. lia.
Qed.

Lemma dc_dst_pres : forall A LBx B mx mdx Fr L0 SP mc m' q,
HEAPAx A LBx LM ((Fr, 1) :: FRS) B mx mdx -> dc_dst mc q ->
heap_pres A4H (L0 ++ LM ++ fr_ivs A4L ((Fr, 1) :: FRS)) SP mc m' -> dc_dst m' q.
Proof. intros A LBx B mx mdx Fr L0 SP mc m' q HP DD HPR. eapply (dc_dst_presx _ _ _ _ _ _ (fun _ => False)); [exact HP | exact DD | apply heap_pres_presx; exact HPR]. Qed.

Lemma dc_blkW_disj : forall Ax LBx Bx mx mdx Fr W A0 n0,
HEAPAx Ax LBx LM ((Fr, 1) :: FRS) Bx mx mdx ->
Forall (fun iv => exists a n, In (a, n) (LBx ++ LM) /\ a <= fst iv /\ snd iv <= a + n) W ->
(alloc_ceiling <= A0 \/ (Fr <= A0 /\ A0 + n0 <= Fr + 128) \/ (2147450880 <= A0 /\ A0 + n0 <= 17594333495296)
\/ (D <= A0 /\ A0 + n0 <= D + 8)) ->
disjoint_from W A0 n0.
Proof.
intros Ax LBx Bx mx mdx Fr W A0 n0 HP HW KIND.
assert (INF : In (Fr, 1) ((Fr, 1) :: FRS)) by (left; reflexivity).
destruct (dc_dfacts _ _ _ _ _ _ HP) as (_ & _ & _ & _ & DBLK & _).
induction W as [|[wl wh] W IH]; cbn [disjoint_from]; [exact I|].
apply Forall_cons_iff in HW as [(a & n & Hin & H1 & H2) HW]. cbn [fst snd] in H1, H2. split; [| exact (IH HW)].
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a n HP Hin) as (_ & _ & Ha0 & Hac & _).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF Hin) as DF. rewrite fr_size_1 in DF.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ a n HP Hin) as APP. cbn [hl_sb A4L] in APP. unfold A_SB in APP.
change ((2 ^ 47 - 1) / 8 + 2147450880 + 1) with 17594333495296 in APP.
pose proof (DBLK a n Hin) as DB.
clear - KIND H1 H2 Ha0 Hac DF APP DB. lia.
Qed.

Lemma dc_dst_blkW : forall Ax LBx Bx mx mdx Fr W mc m' q,
HEAPAx Ax LBx LM ((Fr, 1) :: FRS) Bx mx mdx ->
Forall (fun iv => exists a n, In (a, n) (LBx ++ LM) /\ a <= fst iv /\ snd iv <= a + n) W ->
munch W mc m' -> wmono asegs mc m' -> dc_dst mc q -> dc_dst m' q.
Proof.
intros Ax LBx Bx mx mdx Fr W mc m' q HP HW MU WM [DC DSH].
destruct (dc_dfacts _ _ _ _ _ _ HP) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & D10 & _).
split.
- eapply (rw_cells_transport asegs); [exact DC | exact MU | exact WM |]. cbn [cells_size csize Nat.add].
eapply (dc_blkW_disj _ _ _ _ _ _ _ _ _ HP HW). right; right; right. lia.
- eapply (ro_cells_transport asegs); [exact DSH | exact MU |]. cbn [cells_size csize Nat.add].
eapply (dc_blkW_disj _ _ _ _ _ _ _ _ _ HP HW). right; right; left. lia.
Qed.

Lemma dc_epi :
forall (x1 xsp t0 t1 t2 xs1 a1 a2 a3 a4 a5 a6 a7 x19 x20 x22 x23 x24 x25 x26 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(mX : word -> option byte) (mdX : config) (AX : ASA A4L HIx) (BX : bud) (LBx : list blk) (Fr rv : Z)
(cs : list cell) (w0 : word) (frest : list cell) (x0 x1' x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : byte),
dc_inv mX mdX -> fsaved F F1 -> frm0 fc1 ->
HEAPAx AX LBx LM ((Fr, 1) :: FRS) BX mX mdX ->
rw_cells asegs mX ASP cs -> Z.of_nat (cells_size cs) = 88 ->
rw_cells asegs mX Fr (C8 w0 :: frest) -> Z.of_nat (cells_size frest) = 112 ->
rw_cells asegs mX (Fr / 8 + 2147450880) [C1 x0; C1 x1'; C1 x2; C1 x3; C1 x4; C1 x5; C1 x6; C1 x7; C1 x8; C1 x9; C1 x10; C1 x11; C1 x12; C1 x13; C1 x14; C1 x15] ->
jroot_repA r mX BS p ->
dc_resX LBx BX mX rv ->
AJ5 A4L HIx AX T mdX
(MS (mkR x1 xsp gp (wz A_TP) t0 t1 t2 sp xs1 (wz rv) a1 a2 a3 a4 a5 a6 a7
(wz Fr) x19 x20 (wz Fr) x22 x23 x24 x25 x26 (wz (Fr / 8 + 2147450880)) t3 t4 t5 t6)
F1 (wz 0xa1ac4) fc1 None mX (seg_rom asegs)).
Proof.
intros until x15. intros (VMX & PRESX & STX & SAVE & GX) FS FRM1 HPX SCR SCRsz FFX FFsz FSHX JRX RES.
unfold dc_save in SAVE. unfold ASP in *. pose proof LOS as LOSu. unfold dc_stkA, DC_F, DC_C in LOSu.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (INF : In (Fr, 1) ((Fr, 1) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HPX INF) as (_ & HFal & HF0 & HFc & HFimg & _ & _ & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HPX INF) as HFapp.
rewrite fr_size_1 in HFal, HFc, HFimg, HFapp. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFimg, HFapp. unfold A_SB in HFapp.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 16 <= 17594333495296) by (unfold sh; clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HPX) as MI. change (hl_segs A4L) with asegs in MI.
pose proof (wmono_refl asegs mX) as WM. pose proof (munch_refl [(lo, bv_unsigned sp + -192); (Fr, Fr + 120); (sh, sh + 16); (6444156, 6444160)] mX) as MU.
stash RES. stash JRX. stash GX. stash PRESX.
unfold A_TP. a4l. reenterA asegs A4L HIx asegs_wx HPX.
step. step. stepz. step. if_falsex. step. do 16 stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ mX mc, WMc : wmono asegs mX mc, MIc : mem_inv asegs mc |- _ =>
pose proof (fk1_HEAPA _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -192) _ HPX LO ltac:(lia) MUc WMc MIc) as HPY;
pose proof (fk1_pres _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -192) _ HPX LO ltac:(lia) MUc WMc) as HPRXY end end.
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HPY INF) as (_ & _ & _ & _ & _ & _ & _ & (fp & FPB & FPR & FPnc & FPimg & FPns & FPfr)).
rewrite fr_size_1 in FPB. replace (Fr + 128 - 8) with (Fr + 120) in FPB by lia.
pose proof (ro_C8_of_bytes_at asegs _ _ _ FPB) as FPC.
step.
evt_done5.
eapply (hiA_frame_release A4L HIx) with (Fr := Fr) (k := 1) (fp := fp) (rX := Z_to_bv 5 11);
[exact HPY | exact INF | rewrite fr_size_1; replace (Fr + 128 - 8) with (Fr + 120) by lia; exact FPB | lia | reflexivity | vm_compute; discriminate | | ].
1: vm_compute; split; reflexivity.
intros m5 md5 A5 VM5 HP5 Hoff Hwv.
cbn [fr_remove fr_base fst Z.eqb] in HP5. rewrite Z.eqb_refl in HP5.

lazymatch type of HPY with HEAPA _ _ _ _ _ _ _ ?mq _ => assert (MUr : munch [(fp, fp + 1)] mq m5) end.
{ intros x Hx. cbn [outside] in Hx. pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR. cbn in XR.
rewrite <- (Z_to_bv_bv_unsigned x). change (Z_to_bv 64 (bv_unsigned x)) with (wa (bv_unsigned x)). apply Hoff; lia. }
lazymatch type of HPY with HEAPA _ _ _ _ _ _ _ ?mq _ => assert (WMr : wmono asegs mq m5) by exact Hwv end.
assert (FPlow : fp < alloc_ceiling) by (destruct (Z.lt_ge_cases fp alloc_ceiling) as [L|G]; [exact L | exfalso; apply FPnc; left; exact G]).
apply (rw_cells_transport asegs [(fp, fp + 1)] _ m5) in SAVE; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] _ m5) in SCR; [| exact MUr | exact WMr | cbn [disjoint_from]; lia].
apply (stk_transport_disjoint asegs [(fp, fp + 1)] _ m5) in STX; [| exact MUr | exact WMr | cbn [disjoint_from]; lia].
eapply stk_release in SCR; [| exact STX | lia]. rewrite SCRsz in SCR.
replace (bv_unsigned sp + -192 + 88) with (bv_unsigned sp + -104) in SCR by lia.
clear FPC.
change (662300 + 4) with 662304.
reenterA asegs A4L HIx asegs_wx HP5.
do 17 step.
rename SCR into ST5. release_frame SAVE ST5 (bv_unsigned sp).
evt_done5. unstash RES. unstash JRX. unstash GX. unstash PRESX.

assert (HPRX5 : heap_pres A4H (LBx ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) mX m5).
{ eapply heap_pres_trans; [eapply heap_pres_weaken; [exact HPRXY | lia | intros b Hb; exact Hb] |].
eapply (heap_pres_of_presD (Fr + 32)).
+ eapply (presD_fp HIx _ _ _ _ _ _ _ _ (Fr + 32) _ (bv_unsigned sp) fp HPY); [| lia | exact FPnc | exact FPfr | exact Hoff | exact Hwv].
intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. destruct Hb as [H|H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H].
+ intros a Hd Hc.
destruct (own_frame_fresh HIx Fr 1 LBx LBx LM FRS BX AX _ mdX HPY (incl_refl _)) as [OFF OFS].
assert (Ho : outside [(Fr + 32, Fr + 40)] a).
{ eapply (QSHS.client_outsideF HIx AX LBx LM ((Fr, 1) :: FRS) BX (LBx ++ LM ++ fr_ivs A4L FRS) _ mdX [(Fr + 32, Fr + 40)] (bv_unsigned sp) HPY); [| lia | | lia | exact Hc].
- intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. destruct Hb as [H|H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H].
- apply Forall_cons; [| apply Forall_nil]. right; right; right. exists Fr, 1. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. left. cbn [fst snd]. rewrite fr_size_1. lia. }
cbn [outside] in Ho. lia. }
assert (ELB : exists CBS REM, LBx = BS ++ CBS ++ REM ++ LB).
{ destruct RES as (_ & [(_ & d & q & CBS & REM & E & _) | (_ & q & CBS & REM & E & _)]); exists CBS, REM; exact E. }
destruct ELB as (CBS0 & REM0 & ELB).
assert (INCL : forall b, In b ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) -> In b (LBx ++ LM ++ fr_ivs A4L FRS)).
{ intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb as [Hb|Hb]; [| apply in_or_app; right; apply in_or_app; right; exact Hb].
apply in_app_or in Hb as [Hb|Hb]; [| apply in_or_app; right; apply in_or_app; left; exact Hb].
apply in_or_app; left. rewrite ELB. apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb]. }
assert (AGX : forall BSx, incl BSx LBx -> agree_on asegs BSx mX m5).
{ intros BSx Hi. eapply (agree_of_heap_pres asegs A4H); [exact HPRX5 | reflexivity | intros b Hb; apply in_or_app; left; apply Hi; exact Hb]. }
eapply (Kont _ md5 m5 rv A5 BX).
- unfold jo_post_frameDA.
split; [apply ret_statew_intro; [exact FS | intros _; exact FRM1] |].
split; [eapply model_vm_only_trans; [exact VMX | exact VM5] |].
split; [exact ST5|].
split; [| exact (heapA_errno A4L HIx _ _ _ _ _ _ _ HP5)].
eapply (QrIB.Mq0.presxD_trans A4H); [exact PRESX|]. apply (QrIB.Mq0.pres_presxD A4H).
eapply heap_pres_weaken; [exact HPRX5 | lia | exact INCL].
- eapply lh_globA_client; [exact HPRX5 | exact GX].
- eapply (QrIB.Mq0.jroot_rep_agree A4H A4F); [exact JRX | apply (AGX BS); rewrite ELB; apply incl_appl; apply incl_refl | apply incl_refl].
- destruct RES as (BDX & RES). split; [exact BDX|].
destruct DLOC as (Fd & kd & HFd & HD1 & HD2).
assert (DCX : forall v, rw_cells asegs mX D [C8 v] -> rw_cells asegs m5 D [C8 v]).
{ intros v H. eapply (heap_pres_rw_cells A4H); [exact HPRX5 | exact H |].
eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact HFd | cbn; lia | cbn; lia]. }
destruct RES as [(Hrv & d & q & CBS & REM & E & CO & CW & Hq & DC & JD & BBX) | (Hrv & q & CBS & REM & E & DC & FRES & BBX)].
+ left. split; [exact Hrv|]. exists d, q, CBS, REM. split; [exact CO|]. split; [exact CW|]. split; [exact Hq|]. split; [exact (DCX _ DC)|].
split; [eapply (QrIB.Mq0.jroot_rep_agree A4H A4F); [exact JD | apply (AGX CBS); rewrite E; apply incl_appr; apply incl_appl; apply incl_refl | apply incl_refl] |].
split; [exact BBX|]. rewrite <- E. exact HP5.
+ right. split; [exact Hrv|]. exists q, CBS, REM. split; [exact (DCX _ DC)|].
split; [eapply fresA_agree; [exact FRES | apply (AGX CBS); rewrite E; apply incl_appr; apply incl_appl; apply incl_refl | apply incl_refl] |].
split; [exact BBX|]. rewrite <- E. exact HP5.
Qed.

Lemma dc_pro :
forall (t0 t1 t2 a1 a2 a3 a6 a7 t3 t4 t5 t6 : word) (A : ASA A4L HIx) (n : Z),
HEAPAx A (BS ++ LB) LM FRS B0 m0 md0 -> stk asegs m0 lo (bv_unsigned sp) -> lh_globA m0 ->
rw_cells asegs m0 D [C8 (wz 0)] -> unpoisoned asegs m0 A_SB D 8 ->
Z.of_nat (length FRS) < 4096 ->
sh_lenA r m0 p n -> sh_needB r n <= bB B0 -> 2 <= bD B0 ->
DC_KB * w <= bB B0 -> w <= bD B0 -> sh_needB r n <= DC_KB * w -> 2 <= w ->
(forall (Fr q : Z) (CBS : list blk) (m3 : word -> option byte) (md3 : config) (A3 : ASA A4L HIx) (B3 : bud) (j48 j16 jf : list byte) (F3 : bvmap 5 word) (fc3 : bv 32)
(x1 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x21 t3' t4' t5' t6' : word),
dc_inv m3 md3 -> fsaved F F3 -> frm0 fc3 ->
HEAPAx A3 (BS ++ CBS ++ LB) LM ((Fr, 1) :: FRS) B3 m3 md3 ->
rw_cells asegs m3 ASP [C8 (wz 0); CB 48 j48; C8 (wz SH_A); CB 16 j16; C8 (wz Fr)] ->
rw_cells asegs m3 Fr [C8 (wz 1102416563); C8 (wz 108820); C8 (wz 660968); CB 96 jf] ->
rw_cells asegs m3 (Fr / 8 + 2147450880) [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
jroot_repA r m3 BS p ->
q <> 0 -> dc_dst m3 q -> QrIB.Mq0.scopy A4H A4F r m3 CBS q -> sh_shapeA r n CBS ->
bB B0 - sh_okB r n <= bB B3 -> bD B0 - 1 <= bD B3 ->
AJ5 A4L HIx A3 T md3
(MS (mkR x1 (wz ASP) gp (wz A_TP) t0' t1' t2' sp (wz ASP) (wz 1) a1' a2' a3' a4' a5' a6' a7'
(wz Fr) (wz Fr) (wz D) x21 (wz 2147450880) (wz p) s8 s9 s10 (wz (Fr / 8 + 2147450880)) t3' t4' t5' t6')
F3 (wz 0xa1734) fc3 None m3 (seg_rom asegs))) ->
AJ5 A4L HIx A T md0
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz p) a1 a2 a3 (wz D) (wz SH_A) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz DCR_A) fc None m0 (seg_rom asegs)).
Proof.
intros until n. intros HP ST G0 DC0 DU0 FRN LEN0 SHB SHD BBW BDW SHW W2 KOK.
pose proof LOS as LOSu. unfold dc_stkA, DC_F, DC_C in LOSu.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
unfold DCR_A. unfold ASP in *.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof alloc_ceiling_range as ACR.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HP) as (SB1 & SB2 & SB3 & SB4).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2. apply ro_C8_of_bytes_at in SB3.
assert (UARC : ro_cells asegs m0 (hl_uar_cell A4L) [C4 (Z_to_bv 64 1)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SB4]).
clear SB4. a4l.
pose proof (wmono_refl asegs m0) as WM. pose proof (munch_refl [(bv_unsigned sp - 192, bv_unsigned sp)] m0) as MU.
unfold A_TP in *.
stash G0. stash DC0. stash DU0. stash LEN0. stash KOK.
reenterA asegs A4L HIx asegs_wx HP.
carve_frame 192%nat ST.
step. stepz. do 13 step.
step. step.
rewrite (unsigned_lit (bv_unsigned sp + -192)) by lia. change 18446744073709551584 with (2^64 - 2^5). rewrite OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.land_align_down by lia. change (2^5) with 32.
replace ((bv_unsigned sp + -192) mod 32) with 0 by (clear - SPA; Z.div_mod_to_equations; lia). rewrite Z.sub_0_r.
step.
step. step.
do 6 step. step.
norm_sx32. step. if_false.
step. step. step. step. step.
evt_done5.
eapply (stack_malloc_full HIx) with (k := 1) (bytes := 96) (lo := lo) (LB := BS ++ LB) (LM := LM) (FR := FRS) (B := B0);
[ heap_nowA A4L HIx HP MU WM MI | lia | .. ].
all: rewrite ?unsigned_lit by lia.
1: rewrite fr_size_1; lia.
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

assert (INF : In (Fr, 1) ((Fr, 1) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as (_ & HFal & HF0 & HFc & HFimg & _ & HFshw & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as HFapp.
rewrite fr_size_1 in HFal, HFc, HFimg, HFapp. rewrite fr_shadow_len_1 in HFshw. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFimg, HFapp.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in FR; [| left; cbn; lia].
change (hl_segs A4H) with asegs in FR.
clear SB1 SB2 SB3 UARC.
assert (FSH1 : rw_cells asegs m1' (shad A4L Fr) [CB 16 (repeat (Z_to_bv 8 0) 16)]).
{ split; [split; [cbn; split; [reflexivity | exact I] | cbn [cells_bytes cbytes app]; rewrite app_nil_r; rewrite fr_shadow_len_1 in SHB1; exact SHB1] | exact HFshw]. }
rewrite fr_size_1 in FF1. change (Z.to_nat (128 - 8)) with 120%nat in FF1.
unfold shad in FSH1. a4l.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 16 <= 17594333495296) by (unfold sh; clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI1. change (hl_segs A4L) with asegs in MI1. clear MI.
assert (HPR01 : heap_pres A4H ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m1').
{ eapply heap_pres_trans.
- eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; exact Hb | clia |].
apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil].
- eapply heap_pres_weaken; [exact HPR1 | lia | intros b Hb; exact Hb]. }
clear MU WM. pose proof (wmono_refl asegs m1') as WM. pose proof (munch_refl [(lo, bv_unsigned sp); (Fr, Fr + 120); (sh, sh + 16); (6444156, 6444160)] m1') as MU.
unfold A_SB in HFapp.
reenterA asegs A4L HIx asegs_wx HP1.
step. step. step. step. step. step. if_truex.
step.
step. step. step. step.
rewrite (unsigned_lit Fr) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
step. step. step. step. stepz. stepz. stepz. step. step.
fold sh.
stepz. stepz. stepz. stepz. step. stepz. stepz. stepz. stepz. step. stepz. stepz. stepz. stepz.
step. step. step. unfold SH_A. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m1' mc, WMc : wmono asegs m1' mc, MIc : mem_inv asegs mc |- _ =>
pose proof (fk1_HEAPA _ _ _ _ _ _ _ _ lo (bv_unsigned sp) _ HP1 LO HT MUc WMc MIc) as HP2;
pose proof (fk1_pres _ _ _ _ _ _ _ _ lo (bv_unsigned sp) _ HP1 LO ltac:(lia) MUc WMc) as HPR12 end end.
lazymatch type of HP2 with HEAPA _ _ _ _ _ _ _ ?mc _ =>
assert (HPR02 : heap_pres A4H ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 mc) by (eapply heap_pres_trans; [exact HPR01 | exact HPR12]) end.
unstash G0. unstash DC0. unstash DU0. unstash LEN0. unstash KOK.
pose proof (agree_of_heap_pres asegs A4H _ _ (BS ++ LB) _ _ HPR02 eq_refl ltac:(intros b Hb; apply in_or_app; left; exact Hb)) as AG02.
pose proof (QrIB.Mq0.jroot_rep_agree A4H A4F _ _ _ _ _ _ JR0 AG02 ltac:(apply incl_appl; apply incl_refl)) as JR2.
pose proof (lh_globA_client _ _ _ _ HPR02 G0) as G2.
destruct DLOC as (Fd & kd & HFd & HD1 & HD2).
lazymatch type of HP2 with HEAPA _ _ _ _ _ _ _ ?mc _ =>
assert (DC2 : rw_cells asegs mc D [C8 (wz 0)]);
[ eapply (heap_pres_rw_cells A4H); [exact HPR02 | exact DC0 |];
eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact HFd | cbn; lia | cbn; lia] |];
assert (DU2 : unpoisoned asegs mc A_SB D 8) by (eapply (QsKa.Mqf.unpoisoned_pres_frame HIx); [exact HP | exact HFd | exact HD1 | exact HD2 | exact DU0 | exact HPR02]);
assert (LEN2 : sh_lenA r mc p n)
end.
{ destruct (QrIB.Mq0.jroot_rep_root_in A4H A4F r m0 BS p JR0 NN) as (np & INp & Hnp).
assert (X : forall len0 : Z, bytes_at asegs m0 (p + 40) (le8 (wz len0)) -> bytes_at asegs m2 (p + 40) (le8 (wz len0))).
{ intros len0 Hb. eapply (bytes_at_agree asegs); [exact Hb | exact AG02 |]. exists p, np. split; [apply in_or_app; left; exact INp | rewrite length_le8; lia]. }
unfold sh_lenA, str_lenA in LEN0 |- *. destruct r as [|[|u| |h|kids|kids]|tojs|]; try exact I;
(destruct LEN0 as (len0 & Hb & Hr & Hn); exists len0; split; [exact (X _ Hb) | split; [exact Hr | exact Hn]]). }
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HP2) as (errv2 & ERR2).
evt_done5.
eapply (SHALLOW) with (LB := LB) (BS := BS) (FRS := (Fr, 1) :: FRS) (B := B0) (lo := lo) (p := p) (D := D) (n := n) (dold := wz 0) (r := r) (errv := errv2).
all: rewrite ?unsigned_lit by lia.
1: exact HP2. 1: exact JR2. 1: exact NN. 1: exact G2. 1: exact DC2.
1: exists Fd, kd; split; [right; exact HFd | split; [exact HD1 | exact HD2]].
1: exact DU2. 1: exact DAL. 1: eassumption. 1: exact LO. 1: unfold SH_STK_A; lia.
1: clear - SPA; Z.div_mod_to_equations; lia. 1: lia. 1: exact ERR2. 1: reflexivity. 1: reflexivity.
1: exact LEN2. 1: exact SHB. 1: exact SHD. 1: reflexivity. 1: reflexivity.
intros ms3 md3 m3 rv A3 B3 POST G3 JR3 RES3.
destruct POST as (RS3 & VM3 & ST3 & PXD3 & (errv3 & ERR3)).
destruct RS3 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F3 & fc3 & -> & FS3 & FRM3).
rewrite ?(unsigned_lit (bv_unsigned sp + -192)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -192)) in PXD3 by lia.

pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP1 ltac:(right; exact HFd)) as (Hkd & _ & HFd0 & HFdc & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 ltac:(right; exact HFd)) as HFdapp. cbn [hl_sb A4L] in HFdapp. unfold A_SB in HFdapp.
change ((2 ^ 47 - 1) / 8 + 2147450880 + 1) with 17594333495296 in HFdapp.
assert (FNE : Fr <> Fd).
{ intros ->. pose proof (proj1 (stdpp.base.NoDup_ListNoDup _) (heapA_frame_nodup A4L HIx _ _ _ _ _ _ _ HP1)) as ND. cbn in ND.
apply List.NoDup_cons_iff in ND as [Hni _]. apply Hni. exact (in_map fr_base _ _ HFd). }
pose proof (heapA_frame_apart A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP1 INF ltac:(right; exact HFd) FNE) as FAP. rewrite fr_size_1 in FAP.
pose proof (fr_size_pos kd ltac:(lia)) as FSP.

assert (PXR : forall A0 cs0, rw_cells asegs m2 A0 cs0 ->
client_rangex A4H (hl_volatile A4H) ((BS ++ LB) ++ LM ++ fr_ivs A4L ((Fr, 1) :: FRS)) (bv_unsigned sp + -192) A0 (Z.of_nat (cells_size cs0)) ->
(A0 + Z.of_nat (cells_size cs0) <= D \/ D + 8 <= A0) -> rw_cells asegs m3 A0 cs0).
{ intros A0 cs0 H1 H2 H3. exact (QrIB.Mq0.presxD_rw_cells A4H D _ _ m2 m3 A0 cs0 PXD3 H1 H2 H3). }
apply PXR in FR; [| left; lia | right; cbn [cells_size csize Nat.add]; clia].
apply PXR in FF1.
2: { eapply client_rangex_block; [apply in_or_app; right; apply in_or_app; right; left; reflexivity | cbn [fr_base fst]; lia | cbn [cells_size csize Nat.add fr_base fr_class fst snd]; rewrite fr_size_1; lia]. }
2: { cbn [cells_size csize Nat.add]. lia. }
apply PXR in FSH1.
2: { eapply client_rangex_block; [apply in_or_app; right; apply in_or_app; right; right; left; reflexivity | unfold shad; cbn [fr_base fst hl_sb A4L]; unfold A_SB; fold sh; lia
| unfold shad; cbn [cells_size csize Nat.add fr_base fr_class fst snd hl_sb A4L]; rewrite fr_shadow_len_1; unfold A_SB; fold sh; lia]. }
2: { cbn [cells_size csize Nat.add]. clear - SHR HFdapp HD1 HD2 FSP. lia. }
clear PXR.

assert (PX03 : presxD D ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m3).
{ eapply (QrIB.Mq0.presxD_trans A4H); [apply (QrIB.Mq0.pres_presxD A4H); exact HPR02 |].
eapply (QrIB.Mq0.presxD_weaken A4H); [exact PXD3 | lia |].
intros b Hb. apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb |].
apply in_or_app; right. apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; cbn [fr_ivs flat_map app]; right; right; exact Hb]. }
assert (INV3 : dc_inv m3 md3).
{ split; [eapply model_vm_only_trans; [exact VM1 | exact VM3] |]. split; [exact PX03|]. split; [exact ST3|]. split; [| exact G3].
unfold dc_save. lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) =>
change (c0 :: c1 :: c2 :: c3 :: c4 :: rest) with ([c0; c1; c2; c3; c4] ++ rest) in FR end.
destruct (proj1 (rw_cells_app asegs m3 _ _ _) FR) as [_ SAVE]. cbn [cells_size csize Nat.add] in SAVE.
replace (bv_unsigned sp + -192 + Z.of_nat 88) with (bv_unsigned sp + -104) in SAVE by lia. exact SAVE. }

lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) =>
change (c0 :: c1 :: c2 :: c3 :: c4 :: rest) with ([c0; c1; c2; c3; c4] ++ rest) in FR end.
destruct (proj1 (rw_cells_app asegs m3 _ _ _) FR) as [SCR SAVE]. clear FR. cbn [cells_size csize Nat.add] in SAVE.
replace (bv_unsigned sp + -192 + Z.of_nat 88) with (bv_unsigned sp + -104) in SAVE by lia.
destruct RES3 as [(-> & q & CBS & Hq & DC3 & SC3 & SHP3 & BB3 & BD3 & HP3) | (-> & DC3 & BB3 & BD3 & HP3)].
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI3. change (hl_segs A4L) with asegs in MI3.
pose proof (wmono_refl asegs m3) as WM3. pose proof (munch_refl [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6444156, 6444160)] m3) as MU3.
replace (ret_pc (wz 661296)) with (wz 661296) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
reenterA asegs A4L HIx asegs_wx HP3.
step. if_lit.
evt_done5.
lazymatch type of SCR with rw_cells _ _ _ [_; CB 48 ?j48; _; CB 16 ?j16; _] =>
lazymatch type of FF1 with rw_cells _ _ _ [_; _; _; CB 96 ?jf] =>
eapply (KOK Fr q CBS m3 md3 A3 B3 j48 j16 jf F3 fc3) end end;
[ exact INV3 | exact FS3 | apply FRM3; exact FRM0 | exact HP3 | exact SCR | exact FF1 | | exact JR3 | exact Hq | split; [exact DC3 | exact (dc_dsh_presxD _ _ _ _ _ _ _ _ _ _ HP2 (unpoisoned8_cell asegs _ A_SB D DU2 DAL) PXD3)] | exact SC3 | exact SHP3 | exact BB3 | exact BD3 ].
eapply rw_cells_recast; [exact FSH1 | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity].

-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI3. change (hl_segs A4L) with asegs in MI3.
pose proof (errno_shadowA HIx _ _ _ _ _ _ _ HP3) as ESH. a4l. change ((6444320 - 164) / 8 + 2147450880) with 2148256399 in ESH.
unfold A_ERRNO, A_TP in ERR3. change (6444320 - 164) with 6444156 in ERR3.
pose proof (wmono_refl asegs m3) as WM3. pose proof (munch_refl [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6444156, 6444160)] m3) as MU3.
replace (ret_pc (wz 661296)) with (wz 661296) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
stash KOK. pose proof DC3 as DC3k. stash DC3k.
reenterA asegs A4L HIx asegs_wx HP3.
step. if_lit.
step. step. step. step.
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
step. ub_resolve.
step. step. ub_resolve.
step. step. step. rewrite ?sxb_zero, ?zxb_zero.
step.
step. if_false.
step. stepz. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m3 mc, WMc : wmono asegs m3 mc, MIc : mem_inv asegs mc |- _ =>
pose proof (fk1_HEAPA _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -104) _ HP3 LO ltac:(lia) MUc WMc MIc) as HPY;
pose proof (fk1_pres _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -104) _ HP3 LO ltac:(lia) MUc WMc) as HPR3Y end end.
evt_done5.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
lazymatch type of HPY with HEAPA _ _ _ _ _ _ _ ?mY _ =>
eapply (dc_epi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F3 fc3 mY md3 A3 B3 (BS ++ LB) Fr (2^64 - 1)) end.
+ split; [eapply model_vm_only_trans; [exact VM1 | exact VM3] |].
split; [eapply (QrIB.Mq0.presxD_trans A4H); [exact PX03 |]; apply (QrIB.Mq0.pres_presxD A4H); eapply heap_pres_weaken; [exact HPR3Y | lia | intros b Hb; exact Hb] |].
split; [eassumption|]. split; [unfold dc_save; exact SAVE|].
eapply lh_globA_client; [exact HPR3Y | exact G3].
+ exact FS3.
+ apply FRM3. exact FRM0.
+ exact HPY.
+ exact SCR.
+ reflexivity.
+ exact FF1.
+ reflexivity.
+ eapply rw_cells_recast; [exact FSH1 | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity].
+ eapply (QrIB.Mq0.jroot_rep_agree A4H A4F); [exact JR3 | | apply incl_appl; apply incl_refl].
eapply (agree_of_heap_pres asegs A4H); [exact HPR3Y | reflexivity | intros b Hb; apply in_or_app; left; exact Hb].
+ split; [cbn [bD] in *; lia|]. right. split; [reflexivity|]. exists 0, [], []. split; [reflexivity|].
split; [| split; [left; split; reflexivity | cbn [length Z.of_nat]; lia]].
unstash DC3k. eapply (heap_pres_rw_cells A4H); [exact HPR3Y | exact DC3k |].
eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact HFd | cbn; lia | cbn; lia].
Qed.

Definition dc_scr (Fr : Z) (v0 : word) (j16a : list byte) (c40 : cell) (j16 : list byte) : list cell :=
[C8 v0; CB 16 j16a; C8 (wz 1); C8 (wz Fr); c40; C8 (wz p); C8 (wz SH_A); CB 16 j16; C8 (wz Fr)].

Lemma dc_body :
forall (Fr q : Z) (CBS : list blk) (m3 : word -> option byte) (md3 : config) (A3 : ASA A4L HIx) (B3 : bud) (j48 j16 : list byte) (F3 : bvmap 5 word) (fc3 : bv 32)
(x1 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x21 t3' t4' t5' t6' : word) (ty np : Z),
HEAPAx A3 (BS ++ CBS ++ LB) LM ((Fr, 1) :: FRS) B3 m3 md3 ->
rw_cells asegs m3 ASP [C8 (wz 0); CB 48 j48; C8 (wz SH_A); CB 16 j16; C8 (wz Fr)] ->
In (p, np) BS -> 48 <= np -> rw_cells asegs m3 p [C4 (wz ty)] -> 1 <= ty <= 6 ->
(forall (mc : word -> option byte) (j16a j8 : list byte) (y11 y12 : word),
munch [(ASP, bv_unsigned sp + -104)] m3 mc -> wmono asegs m3 mc -> mem_inv asegs mc ->
rw_cells asegs mc ASP (dc_scr Fr (wz 0) j16a (CB 8 j8) j16) ->
AJ5 A4L HIx A3 T md3
(MS (mkR x1 (wz ASP) gp (wz A_TP) t0' t1' t2' sp (wz ASP) (wz p) y11 y12 a3' a4' a5' a6' a7'
(wz Fr) (wz Fr) (wz D) x21 (wz 2147450880) (wz p) s8 s9 s10 (wz (Fr / 8 + 2147450880)) t3' t4' t5' t6')
F3 (wz (if ty =? 5 then 0xa18a8 else if ty =? 4 then 0xa1770 else 0xa1984)) fc3 None mc (seg_rom asegs))) ->
AJ5 A4L HIx A3 T md3
(MS (mkR x1 (wz ASP) gp (wz A_TP) t0' t1' t2' sp (wz ASP) (wz 1) a1' a2' a3' a4' a5' a6' a7'
(wz Fr) (wz Fr) (wz D) x21 (wz 2147450880) (wz p) s8 s9 s10 (wz (Fr / 8 + 2147450880)) t3' t4' t5' t6')
F3 (wz 0xa1734) fc3 None m3 (seg_rom asegs)).
Proof.
intros until np. intros HP3 SCR INp Hnp TYC TY KD.
pose proof LOS as LOSu. unfold dc_stkA, DC_F, DC_C in LOSu. unfold ASP, dc_scr in *.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (INF : In (Fr, 1) ((Fr, 1) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP3 INF) as (_ & HFal & HF0 & HFc & HFimg & _ & _ & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP3 INF) as HFapp.
rewrite fr_size_1 in HFal, HFc, HFimg, HFapp. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFimg, HFapp. unfold A_SB in HFapp.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 16 <= 17594333495296) by (unfold sh; clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
assert (INp2 : In (p, np) (BS ++ CBS ++ LB)) by (apply in_or_app; left; exact INp).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p np HP3 ltac:(apply in_or_app; left; exact INp2)) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ p np HP3 ltac:(apply in_or_app; left; exact INp2)) as Hpimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hpimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p np 0 HP3 INp2 ltac:(lia) ltac:(lia)) as SHp0. rewrite Z.add_0_r in SHp0.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI3. change (hl_segs A4L) with asegs in MI3.
pose proof (wmono_refl asegs m3) as WM3. pose proof (munch_refl [(bv_unsigned sp + -192, bv_unsigned sp + -104)] m3) as MU3.
unfold A_TP. a4l. stash KD.
reenterA asegs A4L HIx asegs_wx HP3.
stepz. step. step.
step. step. ub_resolve.
step.
asan_chkA.
step. step.
unstash KD.
assert (CASES : ty = 5 \/ ty = 4 \/ ty = 1 \/ ty = 2 \/ ty = 3 \/ ty = 6) by lia.
destruct CASES as [-> | [-> | [-> | [-> | [-> | ->]]]]].
- step. if_lit. evt_done5. eapply (KD _ _ _ _ _); [eassumption | eassumption | eassumption | eassumption].
- step. if_lit. step. step. if_lit. evt_done5. eapply (KD _ _ _ _ _); [eassumption | eassumption | eassumption | eassumption].
- step. if_lit. step. step. if_lit. evt_done5. eapply (KD _ _ _ _ _); [eassumption | eassumption | eassumption | eassumption].
- step. if_lit. step. step. if_lit. evt_done5. eapply (KD _ _ _ _ _); [eassumption | eassumption | eassumption | eassumption].
- step. if_lit. step. step. if_lit. evt_done5. eapply (KD _ _ _ _ _); [eassumption | eassumption | eassumption | eassumption].
- step. if_lit. step. step. if_lit. evt_done5. eapply (KD _ _ _ _ _); [eassumption | eassumption | eassumption | eassumption].
Qed.

Lemma dc_tail0 :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x21 x23 x24 x25 x26 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(mc : word -> option byte) (mdc : config) (A : ASA A4L HIx) (Bc : bud) (Fr : Z) (v0 : word) (j16a : list byte) (c40 : cell) (j16 : list byte)
(w0 : word) (frest : list cell) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : byte)
(d : jroot) (q np ty tojs pb : Z) (CBS REM : list blk),
dc_inv mc mdc -> fsaved F F1 -> frm0 fc1 ->
HEAPAx A (BS ++ CBS ++ REM ++ LB) LM ((Fr, 1) :: FRS) Bc mc mdc ->
rw_cells asegs mc ASP (dc_scr Fr v0 j16a c40 j16) -> csize c40 = 8%nat ->
rw_cells asegs mc Fr (C8 w0 :: frest) -> Z.of_nat (cells_size frest) = 112 ->
rw_cells asegs mc (Fr / 8 + 2147450880) [C1 y0; C1 y1; C1 y2; C1 y3; C1 y4; C1 y5; C1 y6; C1 y7; C1 y8; C1 y9; C1 y10; C1 y11; C1 y12; C1 y13; C1 y14; C1 y15] ->
jroot_repA r mc BS p -> In (p, np) BS -> 48 <= np ->
rw_cells asegs mc p (jhdr_cells ty 1 tojs pb 0 0) ->
copy_of r d -> dc_cwA d CBS w -> q <> 0 -> dc_dst mc q -> jroot_repA d mc CBS q ->
bD B0 - w <= bD Bc -> bB B0 - DC_KB * w + 512 * Z.of_nat (length CBS) <= bB Bc ->
AJ5 A4L HIx A T mdc
(MS (mkR x1 (wz ASP) gp (wz A_TP) t0 t1 t2 sp (wz ASP) a0 a1 a2 a3 a4 a5 a6 a7
(wz Fr) x19 (wz D) x21 (wz 2147450880) x23 x24 x25 x26 (wz (Fr / 8 + 2147450880)) t3 t4 t5 t6)
F1 (wz 0xa1984) fc1 None mc (seg_rom asegs)).
Proof.
intros until REM. intros INV FS FRM1 HP SCR C40 FF FFsz FSH JRc INp Hnp SRC CO CW Hq [DC DSH] JD BDc BBc.
pose proof LOS as LOSu. unfold dc_stkA, DC_F, DC_C in LOSu. unfold ASP, dc_scr in *.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
destruct (dc_dfacts _ _ _ _ _ _ HP) as (D1 & D2 & D3 & D4 & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13).
pose proof (rw_cells_bound asegs mc D _ DC) as DR. cbn [cells_size csize Nat.add] in DR.
assert (INp2 : In (p, np) (BS ++ CBS ++ REM ++ LB)) by (apply in_or_app; left; exact INp).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p np HP ltac:(apply in_or_app; left; exact INp2)) as (_ & Hpal & Hplo & Hphi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p np 3 HP INp2 ltac:(lia) ltac:(lia)) as SHp3.
replace (p / 8 + 2147450880 + 3) with (p / 8 + 2147450883) in SHp3 by lia.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p np 4 HP INp2 ltac:(lia) ltac:(lia)) as SHp4.
replace (p / 8 + 2147450880 + 4) with (p / 8 + 2147450884) in SHp4 by lia.
set (sh := Fr / 8 + 2147450880) in *.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. change (hl_segs A4L) with asegs in MI.
pose proof (wmono_refl asegs mc) as WM. pose proof (munch_refl [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6444156, 6444160)] mc) as MU.
unfold jhdr_cells in SRC.

lazymatch type of SCR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) => change (c0 :: c1 :: c2 :: c3 :: c4 :: rest) with ([c0; c1; c2; c3] ++ ([c4] ++ rest)) in SCR end.
destruct (proj1 (rw_cells_app asegs mc _ _ _) SCR) as [SCRa SCRx]. cbn [cells_size csize Nat.add] in SCRx.
destruct (proj1 (rw_cells_app asegs mc _ _ _) SCRx) as [SCR40 SCRb]. cbn [cells_size Nat.add] in SCRb. rewrite C40 in SCRb.
replace (bv_unsigned sp + -192 + Z.of_nat 40 + Z.of_nat (8 + 0)) with (bv_unsigned sp + -144) in SCRb by lia.
replace (bv_unsigned sp + -192 + Z.of_nat 40) with (bv_unsigned sp + -152) in SCR40 by lia.
stash SCR40. stash SCR. clear SCRx.
stash JD. stash JRc. stash CO. stash CW. stash INV.
unfold A_TP. a4l.
reenterA asegs A4L HIx asegs_wx HP.
step. step. step. if_lit.
step. step. ub_resolve.
asan_chkA.
step. step. asan_chkM 1.
step. step. step. if_falsex.
step. asan_chkA.
step. step. if_truex.
step. step.
evt_done5. unstash JD. unstash JRc. unstash CO. unstash CW. unstash INV. unstash SCR.
eapply (dc_epi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 mc mdc A Bc (BS ++ CBS ++ REM ++ LB) Fr 0);
[ exact INV | exact FS | exact FRM1 | exact HP | exact SCR | rewrite !cells_size_app; cbn [cells_size]; rewrite C40; reflexivity | exact FF | exact FFsz | exact FSH | exact JRc | ].
split; [exact BDc|]. left. split; [reflexivity|]. exists d, q, CBS, REM.
split; [reflexivity|]. split; [exact CO|]. split; [exact CW|]. split; [exact Hq|]. split; [exact DC|]. split; [exact JD | exact BBc].
Qed.
End MDcBase.
End RC__1.
End Mq6.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qvbw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvbw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYIF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYIF.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnCn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnCn.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QR2u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QR2u.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdgq_c1.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qw5U.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2Do.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2Do.Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSHS.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qvmy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvmy. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qawr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qawr.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition VISIT_A : Z := 0xa663c.
Definition JCVISIT_A : Z := 0xa65d4.
Definition EMIT_A : Z := 0x92a2c.
Definition VIS_STK1 : Z := 176.
Definition VIS_STK0 : Z := 176 + 4096.

Section MJoVisit.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Notation joptA := (jopt asegs A4F).
Notation wz := (Z_to_bv 64).

Definition VIS (s : option jshape) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LBa BS LM : list blk) (FRS : list frame) (B : bud) (lo p : Z),
HEAPAx A LBa LM FRS B m md -> incl BS LBa ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - (VIS_STK0 + VIS_STK1 * odepth s) ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
tp = wz A_TP -> bv_unsigned ra mod 2 = 0 ->
joptA s m BS p -> Z.of_nat (length FRS) + (1 + odepth s) < 4096 ->
a0 = wz p -> a4 = wz EMIT_A ->
(forall ms' md' m' (A' : ASA A4L HIx),
ret_state A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (wz 0) m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (LBa ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' ->
HEAPAx A' LBa LM FRS B m' md' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz VISIT_A) fc None m (seg_rom asegs)).

Lemma vk_HEAPA : forall A LBa LM FRS B m md Fr lo SP mX,
HEAPAx A LBa LM ((Fr, 0) :: FRS) B m md -> alloc_ceiling <= lo -> SP <= hiA_top A4L HIx ->
munch [(lo, SP); (Fr, Fr + 56); (Fr / 8 + 2147450880, Fr / 8 + 2147450880 + 8)] m mX ->
wmono asegs m mX -> mem_inv asegs mX -> HEAPAx A LBa LM ((Fr, 0) :: FRS) B mX md.
Proof.
intros A LBa LM FRS B m md Fr lo SP mX HP LO HT MU WM MI.
eapply (fk0_HEAPA HIx); [exact HP | exact LO | exact HT | | exact WM | exact MI].
eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. intros a (H1 & H2 & H3 & _). repeat split; assumption.
Qed.

Lemma vk_pres : forall A LBa LM FRS B m md Fr lo SP mX,
HEAPAx A LBa LM ((Fr, 0) :: FRS) B m md -> alloc_ceiling <= lo -> alloc_ceiling <= SP ->
munch [(lo, SP); (Fr, Fr + 56); (Fr / 8 + 2147450880, Fr / 8 + 2147450880 + 8)] m mX ->
wmono asegs m mX -> heap_pres A4H (LBa ++ LM ++ fr_ivs A4L FRS) SP m mX.
Proof.
intros A LBa LM FRS B m md Fr lo SP mX HP LO HSP MU WM.
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
destruct (own_frame_fresh HIx Fr 0 LBa LBa LM FRS B A m md HP (incl_refl _)) as [OFF OFS].
eapply (heap_pres_of_munch A4H _ SP); [exact MU | exact WM |].
eapply (QSHS.client_outsideF HIx A LBa LM ((Fr, 0) :: FRS) B (LBa ++ LM ++ fr_ivs A4L FRS) m md _ SP HP); [| exact HSP |].
- intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. destruct Hb as [H|H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H].
- apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]].
+ left. cbn [fst snd]. lia.
+ right; right; right. exists Fr, 0. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. left. cbn [fst snd]. rewrite fr_size_0. lia.
+ right; right; right. exists Fr, 0. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. right. unfold shad. cbn [fst snd hl_sb A4L]. rewrite fr_shadow_len_0. unfold A_SB. lia.
Qed.

Lemma vis_pro :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LBa LM : list blk) (FRS : list frame) (B : bud) (lo : Z),
HEAPAx A LBa LM FRS B m md ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - VIS_STK0 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
tp = wz A_TP -> Z.of_nat (length FRS) < 4096 ->
(forall (ASP d Fr : Z) (m1 : word -> option byte) (md1 : config) (A1 : ASA A4L HIx) (jA jG jf : list byte)
(xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
(d = 0 \/ d = 16) -> ASP = bv_unsigned sp + -160 - d ->
HEAPAx A1 LBa LM ((Fr, 0) :: FRS) B m1 md1 ->
model_vm_only (cfg_model md) (cfg_model md1) ->
heap_pres A4H (LBa ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m1 ->
stk asegs m1 lo ASP ->
rw_cells asegs m1 (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs m1 ASP [CB 48 jA; C8 (wz Fr)] ->
rw_cells asegs m1 (ASP + 56) [CB (Z.to_nat d) jG] ->
rw_cells asegs m1 Fr [C8 (wz 1102416563); C8 (wz 0x13d86); C8 (wz 0xa663c); CB 32 jf] ->
rw_cells asegs m1 (Fr / 8 + 2147450880) [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243)] ->
AJ5 A4L HIx A1 T md1
(MS (mkR xra (wz ASP) gp (wz 6444320) xt0 xt1 xt2 sp (wz ASP) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
(wz Fr) a4 a5 a0 (wz 2147450880) a2 a1 a3 (wz (Fr / 8 + 2147450880)) (wz Fr) xt3 xt4 xt5 xt6)
F (wz 0xa6754) fc None m1 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz VISIT_A) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros HP ST LO LOS SPA HT TP FRN KP.
unfold VIS_STK0 in LOS. unfold VISIT_A. subst tp.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof alloc_ceiling_range as ACR.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HP) as (SB1 & SB2 & SB3 & SB4).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2. apply ro_C8_of_bytes_at in SB3.
assert (UARC : ro_cells asegs m (hl_uar_cell A4L) [C4 (Z_to_bv 64 1)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SB4]).
clear SB4. a4l.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp)] m) as MU.
unfold A_TP in *.
reenterA asegs A4L HIx asegs_wx HP.
carve_frame 160%nat ST.
bstep. bstepz. do 13 bstep.
bstep. bstep.
rewrite (unsigned_lit (bv_unsigned sp + -160)) by lia. change 18446744073709551584 with (2^64 - 2^5). rewrite OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.land_align_down by lia. change (2^5) with 32.
assert (Hd : (bv_unsigned sp + -160) mod 32 = 0 \/ (bv_unsigned sp + -160) mod 32 = 16) by (clear - SPA; Z.div_mod_to_equations; lia).
lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?rest) => change (c0 :: c1 :: rest) with ([c0; c1] ++ rest) in FR end.
destruct (proj1 (rw_cells_app asegs m1 _ _ _) FR) as [LOW SAVE]. clear FR. cbn [cells_size csize Nat.add] in SAVE.
replace (bv_unsigned sp + -160 + Z.of_nat 56) with (bv_unsigned sp + -104) in SAVE by lia.
lazymatch type of LOW with rw_cells _ _ _ [C8 ?w; CB 48 ?jb] =>
apply (rw_cells_recast asegs _ _ _ [CB 56 (le8 w ++ jb)]) in LOW;
[| split; [| exact I]; cbn [cell_wf]; rewrite length_app, length_le8; destruct LOW as [[[_ [Hw _]] _] _]; cbn [cell_wf] in Hw; lia
| cbn [cells_bytes cbytes app]; rewrite ?app_nil_r; reflexivity | reflexivity] end.
lazymatch goal with |- evt _ ?Q (MS ?rg ?Fx ?pc ?fcx None ?mc ?rom) =>
let r' := open_constr:(mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in unify rg r';
lazymatch r' with mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31 =>
assert (REST : forall (ASP d : Z) (jA jG : list byte), (d = 0 \/ d = 16) -> ASP = bv_unsigned sp + -160 - d ->
stk asegs mc lo ASP -> rw_cells asegs mc ASP [CB 56 jA] -> rw_cells asegs mc (ASP + 56) [CB (Z.to_nat d) jG] ->
evt asegs Q (MS (mkR x1 (wz ASP) x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Fx pc fcx None mc rom))
end end.
2:{ destruct Hd as [Hd | Hd]; rewrite Hd.
- replace (bv_unsigned sp + -160 - 0) with (bv_unsigned sp + -160) by lia.
eapply (REST (bv_unsigned sp + -160) 0 _ []); [left; reflexivity | lia | exact ST | exact LOW |].
split; [split; [cbn; auto | cbn [cells_bytes cbytes app]; apply bytes_at_nil; lia] |].
unfold wr_at. cbn [cells_size csize Nat.add]. change (Z.of_nat 0) with 0. split; [lia|]. split; [lia|]. intros i Hi. lia.
- replace (bv_unsigned sp + -160 - 16) with (bv_unsigned sp + -176) by lia.
carve_frame 16%nat ST. rename FR into FRX.
destruct (rw_cells_CB_cut asegs _ _ _ _ 40%nat LOW ltac:(lia)) as [LOWa LOWb].
replace (bv_unsigned sp + -160 + Z.of_nat 40) with (bv_unsigned sp + -120) in LOWb by lia.
pose proof (rw_cells_CB_join asegs _ _ _ _ _ _ FRX ltac:(replace (bv_unsigned sp + -176 + Z.of_nat 16) with (bv_unsigned sp + -160) by lia; exact LOWa)) as JN.
eapply (REST (bv_unsigned sp + -176) 16 _ _); [right; reflexivity | lia | exact ST | exact JN |].
replace (bv_unsigned sp + -176 + 56) with (bv_unsigned sp + -120) by lia. exact LOWb. }
intros ASP d jA jG Hd0 HASP STa SCRA GAP. clear LOW ST Hd.
do 6 bstep. bstep. bstep. bstep. bstep. bstep. bstep. bstep.
norm_sx32. bstep. if_false. bstep. bstep.
evt_done5.
eapply (stack_malloc_full HIx) with (k := 0) (bytes := 64) (lo := lo) (LB := LBa) (LM := LM) (FR := FRS) (B := B);
[ heap_nowA A4L HIx HP MU WM MI | lia | .. ].
all: rewrite ?unsigned_lit by lia.
1: rewrite fr_size_0; lia.
1: reflexivity.
1: lia.
1: exact STa.
1: exact LO.
1: cbn [hl_stack_A A4L]; lia.
1: clear - SPA HASP Hd0; Z.div_mod_to_equations; lia.
1: lia.
1: reflexivity.
1: reflexivity.
intros ms1 m1' md1 A1 Fr RS1 VM1 ST1 HPR1 FRNZ (jff & FF1) SHB1 HP1. open_ret RS1.
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as (_ & HFal & HF0 & HFc & HFimg & _ & HFshw & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as HFapp.
rewrite fr_size_0 in HFal, HFc, HFimg, HFapp. rewrite fr_shadow_len_0 in HFshw. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFimg, HFapp.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in SAVE; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in SCRA; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in GAP; [| left; cbn [cells_size csize Nat.add]; lia].
change (hl_segs A4H) with asegs in SAVE, SCRA, GAP.
clear SB1 SB2 SB3 UARC.
assert (FSH1 : rw_cells asegs m1' (shad A4L Fr) [CB 8 (repeat (Z_to_bv 8 0) 8)]).
{ split; [split; [cbn; split; [reflexivity | exact I] | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SHB1] | exact HFshw]. }
rewrite fr_size_0 in FF1. change (Z.to_nat (64 - 8)) with 56%nat in FF1.
unfold shad in FSH1. a4l.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 8 <= 17594333495296) by (unfold sh; clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI1. change (hl_segs A4L) with asegs in MI1. clear MI.
assert (HPR01 : heap_pres A4H (LBa ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m1').
{ eapply heap_pres_trans.
- eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; exact Hb | clia |].
apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil].
- eapply heap_pres_weaken; [exact HPR1 | lia | intros b Hb; exact Hb]. }
clear MU WM. pose proof (wmono_refl asegs m1') as WM. pose proof (munch_refl [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8)] m1') as MU.
unfold A_SB in HFapp.
reenterA asegs A4L HIx asegs_wx HP1.
bstep. bstep. bstep. if_truex.
bstep.
bstep. bstep. bstep. bstep.
rewrite (unsigned_lit Fr) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
bstep. bstep. bstep. bstep. bstepz. bstepz. bstepz. bstep. bstep.
fold sh.
bstepz. bstepz. bstepz. bstepz. bstep. bstepz. bstepz. bstepz. bstepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m1' mc, WMc : wmono asegs m1' mc, MIc : mem_inv asegs mc |- _ =>
pose proof (vk_HEAPA _ _ _ _ _ _ _ _ _ _ _ HP1 LO HT MUc WMc MIc) as HP2;
pose proof (vk_pres _ _ _ _ _ _ _ _ lo (bv_unsigned sp) _ HP1 LO ltac:(lia) MUc WMc) as HPR12 end end.
evt_done5.
eapply (KP ASP d Fr _ md1 A1 _ jG); [exact Hd0 | exact HASP | exact HP2 | exact VM1 | eapply heap_pres_trans; [exact HPR01 | exact HPR12] | eassumption | eassumption | exact SCRA | eassumption | exact FF1 | exact FSH1].
Qed.

Lemma vis_epi :
forall (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(LBa LM : list blk) (FRS : list frame) (B : bud) (lo rv : Z),
alloc_ceiling <= lo -> lo <= bv_unsigned sp - VIS_STK0 -> bv_unsigned sp <= hiA_top A4L HIx -> 0 <= bv_unsigned sp < 2^64 ->
(forall ms' md' m' (A' : ASA A4L HIx),
ret_state A4H ra sp gp (wz 6444320) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (wz rv) m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (LBa ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' ->
HEAPAx A' LBa LM FRS B m' md' ->
AJ5 A4L HIx A' T md' ms') ->
forall (ASP d Fr : Z) (mX : word -> option byte) (mdX : config) (AX : ASA A4L HIx) (cs : list cell) (jG : list byte) (w0 : word) (frest : list cell)
(x0 x1 x2 x3 x4 x5 x6 x7 : byte)
(xra xt0 xt1 xt2 xs1 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 : word),
(d = 0 \/ d = 16) -> ASP = bv_unsigned sp + -160 - d ->
HEAPAx AX LBa LM ((Fr, 0) :: FRS) B mX mdX ->
model_vm_only (cfg_model md) (cfg_model mdX) ->
heap_pres A4H (LBa ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mX ->
stk asegs mX lo ASP ->
rw_cells asegs mX (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs mX ASP cs -> Z.of_nat (cells_size cs) = 56 ->
rw_cells asegs mX (ASP + 56) [CB (Z.to_nat d) jG] ->
rw_cells asegs mX Fr (C8 w0 :: frest) ->
rw_cells asegs mX (Fr / 8 + 2147450880) [C1 x0; C1 x1; C1 x2; C1 x3; C1 x4; C1 x5; C1 x6; C1 x7] ->
AJ5 A4L HIx AX T mdX
(MS (mkR xra (wz ASP) gp (wz 6444320) xt0 xt1 xt2 sp xs1 xa0 xa1 (wz rv) xa3 xa4 xa5 xa6 xa7
(wz Fr) xs3 xs4 xs5 xs6 xs7 xs8 xs9 (wz (Fr / 8 + 2147450880)) (wz Fr) xt3 xt4 xt5 xt6)
F (wz 0xa67c4) fc None mX (seg_rom asegs)).
Proof.
intros until rv. intros LO LOS HT SPR K. unfold VIS_STK0 in LOS. intros until xt6. intros Hd0 HASP HPX VMX HPRX STX SAVE SCR SCRsz GAP FFX FSHX.
pose proof alloc_ceiling_range as ACR.
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HPX INF) as (_ & HFal & HF0 & HFc & HFimg & _ & _ & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HPX INF) as HFapp.
rewrite fr_size_0 in HFal, HFc, HFimg, HFapp. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFimg, HFapp. unfold A_SB in HFapp.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 8 <= 17594333495296) by (unfold sh; clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HPX) as MI. change (hl_segs A4L) with asegs in MI.
pose proof (wmono_refl asegs mX) as WM. pose proof (munch_refl [(lo, ASP); (Fr, Fr + 56); (sh, sh + 8)] mX) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HPX.
bstep. bstep. bstepz. bstep. if_falsex. bstep. do 8 bstepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ mX mc, WMc : wmono asegs mX mc, MIc : mem_inv asegs mc |- _ =>
pose proof (vk_HEAPA _ _ _ _ _ _ _ _ lo ASP _ HPX LO ltac:(lia) MUc WMc MIc) as HPY;
pose proof (vk_pres _ _ _ _ _ _ _ _ lo ASP _ HPX LO ltac:(lia) MUc WMc) as HPRXY end end.
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
apply (rw_cells_transport asegs [(fp, fp + 1)] _ m5) in SAVE; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] _ m5) in SCR; [| exact MUr | exact WMr | cbn [disjoint_from]; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] _ m5) in GAP; [| exact MUr | exact WMr | cbn [disjoint_from cells_size csize Nat.add]; lia].
apply (stk_transport_disjoint asegs [(fp, fp + 1)] _ m5) in STX; [| exact MUr | exact WMr | cbn [disjoint_from]; lia].

eapply stk_release in SCR; [| exact STX | lia]. rewrite SCRsz in SCR.
eapply stk_release in GAP; [| exact SCR | lia]. cbn [cells_size csize] in GAP.
replace (ASP + 56 + Z.of_nat (Z.to_nat d + 0)) with (bv_unsigned sp + -104) in GAP by lia.
clear FPC.
change (681980 + 4) with 681984.
reenterA asegs A4L HIx asegs_wx HP5.
do 18 bstep.
lazymatch goal with H : rw_cells asegs ?mc (bv_unsigned sp + -104) _ |- _ => rename H into SAVE5 end.
rename GAP into ST5.
release_frame SAVE5 ST5 (bv_unsigned sp).
evt_done5.
eapply (K _ md5 m5 A5).
- do 14 eexists. reflexivity.
- eapply model_vm_only_trans; [exact VMX | exact VM5].
- exact ST5.
- eapply heap_pres_trans; [exact HPRX|]. eapply heap_pres_trans; [eapply heap_pres_weaken; [exact HPRXY | lia | intros b Hb; exact Hb] |].
eapply (heap_pres_of_presD (Fr + 32)).
+ eapply (presD_fp HIx _ _ _ _ _ _ _ _ (Fr + 32) _ (bv_unsigned sp) fp HPY); [| lia | exact FPnc | exact FPfr | exact Hoff | exact Hwv].
intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. destruct Hb as [H|H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H].
+ intros a Hd Hc.
destruct (own_frame_fresh HIx Fr 0 LBa LBa LM FRS B AX _ mdX HPY (incl_refl _)) as [OFF OFS].
assert (Ho : outside [(Fr + 32, Fr + 40)] a).
{ eapply (QSHS.client_outsideF HIx AX LBa LM ((Fr, 0) :: FRS) B (LBa ++ LM ++ fr_ivs A4L FRS) _ mdX [(Fr + 32, Fr + 40)] (bv_unsigned sp) HPY); [| lia | | lia | exact Hc].
- intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. destruct Hb as [H|H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H].
- apply Forall_cons; [| apply Forall_nil]. right; right; right. exists Fr, 0. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. left. cbn [fst snd]. rewrite fr_size_0. lia. }
cbn [outside] in Ho. lia.
- exact HP5.
Qed.

Lemma vis_null : VIS None.
Proof.
unfold VIS. intros until p. intros HP INC ST LO LOS SPA HT TP RA JO FRN A0 A4 K.
destruct JO as [-> ->]. cbn [odepth] in LOS, FRN. subst a0 a4 tp.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
eapply vis_pro; [exact HP | exact ST | exact LO | unfold VIS_STK0, VIS_STK1 in *; lia | exact SPA | exact HT | reflexivity | lia |].
intros ASP d Fr m1 md1 A1 jA jG jf xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 Hd0 HASP HP1 VM1 HPR1 ST1 SAVE SCRA GAP FF FSH.
unfold VIS_STK0, VIS_STK1 in LOS.
pose proof alloc_ceiling_range as ACR.
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as (_ & HFal & HF0 & HFc & HFimg & _ & _ & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as HFapp.
rewrite fr_size_0 in HFal, HFc, HFimg, HFapp. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFimg, HFapp. unfold A_SB in HFapp.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 8 <= 17594333495296) by (unfold sh; clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI. change (hl_segs A4L) with asegs in MI.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HP1) as (SB1 & SB2 & _ & _).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2. a4l.
pose proof (wmono_refl asegs m1) as WM. pose proof (munch_refl [(lo, ASP); (Fr, Fr + 56); (sh, sh + 8)] m1) as MU.
reenterA asegs A4L HIx asegs_wx HP1.
do 6 bstep. bstep.
unfold EMIT_A. replace (ret_pc (wz 0x92a2c)) with (wz 0x92a2c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
bstep. bstep.
replace (ret_pc (wz 0xa6770)) with (wz 0xa6770) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
bstep. bstep. bstep. if_lit. bstep. bstep. if_lit. bstep. if_lit. bstep. bstep.

eapply evt_cut.
{ eapply jo_get_type_null_A with (lo := lo) (sbcell := 991672).
unfold small_pre, A_GOT_SB, A_SB. rewrite ?unsigned_lit by lia.
split; [assumption|]. split; [eassumption|]. split; [lia|]. split; [exact LO|]. split; [eassumption|]. split; [eassumption|]. lia. }
intros ms' (m' & (w & x & y & ->) & MUg & WMg & MIg & STg).
rewrite ?unsigned_lit in MUg, STg by lia.
lazymatch type of MUg with munch _ ?mq _ =>
transport_after_call asegs mq m' MUg WMg; try match goal with H : mem_inv asegs mq |- _ => clear H end; clear MUg WMg end.
replace (ret_pc (wz 0xa67b0)) with (wz 0xa67b0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
bstep. bstep. bstep. if_lit. bstep. bstep. if_lit.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m1 mc, WMc : wmono asegs m1 mc, MIc : mem_inv asegs mc |- _ =>
pose proof (vk_HEAPA _ _ _ _ _ _ _ _ lo ASP _ HP1 LO ltac:(lia) MUc WMc MIc) as HPe;
pose proof (vk_pres _ _ _ _ _ _ _ _ lo ASP _ HP1 LO ltac:(lia) MUc WMc) as HPRe end end.
evt_done5.
eapply (vis_epi ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md T LBa LM FRS B lo 0 LO ltac:(unfold VIS_STK0; lia) HT SPR K ASP d Fr _ md1 A1 _ jG);
[ exact Hd0 | exact HASP | exact HPe | exact VM1
| eapply heap_pres_trans; [exact HPR1 | eapply heap_pres_weaken; [exact HPRe | lia | intros b Hb; exact Hb]]
| eassumption | eassumption | exact SCRA | reflexivity | eassumption | exact FF | exact FSH ].
Qed.

Lemma vis_scalar : forall s, jtype s <> JT_OBJECT -> jtype s <> JT_ARRAY -> VIS (Some s).
Proof.
intros s NO NA. unfold VIS. intros until p. intros HP INC ST LO LOS SPA HT TP RA JO FRN A0 A4 K.
destruct JO as [Hp J]. subst a0 a4 tp.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (DN : 0 <= odepth (Some s)) by (cbn [odepth]; apply sdepth_nonneg).
destruct (Qdgq_c1.jval_hdr_rd asegs A4F s m BS p 1 J) as (n & tojs & pb & udel & ud & INp & N48 & HDRH).
assert (INpA : In (p, n) (LBa ++ LM)) by (apply in_or_app; left; apply INC; exact INp).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p n HP INpA) as (_ & Hpal & Hplo & Hphi & _).
pose proof (jtype_range s) as TYR.
eapply vis_pro; [exact HP | exact ST | exact LO | unfold VIS_STK0, VIS_STK1 in *; lia | exact SPA | exact HT | reflexivity | lia |].
intros ASP d Fr m1 md1 A1 jA jG jf xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 Hd0 HASP HP1 VM1 HPR1 ST1 SAVE SCRA GAP FF FSH.
unfold VIS_STK0, VIS_STK1 in LOS.
pose proof alloc_ceiling_range as ACR.
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as (_ & HFal & HF0 & HFc & HFimg & _ & _ & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as HFapp.
rewrite fr_size_0 in HFal, HFc, HFimg, HFapp. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFimg, HFapp. unfold A_SB in HFapp.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 8 <= 17594333495296) by (unfold sh; clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI. change (hl_segs A4L) with asegs in MI.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HP1) as (SB1 & SB2 & _ & _).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in HDRH; [| eapply client_range_block; [apply in_or_app; left; apply INC; exact INp | lia | unfold jhdr_cells; cbn; lia]].
change (hl_segs A4H) with asegs in HDRH.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p n 0 HP1 ltac:(apply INC; exact INp) ltac:(lia) ltac:(lia)) as SH0. rewrite Z.add_0_r in SH0.
a4l.
pose proof (wmono_refl asegs m1) as WM. pose proof (munch_refl [(lo, ASP); (Fr, Fr + 56); (sh, sh + 8)] m1) as MU.
reenterA asegs A4L HIx asegs_wx HP1.
do 6 bstep. bstep.
unfold EMIT_A. replace (ret_pc (wz 0x92a2c)) with (wz 0x92a2c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
bstep. bstep.
replace (ret_pc (wz 0xa6770)) with (wz 0xa6770) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
bstep. bstep. bstep. if_lit. bstep. bstep. if_lit. bstep. if_lit. bstep. bstep.

eapply evt_cut.
{ eapply jo_get_type_A with (lo := lo) (sbcell := 991672) (p := p) (ty := jtype s) (rc := 1) (tojs := tojs) (pb := pb) (udel := udel) (ud := ud).
- unfold small_pre, A_GOT_SB, A_SB. rewrite ?unsigned_lit by lia.
split; [assumption|]. split; [eassumption|]. split; [lia|]. split; [exact LO|]. split; [eassumption|]. split; [eassumption|]. lia.
- exact HDRH.
- lia.
- lia.
- clear - Hpal; Z.div_mod_to_equations; lia.
- lia.
- unfold A_SB. exact SH0.
- unfold A_SB. clear - Hphi ACR Hplo N48. Z.div_mod_to_equations; lia. }
intros ms' (m' & (w & x & y & ->) & MUg & WMg & MIg & STg).
rewrite ?unsigned_lit in MUg, STg by lia.
lazymatch type of MUg with munch _ ?mq _ =>
transport_after_call asegs mq m' MUg WMg; try match goal with H : mem_inv asegs mq |- _ => clear H end; clear MUg WMg end.
replace (ret_pc (wz 0xa67b0)) with (wz 0xa67b0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
bstep. bstep.
assert (TC : jtype s <= 3 \/ jtype s = 6).
{ destruct s; cbn in *; unfold JT_BOOLEAN, JT_DOUBLE, JT_INT, JT_STRING, JT_OBJECT, JT_ARRAY in *; lia. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m1 mc, WMc : wmono asegs m1 mc, MIc : mem_inv asegs mc |- _ =>
pose proof (vk_HEAPA _ _ _ _ _ _ _ _ lo ASP _ HP1 LO ltac:(lia) MUc WMc MIc) as HPe;
pose proof (vk_pres _ _ _ _ _ _ _ _ lo ASP _ HP1 LO ltac:(lia) MUc WMc) as HPRe end end.
destruct TC as [T3 | T6].
-
bstep. if_falsex. bstep. bstep. if_falsex.
evt_done5.
eapply (vis_epi ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md T LBa LM FRS B lo 0 LO ltac:(unfold VIS_STK0; lia) HT SPR K ASP d Fr _ md1 A1 _ jG);
[ exact Hd0 | exact HASP | exact HPe | exact VM1
| eapply heap_pres_trans; [exact HPR1 | eapply heap_pres_weaken; [exact HPRe | lia | intros b Hb; exact Hb]]
| eassumption | eassumption | exact SCRA | reflexivity | eassumption | exact FF | exact FSH ].
-
rewrite T6 in *. bstep. if_lit. bstep. bstep. if_lit.
evt_done5.
eapply (vis_epi ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md T LBa LM FRS B lo 0 LO ltac:(unfold VIS_STK0; lia) HT SPR K ASP d Fr _ md1 A1 _ jG);
[ exact Hd0 | exact HASP | exact HPe | exact VM1
| eapply heap_pres_trans; [exact HPR1 | eapply heap_pres_weaken; [exact HPRe | lia | intros b Hb; exact Hb]]
| eassumption | eassumption | exact SCRA | reflexivity | eassumption | exact FF | exact FSH ].
Qed.

Lemma vis_tail :
forall (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(LBa LM : list blk) (FRS : list frame) (B : bud) (lo : Z),
alloc_ceiling <= lo -> lo <= bv_unsigned sp - VIS_STK0 -> bv_unsigned sp <= hiA_top A4L HIx -> 0 <= bv_unsigned sp < 2^64 ->
(forall ms' md' m' (A' : ASA A4L HIx),
ret_state A4H ra sp gp (wz 6444320) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (wz 0) m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (LBa ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' ->
HEAPAx A' LBa LM FRS B m' md' ->
AJ5 A4L HIx A' T md' ms') ->
forall (ASP d Fr : Z) (mX : word -> option byte) (mdX : config) (AX : ASA A4L HIx) (j0 jG : list byte) (w8 w0 : word) (srest frest : list cell)
(x0 x1 x2 x3 x4 x5 x6 x7 : byte) (jsow uaw keyw parw : word)
(xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 xt5 xt6 : word),
(d = 0 \/ d = 16) -> ASP = bv_unsigned sp + -160 - d ->
HEAPAx AX LBa LM ((Fr, 0) :: FRS) B mX mdX ->
model_vm_only (cfg_model md) (cfg_model mdX) ->
heap_pres A4H (LBa ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mX ->
stk asegs mX lo ASP ->
rw_cells asegs mX (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs mX ASP (CB 8 j0 :: C8 w8 :: srest) -> Z.of_nat (cells_size srest) = 40 ->
rw_cells asegs mX (ASP + 56) [CB (Z.to_nat d) jG] ->
rw_cells asegs mX Fr (C8 w0 :: frest) ->
rw_cells asegs mX (Fr / 8 + 2147450880) [C1 x0; C1 x1; C1 x2; C1 x3; C1 x4; C1 x5; C1 x6; C1 x7] ->
AJ5 A4L HIx AX T mdX
(MS (mkR xra (wz ASP) gp (wz 6444320) xt0 xt1 xt2 sp (wz ASP) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
(wz Fr) (wz EMIT_A) uaw jsow (wz 2147450880) keyw parw xs9 (wz (Fr / 8 + 2147450880)) (wz Fr) xt3 xt4 xt5 xt6)
F (wz 0xa69f4) fc None mX (seg_rom asegs)).
Proof.
intros until lo. intros LO LOS HT SPR K. intros until xt6. intros Hd0 HASP HPX VMX HPRX STX SAVE SCR SCRsz GAP FFX FSHX.
pose proof LOS as LOS'. unfold VIS_STK0 in LOS'.
pose proof alloc_ceiling_range as ACR.
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HPX INF) as (_ & HFal & HF0 & HFc & HFimg & _ & _ & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HPX INF) as HFapp.
rewrite fr_size_0 in HFal, HFc, HFimg, HFapp. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFimg, HFapp. unfold A_SB in HFapp.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 8 <= 17594333495296) by (unfold sh; clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HPX) as MI. change (hl_segs A4L) with asegs in MI.
pose proof (wmono_refl asegs mX) as WM. pose proof (munch_refl [(lo, ASP); (Fr, Fr + 56); (sh, sh + 8)] mX) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HPX.
do 6 bstep. bstep.
unfold EMIT_A. replace (ret_pc (wz 0x92a2c)) with (wz 0x92a2c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
bstep. bstep.
replace (ret_pc (wz 0xa6a10)) with (wz 0xa6a10) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
bstep. bstep. bstep. if_lit. bstep. bstep. if_lit. bstep. if_lit.
evt_done5.
eapply (vis_epi ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md T LBa LM FRS B lo 0 LO LOS HT SPR K ASP d Fr _ mdX AX _ jG);
[ exact Hd0 | exact HASP | exact HPX | exact VMX | exact HPRX | eassumption | eassumption | eassumption
| cbn [cells_size csize Nat.add]; lia | eassumption | eassumption | exact FSHX ].
Qed.
End MJoVisit.
End RC__1.
